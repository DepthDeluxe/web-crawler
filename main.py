#!/usr/bin/env python3

from argparse import ArgumentParser, Namespace
import asyncio
from contextlib import closing
import sqlite3
import aiohttp
from dataclasses import dataclass
from enum import Enum
from typing import Optional, Tuple
import aiohttp.client_exceptions
import lxml.html
from urllib.parse import urlparse
import os
import logging
import tqdm.asyncio
import math
from concurrent.futures import ProcessPoolExecutor
import threading
import re
from datetime import datetime, timedelta

HTTP_TIMEOUT_S = 5.0
NUM_ATTEMPTS = 5
BASE_RETRY_DELAY_S = 0.1
QUARANTINE_DURATION = timedelta(minutes=10)
QUARANTINE_CHECK_TIMEOUT_S = 30

DOMAIN_BLACKLIST = [
    re.compile(r'archive\.org'),
    re.compile(r'.*\.archive\.org'),
    re.compile(r'wikipedia.org'),
    re.compile(r'.*\.wikipedia.org'),
    re.compile(r'linkedin.com'),
    re.compile(r'.*\.linkedin\.com')
]
SCHEME_WHITELIST = [
    'http',
    'https'
]

CONTENT_TYPE_WHITELIST = [
    'text/xhtml+xml',
    'text/xml',
    'text/html',
]

class VisitState(Enum):
    NOT_VISITED = 0
    VISITED = 1
    QUARANTINED = 2

class QuarantineReason(Enum):
    CONNECT_TIMEOUT = 0
    FORBIDDEN = 1
    CLIENT_ERROR = 2
    TOO_MANY_REQUESTS = 3

@dataclass
class Page:
    url: str
    visit_state: VisitState

@dataclass
class Link:
    from_: int
    to: int

class CreateStatus(Enum):
    EXISTING = 0
    NEW = 1

def create_page_from_url(url: str) -> Page:
    parsed_url = urlparse(url)

    page = Page(scheme=parsed_url.scheme, domain=parsed_url.netloc, path=parsed_url.path, parameters=parsed_url.params, visit_state=VisitState.NOT_VISITED)
    return page

class Model:
    def __init__(self, connection: sqlite3.Connection):
        self._connection = connection

    def _cursor(self) -> sqlite3.Cursor:
        return self._connection.cursor()
    
    def commit(self) -> None:
        self._connection.commit()

    def create_tables(self) -> None:
        with closing(self._cursor()) as cursor:
            cursor.execute('CREATE TABLE IF NOT EXISTS pages (id INTEGER PRIMARY KEY AUTOINCREMENT, url VARCHAR(4096) NOT NULL UNIQUE, http_code INT, size INT, visit_state INT NOT NULL, error BLOB)')
            cursor.execute('CREATE TABLE IF NOT EXISTS links (id INTEGER PRIMARY KEY AUTOINCREMENT, from_ INT NOT NULL, to_ INT NOT NULL, UNIQUE(from_, to_))')
            cursor.execute('CREATE TABLE IF NOT EXISTS quarantine (page_id INTEGER PRIMARY KEY, reason INT NOT NULL, until UNIXEPOCH NOT NULL)')

            cursor.execute('CREATE INDEX IF NOT EXISTS pages_url_index ON pages (url)')
            cursor.execute('CREATE INDEX IF NOT EXISTS pages_visit_index ON pages (visit_state)')
            cursor.execute('CREATE INDEX IF NOT EXISTS links_from_index ON links (from_)')

    def _fetch_page_id(self, url: str) -> Optional[int]:
        with closing(self._cursor()) as cursor:
            row = cursor.execute('SELECT id FROM pages WHERE url = ?', (url, )).fetchone()
            if row is None:
                return None
            else:
                return row[0]
            
    def create_or_get_page_id(self, url: str, visit_state: VisitState = VisitState.NOT_VISITED) -> Tuple[CreateStatus, int]:
        existing_id = self._fetch_page_id(url)
        if existing_id is not None:
            return CreateStatus.EXISTING, existing_id

        with closing(self._cursor()) as cursor: 
            cursor.execute('INSERT INTO pages (url, visit_state) VALUES (?, ?)', (url, visit_state.value))
            return CreateStatus.NEW, cursor.lastrowid

    def get_page_id(self, url: str) -> Optional[int]:
        return self._fetch_page_id(url)
    
    def get_unvisited_urls(self, limit: int) -> list[str]:
        with closing(self._cursor()) as cursor:
            rows = cursor.execute('SELECT url FROM pages WHERE visit_state = ? LIMIT ?', (VisitState.NOT_VISITED.value, limit)).fetchall()
            return [row[0] for row in rows]

    def get_num_pages_by_state(self, state: VisitState) -> int:
        with closing(self._cursor()) as cursor:
            row = cursor.execute('SELECT count(*) FROM pages WHERE visit_state = ?', (state.value,)).fetchone()
            return row[0]
        
    def _set_page_visit_state(self, cursor: sqlite3.Cursor, id_: int, visit_state: VisitState):
        cursor.execute('UPDATE pages SET visit_state = ? WHERE id = ?', (visit_state.value, id_))

    def mark_page_visited(self, url: str, size: Optional[int], http_code: int):
        with closing(self._cursor()) as cursor:
            cursor.execute('UPDATE pages SET visit_state = ?, http_code = ?, size = ? WHERE url = ?', (VisitState.VISITED.value, http_code, size, url))

    def set_page_error(self, url: str, error: str) -> None:
        with closing(self._cursor()) as cursor:
            cursor.execute('UPDATE pages SET error = ?, visit_state = ? WHERE url = ?', (error, VisitState.VISITED.value, url))
        
    def quarantine_page(self, id_: int, reason: QuarantineReason, until: Optional[datetime] = None) -> None:
        if until is None:
            until = datetime.now() + QUARANTINE_DURATION

        with closing(self._cursor()) as cursor:
            cursor.execute('INSERT INTO quarantine (page_id, reason, until) VALUES (?, ?, ?)', (id_, reason.value, int(until.timestamp())))
            self._set_page_visit_state(cursor, id_, VisitState.QUARANTINED)

    def unquarantine_pages(self, expiration_date: Optional[datetime] = None) -> int:
        if expiration_date is None:
            expiration_date = datetime.now()

        with closing(self._cursor()) as cursor:
            quarantined_ids = cursor.execute('SELECT page_id FROM quarantine WHERE until < ?', (expiration_date.timestamp(), )).fetchall()
            for id_ in quarantined_ids:
                cursor.execute('DELETE FROM quarantine WHERE id = ?', (id_, ))
                self._set_page_visit_state(cursor, id_, VisitState.NOT_VISITED)

        return len(quarantined_ids)
    
    def _fetch_link_id(self, link: Link) -> Optional[int]:
        with closing(self._cursor()) as cursor: 
            row = cursor.execute('SELECT id FROM links WHERE from_ = ? AND to_ = ?', (link.from_, link.to)).fetchone()
            if row is None:
                return None
            else:
                return row[0]
    
    def create_or_get_link_id(self, from_id: int, to_id: int) -> Tuple[CreateStatus, int]:
        with closing(self._cursor()) as cursor: 
            row = cursor.execute('SELECT id FROM links WHERE from_ = ? AND to_ = ?', (from_id, to_id, )).fetchone()
            if row is None:
                cursor.execute('INSERT INTO links (from_, to_) VALUES (?, ?)', (from_id, to_id))
                return CreateStatus.NEW, cursor.lastrowid
            else:
                return CreateStatus.EXISTING, row[0]

    def get_visit_state(self, url: str) -> VisitState:
        with closing(self._cursor()) as cursor:
            row = cursor.execute('SELECT visit_state FROM pages WHERE url = ?', (url,)).fetchone()
            assert row is not None
            return VisitState(row[0])

class ParseLinksError(Exception):
    pass

def parse_links(text: str, parent_url: str) -> set[str]:
    if text is None:
        return set()

    try:
        tree = lxml.html.fromstring(text)
    except Exception as e:
        raise ParseLinksError('lxml.html parse error: ' + str(e))
    
    if tree is None:
        raise ParseLinksError('Empty page')
    
    try:
        parsed_page_url = urlparse(parent_url)
    except Exception:
        raise ParseLinksError('Bad URL')

    links = set()
    for element in tree.xpath('//a[@href]'):
        link = element.attrib['href']
        try:
            parsed_link = urlparse(link)
        except ValueError:
            continue
        
        if not parsed_link.scheme in SCHEME_WHITELIST:
            # only allow http https connections
            continue
        if parsed_link.scheme == '' or parsed_link.scheme is None:
            parsed_link = parsed_link._replace(scheme=parsed_page_url.scheme)
        if parsed_link.netloc == '' or parsed_link.netloc is None:
            parsed_link = parsed_link._replace(netloc=parsed_page_url.netloc)
        if parsed_link.path is None or parsed_link.path == '':
            # likely a fragment-only link
            continue
        parsed_link = parsed_link._replace(fragment=None)

        if not os.path.isabs(parsed_link.path):
            parsed_link = parsed_link._replace(path=os.path.normpath(parsed_page_url.path + '/' + parsed_link.path))

        in_blacklist = False
        for blacklist in DOMAIN_BLACKLIST:
            if blacklist.match(parsed_link.netloc) is not None:
                # hit the blacklist
                in_blacklist = True
                break

        if in_blacklist:
            continue

        links.add(parsed_link.geturl())

    return links

def is_valid_content_type(headers) -> bool:
    if 'content-type' not in headers:
        return True

    content_type = headers['content-type']
    for item in CONTENT_TYPE_WHITELIST:
        if content_type.startswith(item):
            return True
    
    return False

async def process_url(url: str, executor: ProcessPoolExecutor, model: Model) -> None:
    page_id = model.get_page_id(url)
    assert page_id is not None

    if model.get_visit_state(url) == VisitState.QUARANTINED:
        logging.debug('Skipping quarantined page url=%s', url)
        return

    quarantine_reason = None
    error_reason = None
    links = set()
    for attempt_number in range(NUM_ATTEMPTS):
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=HTTP_TIMEOUT_S)) as session:
            try:
                async with session.get(url) as response:
                    if is_valid_content_type(response.headers):
                        try:
                            text = await response.text()
                        except UnicodeDecodeError:
                            error_reason = 'Page parsing error'
                            break

                        if response.status != 200:
                            logging.debug('URL %s status_code=%d', url, response.status)

                        if response.status == 403:
                            quarantine_reason = QuarantineReason.FORBIDDEN
                            break
                        elif response.status == 429:
                            quarantine_reason = QuarantineReason.TOO_MANY_REQUESTS
                            break
                        else:
                            model.mark_page_visited(url, response.content_length, response.status)
                            try:
                                links = await asyncio.get_running_loop().run_in_executor(executor, parse_links, text, url)
                                # links = parse_links(text, url)
                                for link in links:
                                    _, to_page_id = model.create_or_get_page_id(link)
                                    model.create_or_get_link_id(from_id=page_id, to_id=to_page_id)
                            except ParseLinksError as e:
                                error_reason = str(e)
                                logging.info('Unable to process url url=%s, err=%s', url, error_reason)
                                break

                        quarantine_reason = None
            except asyncio.TimeoutError as e:
                delay = BASE_RETRY_DELAY_S * math.pow(1.5, attempt_number)
                logging.debug('Fetching page failed, will delay url=%s, attempt=%f, delay=%f, err=%s', url, attempt_number, delay, e)
                quarantine_reason = QuarantineReason.CONNECT_TIMEOUT
                await asyncio.sleep(delay)
            except aiohttp.client_exceptions.ClientError as e:
                logging.warning('Unable to connect to %s: %s', url, e)
                quarantine_reason = QuarantineReason.CLIENT_ERROR

    if error_reason is not None:
        model.set_page_error(url, error_reason)
    elif quarantine_reason is not None:
        try:
            model.quarantine_page(page_id, QuarantineReason.CLIENT_ERROR)
        except sqlite3.IntegrityError:
            logging.info('Page is already quarantined url=%s', url)

    return links


async def processing_loop(model: Model, batch_size: int) -> None:
    pbar = tqdm.tqdm(total=1)
    executor = ProcessPoolExecutor()

    min_batch_size = batch_size / 2
    tasks = set([asyncio.create_task(process_url(url, executor, model)) for url in model.get_unvisited_urls(batch_size)])
    while len(tasks) > 0 or len(model.get_unvisited_urls(1)) > 0:
        if len(tasks) <= min_batch_size:
            # add more tasks
            for url in model.get_unvisited_urls(batch_size - len(tasks)):
                tasks.add(asyncio.create_task(process_url(url, executor, model)))

            num_not_visited = model.get_num_pages_by_state(VisitState.NOT_VISITED)
            num_visited = model.get_num_pages_by_state(VisitState.VISITED)

            pbar.reset(num_visited + num_not_visited)
            pbar.update(num_visited)

        done_tasks, pending_tasks = await asyncio.wait(tasks, return_when=asyncio.FIRST_COMPLETED)
        tasks = pending_tasks
        model.commit()

        pbar.update(len(done_tasks))
        pbar.refresh()

        logging.debug('processing done=%d, pending=%d', len(done_tasks), len(pending_tasks))

    pbar.close()

async def quarantine_loop(model: Model):
    while True:
        num_unquarantined = model.unquarantine_pages()
        logging.info('Unquarantined %d pages', num_unquarantined)

        await asyncio.sleep(QUARANTINE_CHECK_TIMEOUT_S)

def is_url_valid(url):
    try:
        parsed_url = urlparse(url)
    except Exception:
        return False

    if parsed_url.scheme != 'http' and parsed_url.scheme != 'https':
        return False
    if parsed_url.netloc == '':
        return False
    
    return True

def seed_main(args: Namespace, model: Model):
    seeded_urls = 0
    for url in args.url:
        if not is_url_valid(url):
            print(f'URL "{url}" is not valid, skipping')
            continue
        model.create_or_get_page_id(url)
        seeded_urls += 1

    model.commit()
    print(f'Seeded {seeded_urls} url{"s" if seeded_urls > 1 else ""}')

def runner_main(args: Namespace, model: Model):
    loop = asyncio.new_event_loop()
    tasks = [
        loop.create_task(processing_loop(model, batch_size=args.batch_size)),
        loop.create_task(quarantine_loop(model))
    ]
    loop.run_until_complete(asyncio.wait(tasks))
    loop.close()

def main():
    global database_path

    parser = ArgumentParser()
    parser.add_argument('--database', type=str, help='SQLite database file to use', default='database.db')
    parser.add_argument('--verbose', action='store_true', help='Verbose logging')
    subparsers = parser.add_subparsers(dest='command')

    runner_parser = subparsers.add_parser('run', help='Runs main processing loop of crawler') 
    runner_parser.add_argument('--batch-size', type=int, help='Batching size for runner')

    seed_parser = subparsers.add_parser('seed', help='Seeds the database with URLs')
    seed_parser.add_argument('url', help='URL to seed into the system', nargs='+')

    args = parser.parse_args()

    if args.verbose:
        level = logging.DEBUG
    else:
        level = logging.INFO
    logging.basicConfig(format='%(asctime)s [%(levelname)s] - %(message)s', level=level)

    connection = sqlite3.connect(args.database)
    model = Model(connection)
    model.create_tables()

    if args.command == 'run':
        runner_main(args, model)
    elif args.command == 'seed':
        seed_main(args, model)
    else:
        raise Exception()

if __name__ == '__main__':
    main()