#!/usr/bin/env python3
"""Fetch immutable upstream proof inputs; reject any checksum mismatch."""
import hashlib
import json
import re
import time
import urllib.error
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def fetch(url):
    for attempt in range(5):
        try:
            with urllib.request.urlopen(url, timeout=60) as response:
                return response.read()
        except urllib.error.HTTPError as error:
            if error.code not in {408, 429, 500, 502, 503, 504} or attempt == 4:
                raise
        except (urllib.error.URLError, ConnectionError, TimeoutError):
            if attempt == 4:
                raise
        print('Retrying interrupted source download:', url, flush=True)
        time.sleep(2 ** attempt)
    raise RuntimeError('Source download attempts exhausted')

for entry in json.loads((ROOT / 'UPSTREAM.json').read_text()):
    target = ROOT / entry['path']
    if target.exists():
        if hashlib.sha256(target.read_bytes()).hexdigest() != entry['port_sha256']:
            raise SystemExit('Existing port differs from pinned bytes: ' + entry['path'])
        print('Verified upstream port: ' + entry['path'])
        continue
    data = fetch(entry['url'])
    if hashlib.sha256(data).hexdigest() != entry['sha256']:
        raise SystemExit('Upstream checksum mismatch: ' + entry['path'])
    text = data.decode('utf-8')
    for old, new in entry['renames'].items():
        text = re.sub(r'\b' + old + r'\b', new, text)
    for old, new in entry['edits']:
        if old not in text:
            raise SystemExit('Expected compatibility input missing: ' + entry['path'])
        text = text.replace(old, new)
    data = text.encode('utf-8')
    if hashlib.sha256(data).hexdigest() != entry['port_sha256']:
        raise SystemExit('Compatibility-port checksum mismatch: ' + entry['path'])
    target.parent.mkdir(parents=True, exist_ok=True)
    if not target.exists():
        target.write_bytes(data)
    print('Verified upstream: ' + entry['path'])
