#!/usr/bin/env python3
"""Fetch immutable upstream proof inputs; reject any checksum mismatch."""
import hashlib
import json
import re
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
for entry in json.loads((ROOT / 'UPSTREAM.json').read_text()):
    target = ROOT / entry['path']
    if target.exists():
        if hashlib.sha256(target.read_bytes()).hexdigest() != entry['port_sha256']:
            raise SystemExit('Existing port differs from pinned bytes: ' + entry['path'])
        print('Verified upstream port: ' + entry['path'])
        continue
    data = urllib.request.urlopen(entry['url'], timeout=120).read()
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
