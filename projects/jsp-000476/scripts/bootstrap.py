#!/usr/bin/env python3
"""Restore the immutable upstream closure and its documented upstream API patches."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import hashlib, json, re, subprocess, time, urllib.request

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = json.loads((ROOT / 'UPSTREAM.json').read_text())
PATCHES = json.loads((ROOT / 'UPSTREAM_PATCHES.json').read_text())

def digest(data): return hashlib.sha256(data).hexdigest()

def fetch(url):
    for attempt in range(5):
        try:
            with urllib.request.urlopen(url, timeout=60) as response: return response.read()
        except Exception:
            if attempt == 4: raise
            time.sleep(2 ** attempt)

def check(data, entry):
    assert digest(data) == entry['sha256'], 'SHA-256 mismatch: ' + entry['url']
    assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest() == entry['git_blob_sha'], 'Git blob mismatch: '+entry['url']

pending = [e for e in MANIFEST if not (ROOT / e['path']).exists()]
for e in MANIFEST:
    path = ROOT / e['path']
    if path.exists() and digest(path.read_bytes()) != e['port_sha256']:
        raise SystemExit('Existing source differs from pinned port: ' + e['path'])
patch_texts = {}
if pending:
    for p in PATCHES:
        data = fetch(p['url']); check(data, p)
        patch_texts[p['name']] = data.decode()

def restore(e):
    data = fetch(e['url']); check(data, e)
    path = ROOT / e['path']; path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
    for patch in e.get('upstream_patches', []):
        found = False
        for section in re.split(r'(?=^diff --git )', patch_texts[patch['name']], flags=re.M):
            match = re.search(r'^--- a/(.*)$', section, re.M)
            if not match: continue
            original = match[1]
            rel = original.removeprefix('projects/HasseWeil/').removeprefix('Warning/')
            if rel != e['path']: continue
            section = section.replace('a/'+original, 'a/'+rel).replace('b/'+original, 'b/'+rel)
            subprocess.run(['patch', '-p1', '--batch', '--forward'], cwd=ROOT,
                input=section, text=True, check=True, capture_output=True)
            found = True
        if not found: raise RuntimeError('Missing pinned patch for ' + e['path'])
    if digest(path.read_bytes()) != e['port_sha256']:
        raise RuntimeError('Patched source mismatch: ' + e['path'])

with ThreadPoolExecutor(max_workers=16) as pool: list(pool.map(restore, pending))
for e in MANIFEST:
    assert digest((ROOT / e['path']).read_bytes()) == e['port_sha256'], e['path']
print(f'Verified {len(MANIFEST)} pinned upstream modules ({len(pending)} restored).', flush=True)
