#!/usr/bin/env python3
"""Fetch immutable upstream inputs and verify their hashes before applying the recorded port."""
import hashlib,json,urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
for entry in json.loads((ROOT/'UPSTREAM.json').read_text()):
    target=ROOT/entry['path']
    if target.exists():
        if hashlib.sha256(target.read_bytes()).hexdigest()!=entry['port_sha256']:
            raise SystemExit(f"Existing input differs from pinned version: {entry['path']}")
        print(entry['path']+': pinned bytes present');continue
    data=urllib.request.urlopen(entry['url'],timeout=120).read()
    if hashlib.sha256(data).hexdigest()!=entry['sha256']:
        raise SystemExit(f"Upstream checksum mismatch: {entry['path']}")
    if entry['path']=='Erdos895.lean':
        data=data.replace(b'import Mathlib\n',b'import Mathlib.Combinatorics.SimpleGraph.Clique\nimport Mathlib.Tactic\n',1)
    if entry['path']=='ErdosProblems/Erdos1216.lean':
        data=data.replace(b'if_false',b'ite_false').replace(b'if_true',b'ite_true')
    if hashlib.sha256(data).hexdigest()!=entry['port_sha256']:
        raise SystemExit(f"Port checksum mismatch: {entry['path']}")
    target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
    print(entry['path']+': checksum verified')
