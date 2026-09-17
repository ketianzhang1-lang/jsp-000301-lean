#!/usr/bin/env python3
"""Fetch exact attributed proof inputs, refusing any hash mismatch.

No credentials are requested. Downloads use immutable public GitHub URLs.
This script does not compile Lean or establish award eligibility.
"""
from __future__ import annotations
import argparse
import hashlib
from pathlib import Path
from urllib.request import Request, urlopen

PIN = '8822f7ddef30fadbd92e1c6ab4ed897af356af5e'
ROOT = f'https://raw.githubusercontent.com/plby/lean-proofs/{PIN}/src/latest/ErdosProblems/'
INPUTS = {
    'Erdos895.lean': ('Erdos895.lean', 'f1527baff5eba895e1208d27c705487fa52a7ed647ca94935d5e9c1137e77163'),
    'Certificate.cnf': ('Erdos895/Certificate.cnf', '260b7c50fac4fcc4525f7253eb37a8750bf744cff5bb41e92a314cdea1ccab45'),
    'Certificate.lrat': ('Erdos895/Certificate.lrat', '2f8729bd57e5ee6d24292e2b51fc72afad884bedf5234b808615568fe9bac582'),
}

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory', type=Path, default=Path(__file__).parent)
    args = parser.parse_args()
    args.directory.mkdir(parents=True, exist_ok=True)
    for name, (relative, expected) in INPUTS.items():
        destination = args.directory/name
        if destination.exists():
            data = destination.read_bytes()
        else:
            request = Request(ROOT+relative, headers={'User-Agent': 'JSP746-reproduction/1.0'})
            with urlopen(request, timeout=120) as response:
                data = response.read()
        digest = hashlib.sha256(data).hexdigest()
        if digest != expected:
            raise SystemExit(f'Hash mismatch for {name}; no file was replaced: {digest}')
        if not destination.exists():
            destination.write_bytes(data)
        print(f'{name}: SHA-256 OK')
    print('Original attribution is retained in Erdos895.lean. No authorship transfer is asserted.')

if __name__ == '__main__':
    main()
