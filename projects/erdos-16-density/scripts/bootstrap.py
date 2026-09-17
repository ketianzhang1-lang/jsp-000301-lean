#!/usr/bin/env python3
"""Fetch the unchanged, checksum-pinned upstream prerequisite, not redistributed here."""
import hashlib
import subprocess
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
TARGET = ROOT / 'Erdos16.lean'
URL = ('https://raw.githubusercontent.com/plby/lean-proofs/'
       '8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos16.lean')
SHA = '939a0a7178f416b3e3a6606ff56f637e1dc5f91f29e75a8e54f6456c44a4d475'
if TARGET.exists():
    data = TARGET.read_bytes()
else:
    data = subprocess.check_output(['curl', '-fLsS', '--retry', '2', URL])
if hashlib.sha256(data).hexdigest() != SHA:
    raise SystemExit('Upstream source checksum mismatch; refusing to use or overwrite it')
if not TARGET.exists():
    TARGET.write_bytes(data)
print('Pinned upstream source verified:', SHA, len(data), 'bytes')
