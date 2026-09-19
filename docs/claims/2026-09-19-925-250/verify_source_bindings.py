"""Verify immutable source bytes and the documented reuse comparison.

This script does not execute Lean or establish mathematical validity.
Run beside sources.json; optionally reuse audit downloads with --source-cache DIR.
"""
import argparse
import hashlib
import json
from pathlib import Path
from urllib.request import Request, urlopen


def verify(cache=None):
    manifest = json.loads(Path(__file__).with_name('sources.json').read_text())
    sources = {}
    for record in manifest['sources']:
        key = record['id']
        if cache is not None:
            data = (cache / (key + '.source')).read_bytes()
        else:
            request = Request(record['url'], headers={'User-Agent': 'JSP-source-binding-review/1.0'})
            with urlopen(request, timeout=45) as response:
                data = response.read()
        actual = {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest(),
                  'git_blob_sha1': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()}
        for field, value in actual.items():
            if value != record[field]:
                raise ValueError(f'{key}: {field} mismatch')
        sources[key] = data
        print(f'PASS {key}: byte count, SHA-256 and Git blob')
    upper = sources['upper250_early']
    if not upper == sources['upper250_historical'] == sources['upper250_selected']:
        raise ValueError('Original, historical and selected upper proofs differ')
    if sources['strict925'] != sources['strict925_historical']:
        raise ValueError('Selected and historical strict supplements differ')
    original = upper.replace(b'\r\n', b'\n')
    reused = sources['upper250_reused'].replace(b'\r\n', b'\n')
    if not reused.endswith(original):
        raise ValueError('Reused upper source differs beyond the header and line endings')
    header = reused[:-len(original)]
    if not (header.startswith(b'/-\n') and header.endswith(b'-/\n')
            and b'ketianzhang1-lang' in header
            and len(header) == manifest['comparisons']['reused_header_normalized_bytes']):
        raise ValueError('Unexpected reuse header')
    if b'exact JSP000250.firstException_upper_bound N hN hlog' not in sources['upper250_bridge']:
        raise ValueError('Expected original theorem call missing')
    print('PASS all documented byte comparisons and source-call marker')
    print('Scope: provenance comparison only; no new Lean verification or priority decision.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-cache', type=Path)
    arguments = parser.parse_args()
    verify(arguments.source_cache)
