"""Verify source provenance and recorded compatibility ports for seven claims.

Run with Python 3 and network access, or --source-cache DIR containing ID.source.
This does not run Lean/NaNoda or establish authorship, priority or award eligibility.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
from urllib.request import Request, urlopen


def require(condition, message):
    if not condition:
        raise ValueError(message)


def verify(cache=None):
    records = json.loads(Path(__file__).with_name('sources.json').read_text())['sources']
    sources = {}
    for row in records:
        key = row['id']
        if cache is None:
            request = Request(row['url'], headers={'User-Agent': 'JSP-source-review/1.0'})
            with urlopen(request, timeout=45) as response:
                data = response.read()
        else:
            data = (cache / (key + '.source')).read_bytes()
        actual = {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest(),
                  'git_blob_sha1': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()}
        for field, value in actual.items():
            require(value == row[field], f'{key}: {field} differs')
        require(key not in sources, 'Duplicate source record: ' + key)
        sources[key] = data
    print(f'PASS {len(records)} source snapshots: byte counts, SHA-256 and Git blobs')

    comparisons = {'later': 0, 'historical': 0, 'strict': 0}
    for key, data in sources.items():
        for suffix in comparisons:
            if key.endswith('_' + suffix):
                selected = key[:-len(suffix)] + 'selected'
                require(selected in sources, 'Missing reference: ' + selected)
                require(data == sources[selected], 'Source/configuration changed: ' + key)
                comparisons[suffix] += 1
    require(comparisons['historical'] == 12, 'Expected eleven original Lean modules and the 907 research note')
    require(comparisons['strict'] == 4, 'Expected four source/configuration bindings to the 301 strict run')
    print('PASS unchanged selected-to-later, original-to-selected and 301 strict-run bindings:', comparisons)

    counts = {140: 20, 388: 155, 554: 51, 585: 56, 725: 42, 907: 38}
    endpoints = {140: 136, 388: 477, 554: 682, 585: 717, 725: 874, 907: 1091}
    for n, count in counts.items():
        manifest = json.loads(sources[f'{n}_UPSTREAM.json_selected'])
        require(len(manifest) == count, f'{n}: upstream closure size changed')
        require(len({x['path'] for x in manifest}) == count, f'{n}: duplicate upstream path')
        name = f'ErdosProblems/Erdos{endpoints[n]}.lean'
        row = next(x for x in manifest if x['path'] == name)
        original = sources[f'{n}_upstream_endpoint']
        require(hashlib.sha256(original).hexdigest() == row['sha256'], f'{n}: upstream root digest differs')
        blob = hashlib.sha1(b'blob ' + str(len(original)).encode() + b'\0' + original).hexdigest()
        require(blob == row['git_blob_sha'], f'{n}: upstream root Git blob differs')
        port = original.decode()
        for old, new in row['renames'].items():
            port = re.sub(r'\b' + old + r'\b', new, port)
        for old, new in row['edits']:
            require(old in port, f'{n}: missing compatibility input')
            port = port.replace(old, new)
        port = row.get('port_notice', '') + port
        require(hashlib.sha256(port.encode()).hexdigest() == row['port_sha256'],
                f'{n}: recorded root compatibility transformation does not reproduce its digest')
        print(f'PASS {n}: upstream endpoint bytes and recorded compatibility transformation; {count}-entry manifest')

    require(hashlib.sha256(sources['907_note_selected']).hexdigest() ==
            '584f4a2c9687de0b5484708ce2be7f71affadd588e247fee0d6deaec7b603a14',
            '907: historical research-note binding differs')
    print('Scope: source bindings and six upstream root ports only. The full imported closures were checked by the separately linked Lean/NaNoda runs.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-cache', type=Path)
    verify(parser.parse_args().source_cache)
