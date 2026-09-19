"""Recheck immutable source bytes and narrowly stated provenance comparisons.

Requires Python 3 and GNU patch for the historical Lean 4.19 compatibility port.
Run beside sources.json; --source-cache DIR reuses prior downloads.
This does not execute Lean, certify authorship, or establish priority/eligibility.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile
from urllib.request import Request, urlopen


def require(condition, message):
    if not condition:
        raise ValueError(message)


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
            require(value == record[field], f'{key}: {field} mismatch')
        sources[key] = data
    print(f"PASS {len(sources)} immutable files: size, SHA-256 and Git blob")

    modules636 = ['JSP000636', 'Construction', 'Lower', 'Thinning', 'Threshold', 'Upper', 'Asymptotics']
    for module in modules636:
        require(sources[f'636_{module}_prior'] == sources[f'636_{module}_selected'],
                f'636: prior {module} differs')
    print('PASS 636: all seven preceding proof modules are byte-identical')
    # Check direct source imports only, not historical independence of authorship.
    for key in [f'636_{m}_selected' for m in modules636] + ['636_endpoint']:
        for name in re.findall(rb'^import\s+(\S+)', sources[key], re.M):
            name = name.decode()
            require(name in modules636 or name == 'Mathlib' or name.startswith('Mathlib.'),
                    f'{key}: unexpected direct import {name}')
    standalone = sources['912_FullProof.lean_selected']
    imports = re.findall(rb'^import\s+(\S+)', standalone, re.M)
    require(bool(imports) and all(x == b'Mathlib' or x.startswith(b'Mathlib.') for x in imports),
            '912 standalone: unexpected direct import')
    print('PASS 636 and 912: inspected direct imports match documented scope')

    modules912 = ['FullProof.lean', 'JSP912/Construction.lean', 'JSP912/Decay.lean',
                  'JSP912/Grid.lean', 'JSP912/Main.lean', 'JSP912/Potential.lean']
    with tempfile.TemporaryDirectory(prefix='jsp912-port-') as tmp:
        root = Path(tmp)
        for module in modules912:
            target = root / module
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(sources['912_' + module.replace('/', '_') + '_recovered'])
        subprocess.run(['patch', '--batch', '--fuzz=0', '-p1', '-d', str(root)],
                       input=sources['912_port_patch'], check=True, capture_output=True)
        for module in modules912:
            require((root / module).read_bytes() == sources['912_' + module.replace('/', '_') + '_selected'],
                    f'912: published patch does not reconstruct {module}')
    print('PASS 912: published compatibility patch reconstructs all six selected proof files exactly')

    require(sources['393_seed_original'] == sources['393_seed_selected'] == sources['393_seed_verified'],
            '393: original, selected and later verified seed files differ')
    for module in ['JSP000393Complete.lean', 'UPSTREAM.json', 'lake-manifest.json']:
        require(sources[f'393_{module}_selected'] == sources[f'393_{module}_verified'],
                f'393: selected and later verified {module} differ')
    require(b'a337720331a34599114a9d4669d6518d5e608f6f' in sources['393_historical_source'],
            '393: historical submission does not identify the original seed commit')
    complete393 = sources['393_JSP000393Complete.lean_selected']
    for marker in [b'JSP000393.family k', b'JSP000393.family_counts k',
                   b'Erdos485.f_minimal', b'minimum_family_upper_bound k', b'Erdos485.erdos_485']:
        require(marker in complete393, f'393: missing source-call marker {marker!r}')
    print('PASS 393: retained original construction, submission reference, verification bindings and source-call markers')

    require(sources['728_lower_original'] == sources['728_lower_historical'] == sources['728_lower_selected'],
            '728: original, historical submission and selected lower proofs differ')
    complete728 = sources['728_JSP000728Complete.lean']
    for marker in [b'exact cameron_erdos_lower_bound N', b'\xe2\x9f\xa8cameron_erdos_lower_bound,',
                   b'maximalSets_card_eq_upstream', b'benchmark_le_allSumFreeSets N',
                   b'Erdos877.erdos_877_exponential_bound']:
        require(marker in complete728, f'728: missing source-call marker {marker!r}')
    print('PASS 728: retained lower proof is the published submission file and is used in the complete endpoint')
    print('Scope: source bindings and inspected call markers; no new Lean verification or award determination.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-cache', type=Path)
    verify(parser.parse_args().source_cache)
