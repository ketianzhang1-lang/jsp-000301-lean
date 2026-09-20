"""Verify GitHub ZIP digest and safely preserve immutable raw rank-11--20 evidence.

Usage: unpack_evidence.py KEY FILENAME EXPECTED_SHA256 ARTIFACT_ID RUN_ID HARNESS_COMMIT [JOB_ID]
The identity values must come from the actual GitHub API download/metadata.
Never execute any file from the archive, and never overwrite a retained attempt.
"""
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys
import zipfile

args = sys.argv[1:]
assert len(args) in (6, 7), __doc__
key, filename, expected_sha, artifact_id, run_id, harness_commit = args[:6]
assert re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9-]*', key), 'Unsafe group key'
assert PurePosixPath(filename).name == filename and '\\' not in filename, 'Unsafe ZIP filename'
assert re.fullmatch(r'[0-9a-f]{64}', expected_sha), 'Expected GitHub SHA256 is required'
assert re.fullmatch(r'[0-9a-f]{40}', harness_commit), 'Expected full harness commit is required'
base = Path(__file__).resolve().parent / 'evidence' / key
archive = base / filename
h = hashlib.sha256()
with archive.open('rb') as stream:
    for chunk in iter(lambda: stream.read(1024 * 1024), b''):
        h.update(chunk)
actual = h.hexdigest()
assert actual == expected_sha, 'Downloaded artifact digest mismatch'
destination = base / 'remote'
assert not destination.exists(), 'Do not overwrite an earlier evidence tree'
with zipfile.ZipFile(archive) as z:
    names = set()
    for info in z.infolist():
        p = PurePosixPath(info.filename)
        assert not p.is_absolute() and '..' not in p.parts and '\\' not in info.filename
        assert info.filename not in names, 'Duplicate ZIP member'
        names.add(info.filename)
        kind = (info.external_attr >> 16) & 0o170000
        assert kind in (0, 0o100000, 0o040000), 'Archive contains nonregular file'
    assert 'SHA256SUMS.json' in names, 'Missing checksum inventory'
    z.extractall(destination)
sums = json.loads((destination / 'SHA256SUMS.json').read_text())
files = {str(p.relative_to(destination)) for p in destination.rglob('*') if p.is_file()}
assert set(sums) == files - {'SHA256SUMS.json'}, 'Checksum inventory is not exact'
for name, sha in sums.items():
    p = PurePosixPath(name)
    assert not p.is_absolute() and '..' not in p.parts and '\\' not in name
    path = destination / name
    assert path.resolve().is_relative_to(destination.resolve()) and not path.is_symlink()
    assert hashlib.sha256(path.read_bytes()).hexdigest() == sha, name
if (destination / 'HARNESS_COMMIT').exists():
    assert (destination / 'HARNESS_COMMIT').read_text().strip() == harness_commit
record = {'artifact_id': int(artifact_id), 'workflow_run': int(run_id),
          'harness_commit': harness_commit, 'filename': filename,
          'sha256': actual, 'bytes': archive.stat().st_size,
          'internal_files_verified': len(sums)}
if len(args) == 7:
    record['workflow_job'] = int(args[6])
assert record['artifact_id'] > 0 and record['workflow_run'] > 0
(base / 'artifact-receipt.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({'key': key, **record}))
