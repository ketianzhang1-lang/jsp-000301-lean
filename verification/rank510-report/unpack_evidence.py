"""Verify downloaded ZIP identity and extract only relative regular paths."""
import hashlib
import json
from pathlib import Path, PurePosixPath
import sys
import zipfile

key, filename, expected_sha, artifact_id, run_id, harness_commit = sys.argv[1:]
base = Path(__file__).resolve().parent / 'evidence' / key
archive = base / filename
actual = hashlib.sha256(archive.read_bytes()).hexdigest()
assert actual == expected_sha, 'Downloaded artifact digest mismatch'
destination = base / 'remote'
assert not destination.exists(), 'Do not overwrite an earlier evidence tree'
with zipfile.ZipFile(archive) as z:
    for info in z.infolist():
        p = PurePosixPath(info.filename)
        assert not p.is_absolute() and '..' not in p.parts
        assert (info.external_attr >> 16) & 0o170000 != 0o120000, 'No symlinks'
    z.extractall(destination)
sums = json.loads((destination / 'SHA256SUMS.json').read_text())
for name, sha in sums.items():
    path = destination / name
    assert path.resolve().is_relative_to(destination.resolve())
    assert hashlib.sha256(path.read_bytes()).hexdigest() == sha, name
record = {'artifact_id': int(artifact_id), 'workflow_run': int(run_id),
          'harness_commit': harness_commit, 'filename': filename,
          'sha256': actual, 'bytes': archive.stat().st_size,
          'internal_files_verified': len(sums)}
(base / 'artifact-receipt.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({'key': key, **record}))
