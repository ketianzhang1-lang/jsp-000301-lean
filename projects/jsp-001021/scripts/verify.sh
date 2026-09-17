#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS=1
python3 scripts/bootstrap.py
mkdir -p evidence/generated .lake/build/lib/lean
python3 - <<'PY'
import subprocess,json
from pathlib import Path
for module in json.loads(Path('MODULES.json').read_text()):
    source=module.replace('.','/')+'.lean'
    output=Path('.lake/build/lib/lean')/(module.replace('.','/')+'.olean')
    output.parent.mkdir(parents=True,exist_ok=True)
    with Path('evidence/generated/build-'+module+'.log').open('w') as log:
        result=subprocess.run(['lake','env','lean','-DwarningAsError=true','-j1','-M14000','-o',str(output),'./'+source],stdout=log,stderr=subprocess.STDOUT)
    if result.returncode:
        print(Path('evidence/generated/build-'+module+'.log').read_text())
        raise SystemExit(result.returncode)
    print('Source compiled:',module,flush=True)
PY
python3 scripts/check_built.py
