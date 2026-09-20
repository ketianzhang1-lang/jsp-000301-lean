#!/usr/bin/env python3
"""Disclosed manual build equivalence for the omitted Lean 4.34 supplement module.

This is an auditor-owned adapter, not Lake. Only the one exact build argv
forms below are substituted. Every other invocation execs the real pinned
Lake binary without changing argv, proof sources, dependencies or config.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

MODULES = {
    "JSP000465Uniform": "JSP000465Uniform.lean",
}
OUT = Path("/out")


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    real_lake = os.environ.get("LEAN_VERIFY_REAL_LAKE", "")
    if not real_lake or not Path(real_lake).is_absolute():
        raise SystemExit("LEAN_VERIFY_REAL_LAKE must be the trusted absolute Lake path")
    args = sys.argv[1:]
    module = args[1][1:] if len(args) == 2 and args[0] == "build" and args[1].startswith("+") else None
    if module not in MODULES:
        os.execv(real_lake, [real_lake] + args)

    started = time.time()
    cwd = Path.cwd()
    source = cwd / MODULES[module]
    artifact = cwd / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
    command = [real_lake, "env", "lean", "-DwarningAsError=true", "-j1", "-M12000",
               "-o", str(artifact), str(source)]
    OUT.mkdir(parents=True, exist_ok=True)
    fd, log_name = tempfile.mkstemp(prefix="manual-build-" + module + "-", suffix=".log", dir=OUT)
    record = {
        "protocol": "manual-equivalence-v1",
        "module": module,
        "requested_argv": [sys.argv[0]] + args,
        "executed_argv": command,
        "cwd": str(cwd),
        "source": str(source),
        "source_sha256_before": None,
        "source_sha256_after": None,
        "output_log": log_name,
        "olean_output": str(artifact),
        "started_at_unix": started,
        "reason": "The selected Lake configuration does not register the supplement module. Compile the exact source using the original pinned Lean invocation.",
    }
    code = 127
    with os.fdopen(fd, "wb") as log:
        try:
            if (cwd / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.34.0":
                raise RuntimeError("Manual adapter is restricted to the pinned Lean 4.34 project")
            record["source_sha256_before"] = sha256(source)
            artifact.parent.mkdir(parents=True, exist_ok=True)
            # Always recompile; an earlier .olean can never count as success.
            artifact.unlink(missing_ok=True)
            child = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            assert child.stdout is not None
            while True:
                chunk = os.read(child.stdout.fileno(), 65536)
                if not chunk:
                    break
                log.write(chunk)
                sys.stdout.buffer.write(chunk)
                sys.stdout.buffer.flush()
            child.stdout.close()
            code = child.wait()
            record["compiler_exit_code"] = code
            record["source_sha256_after"] = sha256(source)
            if record["source_sha256_before"] != record["source_sha256_after"]:
                raise RuntimeError("Source changed during the explicit manual compilation")
            if code == 0 and not artifact.is_file():
                raise RuntimeError("Compiler returned zero without the requested .olean")
        except Exception as error:
            message = ("Manual build adapter error: " + str(error) + "\n").encode()
            log.write(message)
            sys.stdout.buffer.write(message)
            sys.stdout.buffer.flush()
            if code == 0 or "compiler_exit_code" not in record:
                code = 127
    record.update({
        "exit_code": code,
        "adapter_exit_code": code if code >= 0 else 128 - code,
        "seconds": time.time() - started,
        "output_log_sha256": sha256(Path(log_name)),
        "output_log_bytes": Path(log_name).stat().st_size,
        "olean_sha256": sha256(artifact) if artifact.is_file() else None,
    })
    # Append one complete record per actual intercepted build invocation.
    journal = os.open(OUT / "manual-module-builds.jsonl",
                      os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o600)
    try:
        data = (json.dumps(record, sort_keys=True) + "\n").encode()
        with os.fdopen(journal, "ab", closefd=False) as stream:
            stream.write(data)
            stream.flush()
    finally:
        os.close(journal)
    return record["adapter_exit_code"]


if __name__ == "__main__":
    sys.exit(main())
