#!/usr/bin/env python3
"""Read-only inspection of actual rank-11--20 CI artifacts; never executes Lean.

Usage: python3 verify-rank1120/inspect_evidence.py [--key 585 ...] [--output FILE]
Defaults to evidence/<key>/remote below this script's directory. Missing files
are failures. A successful result covers mechanical receipts only, not semantics
or prize eligibility. Negative-control exit status is normally enforced by the
successful original verifier, not separately recorded; that distinction is kept.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys

ROOT = Path(__file__).resolve().parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
OFFICIAL_RULES_COMMIT = "38e63c424c7196f8d4ceb664c5c25f0c0529d5e2"
OFFICIAL_AUDIT_SHA256 = "5db45dddcb4d588bc27e7c7161fbca5cedaa3e73e1c40843d21f5a214323cd07"


class EvidenceError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise EvidenceError(message)


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def read_json(path):
    require(path.is_file(), "Missing JSON: " + str(path))
    return json.loads(path.read_text())


def read_text(path):
    require(path.is_file(), "Missing text: " + str(path))
    return path.read_text(errors="strict")


def relative_file(root, relative):
    pp = PurePosixPath(relative)
    require(not pp.is_absolute() and ".." not in pp.parts and relative not in {"", "."},
            "Unsafe evidence path: " + relative)
    path = root.joinpath(*pp.parts)
    require(path.is_file() and not path.is_symlink(), "Missing/unsafe evidence file: " + str(path))
    require(path.resolve().is_relative_to(root.resolve()), "Evidence path escapes root: " + relative)
    return path


def recorded_output(root, recorded):
    require(recorded.startswith("/out/"), "Unexpected recorded output path: " + recorded)
    return relative_file(root, recorded.removeprefix("/out/"))


def axiom_list(text, name):
    found = re.findall(r"'" + re.escape(name) + r"' depends on axioms:\s*\[([^]]*)\]", text)
    if found:
        values = [{v.strip() for v in item.split(",") if v.strip()} for item in found]
        require(all(v == values[0] for v in values), "Conflicting axiom reports: " + name)
        return values[0]
    require("'" + name + "' does not depend on any axioms" in text,
            "Missing actual axiom report: " + name)
    return set()


def check_command(root, record):
    require(record.get("exit_code") == 0, "Command did not exit zero: " + repr(record.get("argv")))
    if "status" in record:
        require(record["status"] == "ok", "Command status not ok: " + repr(record.get("argv")))
    if "log" in record:
        log = recorded_output(root, record["log"])
        require(digest(log) == record.get("log_sha256"), "Command log hash mismatch: " + str(log))


def check_preflight(result, cfg, label):
    require(result.get("ready_for_target_checks") is True and result.get("issues") == [],
            label + " preflight incomplete: " + repr(result.get("issues")))
    require(result.get("head") == cfg["commit"], label + " commit mismatch")
    require(result.get("toolchain_file") == cfg["toolchain"], label + " toolchain mismatch")


URL_SPELLING_WARNING = "warning: manifest out of date: git url of dependency 'mathlib' changed; use `lake update mathlib` to update it"
REVIEWED_554_POLICY = "reviews/554/inspector-source-diagnostics.json"
REVIEWED_554_POLICY_SHA256 = "753e353352d5f6d98960ef2f5413ff3b723e241e3028e9d11d0c38e11c4926e1"


def reviewed_554_source_diagnostics(root):
    """Review four fixed import-path diagnostics without modifying source or logs.

    The official skill requires successful checks and disclosed diagnostics, not
    zero warnings. The lead-reviewed immutable policy records the exact compiler
    implementation and pure Mathlib forwarding shim. No general warning waiver
    or suppression is available here.
    """
    policy_path = relative_file(ROOT, REVIEWED_554_POLICY)
    require(digest(policy_path) == REVIEWED_554_POLICY_SHA256, "554 diagnostic policy changed")
    policy = read_json(policy_path)
    require(policy["review_status"] == "lead_confirmed_nonblocking_import_path_diagnostics" and
            policy["official_rules_commit"] == OFFICIAL_RULES_COMMIT and
            policy["proof_commit"] == read_text(root / "SOURCE_COMMIT").strip() ==
            "21fcf006fd68b0bead9f979b704c92032f05cba8", "554 diagnostic review scope differs")
    dependencies = read_json(root / "dependencies.log")
    require(dependencies["mathlib"] == policy["mathlib_commit"] ==
            "5ed2965256430c3649e86755f9576b54eca72435", "554 diagnostic Mathlib version differs")
    require(policy["lean_commit"] == "293d5d0c0c3f3dded4688b3ccd6a33939ac5102b" and
            policy["lean_commit"] in read_text(root / "versions.log"), "554 diagnostic Lean version differs")
    shim = policy["mathlib_forwarding_source"]
    require(shim == 'module -- shake: keep-all\n\npublic import Mathlib.Basic.Real.Basic\n\ndeprecated_module (since := "2026-08-27")\n' and
            hashlib.sha256(shim.encode()).hexdigest() ==
            "a1d6fa90c0e6ddc98b82933e33801713f937030bc1d70052afb6794c3637a65d",
            "554 deprecated import is not the reviewed pure forwarding shim")
    require(read_json(root / "original-clean-verifier.json")["exit_code"] == 0,
            "554 original verifier did not pass")
    verifier = policy["original_verifier"]
    require(digest(relative_file(root / "checked-source", verifier["source_path"])) ==
            verifier["source_sha256"], "554 original verifier source changed")
    original_log = read_text(root / "original-clean-verifier.log")
    before = read_json(root / "source-before.json")
    records = policy["reviewed_source_diagnostics"]
    require(len(records) == 4 and len({row["source_path"] for row in records}) == 4,
            "554 review must identify exactly four distinct source diagnostics")
    for row in records:
        source = relative_file(root / "checked-source", row["source_path"])
        log = relative_file(root, row["log_path"])
        require(before[row["source_path"]] == digest(source) == row["source_sha256"],
                "554 reviewed import source/hash differs")
        require(source.read_text().splitlines()[row["source_line"] - 1] == "import Mathlib.Data.Real.Basic",
                "554 reviewed import line differs")
        require(digest(log) == row["log_sha256"] and read_text(log) == row["exact_warning_text"],
                "554 diagnostic block differs or contains an additional diagnostic")
        require("Passed: " + " ".join(row["compiler_argv"]) in original_log and
                row["compiler_argv"][3:6] == ["-DwarningAsError=true", "-j1", "-M8000"],
                "554 reviewed module lacks its actual successful strict compiler invocation")
    return records


def compiler_diagnostics(root, text, *, source_diagnostics=(), source_log=None):
    for diagnostic in source_diagnostics:
        if source_log == diagnostic["log_path"] and text == diagnostic["exact_warning_text"]:
            return None
    # Some selected historical lakefiles spell the same Mathlib Git URL with a
    # .git suffix, while their immutable manifests omit it. This reviewed Lake
    # metadata warning is not a Lean source diagnostic. Never update the manifest
    # to silence it. Actual nine-package revisions are independently checked below.
    if URL_SPELLING_WARNING in text.splitlines():
        lakefile = read_text(root / "checked-source/lakefile.lean")
        declared = re.findall(r'require\s+mathlib\s+from\s+git\s+"([^"\n]+)"', lakefile)
        pinned = [p["url"] for p in read_json(root / "checked-source/lake-manifest.json")["packages"]
                  if p["name"] == "mathlib"]
        require(len(declared) == len(pinned) == 1 and
                declared[0].removesuffix(".git").rstrip("/") == pinned[0].removesuffix(".git").rstrip("/") ==
                "https://github.com/leanprover-community/mathlib4",
                "Unreviewed Lake dependency-URL mismatch")
        text = "\n".join(line for line in text.splitlines() if line != URL_SPELLING_WARNING)
    return re.search(r"(^|\n).*\b(?:error|warning):", text)


def inspect_key(key, root, expected_cfg):
    require(root.is_dir(), "Missing evidence directory: " + str(root))
    sums = read_json(root / "SHA256SUMS.json")
    require(bool(sums), "Empty SHA256SUMS")
    files = {str(p.relative_to(root)) for p in root.rglob("*") if p.is_file()}
    require(set(sums) == files - {"SHA256SUMS.json"},
            "SHA256SUMS coverage differs; missing=" + repr(sorted(files - set(sums) - {"SHA256SUMS.json"})) +
            "; extra=" + repr(sorted(set(sums) - files)))
    for name, sha in sums.items():
        require(re.fullmatch(r"[0-9a-f]{64}", sha) is not None, "Invalid SHA256: " + name)
        require(digest(relative_file(root, name)) == sha, "Artifact file checksum mismatch: " + name)

    cfg = read_json(root / "harness/config.json")[key]
    require(cfg == expected_cfg, "Artifact config differs from the selected group configuration")
    schema = cfg["inspection"]
    require(isinstance(schema["original_target_count"], int) and schema["original_target_count"] > 0,
            "Missing positive expected original target count")
    require(read_text(root / "OFFICIAL_RULES_COMMIT").strip() == OFFICIAL_RULES_COMMIT,
            "Wrong official rules checkout")
    receipt = read_json(root.parent / "artifact-receipt.json")
    require(read_text(root / "HARNESS_COMMIT").strip() == receipt["harness_commit"],
            "Downloaded artifact was not produced by the recorded harness commit")
    archive = relative_file(root.parent, receipt["filename"])
    require(digest(archive) == receipt["sha256"] and archive.stat().st_size == receipt["bytes"],
            "Downloaded ZIP differs from its GitHub artifact receipt")
    require(receipt["internal_files_verified"] == len(sums) and receipt["artifact_id"] > 0 and
            receipt["workflow_run"] > 0, "Invalid artifact identity/count receipt")
    require(read_text(root / "SOURCE_COMMIT").strip() == cfg["commit"], "SOURCE_COMMIT mismatch")
    tip = read_text(root / "BRANCH_TIP").strip()
    require(re.fullmatch(r"[0-9a-f]{40}", tip) is not None, "Invalid branch-tip receipt")

    manifest = read_json(root / "targets.json")
    archived_manifest = read_json(root / "harness" / (key + "-targets.json"))
    selected_manifest = read_json(ROOT / "harness" / (key + "-targets.json"))
    require(archived_manifest == selected_manifest, "Archived target manifest differs from selected local harness")
    require(manifest["targets"] == archived_manifest["targets"] and
            manifest["problems"] == archived_manifest["problems"], "Executed target manifest differs from archived harness")
    for field in ["commit", "toolchain"]:
        require(manifest["project"][field] == cfg[field], "Manifest project mismatch: " + field)
    targets = manifest["targets"]
    names = [t["declaration"] for t in targets]
    require(len(names) == len(set(names)), "Duplicate target declaration")
    for field in ["total_targets", "total_target_count"]:
        if field in cfg:
            require(len(names) == cfg[field], "Configured total target count differs: " + field)
    original_names = [t["declaration"] for t in targets if t["role"] == "theorem"]
    require(len(original_names) == schema["original_target_count"], "Original target coverage changed")

    original = read_json(root / "original-completion.json")
    require(original.get("commit") == cfg["commit"] and original.get("original_clean_verification") == "completed"
            and original.get("inputs_stable") is True, "Original clean-verification completion missing/mismatched")
    mechanical = read_json(root / "mechanical-completion.json")
    require(mechanical.get("proof_commit") == cfg["commit"] and mechanical.get("mechanical_checks") == "completed"
            and mechanical.get("targets") == len(targets) and mechanical.get("network_during_verification") == "disabled",
            "Mechanical completion missing/mismatched")

    stages = {}
    required_stages = ["versions", "build-exporter", "build-checker", "original-clean-verifier", "official-preflight",
                       "official-audit", "bridge-kernel", "independent-nanoda", "dependencies", "final-status", "compress-export"]
    required_stages += ["prepare-dependencies-" + str(i) for i, _ in enumerate(cfg["prepare_commands"])]
    if cfg.get("bootstrap"):
        required_stages.append("bootstrap")
    required_stages += ["extra-kernel-" + x for x in cfg.get("extra_kernel_prefixes", [])]
    for name in required_stages:
        record = read_json(root / (name + ".json"))
        check_command(root, record)
        read_text(root / (name + ".log"))
        stages[name] = record
    # The newer runner emits bridge-precheck.json through run(); accept the
    # explicitly named command-receipt spelling as well. Older runs genuinely
    # did not have this stage. A new runner cannot omit its promised receipt.
    precheck_records = [p for p in [root / "bridge-precheck.json", root / "bridge-precheck-command.json"]
                        if p.is_file()]
    archived_runner = read_text(root / "harness/runner.py")
    precheck_expected = re.search(r"run\(['\"]bridge-precheck['\"]", archived_runner) is not None
    require(not precheck_expected or bool(precheck_records), "New runner's bridge precheck receipt is missing")
    require(len(precheck_records) <= 1, "Ambiguous duplicate bridge precheck receipts")
    if precheck_records:
        record = read_json(precheck_records[0])
        check_command(root, record)
        bridge_source = str(PurePosixPath(manifest["project"]["root"]) / cfg["bridge_path"])
        bridge_output = str(PurePosixPath(manifest["project"]["root"]) / ".lake/build/lib/lean" /
                            (cfg["bridge_module"].replace(".", "/") + ".olean"))
        expected_argv = ["lake", "env", "lean", "-DwarningAsError=true", "-j1", "-M12000",
                         "-o", bridge_output, bridge_source]
        require(record.get("argv") == expected_argv and record.get("cwd") == manifest["project"]["root"],
                "Bridge precheck did not use the exact strict compiler command/source/output")
        precheck_log = read_text(root / "bridge-precheck.log")
        require(not compiler_diagnostics(root, precheck_log),
                "Strict bridge precheck contains a diagnostic failure")
        stages["bridge-precheck"] = record
    for tool, commit in [("exporter", cfg["exporter_commit"]), ("checker", cfg["nanoda_commit"])]:
        for op in ["init", "fetch", "checkout"]:
            record = read_json(root / (op + "-" + tool + ".json"))
            check_command(root, record)
            if op in {"fetch", "checkout"}:
                require(commit in record["argv"], "Wrong pinned external tool: " + tool)

    official_sha = digest(root / "official-skill/scripts/audit.py")
    require(digest(root / "harness/audit.py") == official_sha == digest(ROOT / "harness/audit.py") == OFFICIAL_AUDIT_SHA256,
            "Official audit implementation differs from selected trusted script")
    standalone = read_json(root / "preflight/result.json")
    check_preflight(standalone, cfg, "Standalone")
    require(standalone["exit_code"] == 0 and standalone["script_sha256"] == official_sha,
            "Standalone preflight receipt mismatch")
    audit = read_json(root / "audit/result.json")
    require(audit.get("exit_code") == 0 and audit.get("inputs_stable") is True and
            audit.get("mechanical_status") == "standard_axioms_only", "Official audit not complete/standard-only")
    require(audit["script_sha256"] == official_sha, "Executed audit script hash differs from official source")
    require(audit["manifest_sha256"] == digest(root / "audit/manifest.json"), "Executed manifest hash mismatch")
    require(read_json(root / "audit/manifest.json") == manifest, "Audit parsed a different target manifest")
    check_preflight(audit["preflight"], cfg, "Before audit")
    check_preflight(audit["after"], cfg, "After audit")
    require(audit["preflight"]["file_sha256"] == audit["after"]["file_sha256"] == standalone["file_sha256"],
            "Preflight source/configuration hashes changed")
    require([r["declaration"] for r in audit["targets"]] == names, "Audit target list omitted/reordered declarations")
    require(len(audit["commands"]) == 2 + 3 * len(targets), "Unexpected official command coverage")
    for command in audit["commands"]:
        check_command(root, command)
    axiom_results = {}
    for target, row in zip(targets, audit["targets"]):
        require(row["id"] == target["id"] and row["status"] == "standard_axioms_only", "Failed target: " + target["declaration"])
        require(len(row["commands"]) == 3, "Missing target build/source/declaration command")
        for command in row["commands"]:
            check_command(root, command)
        build, source_check, printed = row["commands"]
        require(build["argv"][-2:] == ["build", "+" + target["module"]], "Wrong explicit target module")
        require(source_check["argv"][-1] == manifest["project"]["root"] + "/" + target["source"], "Wrong target source path")
        audit_file = recorded_output(root, row["audit_file"])
        require(digest(audit_file) == row["audit_sha256"], "Generated audit file hash mismatch")
        generated = read_text(audit_file)
        for wanted in ["import " + target["module"], "#check @" + target["declaration"],
                       "#print " + target["declaration"], "#print axioms " + target["declaration"]]:
            require(wanted in generated, "Missing generated audit directive: " + wanted)
        actual = axiom_list(read_text(recorded_output(root, printed["log"])), target["declaration"])
        require(actual == set(row["axioms"]) and actual <= ALLOWED_AXIOMS, "Axiom evidence mismatch: " + target["declaration"])
        axiom_results[target["declaration"]] = sorted(actual)

    tracked_before = read_json(root / "tracked-before-prepare.json")
    tracked_after = read_json(root / "tracked-after-prepare.json")
    before = read_json(root / "source-before.json")
    after = read_json(root / "source-after.json")
    require(tracked_before == tracked_after and before == after, "Original source/configuration hashes changed")
    require(all(before.get(n) == v for n, v in tracked_after.items()), "Source snapshot does not cover every tracked input")
    for path in (root / "checked-source").rglob("*"):
        if path.is_file():
            name = str(path.relative_to(root / "checked-source"))
            require(before.get(name) == digest(path), "Checked-source snapshot hash mismatch: " + name)
    for name, sha in before.items():
        if name.endswith((".lean", ".json", ".toml", ".py", ".sh")) and not name.startswith("evidence"):
            require(digest(relative_file(root / "checked-source", name)) == sha,
                    "Incomplete checked source/configuration/script snapshot: " + name)
    for target in targets:
        observed_hash = audit["preflight"]["file_sha256"][target["source"]]
        if target["role"] == "bridge":
            require(target["source"] == cfg["bridge_path"] and
                    observed_hash == digest(root / "harness" / cfg["bridge_file"]) ==
                    digest(ROOT / "harness" / cfg["bridge_file"]), "Bridge source binding mismatch")
        else:
            require(before.get(target["source"]) == observed_hash, "Original target not bound to full source snapshot")
            require(digest(relative_file(root / "checked-source", target["source"])) == observed_hash,
                    "Missing original checked target source")
        if "definition_source" in target:
            definition_source = target["definition_source"]
            definition_sha = target.get("definition_sha256")
            if definition_sha is None:
                pinned = [entry for entry in read_json(root / "checked-source/UPSTREAM.json")
                          if entry["path"] == definition_source]
                require(len(pinned) == 1, "Missing/ambiguous immutable definition source: " + definition_source)
                definition_sha = pinned[0]["port_sha256"]
            require(definition_sha is not None and before.get(definition_source) == definition_sha,
                    "Routed target definition is not bound to original source snapshot: " + target["declaration"])
            require(digest(relative_file(root / "checked-source", definition_source)) == definition_sha,
                    "Routed target definition source/hash mismatch: " + target["declaration"])

    locked = read_json(root / "checked-source/lake-manifest.json")
    dependencies = read_json(root / "dependencies.log")
    require(dependencies == {p["name"]: p["rev"] for p in locked["packages"]}, "Actual dependency SHAs differ from manifest")
    version_logs = "\n".join(audit.get("tool_versions", []))
    require("Lean (version " + cfg["lean_version"] + "," in version_logs, "Actual Lean version mismatch")
    image = read_json(root / "image-inspect.json")[0]
    require(re.fullmatch(r"sha256:[0-9a-f]{64}", image["Id"]) is not None, "Missing Docker image digest")
    require(image["Config"]["User"] in {"verifier", "10001", "10001:10001"}, "Image is not configured for non-root checking")
    versions_text = read_text(root / "versions.log")
    require("uid=10001(verifier)" in versions_text, "Actual verification user was not the isolated non-root account")
    workflow = read_text(root / "workflow.yml")
    require(workflow.count("--network none") >= 3 and workflow.count("--cap-drop ALL") >= 4 and
            workflow.count("--security-opt no-new-privileges") >= 4 and
            workflow.count('evidence/tools:/out/tools:ro') >= 3,
            "Executed workflow does not specify the required offline/read-only checker stages")
    require(any("leanprover--lean4---v" + cfg["lean_version"] + "/bin" in e for e in image["Config"]["Env"]),
            "Docker toolchain PATH does not match selected release")

    specs = schema["evidence"]
    require(bool(specs), "No original evidence specifications")
    expected_dirs = ["fresh-project-evidence"] + ["fresh-extra-" + str(i)
                    for i in range(1, 1 + len(cfg.get("additional_evidence_dirs", [])))]
    require([spec["directory"] for spec in specs] == expected_dirs,
            "Original evidence specification does not cover each fresh directory exactly once")
    verification_records, kernel_logs, controls = [], [], []
    source_diagnostics = reviewed_554_source_diagnostics(root) if key == "554" else []
    original_printed_names, original_axiom_outputs = set(), []
    for spec in specs:
        directory = root / spec["directory"]
        require(directory.is_dir(), "Missing original verifier evidence directory")
        record = read_json(directory / spec["verification_json"]) if spec.get("verification_json") else None
        modules = None
        if record is not None:
            expected_status = spec.get("status_value")
            require(record.get("status") == expected_status if expected_status else record.get("status") in {"passed", "PASS"}, "Original verifier JSON did not report expected success")
            require(set(record.get("allowed_axioms", [])) == ALLOWED_AXIOMS,
                    "Original verifier's disclosed axiom policy differs from standard allowlist")
            for source, sha in record.get("source_sha256", {}).items():
                require(before.get(source) == sha, "Original verifier source hash differs: " + source)
            for field in ["preparation_head", "verification_commit", "repository_head"]:
                if field in record:
                    require(record[field] == cfg["commit"], "Original verifier checked a different commit: " + field)
            if "dependency_count" in record:
                require(record["dependency_count"] == len(dependencies), "Original dependency count differs")
            modules = record.get(spec["modules_field"]) if "modules_field" in spec else record.get("modules_compiled", record.get("modules"))
            target_field = spec.get("targets_field", "audited_targets" if "audited_targets" in record else None)
            if target_field:
                require(record[target_field] == original_names,
                        "Original JSON ordered target list differs from official audit manifest")
            count_field = spec.get("target_count_field", "axiom_reports")
            if count_field in record:
                require(record[count_field] == spec.get("target_count", schema["original_target_count"]),
                        "Original verification target count differs")
            if spec.get("supplement_module"):
                require(record["original_proof_commit"] in cfg.get("git_history_required", []),
                        "Supplement verifier used a different base proof commit")
                prefix = cfg["project"].rstrip("/") + "/"
                for path, sha in record["original_source_sha256"].items():
                    require(path.startswith(prefix) and before.get(path.removeprefix(prefix)) == sha,
                            "Supplement's original-source binding differs: " + path)
                require(record["supplement_sha256"] == before.get(spec["supplement_module"] + ".lean"),
                        "Supplement module does not match its immutable source hash")
            verification_records.append(record)
        if spec.get("modules_source"):
            modules_from_source = read_json(root / "checked-source" / spec["modules_source"])
            modules_from_source += spec.get("additional_modules", [])
            if modules is not None:
                require(modules == modules_from_source, "Original module list differs from pinned source manifest")
            modules = modules_from_source
        elif modules is None:
            modules = spec.get("modules")
        require(isinstance(modules, list) and len(modules) == spec["module_count"] and
                len(modules) == len(set(modules)), "Missing/incorrect complete original module list")
        for module in modules:
            path = module.replace(".", "/") + ".lean"
            require(path in before, "Original compiled module missing from frozen source hashes: " + module)
            build_log_pattern = spec.get("build_log_pattern", "build-{module}.log" if record is not None and
                                         ("modules_compiled" in record or "modules" in record) else None)
            if build_log_pattern:
                log = relative_file(directory, build_log_pattern.format(module=module))
                require(not compiler_diagnostics(root, read_text(log), source_diagnostics=source_diagnostics,
                                                 source_log=str(log.relative_to(root))),
                        "Original strict module compilation has a diagnostic failure: " + module)
        native_log = spec.get("native_build_log", "build.log" if record is None else None)
        if native_log:
            build_log = read_text(relative_file(directory, native_log))
            require(not compiler_diagnostics(root, build_log),
                    "Original native Lake clean build has a diagnostic failure")
            for module in modules:
                require(module in build_log, "Native clean build log does not name compiled module: " + module)
        require(bool(spec.get("kernel_logs")), "No original kernel replay coverage specified")
        combined_kernel_text = ""
        for name in spec["kernel_logs"]:
            path = relative_file(directory, name)
            text = read_text(path)
            require(not re.search(r"(^|\n).*\berror:", text), "Original kernel log contains an error")
            combined_kernel_text += text + "\n"
            kernel_logs.append(str(path.relative_to(root)))
        if spec.get("kernel_markers"):
            observed = re.findall(r"(?m)^KERNEL REPLAY .+$", combined_kernel_text)
            require(observed == spec["kernel_markers"], "Combined original replay log omits/reorders modules")
        require(bool(spec.get("negative_logs")), "No original false-arithmetic control specified")
        for name in spec["negative_logs"]:
            path = relative_file(directory, name)
            text = read_text(path)
            proposition = spec.get("negative_proposition")
            if proposition is None:
                original_control_source = root / "checked-source/scripts/check_built.py"
                proposition = "2 + 2 = 5" if original_control_source.is_file() and                     "example : (2 : Nat) + 2 = 5 := by decide" in read_text(original_control_source) else "1 = 0"
            require(proposition in {"1 = 0", "2 + 2 = 5"}, "Unreviewed negative-control proposition")
            mathematical_failure = (r"error:\s*Tactic\s+[`']decide[`']\s+proved that the proposition\s+" +
                                    r"\s*".join(re.escape(token) for token in proposition.split()) + r"\s+is false")
            require(re.search(mathematical_failure, text),
                    "Negative control lacks the intended false-arithmetic rejection: " + str(path))
            controls.append({"log": str(path.relative_to(root)), "expected_exit": "nonzero",
                             "proposition": proposition,
                             "exit_evidence": "mathematical Lean error; nonzero exit enforced by successful original verifier",
                             "separate_exit_code_recorded": False})
        for output in spec["axiom_outputs"]:
            log_path = relative_file(directory, output["log"])
            source = output["source"]
            if source.startswith("evidence:"):
                source_path = relative_file(directory, source.removeprefix("evidence:"))
            elif source.startswith("harness:"):
                source_path = relative_file(root / "harness", source.removeprefix("harness:"))
                require(digest(source_path) == digest(ROOT / "harness" / source.removeprefix("harness:")),
                        "Auditor-owned original axiom source changed")
            else:
                source_path = relative_file(root / "checked-source", source)
            expected_names = re.findall(r"^#print axioms (\S+)", read_text(source_path), re.M)
            require(bool(expected_names) and len(expected_names) == len(set(expected_names)),
                    "Empty/duplicate original audit directives: " + source)
            text = read_text(log_path)
            observed_names = re.findall(r"'([^']+)' (?:depends on axioms:|does not depend on any axioms)", text)
            require(observed_names == expected_names,
                    "Fresh original axiom output does not exactly match its directives: " + output["log"])
            for name in expected_names:
                require(axiom_list(text, name) <= ALLOWED_AXIOMS, "Original closure has nonstandard axioms: " + name)
            original_printed_names.update(expected_names)
            original_axiom_outputs.append({"log": str(log_path.relative_to(root)), "source": source,
                                           "targets": len(expected_names)})
        if spec.get("summary_json"):
            summary = read_json(directory / spec["summary_json"])
            require(summary["modules"] == modules and summary["axiom_targets"] == original_names,
                    "Auditor-owned original verifier summary has different coverage")
            require(summary["dependency_revisions"] == dependencies and summary["proof_files_modified"] is False,
                    "Auditor-owned original verifier summary changed dependencies/proof")
            require(summary["negative_control_exit_code"] != 0, "Auditor-owned negative control accepted false arithmetic")
    require(original_printed_names == set(original_names),
            "Fresh original axiom outputs do not cover exactly all submitted targets")

    exporter = read_json(root / "export-command.json")
    check_command(root, exporter)
    require(stages["bridge-kernel"]["argv"][-1] == cfg["bridge_module"], "Wrong bridge kernel-replay module")
    require(stages["independent-nanoda"]["argv"] ==
            ["/out/tools/checker/target/release/nanoda_bin", "/out/nanoda-config.json"],
            "Wrong independent checker invocation")
    require(exporter["argv"][-len(names):] == names and cfg["bridge_module"] in exporter["argv"],
            "Exporter omitted a target or imported another module")
    require((root / "export.ndjson.gz").stat().st_size > 0, "Empty external export")
    nc = read_json(root / "nanoda-config.json")
    require(nc.get("pp_declars") == names and set(nc.get("permitted_axioms", [])) == ALLOWED_AXIOMS and
            nc.get("unpermitted_axiom_hard_error") is True, "NaNoda target/axiom configuration differs")
    success = re.fullmatch(r"\s*Checked ([0-9]+) declarations with no errors\s*", read_text(root / "independent-nanoda.log"))
    require(success is not None and int(success[1]) > len(names), "Missing actual successful external checker output")
    printed = read_text(root / "nanoda-statements.txt")
    for name in names:
        require(re.search(r"(?m)^(?:theorem|def|axiom|opaque) " + re.escape(name) + r"(?:\s|[.{:(])", printed),
                "Missing independently printed declaration: " + name)

    manual_records = []
    if cfg.get("lake_adapter"):
        approved = {"465-uniform": [["build", "+JSP000465Uniform"]],
                    "897-stability": [["build", "+JSP000897Stability"]]}
        require(key in approved and cfg["lake_adapter"]["intercepted_argv"] == approved[key],
                "Unexpected/unreviewed manual build adapter scope")
        manual = read_json(root / "manual-equivalence.json")
        require(manual["scope"] == cfg["lake_adapter"] and manual["official_audit_script_unchanged"] is True and
                manual["proof_lakefile_unchanged"] is True, "Manual equivalence disclosure differs from selected config")
        require(manual["adapter_sha256"] == digest(root / "manual-lake-adapter") ==
                digest(root / "harness" / cfg["lake_adapter"]["file"]) ==
                digest(ROOT / "harness" / cfg["lake_adapter"]["file"]), "Manual adapter source hash mismatch")
        real_lake = manual["real_lake"]
        require(real_lake == "/opt/elan/toolchains/leanprover--lean4---v" + cfg["lean_version"] + "/bin/lake",
                "Manual compilation used a different Lake executable")
        manual_records = [json.loads(line) for line in read_text(root / "manual-module-builds.jsonl").splitlines()]
        modules = {a[1].removeprefix("+") for a in cfg["lake_adapter"]["intercepted_argv"]}
        expected_counts = Counter(t["module"] for t in targets if t["module"] in modules)
        require(Counter(r["module"] for r in manual_records) == expected_counts,
                "Manual equivalent compilations omit/duplicate official target builds")
        require(len({r["output_log"] for r in manual_records}) == len(manual_records),
                "Manual target compilations reused an earlier log")
        for row in manual_records:
            require(row.get("exit_code") == row.get("compiler_exit_code") == row.get("adapter_exit_code") == 0,
                    "Manual target compilation did not exit zero")
            require(row["protocol"] == "manual-equivalence-v1" and row["cwd"] == manifest["project"]["root"],
                    "Manual target compilation did not use the recorded protocol/project")
            require(row["requested_argv"] == [manual["adapter"], "build", "+" + row["module"]],
                    "Manual adapter intercepted unexpected arguments")
            source = next(t["source"] for t in targets if t["module"] == row["module"])
            source_path = str(PurePosixPath(manifest["project"]["root"]) / source)
            object_path = str(PurePosixPath(manifest["project"]["root"]) / ".lake/build/lib/lean" /
                              (row["module"].replace(".", "/") + ".olean"))
            require(row["executed_argv"] == [real_lake, "env", "lean", "-DwarningAsError=true", "-j1", "-M12000",
                                              "-o", object_path, source_path],
                    "Manual target build was not the exact strict compiler/source/output command")
            require(row["source"] == source_path and row["olean_output"] == object_path,
                    "Manual target paths differ from official audited source/output")
            require(row["source_sha256_before"] == row["source_sha256_after"] ==
                    audit["preflight"]["file_sha256"][source], "Manual compilation source changed or differs from audit")
            output = recorded_output(root, row["output_log"])
            require(digest(output) == row["output_log_sha256"] and output.stat().st_size == row["output_log_bytes"],
                    "Manual target compiler log hash/size mismatch")
            require(not compiler_diagnostics(root, read_text(output)),
                    "Manual strict target compilation contains a diagnostic failure")
            require(re.fullmatch(r"[0-9a-f]{64}", row.get("olean_sha256", "")) is not None,
                    "Manual target compilation lacks its output artifact hash")

    return {"status": "mechanical_evidence_validated", "semantic_verdict": "requires_separate_review",
            "proof_commit": cfg["commit"], "branch_tip": tip, "target_count": len(targets),
            "original_target_count": len(original_names), "axioms": axiom_results,
            "source_inputs_stable": True, "dependency_count": len(dependencies), "dependencies": dependencies,
            "nanoda_declarations": int(success[1]), "official_script_sha256": official_sha,
            "manifest_sha256": audit["manifest_sha256"], "image_id": image["Id"],
            "artifact_files_hashed": len(sums), "original_verification_records": verification_records,
            "original_kernel_logs": kernel_logs, "original_axiom_outputs": original_axiom_outputs,
            "negative_controls": controls,
            "strict_bridge_precheck": "validated" if precheck_records else "absent_in_older_runner",
            "bridge_source_sha256": audit["preflight"]["file_sha256"][cfg["bridge_path"]],
            "manual_equivalent_builds": len(manual_records),
            "reviewed_infrastructure_warnings": [URL_SPELLING_WARNING] if precheck_records and
                    URL_SPELLING_WARNING in read_text(root / "bridge-precheck.log").splitlines() else [],
            **({"reviewed_source_diagnostics": source_diagnostics,
                "source_diagnostic_policy_sha256": REVIEWED_554_POLICY_SHA256} if source_diagnostics else {}),
            "stages": stages}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence-root", type=Path, default=ROOT / "evidence")
    parser.add_argument("--config", type=Path, default=ROOT / "harness/config.json")
    parser.add_argument("--key", action="append")
    parser.add_argument("--output", type=Path, help="Optional JSON summary outside raw remote directories")
    args = parser.parse_args()
    cfgs = read_json(args.config)
    keys = args.key or list(cfgs)
    require(all(key in cfgs for key in keys), "Unconfigured group requested")
    result = {}
    for key in keys:
        try:
            result[key] = inspect_key(key, args.evidence_root / key / "remote", cfgs[key])
        except (EvidenceError, OSError, ValueError, KeyError, TypeError) as error:
            result[key] = {"status": "failed_or_missing_evidence", "error": str(error)}
    if args.output:
        require(not any(args.output.resolve().is_relative_to((args.evidence_root / key / "remote").resolve()) for key in keys),
                "Refusing to modify a raw evidence directory with generated summary")
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: {f: v[f] for f in ["status", "error", "proof_commit", "target_count", "nanoda_declarations"] if f in v}
                      for k, v in result.items()}, indent=2))
    return 0 if all(v["status"] == "mechanical_evidence_validated" for v in result.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
