#!/usr/bin/env python3
"""Read-only inspection of actual rank-5--10 CI artifacts; never executes Lean.

Usage: python3 verify-rank510/inspect_evidence.py [--key 585 ...] [--output FILE]
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
EXPECTED = {
    "636": {"original_targets": 79, "modules": None,
            "kernels": ["JSP000636", "Lower", "Upper", "Construction", "Threshold", "Thinning", "Asymptotics", "OriginalQuestion"]},
    "912-full": {"original_targets": 7, "modules": None,
                 "kernels": ["FullProof", "JSP912.Grid", "JSP912.Construction", "JSP912.Decay", "JSP912.Potential", "JSP912.Main"]},
    "912-modular": {"original_targets": 7, "modules": None,
                    "kernels": ["FullProof", "JSP912.Grid", "JSP912.Construction", "JSP912.Decay", "JSP912.Potential", "JSP912.Main"]},
    "728": {"original_targets": 27, "modules": 47},
    "585": {"original_targets": 61, "modules": 66},
    "506-main": {"original_targets": 49, "modules": 5},
    "506-selection": {"original_targets": 60, "modules": None},
    "393-general": {"original_targets": 24, "modules": 27},
}
# Each entry is an actual output chosen by the fixed submitted verifier, paired
# with its committed audit source. Do not search arbitrary logs for matching
# theorem names: unrelated or historical prints are not fresh audit evidence.
ORIGINAL_AXIOM_OUTPUTS = {
    "636": [("fresh-project-evidence/axioms.log", "Audit.lean")],
    "912-full": [("fresh-project-evidence/axioms.log", "Audit.lean"),
                 ("fresh-project-evidence/axioms-modular.log", "Audit.lean")],
    "912-modular": [("fresh-project-evidence/axioms.log", "Audit.lean"),
                    ("fresh-project-evidence/axioms-modular.log", "Audit.lean")],
    "728": [("fresh-project-evidence/axioms.log", "AuditComplete.lean")],
    "585": [("fresh-project-evidence/axioms.log", "AuditComplete.lean")],
    "506-main": [("fresh-project-evidence/axioms.log", "AuditComplete.lean")],
    "506-selection": [("fresh-project-evidence/axioms.log", "AuditSelection.lean"),
                      ("fresh-extra-1/axioms.log", "AuditComplete.lean")],
    "393-general": [("fresh-project-evidence/build-AuditGeneral.log", "AuditGeneral.lean"),
                    ("fresh-extra-1/build-AuditComplete.log", "AuditComplete.lean")],
}


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
    for field in ["id", "project", "commit", "branch", "toolchain", "bridge_file", "bridge_path", "bridge_module",
                  "exporter_commit", "nanoda_commit"]:
        require(cfg[field] == expected_cfg[field], "Artifact config differs from selected input: " + field)
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
    original_names = [t["declaration"] for t in targets if t["role"] == "theorem"]
    require(len(original_names) == EXPECTED[key]["original_targets"], "Original target coverage changed")

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
        require(not re.search(r"(^|\n).*\b(?:error|warning):", precheck_log),
                "Strict bridge precheck contains a diagnostic failure")
        stages["bridge-precheck"] = record
    for tool, commit in [("exporter", cfg["exporter_commit"]), ("checker", cfg["nanoda_commit"])]:
        for op in ["init", "fetch", "checkout"]:
            record = read_json(root / (op + "-" + tool + ".json"))
            check_command(root, record)
            if op in {"fetch", "checkout"}:
                require(commit in record["argv"], "Wrong pinned external tool: " + tool)

    official_sha = digest(root / "official-skill/scripts/audit.py")
    require(digest(root / "harness/audit.py") == official_sha == digest(ROOT / "harness/audit.py"),
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
    require(any("leanprover--lean4---v" + cfg["lean_version"] + "/bin" in e for e in image["Config"]["Env"]),
            "Docker toolchain PATH does not match selected release")

    evidence_dirs = [root / "fresh-project-evidence"] + sorted(root.glob("fresh-extra-*"))
    require(len(evidence_dirs) == 1 + len(cfg.get("additional_evidence_dirs", [])), "Missing original extra evidence directory")
    verification_records = []
    kernel_logs = []
    controls = []
    for directory in evidence_dirs:
        require(directory.is_dir(), "Missing original verifier evidence directory")
        vp = directory / "verification.json"
        json_expected = key not in {"636", "912-full", "912-modular"}
        require(not json_expected or vp.is_file(), "Missing JSON produced by original verifier: " + str(vp))
        record = read_json(vp) if vp.exists() else None
        if record:
            require(record.get("status") == "passed", "Original verifier JSON not passed")
            require(set(record.get("allowed_axioms", [])) <= ALLOWED_AXIOMS, "Original verifier permits nonstandard axioms")
            for source, sha in record.get("source_sha256", {}).items():
                require(before.get(source) == sha, "Original verifier source hash differs: " + source)
            if "preparation_head" in record:
                require(record["preparation_head"] == cfg["commit"], "Original verifier checked a different commit")
            if "verification_commit" in record:
                require(record["verification_commit"] == cfg["commit"], "Supplement verifier checked a different commit")
            if "dependency_count" in record:
                require(record["dependency_count"] == len(dependencies), "Original dependency count differs")
            verification_records.append(record)
        prefixes = record.get("kernel_prefixes", []) if record else EXPECTED[key].get("kernels", [])
        for prefix in prefixes:
            options = [directory / ("kernel-" + prefix + ".log"), directory / ("leanchecker-" + prefix + ".log")]
            found = [p for p in options if p.is_file()]
            require(len(found) == 1, "Missing/ambiguous original kernel receipt: " + prefix)
            require(not re.search(r"(^|\n).*\berror:", read_text(found[0])), "Original kernel log contains an error")
            kernel_logs.append(str(found[0].relative_to(root)))
        negative = sorted(directory.glob("*negative*.log"))
        require(bool(negative), "Missing false-arithmetic control in " + str(directory))
        for path in negative:
            text = read_text(path)
            require(re.search(r"error:\s*Tactic\s+[`']decide[`']\s+proved that the proposition\s+1\s*=\s*0\s+is false", text),
                    "Negative control failed for another reason or lacks exact false arithmetic: " + str(path))
            controls.append({"log": str(path.relative_to(root)), "expected_exit": "nonzero",
                             "exit_evidence": "semantic Lean error; nonzero exit enforced by successful original verifier",
                             "separate_exit_code_recorded": False})
    primary = verification_records[0] if verification_records else None
    if primary:
        observed_count = primary.get("axiom_reports", len(primary.get("targets", [])))
        if "general_axiom_reports" in primary:
            observed_count = primary["original_axiom_reports"] + primary["general_axiom_reports"]
        require(observed_count == EXPECTED[key]["original_targets"], "Original verification target count differs")
        if EXPECTED[key]["modules"] is not None:
            require(len(primary["modules_compiled"]) == EXPECTED[key]["modules"], "Original module count differs")
        if key == "506-main":
            require(primary.get("upstream_embedded_source_modules") == 480, "506 embedded upstream coverage differs")
    original_printed_names = set()
    original_axiom_outputs = []
    for log_name, audit_source in ORIGINAL_AXIOM_OUTPUTS[key]:
        text = read_text(root / log_name)
        expected_names = re.findall(r"^#print axioms (\S+)",
                                    read_text(root / "checked-source" / audit_source), re.M)
        require(bool(expected_names) and len(expected_names) == len(set(expected_names)),
                "Empty/duplicate original audit directives: " + audit_source)
        observed_names = re.findall(r"'([^']+)' (?:depends on axioms:|does not depend on any axioms)", text)
        require(observed_names == expected_names, "Original audit output does not exactly match its directives: " + log_name)
        for name in expected_names:
            require(axiom_list(text, name) <= ALLOWED_AXIOMS, "Original closure contains nonstandard axioms: " + name)
        original_printed_names.update(expected_names)
        original_axiom_outputs.append({"log": log_name, "source": audit_source, "targets": len(expected_names)})
    require(original_printed_names == set(original_names), "Fresh original audit outputs do not cover exactly all submitted targets")
    if key == "506-selection":
        selection_kernel = root / "fresh-project-evidence/selection-kernel.log"
        require(not re.search(r"(^|\n).*\berror:", read_text(selection_kernel)), "Selection kernel log contains an error")
        kernel_logs.append(str(selection_kernel.relative_to(root)))
        require(primary is not None and len(primary.get("new_theorems", [])) == 11, "Selection theorem count differs")
        require(primary.get("original_proof_commit") == cfg["git_history_required"][0], "Selection verifier bound a different base proof")
        require(set(primary["targets"]) == set(original_names), "Selection verification JSON target list differs")
        for path, sha in primary["original_input_sha256"].items():
            require(path.startswith(cfg["project"] + "/"), "Unexpected original selection-bound path: " + path)
            require(before.get(path.removeprefix(cfg["project"] + "/")) == sha, "Selection original-input hash differs: " + path)
        for path, sha in primary["supplement_input_sha256"].items():
            require(before.get(path) == sha, "Selection supplement-input hash differs: " + path)

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
        require(key == "506-selection", "Unexpected manual adapter scope")
        manual = read_json(root / "manual-equivalence.json")
        require(manual["adapter_sha256"] == digest(root / "manual-lake-adapter") ==
                digest(root / "harness" / cfg["lake_adapter"]["file"]), "Manual adapter source hash mismatch")
        manual_records = [json.loads(line) for line in read_text(root / "manual-module-builds.jsonl").splitlines()]
        modules = {a[1].removeprefix("+") for a in cfg["lake_adapter"]["intercepted_argv"]}
        expected_counts = Counter(t["module"] for t in targets if t["module"] in modules)
        require(Counter(r["module"] for r in manual_records) == expected_counts, "Manual equivalent builds omitted a target")
        for row in manual_records:
            require(row.get("exit_code") == row.get("compiler_exit_code") == row.get("adapter_exit_code") == 0,
                    "Manual target compilation did not exit zero")
            require(row["source_sha256_before"] == row["source_sha256_after"], "Manual target source changed")
            source = next(t["source"] for t in targets if t["module"] == row["module"])
            require(row["source_sha256_before"] == audit["preflight"]["file_sha256"][source],
                    "Manual compilation source differs from official audited source")
            require(digest(recorded_output(root, row["output_log"])) == row["output_log_sha256"], "Manual build log hash mismatch")
            require(re.fullmatch(r"[0-9a-f]{64}", row.get("olean_sha256", "")) is not None, "Missing manual output artifact hash")

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
            "stages": stages}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence-root", type=Path, default=ROOT / "evidence")
    parser.add_argument("--config", type=Path, default=ROOT / "harness/config.json")
    parser.add_argument("--key", action="append", choices=list(EXPECTED))
    parser.add_argument("--output", type=Path, help="Optional JSON summary outside raw remote directories")
    args = parser.parse_args()
    cfgs = read_json(args.config)
    keys = args.key or list(EXPECTED)
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
