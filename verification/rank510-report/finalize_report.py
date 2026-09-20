#!/usr/bin/env python3
"""Finalize the rank 5--10 report from complete, already inspected evidence.

Never executes Lean, downloads data, publishes, edits evidence, or fills missing
results with defaults. Run only after inspect_evidence.py has written all eight
groups to evidence/execution-summary.json and the lead reviewer has written
final-metadata.json. --check-only validates and renders in memory without writing.

Required metadata:
  finalized_at_utc: ISO-8601 UTC time
  rules_commit: the exact reviewed awards revision
  semantic_review_confirmed: [636, 912, 393, 728, 585, 506]
  prs: {"636": {"pr": 382, "head": "40 hex", "state": "open",
                 "merged": false}, ...}
  catalog_393_update: {"commit": "40 hex or null", "url": "https URL or null",
                       "published": false}
  jobs: {"636": {"run_id": 123, "job_id": 456,
                   "harness_commit": "40 hex"}, ... eight groups ...}

Optional failure_history maps an evidence directory basename (e.g.
"636-failed-1") to a concise, reviewed English explanation. These strings may
not contain personal email addresses, local absolute paths or Markdown links.
Successful jobs are selected dynamically from metadata, never inferred from a
whole workflow's status. Failed 393/728 evidence must remain available.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import math
from pathlib import Path, PurePosixPath
import re
import sys
from urllib.parse import urlparse


ROOT = Path(__file__).resolve().parent
KEYS = ("636", "912-full", "912-modular", "393-general", "728", "585", "506-main", "506-selection")
PROBLEMS = (636, 912, 393, 728, 585, 506)
PRS = {636: 382, 912: 691, 393: 368, 728: 373, 585: 432, 506: 363}
COUNTS = {"636": 82, "912-full": 9, "912-modular": 9, "393-general": 29,
          "728": 35, "585": 65, "506-main": 55, "506-selection": 68}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
RULES = "38e63c424c7196f8d4ceb664c5c25f0c0529d5e2"
REPO = "https://github.com/ketianzhang1-lang/jsp-000301-lean"
AWARDS = "https://github.com/TheJustinSunPrize/awards"
TOKEN = re.compile(r"\{\{([A-Z0-9_]+)\}\}")


class FinalizationError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise FinalizationError(message)


def read_json(path):
    require(path.is_file() and not path.is_symlink(), "Missing/unsafe JSON: " + str(path))
    return json.loads(path.read_text(encoding="utf-8"))


def digest(path):
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def hex_value(value, length, label):
    require(isinstance(value, str) and re.fullmatch(r"[0-9a-f]{" + str(length) + r"}", value), label + " is not a valid hash")
    return value


def positive_int(value, label):
    require(type(value) is int and value > 0, label + " must be a positive integer")
    return value


def seconds(value, label):
    require(type(value) in (int, float) and math.isfinite(value) and value >= 0, label + " has no valid runtime")
    return f"{value:.2f}"


def public_text(value, label):
    require(isinstance(value, str) and value.strip(), label + " must be nonempty text")
    require(not re.search(r"[A-Z0-9._%+-]+@[A-Z0-9.-]+\.[A-Z]{2,}", value, re.I), label + " contains an email address")
    require(not any(x in value for x in ("/workspace/", "/home/", "/Users/", "\n", "[", "]", "{{", "}}")), label + " contains private paths or unsupported markup")
    return value.replace("|", "\\|")


def file_in(root, relative):
    require(isinstance(relative, str), "Evidence path must be text")
    parts = PurePosixPath(relative)
    require(not parts.is_absolute() and ".." not in parts.parts and relative not in ("", "."), "Unsafe relative path: " + relative)
    path = root.joinpath(*parts.parts)
    require(path.is_file() and not path.is_symlink() and path.resolve().is_relative_to(root.resolve()), "Missing/unsafe evidence file: " + str(path))
    return path


def log_relative(recorded):
    require(isinstance(recorded, str) and recorded.startswith("/out/"), "Unexpected recorded log path")
    return recorded.removeprefix("/out/")


def job_url(job):
    return f"{REPO}/actions/runs/{job['run_id']}/job/{job['job_id']}"


def job_link(key, job):
    return f"[{key} job {job['job_id']}]({job_url(job)})"


def raw_link(key, relative, label=None):
    # Paths are relative public artifact coordinates, never the private host path.
    return f"[{label or relative}](evidence/{key}/remote/{relative})"


def table(headers, rows):
    return "\n".join(["| " + " | ".join(headers) + " |", "|" + "|".join("---" for _ in headers) + "|"] +
                     ["| " + " | ".join(str(x) for x in row) + " |" for row in rows])


def validate_metadata(meta):
    require(meta.get("rules_commit") == RULES, "Official rules revision changed or is missing; rereview before finalization")
    stamp = meta.get("finalized_at_utc")
    require(isinstance(stamp, str), "Missing finalized_at_utc")
    when = datetime.fromisoformat(stamp.replace("Z", "+00:00"))
    require(when.tzinfo is not None and when.utcoffset() == timezone.utc.utcoffset(when), "Finalization timestamp must specify UTC")
    confirmed = meta.get("semantic_review_confirmed")
    require(isinstance(confirmed, list) and len(confirmed) == 6 and all(type(x) is int for x in confirmed) and set(confirmed) == set(PROBLEMS),
            "Lead reviewer must explicitly confirm all six semantic reviews")
    require(isinstance(meta.get("jobs"), dict) and set(meta["jobs"]) == set(KEYS), "Metadata must select exactly eight jobs")
    for key in KEYS:
        job = meta["jobs"][key]
        positive_int(job["run_id"], key + " run_id")
        positive_int(job["job_id"], key + " job_id")
        hex_value(job["harness_commit"], 40, key + " harness_commit")
    require(len({j["job_id"] for j in meta["jobs"].values()}) == 8, "Each group requires a distinct job receipt")
    prs = meta.get("prs")
    require(isinstance(prs, dict) and set(prs) == {str(p) for p in PROBLEMS}, "Metadata requires all six final PR records")
    for problem in PROBLEMS:
        row = prs[str(problem)]
        require(row.get("pr") == PRS[problem], "Wrong awards PR for " + str(problem))
        hex_value(row.get("head"), 40, "PR head")
        require(row.get("state") in ("open", "closed") and type(row.get("merged")) is bool, "PR state/merged missing")
        require(not row["merged"] or row["state"] == "closed", "A merged PR cannot be open")
    update = meta.get("catalog_393_update")
    require(isinstance(update, dict) and type(update.get("published")) is bool and "commit" in update and "url" in update, "Missing explicit 393 catalog publication record")
    if update["published"]:
        hex_value(update["commit"], 40, "393 catalog commit")
        u = urlparse(update["url"])
        require(u.scheme == "https" and u.netloc == "github.com" and u.path.startswith("/ketianzhang1-lang/awards/") and update["commit"] in u.path,
                "393 published catalog URL must name the exact awards commit")
    elif update["commit"] is not None:
        hex_value(update["commit"], 40, "Unpublished 393 catalog commit")


def validate_receipt(directory, job=None, expected_internal=None):
    receipt = read_json(directory / "artifact-receipt.json")
    positive_int(receipt["artifact_id"], "artifact_id")
    positive_int(receipt["workflow_run"], "artifact workflow_run")
    hex_value(receipt["harness_commit"], 40, "artifact harness_commit")
    hex_value(receipt["sha256"], 64, "artifact archive sha256")
    positive_int(receipt["bytes"], "archive bytes")
    positive_int(receipt["internal_files_verified"], "internal_files_verified")
    archive = file_in(directory, receipt["filename"])
    require(archive.stat().st_size == receipt["bytes"] and digest(archive) == receipt["sha256"], "Archive receipt mismatch: " + directory.name)
    sums = read_json(directory / "remote/SHA256SUMS.json")
    require(len(sums) == receipt["internal_files_verified"], "Internal count differs from archive receipt")
    if job is not None:
        require(receipt["workflow_run"] == job["run_id"] and receipt["harness_commit"] == job["harness_commit"], "Selected job does not match artifact provenance: " + directory.name)
    if expected_internal is not None:
        require(receipt["internal_files_verified"] == expected_internal, "Summary/receipt internal hash count differs")
    return receipt


def actual_axioms(text, name):
    matches = re.findall(r"'" + re.escape(name) + r"' depends on axioms:\s*\[([^]]*)\]", text)
    if matches:
        values = [{v.strip() for v in row.split(",") if v.strip()} for row in matches]
        require(all(v == values[0] for v in values), "Conflicting printed axioms: " + name)
        return values[0]
    require("'" + name + "' does not depend on any axioms" in text, "Actual axiom report absent: " + name)
    return set()


def validate_group(base, key, summary, cfg, job):
    require(summary.get("status") == "mechanical_evidence_validated", "Failed or incomplete summary for " + key)
    require(summary.get("proof_commit") == cfg["commit"], "Summary proof commit mismatch for " + key)
    require(summary.get("source_inputs_stable") is True, "Source stability not established for " + key)
    if "source_stable" in summary:
        require(summary["source_stable"] is True, "Conflicting source_stable for " + key)
    manifest = read_json(base / "harness" / (key + "-targets.json"))
    targets = manifest["targets"]
    require(summary.get("target_count") == len(targets) == COUNTS[key], "Target count mismatch for " + key)
    require(manifest["project"]["commit"] == cfg["commit"], "Configured manifest commit mismatch")
    require(summary.get("original_target_count") == sum(t["role"] == "theorem" for t in targets), "Original target count mismatch")
    for field in ("total_targets", "total_target_count", "fresh_audit_target_count"):
        if field in cfg:
            require(cfg[field] == len(targets), "Config count mismatch: " + key + "/" + field)
    root = base / "evidence" / key / "remote"
    receipt = validate_receipt(root.parent, job, summary["artifact_files_hashed"])
    require((root / "SOURCE_COMMIT").read_text().strip() == cfg["commit"], "Actual source commit differs")
    require(read_json(root / "source-before.json") == read_json(root / "source-after.json"), "Source hashes changed")
    require(read_json(root / "harness" / (key + "-targets.json")) == manifest, "Summary refers to a different target manifest")
    archive_cfg = read_json(root / "harness/config.json")[key]
    for field in ("commit", "toolchain", "bridge_file", "bridge_module", "bridge_path", "exporter_commit", "nanoda_commit"):
        require(archive_cfg[field] == cfg[field], "Artifact configuration mismatch: " + key + "/" + field)
    completion = read_json(root / "mechanical-completion.json")
    require(completion.get("proof_commit") == cfg["commit"] and completion.get("targets") == len(targets) and completion.get("mechanical_checks") == "completed", "Mechanical completion receipt mismatch")
    audit = read_json(root / "audit/result.json")
    require(audit.get("exit_code") == 0 and audit.get("inputs_stable") is True and audit.get("mechanical_status") == "standard_axioms_only", "Official audit not complete")
    require(audit["manifest_sha256"] == summary["manifest_sha256"] == digest(root / "audit/manifest.json"), "Executed manifest digest differs")
    require(audit["script_sha256"] == summary["official_script_sha256"] == digest(root / "official-skill/scripts/audit.py"), "Official script digest differs")
    require([(r["id"], r["declaration"]) for r in audit["targets"]] == [(t["id"], t["declaration"]) for t in targets], "Actual target identities differ")
    require(set(summary["axioms"]) == {t["declaration"] for t in targets}, "Summary axiom coverage incomplete")
    axiom_rows = []
    for target, row in zip(targets, audit["targets"]):
        require(row.get("status") == "standard_axioms_only" and isinstance(row.get("axioms"), list), "Incomplete target axiom result")
        observed = set(row["axioms"])
        require(observed <= ALLOWED and observed == set(summary["axioms"][target["declaration"]]), "Unexpected/conflicting axioms")
        require(len(row["commands"]) == 3, "Target lacks three actual commands")
        links = []
        for label, command in zip(("build", "source", "statement/axioms"), row["commands"]):
            require(command.get("exit_code") == 0 and command.get("status") == "ok", "Target command failed")
            relative = log_relative(command["log"])
            path = file_in(root, relative)
            require(digest(path) == command["log_sha256"], "Target log hash differs")
            links.append(raw_link(key, relative, label))
        printed = file_in(root, log_relative(row["commands"][2]["log"])).read_text()
        require(actual_axioms(printed, target["declaration"]) == observed, "Printed axiom evidence differs")
        axiom_rows.append([key, target["id"], "`" + target["declaration"] + "`", ", ".join("`" + a + "`" for a in sorted(observed)) or "∅", "; ".join(links), job_link(key, job)])
    stages = summary["stages"]
    for stage in ("original-clean-verifier", "official-preflight", "official-audit", "bridge-kernel", "independent-nanoda"):
        require(stages[stage].get("exit_code") == 0, "Stage did not exit zero: " + key + "/" + stage)
        require(read_json(root / (stage + ".json")) == stages[stage], "Stage summary differs from actual record")
        seconds(stages[stage]["seconds"], stage)
    export = read_json(root / "export-command.json")
    require(export.get("exit_code") == 0, "Export did not exit zero")
    seconds(export["seconds"], "export")
    success = re.fullmatch(r"\s*Checked (\d+) declarations with no errors\s*", (root / "independent-nanoda.log").read_text())
    require(success is not None and int(success[1]) == summary["nanoda_declarations"] > 0, "NaNoda count/result differs")
    require(summary["dependency_count"] == len(summary["dependencies"]) == 9, "Dependency coverage differs")
    require(summary["original_kernel_logs"] and summary["negative_controls"], "Missing original kernel/control receipts")
    for relative in summary["original_kernel_logs"]:
        file_in(root, relative)
    for control in summary["negative_controls"]:
        text = file_in(root, control["log"]).read_text()
        require(re.search(r"error:\s*Tactic\s+[`']decide[`']\s+proved that the proposition\s+1\s*=\s*0\s+is false", text), "Negative control failed for another reason")
    for stage in cfg.get("extra_kernel_prefixes", []):
        record = stages["extra-kernel-" + stage]
        require(record["exit_code"] == 0 and record == read_json(root / ("extra-kernel-" + stage + ".json")), "Additional kernel replay missing")
    if key == "506-selection":
        require(summary["manual_equivalent_builds"] > 0, "Selection adapter evidence absent")
        records = [json.loads(line) for line in (root / "manual-module-builds.jsonl").read_text().splitlines()]
        require(len(records) == summary["manual_equivalent_builds"], "Manual build count differs")
        expected = Counter(t["module"] for t in targets if t["module"] in {"JSP000506Selection", "JSP000506.VerificationSelection"})
        require(Counter(r["module"] for r in records) == expected, "Manual module coverage differs")
        for row in records:
            require(row.get("exit_code") == row.get("compiler_exit_code") == row.get("adapter_exit_code") == 0 and row["source_sha256_before"] == row["source_sha256_after"], "Manual compilation failed or changed source")
    return {"summary": summary, "receipt": receipt, "targets": targets, "export": export, "axiom_rows": axiom_rows}


def failure_history(base, meta):
    histories = []
    names = {p.parent.name for p in (base / "evidence").glob("*-failed-*/artifact-receipt.json")}
    require({"393-general-failed-1", "728-failed-1"} <= names, "Original 393/728 failure artifacts must be retained")
    reasons = {
        "393-general-failed-1": "Candidate ed82d0cb2d35fca55f32b00cb75bdd5271226eb8 failed warnings-as-errors on the unused [CharZero K] assumption in minimum_le. The selected new proof omits that unused assumption; it does not disable the linter or backdate the completion.",
        "728-failed-1": "The original 47-module verifier completed; official preflight then rejected periods in manifest target IDs. The corrected manifest renumbers IDs and requirement references without changing the proof.",
    }
    for name, reason in meta.get("failure_history", {}).items():
        require(name in names, "Failure explanation has no retained artifact: " + name)
        reasons[name] = public_text(reason, "Failure explanation")
    for name in sorted(names):
        receipt = validate_receipt(base / "evidence" / name)
        histories.append((name, receipt, reasons.get(name, "Earlier failed or incomplete audit; retained for diagnosis and superseded only by the separately selected job.")))
    return histories


def render(base, meta, groups, failures):
    template = (base / "report-pending.md").read_text(encoding="utf-8")
    replacements = {}
    replacements["OVERALL_CONCLUSION"] = "Verification passed for all six selected original-problem formalizations"
    replacements["OVERALL_REASON"] = "The combined conclusion uses all eight exact-version mechanical evidence groups and the six explicitly confirmed semantic reviews. It is a self-check under the stated trust boundary, not official acceptance or an award decision."
    replacements["FINALIZED_AT_UTC"] = meta["finalized_at_utc"]
    for problem in PROBLEMS:
        for field in ("STATEMENT", "EXECUTION", "COMPLETE"):
            replacements[f"J{problem}_{field}"] = "Yes, for the selected version and stated scope"
        replacements[f"J{problem}_REQUIREMENTS"] = "Yes, technical Lean completeness; official prerequisites remain separate"
    selected = table(["Group", "Selected exact job", "Harness commit", "Proof commit", "Targets"],
                     [[key, job_link(key, meta["jobs"][key]), "`" + meta["jobs"][key]["harness_commit"] + "`", "`" + groups[key]["summary"]["proof_commit"] + "`", COUNTS[key]] for key in KEYS])
    history = table(["Retained failed attempt", "Run / artifact", "What failed"],
                    [[name, f"[run {r['workflow_run']}]({REPO}/actions/runs/{r['workflow_run']}/artifacts/{r['artifact_id']})", reason] for name, r, reason in failures])
    replacements["RUN_HISTORY"] = "the retained failure history below; a whole workflow's conclusion is never substituted for a job receipt"
    # Replace the provisional allocation of first-wave jobs. Actual metadata may
    # select later fixes for any key, including 636/585, without misreporting them.
    begin = template.index("The initial eight-job [workflow")
    end = template.index("\n\n## Four required judgments", begin)
    template = template[:begin] + "Final evidence is selected separately for each of the following jobs. The initial workflow contains failed jobs and is not an overall-success receipt.\n\n" + selected + "\n\nThe retained historical attempts are part of the audit trail, not successful final evidence.\n\n" + history + "\n\nAll selected job identities and harness revisions above come from the final metadata and match their artifact receipts." + template[end:]
    execution_rows = []
    control_rows = []
    integrity_rows = []
    for key in KEYS:
        g = groups[key]; s = g["summary"]; stages = s["stages"]; receipt = g["receipt"]
        original = stages["original-clean-verifier"]
        additional = [name for name in stages if name.startswith("extra-kernel-")]
        kernel = f"{len(s['original_kernel_logs'])} original kernel receipts; bridge exit 0"
        if additional:
            kernel += f"; {len(additional)} extra replay exit 0"
        execution_rows.append([key, s["target_count"], seconds(original["seconds"], "original") + " s / exit 0", kernel,
                               seconds(g["export"]["seconds"], "export") + " s / exit 0", s["nanoda_declarations"],
                               job_link(key, meta["jobs"][key]) + "; " + raw_link(key, "original-clean-verifier.json", "original receipt") + "; " + raw_link(key, "independent-nanoda.log", "NaNoda log")])
        integrity_rows.append([key, f"[artifact {receipt['artifact_id']}]({REPO}/actions/runs/{receipt['workflow_run']}/artifacts/{receipt['artifact_id']})", "`" + receipt["sha256"] + "`", receipt["bytes"], receipt["internal_files_verified"]])
        for control in s["negative_controls"]:
            control_rows.append([key, raw_link(key, control["log"]), "False arithmetic 1 = 0 rejected by Lean", "Nonzero status enforced by successful original verifier; no separate numeric exit record" if not control.get("separate_exit_code_recorded") else "See original control receipt"])
    replacements["EXECUTION_RESULTS"] = table(["Group", "Targets", "Original verifier runtime / exit", "Kernel receipts", "Export runtime / exit", "NaNoda declarations checked", "Exact evidence"], execution_rows) + "\n\nAll eight official target checks, bridge kernel replays, exports and independent NaNoda checks exited zero. Original kernel receipt counts refer to the successful original verifier's own coverage; an empty successful kernel log is not represented as a separately recorded numeric exit code. The original module obligations are the verified counts above."
    replacements["PER_TARGET_AXIOM_RESULTS"] = "All 352 target entries have actual axiom lists contained in `{propext, Classical.choice, Quot.sound}`. A target may use fewer or no axioms; this is not a claim that every target uses exactly three. The [complete axiom results](axiom-results.md) give each exact list, three command logs and its selected job."
    replacements["ARTIFACT_DIGEST_AND_INTERNAL_HASH_VERIFICATION"] = table(["Group", "Archive", "ZIP SHA-256", "Bytes", "Internal files hashed"], integrity_rows) + "\n\nArchive digests and sizes match the saved artifact receipts; internal counts agree with the validated execution summary. The underlying inspector checks full internal hash coverage. Raw logs use the relative coordinates `evidence/<group>/remote/`; the artifact links above identify their downloadable bundles. No private machine path is required."
    replacements["NEGATIVE_CONTROL_REVIEW"] = table(["Group", "Control output", "Observed rejection", "Exit-status evidence"], control_rows)
    replacements["DECISIVE_EVIDENCE_FOR_JUDGMENTS"] = "The statement and scope judgments combine the six source reviews with the independently stated bridges. The execution judgments use the per-job receipts and complete target results below. The complete-resolution judgments apply to the selected proof commits and the explicitly bounded original questions, not to every historical claim or stronger result. This report supplies the combined semantic and execution judgment."
    prs_rows = [[f"JSP-{p:06d}", f"[PR #{PRS[p]}]({AWARDS}/pull/{PRS[p]})", "`" + meta["prs"][str(p)]["head"] + "`", meta["prs"][str(p)]["state"], "yes" if meta["prs"][str(p)]["merged"] else "no"] for p in PROBLEMS]
    final_pr_table = table(["Submission", "PR", "Final observed awards head", "State", "Merged"], prs_rows)
    update = meta["catalog_393_update"]
    catalog = (f"The 393 catalog update was published at [{update['commit']}]({update['url']}). This catalog commit is separate from the newly checked proof commit."
               if update["published"] else "The 393 catalog update remains unpublished in this final metadata. The checked new proof is therefore not represented as already selected by the live catalog.")
    replacements["FINAL_AWARDS_HEADS_AND_APPLICATION_STATUS"] = final_pr_table + "\n\n" + catalog
    replacements["J393_FINAL_COMPLETION_EVIDENCE"] = "The corrected new completion is validated by " + job_link("393-general", meta["jobs"]["393-general"]) + f" at proof `{groups['393-general']['summary']['proof_commit']}`, including 29 target entries, the literal complex bridge and the explicit `ErdosProblems.Erdos485` replay. This evidence does not enlarge the scope or change the dates of the historical rational commits."
    manual_count = groups["506-selection"]["summary"]["manual_equivalent_builds"]
    replacements["MANUAL_EQUIVALENCE_REVIEW"] = f"The selected artifact records {manual_count} actual successful manual compilation invocations, with unchanged before/after source hashes. Their compiler and adapter exits are zero; the journal coverage matches every target using either intercepted module. See " + raw_link("506-selection", "manual-module-builds.jsonl", "per-invocation journal") + ", " + raw_link("506-selection", "manual-equivalence.json", "adapter provenance") + " and its exact job above."
    replacements["INPUT_STABILITY_AND_TOOL_COMPATIBILITY"] = "Every group's summary records stable original source/configuration inputs and all nine locked dependencies. Official preflight/manual-semantic fields remain preserved verbatim in raw results. They are complemented, not overwritten, by the successful separately recorded exporter builds, full exports, independent checker runs and the confirmed semantic reviews. The 4.34 compatibility rebuild remains an explicit adaptation."
    replacements["FINAL_RULES_AND_METADATA_RECHECK"] = f"At `{meta['finalized_at_utc']}`, the final metadata records official rules commit `{meta['rules_commit']}` and the PR states listed above. The rules commit equals the reviewed revision; this script does not itself query a live service. A later rules or PR change requires a new check."
    unmerged = [str(p) for p in PROBLEMS if not meta["prs"][str(p)]["merged"]]
    replacements["ONLINE_APPLICATION_STATUS"] = ("The following submissions remain unmerged in the final metadata: " + ", ".join(unmerged) + ". " if unmerged else "All six PRs are marked merged in the final metadata. ") + "No successful solver registration, completed contributor identity verification or award acceptance is established by these execution artifacts. Those prerequisites and the retrospective pre-opening timing issue remain for maintainers to resolve; no declaration is backdated. " + catalog
    replacements["FINAL_EVIDENCE_PATHS_AND_LINKS"] = "The exact job and archive tables above locate the original artifacts. [Execution summary](evidence/execution-summary.json), [final metadata](final-metadata.json), [target index](target-index.md), [axiom results](axiom-results.md), [reproduction instructions](how-to-reproduce.md), and all six `reviews/<problem>/review.md` memos accompany this report. The source-input and artifact checks are necessary evidence, not a substitute for semantic review or official adjudication."
    template = template.replace("**Pending finalization: {{OVERALL_CONCLUSION}}.**", "**{{OVERALL_CONCLUSION}}.**")
    template = template.replace("This is a report scaffold, not a completed verification certificate. We prepared the semantic reviews and fixed audit inputs for six submissions under account `ketianzhang1-lang`, with OpenAI ChatGPT/Codex assistance. The final verdict must be filled from the exact-version execution evidence and the source reviews below. We claim no independent human certification or official award approval.",
                                "We completed this self-check for six submissions under account `ketianzhang1-lang`, with OpenAI ChatGPT/Codex assistance. Its conclusion combines the exact-version execution evidence and the confirmed source reviews below. We claim no independent human certification or official award approval.")
    template = template.replace("## Eight CI groups and expected coverage", "## Eight CI groups and verified coverage")
    template = template.replace("These are planned counts derived from the committed manifests and verifier sources, **not results**.", "These coverage counts agree with the selected manifests and the validated original-verifier evidence.")
    template = template.replace("Before this document is finalized, every double-braced placeholder must be replaced with actual evidence or an explicit unresolved limitation. Neither a pending source review nor another commit's historical result can be substituted for a missing exact-version check.",
                                "Every execution result above is tied to its selected proof, harness and job. Another commit's historical result cannot substitute for an exact-version check. The unresolved official prerequisites remain as stated.")
    # These describe the work's preparation stage. Convert them only here,
    # after main() has validated all eight exact-version groups and the lead
    # reviewer's semantic confirmations. Original memos/logs remain untouched.
    completed_wording = {
        "The new source is what this audit must check.":
            "The new source is the selected proof checked by the exact job identified above.",
        "The failed artifact and diagnostic history remain reviewable; the corrected commit must pass independently.":
            "The failed artifact and diagnostic history remain reviewable; the corrected commit passed its separately identified check.",
        "final metadata must identify its own exact job and harness.":
            "final metadata identifies its own exact job and harness.",
        "The final 728 result must come from its separately identified corrected run.":
            "The final 728 result comes from its separately identified corrected run.",
        "the corrected jobs require their own final evidence.":
            "the corrected jobs have their own separately validated final evidence.",
        "the final main and selection results must be supported by their own complete job receipts.":
            "the final main and selection results are each supported by their own complete job receipt.",
    }
    for old, new in completed_wording.items():
        require(template.count(old) == 1, "Historical-to-final wording changed; review before rendering: " + old)
        template = template.replace(old, new)
    # Keep protocol language such as 'must' in the trust-boundary requirements.
    # Resolve only obsolete pending conclusions, not the requirements themselves.
    tokens = set(TOKEN.findall(template))
    require(tokens <= replacements.keys(), "Unhandled report tokens: " + repr(sorted(tokens - replacements.keys())))
    report = TOKEN.sub(lambda match: replacements[match[1]], template)
    require(not TOKEN.search(report), "Report still contains placeholders")
    require(not any(term in report for term in ("report scaffold", "Pending finalization:", "These are planned counts")), "Provisional report heading remains")
    require(not re.search(r"[A-Z0-9._%+-]+@[A-Z0-9.-]+\.[A-Z]{2,}", report, re.I), "Public report contains an email address")
    require(not any(p in report for p in ("/workspace/", "/home/", "/Users/")), "Public report contains a private filesystem path")
    axiom_rows = [row for key in KEYS for row in groups[key]["axiom_rows"]]
    require(len(axiom_rows) == 352, "Full axiom index is incomplete")
    axioms = "# Exact per-target axiom results\n\nThe 352 entries below are checked separately across eight jobs and are not 352 distinct mathematical theorems. Each displayed axiom set is a subset of `{propext, Classical.choice, Quot.sound}`; empty sets are valid. The referenced command logs contain the actual source checks, full statements and transitive axiom prints. Relative log coordinates identify files inside the corresponding job artifact.\n\n" + table(["Group", "Target ID", "Declaration", "Actual axioms", "Same-job raw logs", "Exact job"], axiom_rows) + "\n"
    return report, axioms


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--base", type=Path, default=ROOT)
    parser.add_argument("--check-only", action="store_true", help="Validate/render in memory; write nothing")
    args = parser.parse_args()
    base = args.base.resolve()
    meta = read_json(base / "final-metadata.json")
    validate_metadata(meta)
    summary = read_json(base / "evidence/execution-summary.json")
    require(isinstance(summary, dict) and set(summary) == set(KEYS), "Execution summary must contain exactly all eight groups")
    cfg = read_json(base / "harness/config.json")
    for problem in PROBLEMS:
        require((base / "reviews" / str(problem) / "review.md").is_file(), "Confirmed semantic review file missing")
    groups = {key: validate_group(base, key, summary[key], cfg[key], meta["jobs"][key]) for key in KEYS}
    failures = failure_history(base, meta)
    report, axioms = render(base, meta, groups, failures)
    if args.check_only:
        print("Validated all eight groups, 352 targets and six confirmed semantic reviews; no files written.")
        return 0
    # No output file is touched before all validation and rendering succeeds.
    for name, content in (("axiom-results.md", axioms), ("report.md", report)):
        destination = base / name
        require(not destination.is_symlink(), "Refusing a symlink output: " + name)
        temporary = destination.with_name(destination.name + ".tmp")
        require(not temporary.exists(), "Refusing an existing temporary output: " + temporary.name)
        temporary.write_text(content, encoding="utf-8")
        temporary.replace(destination)
    print("Wrote report.md and axiom-results.md from eight validated evidence groups; no remote publication.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (FinalizationError, OSError, ValueError, KeyError, TypeError) as error:
        print("Finalization aborted: " + str(error), file=sys.stderr)
        sys.exit(1)
