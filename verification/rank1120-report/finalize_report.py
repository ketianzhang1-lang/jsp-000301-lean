#!/usr/bin/env python3
"""Finalize ten submissions from every configured exact-version group.

Read-only checks never execute Lean, fetch data, modify raw evidence or publish.
--base ROOT --check-only validates and renders in memory without writing.

final-metadata.json must provide finalized_at_utc (UTC ISO-8601), rules_commit,
semantic_review_confirmed (all ten numeric IDs), semantic_scopes (the reviewed
objects in final-metadata-scopes.json), prs (ID -> pr/head/state/merged), and
jobs (group -> run_id/job_id/harness_commit; conclusion=success if supplied).
Optional failure_history maps retained failed-attempt folder names to accurate
single-line English explanations. Every selected job must match its artifact.

published-documents.json follows the root's documents array schema:
id, file_path (relative to this batch), repo_path, commit, sourceproof, sha256,
url, readback_verified. Separate 388 and 554 Apache license/provenance repairs are required. Selected
proof versions remain unchanged by later documentation-only commits.
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
KEYS = ()
PROBLEMS = ()
PRS = {}
CLAIMS = {}
COUNTS = {}
SCOPES_FIELDS = ("scope", "source_access", "limits", "attribution", "submission_changes")


def configure(base):
    global KEYS, PROBLEMS, PRS, CLAIMS, COUNTS
    selected = read_json(base / "selected.json")
    cfg = read_json(base / "harness/config.json")
    PROBLEMS = tuple(row["id"] for row in selected)
    require(set(PROBLEMS) == {301, 897, 907, 465, 388, 140, 725, 554, 746, 1021} and len(PROBLEMS) == 10,
            "The requested remaining-ten submission set changed")
    PRS = {row["id"]: row["pr"] for row in selected}
    CLAIMS = {row["id"]: row["claim"] for row in selected}
    KEYS = tuple(cfg)
    require(set(KEYS) == {str(p) for p in PROBLEMS} | {"465-uniform", "897-stability"} and
            {int(row["id"].split("-")[1]) for row in cfg.values()} == set(PROBLEMS),
            "Execution groups must contain all ten base versions and both submitted supplements")
    COUNTS = {key: len(read_json(base / "harness" / (key + "-targets.json"))["targets"]) for key in KEYS}
    return cfg


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
    require(when.tzinfo is not None and when.utcoffset() == timezone.utc.utcoffset(when),
            "Finalization timestamp must specify UTC")
    confirmed = meta.get("semantic_review_confirmed")
    require(isinstance(confirmed, list) and len(confirmed) == len(PROBLEMS) and
            all(type(x) is int for x in confirmed) and set(confirmed) == set(PROBLEMS),
            "Lead reviewer must explicitly confirm all ten semantic reviews")
    require(isinstance(meta.get("jobs"), dict) and set(meta["jobs"]) == set(KEYS),
            "Final metadata must select one exact job for every configured group")
    for key, job in meta["jobs"].items():
        positive_int(job["run_id"], key + " run_id")
        positive_int(job["job_id"], key + " job_id")
        hex_value(job["harness_commit"], 40, key + " harness_commit")
        if "conclusion" in job:
            require(job["conclusion"] == "success", "Selected job was not successful: " + key)
    require(len({j["job_id"] for j in meta["jobs"].values()}) == len(KEYS),
            "Each group needs its own distinct exact job receipt")
    require(set(meta.get("prs", {})) == {str(p) for p in PROBLEMS}, "Final metadata needs all ten PR records")
    for problem in PROBLEMS:
        row = meta["prs"][str(problem)]
        require(row.get("pr") == PRS[problem], "Wrong awards PR for " + str(problem))
        hex_value(row.get("head"), 40, "PR head")
        require(row.get("state") in ("open", "closed") and type(row.get("merged")) is bool,
                "PR state or merged status is absent")
        require(not row["merged"] or row["state"] == "closed", "A merged PR cannot be open")
    scopes = meta.get("semantic_scopes")
    require(isinstance(scopes, dict) and set(scopes) == {str(p) for p in PROBLEMS},
            "Lead-reviewed scope descriptions are required for every submission")
    for key, row in scopes.items():
        for field in SCOPES_FIELDS:
            public_text(row[field], key + " semantic " + field)
        require(isinstance(row.get("sources"), list) and row["sources"], "Missing independent source references: " + key)
        for source in row["sources"]:
            public_text(source["title"], "Source title")
            u = urlparse(source["url"])
            require(u.scheme == "https" and u.netloc and not u.username and not u.password,
                    "Invalid public source URL: " + key)


def validate_documents(base, cfg):
    data = read_json(base / "published-documents.json")
    rows = data["documents"]
    require(isinstance(rows, list) and rows, "Missing separately published documentation repairs")
    for row in rows:
        problem = int(row["id"])
        require(problem in PROBLEMS, "Documentation belongs to an unselected problem")
        commit = hex_value(row["commit"], 40, "Documentation commit")
        proof = hex_value(row["sourceproof"], 40, "Documentation source proof")
        require(proof in {c["commit"] for c in cfg.values() if int(c["id"].split("-")[1]) == problem},
                "Documentation was not based on the selected proof")
        require(commit != proof, "Documentation repair and historical proof commit must be distinguished")
        require(row.get("readback_verified") is True, "Published documentation has not been read back and verified")
        sha = hex_value(row["sha256"], 64, "Documentation file SHA256")
        require(digest(file_in(base, row["file_path"])) == sha, "Published documentation local bytes differ")
        expected_url = REPO + "/blob/" + commit + "/" + row["repo_path"]
        require(row["url"] == expected_url, "Documentation URL does not pin the published file")
    for problem in [388, 554]:
        license_rows = [row for row in rows if int(row["id"]) == problem and row["repo_path"].endswith("APACHE-2.0.txt")]
        require(len(license_rows) == 1, str(problem) + " missing full Apache license repair was not recorded as published")
        require(any(int(row["id"]) == problem and row["repo_path"].endswith("PROVENANCE.md") for row in rows),
                str(problem) + " inaccurate historical license description lacks its published correction")
    return rows


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
        if "workflow_job" in receipt:
            require(receipt["workflow_job"] == job["job_id"], "Selected job ID differs from artifact receipt")
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
    if key == '554':
        policy_file = file_in(base, 'reviews/554/inspector-source-diagnostics.json')
        policy = read_json(policy_file)
        require(digest(policy_file) == summary.get('source_diagnostic_policy_sha256') and
                summary.get('reviewed_source_diagnostics') == policy['reviewed_source_diagnostics'] and
                len(summary['reviewed_source_diagnostics']) == 4,
                '554 requires exact disclosure of all four reviewed source import diagnostics')
    for relative in summary["original_kernel_logs"]:
        file_in(root, relative)
    for control in summary["negative_controls"]:
        text = file_in(root, control["log"]).read_text()
        proposition = control["proposition"]
        require(proposition in {"1 = 0", "2 + 2 = 5"}, "Unreviewed negative-control proposition")
        pattern = r"error:\s*Tactic\s+[`']decide[`']\s+proved that the proposition\s+" + r"\s*".join(re.escape(token) for token in proposition.split()) + r"\s+is false"
        require(re.search(pattern, text), "Negative control failed for another reason")
    for stage in cfg.get("extra_kernel_prefixes", []):
        record = stages["extra-kernel-" + stage]
        require(record["exit_code"] == 0 and record == read_json(root / ("extra-kernel-" + stage + ".json")), "Additional kernel replay missing")
    if cfg.get("lake_adapter"):
        require(summary["manual_equivalent_builds"] > 0, "Selection adapter evidence absent")
        records = [json.loads(line) for line in (root / "manual-module-builds.jsonl").read_text().splitlines()]
        require(len(records) == summary["manual_equivalent_builds"], "Manual build count differs")
        expected = Counter(t["module"] for t in targets if t["module"] in {a[1].removeprefix("+") for a in cfg["lake_adapter"]["intercepted_argv"]})
        require(Counter(r["module"] for r in records) == expected, "Manual module coverage differs")
        for row in records:
            require(row.get("exit_code") == row.get("compiler_exit_code") == row.get("adapter_exit_code") == 0 and row["source_sha256_before"] == row["source_sha256_after"], "Manual compilation failed or changed source")
    return {"summary": summary, "receipt": receipt, "targets": targets, "export": export, "axiom_rows": axiom_rows}


def failure_history(base, meta):
    histories = []
    names = {p.parent.name for p in (base / "evidence").glob("*/artifact-receipt.json")
             if "failed" in p.parent.name}
    reasons = {}
    for name, reason in meta.get("failure_history", {}).items():
        require(name in names, "Failure explanation has no retained artifact: " + name)
        reasons[name] = public_text(reason, "Failure explanation")
    for name in sorted(names):
        receipt = validate_receipt(base / "evidence" / name)
        histories.append((name, receipt, reasons.get(name, "Earlier failed or incomplete audit; retained for diagnosis and superseded only by the separately selected job.")))
    return histories


def stage_hash_rows(base, key, group):
    """Bind every reported stage receipt and log to its actual archived bytes."""
    root = base / 'evidence' / key / 'remote'
    records = dict(group['summary']['stages'])
    records['export-command'] = group['export']
    rows = []
    for name, record in sorted(records.items()):
        receipt_relative = name + '.json'
        receipt_file = file_in(root, receipt_relative)
        require(read_json(receipt_file) == record and record.get('exit_code') == 0,
                'Stage receipt differs or failed: ' + key + '/' + name)
        relative = log_relative(record['log'])
        log_file = file_in(root, relative)
        log_sha = digest(log_file)
        require(log_sha == record['log_sha256'], 'Stage log hash differs: ' + key + '/' + name)
        rows.append([key, name, seconds(record['seconds'], name) + ' s / exit 0',
                     raw_link(key, receipt_relative, digest(receipt_file)),
                     raw_link(key, relative, log_sha)])
    return rows



def render(base, meta, cfg, groups, failures, documents):
    total = sum(COUNTS.values())
    original = sum(g['summary']['original_target_count'] for g in groups.values())
    bridge = total - original
    lines = [
        '# 第 11–20 批现有申请：Lean 自查最终报告', '',
        '**总体结论：9 份申请验证通过；1021 按宽泛题库验收范围为证据不足，完整性暂无法确认。**', '',
        '9 份申请的固定版本实际检查成功，且完整覆盖已核对的原题。1021 已完整否定原始论文中的全称等式猜想，该历史命题的验证通过；'
        '但宽泛题库摘要是否还要求其他结论，需主办方裁定，不能据此声称整份申请满足该宽泛范围的验收要求。', '',
        f'机械检查全部成功：{len(PROBLEMS)} 份申请、{len(KEYS)} 组固定版本、{total} 项逐目标检查。'
        '机械成功不补足 1021 的验收范围缺口，也不等于主办方接受、资格审核或授奖。原 PR 打开前自查的历史时序不能补造；未合并的声明仍保持未完成。', '',
        table(['题目', '是否对应指定原题', '固定版本是否实际通过', '是否完整解决原题', 'Lean 完整性要求'],
              [[f'JSP-{p:06d}', '历史命题是；宽泛题库范围暂无法确认' if p == 1021 else '是，限下文明确的原始命题', '是，全部提交版本逐组有成功证据',
                '历史全称等式已完整否定；宽泛题库全题暂无法确认' if p == 1021 else '是，限已复核的完整原题范围',
                '历史命题满足；宽泛题库验收暂无法确认（证据不足）' if p == 1021 else '技术要求通过；官方前置条件仍单列'] for p in PROBLEMS]), '',
        '## English technical report', '',
        '**Overall: nine submissions verified; evidence is insufficient to establish completeness of 1021 under the broader catalog interpretation.** '
        'The historical universal-equality question for 1021 is fully refuted and verified, but its relation to the broader requested catalog scope requires organizer adjudication.', '',
        f"**Mechanical checks passed for all {len(KEYS)} exact-version execution groups, comprising {total} target entries.** "
        'This mechanical result does not resolve the 1021 scope gap.', '',
        f"Finalized at `{meta['finalized_at_utc']}` for GitHub account `ketianzhang1-lang`, with OpenAI ChatGPT/Codex assistance. "
        'This conclusion combines actual inspected mechanical evidence and the lead reviewer’s ten confirmed semantic reviews. '
        'It is a contributor-operated self-check, not independent human certification, organizer acceptance, priority recognition or an award decision.', '',
        'The selected submissions are 301, 897, 907, 465, 388, 140, 725, 554, 746 and 1021. '
        'These are the ten remaining current claims after the previously completed ten; their internal order is not a new numerical estimate of award probability. '
        'Both catalog-selected proof versions for 465 and 897 are included separately.', '',
        '## Required judgments and original scope', '',
        'The “complete” judgment below applies to the explicitly identified original question. For 1021, the original-paper universal equality is fully disproved, '
        'while the broader catalog interpretation remains an organizer decision. The additional author and eligibility prerequisites are not inferred from machine verification.', '',
        table(['Submission', 'Original problem correspondence', 'Exact commit actually verified', 'Complete original scope', 'Lean completeness'],
              [[f'JSP-{p:06d}', 'Yes for the historical question; broader catalog correspondence not determined' if p == 1021 else 'Yes, for the source-defined question below', 'Yes; all selected versions have separate passed job evidence',
                'Historical equality fully refuted; full broader catalog scope not determined' if p == 1021 else 'Yes, within the stated original scope',
                'Historical-question requirements satisfied; broader catalog requirements not determined (insufficient evidence)' if p == 1021 else 'Technical completeness passed; official prerequisites separate'] for p in PROBLEMS]), '',
    ]
    for p in PROBLEMS:
        scope = meta['semantic_scopes'][str(p)]
        sources = ', '.join(f"[{source['title']}]({source['url']})" for source in scope['sources'])
        lines += [f'### JSP-{p:06d}', '', scope['scope'], '', f'Original-statement evidence: {sources}. {scope["source_access"]}', '',
                  'Limits: ' + scope['limits'], '', 'Attribution: ' + scope['attribution'], '',
                  'Submission correction: ' + scope['submission_changes'], '',
                  f'The [detailed semantic review](reviews/{p}/review.md) records the quantifiers, definitions, boundary cases, proof chain, statement bridges and contribution boundaries. '
                  'It is retained as a preparation-stage memo; its pending execution language is superseded only by this final report’s actual evidence.', '']
    lines += ['## Exact proof versions and selected successful jobs', '',
              'Each row selects an individual successful job and its own immutable artifact. A failed or still-running sibling job does not become successful by association, '
              'and a later proof or documentation commit is never substituted for the selected proof below.', '',
              table(['Group', 'Exact proof commit', 'Harness commit', 'Selected job', 'Original + bridge targets'],
                    [[key, '`' + cfg[key]['commit'] + '`', '`' + meta['jobs'][key]['harness_commit'] + '`', job_link(key, meta['jobs'][key]),
                      f"{groups[key]['summary']['original_target_count']} + {COUNTS[key] - groups[key]['summary']['original_target_count']} = {COUNTS[key]}"] for key in KEYS]), '',
              f'There are {total} checked per-group entries: {original} original declarations and {bridge} auditor-owned bridge declarations. '
              'Repeated original declarations across separately selected versions are intentionally checked again; these totals do not count distinct mathematical theorems.', '']
    execution_rows, integrity_rows, control_rows, input_rows, stage_rows = [], [], [], [], []
    for key in KEYS:
        g = groups[key]; s = g['summary']; stages = s['stages']; receipt = g['receipt']
        root = base / 'evidence' / key / 'remote'
        input_rows.append([key,
                           raw_link(key, 'source-before.json', digest(root / 'source-before.json')),
                           raw_link(key, 'source-after.json', digest(root / 'source-after.json')),
                           raw_link(key, 'audit/manifest.json', s['manifest_sha256']),
                           '`' + s['bridge_source_sha256'] + '`'])
        stage_rows.extend(stage_hash_rows(base, key, g))
        original_stage = stages['original-clean-verifier']
        execution_rows.append([key, seconds(original_stage['seconds'], 'original') + ' s / exit 0',
                               str(len(s['original_kernel_logs'])) + ' original replay logs; bridge exit 0',
                               seconds(g['export']['seconds'], 'export') + ' s / exit 0', s['nanoda_declarations'],
                               raw_link(key, 'original-clean-verifier.json', 'original receipt') + '; ' +
                               raw_link(key, 'official-audit.json', 'official audit') + '; ' +
                               raw_link(key, 'independent-nanoda.log', 'NaNoda output')])
        integrity_rows.append([key, f"[artifact {receipt['artifact_id']}]({REPO}/actions/runs/{receipt['workflow_run']}/artifacts/{receipt['artifact_id']})",
                               '`' + receipt['sha256'] + '`', receipt['bytes'], receipt['internal_files_verified']])
        for control in s['negative_controls']:
            control_rows.append([key, control['proposition'], 'Rejected with the intended mathematical false-arithmetic error',
                                 raw_link(key, control['log'])])
    lines += ['## Actual execution results', '',
              table(['Group', 'Clean original verification', 'Kernel evidence', 'Export', 'NaNoda declarations', 'Raw evidence'], execution_rows), '',
              f'Every one of the {total} target entries has an actual transitive axiom list contained in '
              '`{propext, Classical.choice, Quot.sound}`. Some use fewer axioms or none. The '
              '[full per-target axiom table](axiom-results.md) links each exact list to its module build, source check, full statement/axiom output and same-job receipt.', '',
              'The official unchanged auditor provides explicit per-target build, source and statement/axiom checks. '
              'The original verifier separately clean-builds its complete configured source closure and rejects false arithmetic. '
              'The bridge is then kernel-replayed, and every selected declaration closure is exported to the separate NaNoda implementation with a hard-error axiom allowlist. '
              'The checker prints every selected declaration as well as its successful declaration count.', '',
              '## Integrity and negative controls', '',
              table(['Group', 'Archive', 'ZIP SHA-256', 'Bytes', 'Internal files hashed'], integrity_rows), '',
              'Downloaded archive digests match their GitHub artifact receipts. Every internal file is covered by the archived hash inventory; '
              'the selected harness commit, exact source commit, branch-tip receipt, original input snapshots, target manifest and official audit hash are independently cross-checked. '
              'All actual dependency Git revisions match the committed manifests. Raw paths below are archive-relative coordinates, not private machine paths.', '',
              table(['Group', 'Control proposition', 'Observed outcome', 'Actual log'], control_rows), '',
              'For ordinary original verifiers, their successful control branch enforces a nonzero compiler exit and the inspector checks the exact mathematical rejection text. '
              'An empty or unrelated failure log cannot satisfy this requirement. Where the original verifier did not record a separate numeric control exit, this report does not invent one. '
              'The auditor-owned 301 summary separately records its nonzero control exit.', '',
              '## Input snapshots and complete stage hash index', '',
              'The linked snapshot files index every original checked source and dependency input. Their contents agree before and after checking. '
              'The executed manifest and separately supplied bridge are pinned below; all hashes are SHA-256.', '',
              table(['Group', 'Before-input index SHA-256', 'After-input index SHA-256', 'Executed manifest SHA-256', 'Auditor bridge SHA-256'], input_rows), '',
              'The following table includes every recorded preparation and checking stage plus declaration export. '
              'Its receipt and log hashes are recomputed from the selected artifact bytes; stages are listed alphabetically within each group, not in execution order.', '',
              table(['Group', 'Stage', 'Actual time / exit', 'Receipt SHA-256 and link', 'Log SHA-256 and link'], stage_rows), '',
              '## Execution boundary and disclosed adaptations', '',
              f"The audited official skill is [lean-verify at `{RULES}`]({AWARDS}/blob/{RULES}/skills/lean-verify/SKILL.md). "
              'The executed audit.py has SHA-256 `5db45dddcb4d588bc27e7c7161fbca5cedaa3e73e1c40843d21f5a214323cd07` and is byte-identical to the original skill copy. '
              'The skill’s own manual-semantic fields are preserved verbatim in the raw results; the separate confirmed source reviews supply those semantic judgments.', '',
              'Preparation can retrieve fixed dependencies and checker sources. Actual proof checking runs as UID 10001 in a disposable Docker environment with network disabled, '
              'capabilities dropped, no new privileges, and the built external tools mounted read-only. The project’s previous build products and configured evidence output folders are removed before the clean original verification. '
              'Fresh evidence is archived before tracked historical logs are restored solely to retain the exact input snapshot. No local Lean or Lake execution is used.', '',
              'The selected projects use Lean 4.34.0 and nine fixed dependency revisions. Each artifact records actual tool versions and the Docker image digest. '
              'Exporter source `6cea97789dc088ea47fcea15692db85685aedac5` originally targeted a later Lean release and was explicitly rebuilt using the selected Lean 4.34 toolchain; '
              'this is a compatibility rebuild, not a claim that the original exporter revision was a native 4.34 release. '
              'The independent NaNoda source is pinned to `4c544ed4099c8227f07d5de77ad1e69fb0740a27`; Rust 1.90.0 builds the fixed checker.', '',
              'Original declarations defined in downloaded or unregistered source modules can use a configured tracked import entry for the official audit. '
              'The manifest separately records their real definition file and pinned hash. Their actual source is clean-compiled, kernel-replayed and included in the exact declaration closure; '
              'this routing never asserts that the definition is located in the import entry or that an untracked upstream file belonged to the selected Git tree.', '']
    manual_rows = []
    warning_rows = []
    source_warning_rows = []
    for key in KEYS:
        s = groups[key]['summary']
        if cfg[key].get('lake_adapter'):
            manual_rows.append([key, ', '.join('`' + argv[1] + '`' for argv in cfg[key]['lake_adapter']['intercepted_argv']),
                                s['manual_equivalent_builds'], raw_link(key, 'manual-module-builds.jsonl', 'per-invocation journal') + '; ' +
                                raw_link(key, 'manual-equivalence.json', 'adapter identity')])
        for warning in s.get('reviewed_infrastructure_warnings', []):
            warning_rows.append([key, 'Mathlib Git URL differs only by the .git suffix; actual fixed revisions agree',
                                 raw_link(key, 'bridge-precheck.log', 'actual Lake warning')])
        for diagnostic in s.get('reviewed_source_diagnostics', []):
            source_warning_rows.append([key, 'Real compiler warning: deprecated forwarding import path',
                                        raw_link(key, 'checked-source/' + diagnostic['source_path'],
                                                 diagnostic['source_path'] + ':' + str(diagnostic['source_line'])),
                                        '`' + diagnostic['source_sha256'] + '`',
                                        raw_link(key, diagnostic['log_path'], diagnostic['log_sha256'])])
    lines += ['The 301 original proof commit has no strict verifier script. The auditor-owned `301-original.py` is explicitly separate from the selected proof and checks its eight original declarations without modifying the selected Lean source or project configuration.', '']
    if manual_rows:
        lines += [table(['Group', 'Only intercepted Lake build', 'Actual strict recompilations', 'Evidence'], manual_rows), '',
                  'These narrowly scoped adapters provide disclosed manual-equivalent compilation for flat supplement modules omitted by the unchanged selected Lake configuration. '
                  'Every invocation deletes the earlier object and invokes the actual pinned Lean compiler with warnings as errors; source hashes, exact argv, unique output log, new object hash and zero exits are recorded. '
                  'All other arguments delegate unchanged to the real Lake. These rows are not described as native registered Lake-target successes.', '']
    if warning_rows:
        lines += [table(['Group', 'Reviewed non-proof warning', 'Evidence'], warning_rows), '',
                  'This exact Lake metadata warning concerns two spellings of the same repository URL. The locked manifest is preserved and every actual package commit is checked. '
                  'This metadata diagnostic is distinct from the source import warnings below. Every accepted diagnostic is identified explicitly; no general warning exception is used.', '']
    if source_warning_rows:
        lines += [table(['Group', 'Actual diagnostic type', 'Exact checked source and line', 'Source SHA-256', 'Complete warning log SHA-256 and link'], source_warning_rows), '',
                  'The 554 original compiler invocations include `-DwarningAsError=true` and exit zero, but these four actual source import warnings remain. '
                  'The fixed Mathlib file `Mathlib/Data/Real/Basic.lean` is a pure public import of `Mathlib.Basic.Real.Basic` followed by `deprecated_module`; '
                  'its SHA-256 is `a1d6fa90c0e6ddc98b82933e33801713f937030bc1d70052afb6794c3637a65d`. '
                  'Lean 4.34 import processing adds these messages directly at warning severity, bypassing the ordinary `logAt` conversion controlled by `warningAsError`; '
                  'the final message counter counts errors and does not subsequently promote these warnings. '
                  'The [source review](reviews/554/import-deprecation-review.md) and [fixed diagnostic policy](reviews/554/inspector-source-diagnostics.json) '
                  'record immutable compiler/dependency URLs, source hashes, all four complete warning texts and the actual successful strict compiler arguments.', '',
                  'The official skill requires successful original and target checks with faithful diagnostic disclosure; it does not impose a zero-warning rule. '
                  'These exact forwarding-path diagnostics are classified as non-blocking after source review, while all 44 targets, kernel replay and independent NaNoda verification pass. '
                  'The inspector binds each whole diagnostic block to its original source and log hashes. It does not suppress, edit or generalize beyond these four logs. '
                  'The selected proof, dependency pins and raw outputs remain unchanged; this is explicitly not a claim of zero warnings.', '']
    lines += ['## Retained attempts and separately published document repairs', '']
    if failures:
        lines += [table(['Retained failed attempt', 'Run / artifact', 'Actual failure and correction'],
                        [[name, f"[run {r['workflow_run']}]({REPO}/actions/runs/{r['workflow_run']}/artifacts/{r['artifact_id']})", reason]
                         for name, r, reason in failures]), '',
                  'These attempts are preserved as diagnostic history and are not counted as successful evidence. Every final replacement is identified by its own selected job above.', '']
    else:
        lines += ['No failed-attempt artifact is recorded in the final evidence inventory.', '']
    lines += [table(['Submission', 'Repaired documentation', 'Documentation commit', 'Selected proof retained'],
                    [[f"JSP-{int(row['id']):06d}", f"[{row['repo_path']}]({row['url']})", '`' + row['commit'] + '`', '`' + row['sourceproof'] + '`']
                     for row in documents]), '',
              'The documentation commits are distinct from the checked proof commits. In particular, 388’s and 554’s full Apache licenses and corrected provenance descriptions are added without relabeling the historical proof source. '
              'Upstream authors, original notices, complete license texts and compatibility-change records accompany redistributed proof-source evidence. Full mathematical papers are cited rather than included wholesale.', '',
              '## Final application status and unresolved official prerequisites', '',
              table(['Submission', 'PR / existing claim', 'Final observed PR head', 'State', 'Merged'],
                    [[f'JSP-{p:06d}', f'[PR #{PRS[p]}]({AWARDS}/pull/{PRS[p]}) / [claim #{CLAIMS[p]}]({AWARDS}/issues/{CLAIMS[p]})',
                      '`' + meta['prs'][str(p)]['head'] + '`', meta['prs'][str(p)]['state'],
                      'yes' if meta['prs'][str(p)]['merged'] else 'no'] for p in PROBLEMS]), '',
              'The final metadata records a fresh rule/PR-state check at the timestamp above; this rendering script does not query GitHub itself. '
              'A later rule, selected source or PR change requires another assessment. Solver registration, mathematical-source recognition, identity/attribution review, '
              'organizer merge and award eligibility are separate from this technical self-check. The original PRs predate the newer pre-opening verification requirement; '
              'later execution cannot establish that historical condition, and it is not backdated or falsely checked. The existing claim’s merged-PR declaration remains unchecked while its PR is unmerged.', '',
              'Earlier full formalizations and overlapping submissions remain disclosed. Successful checking and separately attributable additions do not establish worldwide first priority, '
              'an award allocation agreement, a minimum payment or an automatic right to a prize. The 1021 catalog-scope interpretation explicitly remains for organizer adjudication.', '',
              'Supporting records: [execution summary](evidence/execution-summary.json), [final metadata](final-metadata.json), '
              '[target index](target-index.md), [per-target axiom results](axiom-results.md), [reproduction instructions](how-to-reproduce.md), '
              '[published document repairs](published-documents.json), and the ten linked semantic memos. The reproduction and evidence links pin the actual selected versions.', '']
    report = '\n'.join(lines)
    require(not TOKEN.search(report), 'Report contains an unresolved placeholder')
    require(not re.search(r'[A-Z0-9._%+-]+@[A-Z0-9.-]+\.[A-Z]{2,}', report, re.I), 'Public report contains an email address')
    require(not any(path in report for path in ('/workspace/', '/home/', '/Users/')), 'Public report exposes a private filesystem path')
    axiom_rows = [row for key in KEYS for row in groups[key]['axiom_rows']]
    require(len(axiom_rows) == total, 'Full per-target axiom table is incomplete')
    axioms = '# Exact per-target axiom results\n\n' + \
        f'The {total} entries are checked separately across {len(KEYS)} exact-version jobs and are not {total} distinct mathematical theorems. ' + \
        'Each actual axiom set is a subset of `{propext, Classical.choice, Quot.sound}`; empty sets are valid. ' + \
        'Command links identify the actual build, source and full statement/transitive-axiom checks inside the corresponding job artifact.\n\n' + \
        table(['Group', 'Target ID', 'Declaration', 'Actual axioms', 'Same-job raw logs', 'Exact job'], axiom_rows) + '\n'
    return report, axioms


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--base', type=Path, default=ROOT)
    parser.add_argument('--check-only', action='store_true', help='Validate and render in memory; write nothing')
    args = parser.parse_args()
    base = args.base.resolve()
    cfg = configure(base)
    meta = read_json(base / 'final-metadata.json')
    validate_metadata(meta)
    summary = read_json(base / 'evidence/execution-summary.json')
    require(isinstance(summary, dict) and set(summary) == set(KEYS), 'Execution summary must contain every configured group exactly once')
    for problem in PROBLEMS:
        file_in(base, 'reviews/' + str(problem) + '/review.md')
    # Re-read-only inspect raw bytes before release: a saved summary cannot mask
    # later evidence changes or a missing current selected manifest/source.
    import importlib.util
    spec = importlib.util.spec_from_file_location('rank1120_actual_inspector', base / 'inspect_evidence.py')
    inspector = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(inspector)
    for key in KEYS:
        actual = inspector.inspect_key(key, base / 'evidence' / key / 'remote', cfg[key])
        require(actual == summary[key], 'Canonical summary differs from fresh read-only inspection: ' + key)
    groups = {key: validate_group(base, key, summary[key], cfg[key], meta['jobs'][key]) for key in KEYS}
    failures = failure_history(base, meta)
    documents = validate_documents(base, cfg)
    for path in ('target-index.md', 'how-to-reproduce.md'):
        file_in(base, path)
    report, axioms = render(base, meta, cfg, groups, failures, documents)
    if args.check_only:
        print(f'Validated {len(KEYS)} groups, {sum(COUNTS.values())} targets and {len(PROBLEMS)} confirmed semantic reviews; no files written.')
        return 0
    for name, content in (('axiom-results.md', axioms), ('report.md', report)):
        destination = base / name
        require(not destination.is_symlink(), 'Refusing a symlink output: ' + name)
        temporary = destination.with_name(destination.name + '.tmp')
        require(not temporary.exists(), 'Refusing an existing temporary output: ' + temporary.name)
        temporary.write_text(content, encoding='utf-8')
        temporary.replace(destination)
    print(f'Wrote report.md and axiom-results.md from {len(KEYS)} validated groups; no remote publication.')
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (FinalizationError, OSError, ValueError, KeyError, TypeError) as error:
        print('Finalization aborted: ' + str(error), file=sys.stderr)
        sys.exit(1)
