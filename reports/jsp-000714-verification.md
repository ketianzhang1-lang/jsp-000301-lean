# JSP-000714 verification receipt

Date: 2026-09-17.
Status: verified supplementary code; no prize nomination or award claim submitted.

## Scope and judgment

This independently written module formalizes the classical modular-parabola
Sidon construction and the explicit lower bound
A(N) >= 2^floor(sqrt(floor(N/8))) for every N >= 32.
It does not resolve the finer questions in Erdos 861. A broader prior public
Lean development exists in plby/lean-proofs. The code is retained as a reusable
supplement, not presented as a new complete solution or a first formalization.
See the source README for mathematical attribution and overlap.

## Pinned source

Repository: ketianzhang1-lang/jsp-000301-lean.
Commit: 86b9aeb7ae4bb8e23fae39dd07019ae4dde5d977.
Directory: projects/jsp-000714.
Lean and Mathlib: v4.34.0; Mathlib 5ed2965256430c3649e86755f9576b54eca72435.

[Source](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/86b9aeb7ae4bb8e23fae39dd07019ae4dde5d977/projects/jsp-000714)

## Actual checks

[CI run 35171596703](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35171596703)
completed successfully at the source commit above.

- Lake build with warnings treated as failures: passed, 3214 jobs.
- Bundled Lean kernel replay: passed.
- Nine named target axiom audits: passed; only propext, Classical.choice and Quot.sound.
- Locked dependency revisions: matched.
- False-arithmetic negative control: rejected as required.
- Independently implemented NaNoda: 31660 declarations checked, no errors.
- Tested-source archive and logs: uploaded by the successful workflow.

NaNoda: 4c544ed4099c8227f07d5de77ad1e69fb0740a27.
lean4export: 6cea97789dc088ea47fcea15692db85685aedac5.
The checker uses a strict three-axiom allowlist.

## Artifact

Artifact ID: 10477435151; name: jsp-000714-evidence.
Size reported by GitHub: 30206043 bytes.
ZIP SHA-256 reported by GitHub:
e99bc86b843685968a9d5bd9299a1889cf891152ee5d076b13871acbc330ebe5.

[Artifact](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35171596703/artifacts/10477435151)

Reported expiry: 2026-12-16T01:42:33Z. The archive was not separately downloaded
and rehashed in this turn; the digest above is GitHub's metadata, not a local
download measurement. Source and reproduction scripts remain in git.

These are contributor-run checks. Imported Mathlib artifacts were cached;
an offline full-library rebuild, independent human review, organizer acceptance,
prize eligibility and payment entitlement are not asserted.
