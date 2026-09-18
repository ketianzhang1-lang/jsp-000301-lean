# Executed verification of the complete JSP-000388 development

The contributor-run checks completed successfully on 2026-09-18 UTC.
We compiled the complete original-statement endpoint, not only the quadratic
obstruction. The original obstruction module is byte-identical to proof revision
`c32d8195dc69e19d9bcf96987543f306c71749f2`.

## Checks that actually passed

- **158 modules** compiled with warnings as errors: 155 upstream proof modules,
  our two proof modules, and the audit module.
- **18 theorem-closure axiom reports**, each allowing only `propext`,
  `Classical.choice` and `Quot.sound`. The complete endpoint and the imported
  affirmative proof satisfy this allowlist, with no `sorryAx` or custom axiom.
- Kernel replay of all **155 upstream modules** under the
  `ErdosProblems.Erdos477` module prefix, plus `JSP000388` and
  `JSP000388Complete`.
- All **nine actual dependency Git revisions** match the committed manifest.
- All **155 original upstream Git blob hashes**, source SHA-256 hashes,
  recorded compatibility edits and resulting local source bytes agree.
- A false-arithmetic control importing the completed project was rejected
  with the expected proof-failure diagnostic.
- The original quadratic source, toolchain pin and dependency manifest are
  retained; no unproved mathematical premise replaces a missing proof step.

[verification/verification.json](verification/verification.json) lists every
compiled module, its source/object hashes, the preparation revision and the
verification limits. The local build resumed previously successful modules only
after matching their exact source hashes and existing build outputs/logs;
subsequent audits, kernel replay and negative control were freshly executed.
The public verifier defaults to compiling every module again.
[verification/axioms.log](verification/axioms.log) and the adjacent kernel,
negative-control and local-verification logs record the executed results.
[verification/SOURCE_SHA256SUMS](verification/SOURCE_SHA256SUMS) fixes the public
integration inputs. Imported source bytes are fixed in `UPSTREAM.json`.

## Reproduction and limits

Use Lean **4.34.0**, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, the committed manifest, and the
commands in [README.md](README.md). The proof was prepared on mathematical
revision `c32d8195dc69e19d9bcf96987543f306c71749f2`; the publishing commit also
preserves the later documentation-only parent
`db3fda04a5befc61657bf677180d092876913b8a`.

Network access and pinned cached Mathlib objects are used. Kernel replay uses
Lean's own kernel and is not an independently implemented checker. NaNoda was
not run in this local environment because the Rust build toolchain was absent.
The hosted workflow additionally attempts that separate check; only a
successful run for the selected proof commit counts as its verification.
The branch's public [workflow runs](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/workflows/jsp-000388.yml)
expose that status independently of this local receipt.

These checks are not independent human certification, organizer acceptance,
a ruling on contribution eligibility or first-formalization priority.
