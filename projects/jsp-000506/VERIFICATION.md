# Verification evidence

The run below completed successfully on September 17, 2026. It checks the
finite theorem described in the README, not the full asymptotic prize problem.

- Tested source commit: `8b9764fd38e85f615b9b871a0e2ac01b7271e952`.
- [Pinned project](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/8b9764fd38e85f615b9b871a0e2ac01b7271e952/projects/jsp-000506).
- [Successful CI run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35168750399), job `105035622425`.
- Lean `4.34.0`; Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
  The dependency lockfile did not change during the run.
- `JSP000506.lean` SHA-256:
  `3f469ec816a59782342009e1ad0df1d47a4b2d82e429c8f77f00a4d08210263e`.
- The local source was compared byte-for-byte with the file fetched at that
  tested commit. Later documentation and evidence additions do not change it.

## Actual checks

`lake build --wfail` succeeded, with 3,095 build jobs including cached
prerequisites. `lake env leanchecker --fresh JSP000506` completed successfully;
it replays both local and imported declarations into an empty Lean kernel
environment. This uses Lean's own kernel, not an independent implementation.

`lake env lean Audit.lean` printed the dependency closure of five targets:

| Target | Reported axioms |
| --- | --- |
| `JSP000506.concentration_reduction` | `propext`, `Classical.choice`, `Quot.sound` |
| `JSP000506.heckel_proposition3` | `propext`, `Classical.choice`, `Quot.sound` |
| `JSP000506.chi_mono` | `propext`, `Classical.choice`, `Quot.sound` |
| `JSP000506.zeta_compl` | `propext`, `Classical.choice`, `Quot.sound` |
| `JSP000506.zeta_le_chi` | `propext`, `Classical.choice`, `Quot.sound` |

No `sorryAx`, custom axiom, or native-evaluation axiom was reported for these
targets. The submitted source contains no `sorry`, `admit`, `axiom`,
`native_decide`, or `unsafe` tokens. This source scan complements the actual
proof checks; it does not replace them.

The workflow used a clean Ubuntu 24.04 hosted runner, checkout with credential
persistence disabled, and read-only repository permissions. It fetched the
pinned Lean toolchain and locked dependencies and used Mathlib's build cache.
The final kernel replay rechecked imported declarations. Network access was
not disabled, and no air-gap or compiler-bootstrap audit is claimed.

## Evidence retention

`verification/ci-excerpt.log` preserves the relevant original timestamped
build and axiom output. `verification/run.json` preserves the retrieved job
conclusions and artifact metadata. The excerpt is not the complete job log.

[CI artifact](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35168750399/artifacts/10475394250):
`jsp-000506-evidence`, 921 bytes; ZIP SHA-256
`f25b5e97519934577667e7f553d1a9df3fd8be322635808df371a2b3ab053390`.
GitHub reported expiration on December 16, 2026; the source and compact
evidence committed here persist beyond that retention window.

There is no NaNoda or Lean4Lean run, independently signed statement review,
organizer acceptance, or award announcement in this evidence package.
