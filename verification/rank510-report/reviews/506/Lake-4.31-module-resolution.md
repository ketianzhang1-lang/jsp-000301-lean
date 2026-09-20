# Lean 4.31 module-target resolution

The fixed upstream Lake sources were inspected without executing Lean:

- https://github.com/leanprover/lean4/blob/v4.31.0/src/lake/Lake/CLI/Build.lean
- https://github.com/leanprover/lean4/blob/v4.31.0/src/lake/Lake/Config/LeanLibConfig.lean
- https://github.com/leanprover/lean4/blob/v4.31.0/src/lake/Lake/Config/Module.lean

The +Module syntax calls findTargetModule? and fails with unknownModule when no configured buildable module matches. A library uses roots and globs; the default globs are exactly its roots, and dotted submodules of those roots are also buildable. Name prefixes are hierarchical Lean module prefixes, not plain textual starts-with tests.

The selected lakefile declares roots JSP000506, JSP000506Bridge and JSP000506Complete. Therefore JSP000506Selection is not a buildable module target. JSP000506.VerificationSelection is a buildable dotted submodule, but it imports the manually compiled JSP000506Selection. The original verify_selection.py deliberately invokes lake env lean -o on that file directly and does not rely on Lake module-target resolution.

Recommendation: retain the original complete verification unchanged, and run equivalent explicit module/source/#check/#print/#print-axioms checks for the selection module and its auditor bridge using absolute trusted binaries. Record the CLI automation limitation separately from the proof result. A disclosed isolated configuration overlay adding only the missing root is another option, but would need separately identified config bytes and cannot be represented as the unchanged original Lake configuration. No source or dependency pin needs alteration.
