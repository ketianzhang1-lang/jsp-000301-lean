/-
Copyright 2026. Released under the Apache License 2.0.
Contribution: ketianzhang1-lang, with OpenAI ChatGPT assistance.
This driver selects complete theorem dependencies and calls the official
Lean.Environment.replay implementation in Lean 4.33.0.
-/
import Lean.Replay
import Lean.Util.FoldConsts

open Lean

def allowedAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

unsafe def main (args : List String) : IO UInt32 := do
  let module :: targets := args | throw <| IO.userError "Expected module and theorem names"
  if targets.isEmpty then throw <| IO.userError "No theorem targets"
  initSearchPath (← findSysroot)
  Lean.withImportModules #[{module := module.toName}] {} fun imported => do
    let constants := imported.constants.map₁
    for target in targets do
      let some ci := constants[target.toName]? | throw <| IO.userError s!"Missing {target}"
      unless ci.isTheorem && !ci.isUnsafe && !ci.isPartial do
        throw <| IO.userError s!"Not a safe theorem: {target}"
    let mut selected : Std.HashMap Name ConstantInfo := {}
    let mut pending := targets.map String.toName
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      if selected.contains name then continue
      let some ci := constants[name]? | throw <| IO.userError s!"Missing dependency {name}"
      if ci.isUnsafe || ci.isPartial then
        throw <| IO.userError s!"Unsafe or partial proof dependency {name}"
      if ci.isAxiom && !allowedAxioms.contains name then
        throw <| IO.userError s!"Unpermitted axiom: {name}"
      selected := selected.insert name ci
      for dependency in ci.getUsedConstantsAsSet do
        pending := dependency :: pending
      match ci with
      | .inductInfo info => pending := info.all ++ info.ctors ++ pending
      | .ctorInfo info => pending := info.induct :: pending
      | .recInfo info => pending := info.all ++ pending
      | .quotInfo _ => pending := `Eq :: pending
      | _ => pure ()
    IO.println s!"Selected {selected.size} declarations for {targets.length} theorem targets."
    (← IO.getStdout).flush
    let checked ← (← mkEmptyEnvironment).replay selected
    for target in targets do
      let some actual := checked.toKernelEnv.find? target.toName
        | throw <| IO.userError s!"Target was not replayed: {target}"
      let some expected := selected[target.toName]?
        | throw <| IO.userError s!"Target was not selected: {target}"
      unless actual.isTheorem && actual.type == expected.type &&
          actual.levelParams == expected.levelParams do
        throw <| IO.userError s!"Replayed theorem statement changed: {target}"
    IO.println s!"Fresh Lean kernel checked {selected.size} declarations for {targets.length} targets; all dependencies replayed and axioms allowed."
  return 0
