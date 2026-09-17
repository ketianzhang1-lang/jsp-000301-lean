import Lake
import Lean
open Lake DSL
package LocalVerification443
@[«script»] unsafe def compile : ScriptFn := fun args => do
  let some path := args[0]? | throw <| IO.userError "expected source path"
  let some moduleName := args[1]? | throw <| IO.userError "expected module name"
  let some output := args[2]? | throw <| IO.userError "expected output path"
  let source ← IO.FS.readFile path
  let sysroot ← Lean.findSysroot
  Lean.initSearchPath sysroot
  Lean.enableInitializersExecution
  let result ← Lean.Elab.runFrontend source {} path moduleName.toName
    (trustLevel := 0) (oleanFileName? := some (System.FilePath.mk output))
  return if result.isSome then 0 else 1
