/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import PeterfalviProblem
import Solution
import Lean.Util.CollectAxioms

/-!
# Axiom audit for every declaration of the library

Run `lake env lean Tests/Axioms.lean` from the repository root after `lake build`.

The audit checks every declaration from a `PeterfalviProblem` module or from `Solution`,
including private declarations. Each may depend only on `propext`, `Classical.choice` and
`Quot.sound`. The audit also checks that `PeterfalviProblem.lean` imports every source file below
`PeterfalviProblem/`.

This file is a test program. The library does not import it.
-/

open Lean Elab Command

namespace PeterfalviProblemTests

/-- The modules of the source files below `PeterfalviProblem/`. -/
def sourceModules : IO (Array Name) := do
  unless ← ("PeterfalviProblem.lean" : System.FilePath).pathExists do
    throw <| IO.userError "Run the axiom audit from the repository root."
  let paths ← ("PeterfalviProblem" : System.FilePath).walkDir
  let mut modules := #[]
  for path in paths do
    if path.extension == some "lean" && !(← path.isDir) then
      modules := modules.push <|
        (path.withExtension "").components.foldl Name.str .anonymous
  return modules.qsort Name.lt

/-- Check the axioms of every declaration of the library. -/
def auditAxioms : CommandElabM Unit := do
  let modules ← sourceModules
  let env ← getEnv
  let imported := env.header.moduleNames
  for moduleName in modules do
    unless imported.contains moduleName do
      throwError "The source module `{moduleName}` is not imported by `PeterfalviProblem`."
  let declarations := env.constants.map₁.fold (init := #[]) fun names name _ => Id.run do
    let some index := env.getModuleIdxFor? name | return names
    let moduleName := env.header.moduleNames[index]!
    if moduleName.getRoot == `PeterfalviProblem || moduleName == `Solution then
      return names.push (name, moduleName)
    return names
  let declarations := declarations.qsort fun left right => left.1.lt right.1
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for (name, moduleName) in declarations do
    let axioms ← Lean.collectAxioms name
    let disallowed := axioms.filter fun axiomName => !allowed.contains axiomName
    unless disallowed.isEmpty do
      throwError "`{name}` from `{moduleName}` uses disallowed axioms: {disallowed}"
  logInfo m!"Axiom audit passed: {declarations.size} declarations in {modules.size} modules."

run_cmd auditAxioms

end PeterfalviProblemTests
