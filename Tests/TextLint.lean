/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Tactic.Linter.TextBased

/-!
# Text and module-name lint for all source files

Run `lake env lean Tests/TextLint.lean` from the repository root.

The program finds `PeterfalviProblem.lean` and every Lean source file below
`PeterfalviProblem/`, and adds `Challenge.lean` and `Solution.lean`. It applies Mathlib's text
linters and module-name linters, with no exceptions. It does not change any file.

This file is a test program. The library does not import it.
-/

open Lean Lean.Linter Mathlib.Linter.TextBased

namespace PeterfalviProblemTests

/-- Lint every source module, including files missing from `PeterfalviProblem.lean`. -/
def lintSources : IO Unit := do
  unless ← ("PeterfalviProblem.lean" : System.FilePath).pathExists do
    throw <| IO.userError "Run the text lint from the repository root."
  let paths ← ("PeterfalviProblem" : System.FilePath).walkDir
  let mut modules := #[`PeterfalviProblem, `Challenge, `Solution]
  for path in paths do
    if path.extension == some "lean" && !(← path.isDir) then
      modules := modules.push <|
        (path.withExtension "").components.foldl Name.str .anonymous
  modules := modules.qsort Name.lt
  let options : LinterOptions := { toOptions := {}, linterSets := {} }
  let textErrors ← lintModules options #[] modules .humanReadable false
  let nameErrors := (← modulesNotUpperCamelCase options modules) +
    (← modulesOSForbidden options modules)
  unless textErrors == 0 && nameErrors == 0 do
    throw <| IO.userError
      s!"Text lint failed: {textErrors} files with text errors; {nameErrors} module-name errors."
  IO.println s!"Text lint passed: {modules.size} source modules; no exceptions."

run_cmd liftM lintSources

end PeterfalviProblemTests
