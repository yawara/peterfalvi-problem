# Working on this repository

- `PeterfalviProblem/Statement.lean` defines the objects in the main theorems. `Challenge.lean`
  repeats its imports and definitions word for word. After changing the statement module, run
  `python3 scripts/gen_challenge.py` and then `python3 scripts/check_challenge.py`.
- `Challenge.lean` imports only Mathlib. Only its two theorem proofs may be `sorry`.
  `Solution.lean` imports `PeterfalviProblem.Main`. Neither is imported by the library.
- Do not add `sorry`, `admit` or axioms to the library. Every declaration must depend only on
  `propext`, `Classical.choice` and `Quot.sound`; `Tests/Axioms.lean` checks this.
- After adding a file below `PeterfalviProblem/`, add it to `PeterfalviProblem.lean`
  (`lake exe mk_all --lib PeterfalviProblem`).
- Run `python3 scripts/check.py` for every change. It must pass with no warnings. Do not switch
  off linters to make new code pass.
- Keep `formalization.yaml`, `README.md` and `README.ja.md` consistent with the Lean statements.
  Keep the English plain: short sentences, one idea per sentence, common words.
- Yawara Ishida is the author and responsible maintainer. Record AI contributions in
  `formalization.yaml` (`automation`), not as authors.
- Keep `lean-toolchain` equal to the toolchain of the pinned Mathlib. Do not run `lake update`
  without a reason; it changes the pinned dependencies.
- Pushing, running the Palomar preflight, submitting to Palomar and registering are separate
  actions. Each needs the maintainer's instruction.
