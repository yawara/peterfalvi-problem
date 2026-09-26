#!/usr/bin/env python3
"""Write Challenge.lean from PeterfalviProblem/Statement.lean.

The Challenge repeats the imports and the definitions of the statement module word for word,
and then states the two main theorems with `sorry`. Run `scripts/check_challenge.py` to check
that the two files still agree.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
STATEMENT = ROOT / "PeterfalviProblem" / "Statement.lean"
CHALLENGE = ROOT / "Challenge.lean"
NAMESPACE_OPEN = "namespace PeterfalviProblem\n"
NAMESPACE_CLOSE = "\nend PeterfalviProblem\n"
THEOREMS_MARKER = "/-! ## The main theorems -/\n"

HEADER = """/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
"""

MODULE_DOC = '''/-!
# Péterfalvi's problem: the statements

This file states the two main theorems. It imports only Mathlib. Its definitions repeat those
of `PeterfalviProblem.Statement` word for word, and the two proofs are left as `sorry`.
`Solution.lean` imports the complete proofs, and Comparator checks that the two files state the
same theorems about the same definitions.

Glauberman and Norton end their 1993 paper with a problem of Péterfalvi:

> **Problem** (Péterfalvi). Can the hypothesis of Proposition 9 be satisfied for `p = 3`?

The same question is Problem 1 in Appendix C of Bender–Glauberman (1994).
`not_hypothesisB_three` answers it: no. `hypothesisB_two` shows that the hypothesis can hold for
`p = 2` (Example 10 of Glauberman–Norton), so the definition is not empty.

Let `p` and `q` be primes and let `F = 𝔽_{p^q}` (`GaloisField p q`).

* `P` is the additive group of `F`. We write it multiplicatively, as `Multiplicative F`, so that
  it can be the first factor of a semidirect product.
* `U` is the group of elements of `Fˣ` whose norm over `𝔽_p` is `1`.
* `U` acts on `P` by multiplication, and `H = P ⋊ U` is the semidirect product.
* `P₀` is the image in `H` of the additive group of the prime field `𝔽_p`.

**Hypothesis (B)** for a group `G`: there are an injective homomorphism `σ : H → G`, a finite
abelian subgroup `Q` of `G` whose order is prime to `p`, and an element `y ∈ Q`, such that
`σ(P₀)` normalizes `Q` and `σ(P₀)^y = y⁻¹ σ(P₀) y` normalizes `σ(U)`. Proposition 9 also assumes
condition (A): `q ∤ p - 1`.

## References

* G. Glauberman and S. P. Norton, *On a combinatorial problem associated with the odd order
  theorem*, Proc. Amer. Math. Soc. **119** (1993), 1089–1094.
* H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*, London Math. Soc.
  Lecture Note Series 188, Cambridge University Press, 1994.
-/
'''

THEOREMS = '''/-- **The answer to Péterfalvi's problem.** Let `q` be a prime with `q ∤ 3 - 1`. This is
condition (A) of Proposition 9 of Glauberman–Norton for `p = 3`. Then no group `G` satisfies
hypothesis (B) for `p = 3` and `q`. -/
theorem not_hypothesisB_three (q : ℕ) (hq : q.Prime) (hA : ¬ q ∣ 3 - 1) (G : Type*) [Group G] :
    ¬ HypothesisB 3 q G := by
  sorry

/-- **Hypothesis (B) can hold for `p = 2`.** For every `q ≠ 0`, the group `SL(2, 2^q)` satisfies
hypothesis (B) for `p = 2` and `q`. This is Example 10 of Glauberman–Norton. -/
theorem hypothesisB_two (q : ℕ) (hq : q ≠ 0) :
    HypothesisB 2 q (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 q)) := by
  sorry
'''


def split_statement(text: str) -> tuple[str, str]:
    """Return the import block and the definitions of the statement module."""
    imports = "".join(line + "\n" for line in text.splitlines() if line.startswith("import "))
    start = text.index(NAMESPACE_OPEN) + len(NAMESPACE_OPEN)
    end = text.rindex(NAMESPACE_CLOSE)
    return imports, text[start:end]


def challenge_text() -> str:
    imports, definitions = split_statement(STATEMENT.read_text(encoding="utf-8"))
    return (HEADER + imports + "\n" + MODULE_DOC + "\n" + NAMESPACE_OPEN + definitions + "\n"
            + THEOREMS_MARKER + "\n" + THEOREMS + NAMESPACE_CLOSE)


if __name__ == "__main__":
    CHALLENGE.write_text(challenge_text(), encoding="utf-8")
    print(f"wrote {CHALLENGE.relative_to(ROOT)}")
