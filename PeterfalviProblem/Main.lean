/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import PeterfalviProblem.Proof.Endgame
import PeterfalviProblem.SL2Example

/-!
# The main theorems

Glauberman and Norton end their 1993 paper with a problem of Péterfalvi:

> **Problem** (Péterfalvi). Can the hypothesis of Proposition 9 be satisfied for `p = 3`?

The same question is Problem 1 in Appendix C of Bender–Glauberman (1994).

`not_hypothesisB_three` answers the question: **no**. Let `q` be a prime with `q ∤ 3 - 1`. Then
no group `G` satisfies hypothesis (B) for `p = 3` and `q`. The group `G` need not be finite.

`hypothesisB_two` shows that hypothesis (B) can hold for other primes. It is Example 10 of
Glauberman–Norton: for `p = 2` and every `q ≥ 1`, the group `SL(2, 2^q)` satisfies it.

The objects in the statements are defined in `PeterfalviProblem.Statement`.
-/

namespace PeterfalviProblem

/-- **The answer to Péterfalvi's problem.** Let `q` be a prime with `q ∤ 3 - 1`. This is
condition (A) of Proposition 9 of Glauberman–Norton for `p = 3`. Then no group `G` satisfies
hypothesis (B) for `p = 3` and `q`. -/
theorem not_hypothesisB_three (q : ℕ) (hq : q.Prime) (hA : ¬ q ∣ 3 - 1) (G : Type*) [Group G] :
    ¬ HypothesisB 3 q G := by
  intro hB
  obtain ⟨data⟩ := hB.nonempty_witness hq hA
  exact false_of_witness data rfl

/-- **Hypothesis (B) can hold for `p = 2`.** For every `q ≠ 0`, the group `SL(2, 2^q)` satisfies
hypothesis (B) for `p = 2` and `q`. This is Example 10 of Glauberman–Norton, with
`σ(P) = {[[1, a], [0, 1]]}`, `σ(U) = {[[a, 0], [0, a⁻¹]]}`, `σ(P₀) = ⟨[[1, 1], [0, 1]]⟩`,
`y = [[0, 1], [1, 1]]` and `Q = ⟨y⟩`. -/
theorem hypothesisB_two (q : ℕ) (hq : q ≠ 0) :
    HypothesisB 2 q (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 q)) :=
  ⟨sigmaSL2 q hq, sigmaSL2_injective q hq, Subgroup.zpowers SL2.elemY, inferInstance,
    inferInstance, not_two_dvd_card_zpowers_elemY q, SL2.elemY, Subgroup.mem_zpowers _,
    map_primeLine_sigmaSL2_le_normalizer q hq, map_primeLine_conj_sigmaSL2_le_normalizer q hq⟩

end PeterfalviProblem
