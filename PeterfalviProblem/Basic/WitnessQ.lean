/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import PeterfalviProblem.Basic.WitnessSetup

/-!
# BG Appendix C, Lemma C.3: the conjugate prime line `P₁ = W₂^y`

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix C, §3 (pp. 148--152), Steps 3 and 4.

Hypothesis (B) supplies an element `y ∈ Q`, and BG's argument runs on the **conjugate prime
line** `P₁ = W₂^y` with generator `t = s^y`.  This file develops that line: `t` has order `p`,
`P₁ = ⟨t⟩` normalizes `U` (unlike `W₂` itself, by `W2_not_le_normalizer_U`), so conjugation by
`t` therefore induces an automorphism `tConjNormOneUnitsAut` of the norm-one group `U` of
`p`-power order.  Feeding powers of `t` through the decomposition `PU = U P₀ U` of Step 1 yields
the Step 4 decompositions, whose right components produce the norm relation `N(2a − 1) = 1`.

The second half records how `W₂` and `Q` interact: `t s⁻¹ ∈ Q`, `W₂ ∩ Q = 1`, `P ∩ Q = 1`,
the
commuting relations inside the abelian group `Q`, and the action `w2ConjQAut` of `W₂` on `Q`
used to produce the element `y_D` with `s^{y_D} = t`.

Migrated from `PeterfalviProblem.Peterfalvi.S16_CoreBounds` (issue 0151): the content is BG Appendix C,
so it is stated against the book's hypotheses (A) + (B), not against the Section 16
configuration, which merely supplies one instance of (B).
-/

namespace PeterfalviProblem

open scoped Pointwise
open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

/-- Elements of the transported `Q` commute.  This is the S16-facing form of
BG Appendix C Remark (B)/(X) used in Lemma C.3 Step 4 when rewriting (C.3) to
(C.4). -/
theorem Q_mul_comm (data : FieldNormalizerData p q G)
    {x y : G} (hx : x ∈ data.Q) (hy : y ∈ data.Q) :
    x * y = y * x := by
  have := data.Q_commutative
  exact setLike_mul_comm (s := data.Q) hx hy

-- The C.3 generator-relation interface `appC_normSet_generator_relation` is now
-- *derived* from the Step 4 capstone (`s₁ = s⁻¹`) rather than carried as a field;
-- see its definition after `step4Capstone` below.

end FieldNormalizerData

end PeterfalviProblem
