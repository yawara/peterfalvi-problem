/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.Norm.Defs

/-!
# The objects in the statement

This file defines the objects that appear in the main theorems. `Challenge.lean` repeats
these definitions word for word, and Comparator checks that the two copies are the same.

Let `p` and `q` be primes and let `F = 𝔽_{p^q}`. We follow Glauberman–Norton (1993),
Proposition 9, which is also Theorem C in Appendix C of Bender–Glauberman (1994).

* `P` is the additive group of `F`. We write it multiplicatively, as `Multiplicative F`, so
  that it can be the first factor of a semidirect product.
* `U` is the group of elements of `Fˣ` whose norm over `𝔽_p` is `1`.
* `U` acts on `P` by multiplication, and `H = P ⋊ U` is the semidirect product.
* `P₀` is the image in `H` of the additive group of the prime field `𝔽_p`.

**Hypothesis (B)** for a group `G`: there are an injective homomorphism `σ : H → G`, a finite
abelian subgroup `Q` of `G` whose order is prime to `p`, and an element `y ∈ Q`, such that
`σ(P₀)` normalizes `Q` and `σ(P₀)^y = y⁻¹ σ(P₀) y` normalizes `σ(U)`.

## Main definitions

* `PeterfalviProblem.normOneUnits`: the group `U`.
* `PeterfalviProblem.normOneFrobeniusGroup`: the group `H = P ⋊ U`.
* `PeterfalviProblem.normOneFrobeniusComplement`: the subgroup `U` of `H`.
* `PeterfalviProblem.primeLine`: the subgroup `P₀` of `H`.
* `PeterfalviProblem.HypothesisB`: hypothesis (B).
-/

namespace PeterfalviProblem

variable (p q : ℕ) [Fact p.Prime]

/-- The additive group `P` of `𝔽_{p^q}`, written multiplicatively. -/
abbrev additiveFieldGroup := Multiplicative (GaloisField p q)

/-- The group `U` of elements of `𝔽_{p^q}ˣ` whose norm over `𝔽_p` is `1`. -/
noncomputable def normOneUnits : Subgroup (GaloisField p q)ˣ :=
  (Units.map (Algebra.norm (ZMod p) (S := GaloisField p q))).ker

/-- The action of `U` on `P` by multiplication: `u` sends `s` to `u * s`. -/
noncomputable def normOneMulAction : normOneUnits p q →* MulAut (additiveFieldGroup p q) :=
  (MulAutMultiplicative (GaloisField p q)).symm.toMonoidHom.comp
    ((AddAut.mulLeft : (GaloisField p q)ˣ →* Multiplicative (AddAut (GaloisField p q))).comp
      (normOneUnits p q).subtype)

/-- The group `H = P ⋊ U`, where `U` acts on `P` by multiplication. -/
abbrev normOneFrobeniusGroup :=
  additiveFieldGroup p q ⋊[normOneMulAction p q] normOneUnits p q

/-- The subgroup `U` of `H = P ⋊ U`. -/
noncomputable def normOneFrobeniusComplement : Subgroup (normOneFrobeniusGroup p q) :=
  (SemidirectProduct.inr : normOneUnits p q →* normOneFrobeniusGroup p q).range

/-- The subgroup `P₀` of `H = P ⋊ U`: the image of the additive group of the prime field
`𝔽_p ⊆ 𝔽_{p^q}`. -/
noncomputable def primeLine : Subgroup (normOneFrobeniusGroup p q) :=
  (AddSubgroup.toSubgroup (algebraMap (ZMod p) (GaloisField p q)).toAddMonoidHom.range).map
    (SemidirectProduct.inl : additiveFieldGroup p q →* normOneFrobeniusGroup p q)

/-- **Hypothesis (B)** of Glauberman–Norton, Proposition 9, for the primes `p`, `q` and the
group `G`: there are an injective homomorphism `σ : H → G`, a finite abelian subgroup `Q` of `G`
whose order is prime to `p`, and an element `y ∈ Q`, such that `σ(P₀)` normalizes `Q` and
`σ(P₀)^y` normalizes `σ(U)`.

Here `σ(P₀)^y = y⁻¹ σ(P₀) y` is the image of `P₀` under `h ↦ y⁻¹ σ(h) y`, because
`MulAut.conj y⁻¹ g = y⁻¹ * g * y`. -/
def HypothesisB (G : Type*) [Group G] : Prop :=
  ∃ σ : normOneFrobeniusGroup p q →* G, Function.Injective σ ∧
    ∃ Q : Subgroup G, Finite Q ∧ IsMulCommutative Q ∧ ¬ p ∣ Nat.card Q ∧
      ∃ y ∈ Q,
        (primeLine p q).map σ ≤ Subgroup.normalizer (Q : Set G) ∧
        (primeLine p q).map ((MulAut.conj y⁻¹).toMonoidHom.comp σ) ≤
          Subgroup.normalizer ((normOneFrobeniusComplement p q).map σ : Set G)

end PeterfalviProblem
