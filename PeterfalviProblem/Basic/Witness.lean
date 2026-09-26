/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import PeterfalviProblem.Basic.FrobeniusGroup

/-!
# Witnesses of hypothesis (B)

A `Witness p q G` holds the data of hypothesis (B) for the group `G`, together with the two
conditions on `q` in Proposition 9 of Glauberman–Norton: `q` is prime, and `q ∤ p - 1`
(condition (A)). It also gives names to the images `P = σ(P)`, `U = σ(U)` and `P₀ = σ(P₀)` in `G`,
because the proof refers to them all the time.

`HypothesisB.nonempty_witness` builds a witness from hypothesis (B) and the two conditions on `q`.
The only change is the direction of conjugation. Hypothesis (B) asks `σ(P₀)^y = y⁻¹ σ(P₀) y` to
normalize `σ(U)`. A witness stores the inverse `y⁻¹` as `Witness.y`. With this element, the same
subgroup is `y σ(P₀) y⁻¹`, which is `MulAut.conj y • σ(P₀)` in Mathlib.

## Main results

* `Witness.s_not_normalizes_U`: the element `x = σ(inl 1)` of `σ(P₀)` does not normalize `σ(U)`.
* `Witness.eq_one_of_mem_Q_of_pow_p_eq_one`: an element of `Q` of order dividing `p` is trivial.
-/

namespace PeterfalviProblem

open scoped Pointwise

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

variable (p q G) in
/-- A witness of hypothesis (B) for the primes `p`, `q` and the group `G`, with condition (A).

The subgroups `P`, `U` and `P₀` of `G` are the images of `normOneFrobeniusKernel p q`,
`normOneFrobeniusComplement p q` and `primeLine p q` under `sigma`. The element `y` is the
inverse of the element `y` of hypothesis (B); see the module docstring. -/
structure Witness where
  /-- The injective homomorphism `σ : H → G`. -/
  sigma : normOneFrobeniusGroup p q →* G
  sigma_injective : Function.Injective sigma
  /-- The finite abelian subgroup `Q` of `G`, of order prime to `p`. -/
  Q : Subgroup G
  Q_finite : Finite Q
  Q_commutative : IsMulCommutative Q
  Q_pPrime : ¬ p ∣ Nat.card Q
  /-- The element `y ∈ Q`: the inverse of the element `y` of hypothesis (B). -/
  y : G
  y_mem_Q : y ∈ Q
  /-- The image `P = σ(P)`. -/
  P : Subgroup G
  /-- The image `U = σ(U)`. -/
  U : Subgroup G
  /-- The image `P₀ = σ(P₀)`. -/
  P0 : Subgroup G
  sigma_P_eq_P : (normOneFrobeniusKernel p q).map sigma = P
  sigma_U_eq_U : (normOneFrobeniusComplement p q).map sigma = U
  sigma_P0_eq_P0 : (primeLine p q).map sigma = P0
  /-- `σ(P₀)` normalizes `Q`. -/
  P0_normalizes_Q : P0 ≤ Subgroup.normalizer (Q : Set G)
  /-- `y σ(P₀) y⁻¹` normalizes `σ(U)`. -/
  P0_conj_y_normalizes_U : MulAut.conj y • P0 ≤ Subgroup.normalizer (U : Set G)
  q_prime : q.Prime
  /-- Condition (A): `q ∤ p - 1`. -/
  q_not_dvd : ¬ q ∣ p - 1

/-- Conjugating the image of a homomorphism is the image of the conjugated homomorphism. -/
theorem conj_smul_map {H : Type*} [Group H] (g : G) (K : Subgroup H) (f : H →* G) :
    MulAut.conj g • K.map f = K.map ((MulAut.conj g).toMonoidHom.comp f) := by
  ext z
  simp only [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map, MonoidHom.coe_comp,
    MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.smul_def]
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨f k, ⟨k, hk, rfl⟩, rfl⟩

/-- Hypothesis (B), together with the conditions that `q` is prime and `q ∤ p - 1`, gives a
witness. -/
theorem HypothesisB.nonempty_witness (hB : HypothesisB p q G) (hq : q.Prime)
    (hA : ¬ q ∣ p - 1) : Nonempty (Witness p q G) := by
  obtain ⟨σ, hσ, Q, hQfin, hQcomm, hQp, y, hyQ, hP0Q, hP0U⟩ := hB
  exact ⟨{
    sigma := σ
    sigma_injective := hσ
    Q := Q
    Q_finite := hQfin
    Q_commutative := hQcomm
    Q_pPrime := hQp
    y := y⁻¹
    y_mem_Q := Q.inv_mem hyQ
    P := (normOneFrobeniusKernel p q).map σ
    U := (normOneFrobeniusComplement p q).map σ
    P0 := (primeLine p q).map σ
    sigma_P_eq_P := rfl
    sigma_U_eq_U := rfl
    sigma_P0_eq_P0 := rfl
    P0_normalizes_Q := hP0Q
    P0_conj_y_normalizes_U := by rw [conj_smul_map]; exact hP0U
    q_prime := hq
    q_not_dvd := hA }⟩

namespace Witness

/-- An element of `Q` whose `p`-th power is `1` is trivial, because `|Q|` is prime to `p`. -/
theorem eq_one_of_mem_Q_of_pow_p_eq_one (data : Witness p q G) {x : G} (hx : x ∈ data.Q)
    (hxp : x ^ p = 1) : x = 1 := by
  have := data.Q_finite
  have hord : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
  rcases (Nat.Prime.eq_one_or_self_of_dvd (Fact.out : p.Prime) _ hord) with h1 | hp
  · exact orderOf_eq_one_iff.mp h1
  · exfalso
    refine data.Q_pPrime ?_
    have hsub : orderOf (⟨x, hx⟩ : data.Q) = orderOf x :=
      (orderOf_injective data.Q.subtype Subtype.val_injective ⟨x, hx⟩).symm
    have : orderOf (⟨x, hx⟩ : data.Q) ∣ Nat.card data.Q := orderOf_dvd_natCard _
    rw [hsub, hp] at this
    exact this

/-- Elements of `Q` commute. -/
theorem Q_mul_comm (data : Witness p q G) {x y : G} (hx : x ∈ data.Q) (hy : y ∈ data.Q) :
    x * y = y * x := by
  have := data.Q_commutative
  exact setLike_mul_comm (s := data.Q) hx hy

/-- The element `x = σ(inl 1)` of `σ(P₀)`. It generates `σ(P₀)`. -/
noncomputable def s (data : Witness p q G) : G :=
  data.sigma (primeLineGenerator p q)

theorem s_mem_P0 (data : Witness p q G) : data.s ∈ data.P0 := by
  rw [← data.sigma_P0_eq_P0]
  exact ⟨primeLineGenerator p q, primeLineGenerator_mem p q, rfl⟩

theorem s_mem_P (data : Witness p q G) : data.s ∈ data.P := by
  rw [← data.sigma_P_eq_P]
  exact ⟨primeLineGenerator p q, ⟨Multiplicative.ofAdd 1, rfl⟩, rfl⟩

/-- The element `x = σ(inl 1)` does not normalize `σ(U)`. Take `u ≠ 1` in `U`. If `x`
normalized `σ(U)`, then `x · u · x⁻¹` would lie in `U`, which forces `u = 1`. -/
theorem s_not_normalizes_U (data : Witness p q G) :
    data.s ∉ Subgroup.normalizer (data.U : Set G) := by
  intro hsN
  obtain ⟨u, hu⟩ := exists_normOneUnit_ne_one p q data.q_prime.one_lt
  have huU : data.sigma (SemidirectProduct.inr u) ∈ data.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr u, ⟨u, rfl⟩, rfl⟩
  have hconj : data.s * data.sigma (SemidirectProduct.inr u) * data.s⁻¹ ∈ data.U :=
    (Subgroup.mem_normalizer_iff.mp hsN _).mp huU
  rw [← data.sigma_U_eq_U] at hconj
  obtain ⟨h, hhU, hh⟩ := hconj
  have hh' : h = primeLineGenerator p q * SemidirectProduct.inr u * (primeLineGenerator p q)⁻¹ :=
    data.sigma_injective (by rw [hh, s, map_mul, map_mul, map_inv])
  exact hu (eq_one_of_conj_primeLineGenerator_mem p q u (hh' ▸ hhU))

end Witness

end PeterfalviProblem
