/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import PeterfalviProblem.Basic.Witness

/-!
# BG Appendix C: basic facts about `H = P ⋊ U` and its prime-field line

Elementary `(p, q)`-level facts about the Frobenius group `H = P ⋊ U` of BG Appendix C and its
prime-field line `P₀`, used throughout the Lemma C.1--C.3 development.

These were previously stated only through the Peterfalvi Section 16 hypothesis (as
`fieldNormalizer*` lemmas); nothing in them depends on that configuration, so they belong here
with the rest of the `(p, q)`-level Appendix C material (issue 0151).
-/

namespace PeterfalviProblem

/-- In the concrete BG Frobenius group `P ⋊ U`, the additive kernel and
norm-one complement generate the whole group. -/
theorem normOneFrobeniusKernel_sup_complement_eq_top (p q : ℕ) [Fact p.Prime] :
    normOneFrobeniusKernel p q ⊔ normOneFrobeniusComplement p q = ⊤ := by
  apply le_antisymm le_top
  intro g _
  rw [← SemidirectProduct.inl_left_mul_inr_right g]
  exact Subgroup.mul_mem_sup ⟨g.left, rfl⟩ ⟨g.right, rfl⟩

/-- Prime-line scalar elements invert by negating the scalar. -/
theorem primeLineElement_neg (p q : ℕ) [Fact p.Prime]
    (c : ZMod p) :
    primeLineElement p q (-c) =
      (primeLineElement p q c)⁻¹ := by
  simp [primeLineElement]

/-- The scalar `1` element is the distinguished prime-line generator. -/
theorem primeLineElement_one (p q : ℕ) [Fact p.Prime] :
    primeLineElement p q 1 = primeLineGenerator p q := by
  simp [primeLineElement, primeLineGenerator]

/-- The distinguished generator lies in the concrete prime-field line `P₀`. -/
theorem primeLineGenerator_mem (p q : ℕ) [Fact p.Prime] :
    primeLineGenerator p q ∈ primeLine p q := by
  dsimp [primeLineGenerator, primeLine, PeterfalviProblem.primeLine]
  rw [PeterfalviProblem.mem_normOneFrobeniusSubspaceKernel_inl]
  exact Submodule.subset_span (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- **Conjugation by a norm-one unit is multiplication in the field.**  For `u ∈ U` and
`a ∈ P = 𝔽_{p^q}`,

`(inr u)⁻¹ · inl a · inr u = inl (u⁻¹ · a)`.

This is the identification of the `U`-action on `P` with field multiplication, read inside the
semidirect product `H = P ⋊ U`.  In particular the `U`-orbit of the prime-line generator
`x = inl 1` is the set of *norm-one elements* of `𝔽_{p^q}` — which, for `p = 3`, is the set of
squares.  That is the set `S` of BG Appendix C, Problem 1 (issue 0180). -/
theorem inr_inv_mul_inl_mul_inr (p q : ℕ) [Fact p.Prime] (u : normOneUnits p q)
    (a : GaloisField p q) :
    (SemidirectProduct.inr u : normOneFrobeniusGroup p q)⁻¹ *
        SemidirectProduct.inl (Multiplicative.ofAdd a) * SemidirectProduct.inr u
      = SemidirectProduct.inl (Multiplicative.ofAdd
          (((u⁻¹ : (GaloisField p q)ˣ) : GaloisField p q) * a)) := by
  rw [← map_inv, ← SemidirectProduct.inl_aut_inv]
  simp [normOneMulAction, Units.smul_def]

/-- The `U`-orbit of the prime-line generator `x = σ(1)`: conjugating by `u ∈ U` gives the
element `u⁻¹` of the field, so the orbit is exactly the norm-one set. -/
theorem inr_inv_mul_primeLineGenerator_mul_inr (p q : ℕ) [Fact p.Prime]
    (u : normOneUnits p q) :
    (SemidirectProduct.inr u : normOneFrobeniusGroup p q)⁻¹ *
        primeLineGenerator p q * SemidirectProduct.inr u
      = SemidirectProduct.inl (Multiplicative.ofAdd
          (((u⁻¹ : (GaloisField p q)ˣ) : GaloisField p q))) := by
  rw [primeLineGenerator, inr_inv_mul_inl_mul_inr, mul_one]

/-- The distinguished generator of `P₀` has order dividing `p`. -/
theorem primeLineGenerator_pow_p (p q : ℕ) [Fact p.Prime] :
    (primeLineGenerator p q) ^ p = 1 := by
  have : CharP (GaloisField p q) p := by
    rw [← Algebra.charP_iff (ZMod p) (GaloisField p q)
      p]
    exact ZMod.charP p
  dsimp [primeLineGenerator]
  let inlHom :
      PeterfalviProblem.additiveFieldGroup p q →*
        normOneFrobeniusGroup p q := SemidirectProduct.inl
  rw [← map_pow inlHom, ← map_one inlHom, SemidirectProduct.inl_inj]
  rw [← ofAdd_nsmul]
  congr
  simp

/-- There is a nonidentity norm-one unit, provided `q > 1`. -/
theorem exists_normOneUnit_ne_one (p q : ℕ) [Fact p.Prime] (hq : 1 < q) :
    ∃ u : normOneUnits p q, u ≠ 1 := by
  have : Nontrivial (normOneUnits p q) :=
    Finite.one_lt_card_iff_nontrivial.mp (normOneUnits_card_gt_one p q hq)
  exact exists_ne 1

/-- The norm-one complement has order prime to `p`.  In BG Appendix C terms,
`|U| = 1 + p + ... + p^{q-1}`, so the `U`-coordinate of any `p`-element in
`P ⋊ U` must be trivial. -/
theorem normOneUnits_card_coprime_p (p q : ℕ) [Fact p.Prime] (hq : q ≠ 0) :
    Nat.Coprime p (Nat.card (normOneUnits p q)) := by
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  rw [normOneUnits_card p q hq, ← Nat.geomSum_eq hp2 q]
  have hsum :
      (∑ k ∈ Finset.range q, p ^ k) =
        (∑ k ∈ Finset.range (q - 1), p ^ (k + 1)) + 1 := by
    rw [show q = (q - 1) + 1 by omega]
    rw [Finset.sum_range_succ']
    simp
  rw [hsum, add_comm]
  have hdiv : p ∣ ∑ k ∈ Finset.range (q - 1), p ^ (k + 1) :=
    Finset.dvd_sum fun k _ => dvd_pow_self p (Nat.succ_ne_zero k)
  rw [Nat.coprime_add_iff_left hdiv]
  exact Nat.coprime_one_right p

/-- Every element of the concrete additive kernel `P ≤ P ⋊ U` has `p`-th power `1`. -/
theorem normOneFrobeniusKernel_pow_p_eq_one (p q : ℕ) [Fact p.Prime]
    {x : normOneFrobeniusGroup p q} (hx : x ∈ normOneFrobeniusKernel p q) :
    x ^ p = 1 := by
  have : CharP (GaloisField p q) p := by
    rw [← Algebra.charP_iff (ZMod p) (GaloisField p q) p]
    exact ZMod.charP p
  rcases hx with ⟨a, rfl⟩
  let inlHom :
      additiveFieldGroup p q →* normOneFrobeniusGroup p q :=
    SemidirectProduct.inl
  rw [← map_pow inlHom, ← map_one inlHom, SemidirectProduct.inl_inj]
  rw [← ofAdd_toAdd a, ← ofAdd_nsmul]
  congr
  simp

/-- In the concrete Frobenius group `P ⋊ U`, a `p`-element has trivial `U`-coordinate. -/
theorem normOneFrobeniusGroup_right_eq_one_of_pow_p_eq_one (p q : ℕ) [Fact p.Prime]
    (hq : q ≠ 0) (x : normOneFrobeniusGroup p q) (hx : x ^ p = 1) :
    (SemidirectProduct.rightHom x : normOneUnits p q) = 1 := by
  have hright_pow :
      (SemidirectProduct.rightHom x : normOneUnits p q) ^ p = 1 := by
    have h := congrArg
      (SemidirectProduct.rightHom :
        normOneFrobeniusGroup p q →* normOneUnits p q) hx
    rw [map_pow] at h
    simpa using h
  have horder_p :
      orderOf (SemidirectProduct.rightHom x : normOneUnits p q) ∣ p :=
    orderOf_dvd_of_pow_eq_one hright_pow
  have horder_card :
      orderOf (SemidirectProduct.rightHom x : normOneUnits p q) ∣
        Nat.card (normOneUnits p q) :=
    orderOf_dvd_natCard (SemidirectProduct.rightHom x : normOneUnits p q)
  have horder_one :
      orderOf (SemidirectProduct.rightHom x : normOneUnits p q) = 1 :=
    Nat.eq_one_of_dvd_coprimes (normOneUnits_card_coprime_p p q hq) horder_p horder_card
  exact orderOf_eq_one_iff.mp horder_one

/-- The concrete `p`-torsion in `P ⋊ U` is contained in the additive kernel `P`.
This is the semidirect-product core of BG's assertion `P char PU`. -/
theorem normOneFrobeniusGroup_mem_kernel_of_pow_p_eq_one (p q : ℕ) [Fact p.Prime]
    (hq : q ≠ 0) (x : normOneFrobeniusGroup p q) (hx : x ^ p = 1) :
    x ∈ normOneFrobeniusKernel p q := by
  have hright := normOneFrobeniusGroup_right_eq_one_of_pow_p_eq_one p q hq x hx
  have hright' : x.right = 1 := by
    simpa [SemidirectProduct.rightHom_eq_right] using hright
  refine ⟨x.left, ?_⟩
  calc
    SemidirectProduct.inl x.left =
        (SemidirectProduct.inl x.left : normOneFrobeniusGroup p q) * 1 := by simp
    _ = (SemidirectProduct.inl x.left : normOneFrobeniusGroup p q) *
        SemidirectProduct.inr x.right := by rw [hright']; simp
    _ = x := SemidirectProduct.inl_left_mul_inr_right x

end PeterfalviProblem
