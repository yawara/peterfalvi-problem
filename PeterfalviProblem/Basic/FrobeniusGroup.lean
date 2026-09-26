/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import PeterfalviProblem.Basic.NormOneUnits

/-!
# The group `H = P ⋊ U`

Facts about the semidirect product `H = P ⋊ U` (`normOneFrobeniusGroup p q`) and its subgroup
`P₀` (`primeLine p q`). Here `P` is the additive group of `F = 𝔽_{p^q}`, written
multiplicatively, and `U` acts on `P` by multiplication.

## Main definitions

* `normOneFrobeniusKernel`: the subgroup `P` of `H`.
* `primeLineGenerator`: the element `x = inl 1` of `P₀`. It generates `P₀`.

## Main results

* `inl_mem_primeLine_iff`: `inl s` lies in `P₀` exactly when `s` lies in the prime field.
* `inr_inv_mul_inl_mul_inr`: conjugation by `u ∈ U` acts on `P` as multiplication by `u⁻¹`.
* `eq_one_of_conj_primeLineGenerator_mem`: `x` normalizes no nontrivial element of `U`.
-/

namespace PeterfalviProblem

variable (p q : ℕ) [Fact p.Prime]

/-- The subgroup `P` of `H = P ⋊ U`. -/
noncomputable def normOneFrobeniusKernel : Subgroup (normOneFrobeniusGroup p q) :=
  (SemidirectProduct.inl : additiveFieldGroup p q →* normOneFrobeniusGroup p q).range

@[simp] theorem normOneMulAction_apply (u : normOneUnits p q) (s : GaloisField p q) :
    ((normOneMulAction p q u) (Multiplicative.ofAdd s)).toAdd =
      ((u : (GaloisField p q)ˣ) : GaloisField p q) * s :=
  rfl

/-- The element `x = inl 1` of `P₀`. It generates `P₀`. -/
noncomputable def primeLineGenerator : normOneFrobeniusGroup p q :=
  SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q))

/-- An element `inl s` of `P` lies in `P₀` exactly when `s` lies in the prime field `𝔽_p`. -/
theorem inl_mem_primeLine_iff (s : GaloisField p q) :
    (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q) ∈
        primeLine p q ↔
      ∃ c : ZMod p, algebraMap (ZMod p) (GaloisField p q) c = s := by
  constructor
  · rintro ⟨z, hz, hzs⟩
    rw [SemidirectProduct.inl_injective hzs] at hz
    simpa using hz
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd (algebraMap (ZMod p) (GaloisField p q) c), by simp, rfl⟩

/-- The element `x = inl 1` lies in `P₀`. -/
theorem primeLineGenerator_mem : primeLineGenerator p q ∈ primeLine p q :=
  (inl_mem_primeLine_iff p q 1).mpr ⟨1, map_one _⟩

/-- `x^p = 1`, because `F` has characteristic `p`. -/
theorem primeLineGenerator_pow_p : (primeLineGenerator p q) ^ p = 1 := by
  rw [primeLineGenerator, ← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul,
    ofAdd_zero, map_one]

set_option backward.isDefEq.respectTransparency false in
/-- Conjugation by `u ∈ U` acts on `P` as multiplication by `u⁻¹`:
`(inr u)⁻¹ · inl a · inr u = inl (u⁻¹ · a)`. -/
theorem inr_inv_mul_inl_mul_inr (u : normOneUnits p q) (a : GaloisField p q) :
    (SemidirectProduct.inr u : normOneFrobeniusGroup p q)⁻¹ *
        SemidirectProduct.inl (Multiplicative.ofAdd a) * SemidirectProduct.inr u
      = SemidirectProduct.inl (Multiplicative.ofAdd
          (((u⁻¹ : (GaloisField p q)ˣ) : GaloisField p q) * a)) := by
  rw [← map_inv, ← SemidirectProduct.inl_aut_inv]
  simp [normOneMulAction, Units.smul_def]

/-- Conjugating `x = inl 1` by `u ∈ U` gives `inl u⁻¹`. -/
theorem inr_inv_mul_primeLineGenerator_mul_inr (u : normOneUnits p q) :
    (SemidirectProduct.inr u : normOneFrobeniusGroup p q)⁻¹ *
        primeLineGenerator p q * SemidirectProduct.inr u
      = SemidirectProduct.inl (Multiplicative.ofAdd
          (((u⁻¹ : (GaloisField p q)ˣ) : GaloisField p q))) := by
  rw [primeLineGenerator, inr_inv_mul_inl_mul_inr, mul_one]

/-- The element `x = inl 1` normalizes no nontrivial element of `U`: if `x · u · x⁻¹` lies in `U`,
then `u = 1`. Indeed `x · u · x⁻¹ = inl (1 - u) · u`. -/
theorem eq_one_of_conj_primeLineGenerator_mem (u : normOneUnits p q)
    (h : primeLineGenerator p q * SemidirectProduct.inr u * (primeLineGenerator p q)⁻¹ ∈
      normOneFrobeniusComplement p q) : u = 1 := by
  obtain ⟨v, hv⟩ := h
  have hleft := congrArg (fun g : normOneFrobeniusGroup p q => g.left.toAdd) hv
  simp only [primeLineGenerator, SemidirectProduct.left_inr, toAdd_one, ← map_inv,
    SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.left_inl,
    SemidirectProduct.right_inr, SemidirectProduct.right_inl, one_mul, map_one, mul_one,
    toAdd_mul, toAdd_ofAdd, ← ofAdd_neg, normOneMulAction_apply] at hleft
  refine Subtype.ext (Units.ext ?_)
  simp only [OneMemClass.coe_one, Units.val_one]
  linear_combination hleft

end PeterfalviProblem
