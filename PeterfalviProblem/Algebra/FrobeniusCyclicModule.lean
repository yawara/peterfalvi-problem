/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.AnnihilatingPolynomial

/-!
# The Frobenius module `𝔽_{p^q}`

The field `𝔽_{p^q}` is a module over the polynomial ring `𝔽_p[X]`, where `X` acts as the
Frobenius map `y ↦ y^p`. This file proves two facts about this module.

* The minimal polynomial of the Frobenius map is `X^q - 1` (`minpoly_frobEnd`). So the module is
  cyclic: it is isomorphic to `𝔽_p[X] / (X^q - 1)`. Hence, if every polynomial that kills `S` also
  kills `S'`, then `S'` is a polynomial multiple of `S` (`exists_aeval_frobEnd_eq_of_forall_imp`).
* If `p ∤ q`, then `X^q - 1` has no repeated factors. So if `cⁿ` kills `S`, then `c` kills `S`
  (`aeval_frobEnd_eq_zero_of_pow`). The proof uses this with `p = 3`, `c = a - 1` and `n = 3`, to
  turn `a³ · S = S` into `a · S = S`.

`aeval_frobEnd_apply` writes the action of a polynomial `c` as `y ↦ ∑ⱼ cⱼ y^{pʲ}`.
-/

namespace PeterfalviProblem

open Polynomial

variable (p q : ℕ) [Fact p.Prime]

/-- The Frobenius map `y ↦ y^p` of `𝔽_{p^q}`, as an `𝔽_p`-linear map. -/
noncomputable def frobEnd : Module.End (ZMod p) (GaloisField p q) :=
  (FiniteField.frobeniusAlgHom (ZMod p) (GaloisField p q)).toLinearMap

theorem frobEnd_apply (y : GaloisField p q) : frobEnd p q y = y ^ p := by
  simp [frobEnd, ZMod.card p]

theorem frobEnd_pow_apply (j : ℕ) (y : GaloisField p q) :
    (frobEnd p q ^ j) y = y ^ p ^ j := by
  induction j with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, frobEnd_apply, ← pow_mul, ← pow_succ]

/-- The minimal polynomial of the Frobenius map is `X^q - 1`. This is Mathlib's
`FiniteField.minpoly_frobeniusAlgHom`, which uses the linear independence of the field
automorphisms. -/
theorem minpoly_frobEnd (hq0 : q ≠ 0) :
    minpoly (ZMod p) (frobEnd p q) = X ^ q - 1 := by
  have h := FiniteField.minpoly_frobeniusAlgHom (ZMod p) (GaloisField p q)
  rwa [GaloisField.finrank p hq0] at h

/-- A polynomial `c` acts by `y ↦ ∑ⱼ cⱼ y^{pʲ}`. -/
theorem aeval_frobEnd_apply (c : (ZMod p)[X]) (y : GaloisField p q) :
    aeval (frobEnd p q) c y
      = ∑ j ∈ Finset.range (c.natDegree + 1), (c.coeff j).val • y ^ p ^ j := by
  rw [aeval_eq_sum_range, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, frobEnd_pow_apply, ← Nat.cast_smul_eq_nsmul (ZMod p),
    ZMod.natCast_val, ZMod.cast_id]

/-- `X^q - 1` kills every element, because the `q`-th power of the Frobenius map is the
identity. -/
theorem aeval_frobEnd_self_eq_zero (hq0 : q ≠ 0) (y : GaloisField p q) :
    aeval (frobEnd p q) (X ^ q - 1 : (ZMod p)[X]) y = 0 := by
  have h := minpoly.aeval (ZMod p) (frobEnd p q)
  rw [minpoly_frobEnd p q hq0] at h
  rw [h]
  rfl

/-- The module is cyclic. There is an element `θ` whose annihilator is exactly the ideal
`(X^q - 1)`, and every element is a polynomial multiple of `θ`. -/
theorem exists_frobenius_cyclic_vector (hq0 : q ≠ 0) :
    ∃ θ : GaloisField p q,
      (∀ c : (ZMod p)[X],
        aeval (frobEnd p q) c θ = 0 ↔ (X ^ q - 1 : (ZMod p)[X]) ∣ c) ∧
      ∀ y : GaloisField p q, ∃ c : (ZMod p)[X], aeval (frobEnd p q) c θ = y := by
  classical
  obtain ⟨θ', hθ'⟩ :=
    Module.exists_ker_toSpanSingleton_eq_annihilator (R := (ZMod p)[X])
      (M := Module.AEval' (frobEnd p q))
  set θ : GaloisField p q := (Module.AEval'.of (frobEnd p q)).symm θ' with hθdef
  have hsmul : ∀ c : (ZMod p)[X], aeval (frobEnd p q) c θ
      = (Module.AEval'.of (frobEnd p q)).symm (c • θ') := fun c =>
    (Module.AEval.of_symm_smul (a := frobEnd p q) c θ').symm
  have hann : ∀ c : (ZMod p)[X],
      aeval (frobEnd p q) c θ = 0 ↔ (X ^ q - 1 : (ZMod p)[X]) ∣ c := by
    intro c
    rw [hsmul c, LinearEquiv.map_eq_zero_iff]
    have hker : (c • θ' = 0) ↔
        c ∈ LinearMap.ker (LinearMap.toSpanSingleton ((ZMod p)[X]) _ θ') := by
      simp [LinearMap.mem_ker]
    rw [hker, hθ', ← Polynomial.span_minpoly_eq_annihilator, minpoly_frobEnd p q hq0,
      Ideal.mem_span_singleton]
  refine ⟨θ, hann, ?_⟩
  -- the Frobenius orbit of `θ` is linearly independent, hence spans by dimension count
  have hli : LinearIndependent (ZMod p) fun j : Fin q => (frobEnd p q ^ (j : ℕ)) θ := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    set c : (ZMod p)[X] := ∑ j : Fin q, C (g j) * X ^ (j : ℕ) with hc
    have hcθ : aeval (frobEnd p q) c θ = 0 := by
      calc aeval (frobEnd p q) c θ
          = ∑ j : Fin q, g j • (frobEnd p q ^ (j : ℕ)) θ := by
            rw [hc, map_sum, LinearMap.sum_apply]
            exact Finset.sum_congr rfl fun j _ => by
              rw [map_mul, aeval_C, aeval_X_pow, Module.End.mul_apply,
                Module.algebraMap_end_apply]
        _ = 0 := hg
    have hdvd := (hann c).mp hcθ
    have hdeg : c.degree < (X ^ q - 1 : (ZMod p)[X]).degree := by
      have hdm : ((X : (ZMod p)[X]) ^ q - 1).degree = (q : WithBot ℕ) := by
        rw [← C_1]
        exact degree_X_pow_sub_C (Nat.pos_of_ne_zero hq0) 1
      rw [hdm, hc]
      refine lt_of_le_of_lt (degree_sum_le _ _) ?_
      rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe q)]
      intro j _
      exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by exact_mod_cast j.isLt)
    have hc0 : c = 0 := eq_zero_of_dvd_of_degree_lt hdvd hdeg
    intro i
    have hci := congrArg (fun r => coeff r (i : ℕ)) hc0
    simp only [hc, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at hci
    rwa [Finset.sum_eq_single i (fun j _ hji =>
        ite_eq_right fun h => hji (Fin.val_injective h.symm))
      (fun h => absurd (Finset.mem_univ i) h), ite_eq_left rfl] at hci
  have hcard : Fintype.card (Fin q) = Module.finrank (ZMod p) (GaloisField p q) := by
    rw [Fintype.card_fin, GaloisField.finrank p hq0]
  have : Nonempty (Fin q) := ⟨⟨0, Nat.pos_of_ne_zero hq0⟩⟩
  have hspan := hli.span_eq_top_of_card_eq_finrank hcard
  intro y
  have hy : y ∈ Submodule.span (ZMod p)
      (Set.range fun j : Fin q => (frobEnd p q ^ (j : ℕ)) θ) := by
    rw [hspan]
    exact Submodule.mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hy
  obtain ⟨gc, hgy⟩ := hy
  refine ⟨∑ j ∈ gc.support, C (gc j) * X ^ (j : ℕ), ?_⟩
  calc aeval (frobEnd p q) (∑ j ∈ gc.support, C (gc j) * X ^ (j : ℕ)) θ
      = ∑ j ∈ gc.support, gc j • (frobEnd p q ^ (j : ℕ)) θ := by
        rw [map_sum, LinearMap.sum_apply]
        exact Finset.sum_congr rfl fun j _ => by
          rw [map_mul, aeval_C, aeval_X_pow, Module.End.mul_apply,
            Module.algebraMap_end_apply]
    _ = y := by simpa [Finsupp.sum] using hgy

/-- If every polynomial that kills `S` also kills `S'`, then `S'` is a polynomial multiple of
`S`. This follows from the cyclicity of the module. -/
theorem exists_aeval_frobEnd_eq_of_forall_imp (hq0 : q ≠ 0) {S S' : GaloisField p q}
    (hann : ∀ c : (ZMod p)[X],
      aeval (frobEnd p q) c S = 0 → aeval (frobEnd p q) c S' = 0) :
    ∃ a : (ZMod p)[X], aeval (frobEnd p q) a S = S' := by
  classical
  obtain ⟨θ, hθdvd, hθsurj⟩ := exists_frobenius_cyclic_vector p q hq0
  obtain ⟨cS, hcS⟩ := hθsurj S
  obtain ⟨cS', hcS'⟩ := hθsurj S'
  set m : (ZMod p)[X] := X ^ q - 1 with hm
  have hm0 : m ≠ 0 := by
    intro h0
    have hdm : ((X : (ZMod p)[X]) ^ q - 1).degree = (q : WithBot ℕ) := by
      rw [← C_1]
      exact degree_X_pow_sub_C (Nat.pos_of_ne_zero hq0) 1
    rw [← hm, h0, degree_zero] at hdm
    exact absurd hdm.symm (by simp)
  have haux : ∀ y : GaloisField p q, ∀ a b : (ZMod p)[X],
      aeval (frobEnd p q) (a * b) y
        = aeval (frobEnd p q) a (aeval (frobEnd p q) b y) := by
    intro y a b
    rw [map_mul, Module.End.mul_apply]
  set g : (ZMod p)[X] := GCDMonoid.gcd cS m with hg
  have hg0 : g ≠ 0 := gcd_ne_zero_of_right hm0
  set s₁ : (ZMod p)[X] := cS / g with hs₁def
  set m₁ : (ZMod p)[X] := m / g with hm₁def
  have hs₁ : g * s₁ = cS := EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_left _ _)
  have hm₁ : g * m₁ = m := EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_right _ _)
  have hm₁0 : m₁ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hm₁
    exact hm0 hm₁.symm
  -- `m₁` kills `S`, hence kills `S'`
  have hkillS : aeval (frobEnd p q) m₁ S = 0 := by
    rw [← hcS, ← haux θ m₁ cS]
    exact (hθdvd _).mpr ⟨s₁, by linear_combination (-(m₁)) * hs₁ + s₁ * hm₁⟩
  have hkillS' := hann m₁ hkillS
  -- hence `m ∣ m₁ * cS'`, and cancelling `m₁` gives `g ∣ cS'`
  rw [← hcS', ← haux θ m₁ cS'] at hkillS'
  obtain ⟨k, hk⟩ := (hθdvd _).mp hkillS'
  have hgcS' : cS' = g * k := by
    have hcancel : m₁ * cS' = m₁ * (g * k) := by
      linear_combination hk + (-(k)) * hm₁
    exact mul_left_cancel₀ hm₁0 hcancel
  -- Bézout: `s₁` and `m₁` are coprime
  have hcop : IsCoprime s₁ m₁ := by
    rw [hs₁def, hm₁def, hg]
    exact isCoprime_div_gcd_div_gcd hm0
  obtain ⟨u, v, huv⟩ := hcop
  -- the multiplier: `a := u * k`
  refine ⟨u * k, ?_⟩
  have hexpand : (u * k) * cS = cS' - v * k * m := by
    linear_combination (-(u * k)) * hs₁ + (-(v * k)) * hm₁ + (-1 : (ZMod p)[X]) * hgcS'
      + (g * k) * huv
  rw [← hcS, ← haux θ (u * k) cS, hexpand, map_sub, LinearMap.sub_apply, hcS',
    (hθdvd (v * k * m)).mpr ⟨v * k, by ring⟩, sub_zero]

/-- If `p ∤ q` and `cⁿ` kills `S`, then `c` kills `S`. Here we use that `X^q - 1` has no repeated
factors when `p ∤ q`. -/
theorem aeval_frobEnd_eq_zero_of_pow (hq0 : q ≠ 0) (hpq : ¬ p ∣ q)
    {S : GaloisField p q} {c : (ZMod p)[X]} {n : ℕ} (hn : n ≠ 0)
    (h : aeval (frobEnd p q) (c ^ n) S = 0) : aeval (frobEnd p q) c S = 0 := by
  classical
  set m : (ZMod p)[X] := X ^ q - 1 with hm
  have hsq : Squarefree m := by
    have hsep : Polynomial.Separable m := by
      rw [hm]
      refine (X_pow_sub_one_separable_iff).mpr ?_
      simpa [Ne, ZMod.natCast_eq_zero_iff] using hpq
    exact hsep.squarefree
  have haux : ∀ y : GaloisField p q, ∀ a b : (ZMod p)[X],
      aeval (frobEnd p q) (a * b) y
        = aeval (frobEnd p q) a (aeval (frobEnd p q) b y) := by
    intro y a b
    rw [map_mul, Module.End.mul_apply]
  set g : (ZMod p)[X] := EuclideanDomain.gcd (c ^ n) m with hg
  -- Bézout: `g` kills `S`
  have hgS : aeval (frobEnd p q) g S = 0 := by
    have h1 : aeval (frobEnd p q) (c ^ n * EuclideanDomain.gcdA (c ^ n) m) S = 0 := by
      rw [mul_comm (c ^ n) _, haux S _ (c ^ n), h, map_zero]
    have h2 : aeval (frobEnd p q) (m * EuclideanDomain.gcdB (c ^ n) m) S = 0 := by
      rw [mul_comm m _, haux S _ m, hm, aeval_frobEnd_self_eq_zero p q hq0, map_zero]
    rw [hg, EuclideanDomain.gcd_eq_gcd_ab (c ^ n) m, map_add, LinearMap.add_apply, h1, h2,
      add_zero]
  -- `g` is squarefree (divides `m`) and divides `c ^ n`, hence divides `c`
  have hgc : g ∣ c := by
    have hgsq : Squarefree g :=
      Squarefree.squarefree_of_dvd (EuclideanDomain.gcd_dvd_right (c ^ n) m) hsq
    exact (hgsq.dvd_pow_iff_dvd hn).mp (EuclideanDomain.gcd_dvd_left _ _)
  obtain ⟨d, hd⟩ := hgc
  rw [hd, mul_comm, haux, hgS, map_zero]

end PeterfalviProblem
