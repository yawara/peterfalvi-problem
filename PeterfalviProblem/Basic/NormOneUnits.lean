/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import PeterfalviProblem.Algebra.PaleySet
import PeterfalviProblem.Statement

/-!
# The norm-one units

Let `F = 𝔽_{p^q}` and let `U ≤ Fˣ` be the group of units of norm one over `𝔽_p`
(`normOneUnits p q`). This file collects the facts about `U` that the proof uses.

## Main results

* `normOneUnits_card`: `|U| = (p^q - 1) / (p - 1)`.
* `coprime_iff_not_dvd`: `(p^q - 1) / (p - 1)` is prime to `p - 1` exactly when `q ∤ p - 1`.
  So the two usual forms of condition (A) agree. This is Lemma 8 of Glauberman–Norton.
* `exists_normOneUnit_ne_one`: `U` is not trivial when `q > 1`.
* `mem_normOneUnits_iff_isSquare`: for `p = 3`, the norm-one units are the nonzero squares.
* `not_isSquare_neg_one_galois`, `isSquare_or_isSquare_neg_galois`: for `p = 3` and odd `q`,
  `-1` is not a square in `F`, so every nonzero element of `F` is a square or minus a square.
-/

namespace PeterfalviProblem

variable (p q : ℕ)

/-! ## The norm as a product -/

/-- The norm of `x ∈ 𝔽_{p^q}` over `𝔽_p`, written as the product `∏_{i<q} x^{p^i}` of the
conjugates of `x`. -/
noncomputable def normN [Fact p.Prime] (x : GaloisField p q) : GaloisField p q :=
  ∏ i ∈ Finset.range q, x ^ (p ^ i)

/-- The product `normN` is Mathlib's norm `Algebra.norm (ZMod p)`, viewed in `𝔽_{p^q}`. -/
theorem normN_eq_algebraMap_norm [Fact p.Prime] (hq : q ≠ 0) (x : GaloisField p q) :
    normN p q x = algebraMap (ZMod p) (GaloisField p q) (Algebra.norm (ZMod p) x) := by
  simpa [normN, GaloisField.finrank p hq, Nat.card_zmod]
    using (FiniteField.algebraMap_norm_eq_prod_pow (ZMod p) (GaloisField p q) x).symm

theorem mem_normOneUnits_iff_normN [Fact p.Prime] (hq : q ≠ 0) (u : (GaloisField p q)ˣ) :
    u ∈ normOneUnits p q ↔ normN p q (u : GaloisField p q) = 1 := by
  constructor
  · intro hu
    have hbase : Algebra.norm (ZMod p) (u : GaloisField p q) = 1 := congrArg Units.val hu
    rw [normN_eq_algebraMap_norm p q hq, hbase, map_one]
  · intro hu
    ext
    apply (algebraMap (ZMod p) (GaloisField p q)).injective
    change algebraMap (ZMod p) (GaloisField p q) (Algebra.norm (ZMod p) (u : GaloisField p q)) =
      algebraMap (ZMod p) (GaloisField p q) (1 : ZMod p)
    rw [← normN_eq_algebraMap_norm p q hq, hu, map_one]

/-! ## The order of `U` -/

/-- `|U| = (p^q - 1) / (p - 1)`. The norm map `Fˣ → 𝔽_pˣ` is onto, and `U` is its kernel. -/
theorem normOneUnits_card [Fact p.Prime] (hq : q ≠ 0) :
    Nat.card (normOneUnits p q) = (p ^ q - 1) / (p - 1) := by
  classical
  let f : (GaloisField p q)ˣ →* (ZMod p)ˣ :=
    Units.map (Algebra.norm (ZMod p) (S := GaloisField p q))
  have hf_surj : Function.Surjective f :=
    FiniteField.unitsMap_norm_surjective (ZMod p) (GaloisField p q)
  have hker : normOneUnits p q = f.ker := rfl
  have hcod : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hdom : Nat.card (GaloisField p q)ˣ = p ^ q - 1 := by
    rw [Nat.card_units, GaloisField.card p q hq]
  have hindex : f.ker.index = p - 1 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf_surj, Subgroup.card_top, hcod]
  have hmul : Nat.card (normOneUnits p q) * (p - 1) = p ^ q - 1 := by
    rw [hker, ← hindex, f.ker.card_mul_index, hdom]
  exact Nat.eq_div_of_mul_eq_right (ne_of_gt (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt))
    (by simpa [mul_comm] using hmul)

/-- The two forms of condition (A) agree: `(p^q - 1) / (p - 1)` is prime to `p - 1` exactly when
`q ∤ p - 1`. This is Lemma 8 of Glauberman–Norton and Remark (I) in Appendix C of
Bender–Glauberman.

The proof: `(p^q - 1) / (p - 1) = ∑_{i<q} p^i ≡ q` modulo `p - 1`, because `p ≡ 1`. -/
theorem coprime_iff_not_dvd (hp : 2 ≤ p) (hq : q.Prime) :
    Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) ↔ ¬ q ∣ p - 1 := by
  have hsum : (p ^ q - 1) / (p - 1) = ∑ k ∈ Finset.range q, p ^ k :=
    (Nat.geomSum_eq hp q).symm
  have hp1 : (p : ZMod (p - 1)) = 1 := by
    have hcast : (p : ZMod (p - 1)) = ((p - 1) + 1 : ℕ) := by congr 1; omega
    rw [hcast, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add]
  have hsumcast : ((∑ k ∈ Finset.range q, p ^ k : ℕ) : ZMod (p - 1)) = (q : ZMod (p - 1)) := by
    push_cast
    rw [hp1]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) ↔ Nat.Coprime q (p - 1) := by
    rw [hsum, ← ZMod.isUnit_iff_coprime, ← ZMod.isUnit_iff_coprime, hsumcast]
  rw [hcop]
  exact hq.coprime_iff_not_dvd

/-- If `q > 1`, then `U` has more than one element: `|U| = 1 + p + ⋯ + p^{q-1} ≥ 1 + p`. -/
theorem normOneUnits_card_gt_one [Fact p.Prime] (hq : 1 < q) :
    1 < Nat.card (normOneUnits p q) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  rw [normOneUnits_card p q (by omega), ← Nat.geomSum_eq hp2 q]
  have hle : (∑ k ∈ Finset.range 2, p ^ k) ≤ ∑ k ∈ Finset.range q, p ^ k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hq)
      (fun _ _ _ => Nat.zero_le _)
  have htwo : 1 < (∑ k ∈ Finset.range 2, p ^ k) := by
    simp
    omega
  exact htwo.trans_le hle

/-- There is a norm-one unit other than `1`, provided `q > 1`. -/
theorem exists_normOneUnit_ne_one [Fact p.Prime] (hq : 1 < q) :
    ∃ u : normOneUnits p q, u ≠ 1 := by
  have : Nontrivial (normOneUnits p q) :=
    Finite.one_lt_card_iff_nontrivial.mp (normOneUnits_card_gt_one p q hq)
  exact exists_ne 1

/-! ## Squares in `𝔽_{3^q}` -/

variable {p q}

/-- For `p = 3`, the norm-one units are the nonzero squares. The norm
`N(x) = ∏_{i<q} x^{3^i}` is the power `x^{(3^q - 1)/2}`, so this is Euler's criterion. -/
theorem mem_normOneUnits_iff_isSquare [Fact p.Prime] (hp : p = 3) (hq : q ≠ 0)
    (u : (GaloisField p q)ˣ) :
    u ∈ normOneUnits p q ↔ IsSquare ((u : GaloisField p q)) := by
  subst hp
  let : Fintype (GaloisField 3 q) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 3 q) = 3 ^ q := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 3 q hq
  have hchar2 : ringChar (GaloisField 3 q) ≠ 2 := by
    rw [ringChar.eq (GaloisField 3 q) 3]
    norm_num
  have hnorm : normN 3 q (u : GaloisField 3 q) =
      (u : GaloisField 3 q) ^ (Fintype.card (GaloisField 3 q) / 2) := by
    rw [normN, Finset.prod_pow_eq_pow_sum, hcard]
    congr 1
    have hgeom : ∑ i ∈ Finset.range q, 3 ^ i = (3 ^ q - 1) / (3 - 1) :=
      Nat.geomSum_eq (by norm_num) q
    have hodd : 3 ^ q % 2 = 1 := Nat.odd_iff.mp (Odd.pow (by decide))
    omega
  rw [mem_normOneUnits_iff_normN 3 q hq u, hnorm,
    ← FiniteField.isSquare_iff hchar2 u.ne_zero]

/-- `|𝔽_{3^q}| ≡ 3 (mod 4)` when `q` is odd. -/
theorem card_galoisField_three_mod_four (hq0 : q ≠ 0) (hqodd : Odd q)
    [Fintype (GaloisField 3 q)] : Fintype.card (GaloisField 3 q) % 4 = 3 := by
  rw [show Fintype.card (GaloisField 3 q) = 3 ^ q by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 3 q hq0]
  obtain ⟨k, rfl⟩ := hqodd
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

/-- `-1` is not a square in `𝔽_{3^q}` when `q` is odd, because `3^q ≡ 3 (mod 4)`. -/
theorem not_isSquare_neg_one_galois [Fact p.Prime] (hp : p = 3) (hq0 : q ≠ 0) (hqodd : Odd q) :
    ¬IsSquare (-1 : GaloisField p q) := by
  subst hp
  let : Fintype (GaloisField 3 q) := Fintype.ofFinite _
  have hchar2 : ringChar (GaloisField 3 q) ≠ 2 := by
    rw [ringChar.eq (GaloisField 3 q) 3]
    norm_num
  exact Paley.not_isSquare_neg_one hchar2 (card_galoisField_three_mod_four hq0 hqodd)

/-- In `𝔽_{3^q}` with `q` odd, every nonzero element is a square or minus a square. -/
theorem isSquare_or_isSquare_neg_galois [Fact p.Prime] (hp : p = 3) (hq0 : q ≠ 0)
    (hqodd : Odd q) {a : GaloisField p q} (ha : a ≠ 0) : IsSquare a ∨ IsSquare (-a) := by
  subst hp
  let : Fintype (GaloisField 3 q) := Fintype.ofFinite _
  have hchar2 : ringChar (GaloisField 3 q) ≠ 2 := by
    rw [ringChar.eq (GaloisField 3 q) 3]
    norm_num
  exact Paley.isSquare_or_isSquare_neg hchar2 (card_galoisField_three_mod_four hq0 hqodd) ha

/-- When `-1` is a non-square, `a` and `-a` are never both squares. -/
theorem not_isSquare_of_isSquare_neg {F : Type*} [Field F]
    (hneg1 : ¬IsSquare (-1 : F)) {a : F} (ha : a ≠ 0) (h : IsSquare (-a)) :
    ¬IsSquare a := by
  intro hsq
  refine hneg1 ?_
  rw [show (-1 : F) = -a * a⁻¹ by field_simp]
  exact h.mul hsq.inv

end PeterfalviProblem
