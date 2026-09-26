/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import PeterfalviProblem.Algebra.InverseClosedSubgroup
import PeterfalviProblem.Proof.FieldLayers

/-!
# The fixed-point principle

Let `data` be a witness with `p = 3` and `q` odd, and let `e` be an odd exponent with
`g w = wᵉ g` on `σ(U)` and `z^{e³} = z` on `𝔽_{3^q}` (`exists_odd_cube_exponent`).

The set of `s ∈ 𝔽_{3^q}` such that `a(t)` commutes with `b(s tᵉ)` for every `t` is an additive
subgroup (`commSubgroup`). It is closed under `s ↦ (sᵉ)⁻¹`: conjugate the commutation by `g²`,
and use `d(u) = a(-uᵉ) · b(-u^{e²})` together with the fact that the layer `a` is abelian.
Applying this three times gives closure under `s ↦ s⁻¹`.

An additive subgroup of `𝔽_{3^q}` that is closed under inversion is everything, or its nonzero
elements satisfy `s⁴ = 1` (`InverseClosed.pow_four_eq_one_or_forall_mem`). In both cases a
nonzero element forces `1 ∈ commSubgroup`. At `t = 1` this says that `x = a(1)` commutes with
`g⁻¹ x g = b(1)`, which contradicts `not_commute_conj`.

## Main results

* `commSubgroup`: the additive subgroup described above.
* `inv_mem_commSubgroup`: `commSubgroup` is closed under inversion.
* `false_of_mem_commSubgroup_ne_zero`: a nonzero element of `commSubgroup` gives a contradiction.
-/

namespace PeterfalviProblem

section FixedPoint

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

/-- Conjugation preserves commutation. -/
private theorem commute_conj {H : Type*} [Group H] {a b : H} (h : Commute a b) (c : H) :
    Commute (c⁻¹ * a * c) (c⁻¹ * b * c) := by
  have e1 : (c⁻¹ * a * c) * (c⁻¹ * b * c) = c⁻¹ * (a * b) * c := by group
  have e2 : (c⁻¹ * b * c) * (c⁻¹ * a * c) = c⁻¹ * (b * a) * c := by group
  unfold Commute SemiconjBy
  rw [e1, e2, h.eq]

/-- Conjugation by `g²` sends the layer `a` to the layer `d`. -/
theorem conj_layerFieldHom_zero (data : Witness p q G)
    (t : Multiplicative (GaloisField p q)) :
    (conjGen data ^ 2)⁻¹ * layerFieldHom data 0 t * conjGen data ^ 2
      = layerFieldHom data 2 t := by
  simp only [layerFieldHom_apply, pow_zero, inv_one, one_mul, mul_one]

/-- Conjugation by `g²` sends the layer `b` to the layer `a`, because `g³ = 1`. -/
theorem conj_layerFieldHom_one (data : Witness p q G) (hp : p = 3)
    (t : Multiplicative (GaloisField p q)) :
    (conjGen data ^ 2)⁻¹ * layerFieldHom data 1 t * conjGen data ^ 2
      = layerFieldHom data 0 t := by
  have h3 := conjGen_pow_three data hp
  simp only [layerFieldHom_apply, pow_zero, inv_one, one_mul, mul_one, pow_one]
  calc (conjGen data ^ 2)⁻¹ * ((conjGen data)⁻¹ * fieldHom data t * conjGen data)
        * conjGen data ^ 2
      = (conjGen data ^ 3)⁻¹ * fieldHom data t * conjGen data ^ 3 := by group
    _ = fieldHom data t := by rw [h3, inv_one, one_mul, mul_one]

/-- The additive subgroup of the `s ∈ 𝔽_{p^q}` such that `a(t)` commutes with `b(s tᵉ)` for
every `t`. -/
def commSubgroup (data : Witness p q G) (e : ℕ) : AddSubgroup (GaloisField p q) where
  carrier := {s | ∀ t : GaloisField p q,
    Commute (layerFieldHom data 0 (Multiplicative.ofAdd t))
      (layerFieldHom data 1 (Multiplicative.ofAdd (s * t ^ e)))}
  zero_mem' := by
    intro t
    simp only [zero_mul, ofAdd_zero, map_one]
    exact Commute.one_right _
  add_mem' := by
    intro s s' hs hs' t
    have hsplit : (s + s') * t ^ e = s * t ^ e + s' * t ^ e := by ring
    rw [hsplit, ofAdd_add, map_mul]
    exact (hs t).mul_right (hs' t)
  neg_mem' := by
    intro s hs t
    have hneg : -s * t ^ e = -(s * t ^ e) := by ring
    rw [hneg, ofAdd_neg, map_inv]
    exact (hs t).inv_right

/-- Conjugation by `g²` sends the layer `a` to `d` and the layer `b` to `a`. So for
`s ∈ commSubgroup`, `d(t)` commutes with `a(s tᵉ)` for every `t`. -/
theorem commute_two_zero_of_mem (data : Witness p q G) (hp : p = 3) {e : ℕ}
    {s : GaloisField p q} (hs : s ∈ commSubgroup data e) (t : GaloisField p q) :
    Commute (layerFieldHom data 2 (Multiplicative.ofAdd t))
      (layerFieldHom data 0 (Multiplicative.ofAdd (s * t ^ e))) := by
  have hmap := commute_conj (hs t) (conjGen data ^ 2)
  rwa [conj_layerFieldHom_zero data, conj_layerFieldHom_one data hp] at hmap

/-- Cancellation for commutation: if `x * y` and `x` both commute with `z`, so does `y`. -/
private theorem commute_of_mul_left {H : Type*} [Group H] {x y z : H} (hxy : Commute (x * y) z)
    (hx : Commute x z) : Commute y z := by
  have h := hx.inv_left.mul_left hxy
  rwa [inv_mul_cancel_left] at h

/-- The layer `a` is abelian: it is the image of an abelian group. -/
private theorem commute_zero_zero (data : Witness p q G)
    (x y : Multiplicative (GaloisField p q)) :
    Commute (layerFieldHom data 0 x) (layerFieldHom data 0 y) :=
  (Commute.all x y).map _

/-- For `s ∈ commSubgroup` and norm-one `u`, `a(s uᵉ)` commutes with `b(u^{e²})`. Apply
`commute_two_zero_of_mem` at `u`, write `d(u) = a(-uᵉ) · b(-u^{e²})`, and cancel the factor
`a(-uᵉ)`, which commutes with `a(s uᵉ)`. -/
theorem commute_inv_pow_of_normOne (data : Witness p q G) (hp : p = 3) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {s : GaloisField p q} (hs : s ∈ commSubgroup data e) (u : normOneUnits p q) :
    Commute (layerFieldHom data 0 (Multiplicative.ofAdd (s * normOneVal u ^ e)))
      (layerFieldHom data 1 (Multiplicative.ofAdd (normOneVal u ^ (e * e)))) := by
  have h2 := commute_two_zero_of_mem data hp hs (normOneVal u)
  rw [layerFieldHom_two_eq data hp hexp u] at h2
  simp only [normOneVal_pow] at h2
  have hcancel := commute_of_mul_left h2 (commute_zero_zero data _ _).inv_left
  have hfinal : Commute (layerFieldHom data 1
      (Multiplicative.ofAdd (normOneVal u ^ (e * e))))
      (layerFieldHom data 0 (Multiplicative.ofAdd (s * normOneVal u ^ e))) := by
    simpa using hcancel.inv_left
  exact hfinal.symm

/-- Let `c ≠ 0`. If `a(c v)` commutes with `b(s (c v)ᵉ)` for every nonzero square `v`, then
`s ∈ commSubgroup`. Every nonzero `t` is `c v` or `-(c v)` for such a `v`, because `-1` is not a
square. The sign does no harm, because `e` is odd. -/
theorem mem_commSubgroup_of_square (data : Witness p q G) (hp : p = 3) (hq : q ≠ 0)
    (hqodd : Odd q) {e : ℕ} (he : Odd e) {c s : GaloisField p q} (hc0 : c ≠ 0)
    (hkey : ∀ v : GaloisField p q, IsSquare v → v ≠ 0 →
      Commute (layerFieldHom data 0 (Multiplicative.ofAdd (c * v)))
        (layerFieldHom data 1 (Multiplicative.ofAdd (s * (c * v) ^ e)))) :
    s ∈ commSubgroup data e := by
  classical
  subst hp
  let : Fintype (GaloisField 3 q) := Fintype.ofFinite _
  have : CharP (GaloisField 3 q) 3 := by
    rw [← Algebra.charP_iff (ZMod 3) (GaloisField 3 q) 3]
    exact ZMod.charP 3
  have hcard : Fintype.card (GaloisField 3 q) = 3 ^ q := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 3 q hq
  have hchar2 : ringChar (GaloisField 3 q) ≠ 2 := by
    rw [ringChar.eq (GaloisField 3 q) 3]
    norm_num
  have h4 : Fintype.card (GaloisField 3 q) % 4 = 3 := by
    rw [hcard]
    have hq2 : q % 2 = 1 := Nat.odd_iff.mp hqodd
    have hk : q = 2 * (q / 2) + 1 := by omega
    rw [hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have he0 : e ≠ 0 := by
    have := Nat.odd_iff.mp he
    omega
  intro t
  rcases eq_or_ne t 0 with rfl | ht0
  · simp [zero_pow he0]
  have hz0 : t * c⁻¹ ≠ 0 := mul_ne_zero ht0 (inv_ne_zero hc0)
  rcases Paley.isSquare_or_isSquare_neg hchar2 h4 hz0 with hsq | hnsq
  · have hv : c * (t * c⁻¹) = t := by
      rw [mul_comm t, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    have hcm := hkey (t * c⁻¹) hsq hz0
    rwa [hv] at hcm
  · have hv : c * -(t * c⁻¹) = -t := by
      rw [mul_neg, mul_comm t, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    have hcm := hkey (-(t * c⁻¹)) hnsq (neg_ne_zero.mpr hz0)
    rw [hv] at hcm
    have hb : s * (-t) ^ e = -(s * t ^ e) := by
      rw [he.neg_pow]
      ring
    rw [hb, ofAdd_neg, map_inv, ofAdd_neg, map_inv] at hcm
    simpa using hcm.inv_inv

/-- `commSubgroup` is closed under `s ↦ (sᵉ)⁻¹` on nonzero elements. Combine
`commute_inv_pow_of_normOne` with `mem_commSubgroup_of_square`. -/
theorem mem_commSubgroup_inv_pow (data : Witness p q G) (hp : p = 3) (hq : q ≠ 0)
    (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {s : GaloisField p q} (hs : s ∈ commSubgroup data e) (hs0 : s ≠ 0) :
    (s ^ e)⁻¹ ∈ commSubgroup data e := by
  refine mem_commSubgroup_of_square data hp hq hqodd he hs0 ?_
  intro v hvsq hv0
  subst hp
  obtain ⟨u0, hu0⟩ : ∃ u0 : normOneUnits 3 q, normOneVal u0 = v :=
    ⟨⟨Units.mk0 v hv0, (mem_normOneUnits_iff_isSquare rfl hq _).mpr (by simpa using hvsq)⟩, rfl⟩
  have hcube : normOneVal u0 ^ (e * e * e) = normOneVal u0 := by
    have hu := normOneUnits_pow_cube data rfl hexp u0
    calc normOneVal u0 ^ (e * e * e) = normOneVal (u0 ^ (e * e * e)) := by rw [normOneVal_pow]
      _ = normOneVal u0 := by rw [hu]
  have hue : normOneVal (u0 ^ (e * e)) ^ e = v := by
    rw [normOneVal_pow, ← pow_mul, hcube, hu0]
  have hue2 : normOneVal (u0 ^ (e * e)) ^ (e * e) = v ^ e := by
    have hexp4 : e * e * (e * e) = e * e * e * e := by ring
    rw [normOneVal_pow, ← pow_mul, hexp4, pow_mul, hcube, hu0]
  have hres := commute_inv_pow_of_normOne data rfl hexp hs (u0 ^ (e * e))
  rw [hue, hue2] at hres
  have harg : (s ^ e)⁻¹ * (s * v) ^ e = v ^ e := by
    rw [mul_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hs0), one_mul]
  rw [harg]
  exact hres

/-- `commSubgroup` is closed under inversion. Applying `s ↦ (sᵉ)⁻¹` three times gives
`s ↦ (s^{e³})⁻¹ = s⁻¹`. -/
theorem inv_mem_commSubgroup (data : Witness p q G) (hp : p = 3) (hq : q ≠ 0)
    (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {s : GaloisField p q} (hs : s ∈ commSubgroup data e) : s⁻¹ ∈ commSubgroup data e := by
  rcases eq_or_ne s 0 with rfl | hs0
  · simp
  have h1 := mem_commSubgroup_inv_pow data hp hq hqodd he hexp hs hs0
  have h1ne : (s ^ e)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hs0)
  have h2 := mem_commSubgroup_inv_pow data hp hq hqodd he hexp h1 h1ne
  have hx2 : (((s ^ e)⁻¹) ^ e)⁻¹ = s ^ (e * e) := by
    rw [inv_pow, inv_inv, ← pow_mul]
  rw [hx2] at h2
  have h2ne : s ^ (e * e) ≠ 0 := pow_ne_zero _ hs0
  have h3 := mem_commSubgroup_inv_pow data hp hq hqodd he hexp h2 h2ne
  have hx3 : ((s ^ (e * e)) ^ e)⁻¹ = s⁻¹ := by
    rw [← pow_mul, hcube]
  rwa [hx3] at h3

/-- **The fixed-point principle.** A nonzero element of `commSubgroup` gives a contradiction.

By `InverseClosed.pow_four_eq_one_or_forall_mem`, either `commSubgroup` is everything, or
`s⁴ = 1`. In the second case `s = ±1`, because `-1` is not a square. In both cases
`1 ∈ commSubgroup`. At `t = 1` this says that `x = a(1)` commutes with `g⁻¹ x g = b(1)`, which
contradicts `not_commute_conj`. -/
theorem false_of_mem_commSubgroup_ne_zero (data : Witness p q G) (hp : p = 3)
    (hqprime : q.Prime) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {s : GaloisField p q} (hs : s ∈ commSubgroup data e) (hs0 : s ≠ 0) : False := by
  classical
  have hq0 : q ≠ 0 := hqprime.ne_zero
  subst hp
  let : Fintype (GaloisField 3 q) := Fintype.ofFinite _
  have : CharP (GaloisField 3 q) 3 := by
    rw [← Algebra.charP_iff (ZMod 3) (GaloisField 3 q) 3]
    exact ZMod.charP 3
  have hcard : Fintype.card (GaloisField 3 q) = 3 ^ q := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 3 q hq0
  have hchar2 : ringChar (GaloisField 3 q) ≠ 2 := by
    rw [ringChar.eq (GaloisField 3 q) 3]
    norm_num
  have h4card : Fintype.card (GaloisField 3 q) % 4 = 3 := by
    rw [hcard]
    have hq2 : q % 2 = 1 := Nat.odd_iff.mp hqodd
    have hk : q = 2 * (q / 2) + 1 := by omega
    rw [hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hinvW : ∀ w ∈ commSubgroup data e, w⁻¹ ∈ commSubgroup data e := fun w hw =>
    inv_mem_commSubgroup data rfl hq0 hqodd he hcube hexp hw
  -- reduce both branches of the dichotomy to `1 ∈ commSubgroup`
  have hone : (1 : GaloisField 3 q) ∈ commSubgroup data e := by
    rcases InverseClosed.pow_four_eq_one_or_forall_mem (commSubgroup data e) hinvW rfl hqprime
        hcard hs hs0 with hfour | hall
    · have hnegsq : ¬ IsSquare (-1 : GaloisField 3 q) := Paley.not_isSquare_neg_one hchar2 h4card
      have hsq : s ^ 2 = 1 := by
        have hfac : (s ^ 2 - 1) * (s ^ 2 + 1) = 0 := by linear_combination hfour
        rcases mul_eq_zero.mp hfac with h | h
        · linear_combination h
        · exact absurd ⟨s, by linear_combination -h⟩ hnegsq
      have hfac : (s - 1) * (s + 1) = 0 := by linear_combination hsq
      rcases mul_eq_zero.mp hfac with h | h
      · have hs1 : s = 1 := by linear_combination h
        rwa [hs1] at hs
      · have hs1 : s = -1 := by linear_combination h
        have hneg := (commSubgroup data e).neg_mem hs
        rwa [hs1, neg_neg] at hneg
    · exact hall 1
  -- at `t = 1`, `1 ∈ commSubgroup` says that `x` commutes with `g⁻¹ x g`
  have hcomm := hone 1
  rw [one_pow, mul_one] at hcomm
  refine not_commute_conj data rfl ?_
  have ha1 : layerFieldHom data 0 (Multiplicative.ofAdd (1 : GaloisField 3 q)) = data.s := by
    simp only [layerFieldHom_apply, pow_zero, inv_one, one_mul, mul_one]
    rfl
  have hb1 : layerFieldHom data 1 (Multiplicative.ofAdd (1 : GaloisField 3 q))
      = (MulAut.conj data.y data.s)⁻¹ * data.s * MulAut.conj data.y data.s := by
    simp only [layerFieldHom_apply, pow_one, conjGen_def]
    rfl
  rwa [ha1, hb1] at hcomm

end FixedPoint

end PeterfalviProblem
