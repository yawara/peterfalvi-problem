/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Additive subgroups of a field that are closed under inversion

Let `W` be an additive subgroup of a field that is also closed under inversion. Such a `W` is very
rigid. The reason is **Hua's identity**

`x - (x⁻¹ + (y - x)⁻¹)⁻¹ = x² / y`,

which builds `x² / y` from `x` and `y` using only subtraction and inversion. So `W` is closed under
`(x, y) ↦ x² / y`. Fix a nonzero `s ∈ W`. Taking `y = s` shows that `K = {v : s v ∈ W}` is closed
under squaring. In characteristic three, `u v = u² + v² - (u + v)²`, so `K` is also closed under
multiplication. In fact `K` is a subfield.

In `𝔽_{3^q}` with `q` prime, the only subfields are `𝔽₃` and `𝔽_{3^q}`. So either `W` is
everything, or `s⁴ = 1` for every nonzero `s ∈ W` (`pow_four_eq_one_or_forall_mem`).

## Main results

* `hua_identity`: `x - (x⁻¹ + (y - x)⁻¹)⁻¹ = x² / y`.
* `sq_div_mem`: an inversion-closed additive subgroup is closed under `(x, y) ↦ x² / y`.
* `scaledSubfield`: in characteristic three, `{v : s v ∈ W}` is a subfield.
* `subfield_eq_bot_or_top`: a finite field of prime degree has no intermediate subfield.
* `pow_four_eq_one_or_forall_mem`: the dichotomy above.
-/

namespace PeterfalviProblem.InverseClosed

variable {F : Type*} [Field F]

/-- **Hua's identity**: `x² / y` can be built from `x` and `y` by subtraction and inversion. The
hypotheses make every inverse in the identity the inverse of a nonzero element. -/
theorem hua_identity {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    x - (x⁻¹ + (y - x)⁻¹)⁻¹ = x ^ 2 / y := by
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hval : x⁻¹ + (y - x)⁻¹ = y / (x * (y - x)) := by
    field_simp
    ring
  rw [hval, inv_div]
  field_simp
  ring

variable (W : AddSubgroup F)

/-- An inversion-closed additive subgroup is closed under `(x, y) ↦ x² / y`, by Hua's
identity. -/
theorem sq_div_mem (hinv : ∀ w ∈ W, w⁻¹ ∈ W) {x y : F} (hx : x ∈ W) (hy : y ∈ W) (hy0 : y ≠ 0) :
    x ^ 2 / y ∈ W := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  rcases eq_or_ne x y with rfl | hxy
  · rw [sq, mul_div_assoc, div_self hx0, mul_one]
    exact hx
  rw [← hua_identity hx0 hy0 hxy]
  exact W.sub_mem hx (hinv _ (W.add_mem (hinv _ hx) (hinv _ (W.sub_mem hy hx))))

/-- If `s ∈ W` is nonzero and `s v ∈ W`, then `s v² ∈ W`. -/
theorem mul_sq_mem (hinv : ∀ w ∈ W, w⁻¹ ∈ W) {s v : F} (hs : s ∈ W) (hs0 : s ≠ 0)
    (hv : s * v ∈ W) : s * v ^ 2 ∈ W := by
  have key : (s * v) ^ 2 / s = s * v ^ 2 := by
    field_simp
  rw [← key]
  exact sq_div_mem W hinv hv hs hs0

/-- In characteristic three, `u v = u² + v² - (u + v)²`. So if `s u` and `s v` lie in `W`, then
so does `s u v`. -/
theorem mul_mul_mem (hinv : ∀ w ∈ W, w⁻¹ ∈ W) (h3 : (3 : F) = 0) {s u v : F} (hs : s ∈ W)
    (hs0 : s ≠ 0) (hu : s * u ∈ W) (hv : s * v ∈ W) : s * (u * v) ∈ W := by
  have hsum : s * (u + v) ∈ W := by
    have : s * (u + v) = s * u + s * v := by ring
    rw [this]
    exact W.add_mem hu hv
  have key : s * (u * v) = s * u ^ 2 + s * v ^ 2 - s * (u + v) ^ 2 := by
    linear_combination (s * u * v) * h3
  rw [key]
  exact W.sub_mem (W.add_mem (mul_sq_mem W hinv hs hs0 hu) (mul_sq_mem W hinv hs hs0 hv))
    (mul_sq_mem W hinv hs hs0 hsum)

/-- Let `W` be an inversion-closed additive subgroup of a field of characteristic three, and let
`s ∈ W` be nonzero. Then `{v : s v ∈ W}` is a subring. -/
def scaledSubring (hinv : ∀ w ∈ W, w⁻¹ ∈ W) (h3 : (3 : F) = 0) {s : F} (hs : s ∈ W)
    (hs0 : s ≠ 0) : Subring F where
  carrier := {v | s * v ∈ W}
  zero_mem' := by
    change s * (0 : F) ∈ W
    simp
  one_mem' := by
    change s * (1 : F) ∈ W
    simpa using hs
  add_mem' := by
    intro u v hu hv
    change s * (u + v) ∈ W
    have h : s * (u + v) = s * u + s * v := by ring
    rw [h]
    exact W.add_mem hu hv
  neg_mem' := by
    intro u hu
    change s * (-u) ∈ W
    have h : s * (-u) = -(s * u) := by ring
    rw [h]
    exact W.neg_mem hu
  mul_mem' := fun hu hv => mul_mul_mem W hinv h3 hs hs0 hu hv

/-- The subring `{v : s v ∈ W}` is a subfield, because `s v⁻¹ = s² / (s v)`. -/
def scaledSubfield (hinv : ∀ w ∈ W, w⁻¹ ∈ W) (h3 : (3 : F) = 0) {s : F}
    (hs : s ∈ W) (hs0 : s ≠ 0) : Subfield F :=
  { scaledSubring W hinv h3 hs hs0 with
    inv_mem' := by
      intro v hv
      rcases eq_or_ne v 0 with rfl | hv0
      · change s * (0 : F)⁻¹ ∈ W
        simp
      change s * v⁻¹ ∈ W
      have hsv : s * v ∈ W := hv
      have key : s ^ 2 / (s * v) = s * v⁻¹ := by
        rw [sq, mul_div_mul_left _ _ hs0, div_eq_mul_inv]
      rw [← key]
      exact sq_div_mem W hinv hs hsv (mul_ne_zero hs0 hv0) }

/-! ### Fields of prime degree

The only subfields of `𝔽_{p^q}` with `q` prime are `𝔽_p` and `𝔽_{p^q}`: a subfield has `p^d`
elements with `d ∣ q`. -/

section PrimeDegree

variable [Fintype F] {p q : ℕ} [Fact p.Prime] [CharP F p]

/-- A finite field of prime degree over its prime field has no subfield other than the prime
field and itself. -/
theorem subfield_eq_bot_or_top (hq : q.Prime) (hcard : Fintype.card F = p ^ q) (K : Subfield F) :
    K = ⊥ ∨ K = ⊤ := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have hpp : p.Prime := Fact.out
  obtain ⟨d, -, hdcard⟩ := FiniteField.card K p
  have hpow : Fintype.card F = Fintype.card K ^ Module.finrank K F := Module.card_eq_pow_finrank
  rw [hcard, hdcard, ← pow_mul] at hpow
  have hexp : q = (d : ℕ) * Module.finrank K F := Nat.pow_right_injective hpp.two_le hpow
  rcases hq.eq_one_or_self_of_dvd (d : ℕ) ⟨_, hexp⟩ with h1 | hqd
  · -- `|K| = p`, so every element of `K` satisfies `x ^ p = x`
    left
    refine le_antisymm (fun x hx => ?_) bot_le
    have hcardK : Fintype.card K = p := by rw [hdcard, h1, pow_one]
    have hfix : (⟨x, hx⟩ : K) ^ p = ⟨x, hx⟩ := by
      have := FiniteField.pow_card (⟨x, hx⟩ : K)
      rwa [hcardK] at this
    refine (Subfield.mem_bot_iff_pow_eq_self F p).mpr ?_
    exact congrArg Subtype.val hfix
  · -- `|K| = |F|`, so the inclusion is onto
    right
    refine le_antisymm le_top (fun x _ => ?_)
    have hcards : Fintype.card K = Fintype.card F := by rw [hdcard, hcard, hqd]
    have hbij : Function.Bijective ((↑) : K → F) :=
      (Fintype.bijective_iff_injective_and_card _).mpr ⟨Subtype.val_injective, hcards⟩
    obtain ⟨k, hk⟩ := hbij.2 x
    exact hk ▸ k.2

/-- Let `F` be a finite field of characteristic three whose degree over `𝔽₃` is prime. Let `W` be
an inversion-closed additive subgroup, and let `s ∈ W` be nonzero. Then `W = F` or `s⁴ = 1`. -/
theorem pow_four_eq_one_or_forall_mem (hinv : ∀ w ∈ W, w⁻¹ ∈ W) (hp : p = 3) (hq : q.Prime)
    (hcard : Fintype.card F = p ^ q) {s : F} (hs : s ∈ W) (hs0 : s ≠ 0) :
    s ^ 4 = 1 ∨ ∀ x : F, x ∈ W := by
  have h3 : (3 : F) = 0 := by
    have := CharP.cast_eq_zero F p
    rw [hp] at this
    exact_mod_cast this
  rcases subfield_eq_bot_or_top hq hcard (scaledSubfield W hinv h3 hs hs0) with hbot | htop
  · left
    have hsinv : s⁻¹ ∈ W := hinv _ hs
    have hv : s⁻¹ * s⁻¹ ∈ scaledSubfield W hinv h3 hs hs0 := by
      change s * (s⁻¹ * s⁻¹) ∈ W
      have hrw : s * (s⁻¹ * s⁻¹) = s⁻¹ := by
        field_simp
      rw [hrw]
      exact hsinv
    rw [hbot] at hv
    have hpow : (s⁻¹ * s⁻¹) ^ p = s⁻¹ * s⁻¹ := (Subfield.mem_bot_iff_pow_eq_self F p).mp hv
    rw [hp] at hpow
    have hfac : (s⁻¹) ^ 2 * ((s⁻¹) ^ 4 - 1) = 0 := by linear_combination hpow
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd h (pow_ne_zero _ (inv_ne_zero hs0))
    · have h1 : (s ^ 4)⁻¹ = 1 := by
        rw [← inv_pow]
        linear_combination h
      exact inv_eq_one.mp h1
  · right
    intro x
    have hx : x * s⁻¹ ∈ scaledSubfield W hinv h3 hs hs0 := htop ▸ Subfield.mem_top _
    have hmem : s * (x * s⁻¹) ∈ W := hx
    have hrw : s * (x * s⁻¹) = x := by
      field_simp
    rwa [hrw] at hmem

end PrimeDegree

end PeterfalviProblem.InverseClosed
