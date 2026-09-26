/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

/-!
# Identities in groups

This file proves some identities that hold in every group. The proof of the main theorem applies
them to a witness of hypothesis (B).

## Main results

* `pow_three_mul_eq_pow_three_of_commute`: if `x³ = 1` and `c` commutes with `x⁻¹ c x`, then
  `(x c x)³ = (x c)³`.
* `inv_mul_pow_three_eq_one_of_commute_conj`: if `g³ = (g x)³ = 1` and `x` commutes with
  `g⁻¹ x g`, then `(x⁻¹ g)³ = 1`.
* `cross_commute_of_three_relations`: the relations `a₂ a₁ a₀ = 1`, `b₂ b₁ b₀ = 1` and
  `(a₂ b₂)(a₁ b₁)(a₀ b₀) = 1`, together with `a₁ b₁ = b₁ a₁` and `a₀ b₀ = b₀ a₀`, give
  `a₁ b₀ = b₀ a₁`.
* `commute_conj_of_le_closure_twisted`: a family of such relations on an abelian subgroup `P`
  forces an element `t` to commute with every element of `g⁻¹ P g`.
-/

namespace PeterfalviProblem

variable {G : Type*} [Group G]

section LemmaA

variable {x c g : G}

/-- `x³ = 1`, unfolded. -/
private theorem mul_mul_eq_one_of_pow_three (hx : x ^ 3 = 1) : x * (x * x) = 1 := by
  rw [pow_succ, pow_succ, pow_one] at hx
  rwa [← mul_assoc]

/-- With `x³ = 1` the inverse of `x` is `x * x`. -/
private theorem inv_eq_mul_self (hx : x ^ 3 = 1) : x⁻¹ = x * x :=
  inv_eq_of_mul_eq_one_left (by
    have h := mul_mul_eq_one_of_pow_three hx
    rwa [mul_assoc])

/-- Cancelling a block `x * x * x` anywhere inside a right-associated product. -/
private theorem cancel_three (hx : x ^ 3 = 1) (r : G) : x * (x * (x * r)) = r := by
  have h : x * x * x = 1 := by
    have h := mul_mul_eq_one_of_pow_three hx
    rwa [← mul_assoc] at h
  rw [← mul_assoc, ← mul_assoc, h, one_mul]

/-- Expansion of `(x · c)³` into the three `x`-conjugates of `c`, valid whenever `x³ = 1`:

`(x c)³ = c^{x²} · (c^x · c)`.

Equivalently `(x c)³ = 1` says that the "norm" of `c` along `⟨x⟩` is trivial. -/
theorem pow_three_eq_conj_mul (hx : x ^ 3 = 1) (c : G) :
    (x * c) ^ 3 = x⁻¹ * (x⁻¹ * c * x) * x * ((x⁻¹ * c * x) * c) := by
  have hxi : x⁻¹ = x * x := inv_eq_mul_self hx
  have hcan : ∀ r : G, x * (x * (x * r)) = r := cancel_three hx
  simp only [hxi, pow_succ, pow_zero, one_mul, mul_assoc, hcan]

/-- **Lemma A′.**  Let `x` have order dividing three and let `c` commute with its conjugate
`x⁻¹cx`.  Then

`(x * c * x)³ = (x * c)³`.

Indeed both sides equal `c^{x²} · c^x · c` up to the order of the last two factors:
`(x * c)³ = c^{x²} c^{x} c` and `(x * c * x)³ = c^{x²} c c^{x}`.

This is the first step of the partial resolution of BG Appendix C, Problem 1: for a witness of
hypothesis (B) one takes `c = ⁅x, y⁆`, which lies in the abelian subgroup `Q`, so the commutation
hypothesis is free and the conclusion says `(g * x)³ = g³` for `g = x * c`. -/
theorem pow_three_mul_eq_pow_three_of_commute (hx : x ^ 3 = 1)
    (h : Commute c (x⁻¹ * c * x)) : (x * c * x) ^ 3 = (x * c) ^ 3 := by
  have hxi : x⁻¹ = x * x := inv_eq_mul_self hx
  have hcan : ∀ r : G, x * (x * (x * r)) = r := cancel_three hx
  have e₂ : (x * c * x) ^ 3 = x⁻¹ * (x⁻¹ * c * x) * x * (c * (x⁻¹ * c * x)) := by
    simp only [hxi, pow_succ, pow_zero, one_mul, mul_assoc, hcan]
  rw [pow_three_eq_conj_mul hx c, e₂, h.eq]

/-- The shape used downstream.  If `g = x * c` has order dividing three — automatic when `g` is a
conjugate of the order-three element `x` — and `c` commutes with `x⁻¹cx`, then the product
`g * x` also has order dividing three. -/
theorem pow_three_mul_pow_three_eq_one (hx : x ^ 3 = 1) (h : Commute c (x⁻¹ * c * x))
    (hg : (x * c) ^ 3 = 1) : (x * c * x) ^ 3 = 1 := by
  rw [pow_three_mul_eq_pow_three_of_commute hx h, hg]

/-- **The last mile of Theorem 1.**  Let `x` and `g` have order dividing three, let `g · x` also
have order dividing three, and suppose `x` commutes with its `g`-conjugate.  Then

`(x⁻¹ g)³ = 1`.

Since `x⁻¹g = ⁅x, y⁆` lies in the `3′`-group `Q` for a witness of hypothesis (B), this forces
`x⁻¹g = 1`, i.e. `g = x` — and `⟨g⟩` normalizes `σ(U)` whereas `⟨x⟩` does not.  That is the final
contradiction of Theorem 1.

The computation: `(g x)³ = 1` says `x^{g²} · x^g · x = 1`, so also `x · x^{g²} · x^g = 1` after a
cyclic shift; commuting the last two factors (the hypothesis, conjugated by `g`) gives
`x · x^g · x^{g²} = 1`, which is exactly `(g x⁻¹)³ = 1`, and `x⁻¹g` is conjugate to `g x⁻¹`. -/
theorem inv_mul_pow_three_eq_one_of_commute_conj (hg : g ^ 3 = 1) (hgx : (g * x) ^ 3 = 1)
    (hcomm : x * (g⁻¹ * x * g) = (g⁻¹ * x * g) * x) : (x⁻¹ * g) ^ 3 = 1 := by
  -- `x^{g²} · (x^g · x) = 1`.
  have h1 : g⁻¹ * (g⁻¹ * x * g) * g * ((g⁻¹ * x * g) * x) = 1 := by
    rw [← pow_three_eq_conj_mul hg x]; exact hgx
  -- Cyclic shift: `x · x^{g²} · x^g = 1`.
  have h2 : x * (g⁻¹ * (g⁻¹ * x * g) * g) * (g⁻¹ * x * g) = 1 := by
    have := h1
    rw [mul_assoc] at this
    have hx1 : g⁻¹ * (g⁻¹ * x * g) * g * (g⁻¹ * x * g) = x⁻¹ := by
      rw [← mul_one (g⁻¹ * (g⁻¹ * x * g) * g * (g⁻¹ * x * g)), ← mul_inv_cancel x,
        ← mul_assoc, ← mul_assoc, ← mul_assoc]
      simp only [← mul_assoc] at this ⊢
      rw [this, one_mul]
    calc x * (g⁻¹ * (g⁻¹ * x * g) * g) * (g⁻¹ * x * g)
        = x * (g⁻¹ * (g⁻¹ * x * g) * g * (g⁻¹ * x * g)) := by rw [mul_assoc]
      _ = x * x⁻¹ := by rw [hx1]
      _ = 1 := mul_inv_cancel x
  -- The `g`-conjugate of the commutation hypothesis swaps the last two factors.
  have hcomm' : (g⁻¹ * x * g) * (g⁻¹ * (g⁻¹ * x * g) * g) =
      (g⁻¹ * (g⁻¹ * x * g) * g) * (g⁻¹ * x * g) := by
    have := congrArg (fun z => g⁻¹ * z * g) hcomm
    simpa [mul_assoc] using this
  have h3 : x * (g⁻¹ * x * g) * (g⁻¹ * (g⁻¹ * x * g) * g) = 1 := by
    rw [mul_assoc, hcomm', ← mul_assoc]; exact h2
  -- Read this as `(g x⁻¹)³ = 1`, then conjugate by `x`.
  have h4 : (g * x⁻¹) ^ 3 = 1 := by
    rw [pow_three_eq_conj_mul hg x⁻¹]
    have hid : g⁻¹ * (g⁻¹ * x⁻¹ * g) * g * ((g⁻¹ * x⁻¹ * g) * x⁻¹)
        = (x * (g⁻¹ * x * g) * (g⁻¹ * (g⁻¹ * x * g) * g))⁻¹ := by group
    rw [hid, h3, inv_one]
  calc (x⁻¹ * g) ^ 3 = x⁻¹ * (g * x⁻¹) ^ 3 * x := by
        simp only [pow_succ, pow_zero, one_mul]; group
    _ = 1 := by rw [h4]; group

end LemmaA

section LemmaC

variable {a₀ a₁ a₂ b₀ b₁ b₂ : G}

/-- **Lemma C** (the cancellation behind the partial resolution of BG Appendix C, Problem 1).

Suppose three "layered" relations hold,

* `a₂ * a₁ * a₀ = 1`,
* `b₂ * b₁ * b₀ = 1`,
* `(a₂ * b₂) * (a₁ * b₁) * (a₀ * b₀) = 1`,

and that same-layer elements commute, `a₁ * b₁ = b₁ * a₁` and `a₀ * b₀ = b₀ * a₀`.  Then the
*cross-layer* pair commutes as well: `a₁ * b₀ = b₀ * a₁`.

Solving the first two relations for the top layer turns the third into
`(a₁b₁)(a₀b₀) = (b₁b₀)(a₁a₀)`; cancelling `b₁` on the left and `a₀` on the right — each licensed
by one of the same-layer commutations — leaves exactly `a₁b₀ = b₀a₁`.

In the application the three layers are `P`, `P^g` and `P^{g²}` for an element `g` of order three,
and the three relations are the `σ(U)`-conjugates of `(g * x)³ = 1` evaluated at `s`, `t` and
`s + t` in the set of squares of `𝔽_{3^q}`; the hypotheses hold because each layer is abelian and
because conjugation is additive on `P`. -/
theorem cross_commute_of_three_relations (ha : a₂ * a₁ * a₀ = 1) (hb : b₂ * b₁ * b₀ = 1)
    (hab : a₂ * b₂ * (a₁ * b₁) * (a₀ * b₀) = 1) (h₁ : a₁ * b₁ = b₁ * a₁)
    (h₀ : a₀ * b₀ = b₀ * a₀) : a₁ * b₀ = b₀ * a₁ := by
  -- Solve the first two relations for the top layer.
  have ha₂ : a₂ = (a₁ * a₀)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← mul_assoc]; exact ha
  have hb₂ : b₂ = (b₁ * b₀)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← mul_assoc]; exact hb
  -- Substituting them turns the third relation into `(a₁b₁)(a₀b₀) = (b₁b₀)(a₁a₀)`.
  have key : a₁ * b₁ * (a₀ * b₀) = b₁ * b₀ * (a₁ * a₀) := by
    rw [ha₂, hb₂] at hab
    have h : (a₁ * a₀)⁻¹ * ((b₁ * b₀)⁻¹ * (a₁ * b₁ * (a₀ * b₀))) = 1 := by
      simpa [mul_assoc] using hab
    exact inv_mul_eq_iff_eq_mul.mp (inv_mul_eq_one.mp h).symm
  -- Cancel `b₁` on the left, using `a₁b₁ = b₁a₁`.
  have step : a₁ * (a₀ * b₀) = b₀ * (a₁ * a₀) := by
    have hL : a₁ * b₁ * (a₀ * b₀) = b₁ * (a₁ * (a₀ * b₀)) := by
      rw [h₁, mul_assoc]
    have hR : b₁ * b₀ * (a₁ * a₀) = b₁ * (b₀ * (a₁ * a₀)) := mul_assoc _ _ _
    rw [hL, hR] at key
    exact mul_left_cancel key
  -- Cancel `a₀` on the right, using `a₀b₀ = b₀a₀`.
  have step₂ : a₁ * b₀ * a₀ = b₀ * a₁ * a₀ := by
    rw [mul_assoc, mul_assoc, ← h₀]
    exact step
  exact mul_right_cancel step₂

section Semilinear

/-- **Semilinearity of the layer map.**  Suppose `g` normalizes a subgroup with exponent `e`, in
the sense `g · v = vᵉ · g`.  Then conjugating the `g`-layer by `v` shifts the base point by `vᵉ`:

`(z^g)^v = (z^{vᵉ})^g`.

This is the rule that produces the relation family for a *non-centralising* action: conjugating
`x^{g²} · x^g · x = 1` by `v ∈ σ(U)` gives

`(x^{v^{e²}})^{g²} · (x^{v^e})^g · x^v = 1`,

the twisted relation `R(s)` of the partial resolution.  For `e = 1` it degenerates to the plain
statement that conjugation by `v` commutes with the layer map, which is what
`pow_three_mul_conj_eq_one` uses. -/
theorem conj_layer_of_exp {g v : G} {e : ℕ} (hexp : g * v = v ^ e * g) (z : G) :
    v⁻¹ * (g⁻¹ * z * g) * v = g⁻¹ * ((v ^ e)⁻¹ * z * v ^ e) * g := by
  calc v⁻¹ * (g⁻¹ * z * g) * v = (g * v)⁻¹ * z * (g * v) := by group
    _ = (v ^ e * g)⁻¹ * z * (v ^ e * g) := by rw [hexp]
    _ = g⁻¹ * ((v ^ e)⁻¹ * z * v ^ e) * g := by group

/-- Iterating `conj_layer_of_exp`: the second layer moves by `v^{e²}`. -/
theorem conj_layer_two_of_exp {g v : G} {e : ℕ} (h₁ : g * v = v ^ e * g)
    (h₂ : g * v ^ e = (v ^ e) ^ e * g) (z : G) :
    v⁻¹ * (g⁻¹ * (g⁻¹ * z * g) * g) * v
      = g⁻¹ * (g⁻¹ * ((v ^ (e * e))⁻¹ * z * v ^ (e * e)) * g) * g := by
  rw [conj_layer_of_exp h₁ (g⁻¹ * z * g), conj_layer_of_exp h₂ z, ← pow_mul]

end Semilinear

end LemmaC

/-- **Theorem 1's engine** (twisted form).  Let `P` be an abelian subgroup, `g` an element with
`σ` an endomorphism preserving `P`, and `S ⊆ P` a set of elements satisfying the *layered*
relation

`(σ²s)^{g²} · (σs)^g · s = 1`.

Fix `t ∈ S`.  If `σ` maps the elements `s ∈ S` with `s · t ∈ S` onto a generating set of `P`, then

`t · v^g = v^g · t` for every `v ∈ P`.

For each admissible `s` the three relations at `s`, `t` and `s · t` feed
`cross_commute_of_three_relations` — the middle layers multiply correctly because `σ` is a
homomorphism — and the elements commuting with `t` after conjugation form a subgroup, so a
generating set suffices.

In the application `P` is the additive group of `𝔽_{3^q}`, `S` the set of squares, `t = 1`, and
`σ` a power of the Frobenius: that is exactly the case `e ∈ ⟨3⟩` of the partial resolution, where
`s ↦ s^e` is additive.  `commute_conj_of_le_closure` is the untwisted specialisation `σ = id`
(the centralising case `e = 1`, available for every `q`). -/
theorem commute_conj_of_le_closure_twisted {P : Subgroup G}
    (hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) {g : G} (σ : G → G)
    (hσmul : ∀ a ∈ P, ∀ b ∈ P, σ (a * b) = σ a * σ b)
    (hσP : ∀ v ∈ P, σ v ∈ P) {S : Set G} (hSP : S ⊆ (P : Set G))
    (hrel : ∀ s ∈ S,
      (g⁻¹ * (g⁻¹ * σ (σ s) * g) * g) * (g⁻¹ * σ s * g) * s = 1)
    {t : G} (ht : t ∈ S)
    (hspan : P ≤ Subgroup.closure (σ '' {s | s ∈ S ∧ s * t ∈ S})) :
    ∀ v ∈ P, t * (g⁻¹ * v * g) = (g⁻¹ * v * g) * t := by
  -- The elements commuting with `t` after conjugation form a subgroup.
  set C : Subgroup G :=
    (Subgroup.centralizer ({t} : Set G)).comap (MulAut.conj g⁻¹).toMonoidHom with hC
  have hmemC : ∀ v : G, v ∈ C ↔ t * (g⁻¹ * v * g) = (g⁻¹ * v * g) * t := by
    intro v
    constructor
    · intro hv
      have := (Subgroup.mem_centralizer_iff.mp hv) t rfl
      simpa [MulAut.conj_apply, mul_assoc] using this
    · intro hv
      refine Subgroup.mem_centralizer_iff.mpr ?_
      rintro m rfl
      simpa [MulAut.conj_apply, mul_assoc] using hv
  have hgen : σ '' {s | s ∈ S ∧ s * t ∈ S} ⊆ (C : Set G) := by
    rintro _ ⟨s, ⟨hs, hst⟩, rfl⟩
    have ha := hrel s hs
    have hb := hrel t ht
    have hab := hrel (s * t) hst
    have hab' : (g⁻¹ * (g⁻¹ * σ (σ s) * g) * g) * (g⁻¹ * (g⁻¹ * σ (σ t) * g) * g) *
        ((g⁻¹ * σ s * g) * (g⁻¹ * σ t * g)) * (s * t) = 1 := by
      rw [← hab, hσmul s (hSP hs) t (hSP ht),
        hσmul (σ s) (hσP s (hSP hs)) (σ t) (hσP t (hSP ht))]
      group
    have h₁ : (g⁻¹ * σ s * g) * (g⁻¹ * σ t * g) = (g⁻¹ * σ t * g) * (g⁻¹ * σ s * g) := by
      have hcomm := hP (σ s) (hσP s (hSP hs)) (σ t) (hσP t (hSP ht))
      have hcs : g⁻¹ * σ s * g * (g⁻¹ * σ t * g) = g⁻¹ * (σ s * σ t) * g := by group
      have hct : g⁻¹ * σ t * g * (g⁻¹ * σ s * g) = g⁻¹ * (σ t * σ s) * g := by group
      rw [hcs, hct, hcomm]
    have h₀ : s * t = t * s := hP s (hSP hs) t (hSP ht)
    exact (hmemC (σ s)).mpr (cross_commute_of_three_relations ha hb hab' h₁ h₀).symm
  intro v hv
  exact (hmemC v).mp ((Subgroup.closure_le C).mpr hgen (hspan hv))

end PeterfalviProblem
