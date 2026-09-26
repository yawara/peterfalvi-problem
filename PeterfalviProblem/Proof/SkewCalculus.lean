/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import PeterfalviProblem.Proof.PairComposition

/-!
# Skew pairs

Let `data` be a witness with `p = 3` and `q ≠ 3` odd, and let `e` be an odd exponent as in
`exists_odd_cube_exponent`.

A *skew pair* `SkewPair data e A B X Y` is the relation

`a(A w) · b(X wᵉ) · a(B w)⁻¹ = b(Y wᵉ)` for every nonzero square `w`.

We call `A` and `B` the parameters and `X` and `Y` the weights. When `A = B`, a skew pair is a
conjugation pair after the substitution `v = A w` (`SkewPair.conjPair_of_self`).

A *Paley point* is a pair of norm-one units `p₀ = p₁ + 1`. For two Paley points `p` and `r`, write
`δ₀ = r₀ᵉ - p₀ᵉ`, `δ₁ = r₁ᵉ - p₁ᵉ`, `K(p) = p₁^{e²} - p₀^{e²}` and `K(r) = r₁^{e²} - r₀^{e²}`.
Comparing the factorizations of `layerFieldHom_two_factor` for `p` and `r` gives the skew pair
`(δ₀, δ₁; K(p), K(r))` with no further condition (`skewPair_edge`). We call it the *edge* from
`p` to `r`. A collision is an edge with `δ₀ = δ₁`.

Skew pairs can be reversed, composed and rescaled. A *closed loop* is a skew pair with equal
parameters. `FrobFam` says that all the Frobenius images `(A^{3ʲ}, B^{3ʲ}; X^{3ʲ}, Y^{3ʲ})` are skew
pairs. Edges have this property, and the operations keep it. A Frobenius-closed closed loop whose
weights are not both zero gives a Frobenius-closed family of conjugation pairs, and hence a
contradiction (`FrobFam.false_of_self`).

## Main results

* `skewPair_edge`: the edge between two Paley points.
* `FrobFam.false_of_self`: a Frobenius-closed closed loop has zero weights.
* `weight_sum_eq_zero_of_antipodal_edge`: an edge with `δ₁ = -δ₀` has `K(p) + K(r) = 0`.
* `weights_eq_zero_of_four_loop`: the weights of a four-leg loop vanish.
-/

namespace PeterfalviProblem

section SkewCalculus

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

/-- **A skew pair**: `a(A w) · b(X wᵉ) · a(B w)⁻¹ = b(Y wᵉ)` for every nonzero square `w`. -/
def SkewPair (data : Witness p q G) (e : ℕ) (A B X Y : GaloisField p q) : Prop :=
  ∀ w : GaloisField p q, IsSquare w → w ≠ 0 →
    layerFieldHom data 0 (Multiplicative.ofAdd (A * w)) *
        layerFieldHom data 1 (Multiplicative.ofAdd (X * w ^ e)) *
        (layerFieldHom data 0 (Multiplicative.ofAdd (B * w)))⁻¹
      = layerFieldHom data 1 (Multiplicative.ofAdd (Y * w ^ e))

/-- Each layer turns sums into products. -/
private theorem layer_split (data : Witness p q G) (i : ℕ)
    {x y z : GaloisField p q} (h : x = y + z) :
    layerFieldHom data i (Multiplicative.ofAdd x)
      = layerFieldHom data i (Multiplicative.ofAdd y) *
        layerFieldHom data i (Multiplicative.ofAdd z) := by
  subst h
  rw [ofAdd_add]
  exact map_mul _ _ _

/-- Each layer turns negation into inversion. -/
private theorem layer_neg (data : Witness p q G) (i : ℕ)
    {x y : GaloisField p q} (h : x = -y) :
    layerFieldHom data i (Multiplicative.ofAdd x)
      = (layerFieldHom data i (Multiplicative.ofAdd y))⁻¹ := by
  subst h
  rw [ofAdd_neg]
  exact map_inv _ _

namespace SkewPair

variable {data : Witness p q G} {e : ℕ}

/-- **Reversal**: `(A, B; X, Y)` gives `(B, A; -X, -Y)`. -/
theorem rev {A B X Y : GaloisField p q} (h : SkewPair data e A B X Y) :
    SkewPair data e B A (-X) (-Y) := by
  intro w hw hw0
  rw [layer_neg data 1 (show -X * w ^ e = -(X * w ^ e) by ring),
    layer_neg data 1 (show -Y * w ^ e = -(Y * w ^ e) by ring), ← h w hw hw0]
  group

/-- **Composition**: `(A, B; X₁, Y₁)` and `(B, C; X₂, Y₂)` give `(A, C; X₁ + X₂, Y₁ + Y₂)`. -/
theorem comp {A B C X₁ Y₁ X₂ Y₂ : GaloisField p q} (h₁ : SkewPair data e A B X₁ Y₁)
    (h₂ : SkewPair data e B C X₂ Y₂) : SkewPair data e A C (X₁ + X₂) (Y₁ + Y₂) := by
  intro w hw hw0
  rw [layer_split data 1 (show (X₁ + X₂) * w ^ e = X₁ * w ^ e + X₂ * w ^ e by ring),
    layer_split data 1 (show (Y₁ + Y₂) * w ^ e = Y₁ * w ^ e + Y₂ * w ^ e by ring),
    ← h₁ w hw hw0, ← h₂ w hw hw0]
  group

/-- **Rescaling** by a nonzero square `s`: `(A, B; X, Y)` gives `(A s, B s; X sᵉ, Y sᵉ)`.
Substitute `s w` for `w`. -/
theorem rescale {A B X Y : GaloisField p q} (h : SkewPair data e A B X Y)
    {s : GaloisField p q} (hs : IsSquare s) (hs0 : s ≠ 0) :
    SkewPair data e (A * s) (B * s) (X * s ^ e) (Y * s ^ e) := by
  intro w hw hw0
  have g := h (s * w) (hs.mul hw) (mul_ne_zero hs0 hw0)
  rw [show A * (s * w) = A * s * w by ring, show B * (s * w) = B * s * w by ring,
    show X * (s * w) ^ e = X * s ^ e * w ^ e by rw [mul_pow]; ring,
    show Y * (s * w) ^ e = Y * s ^ e * w ^ e by rw [mul_pow]; ring] at g
  exact g

/-- A closed loop `(A, A; X, Y)` gives `(-A, -A; Y, X)`. -/
theorem self_symm {A X Y : GaloisField p q} (h : SkewPair data e A A X Y) :
    SkewPair data e (-A) (-A) Y X := by
  intro w hw hw0
  rw [layer_neg data 0 (show -A * w = -(A * w) by ring), ← h w hw hw0]
  group

/-- A closed loop `(A, A; 0, Y)` has `Y = 0`, because the layer `b` is injective. -/
theorem self_right_eq_zero {A Y : GaloisField p q} (h : SkewPair data e A A 0 Y) : Y = 0 := by
  have h1 := h 1 ⟨1, (mul_one 1).symm⟩ one_ne_zero
  have h0 : layerFieldHom data 1 (Multiplicative.ofAdd ((0 : GaloisField p q) * 1 ^ e)) = 1 := by
    have harg : Multiplicative.ofAdd ((0 : GaloisField p q) * 1 ^ e) = 1 := by
      rw [zero_mul]
      exact ofAdd_zero
    rw [harg]
    exact map_one _
  rw [h0, mul_one, mul_inv_cancel] at h1
  have h0' : layerFieldHom data 1 (Multiplicative.ofAdd (0 : GaloisField p q)) = 1 := by
    rw [ofAdd_zero]
    exact map_one _
  have harg := layerFieldHom_injective data 1 (h0'.trans h1)
  have hval : (0 : GaloisField p q) = Y * 1 ^ e := by
    have := congrArg Multiplicative.toAdd harg
    simpa using this
  simpa using hval.symm

/-- A closed loop `(A, A; X, 0)` has `X = 0`. -/
theorem self_left_eq_zero {A X : GaloisField p q} (h : SkewPair data e A A X 0) : X = 0 :=
  self_right_eq_zero h.self_symm

/-- A closed loop `(A, A; X, Y)` with `A` a nonzero square gives the conjugation pair
`(X A^{-e}, Y A^{-e})`. Substitute `v = A w`. -/
theorem conjPair_of_self {A X Y : GaloisField p q} (h : SkewPair data e A A X Y)
    (hA : IsSquare A) (hA0 : A ≠ 0) :
    ConjPair data e (X * (A ^ e)⁻¹) (Y * (A ^ e)⁻¹) := by
  intro v hv hv0
  have g := h (A⁻¹ * v) (hA.inv.mul hv) (mul_ne_zero (inv_ne_zero hA0) hv0)
  rw [show A * (A⁻¹ * v) = v by rw [← mul_assoc, mul_inv_cancel₀ hA0, one_mul],
    show X * (A⁻¹ * v) ^ e = X * (A ^ e)⁻¹ * v ^ e by rw [mul_pow, inv_pow]; ring,
    show Y * (A⁻¹ * v) ^ e = Y * (A ^ e)⁻¹ * v ^ e by rw [mul_pow, inv_pow]; ring] at g
  exact g

/-- A closed loop `(A, A; X, Y)` with `-A` a nonzero square gives the conjugation pair
`(Y (-A)^{-e}, X (-A)^{-e})`. -/
theorem conjPair_of_self_neg {A X Y : GaloisField p q} (h : SkewPair data e A A X Y)
    (hA : IsSquare (-A)) (hA0 : A ≠ 0) :
    ConjPair data e (Y * ((-A) ^ e)⁻¹) (X * ((-A) ^ e)⁻¹) :=
  conjPair_of_self h.self_symm hA (neg_ne_zero.mpr hA0)

end SkewPair

/-- **The edge between two Paley points.** For Paley points `p` and `r`, the skew pair
`(δ₀, δ₁; K(p), K(r))` holds. Compare the two factorizations of `d(z)` given by
`layerFieldHom_two_factor`. -/
theorem skewPair_edge (data : Witness p q G) (hp : p = 3) (hq : q ≠ 0) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    (p₀ p₁ r₀ r₁ : normOneUnits p q)
    (hpp : normOneVal p₀ = normOneVal p₁ + 1) (hrr : normOneVal r₀ = normOneVal r₁ + 1) :
    SkewPair data e (normOneVal r₀ ^ e - normOneVal p₀ ^ e)
      (normOneVal r₁ ^ e - normOneVal p₁ ^ e)
      (normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e))
      (normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e)) := by
  intro w hw hw0
  obtain ⟨u, hu⟩ : ∃ u : normOneUnits p q, normOneVal u = w :=
    ⟨⟨Units.mk0 w hw0, (mem_normOneUnits_iff_isSquare hp hq _).mpr (by simpa using hw)⟩, rfl⟩
  -- the auxiliary height `z := u^{e²}` satisfies `zᵉ = u` and `z^{e²} = uᵉ`
  have hz1 : (u ^ (e * e)) ^ e = u := by
    rw [← pow_mul]
    exact normOneUnits_pow_cube data hp hexp u
  have hz2 : (u ^ (e * e)) ^ (e * e) = u ^ e := by
    rw [← pow_mul, show e * e * (e * e) = e * e * e * e by ring, pow_mul,
      normOneUnits_pow_cube data hp hexp u]
  have hP := layerFieldHom_two_factor data hp hexp p₀ p₁ (u ^ (e * e)) hpp
  have hR := layerFieldHom_two_factor data hp hexp r₀ r₁ (u ^ (e * e)) hrr
  rw [hz1, hz2] at hP hR
  simp only [normOneVal_mul, normOneVal_pow, hu] at hP hR
  have hEq := hP.symm.trans hR
  rw [layer_split data 0 (show (normOneVal r₀ ^ e - normOneVal p₀ ^ e) * w
        = normOneVal r₀ ^ e * w + -(normOneVal p₀ ^ e * w) by ring),
    layer_neg data 0 (rfl : -(normOneVal p₀ ^ e * w) = -(normOneVal p₀ ^ e * w)),
    layer_split data 0 (show (normOneVal r₁ ^ e - normOneVal p₁ ^ e) * w
        = normOneVal r₁ ^ e * w + -(normOneVal p₁ ^ e * w) by ring),
    layer_neg data 0 (rfl : -(normOneVal p₁ ^ e * w) = -(normOneVal p₁ ^ e * w))]
  calc layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal r₀ ^ e * w)) *
        (layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal p₀ ^ e * w)))⁻¹ *
        layerFieldHom data 1 (Multiplicative.ofAdd
          ((normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e)) * w ^ e)) *
        (layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal r₁ ^ e * w)) *
          (layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal p₁ ^ e * w)))⁻¹)⁻¹
      = layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal r₀ ^ e * w)) *
          ((layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal p₀ ^ e * w)))⁻¹ *
            layerFieldHom data 1 (Multiplicative.ofAdd
              ((normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e)) * w ^ e)) *
            layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal p₁ ^ e * w))) *
          (layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal r₁ ^ e * w)))⁻¹ := by
        group
    _ = layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal r₀ ^ e * w)) *
          ((layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal r₀ ^ e * w)))⁻¹ *
            layerFieldHom data 1 (Multiplicative.ofAdd
              ((normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e)) * w ^ e)) *
            layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal r₁ ^ e * w))) *
          (layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal r₁ ^ e * w)))⁻¹ := by
        rw [hEq]
    _ = layerFieldHom data 1 (Multiplicative.ofAdd
          ((normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e)) * w ^ e)) := by
        group

/-- `δ₀ = r₀ᵉ - p₀ᵉ ≠ 0` when `p₀ ≠ r₀`. -/
theorem skewPair_edge_left_ne_zero {e : ℕ}
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    {p₀ r₀ : normOneUnits p q} (hne : normOneVal p₀ ≠ normOneVal r₀) :
    normOneVal r₀ ^ e - normOneVal p₀ ^ e ≠ 0 := by
  intro h0
  exact hne (Paley.pow_injective_of_cube hcube (sub_eq_zero.mp h0)).symm

/-- `K(p) = p₁^{e²} - p₀^{e²} ≠ 0`, because `z ↦ z^{e²}` is injective and `p₀ ≠ p₁`. -/
theorem skewPair_edge_weight_ne_zero {e : ℕ}
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    {p₀ p₁ : normOneUnits p q} (hpp : normOneVal p₀ = normOneVal p₁ + 1) :
    normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e) ≠ 0 := by
  intro h0
  have hpow : (normOneVal p₁ ^ e) ^ e = (normOneVal p₀ ^ e) ^ e := by
    rw [← pow_mul, ← pow_mul]
    exact sub_eq_zero.mp h0
  have h1 : normOneVal p₁ = normOneVal p₀ :=
    Paley.pow_injective_of_cube hcube (Paley.pow_injective_of_cube hcube hpow)
  rw [h1] at hpp
  simp at hpp

/-- A Frobenius-closed family of closed loops `(A, A; X, Y)`, with `A ≠ 0` and weights not both
zero, gives a contradiction. If one weight is zero, then so is the other. Otherwise the loop is a
conjugation pair with a nonzero value: read forwards if `A` is a square, and backwards if not. The
Frobenius map does not change the square class of `A`, so the whole family is read in the same
direction, and `false_of_conjPair_frobenius_family` applies. -/
theorem false_of_skewPair_self_frobenius_family (data : Witness p q G) (hp : p = 3)
    (hqprime : q.Prime) (hq3 : q ≠ 3) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {A X Y : GaloisField p q} (hA0 : A ≠ 0) (hXY : ¬(X = 0 ∧ Y = 0))
    (hfam : ∀ j : ℕ, SkewPair data e (A ^ p ^ j) (A ^ p ^ j) (X ^ p ^ j) (Y ^ p ^ j)) :
    False := by
  subst hp
  have h00 : SkewPair data e A A X Y := by simpa using hfam 0
  -- the two weights vanish together, so both are non-zero
  have hX0 : X ≠ 0 := by
    intro h0
    exact hXY ⟨h0, SkewPair.self_right_eq_zero (by rwa [h0] at h00)⟩
  have hY0 : Y ≠ 0 := by
    intro h0
    exact hXY ⟨SkewPair.self_left_eq_zero (by rwa [h0] at h00), h0⟩
  rcases isSquare_or_isSquare_neg_galois rfl hqprime.ne_zero hqodd hA0 with hsq | hnsq
  · -- read forwards: the pairs `(X A^{-e}, Y A^{-e})`
    have hfam' : ∀ j : ℕ,
        ConjPair data e ((X * (A ^ e)⁻¹) ^ 3 ^ j) ((Y * (A ^ e)⁻¹) ^ 3 ^ j) := by
      intro j
      have h := SkewPair.conjPair_of_self (hfam j) (hsq.pow _) (pow_ne_zero _ hA0)
      rw [show (X * (A ^ e)⁻¹) ^ 3 ^ j = X ^ 3 ^ j * ((A ^ 3 ^ j) ^ e)⁻¹ by
          rw [mul_pow, inv_pow, pow_right_comm],
        show (Y * (A ^ e)⁻¹) ^ 3 ^ j = Y ^ 3 ^ j * ((A ^ 3 ^ j) ^ e)⁻¹ by
          rw [mul_pow, inv_pow, pow_right_comm]]
      exact h
    exact false_of_conjPair_frobenius_family data rfl hqprime hq3 hqodd he hcube hexp
      (mul_ne_zero hX0 (inv_ne_zero (pow_ne_zero _ hA0))) hfam'
  · -- read backwards: the pairs `(Y (-A)^{-e}, X (-A)^{-e})`
    have hfam' : ∀ j : ℕ,
        ConjPair data e ((Y * ((-A) ^ e)⁻¹) ^ 3 ^ j) ((X * ((-A) ^ e)⁻¹) ^ 3 ^ j) := by
      intro j
      have hodd3j : Odd (3 ^ j : ℕ) := (by decide : Odd (3 : ℕ)).pow
      have hAneg : (-A) ^ 3 ^ j = -(A ^ 3 ^ j) := hodd3j.neg_pow A
      have hAj : IsSquare (-(A ^ 3 ^ j)) := by
        rw [← hAneg]
        exact hnsq.pow _
      have h := SkewPair.conjPair_of_self_neg (hfam j) hAj (pow_ne_zero _ hA0)
      rw [show (Y * ((-A) ^ e)⁻¹) ^ 3 ^ j = Y ^ 3 ^ j * ((-(A ^ 3 ^ j)) ^ e)⁻¹ by
          rw [mul_pow, inv_pow, pow_right_comm, hAneg],
        show (X * ((-A) ^ e)⁻¹) ^ 3 ^ j = X ^ 3 ^ j * ((-(A ^ 3 ^ j)) ^ e)⁻¹ by
          rw [mul_pow, inv_pow, pow_right_comm, hAneg]]
      exact h
    exact false_of_conjPair_frobenius_family data rfl hqprime hq3 hqodd he hcube hexp
      (mul_ne_zero hY0 (inv_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr hA0)))) hfam'

/-! ### Frobenius-closed families of skew pairs -/

/-- Paley points are stable under the Frobenius map: `p₀ = p₁ + 1` gives
`p₀^{pʲ} = p₁^{pʲ} + 1`. -/
theorem paley_frobenius_iterate {p₀ p₁ : normOneUnits p q}
    (hpp : normOneVal p₀ = normOneVal p₁ + 1) (j : ℕ) :
    normOneVal (p₀ ^ p ^ j) = normOneVal (p₁ ^ p ^ j) + 1 := by
  simp only [normOneVal_pow]
  rw [hpp, add_pow_char_pow, one_pow]

/-- `(x^{pʲ})ᵏ - (y^{pʲ})ᵏ = (xᵏ - yᵏ)^{pʲ}` in characteristic `p`. -/
private theorem normOneVal_sub_pow_frobenius (j k : ℕ) (x y : normOneUnits p q) :
    normOneVal (x ^ p ^ j) ^ k - normOneVal (y ^ p ^ j) ^ k
      = (normOneVal x ^ k - normOneVal y ^ k) ^ p ^ j := by
  rw [normOneVal_pow, normOneVal_pow, pow_right_comm (normOneVal x) (p ^ j) k,
    pow_right_comm (normOneVal y) (p ^ j) k, ← sub_pow_char_pow]

/-- **A Frobenius-closed family of skew pairs**: every Frobenius image
`(A^{pʲ}, B^{pʲ}; X^{pʲ}, Y^{pʲ})` is a skew pair. -/
def FrobFam (data : Witness p q G) (e : ℕ) (A B X Y : GaloisField p q) : Prop :=
  ∀ j : ℕ, SkewPair data e (A ^ p ^ j) (B ^ p ^ j) (X ^ p ^ j) (Y ^ p ^ j)

namespace FrobFam

variable {data : Witness p q G} {e : ℕ}

/-- Edges are Frobenius-closed, because the Frobenius map sends Paley points to Paley points. -/
theorem edge (data : Witness p q G) (hp : p = 3) (hq : q ≠ 0) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {p₀ p₁ r₀ r₁ : normOneUnits p q}
    (hpp : normOneVal p₀ = normOneVal p₁ + 1) (hrr : normOneVal r₀ = normOneVal r₁ + 1) :
    FrobFam data e (normOneVal r₀ ^ e - normOneVal p₀ ^ e)
      (normOneVal r₁ ^ e - normOneVal p₁ ^ e)
      (normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e))
      (normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e)) := by
  intro j
  have he := skewPair_edge data hp hq hexp _ _ _ _ (paley_frobenius_iterate hpp j)
    (paley_frobenius_iterate hrr j)
  rw [normOneVal_sub_pow_frobenius j e r₀ p₀, normOneVal_sub_pow_frobenius j e r₁ p₁,
    normOneVal_sub_pow_frobenius j (e * e) p₁ p₀,
    normOneVal_sub_pow_frobenius j (e * e) r₁ r₀] at he
  exact he

/-- Reversal keeps a family Frobenius-closed, because `3ʲ` is odd. -/
theorem rev (hp : p = 3) {A B X Y : GaloisField p q} (h : FrobFam data e A B X Y) :
    FrobFam data e B A (-X) (-Y) := by
  subst hp
  intro j
  have hodd : Odd (3 ^ j : ℕ) := (by decide : Odd (3 : ℕ)).pow
  have hrev := (h j).rev
  rwa [← hodd.neg_pow X, ← hodd.neg_pow Y] at hrev

/-- Composition keeps a family Frobenius-closed, because `(x + y)^{pʲ} = x^{pʲ} + y^{pʲ}`. -/
theorem comp {A B C X₁ Y₁ X₂ Y₂ : GaloisField p q} (h₁ : FrobFam data e A B X₁ Y₁)
    (h₂ : FrobFam data e B C X₂ Y₂) : FrobFam data e A C (X₁ + X₂) (Y₁ + Y₂) := by
  intro j
  have hcomp := (h₁ j).comp (h₂ j)
  rwa [← add_pow_char_pow, ← add_pow_char_pow] at hcomp

/-- Rescaling by a nonzero square keeps a family Frobenius-closed. -/
theorem rescale {A B X Y : GaloisField p q} (h : FrobFam data e A B X Y)
    {s : GaloisField p q} (hs : IsSquare s) (hs0 : s ≠ 0) :
    FrobFam data e (A * s) (B * s) (X * s ^ e) (Y * s ^ e) := by
  intro j
  rw [mul_pow, mul_pow, show (X * s ^ e) ^ p ^ j = X ^ p ^ j * (s ^ p ^ j) ^ e by
      rw [mul_pow, pow_right_comm s e (p ^ j)],
    show (Y * s ^ e) ^ p ^ j = Y ^ p ^ j * (s ^ p ^ j) ^ e by
      rw [mul_pow, pow_right_comm s e (p ^ j)]]
  exact (h j).rescale (hs.pow _) (pow_ne_zero _ hs0)

/-- A Frobenius-closed closed loop `(A, A; X, Y)` with `A ≠ 0` and weights not both zero gives
a contradiction. -/
theorem false_of_self (data : Witness p q G) (hp : p = 3)
    (hqprime : q.Prime) (hq3 : q ≠ 3) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {A X Y : GaloisField p q} (hA0 : A ≠ 0) (hXY : ¬(X = 0 ∧ Y = 0))
    (h : FrobFam data e A A X Y) : False :=
  false_of_skewPair_self_frobenius_family data hp hqprime hq3 hqodd he hcube hexp hA0 hXY h

end FrobFam

/-! ### Edges with `δ₁ = -δ₀`

The edge from `r` to `p` is `(-δ₀, -δ₁; K(r), K(p))`. If `δ₁ = -δ₀`, it starts where the edge from
`p` to `r` ends, and the two compose into a closed loop with weights `(K(p) + K(r), K(r) + K(p))`.
-/

/-- An edge with `δ₁ = -δ₀` and `K(p) + K(r) ≠ 0` gives a contradiction. -/
theorem false_of_antipodal_edge (data : Witness p q G) (hp : p = 3)
    (hqprime : q.Prime) (hq3 : q ≠ 3) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {p₀ p₁ r₀ r₁ : normOneUnits p q}
    (hpp : normOneVal p₀ = normOneVal p₁ + 1) (hrr : normOneVal r₀ = normOneVal r₁ + 1)
    (hne : normOneVal p₀ ≠ normOneVal r₀)
    (hopp : normOneVal r₁ ^ e - normOneVal p₁ ^ e
      = -(normOneVal r₀ ^ e - normOneVal p₀ ^ e))
    (hK : (normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e))
      + (normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e)) ≠ 0) : False := by
  subst hp
  have hq0 : q ≠ 0 := hqprime.ne_zero
  have f₁ := FrobFam.edge data rfl hq0 hexp hpp hrr
  have f₂ := FrobFam.edge data rfl hq0 hexp hrr hpp
  -- the swap edge's parameters coincide with `δ₁` and `δ₀` on the ratio class `-1`
  rw [show normOneVal p₀ ^ e - normOneVal r₀ ^ e
      = normOneVal r₁ ^ e - normOneVal p₁ ^ e by linear_combination -hopp,
    show normOneVal p₁ ^ e - normOneVal r₁ ^ e
      = normOneVal r₀ ^ e - normOneVal p₀ ^ e by linear_combination -hopp] at f₂
  exact FrobFam.false_of_self data rfl hqprime hq3 hqodd he hcube hexp
    (skewPair_edge_left_ne_zero hcube hne) (fun hZ => hK hZ.1) (f₁.comp f₂)

/-- An edge with `δ₁ = -δ₀` has `K(p) + K(r) = 0`. -/
theorem weight_sum_eq_zero_of_antipodal_edge (data : Witness p q G) (hp : p = 3)
    (hqprime : q.Prime) (hq3 : q ≠ 3) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {p₀ p₁ r₀ r₁ : normOneUnits p q}
    (hpp : normOneVal p₀ = normOneVal p₁ + 1) (hrr : normOneVal r₀ = normOneVal r₁ + 1)
    (hne : normOneVal p₀ ≠ normOneVal r₀)
    (hopp : normOneVal r₁ ^ e - normOneVal p₁ ^ e
      = -(normOneVal r₀ ^ e - normOneVal p₀ ^ e)) :
    (normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e))
      + (normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e)) = 0 := by
  by_contra hK
  exact false_of_antipodal_edge data hp hqprime hq3 hqodd he hcube hexp hpp hrr hne hopp hK

/-! ### Legs at any height

A *leg* is an edge rescaled to start at a given nonzero height `h`. If `h / δ₀` is a square, we
rescale the edge from `p` to `r` by `h / δ₀`. Otherwise `-h / δ₀` is a square, and we rescale the
edge from `r` to `p` by `-h / δ₀`. In both cases the leg goes from `h` to `h δ₁ / δ₀`. -/

/-- If `h / δ₀` is a square, the edge from `p` to `r` gives a leg from `h` to `h δ₁ / δ₀` with
weights `K(p) (h / δ₀)ᵉ` and `K(r) (h / δ₀)ᵉ`. -/
theorem FrobFam.leg_fwd (data : Witness p q G) (hp : p = 3) (hq : q ≠ 0) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {p₀ p₁ r₀ r₁ : normOneUnits p q}
    (hpp : normOneVal p₀ = normOneVal p₁ + 1) (hrr : normOneVal r₀ = normOneVal r₁ + 1)
    (hA0 : normOneVal r₀ ^ e - normOneVal p₀ ^ e ≠ 0) {h : GaloisField p q} (hh0 : h ≠ 0)
    (hs : IsSquare (h * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹)) :
    FrobFam data e h
      (h * ((normOneVal r₁ ^ e - normOneVal p₁ ^ e)
        * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹))
      ((normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e))
        * (h * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹) ^ e)
      ((normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e))
        * (h * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹) ^ e) := by
  have hs0 : h * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹ ≠ 0 :=
    mul_ne_zero hh0 (inv_ne_zero hA0)
  have hfam := (FrobFam.edge data hp hq hexp hpp hrr).rescale hs hs0
  rw [show (normOneVal r₀ ^ e - normOneVal p₀ ^ e)
        * (h * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹) = h by
      field_simp,
    show (normOneVal r₁ ^ e - normOneVal p₁ ^ e)
        * (h * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹)
      = h * ((normOneVal r₁ ^ e - normOneVal p₁ ^ e)
        * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹) by ring] at hfam
  exact hfam

/-- If `-h / δ₀` is a square, the edge from `r` to `p` gives a leg from `h` to `h δ₁ / δ₀` with
weights `K(r) (-h / δ₀)ᵉ` and `K(p) (-h / δ₀)ᵉ`. -/
theorem FrobFam.leg_swap (data : Witness p q G) (hp : p = 3) (hq : q ≠ 0) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {p₀ p₁ r₀ r₁ : normOneUnits p q}
    (hpp : normOneVal p₀ = normOneVal p₁ + 1) (hrr : normOneVal r₀ = normOneVal r₁ + 1)
    (hA0 : normOneVal r₀ ^ e - normOneVal p₀ ^ e ≠ 0) {h : GaloisField p q} (hh0 : h ≠ 0)
    (hs : IsSquare (-(h * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹))) :
    FrobFam data e h
      (h * ((normOneVal r₁ ^ e - normOneVal p₁ ^ e)
        * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹))
      ((normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e))
        * (-(h * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹)) ^ e)
      ((normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e))
        * (-(h * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹)) ^ e) := by
  have hs0 : -(h * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero hh0 (inv_ne_zero hA0))
  have hfam := (FrobFam.edge data hp hq hexp hrr hpp).rescale hs hs0
  rw [show (normOneVal p₀ ^ e - normOneVal r₀ ^ e)
        * -(h * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹) = h by
      field_simp; ring,
    show (normOneVal p₁ ^ e - normOneVal r₁ ^ e)
        * -(h * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹)
      = h * ((normOneVal r₁ ^ e - normOneVal p₁ ^ e)
        * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹) by
      field_simp; ring] at hfam
  exact hfam

/-- The coefficient of a leg's first weight: `K(p)` in the first case (`true`) and `-K(r)` in
the second case (`false`). -/
noncomputable def legWeight (Kp Kr : GaloisField p q) : Bool → GaloisField p q
  | true => Kp
  | false => -Kr

@[simp] theorem legWeight_true (Kp Kr : GaloisField p q) : legWeight Kp Kr true = Kp := rfl

@[simp] theorem legWeight_false (Kp Kr : GaloisField p q) : legWeight Kp Kr false = -Kr := rfl

/-- Both cases at once. The Boolean `b` says whether `h / δ₀` is a square. The leg goes from `h`
to `h δ₁ / δ₀`, with weights `legWeight K(p) K(r) b · (h / δ₀)ᵉ` and
`legWeight K(r) K(p) b · (h / δ₀)ᵉ`; here we use that `e` is odd. -/
theorem FrobFam.leg_resolved (data : Witness p q G) (hp : p = 3) (hq : q ≠ 0)
    {e : ℕ} (he : Odd e)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {p₀ p₁ r₀ r₁ : normOneUnits p q}
    (hpp : normOneVal p₀ = normOneVal p₁ + 1) (hrr : normOneVal r₀ = normOneVal r₁ + 1)
    (hA0 : normOneVal r₀ ^ e - normOneVal p₀ ^ e ≠ 0) {h : GaloisField p q} (hh0 : h ≠ 0)
    (b : Bool)
    (hs : cond b (IsSquare (h * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹))
      (IsSquare (-(h * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹)))) :
    FrobFam data e h
      (h * ((normOneVal r₁ ^ e - normOneVal p₁ ^ e)
        * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹))
      (legWeight (normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e))
          (normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e)) b
        * (h * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹) ^ e)
      (legWeight (normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e))
          (normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e)) b
        * (h * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹) ^ e) := by
  cases b
  · have hfam := FrobFam.leg_swap data hp hq hexp hpp hrr hA0 hh0 hs
    simp only [legWeight]
    rw [show (normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e))
          * (-(h * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹)) ^ e
        = -(normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e))
          * (h * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹) ^ e by
        rw [he.neg_pow]; ring,
      show (normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e))
          * (-(h * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹)) ^ e
        = -(normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e))
          * (h * (normOneVal r₀ ^ e - normOneVal p₀ ^ e)⁻¹) ^ e by
        rw [he.neg_pow]; ring] at hfam
    exact hfam
  · simpa only [legWeight] using
      FrobFam.leg_fwd data hp hq hexp hpp hrr hA0 hh0 hs

/-! ### Four-leg loops

Four Frobenius-closed families that chain as `A → B₁ → B₂ ← B₃ ← A` compose into the closed loop
`h₁ ∘ h₂ ∘ rev h₃ ∘ rev h₄`, with weights `(X₁ + X₂ - X₃ - X₄, Y₁ + Y₂ - Y₃ - Y₄)`. -/

/-- A four-leg loop whose weights are not both zero gives a contradiction. -/
theorem false_of_four_loop (data : Witness p q G) (hp : p = 3)
    (hqprime : q.Prime) (hq3 : q ≠ 3) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {A B₁ B₂ B₃ X₁ Y₁ X₂ Y₂ X₃ Y₃ X₄ Y₄ : GaloisField p q}
    (h₁ : FrobFam data e A B₁ X₁ Y₁) (h₂ : FrobFam data e B₁ B₂ X₂ Y₂)
    (h₃ : FrobFam data e B₃ B₂ X₃ Y₃) (h₄ : FrobFam data e A B₃ X₄ Y₄)
    (hA0 : A ≠ 0)
    (hW : ¬(X₁ + X₂ - X₃ - X₄ = 0 ∧ Y₁ + Y₂ - Y₃ - Y₄ = 0)) : False := by
  subst hp
  have hcomp := ((h₁.comp h₂).comp (h₃.rev rfl)).comp (h₄.rev rfl)
  rw [show X₁ + X₂ + -X₃ + -X₄ = X₁ + X₂ - X₃ - X₄ by ring,
    show Y₁ + Y₂ + -Y₃ + -Y₄ = Y₁ + Y₂ - Y₃ - Y₄ by ring] at hcomp
  exact FrobFam.false_of_self data rfl hqprime hq3 hqodd he hcube hexp hA0 hW hcomp

/-- The weights of a four-leg loop vanish. -/
theorem weights_eq_zero_of_four_loop (data : Witness p q G) (hp : p = 3)
    (hqprime : q.Prime) (hq3 : q ≠ 3) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {A B₁ B₂ B₃ X₁ Y₁ X₂ Y₂ X₃ Y₃ X₄ Y₄ : GaloisField p q}
    (h₁ : FrobFam data e A B₁ X₁ Y₁) (h₂ : FrobFam data e B₁ B₂ X₂ Y₂)
    (h₃ : FrobFam data e B₃ B₂ X₃ Y₃) (h₄ : FrobFam data e A B₃ X₄ Y₄)
    (hA0 : A ≠ 0) :
    X₁ + X₂ - X₃ - X₄ = 0 ∧ Y₁ + Y₂ - Y₃ - Y₄ = 0 := by
  by_contra hW
  exact false_of_four_loop data hp hqprime hq3 hqodd he hcube hexp h₁ h₂ h₃ h₄ hA0 hW

end SkewCalculus

end PeterfalviProblem
