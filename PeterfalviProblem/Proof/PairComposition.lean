/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import PeterfalviProblem.Algebra.FrobeniusCyclicModule
import PeterfalviProblem.Proof.CommutingSubgroup

/-!
# Conjugation pairs and collisions

Let `data` be a witness with `p = 3` and `q ≠ 3` odd, and let `e` be an odd exponent as in
`exists_odd_cube_exponent`.

A *conjugation pair* `ConjPair data e s s'` is the relation

`a(v) · b(s vᵉ) · a(v)⁻¹ = b(s' vᵉ)` for every nonzero square `v`.

Pairs can be added, and a pair `(0, s')` has `s' = 0`. In characteristic three
`a(v)² = a(-v) = a(v)⁻¹`, so pairs `(s, s')` and `(s', s'')` give a pair `(s'', s)`
(`ConjPair.chain`).

Suppose that `(S^{3ʲ}, S'^{3ʲ})` is a pair for every `j`, and `S ≠ 0`. Then `(c · S, c · S')` is a
pair for every polynomial `c ∈ 𝔽₃[X]`, where `X` acts as the Frobenius map. The Frobenius module
is cyclic, so `S' = a₀ · S` for some polynomial `a₀`. The chain rule then gives `a₀³ · S = S`, and
`a₀³ - 1 = (a₀ - 1)³` in characteristic three. For `q ≠ 3` the polynomial `X^q - 1` has no
repeated factors, so `a₀ · S = S`, that is, `S' = S`. But a pair `(S, S)` with `S ≠ 0` puts `S`
into `commSubgroup`, which contradicts the fixed-point principle
(`false_of_conjPair_frobenius_family`).

A *collision* is given by norm-one units `p₀ = p₁ + 1` and `r₀ = r₁ + 1` with `p₀ ≠ r₀` and
`p₀ᵉ - p₁ᵉ = r₀ᵉ - r₁ᵉ` (`CollisionPair`). By `layerFieldHom_one_conj`, a collision gives a
conjugation pair, and its images under the Frobenius map give a whole family. So no collision
exists (`false_of_collisionPair`).

## Main results

* `ConjPair.chain`: pairs `(s, s')` and `(s', s'')` give the pair `(s'', s)`.
* `false_of_conjPair_frobenius_family`: a Frobenius-closed family of pairs with `S ≠ 0` gives a
  contradiction.
* `false_of_collisionPair`: a collision gives a contradiction.
-/

namespace PeterfalviProblem

section PairComposition

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

/-! ### Collisions -/

/-- **A collision.** There are norm-one units `p₀ = p₁ + 1` and `r₀ = r₁ + 1` with
`p₀ᵉ - p₁ᵉ = r₀ᵉ - r₁ᵉ`, such that `δ = r₀ᵉ - p₀ᵉ` is also a norm-one unit (`d₀`). The values are
`S = K(p) · (δ⁻¹)^{e⁴}` and `S' = K(r) · (δ⁻¹)^{e⁴}`, where `K(p) = p₁^{e²} - p₀^{e²}` and
`K(r) = r₁^{e²} - r₀^{e²}`. When `z^{e³} = z` for all `z`, the factor `(δ⁻¹)^{e⁴}` is
`δ^{-e}`. -/
def CollisionPair (p q e : ℕ) [Fact p.Prime] (S S' : GaloisField p q) : Prop :=
  ∃ p₀ p₁ r₀ r₁ d₀ : normOneUnits p q,
    normOneVal p₀ = normOneVal p₁ + 1 ∧ normOneVal r₀ = normOneVal r₁ + 1 ∧
    normOneVal p₀ ^ e - normOneVal p₁ ^ e = normOneVal r₀ ^ e - normOneVal r₁ ^ e ∧
    normOneVal d₀ = normOneVal r₀ ^ e - normOneVal p₀ ^ e ∧
    S = (normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e)) *
        normOneVal (d₀⁻¹ ^ (e * e)) ^ (e * e) ∧
    S' = (normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e)) *
        normOneVal (d₀⁻¹ ^ (e * e)) ^ (e * e)

/-- The condition that `δ` be a square costs nothing. Let `p₀ = p₁ + 1` and `r₀ = r₁ + 1` be
norm-one units with `p₀ᵉ - p₁ᵉ = r₀ᵉ - r₁ᵉ` and `r₀ᵉ - p₀ᵉ ≠ 0`. Since `-1` is not a square,
exactly one of `r₀ᵉ - p₀ᵉ` and `p₀ᵉ - r₀ᵉ` is a square. So one of the two orders of the points
gives a `CollisionPair`. -/
theorem exists_collisionPair_of_sub_ne_zero (hp : p = 3) (hq : q ≠ 0) (hqodd : Odd q) {e : ℕ}
    (p₀ p₁ r₀ r₁ : normOneUnits p q)
    (hpp : normOneVal p₀ = normOneVal p₁ + 1) (hrr : normOneVal r₀ = normOneVal r₁ + 1)
    (hcoll : normOneVal p₀ ^ e - normOneVal p₁ ^ e = normOneVal r₀ ^ e - normOneVal r₁ ^ e)
    (hd : normOneVal r₀ ^ e - normOneVal p₀ ^ e ≠ 0) :
    ∃ S S', CollisionPair p q e S S' := by
  subst hp
  rcases isSquare_or_isSquare_neg_galois rfl hq hqodd hd with hsq | hnsq
  · -- the given order already has a square difference
    refine ⟨_, _, p₀, p₁, r₀, r₁,
      ⟨Units.mk0 _ hd, (mem_normOneUnits_iff_isSquare rfl hq _).mpr hsq⟩,
      hpp, hrr, hcoll, rfl, rfl, rfl⟩
  · -- swap the two points; the difference changes sign
    have hd' : normOneVal p₀ ^ e - normOneVal r₀ ^ e ≠ 0 := by
      intro h
      exact hd (by linear_combination -h)
    have hsq' : IsSquare (normOneVal p₀ ^ e - normOneVal r₀ ^ e) := by
      have hrw : normOneVal p₀ ^ e - normOneVal r₀ ^ e
          = -(normOneVal r₀ ^ e - normOneVal p₀ ^ e) := by ring
      rw [hrw]
      exact hnsq
    refine ⟨_, _, r₀, r₁, p₀, p₁,
      ⟨Units.mk0 _ hd', (mem_normOneUnits_iff_isSquare rfl hq _).mpr hsq'⟩,
      hrr, hpp, hcoll.symm, rfl, rfl, rfl⟩

/-- Collisions are stable under the Frobenius map. In characteristic `p`, the map `a ↦ a^p` is a
ring homomorphism. So it sends a collision to a collision, and it raises `S` and `S'` to the
`p`-th power. -/
theorem CollisionPair.frobenius {e : ℕ} {S S' : GaloisField p q}
    (h : CollisionPair p q e S S') : CollisionPair p q e (S ^ p) (S' ^ p) := by
  obtain ⟨p₀, p₁, r₀, r₁, d₀, hpp, hrr, hcoll, hd, rfl, rfl⟩ := h
  have hswap : ∀ (a : GaloisField p q) (k : ℕ), (a ^ p) ^ k = (a ^ k) ^ p := by
    intro a k
    rw [← pow_mul, Nat.mul_comm, pow_mul]
  have hd0 : ((d₀ ^ p)⁻¹ : normOneUnits p q) ^ (e * e) = (d₀⁻¹ ^ (e * e)) ^ p := by
    rw [← inv_pow, ← pow_mul, ← pow_mul, Nat.mul_comm p (e * e)]
  refine ⟨p₀ ^ p, p₁ ^ p, r₀ ^ p, r₁ ^ p, d₀ ^ p, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [normOneVal_pow]
    rw [hpp, add_pow_char, one_pow]
  · simp only [normOneVal_pow]
    rw [hrr, add_pow_char, one_pow]
  · simp only [normOneVal_pow, hswap, ← sub_pow_char, hcoll]
  · simp only [normOneVal_pow, hswap, ← sub_pow_char]
    rw [hd]
  · rw [hd0]
    simp only [normOneVal_pow, hswap, ← sub_pow_char, ← mul_pow]
  · rw [hd0]
    simp only [normOneVal_pow, hswap, ← sub_pow_char, ← mul_pow]

/-- The same for `a ↦ a^{pʲ}`. -/
theorem CollisionPair.frobenius_iterate {e : ℕ} {S S' : GaloisField p q}
    (h : CollisionPair p q e S S') (j : ℕ) :
    CollisionPair p q e (S ^ p ^ j) (S' ^ p ^ j) := by
  induction j with
  | zero => simpa using h
  | succ k ih =>
      have hstep := ih.frobenius
      rwa [← pow_mul, ← pow_mul, ← pow_succ] at hstep

/-- **A conjugation pair**: `a(v) · b(s vᵉ) · a(v)⁻¹ = b(s' vᵉ)` for every nonzero square
`v`. -/
def ConjPair (data : Witness p q G) (e : ℕ) (s s' : GaloisField p q) : Prop :=
  ∀ v : GaloisField p q, IsSquare v → v ≠ 0 →
    layerFieldHom data 0 (Multiplicative.ofAdd v) *
        layerFieldHom data 1 (Multiplicative.ofAdd (s * v ^ e)) *
        (layerFieldHom data 0 (Multiplicative.ofAdd v))⁻¹
      = layerFieldHom data 1 (Multiplicative.ofAdd (s' * v ^ e))

/-- Conjugation distributes over products. -/
private theorem conj_mul {H : Type*} [Group H] {x b₁ b₂ c₁ c₂ : H}
    (h₁ : x * b₁ * x⁻¹ = c₁) (h₂ : x * b₂ * x⁻¹ = c₂) : x * (b₁ * b₂) * x⁻¹ = c₁ * c₂ := by
  rw [← h₁, ← h₂]; group

/-- Conjugation commutes with inversion. -/
private theorem conj_inv {H : Type*} [Group H] {x b c : H}
    (h : x * b * x⁻¹ = c) : x * b⁻¹ * x⁻¹ = c⁻¹ := by
  rw [← h]; group

namespace ConjPair

variable {data : Witness p q G} {e : ℕ}

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

/-- Pairs can be added, because the layer `b` and conjugation are homomorphisms. -/
theorem add {s₁ s₁' s₂ s₂' : GaloisField p q} (h₁ : ConjPair data e s₁ s₁')
    (h₂ : ConjPair data e s₂ s₂') : ConjPair data e (s₁ + s₂) (s₁' + s₂') := by
  intro v hv hv0
  rw [layer_split data 1 (show (s₁ + s₂) * v ^ e = s₁ * v ^ e + s₂ * v ^ e by ring),
    layer_split data 1 (show (s₁' + s₂') * v ^ e = s₁' * v ^ e + s₂' * v ^ e by ring)]
  exact conj_mul (h₁ v hv hv0) (h₂ v hv hv0)

/-- `(0, 0)` is a pair. -/
theorem zero (data : Witness p q G) (e : ℕ) : ConjPair data e 0 0 := by
  intro v hv hv0
  have h0 : layerFieldHom data 1 (Multiplicative.ofAdd ((0 : GaloisField p q) * v ^ e)) = 1 := by
    have harg : Multiplicative.ofAdd ((0 : GaloisField p q) * v ^ e) = 1 := by
      rw [zero_mul]
      exact ofAdd_zero
    rw [harg]
    exact map_one _
  rw [h0, mul_one]
  exact mul_inv_cancel _

/-- Pairs can be negated. -/
theorem neg {s s' : GaloisField p q} (h : ConjPair data e s s') :
    ConjPair data e (-s) (-s') := by
  intro v hv hv0
  rw [layer_neg data 1 (show -s * v ^ e = -(s * v ^ e) by ring),
    layer_neg data 1 (show -s' * v ^ e = -(s' * v ^ e) by ring)]
  exact conj_inv (h v hv hv0)

/-- Pairs can be multiplied by natural numbers. -/
theorem nsmul {s s' : GaloisField p q} (h : ConjPair data e s s') (k : ℕ) :
    ConjPair data e (k • s) (k • s') := by
  induction k with
  | zero => simpa using ConjPair.zero data e
  | succ n ih =>
      rw [succ_nsmul, succ_nsmul]
      exact ih.add h

/-- Finite sums of pairs are pairs. -/
theorem sum {ι : Type*} (f g : ι → GaloisField p q) (T : Finset ι)
    (h : ∀ i ∈ T, ConjPair data e (f i) (g i)) :
    ConjPair data e (∑ i ∈ T, f i) (∑ i ∈ T, g i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using ConjPair.zero data e
  | insert a T ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a T)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A pair `(0, s')` has `s' = 0`, because `b(s') = a(1) · 1 · a(1)⁻¹ = 1` and the layer `b` is
injective. -/
theorem right_eq_zero {s' : GaloisField p q} (h : ConjPair data e 0 s') : s' = 0 := by
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
  have hval : (0 : GaloisField p q) = s' * 1 ^ e := by
    have := congrArg Multiplicative.toAdd harg
    simpa using this
  simpa using hval.symm

end ConjPair

/-- **A collision gives a conjugation pair** `(S, S')`. Substitute `v = δ zᵉ` in
`layerFieldHom_one_conj`. As `z` runs over the norm-one units, so does `v`, because `δ` is a
square and `z ↦ zᵉ` is a bijection. -/
theorem ConjPair.of_collisionPair (data : Witness p q G) (hp : p = 3) (hq : q ≠ 0)
    {e : ℕ} (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {S S' : GaloisField p q} (hpair : CollisionPair p q e S S') : ConjPair data e S S' := by
  obtain ⟨p₀, p₁, r₀, r₁, d₀, hpp, hrr, hcoll, hd, hS, hS'⟩ := hpair
  have hd0 : normOneVal d₀ ≠ 0 := Units.ne_zero _
  have hdcube : normOneVal d₀ ^ (e * e * e) = normOneVal d₀ := by
    have hu := normOneUnits_pow_cube data hp hexp d₀
    calc normOneVal d₀ ^ (e * e * e) = normOneVal (d₀ ^ (e * e * e)) := by rw [normOneVal_pow]
      _ = normOneVal d₀ := by rw [hu]
  have hZval : normOneVal (d₀⁻¹ ^ (e * e)) ^ (e * e) * normOneVal d₀ ^ e = 1 := by
    have hexp4 : e * e * (e * e) = e * e * e * e := by ring
    rw [normOneVal_pow, normOneVal_inv, ← pow_mul, inv_pow, hexp4, pow_mul, hdcube]
    exact inv_mul_cancel₀ (pow_ne_zero _ hd0)
  have hSd : S * normOneVal d₀ ^ e
      = normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e) := by
    rw [hS, mul_assoc, hZval, mul_one]
  have hS'd : S' * normOneVal d₀ ^ e
      = normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e) := by
    rw [hS', mul_assoc, hZval, mul_one]
  have hdsq : IsSquare (normOneVal d₀) := by
    have := (mem_normOneUnits_iff_isSquare hp hq (d₀ : (GaloisField p q)ˣ)).mp d₀.2
    simpa [normOneVal] using this
  intro w hw hw0
  -- normalise the argument: `w = δ · v` with `v` a non-zero square
  have hv_sq : IsSquare ((normOneVal d₀)⁻¹ * w) := hdsq.inv.mul hw
  have hv0 : (normOneVal d₀)⁻¹ * w ≠ 0 := mul_ne_zero (inv_ne_zero hd0) hw0
  obtain ⟨u0, hu0⟩ : ∃ u0 : normOneUnits p q,
      normOneVal u0 = (normOneVal d₀)⁻¹ * w :=
    ⟨⟨Units.mk0 _ hv0, (mem_normOneUnits_iff_isSquare hp hq _).mpr (by simpa using hv_sq)⟩, rfl⟩
  have hcubev : normOneVal u0 ^ (e * e * e) = normOneVal u0 := by
    have hu := normOneUnits_pow_cube data hp hexp u0
    calc normOneVal u0 ^ (e * e * e) = normOneVal (u0 ^ (e * e * e)) := by rw [normOneVal_pow]
      _ = normOneVal u0 := by rw [hu]
  have hue : normOneVal (u0 ^ (e * e)) ^ e = (normOneVal d₀)⁻¹ * w := by
    rw [normOneVal_pow, ← pow_mul, hcubev, hu0]
  have hue2 : normOneVal (u0 ^ (e * e)) ^ (e * e) = ((normOneVal d₀)⁻¹ * w) ^ e := by
    have hexp4 : e * e * (e * e) = e * e * e * e := by ring
    rw [normOneVal_pow, ← pow_mul, hexp4, pow_mul, hcubev, hu0]
  have hrel := layerFieldHom_one_conj data hp hexp p₀ p₁ r₀ r₁ (u0 ^ (e * e)) hpp hrr hcoll
  rw [hue, hue2, ← hd] at hrel
  have hw' : normOneVal d₀ * ((normOneVal d₀)⁻¹ * w) = w := by
    rw [← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
  have hcancel : ∀ X : GaloisField p q,
      X * normOneVal d₀ ^ e * ((normOneVal d₀)⁻¹ * w) ^ e = X * w ^ e := by
    intro X
    rw [mul_pow, inv_pow]
    calc X * normOneVal d₀ ^ e * ((normOneVal d₀ ^ e)⁻¹ * w ^ e)
        = X * (normOneVal d₀ ^ e * (normOneVal d₀ ^ e)⁻¹) * w ^ e := by ring
      _ = X * w ^ e := by rw [mul_inv_cancel₀ (pow_ne_zero _ hd0)]; ring
  have hbS : (normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e)) *
      ((normOneVal d₀)⁻¹ * w) ^ e = S * w ^ e := by
    rw [← hSd]; exact hcancel S
  have hbS' : (normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e)) *
      ((normOneVal d₀)⁻¹ * w) ^ e = S' * w ^ e := by
    rw [← hS'd]; exact hcancel S'
  rw [hw', hbS, hbS'] at hrel
  rw [ConjPair.layer_neg data 0 (rfl : -w = -w)] at hrel
  exact hrel.symm

/-- A pair `(m, m)` with `m ≠ 0` gives a contradiction. Such a pair says that `a(v)` commutes
with `b(m vᵉ)` for every nonzero square `v`. So `m ∈ commSubgroup`, and the fixed-point principle
`false_of_mem_commSubgroup_ne_zero` applies. -/
theorem false_of_conjPair_self (data : Witness p q G) (hp : p = 3)
    (hqprime : q.Prime) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {m : GaloisField p q} (h : ConjPair data e m m) (hm0 : m ≠ 0) : False := by
  have hq0 : q ≠ 0 := hqprime.ne_zero
  have hmem : m ∈ commSubgroup data e := by
    refine mem_commSubgroup_of_square data hp hq0 hqodd he one_ne_zero ?_
    intro v hv hv0
    have h1 := h v hv hv0
    simp only [one_mul]
    exact (commute_iff_eq _ _).mpr (mul_inv_eq_iff_eq_mul.mp h1)
  exact false_of_mem_commSubgroup_ne_zero data hp hqprime hqodd he hcube hexp hmem hm0

/-- The value `S` of a collision is nonzero, because `z ↦ z^{e²}` is injective and
`p₀ ≠ p₁`. -/
theorem CollisionPair.left_ne_zero {e : ℕ}
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    {S S' : GaloisField p q} (hpair : CollisionPair p q e S S') : S ≠ 0 := by
  obtain ⟨p₀, p₁, r₀, r₁, d₀, hpp, -, -, -, hS, -⟩ := hpair
  rw [hS]
  refine mul_ne_zero ?_ (pow_ne_zero _ (Units.ne_zero _))
  intro hzero
  have hEq : normOneVal p₁ ^ (e * e) = normOneVal p₀ ^ (e * e) := by
    linear_combination hzero
  have hinj : normOneVal p₁ = normOneVal p₀ := by
    have h1 := hcube (normOneVal p₁)
    have h2 := hcube (normOneVal p₀)
    calc normOneVal p₁ = (normOneVal p₁ ^ (e * e)) ^ e := by rw [← pow_mul, h1]
      _ = (normOneVal p₀ ^ (e * e)) ^ e := by rw [hEq]
      _ = normOneVal p₀ := by rw [← pow_mul, h2]
  rw [hpp] at hinj
  exact one_ne_zero (by linear_combination -hinj)

/-! ### Chain reversal

In characteristic three, `a(v)² = a(2v) = a(-v) = a(v)⁻¹`. So two conjugations by `a(v)` are one
conjugation by `a(v)⁻¹`. -/

/-- **Chain reversal.** Pairs `(s, s')` and `(s', s'')` give the pair `(s'', s)`. Conjugating the
first relation by `a(v)` and using the second gives `a(v)² · b(s vᵉ) · a(v)⁻² = b(s'' vᵉ)`, and
`a(v)² = a(v)⁻¹`. -/
theorem ConjPair.chain (data : Witness p q G) (hp : p = 3)
    {e : ℕ} {s s' s'' : GaloisField p q}
    (h₁ : ConjPair data e s s') (h₂ : ConjPair data e s' s'') :
    ConjPair data e s'' s := by
  subst hp
  have : CharP (GaloisField 3 q) 3 := by
    rw [← Algebra.charP_iff (ZMod 3) (GaloisField 3 q) 3]
    exact ZMod.charP 3
  intro v hv hv0
  have h1 := h₁ v hv hv0
  have h2 := h₂ v hv hv0
  have hdouble : layerFieldHom data 0 (Multiplicative.ofAdd (v + v)) *
      layerFieldHom data 1 (Multiplicative.ofAdd (s * v ^ e)) *
      (layerFieldHom data 0 (Multiplicative.ofAdd (v + v)))⁻¹
      = layerFieldHom data 1 (Multiplicative.ofAdd (s'' * v ^ e)) := by
    rw [ConjPair.layer_split data 0 (rfl : v + v = v + v)]
    calc (layerFieldHom data 0 (Multiplicative.ofAdd v) *
          layerFieldHom data 0 (Multiplicative.ofAdd v)) *
          layerFieldHom data 1 (Multiplicative.ofAdd (s * v ^ e)) *
          (layerFieldHom data 0 (Multiplicative.ofAdd v) *
            layerFieldHom data 0 (Multiplicative.ofAdd v))⁻¹
        = layerFieldHom data 0 (Multiplicative.ofAdd v) *
          (layerFieldHom data 0 (Multiplicative.ofAdd v) *
            layerFieldHom data 1 (Multiplicative.ofAdd (s * v ^ e)) *
            (layerFieldHom data 0 (Multiplicative.ofAdd v))⁻¹) *
          (layerFieldHom data 0 (Multiplicative.ofAdd v))⁻¹ := by group
      _ = layerFieldHom data 0 (Multiplicative.ofAdd v) *
          layerFieldHom data 1 (Multiplicative.ofAdd (s' * v ^ e)) *
          (layerFieldHom data 0 (Multiplicative.ofAdd v))⁻¹ := by rw [h1]
      _ = _ := h2
  have hvv : v + v = -v := by
    have h3 : (3 : GaloisField 3 q) = 0 := by
      exact_mod_cast CharP.cast_eq_zero (GaloisField 3 q) 3
    linear_combination v * h3
  rw [hvv, ConjPair.layer_neg data 0 (rfl : -v = -v), inv_inv] at hdouble
  rw [← hdouble]
  group

/-! ### Frobenius-closed families

`ConjPair.chain` and the cyclicity of the Frobenius module (`Algebra/FrobeniusCyclicModule.lean`)
turn a Frobenius-closed family of pairs into a pair `(S, S)`.

* A pair `(0, s')` has `s' = 0`. So every polynomial that kills `S` also kills `S'`, and hence
  `S' = a₀ · S` for some polynomial `a₀` (`exists_aeval_frobEnd_eq_of_forall_imp`).
* The chain rule, applied to the pairs `(S, a₀ · S)` and `(a₀ · S, a₀² · S)`, gives the pair
  `(a₀² · S, S)`. Comparing it with the pair `(a₀² · S, a₀³ · S)` gives `a₀³ · S = S`.
* In characteristic three, `a₀³ - 1 = (a₀ - 1)³`. For `q ≠ 3`, `X^q - 1` has no repeated
  factors, so `a₀ · S = S`, that is, `S' = S`. -/

open Polynomial in
/-- If `(S^{pʲ}, S'^{pʲ})` is a pair for every `j`, then `(c · S, c · S')` is a pair for every
polynomial `c`. -/
theorem conjPair_aeval_of_frobenius_family (data : Witness p q G) {e : ℕ}
    {S S' : GaloisField p q}
    (hfam : ∀ j : ℕ, ConjPair data e (S ^ p ^ j) (S' ^ p ^ j)) (c : (ZMod p)[X]) :
    ConjPair data e (aeval (frobEnd p q) c S) (aeval (frobEnd p q) c S') := by
  rw [aeval_frobEnd_apply, aeval_frobEnd_apply]
  exact ConjPair.sum _ _ _ fun j _ => (hfam j).nsmul _

open Polynomial in
/-- **Frobenius-closed families.** Let `q ≠ 3`, and suppose that `(S^{3ʲ}, S'^{3ʲ})` is a pair
for every `j`, with `S ≠ 0`. Then we reach a contradiction: by the argument above, `(S, S)` is a
pair, which contradicts `false_of_conjPair_self`. -/
theorem false_of_conjPair_frobenius_family (data : Witness p q G) (hp : p = 3)
    (hqprime : q.Prime) (hq3 : q ≠ 3) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {S S' : GaloisField p q} (hS0 : S ≠ 0)
    (hfam : ∀ j : ℕ, ConjPair data e (S ^ p ^ j) (S' ^ p ^ j)) : False := by
  subst hp
  have hq0 : q ≠ 0 := hqprime.ne_zero
  have hcp : ∀ c : (ZMod 3)[X],
      ConjPair data e (aeval (frobEnd 3 q) c S) (aeval (frobEnd 3 q) c S') :=
    conjPair_aeval_of_frobenius_family data hfam
  have haux : ∀ y : GaloisField 3 q, ∀ a b : (ZMod 3)[X],
      aeval (frobEnd 3 q) (a * b) y
        = aeval (frobEnd 3 q) a (aeval (frobEnd 3 q) b y) := by
    intro y a b
    rw [map_mul, Module.End.mul_apply]
  -- the graph property forces the annihilator inclusion
  have hann : ∀ c : (ZMod 3)[X],
      aeval (frobEnd 3 q) c S = 0 → aeval (frobEnd 3 q) c S' = 0 := by
    intro c h0
    have h := hcp c
    rw [h0] at h
    exact ConjPair.right_eq_zero h
  obtain ⟨a₀, ha₀⟩ := exists_aeval_frobEnd_eq_of_forall_imp 3 q hq0 hann
  -- chain reversal at the pair `(S, S')` and its `a₀`-translate
  have h1 : ConjPair data e S S' := by
    have h := hcp 1
    simpa using h
  have h2 : ConjPair data e S' (aeval (frobEnd 3 q) a₀ S') := by
    have h := hcp a₀
    rwa [ha₀] at h
  have h3 := ConjPair.chain data rfl h1 h2
  have hsq2 : aeval (frobEnd 3 q) a₀ S' = aeval (frobEnd 3 q) (a₀ * a₀) S := by
    rw [haux S a₀ a₀, ha₀]
  rw [hsq2] at h3
  -- subtract the `a₀²`-pair: the graph forces `a₀³ • S = S`
  have h5 := (hcp (a₀ * a₀)).add h3.neg
  rw [add_neg_cancel] at h5
  have h6 : aeval (frobEnd 3 q) (a₀ * a₀) S' = S :=
    add_neg_eq_zero.mp (ConjPair.right_eq_zero h5)
  -- `(a₀³ - 1) • S = 0`, and `(a₀ - 1)³ = a₀³ - 1` in characteristic three
  have h33 : aeval (frobEnd 3 q) (a₀ ^ 3) S = S := by
    have hpow : a₀ ^ 3 = (a₀ * a₀) * a₀ := by ring
    rw [hpow, haux S (a₀ * a₀) a₀, ha₀]
    exact h6
  have h7 : aeval (frobEnd 3 q) (a₀ ^ 3 - 1) S = 0 := by
    rw [map_sub, LinearMap.sub_apply, h33, map_one, Module.End.one_apply, sub_self]
  have : CharP ((ZMod 3)[X]) 3 :=
    charP_of_injective_ringHom (C_injective (R := ZMod 3)) 3
  have : ExpChar ((ZMod 3)[X]) 3 := .prime Nat.prime_three
  have hchar : (a₀ - 1) ^ 3 = a₀ ^ 3 - 1 := by
    rw [sub_pow_expChar, one_pow]
  have h8 : aeval (frobEnd 3 q) ((a₀ - 1) ^ 3) S = 0 := by
    rw [hchar]
    exact h7
  have hpq : ¬ (3 : ℕ) ∣ q := fun hdvd =>
    hq3 (((Nat.prime_dvd_prime_iff_eq Nat.prime_three hqprime).mp hdvd).symm)
  have h9 := aeval_frobEnd_eq_zero_of_pow 3 q hq0 hpq (by norm_num : (3 : ℕ) ≠ 0) h8
  rw [map_sub, LinearMap.sub_apply, map_one, Module.End.one_apply] at h9
  have hSS : S' = S := by
    rw [← ha₀]
    exact sub_eq_zero.mp h9
  have hself : ConjPair data e S S := by
    have h := h1
    rwa [hSS] at h
  exact false_of_conjPair_self data rfl hqprime hqodd he hcube hexp hself hS0

open Polynomial in
/-- **No collision exists** when `q ≠ 3`. The Frobenius images of a collision give a
Frobenius-closed family of pairs (`ConjPair.of_collisionPair`, `CollisionPair.frobenius_iterate`),
and `false_of_conjPair_frobenius_family` applies. -/
theorem false_of_collisionPair (data : Witness p q G) (hp : p = 3)
    (hqprime : q.Prime) (hq3 : q ≠ 3) (hqodd : Odd q) {e : ℕ} (he : Odd e)
    (hcube : ∀ z : GaloisField p q, z ^ (e * e * e) = z)
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {S S' : GaloisField p q} (hpair : CollisionPair p q e S S') : False :=
  false_of_conjPair_frobenius_family data hp hqprime hq3 hqodd he hcube hexp
    (CollisionPair.left_ne_zero hcube hpair)
    (fun j => ConjPair.of_collisionPair data hp hqprime.ne_zero hexp
      (hpair.frobenius_iterate j))

end PairComposition

end PeterfalviProblem
