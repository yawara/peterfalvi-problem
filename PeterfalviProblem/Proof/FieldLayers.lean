/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import PeterfalviProblem.Proof.CubeRelation

/-!
# The three layers

Let `data` be a witness with `p = 3`, and let `g = conjGen data`. Suppose that `g` acts on
`σ(U)` by a power map, that is, `g w = wᵉ g` for all `w ∈ σ(U)`. (`Exponent.lean` shows that such
an `e` exists.)

The three layers are the injective homomorphisms `layerFieldHom data i` for `i = 0, 1, 2`. They
send `t ∈ 𝔽_{3^q}` to `g⁻ⁱ σ(inl t) gⁱ`. We write them `a`, `b` and `d`. Conjugating the relation
`(g x)³ = 1` by the elements of `σ(U)` gives the relation family

`d(u^{e²}) · b(uᵉ) · a(u) = 1` for every `u ∈ U` (`layered_relation_field`).

## Main results

* `layered_relation_field`: the relation family.
* `normOneUnits_pow_cube`: `u^{e³} = u` for `u ∈ U`, because `g³ = 1`.
* `layerFieldHom_two_eq`: `d(r) = a(-rᵉ) · b(-r^{e²})` for `r ∈ U`.
* `layerFieldHom_two_factor`: for norm-one `p₀ = p₁ + 1` and `z`,
  `d(z) = a(-p₀ᵉ zᵉ) · b(K z^{e²}) · a(p₁ᵉ zᵉ)` with `K = p₁^{e²} - p₀^{e²}`.
* `layerFieldHom_one_conj`: if two such pairs give the same value of `p₀ᵉ - p₁ᵉ`, then
  conjugation by an element of the layer `a` maps one element of the layer `b` to another.
-/

namespace PeterfalviProblem

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

/-- **The twisted relation family.**  Suppose `g = x^y` normalizes `σ(U)` with exponent `e`, i.e.
`g w = wᵉ g` for `w ∈ σ(U)` (the general case `e ≠ 1`).  Conjugating `(g x)³ = 1` by `v ∈ σ(U)`
and pushing the conjugation through the layers with `conj_layer_of_exp` gives

`(x^{v^{e²}})^{g²} · (x^{v^e})^g · x^v = 1`.

This is the relation `R(s)` of `notes/bg/appC_problem1_partial_resolution.md` in its layered form:
the three layers are based at `v^{e²}`, `v^e` and `v`, which under the identification of `σ(P)`
with `𝔽_{3^q}` are the field elements `s^{e²}`, `s^e` and `s`.  Feeding this family to
`commutator_eq_top_of_relations` is what makes `N` perfect when the relation lattice spans. -/
theorem layered_relation_of_exp (data : Witness p q G) (hp : p = 3) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data) {v : G} (hv : v ∈ data.U) :
    (conjGen data)⁻¹ * ((conjGen data)⁻¹ * ((v ^ (e * e))⁻¹ * data.s * v ^ (e * e)) *
        conjGen data) * conjGen data *
      (((conjGen data)⁻¹ * ((v ^ e)⁻¹ * data.s * v ^ e) * conjGen data) *
        (v⁻¹ * data.s * v)) = 1 := by
  have hx3 : data.s ^ 3 = 1 := by
    subst hp
    rw [Witness.s, ← map_pow, primeLineGenerator_pow_p, map_one]
  have hg3 : (conjGen data) ^ 3 = 1 := by
    rw [conjGen_def, ← map_pow, hx3, map_one]
  -- The layered form of `(g x)³ = 1`.
  have hlayer : (conjGen data)⁻¹ * ((conjGen data)⁻¹ * data.s * conjGen data) * conjGen data *
      (((conjGen data)⁻¹ * data.s * conjGen data) * data.s) = 1 :=
    (pow_three_eq_conj_mul hg3 data.s).symm.trans (conj_mul_pow_three_eq_one data hp)
  -- Conjugate by `v` and push the conjugation through the three layers.
  have hconj := congrArg (fun z => v⁻¹ * z * v) hlayer
  simp only [mul_one, inv_mul_cancel] at hconj
  have hdist : v⁻¹ * ((conjGen data)⁻¹ * ((conjGen data)⁻¹ * data.s * conjGen data) *
        conjGen data * (((conjGen data)⁻¹ * data.s * conjGen data) * data.s)) * v
      = (v⁻¹ * ((conjGen data)⁻¹ * ((conjGen data)⁻¹ * data.s * conjGen data) * conjGen data) * v)
        * ((v⁻¹ * ((conjGen data)⁻¹ * data.s * conjGen data) * v) * (v⁻¹ * data.s * v)) := by
    group
  rw [hdist, conj_layer_two_of_exp (hexp v hv) (hexp (v ^ e) (data.U.pow_mem hv e)) data.s,
    conj_layer_of_exp (hexp v hv) data.s] at hconj
  exact hconj

/-- **The exponent has order three on `σ(U)`.**  Conjugating three times by `g` is conjugating by
`g³ = 1`, so `w^{e³} = w` for every `w ∈ σ(U)`. -/
theorem pow_three_exp_eq_self (data : Witness p q G) (hp : p = 3) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data) {z : G} (hz : z ∈ data.U) :
    z ^ (e * e * e) = z := by
  have hx3 : data.s ^ 3 = 1 := by
    subst hp
    rw [Witness.s, ← map_pow, primeLineGenerator_pow_p, map_one]
  have hg3 : conjGen data ^ 3 = 1 := by rw [conjGen_def, ← map_pow, hx3, map_one]
  have step : ∀ w ∈ data.U, conjGen data * w * (conjGen data)⁻¹ = w ^ e := by
    intro w hw
    rw [hexp w hw]
    group
  have e1 : conjGen data * z * (conjGen data)⁻¹ = z ^ e := step z hz
  have e2 : conjGen data * z ^ e * (conjGen data)⁻¹ = z ^ (e * e) := by
    rw [step _ (data.U.pow_mem hz e), ← pow_mul]
  have e3 : conjGen data * z ^ (e * e) * (conjGen data)⁻¹ = z ^ (e * e * e) := by
    rw [step _ (data.U.pow_mem hz (e * e)), ← pow_mul]
  calc z ^ (e * e * e)
      = conjGen data * (conjGen data * (conjGen data * z * (conjGen data)⁻¹) *
          (conjGen data)⁻¹) * (conjGen data)⁻¹ := by rw [e1, e2, e3]
    _ = conjGen data ^ 3 * z * (conjGen data ^ 3)⁻¹ := by
        rw [show conjGen data ^ 3 = conjGen data * conjGen data * conjGen data by
          rw [pow_succ, pow_succ, pow_one]]
        group
    _ = z := by rw [hg3]; group

/-! ### The relation family in field coordinates

The collision-span computation runs entirely in `𝔽_{3^q}`, so the relation family has to be read
through the identification of `σ(P)` with the field.  `layerFieldHom data i` is the `i`-th layer
`t ↦ (gⁱ)⁻¹ σ(inl t) gⁱ`, and `layered_relation_field` is the relation `d(t^{E²}) b(t^E) a(t) = 1`
of `notes/bg/appC_problem1_partial_resolution.md`. -/

/-- The field element underlying a norm-one unit.  (Notation for the doubly-coerced
`((u : (GaloisField p q)ˣ) : GaloisField p q)`, which the relation family is full of.) -/
def normOneVal (u : normOneUnits p q) : GaloisField p q :=
  ((u : (GaloisField p q)ˣ) : GaloisField p q)

@[simp]
theorem normOneVal_mul (u v : normOneUnits p q) :
    normOneVal (u * v) = normOneVal u * normOneVal v := rfl

@[simp]
theorem normOneVal_inv (u : normOneUnits p q) :
    normOneVal u⁻¹ = (normOneVal u)⁻¹ := by
  simp [normOneVal]

@[simp]
theorem normOneVal_pow (u : normOneUnits p q) (k : ℕ) :
    normOneVal (u ^ k) = normOneVal u ^ k := by
  simp only [normOneVal, SubgroupClass.coe_pow, Units.val_pow_eq_pow_val]

/-- The element of `σ(U)` attached to a norm-one unit. -/
noncomputable def unitElt (data : Witness p q G) (u : normOneUnits p q) : G :=
  data.sigma (SemidirectProduct.inr u)

theorem unitElt_mem_U (data : Witness p q G) (u : normOneUnits p q) :
    unitElt data u ∈ data.U := by
  rw [← data.sigma_U_eq_U]
  exact ⟨SemidirectProduct.inr u, ⟨u, rfl⟩, rfl⟩

theorem unitElt_pow (data : Witness p q G) (u : normOneUnits p q) (k : ℕ) :
    unitElt data u ^ k = unitElt data (u ^ k) := by
  rw [unitElt, unitElt, ← map_pow, ← map_pow]

/-- **Conjugating `x = σ(1)` by a norm-one unit is multiplication in the field.** -/
theorem conj_s_unitElt (data : Witness p q G) (u : normOneUnits p q) :
    (unitElt data u)⁻¹ * data.s * unitElt data u =
      fieldHom data (Multiplicative.ofAdd
        (((u⁻¹ : normOneUnits p q) : (GaloisField p q)ˣ) : GaloisField p q)) := by
  have hval := inr_inv_mul_primeLineGenerator_mul_inr p q u
  rw [unitElt, Witness.s, ← map_inv data.sigma, ← map_mul data.sigma,
    ← map_mul data.sigma, hval]
  rfl

/-- The `i`-th layer of `σ(P)`, in field coordinates. -/
noncomputable def layerFieldHom (data : Witness p q G) (i : ℕ) :
    Multiplicative (GaloisField p q) →* G :=
  (MulAut.conj (((conjGen data) ^ i)⁻¹) : G →* G).comp (fieldHom data)

@[simp]
theorem layerFieldHom_apply (data : Witness p q G) (i : ℕ)
    (t : Multiplicative (GaloisField p q)) :
    layerFieldHom data i t =
      ((conjGen data) ^ i)⁻¹ * fieldHom data t * (conjGen data) ^ i := by
  change ((conjGen data) ^ i)⁻¹ * fieldHom data t * (((conjGen data) ^ i)⁻¹)⁻¹ = _
  rw [inv_inv]

/-- Each layer is a faithful copy of `(𝔽_{3^q}, +)`: `fieldHom` is injective because `σ` is, and
conjugation is a bijection. -/
theorem layerFieldHom_injective (data : Witness p q G) (i : ℕ) :
    Function.Injective (layerFieldHom data i) := by
  intro s t hst
  simp only [layerFieldHom_apply] at hst
  exact fieldHom_injective data (mul_left_cancel (mul_right_cancel hst))

/-- **The relation family, in field coordinates.**  For every norm-one `u`,

`d(u^{e²}) · b(u^e) · a(u) = 1`,

where `a`, `b`, `d` are the three layers.  This is the shape in which the collision-span
computation of `notes/bg/appC_problem1_partial_resolution.md` uses hypothesis (B). -/
theorem layered_relation_field (data : Witness p q G) (hp : p = 3) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    (u : normOneUnits p q) :
    layerFieldHom data 2 (Multiplicative.ofAdd
        (((u ^ (e * e) : normOneUnits p q) : (GaloisField p q)ˣ) : GaloisField p q)) *
      layerFieldHom data 1 (Multiplicative.ofAdd
        (((u ^ e : normOneUnits p q) : (GaloisField p q)ˣ) : GaloisField p q)) *
      layerFieldHom data 0 (Multiplicative.ofAdd
        (((u : normOneUnits p q) : (GaloisField p q)ˣ) : GaloisField p q)) = 1 := by
  have hrel := layered_relation_of_exp data hp hexp (unitElt_mem_U data u⁻¹)
  have h0 := conj_s_unitElt data u⁻¹
  have h1 := conj_s_unitElt data (u⁻¹ ^ e)
  have h2 := conj_s_unitElt data (u⁻¹ ^ (e * e))
  rw [← unitElt_pow] at h1 h2
  rw [h0, h1, h2] at hrel
  simp only [inv_pow, inv_inv] at hrel
  have hshape : ∀ A B C : G,
      (((conjGen data) ^ 2)⁻¹ * A * (conjGen data) ^ 2) *
          (((conjGen data) ^ 1)⁻¹ * B * (conjGen data) ^ 1) *
          (((conjGen data) ^ 0)⁻¹ * C * (conjGen data) ^ 0)
        = (conjGen data)⁻¹ * ((conjGen data)⁻¹ * A * conjGen data) * conjGen data *
            (((conjGen data)⁻¹ * B * conjGen data) * C) := by
    intro A B C
    rw [show (conjGen data) ^ 2 = conjGen data * conjGen data by rw [pow_succ, pow_one],
      pow_one, pow_zero]
    group
  simp only [layerFieldHom_apply]
  rw [hshape]
  exact hrel

/-- **The exponent cubes to the identity on the norm-one units.**  Read off the `G`-level
statement `pow_three_exp_eq_self` through the injectivity of `σ`. -/
theorem normOneUnits_pow_cube (data : Witness p q G) (hp : p = 3) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    (u : normOneUnits p q) : u ^ (e * e * e) = u := by
  refine SemidirectProduct.inr_injective (data.sigma_injective ?_)
  rw [map_pow, map_pow]
  exact pow_three_exp_eq_self data hp hexp (unitElt_mem_U data u)

/-- **Relation (1) of the collision-span obstruction.**  Substituting `t = r^e` into the relation
family and using `e³ = 1` on the norm-one units,

`d(r) = a(-r^e) · b(-r^{e²})`,

i.e. the third layer at `r` is a product of one element of the first layer and one of the second.
(`notes/bg/appC_problem1_partial_resolution.md`, step 1 of the criterion.) -/
theorem layerFieldHom_two_eq (data : Witness p q G) (hp : p = 3) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    (r : normOneUnits p q) :
    layerFieldHom data 2 (Multiplicative.ofAdd (normOneVal r))
      = (layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal (r ^ e))))⁻¹ *
        (layerFieldHom data 1 (Multiplicative.ofAdd (normOneVal (r ^ (e * e)))))⁻¹ := by
  have hrel := layered_relation_field data hp hexp (r ^ e)
  have h1 : (r ^ e) ^ (e * e) = r := by
    rw [← pow_mul, ← mul_assoc]
    exact normOneUnits_pow_cube data hp hexp r
  have h2 : (r ^ e) ^ e = r ^ (e * e) := by rw [← pow_mul]
  rw [h1, h2] at hrel
  have hone : layerFieldHom data 2 (Multiplicative.ofAdd (normOneVal r)) *
      (layerFieldHom data 1 (Multiplicative.ofAdd (normOneVal (r ^ (e * e)))) *
        layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal (r ^ e)))) = 1 := by
    rw [← mul_assoc]
    exact hrel
  rw [eq_inv_iff_mul_eq_one.mpr hone, mul_inv_rev]

/-- **Relation (2) of the collision-span obstruction.**  For `p` in the Paley set
`T = {p ∈ U : p - 1 ∈ U}` (given here as a pair `p₀ = p`, `p₁ = p - 1` of norm-one units) and any
norm-one `z`, splitting `z = p z - (p-1) z` and applying relation (1) twice gives the exact
non-commutative factorisation

`d(z) = a(-p^e z^e) · b(K(p) z^{e²}) · a((p-1)^e z^e)`,  `K(p) = (p-1)^{e²} - p^{e²}`.

The two second-layer factors merge because the layer is the image of a homomorphism from an
abelian group.  This is the identity whose *collisions* drive the whole obstruction. -/
theorem layerFieldHom_two_factor (data : Witness p q G) (hp : p = 3) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    (p₀ p₁ z : normOneUnits p q) (hpp : normOneVal p₀ = normOneVal p₁ + 1) :
    layerFieldHom data 2 (Multiplicative.ofAdd (normOneVal z))
      = (layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal (p₀ ^ e * z ^ e))))⁻¹ *
        layerFieldHom data 1 (Multiplicative.ofAdd
          ((normOneVal (p₁ ^ (e * e)) - normOneVal (p₀ ^ (e * e))) * normOneVal (z ^ (e * e)))) *
        layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal (p₁ ^ e * z ^ e))) := by
  -- split `z = p₀ z - p₁ z` in the third layer
  have hsplit : normOneVal z = normOneVal (p₀ * z) + -normOneVal (p₁ * z) := by
    simp only [normOneVal_mul, hpp]
    ring
  have hd : layerFieldHom data 2 (Multiplicative.ofAdd (normOneVal z))
      = layerFieldHom data 2 (Multiplicative.ofAdd (normOneVal (p₀ * z))) *
        (layerFieldHom data 2 (Multiplicative.ofAdd (normOneVal (p₁ * z))))⁻¹ := by
    rw [← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add, hsplit]
  rw [hd, layerFieldHom_two_eq data hp hexp (p₀ * z), layerFieldHom_two_eq data hp hexp (p₁ * z)]
  -- merge the two second-layer factors
  simp only [mul_inv_rev, inv_inv, mul_pow, normOneVal_mul, normOneVal_pow]
  have hb : (layerFieldHom data 1 (Multiplicative.ofAdd
        (normOneVal p₀ ^ (e * e) * normOneVal z ^ (e * e))))⁻¹ *
      layerFieldHom data 1 (Multiplicative.ofAdd
        (normOneVal p₁ ^ (e * e) * normOneVal z ^ (e * e)))
      = layerFieldHom data 1 (Multiplicative.ofAdd
        ((normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e)) * normOneVal z ^ (e * e))) := by
    rw [← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add]
    congr 2
    ring
  simp only [mul_assoc]
  congr 1
  rw [← mul_assoc, hb]

/-- **Relation (3) of the collision-span obstruction: a collision conjugates one second-layer
element into another.**  If `p` and `r` both lie in the Paley set and *collide*, i.e.

`p^e - (p-1)^e = r^e - (r-1)^e`,

then, with `δ = r^e - p^e`, equating the two factorisations of `d(z)` gives

`b(K(r) z^{e²}) = a(δ z^e) · b(K(p) z^{e²}) · a(-δ z^e)`.

Conjugation by a *first*-layer element therefore maps a second-layer element back into the second
layer — the whole point of the obstruction. -/
theorem layerFieldHom_one_conj (data : Witness p q G) (hp : p = 3) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    (p₀ p₁ r₀ r₁ z : normOneUnits p q)
    (hpp : normOneVal p₀ = normOneVal p₁ + 1) (hrr : normOneVal r₀ = normOneVal r₁ + 1)
    (hcoll : normOneVal p₀ ^ e - normOneVal p₁ ^ e = normOneVal r₀ ^ e - normOneVal r₁ ^ e) :
    layerFieldHom data 1 (Multiplicative.ofAdd
        ((normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e)) * normOneVal z ^ (e * e)))
      = layerFieldHom data 0 (Multiplicative.ofAdd
            ((normOneVal r₀ ^ e - normOneVal p₀ ^ e) * normOneVal z ^ e)) *
        layerFieldHom data 1 (Multiplicative.ofAdd
            ((normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e)) * normOneVal z ^ (e * e))) *
        layerFieldHom data 0 (Multiplicative.ofAdd
            (-((normOneVal r₀ ^ e - normOneVal p₀ ^ e) * normOneVal z ^ e))) := by
  have hP := layerFieldHom_two_factor data hp hexp p₀ p₁ z hpp
  have hR := layerFieldHom_two_factor data hp hexp r₀ r₁ z hrr
  rw [hP] at hR
  simp only [normOneVal_mul, normOneVal_pow] at hR
  -- solve for the second-layer factor of `r`
  have hsolve : layerFieldHom data 1 (Multiplicative.ofAdd
        ((normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e)) * normOneVal z ^ (e * e)))
      = layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal r₀ ^ e * normOneVal z ^ e)) *
        ((layerFieldHom data 0 (Multiplicative.ofAdd
              (normOneVal p₀ ^ e * normOneVal z ^ e)))⁻¹ *
          layerFieldHom data 1 (Multiplicative.ofAdd
              ((normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e)) * normOneVal z ^ (e * e))) *
          layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal p₁ ^ e * normOneVal z ^ e))) *
        (layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal r₁ ^ e * normOneVal z ^ e)))⁻¹ := by
    rw [hR]
    simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  -- the two first-layer differences are `δ z^e` and `-δ z^e`
  have hleft : layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal r₀ ^ e * normOneVal z ^ e)) *
      (layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal p₀ ^ e * normOneVal z ^ e)))⁻¹
      = layerFieldHom data 0 (Multiplicative.ofAdd
          ((normOneVal r₀ ^ e - normOneVal p₀ ^ e) * normOneVal z ^ e)) := by
    rw [← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add]
    congr 2
    ring
  have hright : layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal p₁ ^ e * normOneVal z ^ e)) *
      (layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal r₁ ^ e * normOneVal z ^ e)))⁻¹
      = layerFieldHom data 0 (Multiplicative.ofAdd
          (-((normOneVal r₀ ^ e - normOneVal p₀ ^ e) * normOneVal z ^ e))) := by
    rw [← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add]
    congr 2
    linear_combination (-(normOneVal z ^ e)) * hcoll
  rw [hsolve, ← hleft, ← hright]
  simp only [mul_assoc]

end PeterfalviProblem
