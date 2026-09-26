/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import PeterfalviProblem.Proof.FieldLayers

/-!
# The case of a Frobenius exponent

This file treats a witness with `p = 3` whose exponent `e` agrees on `U` with a power
`u ↦ u^{3ʲ}` of the Frobenius map. Every witness with `q = 3` is of this kind.

In this case the map `s ↦ s^{3ʲ}` is additive. For each `s` in the Paley set
`T = {s : s and s + 1 are nonzero squares}`, the relations of the family at `s`, `1` and `s + 1`
make `x` commute with `g⁻¹ σ(inl s)^{3ʲ} g` (`commute_conj_of_le_closure_twisted`). The set `T`
generates `𝔽_{3^q}` as an additive group (`Paley.addClosure_paleySet_eq_top`). So `x` commutes with
all of `g⁻¹ σ(P) g`, and in particular with `g⁻¹ x g`. This contradicts `not_commute_conj`.

## Main results

* `le_closure_orbitS`: the conjugates `s = v⁻¹ x v` (`v ∈ σ(U)`) for which `s x` is again such a
  conjugate generate `σ(P)`.
* `false_of_frobenius_exponent`: no witness has a Frobenius exponent.
-/

namespace PeterfalviProblem

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

/-- The `σ(U)`-orbit of the generator `x = σ(1)` of `σ(P₀)`.  Under the identification of `σ(P)`
with `𝔽_{3^q}` this is the set of squares — the set `S` of the partial resolution. -/
def orbitS (data : Witness p q G) : Set G :=
  {s | ∃ v ∈ data.U, s = v⁻¹ * data.s * v}

/-- **The orbit `S` in field terms.**  The `σ(U)`-orbit of `x = σ(1)` is precisely the `σ`-image
of the *norm-one set* of `𝔽_{p^q}`, embedded additively:

`orbitS data = { σ(inl u) : u a norm-one unit }`.

This is the translation promised by `AppC.inr_inv_mul_primeLineGenerator_mul_inr`: conjugation by
`σ(inr u)` multiplies the base point by `u⁻¹`, and inversion permutes the norm-one units.  For
`p = 3` the norm-one set is the set of squares, so the spanning hypothesis of
`false_of_centralizing_of_spanning` becomes exactly Lemma B of
`notes/bg/appC_problem1_partial_resolution.md`. -/
theorem mem_orbitS_iff (data : Witness p q G) {s : G} :
    s ∈ orbitS data ↔ ∃ u : normOneUnits p q,
      s = data.sigma (SemidirectProduct.inl (Multiplicative.ofAdd
        (((u : (GaloisField p q)ˣ) : GaloisField p q)))) := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [← data.sigma_U_eq_U] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    obtain ⟨u, rfl⟩ := hw
    refine ⟨u⁻¹, ?_⟩
    rw [Witness.s, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    rw [inr_inv_mul_primeLineGenerator_mul_inr]
    simp
  · rintro ⟨u, rfl⟩
    refine ⟨data.sigma (SemidirectProduct.inr u⁻¹), ?_, ?_⟩
    · rw [← data.sigma_U_eq_U]
      exact ⟨SemidirectProduct.inr u⁻¹, ⟨u⁻¹, rfl⟩, rfl⟩
    · rw [Witness.s, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      rw [inr_inv_mul_primeLineGenerator_mul_inr]
      simp

/-- The conjugates `v⁻¹ x v` with `v ∈ σ(U)` lie in `σ(P)`. -/
theorem conj_s_mem_P (data : Witness p q G) {v : G} (hv : v ∈ data.U) :
    v⁻¹ * data.s * v ∈ data.P := by
  rw [← data.sigma_U_eq_U] at hv
  obtain ⟨w, ⟨u, rfl⟩, rfl⟩ := hv
  rw [← data.sigma_P_eq_P, Witness.s, ← map_inv, ← map_mul, ← map_mul,
    inr_inv_mul_primeLineGenerator_mul_inr]
  exact ⟨_, ⟨_, rfl⟩, rfl⟩

/-- **Lemma B, transported into `G`.**  For `p = 3` the spanning hypothesis of
`false_of_centralizing_of_spanning` *holds*: the elements `s` of the `σ(U)`-orbit of `x` with
`s · x` again in the orbit generate `σ(P)`.

Through `mem_orbitS_iff` and `mem_normOneUnits_iff_isSquare` the generating set is the image of
the Paley set `T = {a : a and a + 1 are nonzero squares}` of `𝔽_{3^q}`, which generates the
additive group by `PeterfalviProblem.Paley.addClosure_paleySet_eq_top`.  Condition (A) supplies the two
numerical inputs of that lemma: `q ∤ p - 1 = 2` makes `q` odd, hence `|F| = 3^q ≡ 3 (mod 4)` and
`|F| ≥ 27`. -/
theorem le_closure_orbitS (data : Witness p q G) (hp : p = 3) :
    data.P ≤ Subgroup.closure {s | s ∈ orbitS data ∧ s * data.s ∈ orbitS data} := by
  classical
  let : Fintype (GaloisField p q) := Fintype.ofFinite _
  have hq0 : q ≠ 0 := data.q_prime.pos.ne'
  have hcard : Fintype.card (GaloisField p q) = p ^ q := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p q hq0
  have hqodd : Odd q := q_odd data hp
  have hq3 : 3 ≤ q := by
    have h2 : 2 ≤ q := data.q_prime.two_le
    rcases hqodd with ⟨k, hk⟩
    omega
  have : CharP (GaloisField p q) p := by
    rw [← Algebra.charP_iff (ZMod p) (GaloisField p q) p]
    exact ZMod.charP p
  have h3 : ringChar (GaloisField p q) = 3 := by
    rw [ringChar.eq (GaloisField p q) p, hp]
  have h4 : Fintype.card (GaloisField p q) % 4 = 3 := by
    rw [hcard, hp]
    obtain ⟨k, hk⟩ := hqodd
    subst hk
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h9 : 9 < Fintype.card (GaloisField p q) := by
    rw [hcard, hp]
    calc (9 : ℕ) < 3 ^ 3 := by norm_num
      _ ≤ 3 ^ q := Nat.pow_le_pow_right (by norm_num) hq3
  set K : Subgroup G := Subgroup.closure {s | s ∈ orbitS data ∧ s * data.s ∈ orbitS data} with hK
  -- every element of the Paley set maps into the generating set
  have hmemK : ∀ a : GaloisField p q, a ∈ Paley.paleySet (GaloisField p q) →
      fieldHom data (Multiplicative.ofAdd a) ∈ K := by
    rintro a ⟨ha0, hasq, ha10, ha1sq⟩
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · rw [mem_orbitS_iff]
      refine ⟨⟨Units.mk0 a ha0, (mem_normOneUnits_iff_isSquare hp hq0 _).mpr (by simpa using
        hasq)⟩, ?_⟩
      simp [fieldHom]
    · have hmul : fieldHom data (Multiplicative.ofAdd a) * data.s =
          fieldHom data (Multiplicative.ofAdd (a + 1)) := by
        rw [Witness.s, primeLineGenerator, fieldHom]
        simp only [MonoidHom.coe_comp, Function.comp_apply]
        rw [← map_mul data.sigma, ← map_mul SemidirectProduct.inl, ← ofAdd_add]
      rw [hmul, mem_orbitS_iff]
      refine ⟨⟨Units.mk0 (a + 1) ha10, (mem_normOneUnits_iff_isSquare hp hq0 _).mpr (by simpa using
        ha1sq)⟩, ?_⟩
      simp [fieldHom]
  -- the preimage of `K` is an additive subgroup of the field containing the Paley set
  let A : AddSubgroup (GaloisField p q) :=
    { carrier := {a | fieldHom data (Multiplicative.ofAdd a) ∈ K}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, ofAdd_add, map_mul] at *
        exact K.mul_mem ha hb
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, ofAdd_neg, map_inv] at *
        exact K.inv_mem ha }
  have hAtop : A = ⊤ := by
    rw [eq_top_iff, ← Paley.addClosure_paleySet_eq_top (F := GaloisField p q) h3 h4 h9,
      AddSubgroup.closure_le]
    exact hmemK
  intro x hx
  rw [← fieldHom_range data] at hx
  obtain ⟨a, rfl⟩ := hx
  have hmem : Multiplicative.toAdd a ∈ A := hAtop ▸ AddSubgroup.mem_top _
  exact hmem

/-- **Theorem 1, Frobenius-power case.**  If `g` acts on `σ(U)` by an exponent agreeing with a
Frobenius power `u ↦ u^{3ʲ}` on the norm-one units, hypothesis (B) fails.  The transported
Frobenius `s ↦ s^{3ʲ}` is additive on `σ(P)`, so the layered relation family feeds the twisted
engine `commute_conj_of_le_closure_twisted`; the Paley spanning transports along the Frobenius
bijection; and the resulting commutation `[x, x^g] = 1` is fatal (`not_commute_conj`).  This is
the `e ∈ ⟨3⟩` half of Theorem 1 of `notes/bg/appC_problem1_partial_resolution.md` —
`false_of_centralizing` is the specialisation `j = 0`. -/
theorem false_of_frobenius_exponent (data : Witness p q G) (hp : p = 3)
    {e j : ℕ} (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    (hfrob : ∀ u : normOneUnits p q, u ^ e = u ^ 3 ^ j) : False := by
  subst hp
  classical
  -- the transported Frobenius power on `σ(P)`
  set σf : G → G := fun x =>
    if h : ∃ a : Multiplicative (GaloisField 3 q), fieldHom data a = x then
      fieldHom data (Multiplicative.ofAdd (Multiplicative.toAdd (Classical.choose h) ^ 3 ^ j))
    else x with hσfdef
  have hσf_apply : ∀ a : Multiplicative (GaloisField 3 q),
      σf (fieldHom data a)
        = fieldHom data (Multiplicative.ofAdd (Multiplicative.toAdd a ^ 3 ^ j)) := by
    intro a
    have hex : ∃ b, fieldHom data b = fieldHom data a := ⟨a, rfl⟩
    simp only [hσfdef, dite_eq_left hex]
    have hchoose : Classical.choose hex = a :=
      fieldHom_injective data (Classical.choose_spec hex)
    rw [hchoose]
  have hσP : ∀ v ∈ data.P, σf v ∈ data.P := by
    intro v hv
    rw [← fieldHom_range data] at hv ⊢
    obtain ⟨a, rfl⟩ := hv
    rw [hσf_apply]
    exact ⟨_, rfl⟩
  have hσmul : ∀ a ∈ data.P, ∀ b ∈ data.P, σf (a * b) = σf a * σf b := by
    intro x hx y hy
    rw [← fieldHom_range data] at hx hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    have harg : Multiplicative.ofAdd (Multiplicative.toAdd (a * b) ^ 3 ^ j)
        = Multiplicative.ofAdd (Multiplicative.toAdd a ^ 3 ^ j)
          * Multiplicative.ofAdd (Multiplicative.toAdd b ^ 3 ^ j) := by
      rw [← ofAdd_add]
      congr 1
      rw [toAdd_mul, add_pow_char_pow]
    rw [← map_mul, hσf_apply, harg, map_mul, ← hσf_apply, ← hσf_apply]
  -- orbit elements in field coordinates, and the twist as the `e`-power on the orbit
  have hSP : orbitS data ⊆ (data.P : Set G) := by
    rintro s ⟨v, hv, rfl⟩
    exact conj_s_mem_P data hv
  have horbit : ∀ v ∈ data.U, ∃ u : normOneUnits 3 q, v = unitElt data u := by
    intro v hv
    rw [← data.sigma_U_eq_U] at hv
    obtain ⟨w', ⟨u, rfl⟩, rfl⟩ := hv
    exact ⟨u, rfl⟩
  have hval_pow : ∀ u : normOneUnits 3 q,
      (((u⁻¹ : normOneUnits 3 q) : (GaloisField 3 q)ˣ) : GaloisField 3 q) ^ 3 ^ j
        = ((((u ^ e)⁻¹ : normOneUnits 3 q) : (GaloisField 3 q)ˣ) : GaloisField 3 q) := by
    intro u
    have h := hfrob u⁻¹
    have hval := congrArg (fun z : normOneUnits 3 q =>
      ((z : (GaloisField 3 q)ˣ) : GaloisField 3 q)) h
    simp only [inv_pow] at hval ⊢
    exact hval.symm
  have hσf_orbit : ∀ u : normOneUnits 3 q,
      σf ((unitElt data u)⁻¹ * data.s * unitElt data u)
        = (unitElt data u ^ e)⁻¹ * data.s * unitElt data u ^ e := by
    intro u
    rw [conj_s_unitElt data u, hσf_apply, unitElt_pow, conj_s_unitElt data (u ^ e)]
    congr 2
    simp only [toAdd_ofAdd]
    exact hval_pow u
  have hrel : ∀ s' ∈ orbitS data,
      ((conjGen data)⁻¹ * ((conjGen data)⁻¹ * σf (σf s') * conjGen data) * conjGen data) *
        ((conjGen data)⁻¹ * σf s' * conjGen data) * s' = 1 := by
    rintro s' ⟨v, hv, rfl⟩
    obtain ⟨u, rfl⟩ := horbit v hv
    have h1 : σf ((unitElt data u)⁻¹ * data.s * unitElt data u)
        = (unitElt data u ^ e)⁻¹ * data.s * unitElt data u ^ e := hσf_orbit u
    have h2 : σf ((unitElt data u ^ e)⁻¹ * data.s * unitElt data u ^ e)
        = (unitElt data u ^ (e * e))⁻¹ * data.s * unitElt data u ^ (e * e) := by
      have h := hσf_orbit (u ^ e)
      rw [← unitElt_pow, ← pow_mul] at h
      exact h
    rw [h1, h2]
    have hlay := layered_relation_of_exp data rfl hexp hv
    calc ((conjGen data)⁻¹ * ((conjGen data)⁻¹ *
            ((unitElt data u ^ (e * e))⁻¹ * data.s * unitElt data u ^ (e * e)) *
            conjGen data) * conjGen data) *
          ((conjGen data)⁻¹ * ((unitElt data u ^ e)⁻¹ * data.s * unitElt data u ^ e) *
            conjGen data) *
          ((unitElt data u)⁻¹ * data.s * unitElt data u)
        = ((conjGen data)⁻¹ * ((conjGen data)⁻¹ *
            ((unitElt data u ^ (e * e))⁻¹ * data.s * unitElt data u ^ (e * e)) *
            conjGen data) * conjGen data) *
          (((conjGen data)⁻¹ * ((unitElt data u ^ e)⁻¹ * data.s * unitElt data u ^ e) *
            conjGen data) *
          ((unitElt data u)⁻¹ * data.s * unitElt data u)) := by group
      _ = 1 := hlay
  -- the spanning hypothesis transports along the Frobenius bijection
  have hσinv : ∀ x ∈ data.P, σf x⁻¹ = (σf x)⁻¹ := by
    intro x hx
    have h1 : σf x⁻¹ * σf x = 1 := by
      rw [← hσmul x⁻¹ (inv_mem hx) x hx, inv_mul_cancel]
      rw [show (1 : G) = fieldHom data 1 from (map_one _).symm, hσf_apply]
      simp
    exact eq_inv_of_mul_eq_one_left h1
  have hclP : Subgroup.closure {s' | s' ∈ orbitS data ∧ s' * data.s ∈ orbitS data}
      ≤ data.P :=
    (Subgroup.closure_le _).mpr fun s' hs' => hSP hs'.1
  have hfrob_inj : Function.Injective (fun z : GaloisField 3 q => z ^ 3 ^ j) := by
    intro x y hxy
    simp only at hxy
    have h0 : (x - y) ^ 3 ^ j = 0 := by
      rw [sub_pow_char_pow, hxy, sub_self]
    exact sub_eq_zero.mp
      ((pow_eq_zero_iff (by positivity : 0 < 3 ^ j).ne').mp h0)
  have hσf_surj : ∀ v ∈ data.P, ∃ w ∈ data.P, σf w = v := by
    intro v hv
    rw [← fieldHom_range data] at hv
    obtain ⟨a, rfl⟩ := hv
    obtain ⟨t, ht⟩ := Finite.injective_iff_surjective.mp hfrob_inj (Multiplicative.toAdd a)
    refine ⟨fieldHom data (Multiplicative.ofAdd t), ?_, ?_⟩
    · rw [← fieldHom_range data]
      exact ⟨_, rfl⟩
    · rw [hσf_apply]
      have hta : Multiplicative.toAdd (Multiplicative.ofAdd t) ^ 3 ^ j
          = Multiplicative.toAdd a := by
        simpa using ht
      rw [hta]
      simp
  have hspan : data.P ≤ Subgroup.closure
      (σf '' {s' | s' ∈ orbitS data ∧ s' * data.s ∈ orbitS data}) := by
    intro v hv
    obtain ⟨w, hwP, rfl⟩ := hσf_surj v hv
    have hw := le_closure_orbitS data rfl hwP
    refine Subgroup.closure_induction
      (p := fun x _ => σf x ∈ Subgroup.closure
        (σf '' {s' | s' ∈ orbitS data ∧ s' * data.s ∈ orbitS data}))
      (fun x hx => Subgroup.subset_closure ⟨x, hx, rfl⟩) ?_ ?_ ?_ hw
    · have h0 : (0 : GaloisField 3 q) ^ 3 ^ j = 0 :=
        zero_pow (by positivity : (0 : ℕ) < 3 ^ j).ne'
      rw [show (1 : G) = fieldHom data 1 from (map_one _).symm, hσf_apply, toAdd_one, h0,
        ofAdd_zero, map_one]
      exact Subgroup.one_mem _
    · intro x y hxc hyc hx hy
      rw [hσmul x (hclP hxc) y (hclP hyc)]
      exact Subgroup.mul_mem _ hx hy
    · intro x hxc hx
      rw [hσinv x (hclP hxc)]
      exact Subgroup.inv_mem _ hx
  -- feed the engine and close by the fixed-point contradiction
  have ht : data.s ∈ orbitS data := ⟨1, data.U.one_mem, by group⟩
  have hcomm := commute_conj_of_le_closure_twisted (P := data.P) (g := conjGen data)
    (fun a ha b hb => P_mul_comm data ha hb) σf hσmul hσP hSP hrel ht hspan
    data.s data.s_mem_P
  exact not_commute_conj data rfl hcomm

end PeterfalviProblem
