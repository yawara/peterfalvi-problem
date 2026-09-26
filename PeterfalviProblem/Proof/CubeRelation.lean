/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import PeterfalviProblem.Basic.Witness
import PeterfalviProblem.Proof.GroupIdentities

/-!
# The relation `(g x)³ = 1`

Let `data` be a witness of hypothesis (B) with `p = 3`. Write `x = σ(inl 1)` for the generator
of `σ(P₀)` (`Witness.s`), and `g = y x y⁻¹` (`conjGen`). In the notation of hypothesis (B),
`g = x^y`. So `⟨g⟩ = y σ(P₀) y⁻¹` normalizes `σ(U)`, while `⟨x⟩` does not.

The element `c = x⁻¹ g` lies in `Q`, and `Q` is abelian. So `c` commutes with `x⁻¹ c x`, and
`pow_three_mul_eq_pow_three_of_commute` gives `(g x)³ = g³ = 1`. This is the only relation that
the rest of the proof takes from hypothesis (B).

## Main results

* `conj_mul_pow_three_eq_one`: `(g x)³ = 1`.
* `not_commute_conj`: `x` does not commute with `g⁻¹ x g`. Otherwise `c = x⁻¹ g` would satisfy
  `c³ = 1`. Then `c = 1`, because `|Q|` is prime to `3`, and so `g = x` would normalize `σ(U)`.
  Every branch of the proof ends with this contradiction.
* `q_odd`: for `p = 3`, condition (A) makes `q` odd.
* `fieldHom`: the injective homomorphism `a ↦ σ(inl a)` from the additive group of `𝔽_{p^q}`
  onto `σ(P)`.
-/

namespace PeterfalviProblem

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

/-- `x⁻¹ z x ∈ Q` for `z ∈ Q`, because `σ(P₀)` normalizes `Q`. -/
theorem conj_mem_Q (data : Witness p q G) (z : G) (hz : z ∈ data.Q) :
    data.s⁻¹ * z * data.s ∈ data.Q :=
  (Subgroup.mem_normalizer_iff''.mp (data.P0_normalizes_Q data.s_mem_P0) z).mp hz

/-- `c = x⁻¹ (y x y⁻¹)` lies in `Q`: it is the product of `x⁻¹ y x ∈ Q` and `y⁻¹ ∈ Q`. -/
theorem inv_mul_conj_mem_Q (data : Witness p q G) :
    data.s⁻¹ * MulAut.conj data.y data.s ∈ data.Q := by
  have h1 : data.s⁻¹ * data.y * data.s ∈ data.Q := conj_mem_Q data data.y data.y_mem_Q
  have h2 : data.s⁻¹ * MulAut.conj data.y data.s
      = (data.s⁻¹ * data.y * data.s) * data.y⁻¹ := by
    simp only [MulAut.conj_apply]
    group
  rw [h2]
  exact data.Q.mul_mem h1 (data.Q.inv_mem data.y_mem_Q)

/-- `x³ = 1` when `p = 3`. -/
theorem s_pow_three (data : Witness p q G) (hp : p = 3) : data.s ^ 3 = 1 := by
  subst hp
  rw [Witness.s, ← map_pow, primeLineGenerator_pow_p, map_one]

/-- **The relation `(g x)³ = 1`**, for `p = 3` and `g = y x y⁻¹`.

Both `g` and `x` have order three, and the relation says that their product has order dividing
three. This is the only relation that the proof takes from hypothesis (B).

The proof applies `pow_three_mul_pow_three_eq_one` to `c = x⁻¹ g`. The element `c` lies in `Q`,
and so does `x⁻¹ c x`. Since `Q` is abelian, they commute. -/
theorem conj_mul_pow_three_eq_one (data : Witness p q G) (hp : p = 3) :
    (MulAut.conj data.y data.s * data.s) ^ 3 = 1 := by
  subst hp
  have hx3 : data.s ^ 3 = 1 := s_pow_three data rfl
  have hcQ := inv_mul_conj_mem_Q data
  have hcxQ : data.s⁻¹ * (data.s⁻¹ * MulAut.conj data.y data.s) * data.s ∈ data.Q :=
    conj_mem_Q data _ hcQ
  have hcomm : Commute (data.s⁻¹ * MulAut.conj data.y data.s)
      (data.s⁻¹ * (data.s⁻¹ * MulAut.conj data.y data.s) * data.s) :=
    data.Q_mul_comm hcQ hcxQ
  have hxc : data.s * (data.s⁻¹ * MulAut.conj data.y data.s) = MulAut.conj data.y data.s := by
    group
  have hg3 : (data.s * (data.s⁻¹ * MulAut.conj data.y data.s)) ^ 3 = 1 := by
    rw [hxc, ← map_pow, hx3, map_one]
  have key := pow_three_mul_pow_three_eq_one hx3 hcomm hg3
  rwa [hxc] at key

/-- The element `g = y x y⁻¹`. It generates `y σ(P₀) y⁻¹`, which normalizes `σ(U)`. In the
notation of hypothesis (B), `g = x^y`. -/
noncomputable def conjGen (data : Witness p q G) : G := MulAut.conj data.y data.s

@[simp]
theorem conjGen_def (data : Witness p q G) :
    conjGen data = MulAut.conj data.y data.s := rfl

/-- `g³ = 1` when `p = 3`, because `x³ = 1`. -/
theorem conjGen_pow_three (data : Witness p q G) (hp : p = 3) :
    conjGen data ^ 3 = 1 := by
  rw [conjGen_def, ← map_pow, s_pow_three data hp, map_one]

/-- **The final contradiction.** For `p = 3`, the element `x` does not commute with `g⁻¹ x g`.

Suppose it did. By `inv_mul_pow_three_eq_one_of_commute_conj` and `(g x)³ = 1`, the element
`c = x⁻¹ g` satisfies `c³ = 1`. But `c ∈ Q` and `|Q|` is prime to `3`, so `c = 1` and `g = x`.
This is impossible: `g` normalizes `σ(U)` and `x` does not (`Witness.s_not_normalizes_U`). -/
theorem not_commute_conj (data : Witness p q G) (hp : p = 3) :
    ¬ Commute data.s ((MulAut.conj data.y data.s)⁻¹ * data.s * MulAut.conj data.y data.s) := by
  intro hcomm
  subst hp
  have hx3 : data.s ^ 3 = 1 := s_pow_three data rfl
  have hg3 : (MulAut.conj data.y data.s) ^ 3 = 1 := by
    rw [← map_pow, hx3, map_one]
  have hgx : (MulAut.conj data.y data.s * data.s) ^ 3 = 1 :=
    conj_mul_pow_three_eq_one data rfl
  -- `c = x⁻¹g` has order dividing three and lies in the `3′`-group `Q`, so it is trivial.
  have hc3 : (data.s⁻¹ * MulAut.conj data.y data.s) ^ 3 = 1 :=
    inv_mul_pow_three_eq_one_of_commute_conj hg3 hgx hcomm.eq
  have hc1 : data.s⁻¹ * MulAut.conj data.y data.s = 1 :=
    data.eq_one_of_mem_Q_of_pow_p_eq_one (inv_mul_conj_mem_Q data) hc3
  -- Hence `g = x`, but `⟨g⟩` normalizes `σ(U)` and `x` does not.
  have hgx' : MulAut.conj data.y data.s = data.s := by
    have := congrArg (fun z => data.s * z) hc1
    simpa using this
  refine data.s_not_normalizes_U ?_
  have hmem : MulAut.conj data.y data.s ∈ Subgroup.normalizer (data.U : Set G) := by
    refine data.P0_conj_y_normalizes_U ?_
    exact ⟨data.s, data.s_mem_P0, rfl⟩
  rwa [hgx'] at hmem

/-- For `p = 3`, condition (A) says `q ∤ 2`, so the prime `q` is odd. -/
theorem q_odd (data : Witness p q G) (hp : p = 3) : Odd q := by
  subst hp
  exact data.q_prime.odd_of_ne_two fun h => data.q_not_dvd (by subst h; decide)

/-- `σ(P)` is abelian. -/
theorem P_mul_comm (data : Witness p q G) {a b : G} (ha : a ∈ data.P)
    (hb : b ∈ data.P) : a * b = b * a := by
  have : IsMulCommutative (normOneFrobeniusKernel p q) := by
    unfold normOneFrobeniusKernel
    infer_instance
  rw [← data.sigma_P_eq_P] at ha hb
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  rw [← map_mul, ← map_mul]
  congr 1
  exact setLike_mul_comm (s := normOneFrobeniusKernel p q) ha' hb'

/-- The homomorphism `a ↦ σ(inl a)` from the additive group of `𝔽_{p^q}` (written
multiplicatively) to `G`. It is injective, with image `σ(P)`. -/
noncomputable def fieldHom (data : Witness p q G) :
    Multiplicative (GaloisField p q) →* G :=
  data.sigma.comp SemidirectProduct.inl

theorem fieldHom_injective (data : Witness p q G) :
    Function.Injective (fieldHom data) :=
  data.sigma_injective.comp SemidirectProduct.inl_injective

theorem fieldHom_range (data : Witness p q G) :
    (fieldHom data).range = data.P := by
  rw [← data.sigma_P_eq_P, normOneFrobeniusKernel, fieldHom, MonoidHom.range_comp]

end PeterfalviProblem
