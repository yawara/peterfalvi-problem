# Péterfalvi's Problem for p = 3

A Lean 4 proof that no group satisfies hypothesis (B) of Proposition 9 of Glauberman–Norton when
`p = 3`. This answers a question of Péterfalvi that has been open in print since 1993.

- Author and maintainer: Yawara Ishida.
- License: [Apache-2.0](LICENSE).
- 日本語版: [README.ja.md](README.ja.md).

## The problem

G. Glauberman and S. P. Norton, *On a combinatorial problem associated with the odd order
theorem*, Proc. Amer. Math. Soc. **119** (1993), 1089–1094, end with this question
([doi:10.1090/S0002-9939-1993-1160299-X](https://doi.org/10.1090/S0002-9939-1993-1160299-X)):

> **Problem** (Péterfalvi). Can the hypothesis of Proposition 9 be satisfied for `p = 3`?

The same question is Problem 1 in Appendix C of H. Bender and G. Glauberman, *Local Analysis for
the Odd Order Theorem* (London Math. Soc. Lecture Note Series 188, 1994), p. 152: "Can `p = 3` in
Theorem C?"

The hypothesis comes from T. Peterfalvi's simplification of the last chapter of the Feit–Thompson
proof (C. R. Acad. Sci. Paris Sér. I Math. **299** (1984), 531–534). Let `p` and `q` be primes, and
let `F` be the field with `p^q` elements.

- `P` is the additive group of `F`.
- `U` is the group of elements of `F` of norm one over the prime field `𝔽_p`. It acts on `P` by
  multiplication.
- `H = P ⋊ U` is the semidirect product, and `P₀` is the image in `H` of the additive group of
  `𝔽_p`.

Proposition 9 assumes two things.

- **(A)** `q` does not divide `p - 1`.
- **(B)** There are a group `G`, an injective homomorphism `σ : H → G`, a finite abelian subgroup
  `Q` of `G` whose order is prime to `p`, and an element `y ∈ Q`, such that `σ(P₀)` normalizes `Q`
  and `σ(P₀)^y = y⁻¹ σ(P₀) y` normalizes `σ(U)`.

For `p = 2` the hypothesis holds: Glauberman–Norton give `SL(2, 2^q)` and the Suzuki groups as
examples, due to Péterfalvi. For `p ≥ 5` it fails, by Propositions 7 and 9 of the same paper. The
case `p = 3` was left open. Remark (IV) in Appendix C of Bender–Glauberman says the same: "It is
not yet known whether `p` may be equal to 3."

## The result

The answer is **no**. The repository proves two theorems. Both depend only on the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

| Statement | Lean |
| --- | --- |
| For every prime `q` with `q ∤ 3 - 1`, no group satisfies hypothesis (B) for `p = 3`. | [`PeterfalviProblem.not_hypothesisB_three`](PeterfalviProblem/Main.lean) |
| For every `q ≥ 1`, the group `SL(2, 2^q)` satisfies hypothesis (B) for `p = 2`. | [`PeterfalviProblem.hypothesisB_two`](PeterfalviProblem/Main.lean) |

```lean
theorem not_hypothesisB_three (q : ℕ) (hq : q.Prime) (hA : ¬ q ∣ 3 - 1) (G : Type*) [Group G] :
    ¬ HypothesisB 3 q G

theorem hypothesisB_two (q : ℕ) (hq : q ≠ 0) :
    HypothesisB 2 q (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 q))
```

The first theorem is the answer to the problem. Its hypotheses are exactly those of
Proposition 9 with `p = 3`: `q` is prime, and condition (A) holds. For a prime `q`, condition (A)
with `p = 3` says `q ≠ 2`. The group `G` can be any group; it need not be finite.

The second theorem is Péterfalvi's example for `p = 2` (Example 10 of Glauberman–Norton,
Remark (II) in Appendix C of Bender–Glauberman). It shows that the definition of hypothesis (B)
is not empty, so the first theorem is not true for a trivial reason. It uses the data of the
paper: `σ(P) = {[[1, a], [0, 1]]}`, `σ(U) = {[[a, 0], [0, a⁻¹]]}`, `σ(P₀) = ⟨[[1, 1], [0, 1]]⟩`,
`y = [[0, 1], [1, 1]]` and `Q = ⟨y⟩`.

The definitions are in [`PeterfalviProblem/Statement.lean`](PeterfalviProblem/Statement.lean):

| Object | Lean | Definition |
| --- | --- | --- |
| `P` | `additiveFieldGroup p q` | `Multiplicative (GaloisField p q)`: the additive group of `F`, written multiplicatively |
| `U` | `normOneUnits p q` | the kernel of the norm map `Fˣ → 𝔽_pˣ` |
| `H = P ⋊ U` | `normOneFrobeniusGroup p q` | Mathlib's semidirect product, for the action `u · s = u s` |
| `U ≤ H` | `normOneFrobeniusComplement p q` | the image of `U` in `H` |
| `P₀ ≤ H` | `primeLine p q` | the image in `H` of the image of `𝔽_p → F` |
| (B) | `HypothesisB p q G` | the proposition described above |

## How the statement follows the sources

The statement follows Proposition 9 of Glauberman–Norton. These are the places where a choice
was made.

1. **The group `U`.** It is the kernel of the norm map. Glauberman–Norton define `U` as the set of
   `(p - 1)`-th powers of `Fˣ`, and they note that these are the elements of norm one.
   Bender–Glauberman define `U` as the elements of norm one.
2. **`σ(U)` in the last condition.** The papers say that `σ(P₀)^y` normalizes `U`. Since
   `σ(P₀)^y` lies in `G`, this means `σ(U)`: Remark (VI) in Appendix C of Bender–Glauberman
   identifies `H` with its image in `G`.
3. **Conjugation.** `σ(P₀)^y` means `y⁻¹ σ(P₀) y`. In Lean it is the image of `P₀` under
   `h ↦ y⁻¹ σ(h) y`.
4. **"Finite abelian `p′`-subgroup."** This is a finite abelian subgroup `Q` with `p ∤ |Q|`.
5. **Condition (A).** We use the form `q ∤ p - 1` of Proposition 9. Bender–Glauberman state (A) as
   `gcd((p^q - 1)/(p - 1), p - 1) = 1`. The two forms are equivalent (Lemma 8 of
   Glauberman–Norton); the lemma `coprime_iff_not_dvd` proves this, but the main theorem does not
   need it.
6. **The group `G`.** It is any group. Nothing in the sources requires `G` to be finite, and the
   negative answer holds without that assumption.
7. **The example for `p = 2`.** It is proved for every `q ≥ 1`, not only for primes `q`.

The definitions need only that `p` is prime. The theorems add the conditions on `q`. There is no
degenerate case that makes the first theorem true for a trivial reason: the second theorem shows
that the same definition is satisfied for `p = 2`. The pair `p = 3`, `q = 2` is excluded by
condition (A), as in the sources; the theorem says nothing about it.

## How the proof works

The proof is new. It uses no classification of groups and no character sums; it is elementary
but long. Fix a group `G` and data as in hypothesis (B), for `p = 3`.

1. **One relation.** Let `x` be the generator `σ(inl 1)` of `σ(P₀)`, and let `g = y⁻¹ x y`. The
   element `c = x⁻¹ g` lies in `Q`, which is abelian. A short computation in `G` then gives
   `(g x)³ = 1` ([`CubeRelation.lean`](PeterfalviProblem/Proof/CubeRelation.lean)). This is the
   only relation that the proof takes from hypothesis (B).
2. **The final contradiction.** If `x` commuted with `g⁻¹ x g`, then `c³ = 1`. Since `|Q|` is
   prime to `3`, this gives `c = 1` and `g = x`. But `g` normalizes `σ(U)` and `x` does not. Every
   branch of the proof ends here (`not_commute_conj`).
3. **Three layers.** The maps `a(t) = σ(inl t)`, `b(t) = g⁻¹ a(t) g` and `d(t) = g⁻² a(t) g²` are
   three injective copies of the additive group of `F`. The element `g` normalizes `σ(U)`, and
   `U` is cyclic, so `g` acts on `σ(U)` as a power map `w ↦ wᵉ`. We may take `e` odd with
   `z^{e³} = z` for all `z ∈ F` ([`Exponent.lean`](PeterfalviProblem/Proof/Exponent.lean)).
   Conjugating `(g x)³ = 1` by `σ(U)` gives the relations `d(u^{e²}) b(uᵉ) a(u) = 1` for all
   `u ∈ U` ([`FieldLayers.lean`](PeterfalviProblem/Proof/FieldLayers.lean)).
4. **The Frobenius case, and `q = 3`.** If `e` agrees on `U` with a power of the Frobenius map,
   the relations are additive. Together with the fact that the *Paley set*
   `{s : s and s + 1 are nonzero squares}` generates `F` additively, they make `x` commute with
   `g⁻¹ x g` ([`FrobeniusPower.lean`](PeterfalviProblem/Proof/FrobeniusPower.lean),
   [`PaleySet.lean`](PeterfalviProblem/Algebra/PaleySet.lean)). For `q = 3` this is the only case:
   `|U| = 13`, and `e³ ≡ 1 (mod 13)` forces `e ≡ 1, 3` or `9`.
5. **The case `q ≠ 3`.** Here `q ≥ 5`. The argument works entirely inside `F`.
   - *The fixed-point principle*
     ([`CommutingSubgroup.lean`](PeterfalviProblem/Proof/CommutingSubgroup.lean)). The `s ∈ F`
     such that `a(t)` commutes with `b(s tᵉ)` for all `t` form an additive subgroup that is closed
     under inversion. By Hua's identity it is `F` or small
     ([`InverseClosedSubgroup.lean`](PeterfalviProblem/Algebra/InverseClosedSubgroup.lean)).
     Either way a nonzero element makes `x` commute with `g⁻¹ x g`.
   - *Collisions* ([`PairComposition.lean`](PeterfalviProblem/Proof/PairComposition.lean)). Two
     points `p ≠ r` of the Paley set *collide* if `(p + 1)ᵉ - pᵉ = (r + 1)ᵉ - rᵉ`. A collision
     gives relations of the form `a(v) b(s vᵉ) a(v)⁻¹ = b(s' vᵉ)`. In characteristic three these
     relations can be chained, and `F` is a cyclic module for the Frobenius map
     ([`FrobeniusCyclicModule.lean`](PeterfalviProblem/Algebra/FrobeniusCyclicModule.lean)). For
     `q ≠ 3` the polynomial `X^q - 1` has no repeated factor over `𝔽₃`, and this forces `s' = s`,
     which the fixed-point principle rules out. So there is no collision.
   - *Loops* ([`SkewCalculus.lean`](PeterfalviProblem/Proof/SkewCalculus.lean)). Any two points
     of the Paley set still give a weaker relation, an *edge*. Edges can be composed. A closed
     loop of edges whose weights are not both zero gives a contradiction in the same way. So all
     closed loops have zero weights.
   - *The master formula* ([`MasterFormula.lean`](PeterfalviProblem/Proof/MasterFormula.lean)).
     With no collisions and zero loop weights, the four-leg loops of two edges force the weights
     `K(p) = p^{e²} - (p + 1)^{e²}` to follow a formula with two constants `λ₊` and `λ₋`.
   - *The end* ([`Endgame.lean`](PeterfalviProblem/Proof/Endgame.lean)). Each of the four cases
     for `λ₊` and `λ₋` contradicts the formula, by arithmetic in `F`. The Paley set has at least
     `(3^q - 3)/4 ≥ 60` points, which is more than the argument needs.

The Lean library has about 5,800 lines in 19 files. Its main result is `false_of_witness` in
[`Endgame.lean`](PeterfalviProblem/Proof/Endgame.lean); [`Main.lean`](PeterfalviProblem/Main.lean)
turns it into `not_hypothesisB_three`.

## What is new, and what is not here

- **New:** the negative answer and its proof. They were found in August 2026 in the author's
  formalization of Bender–Glauberman, and they have not been published elsewhere.
- **Not here:** the other results of Glauberman–Norton and of Appendix C of Bender–Glauberman,
  such as Proposition 7 (`p ≥ 5`), Theorem C, and Example 11 (the Suzuki groups).
- **Literature.** On 2026-08-09, OpenAlex and Semantic Scholar listed no works citing
  Glauberman–Norton (1993); these databases miss the citation in Bender–Glauberman (1994). An
  AI-assisted search found no published answer, and Peterfalvi's later book, *Character Theory
  for the Odd Order Theorem* (2000), does not return to the problem. MathSciNet and zbMATH were
  not searched for citations. We know of no earlier answer, but we have not established novelty
  beyond this search.

## Related formalizations

- [yawara/odd-order](https://github.com/yawara/odd-order), the author's Lean formalization of the
  Feit–Thompson theorem and of the books of Isaacs, Bender–Glauberman and Peterfalvi. The proof
  was first found and formalized there, as `hypothesisB_false`. This repository extracts it from
  commit `82e8b66fe59ea58d67c59b4ebe8b4fb73ff2c1e0`, restates the problem in a short statement
  module, removes parts that the proof does not need, and simplifies a few steps.
- [math-comp/odd-order](https://github.com/math-comp/odd-order), the Coq formalization of the
  Feit–Thompson theorem by Gonthier et al. Its file `theories/BGappendixC.v` proves Theorem C of
  Appendix C of Bender–Glauberman (`p ≤ q`) for finite groups under the same hypotheses. It does
  not treat Problem 1, and it was not used here.

## Files

| Path | Contents |
| --- | --- |
| [`Challenge.lean`](Challenge.lean) | The two statements, importing only Mathlib, with the proofs left as `sorry` |
| [`Solution.lean`](Solution.lean) | Imports the complete proofs |
| [`comparator.json`](comparator.json) | Comparator selects the two theorems and permits only the standard axioms |
| [`PeterfalviProblem/Statement.lean`](PeterfalviProblem/Statement.lean) | The definitions in the statements, repeated word for word in `Challenge.lean` |
| [`PeterfalviProblem/Main.lean`](PeterfalviProblem/Main.lean) | The two main theorems |
| [`PeterfalviProblem/Basic/`](PeterfalviProblem/Basic/) | Norm-one units, the group `H`, and the structure `Witness` that holds the data of (B) |
| [`PeterfalviProblem/Algebra/`](PeterfalviProblem/Algebra/) | Facts about finite fields: the Paley set, the Frobenius module, inversion-closed subgroups |
| [`PeterfalviProblem/Proof/`](PeterfalviProblem/Proof/) | The proof, in the order of the outline above |
| [`PeterfalviProblem/SL2Example.lean`](PeterfalviProblem/SL2Example.lean) | The example `SL(2, 2^q)` for `p = 2` |
| [`Tests/`](Tests/) | The axiom audit and the text lint |
| [`formalization.yaml`](formalization.yaml) | Metadata: sources, provenance, AI use, review |

## Building and checking

Install [elan](https://github.com/leanprover/elan) and Python 3.11 or later. The Lean version is
fixed by [`lean-toolchain`](lean-toolchain) (`v4.35.0-rc2`), and Mathlib is pinned in
[`lake-manifest.json`](lake-manifest.json).

```sh
lake exe cache get
lake build
python3 -m pip install -r requirements-palomar.txt
python3 scripts/check.py
```

`scripts/check.py` checks the metadata, builds the library with no warnings, builds the Challenge
(which may report only its two `sorry` holes), checks that `PeterfalviProblem.lean` imports every
file, runs Mathlib's linters, and checks that every declaration uses only the three standard
axioms. It writes its logs to `.audit/`.

`scripts/verify-comparator.sh` runs Comparator, with Lean, NanoDa and con-ron checking the
proofs. It needs Linux and bubblewrap 0.12.0; the [CI workflow](.github/workflows/lean.yml) builds
bubblewrap with Palomar's pinned installer. The [Palomar preflight
workflow](.github/workflows/palomar-preflight.yml) runs Palomar's own mechanical verification.

## How this was made

Yawara Ishida directed the work and is responsible for it. AI systems made substantive
contributions.

- In August 2026, in the odd-order project, Claude agents (Claude Code with Claude Opus 5 and
  Claude Fable 5) found the proof, wrote the informal proof, and wrote the first Lean proof.
  Separate agent sessions reviewed the informal proof, each trying to refute one part of it.
  GAP and C programs checked the key identities in small fields.
- Four consultations with ChatGPT (GPT-5.6) informed the search. The agents checked each answer
  before using it. One idea from them is in the final proof: the use of Hua's identity in
  [`InverseClosedSubgroup.lean`](PeterfalviProblem/Algebra/InverseClosedSubgroup.lean).
- In September 2026, Claude Code with Claude Opus 5.5 extracted the proof into this repository,
  wrote the statement module and the Challenge, simplified the proof, and wrote the
  documentation.

No independent human review of the mathematics or of the Lean statements is claimed. The Lean
kernel checks the proofs. [`formalization.yaml`](formalization.yaml) records these facts in the
Palomar metadata format.

## Citation

Please cite this repository with the commit you used. A [`CITATION.cff`](CITATION.cff) is
included.

```bibtex
@software{ishida2026peterfalvi,
  author       = {Ishida, Yawara},
  title        = {{P}{\'e}terfalvi's Problem for $p = 3$: No Group Satisfies Hypothesis ({B})},
  year         = {2026},
  url          = {https://github.com/yawara/peterfalvi-problem},
  organization = {A.I.System Research, Inc.},
  license      = {Apache-2.0}
}
```

## License

This repository is released under the [Apache License 2.0](LICENSE). The cited papers and books
keep their own licenses.
