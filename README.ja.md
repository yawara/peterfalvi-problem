# p = 3 に対する Péterfalvi の問題

`p = 3` のとき、Glauberman–Norton の Proposition 9 の仮説 (B) を満たす群は存在しない。
このことの Lean 4 による証明です。1993 年に活字になって以来未解決だった Péterfalvi の問いに
答えます。

- 著者・管理者: Yawara Ishida
- ライセンス: [Apache-2.0](LICENSE)
- English: [README.md](README.md)

## 問題

G. Glauberman と S. P. Norton の論文 *On a combinatorial problem associated with the odd order
theorem* (Proc. Amer. Math. Soc. **119** (1993), 1089–1094,
[doi:10.1090/S0002-9939-1993-1160299-X](https://doi.org/10.1090/S0002-9939-1993-1160299-X))
は、次の問いで終わっています。

> **Problem** (Péterfalvi). Can the hypothesis of Proposition 9 be satisfied for `p = 3`?
>
> (Proposition 9 の仮説は `p = 3` で満たされうるか。)

同じ問いは、H. Bender と G. Glauberman の *Local Analysis for the Odd Order Theorem*
(London Math. Soc. Lecture Note Series 188, 1994) の付録 C、p. 152 の Problem 1
「Can `p = 3` in Theorem C?」でもあります。

この仮説は、Feit–Thompson の証明の最終章を T. Peterfalvi が簡略化した論文
(C. R. Acad. Sci. Paris Sér. I Math. **299** (1984), 531–534) に由来します。`p` と `q` を素数とし、
`F` を元の個数が `p^q` の体とします。

- `P` は `F` の加法群です。
- `U` は、素体 `𝔽_p` 上のノルムが 1 である `F` の元の群です。`U` は `P` に掛け算で作用します。
- `H = P ⋊ U` は半直積で、`P₀` は `𝔽_p` の加法群の `H` における像です。

Proposition 9 は次の 2 つを仮定します。

- **(A)** `q` は `p - 1` を割り切らない。
- **(B)** 群 `G`、単射準同型 `σ : H → G`、位数が `p` と互いに素な `G` の有限可換部分群 `Q`、
  元 `y ∈ Q` があって、`σ(P₀)` は `Q` を正規化し、`σ(P₀)^y = y⁻¹ σ(P₀) y` は `σ(U)` を正規化する。

`p = 2` ではこの仮説が成り立ちます。Glauberman–Norton は Péterfalvi による例として
`SL(2, 2^q)` と鈴木群を挙げています。`p ≥ 5` では、同じ論文の Proposition 7 と 9 により成り立ち
ません。`p = 3` の場合が未解決のまま残されていました。Bender–Glauberman の付録 C の Remark (IV)
も「`p` が 3 に等しくなりうるかどうかは、まだ分かっていない」と述べています。

## 結果

答えは **否** です。このリポジトリは 2 つの定理を証明します。どちらも標準の公理
`propext`、`Classical.choice`、`Quot.sound` だけに依存します。

| 主張 | Lean |
| --- | --- |
| `q ∤ 3 - 1` を満たすすべての素数 `q` について、`p = 3` の仮説 (B) を満たす群は存在しない。 | [`PeterfalviProblem.not_hypothesisB_three`](PeterfalviProblem/Main.lean) |
| すべての `q ≥ 1` について、群 `SL(2, 2^q)` は `p = 2` の仮説 (B) を満たす。 | [`PeterfalviProblem.hypothesisB_two`](PeterfalviProblem/Main.lean) |

```lean
theorem not_hypothesisB_three (q : ℕ) (hq : q.Prime) (hA : ¬ q ∣ 3 - 1) (G : Type*) [Group G] :
    ¬ HypothesisB 3 q G

theorem hypothesisB_two (q : ℕ) (hq : q ≠ 0) :
    HypothesisB 2 q (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 q))
```

1 つ目の定理が問題への答えです。仮定は `p = 3` の Proposition 9 の仮定そのもので、`q` が素数で
あることと条件 (A) です。素数 `q` に対して、`p = 3` の条件 (A) は `q ≠ 2` と同じです。群 `G` は
任意の群でよく、有限である必要はありません。

2 つ目の定理は `p = 2` に対する Péterfalvi の例です (Glauberman–Norton の Example 10、
Bender–Glauberman 付録 C の Remark (II))。仮説 (B) の定義が空でないこと、したがって 1 つ目の定理
が自明な理由で成り立っているのではないことを示します。論文のデータ
`σ(P) = {[[1, a], [0, 1]]}`、`σ(U) = {[[a, 0], [0, a⁻¹]]}`、`σ(P₀) = ⟨[[1, 1], [0, 1]]⟩`、
`y = [[0, 1], [1, 1]]`、`Q = ⟨y⟩` をそのまま使います。

定義は [`PeterfalviProblem/Statement.lean`](PeterfalviProblem/Statement.lean) にあります。

| 対象 | Lean | 定義 |
| --- | --- | --- |
| `P` | `additiveFieldGroup p q` | `Multiplicative (GaloisField p q)`: `F` の加法群を乗法的に書いたもの |
| `U` | `normOneUnits p q` | ノルム写像 `Fˣ → 𝔽_pˣ` の核 |
| `H = P ⋊ U` | `normOneFrobeniusGroup p q` | 作用 `u · s = u s` による Mathlib の半直積 |
| `U ≤ H` | `normOneFrobeniusComplement p q` | `U` の `H` における像 |
| `P₀ ≤ H` | `primeLine p q` | `𝔽_p → F` の像の、`H` における像 |
| (B) | `HypothesisB p q G` | 上で述べた命題 |

## 原典との対応

主張は Glauberman–Norton の Proposition 9 に従います。選択をした箇所は次のとおりです。

1. **群 `U`。** ノルム写像の核として定義します。Glauberman–Norton は `U` を `Fˣ` の `(p - 1)` 乗
   全体と定義し、それがノルム 1 の元全体であると注意しています。Bender–Glauberman は `U` を
   ノルム 1 の元全体と定義しています。
2. **最後の条件の `σ(U)`。** 論文は「`σ(P₀)^y` は `U` を正規化する」と書いています。`σ(P₀)^y` は
   `G` の部分群なので、これは `σ(U)` のことです。Bender–Glauberman 付録 C の Remark (VI) は、
   `H` をその `G` における像と同一視しています。
3. **共役。** `σ(P₀)^y` は `y⁻¹ σ(P₀) y` のことです。Lean では、`h ↦ y⁻¹ σ(h) y` による `P₀` の
   像です。
4. **「有限可換 `p′`-部分群」。** `p ∤ |Q|` を満たす有限可換部分群 `Q` のことです。
5. **条件 (A)。** Proposition 9 の形 `q ∤ p - 1` を使います。Bender–Glauberman は (A) を
   `gcd((p^q - 1)/(p - 1), p - 1) = 1` と書いています。2 つの形は同値です (Glauberman–Norton の
   Lemma 8)。補題 `coprime_iff_not_dvd` がこれを証明しますが、主定理には必要ありません。
6. **群 `G`。** 任意の群です。原典は `G` が有限であることを要求しておらず、否定的な答えはこの
   仮定なしで成り立ちます。
7. **`p = 2` の例。** 素数 `q` だけでなく、すべての `q ≥ 1` について証明しています。

定義が仮定するのは `p` が素数であることだけで、`q` に関する条件は定理の側で加えています。
1 つ目の定理を自明にするような退化した場合はありません。2 つ目の定理が、同じ定義が `p = 2` で
満たされることを示しているからです。`p = 3`, `q = 2` の組は原典どおり条件 (A) によって除かれて
おり、定理はこの場合について何も述べません。

## 証明の流れ

証明は新しいものです。群の分類も指標和も使いません。初等的ですが長い証明です。`p = 3` として、
群 `G` と仮説 (B) のデータを固定します。

1. **1 本の関係式。** `x` を `σ(P₀)` の生成元 `σ(inl 1)` とし、`g = y⁻¹ x y` とします。元
   `c = x⁻¹ g` は可換群 `Q` に入ります。ここから `G` の中の短い計算で `(g x)³ = 1` が出ます
   ([`CubeRelation.lean`](PeterfalviProblem/Proof/CubeRelation.lean))。証明が仮説 (B) から取り
   出す関係式はこれだけです。
2. **最後の矛盾。** もし `x` が `g⁻¹ x g` と可換なら `c³ = 1` です。`|Q|` は 3 と互いに素なので
   `c = 1`、つまり `g = x` となります。ところが `g` は `σ(U)` を正規化し、`x` は正規化しません。
   証明のすべての枝は、最後にここに行き着きます (`not_commute_conj`)。
3. **3 つの層。** 写像 `a(t) = σ(inl t)`, `b(t) = g⁻¹ a(t) g`, `d(t) = g⁻² a(t) g²` は、`F` の加法群
   の 3 つの単射なコピーです。`g` は `σ(U)` を正規化し、`U` は巡回群なので、`g` は `σ(U)` に冪写像
   `w ↦ wᵉ` として作用します。`e` は奇数で、すべての `z ∈ F` について `z^{e³} = z` となるように
   取れます ([`Exponent.lean`](PeterfalviProblem/Proof/Exponent.lean))。`(g x)³ = 1` を `σ(U)` の
   元で共役すると、すべての `u ∈ U` について関係式 `d(u^{e²}) b(uᵉ) a(u) = 1` が得られます
   ([`FieldLayers.lean`](PeterfalviProblem/Proof/FieldLayers.lean))。
4. **Frobenius の場合と `q = 3`。** `e` が `U` 上で Frobenius 写像の冪と一致するなら、関係式は
   加法的です。*Paley 集合* `{s : s と s + 1 がともに 0 でない平方元}` が `F` を加法的に生成する
   ことと合わせると、`x` は `g⁻¹ x g` と可換になります
   ([`FrobeniusPower.lean`](PeterfalviProblem/Proof/FrobeniusPower.lean)、
   [`PaleySet.lean`](PeterfalviProblem/Algebra/PaleySet.lean))。`q = 3` ではこの場合しかありません。
   `|U| = 13` で、`e³ ≡ 1 (mod 13)` から `e ≡ 1, 3, 9` となるからです。
5. **`q ≠ 3` の場合。** このとき `q ≥ 5` です。議論はすべて `F` の中で進みます。
   - *不動点原理*
     ([`CommutingSubgroup.lean`](PeterfalviProblem/Proof/CommutingSubgroup.lean))。すべての `t`
     について `a(t)` が `b(s tᵉ)` と可換になる `s ∈ F` の全体は、逆元をとる操作で閉じた加法部分群
     です。Hua の恒等式により、これは `F` 全体か、小さい部分群です
     ([`InverseClosedSubgroup.lean`](PeterfalviProblem/Algebra/InverseClosedSubgroup.lean))。
     どちらの場合も、0 でない元があれば `x` は `g⁻¹ x g` と可換になります。
   - *衝突* ([`PairComposition.lean`](PeterfalviProblem/Proof/PairComposition.lean))。Paley 集合
     の 2 点 `p ≠ r` が `(p + 1)ᵉ - pᵉ = (r + 1)ᵉ - rᵉ` を満たすとき、*衝突する* と言います。衝突
     からは `a(v) b(s vᵉ) a(v)⁻¹ = b(s' vᵉ)` の形の関係式が得られます。標数 3 ではこの関係式を
     つなげることができ、`F` は Frobenius 写像についての巡回加群です
     ([`FrobeniusCyclicModule.lean`](PeterfalviProblem/Algebra/FrobeniusCyclicModule.lean))。
     `q ≠ 3` なら多項式 `X^q - 1` は `𝔽₃` 上で重複因子を持たず、このことから `s' = s` が従います。
     これは不動点原理で否定されます。したがって衝突は存在しません。
   - *ループ* ([`SkewCalculus.lean`](PeterfalviProblem/Proof/SkewCalculus.lean))。Paley 集合の
     任意の 2 点は、それでも弱い関係式 (*辺*) を与えます。辺は合成できます。重みが両方 0 では
     ない閉じたループからは、同じようにして矛盾が出ます。したがって閉じたループの重みはすべて
     0 です。
   - *master formula* ([`MasterFormula.lean`](PeterfalviProblem/Proof/MasterFormula.lean))。
     衝突がなく、ループの重みが 0 なら、2 本の辺からなる 4 脚のループにより、重み
     `K(p) = p^{e²} - (p + 1)^{e²}` は 2 つの定数 `λ₊`, `λ₋` を持つ公式に従います。
   - *終局* ([`Endgame.lean`](PeterfalviProblem/Proof/Endgame.lean))。`λ₊` と `λ₋` についての 4 つ
     の場合のそれぞれが、`F` の中の計算で公式と矛盾します。Paley 集合は少なくとも
     `(3^q - 3)/4 ≥ 60` 個の点を持ち、議論に必要な数より十分多くあります。

Lean のライブラリは 19 ファイル、約 5,800 行です。主結果は
[`Endgame.lean`](PeterfalviProblem/Proof/Endgame.lean) の `false_of_witness` で、
[`Main.lean`](PeterfalviProblem/Main.lean) がこれを `not_hypothesisB_three` に仕上げます。

## 新しいこと、ここにないもの

- **新しいこと:** 否定的な答えとその証明です。2026 年 8 月、著者による Bender–Glauberman の
  形式化の中で見つかり、他の場所では発表されていません。
- **ここにないもの:** Glauberman–Norton と Bender–Glauberman 付録 C の他の結果。たとえば
  Proposition 7 (`p ≥ 5`)、Theorem C、Example 11 (鈴木群) です。
- **文献。** 2026-08-09 の時点で、OpenAlex と Semantic Scholar は Glauberman–Norton (1993) を引用
  する文献を 1 件も挙げていませんでした (これらのデータベースは Bender–Glauberman (1994) による
  引用を拾っていません)。AI を使った文献調査でも発表された解答は見つからず、Peterfalvi の後の本
  *Character Theory for the Odd Order Theorem* (2000) もこの問題に戻っていません。MathSciNet と
  zbMATH での被引用検索はしていません。先行する解答を私たちは知りませんが、この調査の範囲を
  超えて新規性を確かめてはいません。

## 関連する形式化

- [yawara/odd-order](https://github.com/yawara/odd-order): 著者による Feit–Thompson の定理と、
  Isaacs、Bender–Glauberman、Peterfalvi の本の Lean による形式化です。証明はここで最初に見つかり、
  `hypothesisB_false` として形式化されました。このリポジトリは、コミット
  `82e8b66fe59ea58d67c59b4ebe8b4fb73ff2c1e0` からこの証明を取り出し、問題を短い主張モジュールで
  述べ直し、証明に不要な部分を除き、いくつかの段階を簡単にしたものです。
- [math-comp/odd-order](https://github.com/math-comp/odd-order): Gonthier らによる Feit–Thompson
  の定理の Coq による形式化です。そのファイル `theories/BGappendixC.v` は、同じ仮説のもとで
  Bender–Glauberman 付録 C の Theorem C (`p ≤ q`) を有限群について証明しています。Problem 1 は
  扱っておらず、ここでは使っていません。

## ファイル

| パス | 内容 |
| --- | --- |
| [`Challenge.lean`](Challenge.lean) | 2 つの主張。Mathlib だけを import し、証明は `sorry` のまま |
| [`Solution.lean`](Solution.lean) | 完全な証明を import する |
| [`comparator.json`](comparator.json) | Comparator が 2 つの定理を選び、標準の公理だけを許す |
| [`PeterfalviProblem/Statement.lean`](PeterfalviProblem/Statement.lean) | 主張に現れる定義。`Challenge.lean` が一字一句そのまま繰り返す |
| [`PeterfalviProblem/Main.lean`](PeterfalviProblem/Main.lean) | 2 つの主定理 |
| [`PeterfalviProblem/Basic/`](PeterfalviProblem/Basic/) | ノルム 1 の元、群 `H`、(B) のデータを保持する構造体 `Witness` |
| [`PeterfalviProblem/Algebra/`](PeterfalviProblem/Algebra/) | 有限体の事実: Paley 集合、Frobenius 加群、逆元で閉じた部分群 |
| [`PeterfalviProblem/Proof/`](PeterfalviProblem/Proof/) | 証明。上の流れの順 |
| [`PeterfalviProblem/SL2Example.lean`](PeterfalviProblem/SL2Example.lean) | `p = 2` の例 `SL(2, 2^q)` |
| [`Tests/`](Tests/) | 公理の監査とテキストの lint |
| [`formalization.yaml`](formalization.yaml) | メタデータ: 原典、出自、AI の利用、レビュー |

## ビルドと検査

[elan](https://github.com/leanprover/elan) と Python 3.11 以上を入れてください。Lean の版は
[`lean-toolchain`](lean-toolchain) (`v4.35.0-rc2`) で固定され、Mathlib は
[`lake-manifest.json`](lake-manifest.json) で固定されています。

```sh
lake exe cache get
lake build
python3 -m pip install -r requirements-palomar.txt
python3 scripts/check.py
```

`scripts/check.py` は、メタデータを検査し、ライブラリを警告なしでビルドし、Challenge をビルドし
(報告してよいのは 2 つの `sorry` だけ)、`PeterfalviProblem.lean` がすべてのファイルを import
していることを確かめ、Mathlib の linter を走らせ、すべての宣言が標準の 3 つの公理だけを使うことを
確かめます。ログは `.audit/` に書き出されます。

`scripts/verify-comparator.sh` は Comparator を走らせ、証明を Lean、NanoDa、con-ron で検査します。
Linux と bubblewrap 0.12.0 が必要です。[CI のワークフロー](.github/workflows/lean.yml) は Palomar
の固定されたインストーラで bubblewrap をビルドします。[Palomar の preflight
ワークフロー](.github/workflows/palomar-preflight.yml) は Palomar 自身の機械的検証を走らせます。

## 作り方

作業は Yawara Ishida が指揮し、その責任を負います。AI システムが実質的に貢献しています。

- 2026 年 8 月、odd-order プロジェクトの中で、Claude のエージェント (Claude Code、Claude Opus 5 と
  Claude Fable 5) が証明を見つけ、非形式的な証明を書き、最初の Lean の証明を書きました。別の
  エージェントのセッションが、それぞれ証明の一部を反駁しようとする形で非形式的な証明を検査
  しました。GAP と C のプログラムが、小さい体で主要な恒等式を検査しました。
- ChatGPT (GPT-5.6) への 4 回の相談が探索の参考になりました。エージェントはそれぞれの回答を使う
  前に検査しました。最終的な証明にはそこからのアイデアが 1 つ入っています。
  [`InverseClosedSubgroup.lean`](PeterfalviProblem/Algebra/InverseClosedSubgroup.lean) での Hua の
  恒等式の使い方です。
- 2026 年 9 月、Claude Code (Claude Opus 5.5) が証明をこのリポジトリに取り出し、主張モジュールと
  Challenge を書き、証明を簡単にし、文書を書きました。

数学についても Lean の主張についても、独立した人間によるレビューは主張しません。証明は Lean の
カーネルが検査します。[`formalization.yaml`](formalization.yaml) は、これらの事実を Palomar の
メタデータ形式で記録しています。

## 引用

このリポジトリを、使ったコミットとともに引用してください。[`CITATION.cff`](CITATION.cff) も
あります。

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

## ライセンス

このリポジトリは [Apache License 2.0](LICENSE) で公開しています。引用している論文や本には、それぞれ
のライセンスが適用されます。
