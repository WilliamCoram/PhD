# Decomposition — `lwx-seam-m`

LWX Proposition 2.17 at **every** analyticity level `m`, so that the seam between the integral
model and Buzzard's overconvergent forms covers the whole boundary annulus `p⁻¹ < ‖T₀‖ < 1`.

Sources (verbatim extracts with locators are quoted per leaf below):

* `references/lwx.txt` — Liu–Wan–Xiao, *The eigencurve over the boundary of weight space*,
  arXiv:1412.2584v4.
* `references/colmez.txt` — P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330
  (2010), 13–59 (text extracted from `references/colmez_asterisque330.pdf` with `pypdf`; the
  extraction garbles displayed formulas **and renders `≤`/`≥` as `<`/`>`**, so every formula and
  every inequality below was re-derived and checked against exhaustive numerical examples — see
  group A, "A reading trap in the extracted text").

Skeleton status: **all ten files compile, sorries only** (`lake build`, 3730 jobs).

| File | Lines | Sorries |
|---|---|---|
| `PhD/TateFredholm/Unitriangular.lean` | 130 | 9 |
| `PhD/TateFredholm/BlockMap.lean` | 105 | 10 |
| `PhD/LWX/AmiceValuation.lean` | 190 | 22 |
| `PhD/LWX/PowSubOne.lean` | 93 | 8 |
| `PhD/LWX/AmiceBasis.lean` | 228 | 24 |
| `PhD/LWX/HaloWeightH.lean` | 447 | 51 |
| `PhD/LWX/DiscModel.lean` | 238 | 20 |
| `PhD/LWX/DiscForms.lean` | 195 | 9 |
| `PhD/LWX/SeamH.lean` | 265 | 15 |
| `PhD/LWX/QuaternionicH.lean` | 164 | 3 |

---

## Step 1 — The prose proof

### Top-level result SH-M

> **Proposition 2.17.** Using the isomorphism (2.11.1), the space `S^D_int` admits an orthonormal
> basis (over `Λ`) given by `1_0, …, 1_{t−1}, z_0, …, z_{t−1}, (z_0 choose 2), …`  … Let
> `P = (P_{m,n})` denote the corresponding infinite matrix for the `U_p`-action … Then it agrees
> with the characteristic power series of the `U_p`-action on each `S^{D,†,m}_{[−]_m}`.
> — `lwx.txt:966–1006`

> **Proof.** By [Colm10, Théorème 1.29] we cited above, the functions `⌊n/(q⁻¹pᵐ)⌋!·(z_i choose n)`
> for `i = 0, …, t−1` and `n ∈ Z_{≥0}` form an orthonormal basis of `S^{D,†,m}_{[−]_m}`. If `P′`
> denotes the infinite matrix of `U_p`-action on this basis, then `P` and `P′` are conjugated by
> an infinite diagonal matrix with diagonal entries `1, …, 1, …, ⌊n/(q⁻¹pᵐ)⌋!, …`.  So taking the
> limit of the characteristic polynomial of the first `r×r`-minors, as `r` goes to infinity gives
> `Char(U_p; S^{D,†,m}_{[−]_m}) = det(I∞ − XP′) = det(I∞ − XP)`. — `lwx.txt:993–1010`

The `m = 1` case is already formalised (`PhD/LWX/Seam.lean`,
`specCharSeries_ofCerts_eq_heckeCharPowerSeries`).  The proof there has four moves; the
generalisation keeps all four and replaces the ambient space:

1. **Model.** `S^{D,†,m}` is functions valued in `OB_{qp^{-m}}` = continuous functions on `ℤ_p`
   analytic on each disc `a + q⁻¹pᵐℤ_p`.  At `m = 1` (`q = p`, odd `p`) there is exactly one
   disc, so `OB_{p^{-1}}` is the Tate algebra `K⟨z⟩` and `S^{D,†,1}` is `QMF.Weight.Forms` at the
   halo weight.  For `m = h + 1 > 1` there are `pʰ` discs and the model is `c(ℤ/pʰ × ℕ, K)`.
2. **Basis.** Amice's theorem gives the orthonormal basis `⌊n/pʰ⌋!·(z choose n)` of that model.
   At `m = 1` this is `PhD/LWX/Colmez.lean`'s `colmezEquiv` (descending Pochhammer, one disc);
   in general it is Colmez's Théorème 1.4.7, which is **not** in mathlib and must be proved.
3. **Action.** `U_p` acts by the certificate matrices of [LWX, Prop 3.1]; on the model it is the
   `(2.3.2)` slash action.  At `m = 1` this is `AnalyticWeight.kappaSlash` at the halo weight; in
   general the action permutes the discs and is a *block* operator of single-disc weight actions
   at conjugated matrices.
4. **Seam.** `diag(⌊n/pʰ⌋!)` conjugates the Colmez-basis matrix `P′` into the integral matrix
   `P(T₀)`, and `charPowerSeries` is invariant under conjugation by a diagonal of units.  This
   move is already fully general in the repo (`charPowerSeries_eq_of_diag_intertwine`,
   `charPowerSeries_conj`).

Moves 2 and 3 are the whole content of this board; move 4 is transcription.

### Why a shortcut is not available (recorded so it is not re-attempted)

Three shortcuts were considered and each was rejected against the source:

* *"Take `m` large only in the statement, keep the Tate algebra."*  False: `S^{D,†,m}` is by
  definition valued in `Ind(χ)^{m,an}`, and `lwx.txt:634–639` says "the latter space may be
  understood as the subspace of continuous functions `h ∈ C(ℤ_p; A)` such that `h` is analytic
  on `a + q⁻¹pᵐℤ_p` for all `a ∈ ℤ_p`" — a strictly larger space than `K⟨z⟩` for `m > 1`.
* *"Use [Bu04, Lemma 4] to reduce every `m` to `m = 1`."*  Circular: `lwx.txt:735` invokes
  [Bu04, Lemma 4] only to say the characteristic series is independent of the flexibility, and
  the `m = 1` space is only defined when the character is `1`-locally analytic, which fails on
  most of the annulus.  Independence of `m` is a *corollary* of this board (leaf SH-9), not an
  input.
* *"Redefine the Mahler side instead."*  The Mahler side is fixed: `P` is the matrix of `U_p` on
  the integral model `S^D_int`, already formalised (`PhD/LWX/UpMatrix.lean`), and Prop 2.17 is
  precisely the comparison of that fixed matrix with the analytic side.

---

## Step 2 — Ordered leaves

Dependency graph (`→` = "imports"):

```
Unitriangular ─┐
AmiceValuation ─┼→ AmiceBasis ─┐
PowSubOne ─────┘               │
PowSubOne → HaloWeightH ───────┼→ DiscModel → DiscForms ─┐
BlockMap ──────────────────────┘                         ├→ SeamH → QuaternionicH
                                                 Seam ───┘
```

(`PhD/LWX/Seam.lean` and `PhD/LWX/Certificates.lean` are existing, sorry-free files.)

---

## Step 3–4 — Leaves, with source quotes, Lean ↔ source match, and discharge

### Group U — `PhD/TateFredholm/Unitriangular.lean` (the orthonormality criterion)

Colmez proves Théorème 1.4.7 by reducing modulo `p`:

> "Le (ii) du lemme implique alors que si on découpe la matrice `M_m` en blocs de taille
> `pʰ × pʰ`, on obtient une matrice triangulaire supérieure par blocs et chacun des blocs
> diagonaux est triangulaire inférieur avec des éléments inversibles sur la diagonale (cette
> inversibilité résulte du second point du lemme). La matrice `M_m` est donc inversible, ce qui
> montre que le lemme 1.4.9 fournit les points manquant pour démontrer le th. 1.4.7."
> — `colmez.txt:673–682`

and the reduction step is licensed by

> **Proposition 1.1.5.** Si `L` est de valuation discrète, et `π_L` est une uniformisante de `L`,
> alors … `(e_i)_{i∈I}` est une base orthonormale de `B` si et seulement si `(ē_i)_{i∈I}` est une
> base algébrique du `k_L`-espace vectoriel `B̄ = B°/π_L B°`. — `colmez.txt:117–127`

**Deliberate strengthening (recorded).** Prop 1.1.5 assumes `L` **discretely valued**.  Our `K`
is an arbitrary complete ultrametric field (the repo's standing hypothesis, and `K_p` for `D/ℚ`
*is* discretely valued, but `QMF`'s weight tower is stated without that assumption and the
`lwx-slopes` board consumes it over general `K`).  Rather than add a discreteness hypothesis that
would not survive downstream, group U replaces the reduction argument by a direct one:

* **U-1** `IsUnitriangularPerturbation M q` — entries of norm `≤ 1`, unit diagonal, entries below
  the diagonal of norm `≤ q < 1`, finitely supported columns.  This is Colmez's "triangulaire …
  avec des éléments inversibles sur la diagonale" made quantitative, with `q` playing the role of
  `|π_L|`.
* **U-2 … U-4** `ofPerturbation`, `matrixCoeff_ofPerturbation`, `norm_ofPerturbation_le`.
  *Discharge:* `TateFredholm.ofCoeffs` (`PhD/TateFredholm/GenFun.lean:178`), verified signature
  `ofCoeffs (M) (hbd : ∃ C, ∀ j i, ‖M j i‖ ≤ C) (hcol : ∀ i, Tendsto (fun j => M j i) cofinite (𝓝 0))`.
* **U-5** `norm_ofPerturbation` (isometry).  *Largest-index argument:* pick `n₀` maximal with
  `‖a n₀‖ = ‖a‖` (exists: `a ∈ c₀`, so `‖a ·‖` attains its max on a finite set).  In coordinate
  `n₀`, `∑_n M n₀ n · a n` has the term `M n₀ n₀ a n₀` of norm exactly `‖a‖`; terms with `n < n₀`
  have `‖M n₀ n‖ ≤ q` (below diagonal) hence norm `≤ q‖a‖ < ‖a‖`; terms with `n > n₀` have
  `‖a n‖ < ‖a‖` by maximality.  Ultrametric ⇒ the sum has norm exactly `‖a‖`.
* **U-6** `surjective_of_forall_exists_approx` — abstract successive approximation over a complete
  space.  *Discharge:* geometric-series completeness; `c(I,K)` is complete.
* **U-7** `exists_approx_single` — strong induction on `k`: divide the `k`-th column by its unit
  diagonal entry; the finitely many above-diagonal entries are corrected by the inductive
  hypothesis; the below-diagonal residue has norm `≤ q`.
* **U-8** `exists_approx` — truncate to finite support and sum U-7.
* **U-9 … U-11** `injective_ofPerturbation`, `equivOfPerturbation`, `norm_equivOfPerturbation_symm`.

**Lean ↔ source match.** `IsUnitriangularPerturbation.norm_diag` is Colmez's "éléments inversibles
sur la diagonale"; `norm_le_of_lt` is "triangulaire inférieur" *within* a diagonal block **and**
"triangulaire supérieure par blocs" *across* blocks, merged because the order `discIdx` (group AB)
linearises both at once; `col_finite` is Colmez's "si `n < (m+1)pʰ − 1`, alors `m(k) < m(n)`
implique que `k < (m+1)pʰ − 1`" (`colmez.txt:672–673`), i.e. the finite-block truncation.

**Attacks attempted.**
1. *Is the largest-index argument valid when `‖a‖` is attained at infinitely many indices?*  It
   is not attained infinitely often: `a ∈ c(ℕ,K)` means `a n → 0`, so `{n : ‖a n‖ = ‖a‖}` is
   finite and nonempty for `a ≠ 0`.  Handled; `a = 0` separately.  **Survived.**
2. *Does surjectivity need `q < 1` strictly, or would `q ≤ 1` do?*  Strictly: with `q = 1` the
   successive approximation does not converge, and the claim is false (an upper-triangular
   matrix with unit diagonal and unit entries can fail to be surjective).  The hypothesis
   `q_lt_one` is present.  **Survived** (and confirms the field is needed).
3. *Is `col_finite` really available, or is it an artifact?*  It is: the `n`-th Colmez basis
   element `g_n` is a polynomial of degree `n`, so its Taylor expansion on each disc has degree
   `≤ n` (`natDegree_discPoly_le`), giving finitely many nonzero rows per column.  Quoted at
   `colmez.txt:672`.  **Survived.**
4. *Could `IsUnitriangularPerturbation` be weakened to `Tendsto` columns instead of finite
   support (more general)?*  Yes for U-5/U-6, but U-7's induction uses finiteness.  Left as
   stated; noted in "deferred".  **Survived as stated.**

### Group BM — `PhD/TateFredholm/BlockMap.lean` (rectangular block maps)

Pure infrastructure, no source quote needed (it is the fibre-changing analogue of the existing
`blockDiag` in `PhD/TateFredholm/Conjugation.lean:100`).  Leaves BM-1 … BM-10:
`blockOpMap`, `blockMap`, `blockOpMap_blockIncl`, `matrixCoeff_blockOpMap`, `blockMap_blockIncl`,
`matrixCoeff_blockMap`, `blockMap_eq_blockDiag`, `blockMap_id`, `blockMap_comp_blockOp`,
`blockOp_comp_blockMap`, `blockMap_comp`, `blockMapEquiv`.

*Discharge:* `cSpace.blockIncl`/`blockProj` (`BlockOp.lean:548,585`), `blockProj_blockIncl`
(`:611`), `matrixCoeff_blockOp` (`:646`), `blockOp_comp` (`:691`), and the proofs of
`blockDiag_comp_blockOp` / `blockOp_comp_blockDiag` (`Conjugation.lean:124,135`) transcribe
verbatim with `I` and `I'` distinguished.

**Attacks attempted.**
1. *Does `blockMap` need `[Fintype σ]`?*  Yes — the definition is a finite double sum.  `σ = ι`
   (class representatives, finite) and `σ = ZMod (pʰ)` (finite).  **Survived.**
2. *Is `blockMap_eq_blockDiag` type-correct (`I = I'`)?*  Checked: it compiles in the skeleton.
   **Survived.**
3. *Could this be avoided by working with `c(ι × ℤ/pʰ × ℕ)` reassociated?*  It could, at the cost
   of an associativity reindexing on every statement; strictly worse.  **Survived.**

### Group A — `PhD/LWX/AmiceValuation.lean` (Colmez, Lemme 1.4.9)

> **Lemme 1.4.9.** (i) `g_{n,j}` est à coefficients dans `ℤ_p`.
> (ii) Sa réduction `ḡ_{n,j}` modulo `p` vérifie : `ḡ_{n,j} = 0` si `j > i(n)` ;
> `deg(ḡ_{n,j}) = m(n)` si `j = i(n)` ; `deg(ḡ_{n,j}) < m(n)` si `j < i(n)`.
> — `colmez.txt:666–671`

> **Démonstration du lemme 1.4.9.** Soit `K_{n,j} = {k ≤ n − 1, v_p(j + k) ≥ h}`.  L'application
> `k ↦ j + k` induisant une bijection de `K_{n,j}` sur l'ensemble des entiers de `[j, j + n − 1]`
> divisibles par `pʰ`, on a `|K_{n,j}| = ⌊(j+n−1)/pʰ⌋ − ⌊(j−1)/pʰ⌋`, et donc
> `|K_{n,j}| = m(n) + 1` si `j ≥ i(n)` et `|K_{n,j}| = m(n)` si `j < i(n)`.
> On a `g_{n,j} = c_{n,j} f_{n,j}`, où `c_{n,j} ∈ ℚ_p^×` et `f_{n,j} … ∈ ℤ_p[x]` a pour réduction
> `f̄_{n,j} = ∏_{k∈K_{n,j}} (x − β_k)` modulo `p` … Comme le degré de `f_{n,j}` est le cardinal de
> `K_{n,j}`, le lemme est équivalent aux résultats suivants : `v_p(c_{n,j}) ≥ 0` pour tout `j` ;
> `v_p(c_{n,j}) = 0` si `j = i(n)` ; `v_p(c_{n,j}) > 0` si `j > i(n)`.
> — `colmez.txt:684–708`

> `v_p(c_{n,j}) = ∑_{ℓ=1}^{h} ( ⌊(n+j−1)/p^ℓ⌋ − ⌊(j−1)/p^ℓ⌋ − ⌊n/p^ℓ⌋ )`.  Comme
> `⌊x+y⌋ ≥ ⌊x⌋ + ⌊y⌋`, chacun des termes de la somme est `≥ 0`, et donc `v_p(c_{n,j}) ≥ 0`.
> — `colmez.txt:722–740`

**Leaves.**
* **A-1** `card_filter_range_mod_eq` — `#{k < n : k ≡ r (q)} = ⌊n/q⌋ + [r < n mod q]`.  This is
  Colmez's `|K_{n,j}| = ⌊(j+n−1)/pʰ⌋ − ⌊(j−1)/pʰ⌋` re-centred (see A-9).
  *Discharge:* `Nat.Ioc_filter_dvd_card_eq_div`, `Nat.card_multiples`, plus a shift.  Verified
  present.  (`Nat.count_modEq_card` does **not** exist — checked by grep; do not cite it.)
* **A-2** `padicValNat_factorial_sub_factorial_div_pow` — Colmez's "identité
  `v_p(n!) − v_p(⌊n/pʰ⌋!) = ∑_{ℓ=1}^{h} ⌊n/p^ℓ⌋`" (`colmez.txt:727`).
  *Discharge:* `padicValNat_factorial (hnb : log p n < b) : padicValNat p n ! = ∑ i ∈ Ico 1 b, n / p^i`.
* **A-3** `min_padicValNat_eq_card` — Colmez's "`∑_{k=0}^{n−1} inf(v_p(j+k), h) = ∑_{ℓ=1}^{h} #{…}`"
  (`colmez.txt:728–735`).
* **A-4 … A-7** `colmezPoly`, `colmezPoly_eval_natCast`, `natDegree_colmezPoly`, `discPoly`,
  `discPoly_eval`, `natDegree_discPoly_le` — the objects `g_n` and `g_{n,a}(x) = g_n(a + pʰx)`.
  *Discharge:* `descPochhammer`, `Polynomial.eval_comp`, `Ring.choose`/`descPochhammer` bridge.
* **A-8** `discPoly_eq` — the factorisation `g_{n,a} = c_{n,a}·f_{n,a}`, verbatim
  `colmez.txt:697`.  Each linear factor `a − k + pʰx` is `pʰ(x − (k−a)/pʰ)` when `pʰ ∣ k − a` and
  `(a−k)(1 + pʰx/(a−k))` otherwise.
* **A-9** `norm_discConst` — `‖c_{n,a}‖ = p^{−N}`, `N = #{1 ≤ ℓ ≤ h : a mod p^ℓ < n mod p^ℓ}`.
  This is Colmez's displayed formula re-centred; see the correction note below.
* **A-10 … A-12** `norm_discConst_le_one`, `norm_discConst_res`, `norm_discConst_le_inv_of_lt` —
  Colmez's three bullet points `v_p(c) ≥ 0`, `= 0` at the diagonal disc, `> 0` below it.
* **A-13 … A-15** `norm_coeff_discFactor_le`, `norm_coeff_discFactor_le_inv_of_lt`,
  `norm_coeff_discFactor_card` — `f̄_{n,a}` is monic of degree `|K_{n,a}|`.
* **A-16 … A-19** the four facts consumed downstream: `norm_coeff_discPoly_le` (=(i)),
  `norm_coeff_discPoly_le_inv_of_lt`, `norm_coeff_discPoly_le_inv_of_res_lt`,
  `norm_coeff_discPoly_diag`.

**Re-centring of the source's indexing (and the reason A-9's statement differs from the quoted
formula).**  Colmez centres the discs at `−j`, `1 ≤ j ≤ pʰ`, and writes `n = (m(n)+1)pʰ − i(n)`.
Solving that under `1 ≤ i(n) ≤ pʰ`: `(m(n)+1)pʰ` is the least multiple of `pʰ` strictly greater
than `n`, so

* `m(n) = ⌊n/pʰ⌋` for **every** `n`, and
* `i(n) = pʰ − (n mod pʰ)`.

(Checked by exhaustive search for `pʰ ∈ {3,4,5,8,9}` and `n < 60`.)  So Colmez's `m(n)` is exactly
the `⌊n/pʰ⌋` appearing in Théorème 1.4.7's basis `⌊n/pʰ⌋!·(z choose n)`, with no discrepancy.

Here the discs are indexed by their natural centre `a`, `0 ≤ a < pʰ`, related to Colmez's `j` by
`j = pʰ − a`; hence `a = n mod pʰ` is the disc `j = i(n)`, and

| Colmez | here |
|---|---|
| `j > i(n)` | `a < n mod pʰ` |
| `j = i(n)` | `a = n mod pʰ` |
| `j < i(n)` | `a > n mod pʰ` |

giving the dictionary

| Colmez, Lemme 1.4.9 | here | Lean |
|---|---|---|
| (i) `g_{n,j} ∈ ℤ_p[x]` | integral on every disc | `norm_coeff_discPoly_le` |
| (ii) `deg ḡ_{n,j} ≤ m(n)` for all `j` | coeff at degree `> ⌊n/pʰ⌋` is `p`-divisible on every disc | `norm_coeff_discPoly_le_inv_of_lt` |
| (ii) `ḡ_{n,j} = 0` for `j > i(n)` | coeff at degree `⌊n/pʰ⌋` is `p`-divisible for `a < n mod pʰ` | `norm_coeff_discPoly_le_inv_of_res_lt` |
| (ii) `deg ḡ_{n,i(n)} = m(n)` | coeff at degree `⌊n/pʰ⌋` is a **unit** at `a = n mod pʰ` | `norm_coeff_discPoly_diag` |

and `|K_{n,a}| = ⌊n/pʰ⌋ + [a < n mod pʰ]`,
`v_p(c_{n,a}) = #{1 ≤ ℓ ≤ h : a mod p^ℓ < n mod p^ℓ}`.  Note the third row is a **weakening** of
Colmez's statement (he gets the whole reduction to vanish, we only need the top coefficient);
that is the direction the unitriangularity criterion consumes.

**A reading trap in the extracted text (recorded so it is not mis-resolved again).**  The `pypdf`
extraction of `colmez_asterisque330.pdf` renders `≤` and `≥` as `<` and `>` throughout: the
definition prints as "avec 1 < i(n) < ph" (`colmez.txt:616`) where the original must be
`1 ≤ i(n) ≤ pʰ`, and the proof of Thm 1.4.7 prints as "pour m < ra(ra)" (`colmez.txt:675`) where it
must be `m ≤ m(n)`.  Consequently the third bullet of clause (ii), which prints as
"deg(ḡ_{n,j}) < m(n) si j < i(n)" (`colmez.txt:670`), is `deg(ḡ_{n,j}) ≤ m(n)` in the original.
This matters: the strict reading is **false** — at `p = 3`, `h = 1`, `n = 4`, `j = 1 < i(4) = 2`
the reduction is `ḡ_{4,1} ≡ 2x − 2`, of degree `1 = m(4)`, not `< 1`.  The non-strict reading is
what the proof of Théorème 1.4.7 uses ("l'existence d'éléments `a_{j,m} ∈ F_p`, pour `m ≤ m(n)`")
and is what the diagonal blocks being *triangular* (not strictly triangular) requires.  Verified
exhaustively for `p = 3`, `h = 1`, `n ≤ 7`, `1 ≤ j ≤ 3`: the `≤` reading holds in every case, the
`<` reading fails in 7 of 21.

**Attacks attempted.**
1. *Is `m(n) = ⌊n/pʰ⌋`, or is it off by one when `pʰ ∣ n`?*  An earlier draft of this plan claimed
   the latter and cited it as an error in the source.  That claim was **my own arithmetic slip**
   (mis-solving `n = (m+1)pʰ − i` under `1 ≤ i ≤ pʰ`).  `m(n) = ⌊n/pʰ⌋` always, verified
   exhaustively; Colmez is correct.  Separately, the *strict* third bullet is false, but that
   strictness is an artifact of the `≤`→`<` text extraction, not of the paper — see the reading
   trap above.  **Attack succeeded against my draft, not against the source; both corrected.**
2. *Is `norm_coeff_discPoly_le_inv_of_lt` claimed on every disc, or only on some?*  Every disc —
   because `deg f̄_{n,a} = |K_{n,a}| ≤ ⌊n/pʰ⌋ + 1` and when `|K| = ⌊n/pʰ⌋ + 1` we have
   `a ≥ n mod pʰ`… so coefficients above `|K|` are `p`-divisible but the one **at** `⌊n/pʰ⌋ + 1`
   would not be.  Re-checked: `|K_{n,a}| = ⌊n/pʰ⌋ + [a < n mod pʰ]`, so `|K| ≤ ⌊n/pʰ⌋ + 1` with
   equality only when `a < n mod pʰ`, and in that case `v_p(c_{n,a}) ≥ 1` (A-12) kills the whole
   polynomial mod `p`.  Hence coefficients at degree `> ⌊n/pʰ⌋` are `p`-divisible on every disc.
   **Survived, after the argument was repaired to route through A-12.**
3. *Does `padicValNat_factorial` have the hypothesis I need?*  Verified:
   `padicValNat_factorial (hnb : Nat.log p n < b) : padicValNat p n ! = ∑ i ∈ Ico 1 b, n / p ^ i`.
   The bound `b` is chosen `> max(h, log p n)`.  **Survived.**
4. *Is `Nat.count_modEq_card` available for A-1?*  **No** — not found by grep in this mathlib.
   A-1 is discharged from `Nat.Ioc_filter_dvd_card_eq_div` instead.  **Attack succeeded; citation
   corrected.**

### Group AB — `PhD/LWX/AmiceBasis.lean` (Colmez, Théorème 1.4.7)

> **Théorème 1.4.7.** Les `[n/pʰ]!·(z choose n)` pour `n ∈ ℕ` forment une base orthonormale de
> `LA_h(ℤ_p, L)`. — `colmez.txt:634–635`

> **Lemme 1.4.5.** Les `e_{h,n}` pour `n ∈ ℕ` forment une base orthonormale de `LA_h(ℤ_p, L)`.
> Plus précisément, si `φ ∈ LA_h(ℤ_p,L)` et si `φ_i(x) = φ(−i + pʰx)`, alors `φ_i` est analytique
> sur `ℤ_p` … et `v_{LA_h}(φ) = inf_{n∈ℕ} v_p(α_{i(n),m(n)})`. — `colmez.txt:621–627`

Lemme 1.4.5 says exactly that `LA_h(ℤ_p, L) ≅ c(ℤ/pʰ × ℕ, L)` as a normed space, with the sup of
the per-disc Taylor coefficients.  **That isomorphism is taken as the definition here** — the
disc model is `c(ZMod (p^h) × ℕ, K)` and no separate space `LA_h` is constructed.  This is the
one place where the formalisation departs from the source's *presentation* (not its content); it
is recorded as design decision D1 in `plan.md` and is the reason Lemme 1.4.5 has no leaf.

**Leaves.**
* **AB-1 … AB-4** `revIdx` (`n ↦ ⌊n/q⌋q + (q−1−n mod q)`, an involution), `revIdx_apply`,
  `revIdx_div`, `revIdx_mod`.
* **AB-5 … AB-8** `discIdx` (`(a,k) ↦ k·pʰ + (pʰ−1−a)`), `discIdx_apply`, `discIdx_symm_apply`,
  `discIdx_res_div` (`discIdx (n mod pʰ, ⌊n/pʰ⌋) = revIdx (pʰ) n`).
* **AB-9** `discCoeff`; **AB-10** `lt_discIdx_iff` — the criterion matching group A's three cases.
* **AB-11** `colmezMatrix`; **AB-12** `isUnitriangularPerturbation_colmezMatrix` — the junction of
  groups A and U.
* **AB-13 … AB-14** `norm_comap_equiv`, `surjective_comap_equiv` — reindexing is isometric.
* **AB-15 … AB-21** `colmezToDisc`, `matrixCoeff_colmezToDisc`, `colmezToDisc_apply`,
  `norm_colmezToDisc`, `surjective_colmezToDisc`, `injective_colmezToDisc`, **`colmezDiscEquiv`**
  — Amice's theorem.
* **AB-22 … AB-24** `diagFactorialH`, `discToMahler`, `discToMahler_colmezToDisc`.
* **AB-25 … AB-31** `discCoord`, `coe_discCoord`, `appr_add_pow_mul_discCoord`, `appr_natCast`,
  `discCoord_natCast`, `discEval`, `discEval_colmezToDisc_natCast`,
  **`discToMahler_apply_eq_fwdDiff`**.

**Lean ↔ source match.**  Colmez's "triangulaire supérieure par blocs … chacun des blocs diagonaux
triangulaire inférieur" is a statement about the `pʰ × pʰ` block decomposition indexed by
`(m(n), i(n))`.  Linearising with `discIdx` — block index `k` outer, disc index `a` **reversed**
inner — turns "upper triangular by blocks, lower triangular within a block" into a single
lower-unitriangular condition, which is `IsUnitriangularPerturbation`.  `lt_discIdx_iff` is the
proof that the linearisation is faithful.

**Defect found and fixed during this pass.**  The first skeleton had
`discIdx_res_div : discIdx h (n mod pʰ, ⌊n/pʰ⌋) = n`, which is **false**: the left side is
`⌊n/pʰ⌋·pʰ + (pʰ − 1 − n mod pʰ)`, equal to `n` only when `2·(n mod pʰ) = pʰ − 1`.  The diagonal
of column `n` sits at position `revIdx (pʰ) n`, not `n`.  Fix: introduce `revIdx`, define
`colmezMatrix k n := ψ (discCoeff h (revIdx (pʰ) n) (discIdx⁻¹ k))`, and define `colmezToDisc` as
`comap discIdx ∘ ofPerturbation ∘ comap revIdx`.  The two reversals cancel, so
`matrixCoeff_colmezToDisc x n = ψ (discCoeff h n x)` — i.e. `colmezToDisc eₙ` is still the disc
model of `g_n` on the nose, which is what the seam (group SH) needs.  Verified by recomputing the
composite matrix coefficient by hand and re-compiling.

**Attacks attempted.**
1. *Is `discIdx` a bijection?*  `toFun (a,k) = k·pʰ + s` with `s = pʰ−1−a.val ∈ [0, pʰ−1]`, so it
   is divmod composed with the reversal `a ↦ pʰ−1−a` on residues, which is an involution of
   `Fin pʰ`.  **Survived.**
2. *Is the diagonal at `(n,n)`?*  **No** — see the defect above.  **Attack succeeded; plan
   corrected.**
3. *Does the column reindexing break `discToMahler_colmezToDisc`?*  No: `revIdx` preserves
   `⌊·/pʰ⌋` (AB-3), so `diag(⌊n/pʰ⌋!)` is unchanged under it; and the reversals cancel before
   `diagFactorialH` is applied anyway.  **Survived.**
4. *Is `natDegree_discPoly_le` enough for `col_finite`?*  `deg g_{n,a} ≤ n`, so column `n` of
   `colmezMatrix` is supported in `{k : ⌊k/pʰ⌋ ≤ revIdx n}`, a finite set.  **Survived.**
5. *Does `PadicInt.appr` have the API needed for AB-25 … AB-29?*  Verified present:
   `PadicInt.appr`, `appr_lt`, `appr_spec`, `appr_mono`, `dvd_appr_sub_appr`, and
   `PadicInt.denseRange_natCast`.  **Survived.**

### Group X — `PhD/LWX/PowSubOne.lean` (the extension formula and the threshold)

> "χ extends to a continuous homomorphism `κ : (ℤ_p + pᵐA°⟨z⟩)^× = ℤ_p^×·(1 + pᵐA°⟨z⟩) → (A°⟨z⟩)^×`,
> `a·x ↦ χ(a)·χ(exp(pᵐ))^{(log x)/pᵐ}`." — `lwx.txt:457–461`

> "Choose `m ∈ ℕ` such that `r < p^{−q/pᵐ(p−1)}` so that the universal character is `m`-locally
> analytic." — `lwx.txt:882`

**Leaves.**
* **X-1** `oneAddPow_natCast`; **X-2** `norm_choose_intHom_le_one`;
  **X-3** `continuous_oneAddPow_intHom` (`PadicInt.continuous_choose`, uniform convergence).
* **X-4** **`oneAddPow_pow_mul`**: `(1+T)^{pʰu} = ((1+T)^{pʰ})^u` for `u ∈ ℤ_p`.  This *is* the
  extension formula: `χ(exp(pᵐ)) = (1+T)^{p^{m−1}}` and the exponent `(log x)/pᵐ`.
  *Proof:* both sides are continuous in `u` (X-3) and agree on `ℕ` (X-1 + `pow_mul`); `ℕ` is
  dense in `ℤ_p` (`PadicInt.denseRange_natCast`), so `DenseRange.equalizer`.
* **X-5** `norm_choose_prime_pow_le` — Kummer: `v_p(C(pʰ,k)) = h − v_p(k)`, so
  `‖C(pʰ,k)‖ ≤ ‖p‖ʰ·k`.  *Discharge:* `Nat.emultiplicity_choose_prime_pow (hp) (hkn : k ≤ p^n) (hk0 : k ≠ 0)`
  (verified signature), `norm_natCast_eq_pow_padicValNat` (`PadicExpLog.lean:77`, takes `h3`),
  `Nat.ordProj_le`.
* **X-6** `exists_norm_pow_prime_pow_sub_one_le` — `‖(1+T)^{pʰ} − 1‖ ≤ ‖p‖ʰ·B`, `B = sup_k k‖T‖ᵏ`,
  finite because `‖T‖ < 1`.
* **X-7** `tendsto_pow_prime_pow_sub_one`; **X-8** **`exists_sq_norm_pow_prime_pow_sub_one_lt`** —
  `∃ h, ‖(1+T)^{pʰ} − 1‖² < p⁻¹`.

**The analyticity condition used here is stronger than LWX's, deliberately (BINDING).**  LWX's
`m`-local analyticity is `v(T_χ) > q/(pᵐ(p−1))`, i.e. `‖T₀‖ < p^{−1/(p^{m−1}(p−1))}`.  The
hypothesis carried through this board is `‖(1+T₀)^{pʰ} − 1‖² < p⁻¹` (`h = m − 1`), which forces
roughly `‖T₀‖ < p^{−1/(2pʰ)}` — strictly stronger for `p ≥ 3`.  The reason is that the character
is built from `padicExp`/`padicLog`, whose common convergence disc in the repo is `‖w‖² < ‖p‖`
(Koblitz, Ch. IV §1; `PhD/LWX/PadicExpLog.lean`), not the sharp `v(w) > 1/(p−1)`.  This is the
*same* gap the existing `m = 1` files already carry (`HaloWeight.lean` needs `‖T₀‖² < p⁻¹` where
LWX needs `‖T₀‖ < p^{−1/(p−1)}`), and LWX themselves flag the analogous slack at
`lwx.txt` §2.7 ("this is certainly not optimal").  It is harmless here **because the family of
levels is cofinal either way**: X-8 shows every halo point satisfies the stronger condition at
some `h`, so the corollaries (SH-9, SH-10, QH-3) are unaffected.  Sharpening `PadicExpLog` to the
`v(w) > 1/(p−1)` disc is listed under "deferred".

**Attacks attempted.**
1. *Is `‖(1+T)^{pʰ} − 1‖ ≤ ‖p‖ʰ·B` actually true for `‖T‖` close to 1?*  Checked numerically at
   `p = 3`, `‖T‖ = 3^{−0.1}`: the sequence of norms is `3^{−0.1}, 3^{−0.3}, 3^{−0.9}, 3^{−1.9},
   3^{−2.9}, …`, and `B = 3^{1.1}` works for all `h`.  The general bound follows from X-5 since
   `sup_k k‖T‖ᵏ < ∞`.  **Survived.**
2. *Is `‖T'_h‖ = ‖p‖ʰ‖T₀‖` (which would be simpler)?*  **False** near the outer edge: for
   `‖T₀‖ > p^{−1/(p−1)}` the term `T₀^p` dominates `pT₀`.  Only the inequality is claimed.
   **Attack succeeded against a simpler statement; the stated inequality survives.**
3. *Does X-4 need `‖T‖ < 1` or `‖T‖² < p⁻¹`?*  Only `‖T‖ < 1`, since it is the binomial series,
   not `exp`/`log`.  Confirmed the skeleton's hypotheses.  **Survived.**
4. *Is the density argument sound when `K` has positive residue characteristic?*  `DenseRange`
   of `ℕ → ℤ_p` is a statement about `ℤ_p`, independent of `K`; both sides are continuous
   `ℤ_p → K`.  **Survived.**

### Group WH — `PhD/LWX/HaloWeightH.lean` (the level-`h` halo weight)

Source: the same `lwx.txt:455–461` extension formula, and `lwx.txt:610–613` for the level

> `{ (a b; c d) ∈ M₂(ℤ_p) | q | c, p ∤ d, and ad − bc ≠ 0 }`

which at level `h` becomes `p^{h+1} | c` (design decision D3: the conjugates of `M₁` by the disc
maps).

51 leaves, mirroring `PhD/LWX/HaloWeight.lean` (`h = 0`) declaration for declaration:
`Mh`/`M1Kh` and the level facts (WH-1 … WH-10); `haloUnitsH`, `repLift` and the residue facts
(WH-11 … WH-20); `TH`, `haloExponentH` and the analytic estimates (WH-21 … WH-28);
**`specialize_univChar_eq_padicExp`** (WH-29, the junction with X-4), `haloCharFunH` and its
multiplicativity/norm/`_psi` (WH-30 … WH-36); `haloCharH` (WH-37 … WH-39); `haloRhoH` and
`levelBounds_M1Kh` (WH-40 … WH-46); `haloColH`, its row decay, its evaluation,
**`haloWeightH`** and the automorphy factor (WH-47 … WH-51).

**Lean ↔ source match.** `haloCharFunH x = [r](T₀)·exp(s_h·log(x/ψ(r)))` where `r` is the residue
of `x` modulo `p^{h+1}` is literally `χ(a)·χ(exp(pᵐ))^{(log x)/pᵐ}` with `a = r`, `m = h+1`, once
WH-29 identifies `χ(exp(p^{h+1}))^{(log x)/p^{h+1}}` with `exp(s_h·log x)`.  `haloRhoH` is the
row-decay radius: the level-`h` analogue of `HaloWeight.haloRho = ‖T₀‖√p`, with `‖T₀‖` replaced by
`max(p^{−(h+1)}, ‖T'_h‖)` because the level's `c`-entry is now only `p^{−(h+1)}`-small.

**Attacks attempted.**
1. *Is `haloRhoH < 1` under `hT`?*  `haloRhoH = max(p^{−(h+1)}, ‖T'_h‖)·√p`.  `p^{−(h+1)}√p ≤
   p^{−1}√p = p^{−1/2} < 1` ✓, and `‖T'_h‖√p < 1` ⟺ `‖T'_h‖² < p⁻¹` ✓ = `hT`.  **Survived.**
2. *Is `p⁻¹ ≤ haloRhoH` (needed by `c_le`)?*  The level's `c`-bound is `p^{−(h+1)}`, and
   `p^{−(h+1)} ≤ haloRhoH` holds since `√p ≥ 1`.  The skeleton states `inv_pow_le_haloRhoH` with
   `p^{−(h+1)}`, not `p⁻¹` — checked, `levelBounds_M1Kh.c_le` uses the former.  **Survived after
   the statement was tightened.**
3. *Does `haloCharFunH_mul` need `hT`, or does `h1` suffice?*  It needs `hT`: multiplicativity
   goes through `padicExp_add`, whose hypothesis is `‖w‖² < ‖p‖`.  Present in the skeleton.
   **Survived.**
4. *Is `repLift` well defined — is the natural lift of a unit residue class a `p`-adic unit?*
   Yes: `r ∈ (ℤ/p^{h+1})ˣ` ⇒ `p ∤ r.val` ⇒ `‖(r.val : ℤ_p)‖ = 1`.  **Survived.**
5. *Is `Mh p 0 = M1 p` (so `h = 0` really recovers the existing file)?*  Stated as `Mh_zero`;
   the carriers are syntactically the same with `(p⁻¹)^1 = p⁻¹`.  **Survived** — and SH-11
   pins the compatibility down.

### Group D — `PhD/LWX/DiscModel.lean` (the disc action)

> "Similar to (2.3.1), sending `f` to `h(z) = f((1 0; qz 1))` induces an isomorphism
> `Ind_{B(ℤ_p)}^{Iw_q}(χ)^{m,an} ≅ OB_{qp^{−m}} ⊗̂ A`.  Here the latter space may be understood as
> the subspace of continuous functions `h ∈ C(ℤ_p; A)` such that `h` is analytic on
> `a + q⁻¹pᵐℤ_p` for all `a ∈ ℤ_p`." — `lwx.txt:632–639`

> "The condition that `χ` is `m`-locally analytic is used so that the action (2.3.2) is well
> defined." — `lwx.txt:630–631`

**The key construction (design decision D3).**  Write `t_a(w) = a + pʰw`, i.e. the matrix
`t_a = (pʰ a; 0 1)`.  For `δ ∈ M₁` and a disc `a`, put `a' = möb δ (a) mod pʰ` (`discImage`).
Then `t_{a'}⁻¹·δ·t_a` is integral with `c`-entry `δ₁₀·pʰ` and `d`-entry `δ₁₀a + δ₁₁`, i.e. it lies
in `M_h` (`discConj`, `discConjMat_mem_Mh`); explicitly

```
δ' = ( δ₀₀ − a'δ₁₀ ,  (δ₀₀a + δ₀₁ − a'(δ₁₀a + δ₁₁))/pʰ ;  δ₁₀pʰ ,  δ₁₀a + δ₁₁ ).
```

Its `b`-entry is integral **exactly because** `a'` was chosen as the residue of `möb δ (a)`:
`δ₀₀a + δ₀₁ − a'(δ₁₀a + δ₁₁) = (δ₁₀a + δ₁₁)·(möb δ (a) − a')` has norm `≤ p^{−h}`.  Hence
`möb δ (a + pʰw) = a' + pʰ·möb δ' (w)` (`mobiusFun_add_pow_mul`): the action carries the Taylor
expansion on disc `a'` to the one on disc `a`, through the *single-disc* weight action of `δ'` at
the level `M_h`.  That is `AnalyticWeight.kappaSlash` at `haloWeightH` — so the disc action is a
`blockOp` of `kappaSlash`s permuted by `discImage`.

**Leaves.** D-1 … D-9 (`discImage`, `discConjMat`, `discConjMat_mem_Mh`, `discConj`, `discConjK`,
`denUnit_discConj`, `mobiusFun_add_pow_mul`, `toZModPow_mobiusFun`); D-10 … D-13 (the cocycle:
`discImage_one`, `discConj_one`, `discImage_mul`, `discConj_mul`); D-14 … D-20 (`discSlash`,
`matrixCoeff_discSlash`, `blockProj_discSlash`, `discSlash_one`, `discSlash_mul`,
`discSlashAction`, `discSMulSlashClass`, `isCompactoid_discSlash`); D-21 … D-22
(`evalAt_mk_kappaSlash`, **`discEval_discSlash`**).

**Lean ↔ source match.**  `discEval_discSlash` is `(2.3.2)` verbatim:
`(f ∣ δ)(z) = [cz + d](T₀)·f(möb δ (z))` for every `z ∈ ℤ_p`.  Note the automorphy factor is the
*unconjugated* `cz + d`, because `denUnit_discConj` says `c'w + d' = c(a + pʰw) + d`, i.e. the
denominator is disc-independent.  That is the technical heart of D.

**Attacks attempted.**
1. *Is `discConj` exactly `t_{a'}⁻¹δt_a`, or only up to a scalar?*  Exactly:
   `t_{a'} = (pʰ a'; 0 1)` has `det = pʰ` and adjugate `(1 −a'; 0 pʰ)`, so
   `t_{a'}⁻¹ = (1/pʰ)(1 −a'; 0 pʰ)` and the displayed `δ'` is that product.  Since the inverse is
   exact (not projective), the cocycle `discConj (δ₁δ₂) a = discConj δ₁ (discImage δ₂ a)·discConj δ₂ a`
   is an equality of matrices, not merely of Möbius maps.  **Survived** (an earlier draft used
   the adjugate without dividing, which would have made the cocycle off by `pʰ`).
2. *Is `discImage` a right action (`discImage (δ₁δ₂) = discImage δ₁ ∘ discImage δ₂`)?*  Follows
   from `möb (δ₁δ₂) = möb δ₁ ∘ möb δ₂`, which is the repo's convention — verified against the
   `slash_mul` proof of `cfunSlashAction` (`IntegralModel.lean:672–680`, uses `mobius_cocycle`).
   **Survived.**
3. *Does `discSlash` compose in the right order?*  `discSlash (δ₁δ₂) = discSlash δ₂ ∘ discSlash δ₁`,
   matching `AnalyticWeight.kappaSlash_mul (g h : S) : kappaSlash (g*h) = (kappaSlash h).comp (kappaSlash g)`.
   Verified against `Char.lean:826`.  **Survived.**
4. *Is `‖δ'₀₀‖ ≤ p⁻¹` when `‖δ₀₀‖ ≤ p⁻¹` (needed for compactoidness)?*
   `δ'₀₀ = δ₀₀ − a'δ₁₀`, and `‖a'δ₁₀‖ ≤ p⁻¹` since `‖δ₁₀‖ ≤ p⁻¹` and `‖a'‖ ≤ 1`.  Ultrametric ⇒
   `‖δ'₀₀‖ ≤ p⁻¹`.  `isCompactoid_discSlash` is stated with `σ = max ρ p⁻¹`.  **Survived.**
5. *Could the `b`-entry fail to be integral for some `δ ∈ M₁`?*  Only if `a'` were not the residue
   of `möb δ (a)`.  The definition of `discImage` forces it.  **Survived** — this is precisely why
   `discImage` must be defined by `toZModPow ∘ möb`, not by any other formula.

### Group DF — `PhD/LWX/DiscForms.lean` (`S^{D,†,m}` and `U_p`)

> `S^{D,†,m}_χ := { φ : D^×\(D ⊗ 𝔸_f)^×/K^p → Ind_{B(ℤ_p)}^{Iw_q}(χ)^{m,an} | φ(xu_p) = φ(x)‖^χ_{u_p},
> for u_p ∈ Iw_q }` — `lwx.txt:686–692`

Nine leaves, each a transcription of the corresponding declaration in
`PhD/QMF/Weight/{Forms,Compact,Fredholm}.lean` with `c(ℕ,K)` replaced by `c(ℤ/pʰ × ℕ, K)` and
`kappaSlash` by `discSlash`: `discLevelSMulSlashClass`, `mem_discForms_iff`, `discEvalAtReps`
(`map_add'`, `map_smul'`), `blockProj_discEvalAtReps`,
`bijective_discEvalAtReps_of_stabilizer_eq_bot`, `discEvalAtReps_discHeckeOperator`,
`isCompactoid_discHeckeBlockOp`, `evalT_discHeckeCharPowerSeries_eq_zero_iff`.

*Discharge:* `AbstractHeckeOperatorSlash.{slashFixedPointsOfLE, heckeOperatorSlash,
heckeOperatorSlash_apply_rep, bijective_evalAtRepsSlash, stabilizerAtSlash}` (verified
signatures), `RightSlashAction.comap` (`SlashAction.lean:893`), `TateFredholm.{blockOp,
isCompactoid_blockOp, charPowerSeries, evalT_charPowerSeries_eq_zero_iff}`.

**Attacks attempted.**
1. *Do these need `κ` to be `haloWeightH`, or any `AnalyticWeight` at `M1Kh`?*  Any — the group is
   stated for a general `κ : AnalyticWeight UK (M1Kh h ψ) ρ`.  Confirmed by compiling.
   **Survived.**
2. *Is the level monoid `levelM1 θ` (integral) the right one, or should it be `levelMonoidOf`?*
   Integral: `discSlash` consumes `δ : M1 p` over `ℚ_p`, so the level pulls back along
   `levelM1ToM1`.  This is *simpler* than the `m = 1` case, which had to cross the `ψ` seam.
   **Survived.**
3. *Is `charPowerSeries` defined for the index type `ι × (ℤ/pʰ × ℕ)`?*  `charPowerSeries` is
   stated for `c(I,R)` with `[DecidableEq I]`; the instance exists.  Confirmed by compiling.
   **Survived.**

### Group SH — `PhD/LWX/SeamH.lean` (the milestone)

Quotes: the Prop 2.17 statement and proof at `lwx.txt:966–1010` (Step 1 above), and

> "But [Bu04, Lemma 4] says that the characteristic power series for the `U_p`-action on the space
> of overconvergent automorphic forms does not depend on this general flexibility."
> — `lwx.txt:735–737`

> "By [Bu04, Lemma 4], `Char(U_p; S^{D,†,m}_{[−]≤r})` and hence `Spc^{≤r}_D` does not depend on the
> choice of `m`, and it is compatible as `r` varies." — `lwx.txt:888–891`

**Leaves.** SH-1 `entry_eq_fwdDiff` (the *binomial* form of the entry stream — the `m = 1` seam
used the monomial form `fwdDiff_iter_cfunSlash_pow`, which is public, whereas the binomial form is
`private` in `IntegralModel.lean:1160`, so it must be restated here); SH-2
`specialize_entry_eq_fwdDiff`; SH-3 `discEval_colmezToDisc_single`; **SH-4**
`discToMahler_comp_discSlash`; SH-5 … SH-8 the blockwise transcription
(`matrixCoeff_diagFactorialHBlock` and the two `_comp` variants, `discToMahlerBlock_eq`,
`discToMahlerBlock_comp_discHeckeBlockOp`, `diagFactorialHBlock_comp_colmezConj`,
`isCompactoid_discHeckeBlockOp_haloWeightH`); **SH-M**
`specCharSeries_ofCerts_eq_discHeckeCharPowerSeries`; SH-9
`discHeckeCharPowerSeries_eq_of_levels`; SH-10
`exists_level_specCharSeries_eq_heckeCharPowerSeries`; SH-11
`discHeckeCharPowerSeries_zero_eq_heckeCharPowerSeries`.

**Lean ↔ source match.**  SH-M is the displayed conclusion "`Char(U_p; S^{D,†,m}_{[−]_m}) =
det(I∞ − XP′) = det(I∞ − XP)`", with `det(I∞ − XP)` = `specCharSeries` (already defined,
`Halo.lean:157`) and `Char(U_p; S^{D,†,m})` = `discHeckeCharPowerSeries`.  `diag(⌊n/pʰ⌋!)` is
LWX's "infinite diagonal matrix with diagonal entries `1,…,1, …, ⌊n/(q⁻¹pᵐ)⌋!, …`".  SH-9 is
[Bu04, Lemma 4] as *used* by LWX (independence of `m`), obtained for free because both sides equal
`specCharSeries` of the same certificate datum — note this proves the instance of Bu04's lemma
that Def 2.13 needs, **not** Bu04's lemma in its full generality (`α`, `β` independent).

**Attacks attempted.**
1. *Does SH-4 hold on all of `c(ℤ/pʰ × ℕ, K)`, or only on the Colmez basis?*  Both sides are
   continuous linear and `colmezDiscEquiv` is an isomorphism, so checking on
   `colmezToDisc (single n 1)` for all `n` suffices.  **Survived.**
2. *Is `entry_eq_fwdDiff` really needed, or does the monomial form suffice?*  Needed: the Colmez
   basis is `⌊n/pʰ⌋!(z choose n)`, so `discEval` of a basis vector produces `Ring.choose (möb z) n`,
   not `(möb z)^n`.  The `m = 1` seam got away with monomials because it went through
   `monomialToMahler`; there is no such route here.  **Survived** (and this is why SH-1 exists).
3. *Is the diagonal `⌊n/pʰ⌋!` a unit in `K` (needed by `charPowerSeries_eq_of_diag_intertwine`)?*
   It is a nonzero natural number cast into a field of characteristic zero.  The `m = 1` proof
   uses exactly this (`Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)`).  **Survived.**
4. *Does `charPowerSeries_conj` allow the index type to change from `ι × (ℤ/pʰ × ℕ)` to `ι × ℕ`?*
   Verified: `charPowerSeries_conj [IsTate R] {J} [DecidableEq J] (φ : c(I,R) ≃L c(J,R)) (u) (hu)`
   (`Fredholm.lean:977`).  **Survived.**
5. *Is SH-11 (`h = 0` recovers `Seam.lean`) actually provable, or is it a definitional trap?*  It
   requires `Mh p 0 = M1 p` and `haloWeightH 0 = haloWeight` up to the level identification, plus
   the `ψ`-seam that `Seam.lean` crosses and `DiscForms` does not.  It is stated as a *corollary*
   with its own ticket and is the only leaf here where a defeq mismatch is plausible; if it turns
   out to need a transport lemma, that is a sub-ticket, not a defect.  **Survived, flagged as the
   riskiest leaf in the group.**

### Group QH — `PhD/LWX/QuaternionicH.lean`

Quotes: `lwx.txt:672–680` (§2.4, `D/ℚ` split at `p`, tame level `K^p`, neatness) and
`lwx.txt:879–891` (Definition 2.13).

Three leaves: **QH-M** `specCharSeries_ofCerts_eq_discHeckeCharPowerSeriesQ`,
**QH-2** `evalT_specCharSeries_eq_zero_iff_disc`, **QH-3**
`exists_level_evalT_specCharSeries_eq_zero_iff`.

**Attacks attempted.**
1. *Does QH need the `padicComparison` transport that `Quaternionic.lean` needed?*  Only for the
   coefficients (`ψ = padicComparison p`), not for the level — `thetaInt` is already valued in
   `M₂(ℚ_p)` and `DiscForms` takes that directly.  So QH-M is a direct instantiation of SH-M.
   **Survived** (and this is a genuine simplification over the `m = 1` file).
2. *Is `isUpShape_certM1` applicable with the same hypotheses?*  Verified signature
   `isUpShape_certM1 θ U hU vRep hvΔ u hη hηa hv`; the inputs `etaAdelic'_mem_levelM1` and
   `norm_thetaInt_etaAdelic'_zero_zero` already exist in `Quaternionic.lean`.  **Survived.**
3. *Is QH-3 vacuous (does the `∃ h` escape into a trivial statement)?*  No: the witness `h` comes
   from X-8 and the conclusion is a genuine iff at that `h`; combined with SH-9 the choice of `h`
   is immaterial.  **Survived.**

---

## Step 5 — Confidence gate

| Condition | Verdict |
|---|---|
| Every leaf has a source locator or is explicitly infrastructure | ✓ (groups U, BM, DF are infrastructure/transcription; all others carry `lwx.txt`/`colmez.txt` locators) |
| Every leaf has a verbatim source quote where it claims to follow a source | ✓ |
| Every "discharged by mathlib lemma X" claim was checked by grep/signature | ✓ — two citations were **wrong** and were corrected (`Nat.count_modEq_card` does not exist; `padicValNat_factorial`'s hypothesis is `Nat.log p n < b`) |
| No leaf is false | ✓ after one correction: my own `discIdx_res_div` (the diagonal is at `revIdx n`, not `n`).  A second suspected defect — an off-by-one in Colmez's `m(n)` — was withdrawn: it was my arithmetic slip, and the paper is correct |
| No leaf needs substantial mathlib-absent infrastructure beyond what is planned | ✓ — the only genuinely new mathematics is Amice's theorem (groups A + AB + U), which is the declared goal, not a surprise |
| The Lean skeleton compiles | ✓ `lake build`, 3730 jobs, sorries only |
| Estimates grounded in line counts actually read | ✓ — sizes below are scaled from the existing `m = 1` analogues, which were read |

**Feasibility.**  The board is feasible.  Groups U, BM, DF, QH are transcription of existing repo
patterns (roughly 40% of the leaves and 20% of the effort).  Groups D and WH are mirrors of
`Seam.lean`/`HaloWeight.lean` with one new idea each (the conjugation identity; the binomial power
identity), both of which have been checked by hand.  Groups A and AB are the genuinely new
mathematics — Colmez's Lemme 1.4.9 and Théorème 1.4.7 — and are the single largest risk; the two
worked numerical examples above and the `IsUnitriangularPerturbation` criterion reduce that risk
to ordinary combinatorial bookkeeping over `padicValNat`.  Group SH is four lines of algebra on
top of infrastructure that already exists and is sorry-free.

---

## Prior-`B2` consultation

* Root log `.mathlib-quality/b2_log.jsonl`: entries concern `NewtonPolygon` height/support
  statements.  **No match** — different area, no statement in this board resembles them.
* `.mathlib-quality/lwx-halo/b2_log.jsonl`: entries concern `T`-rescaled Mahler transport (a
  route abandoned in favour of the integral halo ring).  **No match** — this board does not
  rescale by `T`; the disc model's Taylor coordinates are unrescaled and the only diagonal is
  `⌊n/pʰ⌋!`.
* `.mathlib-quality/lwx-seam/b2_log.jsonl`, `.mathlib-quality/tate-riesz/b2_log.jsonl`: empty at
  the time of writing.
* This board's own `b2_log.jsonl` is empty.

---

## Deferred (not tickets)

1. Sharpen `PhD/LWX/PadicExpLog.lean` from the `‖w‖² < ‖p‖` disc to the sharp `v(w) > 1/(p−1)`,
   which would replace `hT : ‖T'_h‖² < p⁻¹` by LWX's exact `m`-local analyticity condition and
   make `HaloWeight.lean`'s `h1` match the paper.  Affects this board and `lwx-halo`.
2. Merge `PhD/LWX/HaloWeight.lean` into `HaloWeightH.lean` as the `h = 0` case, once SH-11 shows
   the two agree.  Deliberately not done during this board: `HaloWeight.lean` is a dependency of
   the completed `lwx-seam` and `lwx-slopes` boards.
3. `p = 2` (LWX require `m ≥ 2`; `PadicExpLog` requires `p ≠ 2` throughout the repo).
4. Colmez's Corollaire 1.4.8 (`φ` locally analytic ⟺ `liminf (1/n)v_p(a_n(φ)) > 0`) — not needed
   by Prop 2.17, but the natural next statement from the same page.
5. Weakening `IsUnitriangularPerturbation.col_finite` to a `Tendsto` hypothesis.
6. Rigid-analytic packaging of `OB_{qp^{−m}}` (LWX's `B_{qp^{−m}}` as a rigid space); the model
   here is the normed-space model only.
