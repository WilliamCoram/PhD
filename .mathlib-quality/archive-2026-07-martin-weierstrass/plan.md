# Development Plan: Martin's Weierstrass division & preparation in full generality

## Goal

Formalise §1.3 of [Mar16] at its stated generality — an **arbitrary ultrametric complete
normed (commutative) ring `A`** and an **arbitrary radius `r > 0`** — in a new folder
`PhD/Martin/`:

* **Proposition 1.27 (Weierstrass division).** For `g ∈ A{r⁻¹T}` `T`-distinguished of
  order `s` (Def 1.24: `g_s` a *multiplicative unit*, `‖g_s‖rˢ = ‖g‖`, strict Gauss-term
  dominance for `n > s` only), every `f` has a unique decomposition `f = gq + R` with
  `deg R < s`, and `‖f‖ = max(‖g‖‖q‖, ‖R‖)`.
* **Corollary 1.28 (Weierstrass preparation).** Such `g` factors uniquely as `g = e·w`,
  `w` monic of degree `s`, `e` a multiplicative unit of `A{r⁻¹T}`.

Main Lean statements (endpoints, in `PhD/Martin/`):

```lean
theorem PowerSeries.Restricted.weierstrassDivision_exists_of_isMulDistinguished
    [NormedCommRing A] [IsUltrametricDist A] [CompleteSpace A] {c : ℝ} [Fact (0 < c)]
    {g : Restricted A c} {s : ℕ} (hg : IsMulDistinguished c g.1 s) (f : Restricted A c) :
    ∃ (q : Restricted A c) (r : Polynomial A), r.degree < s ∧
      f = g * q + Polynomial.toRestricted c r

theorem PowerSeries.Restricted.weierstrassPreparation_exists_of_isMulDistinguished
    [NormedCommRing A] [IsUltrametricDist A] [CompleteSpace A] [NormOneClass A]
    {c : ℝ} [Fact (0 < c)] {g : Restricted A c} {s : ℕ}
    (hg : IsMulDistinguished c g.1 s) :
    ∃ (ω : Polynomial A) (e : Restricted A c), ω.Monic ∧ ω.degree = s ∧
      ‖Polynomial.toRestricted c ω‖ = c ^ s ∧ IsNormMulUnit e ∧
      g = e * Polynomial.toRestricted c ω
```

plus norm equality (his (1.8)), q/r-uniqueness, and `[NormMulClass A]` bridge corollaries
showing these subsume the project's oracle-free statements.

## References

- **[Mar16]** F. Martin, *Overconvergent subanalytic subsets in the framework of
  Berkovich spaces*, J. EMS 18 (2016), 2405–2457, §1.3. Local copies:
  `.mathlib-quality/references/martin-overconvergent-subanalytic.pdf` and text extraction
  with line anchors `.mathlib-quality/references/martin-sec1.3.txt` (Def 1.20 @ :47,
  Lemma 1.21 @ :50, Remark 1.22 @ :57, Def 1.24 @ :95, Lemma 1.26 @ :110,
  Prop 1.27 @ :141, Cor 1.28 @ :221). Every leaf of the decomposition quotes this text.
- Lang, *Algebra*, §IV.1 (Euclidean division by a polynomial with invertible leading
  coefficient) — cited by Martin as [Lan02, 4.1.1].

## Mathlib/project inventory

| Concept | Status | Action |
|---------|--------|--------|
| `A{r⁻¹T}` with Gauss sup norm | project: `PowerSeries.Restricted A c` (`[NormedRing]`/`[NormedCommRing] [IsUltrametricDist]`, `[Fact (0 < c)]`) | USE |
| Completeness of `A{r⁻¹T}` | project: `CompleteSpace (Restricted R c)` (Complete.lean:65, from Mv) | USE |
| `NormOneClass`, `IsUltrametricDist` instances for `Restricted` | project (GaussNorm.lean:278/285, from Mv) | USE |
| Gauss-term attainment | project: `Restricted.exists_coeff_ne_zero_norm_eq` (GaussNorm.lean:213) | USE |
| Coefficient bound `‖f_n‖cⁿ ≤ ‖f‖` | project: `norm_coeff_mul_pow_le` (GaussNorm.lean:220) | USE |
| Dominant achieving pair | project: `exists_achievesGaussNorm_dominant_max` (GaussNorm.lean:188, NormMulClass-free) | USE |
| Polynomial embedding + norm | project: `Polynomial.toRestricted`, `norm_toRestricted` (GaussNorm.lean:335+), `toRestricted_injective` | USE |
| `divisionAddSubgroup`, `coeff_continuous`, `isClosed_setOf_coeff_eq_zero` | project WeierstrassDivision.lean:185–223, all `omit [NormMulClass R]` | USE |
| Norm-equality/bounds/uniqueness for division | project WeierstrassDivision.lean:58–147 — **requires `[NormMulClass R]`** | RE-DERIVE under Martin's weaker hypothesis (this is Lemma 1.26's role) |
| `isClosed_divisionSet`, `exists_toRestricted_eq_of_coeff_eq_zero` | project, but NormMulClass-bound resp. `private` | RE-DERIVE in Martin folder (same proofs, Martin bounds; note dedup for future PR) |
| Truncation | mathlib `PowerSeries.trunc`, `coeff_trunc` (Trunc.lean:63), `degree_trunc_lt` (Trunc.lean:87) | USE |
| Euclidean division by monic | mathlib `Polynomial.modByMonic_add_div` (Div.lean:259), `degree_modByMonic_lt` (Div.lean:147), `monic_C_mul_of_mul_leadingCoeff_eq_one` (Monic.lean:60) | USE |
| `1 − t` invertible, `‖t‖ < 1`, complete ring | mathlib `Units.oneSub` (Analysis/Normed/Ring/Units.lean) | USE |
| Geometric Cauchy sequences | mathlib `cauchySeq_of_le_geometric` (SpecificLimits/Basic.lean:528) | USE |
| Multiplicative unit (Def 1.20) | **not in mathlib, not in project** | DEFINE `IsNormMulUnit` + API |
| `T`-distinguished, Martin form (Def 1.24) | project has `IsDistinguished` (plain `IsUnit` coeff) | DEFINE `IsMulDistinguished` + bridge |

## File structure (all new code in `PhD/Martin/`)

- `PhD/Martin/NormMulUnit.lean` — `IsNormMulUnit` (Def 1.20), Lemma 1.21 characterisation,
  inverse/product/one lemmas, Remark 1.22 (`1 + small`), `NormMulClass` bridge.
- `PhD/Martin/Distinguished.lean` — `IsMulDistinguished` (Def 1.24), `toIsDistinguished`,
  `NormMulClass` iff, greatest achieving index, truncation lemmas, **Lemma 1.26** (both parts).
- `PhD/Martin/WeierstrassDivision.lean` — norm equality (1.8), bounds, uniqueness,
  polynomial Euclidean step, one-step approximate division (1.11), density, closedness,
  **Proposition 1.27**.
- `PhD/Martin/WeierstrassPrep.lean` — quotient-unit chain, **Corollary 1.28**
  (existence + uniqueness), `NormMulClass` bridge corollaries.

Imports flow: `NormMulUnit ← Distinguished ← WeierstrassDivision ← WeierstrassPrep`;
`Distinguished` imports the project's `PowerSeries/Restricted/Distinguished.lean`;
`WeierstrassDivision` imports the project's engine file for the reusable
NormMulClass-free machinery. New code only in `PhD/Martin/` (user requirement); existing
files are not modified.

## Dependency graph

```
IsNormMulUnit API ──→ IsMulDistinguished ──→ Lemma 1.26(2) ──→ Lemma 1.26(1)
                                     │                 │
                    greatest-index, trunc lemmas       ▼
                                     │        norm equality (1.8) ──→ bounds ──→ uniqueness
                                     ▼                 │                  │
                        Euclidean step ──→ one-step (1.11) ──→ density ──┐│
                                                       closedness ───────┼┴→ Prop 1.27 (division)
                                                                          │
                       quotient-unit chain (needs 1.26(2), 1.22, division)┴→ Cor 1.28 (preparation)
                                                                          → NormMulClass bridges
```

## Generality decisions

- `A`: `[NormedCommRing A] [IsUltrametricDist A]` — Martin's "ultrametric complete normed
  ring" per BGR 1.2.1.1 conventions (commutative with 1; `norm_mul_le` is mathlib's
  `NormedRing` axiom). `CompleteSpace A` only where the source needs it (existence,
  Remark 1.22); norm-equality and uniqueness are completeness-free — *more precise than
  the source*, which assumes completeness globally.
- `NormOneClass A` only where `‖1‖ = 1` is genuinely used (Lemma 1.21 forward direction,
  Remark 1.22, preparation). Not needed for division existence/uniqueness.
- Radius: `{c : ℝ} [Fact (0 < c)]` — arbitrary positive real, project convention.
- `IsNormMulUnit` stated over `[NormedRing A]` (no commutativity) with left
  multiplicativity, matching how it is consumed; the Weierstrass files use
  `NormedCommRing` (Martin's setting; the preparation rearrangement `g = w q⁻¹ = q⁻¹ w`
  is genuinely commutative).
- Names carry the `_of_isMulDistinguished` suffix to avoid clashing with the project's
  `NormMulClass` versions in the same `PowerSeries.Restricted` namespace; on a future
  mathlib PR the Martin versions are the strictly more general ones and would take the
  plain names.
- Omitted from scope (not needed for 1.27/1.28): Martin's Remark 1.23 (contractive
  morphisms preserve multiplicative units), Lemma 1.29 (Noetherian coefficient
  decomposition — belongs to his §1.4), and the multivariate iteration remark (already
  covered by the project's Mv development).

## ChatGPT validation

`ask_chatgpt_math` not configured in this session — skipped per command spec.
