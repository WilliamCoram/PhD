# Development Plan: test.lean refactor — blueprint §5.4–5.14 on the IsNewtonPolygonOf spec

Started 2026-08-03. Predecessor board (IsNewtonPolygonOf spec, completed same day) archived in
`archive-2026-08-newtonpolygon-spec/`.

## Goal

Re-derive the full mathematical content of `PhD/Test/test.lean` (blueprint §5.4–5.14: Newton
polygons of polynomials and power series over a complete ultrametric nontrivially-normed field,
through purity, factorisation at breaks, root counting, radius of convergence, Weierstrass
factorisation along the polygon, and power-series zero counting) in NEW files under
`PhD/NewtonPolygons/`, with the agreed statement discipline:

- **Workhorse lemmas** take a spec hypothesis: `(P : NewtonPolygon₀) (hP : IsNewtonPolygonOf
  (coeffVal f) P)` plus structure-data hypotheses on `P` where needed (first slope, first
  length, strictness `P.slopes 0 < P.slopes 1` for genuine-break facts).
- **Headline results** also get construction-applied corollaries about
  `newtonPolygon₀OfPowerSeries`, one line via `isNewtonPolygonOf_powerSeries`.
- Facts that are genuinely representation-dependent (touching, strict-after-break) are proved
  on the constructed polygon using the SpecConstruction walk layer, then transferred to
  arbitrary spec'd `P` via height-uniqueness (`IsNewtonPolygonOf.height_eq`) where a spec-level
  form is wanted.

**IMPORT POLICY (user-mandated, binding)**: new files import ONLY `Mathlib`,
`PhD.ForMathlib.*`, `PhD.NewtonPolygons.*`. Specifically forbidden: `PhD.Test.*`,
`PhD.LegacyCode.*` (= old ToPR), `PhD.WeierstrassPrep.*`, `PhD.BirkovichWP.*`.
`PhD/Test/test.lean` is reference-only (it no longer compiles — its imports moved to
LegacyCode/bad/).

## References

- **[BP]** `blueprint/src/chapter/NP.tex` §Properties (verbatim statements for 5.4–5.14).
- **[T]** `PhD/Test/test.lean` — the complete, formerly-sorry-free formalisation on deprecated
  APIs; the primary proof-route source. Line-anchored inventory in
  `.mathlib-quality/references/test-inventory.md` (Section map: 5.4 @392, 5.5 @1175, 5.6
  @420–626, 5.7 @627–1225, 5.8 @1226, 5.9 @1306, 5.10 @1351, 5.11 @1487–1920,
  radius infra @1969–2099, 5.12 @2100–2550, 5.13 @2551–3228, 5.14 @3229–3553.)
- Previous board's `decomposition.md` (archived) for the spec API's attack logs.

## Dependency map (inventoried 2026-08-03; all replacement files sorry-free)

| test.lean pillar | Replacement | Notes |
|---|---|---|
| ToPR.NewtonPolygon (algorithm) | `PhD.NewtonPolygons.{Height,Spec,SpecConstruction}` + `PhD.ForMathlib.NumberTheory.NewtonPolygon.*` | spec + walk layer + line bounds already proved |
| Test.addVals2 (valuation) | `PhD.ForMathlib.RingTheory.Valuation.AddVal.*`, `PhD.ForMathlib.Analysis.Normed.Ring.NegLogNorm`, `PhD.ForMathlib.Topology.Algebra.Valued.AddVal` | exact bridge names: see §Valuation bridge below (pending final inventory) |
| ToPR.GaussNorm | **Mathlib** `RingTheory/{Mv}PowerSeries/GaussNorm` + `PhD.ForMathlib.RingTheory.{PowerSeries,MvPowerSeries,Polynomial}.GaussNorm` | ⚠ never co-import `Mathlib.RingTheory.Polynomial.GaussNorm` (ForMathlib Polynomial/GaussNorm shadows it) |
| ToPR.Restricted | `PhD.ForMathlib.RingTheory.PowerSeries.Restricted.{Basic,GaussNorm,Complete,Units}` | `PowerSeries.IsRestricted c f`, ring `PowerSeries.Restricted R c` |
| WeierstrassPrep.WPrep_gen | `PhD.ForMathlib.RingTheory.PowerSeries.Restricted.{MulDistinguished,MulWeierstrassDivision,MulWeierstrassPrep}` (Martin §1.3) | `IsMulDistinguished c f s`; **`MemDivisibleValueGroup` hypothesis GONE** |
| Test.DivValueGroup | **obsolete** | delete all uses; `memDivisibleValueGroup_exp_slope`(′), `exists_memDivisibleValueGroup_between` are dead code — NOT ported |

Mechanical rename table (apply during porting):
`Restricted.norm_eq → Restricted.norm_def` (c explicit) · `Restricted.gaussNorm_achieved' →
Restricted.exists_achievesGaussNorm` · `Polynomial.toRestricted_mul/zero → map_mul/map_zero` ·
`local instance …normMulClass → (delete; global instance under [Fact (0 < c)])` ·
`[StrongPos …] → [Fact (0 < c)]` · `distinguishedGen → IsMulDistinguished` (field `unit`
becomes `isNormMulUnit_coeff`; over a field build via `norm_mul`) ·
`weierstrassPreparation_polynomial_divisible hdiv … → weierstrassPreparation_polynomial_of_isMulDistinguished`
(drop `hdiv`) · `dominant_const_of_isUnit_toRestricted → Restricted.norm_coeff_lt_norm_constantCoeff_of_isUnit`
+ 3-line polynomial wrapper (micro-gap G1) · `PowerSeries.le_gaussNorm norm c x` → insert
`HasGaussNorm` witness.

Micro-gaps to fill in-board (small lemmas, not sub-developments):
- **G1**: polynomial-flavoured `dominant_const_of_isUnit_toRestricted` wrapper (~3 lines).
- **G2**: `Restricted.C_isUnit` / `C_one` conveniences (`IsUnit.map (Restricted.C c)`, `map_one`).
- **G3**: everything `firstBreak`-flavoured — this board's actual subject.

## Valuation bridge (RESOLVED)

`PhD.ForMathlib.Analysis.Normed.Ring.NegLogNorm` provides `negLogNorm : E → WithTop ℝ`
(`[Norm E]`) with: `negLogNorm_zero : negLogNorm 0 = ⊤`, `negLogNorm_eq_top : = ⊤ ↔ r = 0`
(norm-faithful setting), `negLogNorm_of_ne_zero : r ≠ 0 → negLogNorm r = (-Real.log ‖r‖ : ℝ)`,
order-reversal `negLogNorm_le_negLogNorm : negLogNorm r ≤ negLogNorm s ↔ ‖s‖ ≤ ‖r‖` (+ strict),
`le_negLogNorm_add` (ultrametric), `add_negLogNorm_le_negLogNorm_mul`, `negLogNorm_mul`
(`[NormMulClass]`), `negLogNorm_one = 0`, `negLogNorm_nonneg_iff : 0 ≤ negLogNorm r ↔ ‖r‖ ≤ 1`.
The bridge def is `coeffVal (f : PowerSeries K) : ℕ → WithTop ℝ := coeffSeq negLogNorm f`.
Canonical base stays `e` ([T] lines 26–70 rationale). Admissibility: polynomials via a
`Finset.min'` affine floor; restricted series via the Gauss-norm bound
(`‖aₖ‖ cᵏ ≤ B ⟹ negLog aₖ ≥ k log c − log B`) through `isAdmissible_of_affine_bound`.

## File structure (all new, in PhD/NewtonPolygons/)

- `CoeffVal.lean` — valuation bridge for `K` nontrivially-normed ultrametric field: `coeffVal`,
  its API, admissibility lemmas, `isNewtonPolygonOf_coeffVal` (spec instance for polynomials /
  restricted series), the `a₀ = 1 ⇒ anchored at origin` normalisation lemmas.
- `FirstBreak.lean` — §5.4/5.5/5.6 + the break toolkit: `HasFirstBreak` (constructed-polygon
  first-segment data: `slopes 0 = m ∧ lengths 0 = i`), points-on/above-line (spec-level ≤ via
  `unitSlope_zero_mul_le`; construction-level strict via `nextStep_slope_lt`), touching,
  `IsPureSeries`, `isPureSeries_iff_distinguished` (5.6, target predicate now
  `IsMulDistinguished`), `distinguished_of_firstBreak`, `isPureSeries_of_irreducible` (5.5).
- `PolynomialRoots.lean` — §5.7–5.11: factorisation at the first break (Martin WP, no
  divisibility hypothesis), Gauss-norm bound below the first slope (5.8), no-zeros (5.9), root
  counting at the first slope (5.10) and along the whole polygon (5.11); roots measured in
  `AlgebraicClosure K` with an extending valuation `w`, exactly as [T].
- `RadiusOfConvergence.lean` — [T] 1969–2099 infra: `radiusOfConvergence`, restricted ↔
  summable, + §5.12 (`isRestricted_of_lt_slope`, `not_isRestricted_of_slopes_le`, the two
  radius halves).
- `PowerSeriesZeros.lean` — §5.13 (`exists_weierstrass_factorisation` along the polygon) and
  §5.14 (zero counting via `HasSum` over a complete ultrametric extension `L`), as in [T]
  2551–3553.

Import DAG: CoeffVal → FirstBreak → PolynomialRoots → {RadiusOfConvergence → PowerSeriesZeros}.

## Statement-shape decisions (binding for the decomposition)

1. Spec-hypothesis form for geometry consumed downstream; hypotheses on `P`'s structure data
   (`slopes 0`, `lengths 0`) plus `P.slopes 0 < P.slopes 1` wherever "genuine first break" is
   mathematically required (collinear-split representations make it necessary — recorded
   attack, previous board L2).
2. Applied corollaries on `newtonPolygon₀OfPowerSeries (negLog…) f` for every blueprint-numbered
   result.
3. [T]'s hypotheses carry over: `a₀ = 1` normalisation, `0 < natDegree`, `[CompleteSpace K]`
   where Weierstrass enters, `hdense`/infinite-support caveats in 5.12 — MINUS every
   `MemDivisibleValueGroup`/density hypothesis (obsolete).
4. Deletions vs [T]: `memDivisibleValueGroup_exp_slope`(′), `exists_memDivisibleValueGroup_between`,
   the `exists_factor_aux` divisible-group plumbing — not ported. 5.7's proof simplifies:
   Martin WP applies at radius `exp m` directly.

## Generality decisions

- Base field: `[NontriviallyNormedField K] [IsUltrametricDist K]` (+ `[CompleteSpace K]` from
  5.7 on), matching [T]. Roots in `AlgebraicClosure K` with `w : Valuation … ℝ≥0` extending the
  norm (5.7–5.11); abstract complete ultrametric `L` for 5.12–5.14, matching [T]'s design notes.
- Polygon side stays Γ-generic only where free; the bridge fixes Γ = ℝ.

## Execution

Same pattern as the previous board: `/beastmode`, parallel workers per file, cleanup cadence
(per-file golf after every ~3 proof tickets, merged where adjacent), endpoint axiom checks.
ChatGPT MCP not configured — validation step skipped.
