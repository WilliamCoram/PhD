# Development Plan: LWX slopes near the boundary (coefficient-level Tier 2)

**BOARD PATH: `.mathlib-quality/lwx-slopes/`** — named board.  The default `.mathlib-quality/`
root belongs to the (completed) NewtonPolygons project and must not be touched; the sibling
board `.mathlib-quality/lwx-halo/` (Tier 1) is the upstream of this one and is *not* edited
here.  Every `/beastmode` invocation for this project must name this path.

Planned 2026-09-05.  Source: Liu–Wan–Xiao, *The eigencurve over the boundary of weight
space* (arXiv:1412.2584v4, November 2016 version; a copy is in the user's possession as
`~/Desktop/Papers/Liu, Wan, Xiao - The eigencurve over the boundary of weight space.pdf`;
cite as [LWX]; page numbers are the printed ones, which coincide with the PDF page numbers).
Secondary locators `lwx.txt:NNNN` refer to the `pypdf` text extraction of that PDF (36 pages;
regenerate with `pypdf.PdfReader(...).pages[i].extract_text()`, one `===== PDF PAGE i =====`
banner per page).

## Goal

The coefficient-level content of [LWX, §3.23–§4.2] on top of the Tier-1 outputs
(`PhD/LWX/Halo.lean`: Theorem 3.16 as `norm_charCoeff_upOp_le`, Corollary 3.18's inequality
as `norm_specCharSeries_coeff_le` / `isBelow_newtonPolygon_specCharSeries`), for an odd
prime `p`, any `UpDatum` on a class set `ι` with `t = |ι|`, and any halo specialization
`ψ : ℤ_p → K`, `p⁻¹ < ‖T₀‖ < 1`:

1. **Corollary 3.18, the sharpness clauses** (unconditional): `v(c_n(T₀)) = λ(n)·v(T₀)` iff
   `b_{n,λ(n)} ∈ ℤ_p^×`, and the margin `v(c_n(T₀)) ≥ λ(n)v(T₀) + min{v(T₀), 1 − v(T₀)}`
   otherwise.  (`Sharpness.lean`.)
2. **Lemma 4.1** (unconditional, pure combinatorics): the upper bound polygon (vertices
   `(n_k, λ(n_k))`, `n_k = kpt`) lies above the lower bound polygon by at most `(p²−1)t/8`
   (in `v(T)`-units), with `λ(n_k) = k²p(p−1)t/2` [(3.23.1)] and the band identities of
   [LWX, p. 25].  (`UpperPolygon.lean`.)
3. **The Claim of §4.2** (unconditional): for `T₀` in the small annulus
   `0 < v(T₀) < 8/((p²−1)t+8)`, a coefficient `c_l` whose point lies strictly below the upper
   bound polygon has `v(c_l(T)) = m(l)·v(T)` at every such `T`, with `m(l)` = the least unit
   index of `c_l` — `T`-free.  (`Claim.lean`.)
4. **Theorem 1.3, Step II, and Theorem 1.5, first half** — both **conditional on the touching
   hypothesis** `HasUnitBand D ω k` (unit coefficients `b_{n,λ(n)}` in `[n_k − t, n_k]` and in
   `[n_k, n_k + t]`; the `T`-free form of what Step I extracts from Atkin–Lehner theory and
   classicality, which stay out of scope):
   * Step II at every halo point: `(n_k^−, λ(n_k^−)v(T))`, `(n_k^+, λ(n_k^+)v(T))` are
     consecutive vertices of the Newton polygon joined by the segment of slope `kφ(q)v(T)`
     through `(n_k, λ(n_k)v(T))`; the slope reading `unitSlope_specCharSeries_eq_iff` /
     `_mem_Ioo` (the polygon-level `X_k` / `X_{(k,k+1)}` statement of Theorem 1.3 with
     `deg X_k = n_k^+ − n_k^−`, `deg X_{(k,k+1)} = n_{k+1}^− − n_k^+`), and the bridge
     `hasUnitBand_of_height_eq` (touching at one halo point ⟹ `HasUnitBand`).
     (`Vertices.lean`.)
   * Theorem 1.5 (1.5.1) at the polygon level: a `T`-free sequence `slopeRatio D ω j`
     (`= φ(q)·α̃_j(ω)`) with `unitSlope_j(T) = v(T)·slopeRatio j` for every `T` in the small
     annulus.  (`SlopeRatios.lean`; **MILESTONE** `unitSlope_specCharSeries_eq_slopeRatio`.)

**Out of scope (recorded so nobody re-litigates):** Step I (Atkin–Lehner Prop 3.22,
classicality Prop 2.15, the slope-sum matching (3.23.1) with dimensions) and Step III (the
`r^{ord}` degree identifications via Hida, Cor 3.21, and the theta exact sequence); the second
half of Theorem 1.5 (arithmetic progressions; needs Atkin–Lehner); the rigid-analytic
packaging (`Spc`, `X_I`, finite flatness, [Bu07, Cor 4.3]); `α_i → ∞`; `p = 2`; Remark 3.25's
integral factorization (the `tate-riesz` board); Prop 2.17.  The `lwx-halo` board is complete
(44/44 tickets, `IntegralModel.lean` sorry-free, verified 2026-09-05); this board consumes only
its `Halo.lean` exports and does not import `IntegralModel.lean`.

## Architecture (planning-time findings)

- **The touching hypothesis is `T`-free.**  [LWX, Step II] derives the unit indices `n_k^±`
  from touching at the single weight `T_{χ_k}` via the equality clause (3.23.2), and then
  re-derives the polygon at *every* `T` from the unit indices alone.  So the honest
  hypothesis for the conditional milestones is `HasUnitBand D ω k` (existence of units on
  both sides of `n_k`), and `hasUnitBand_of_height_eq` proves it is implied by touching at
  any single halo point — which is exactly what Step I supplies.  No rigid geometry anywhere.
- **All strictness comes from one competitor lemma.**  "Consecutive vertices" and "the
  differences in all strict inequalities are at least `min{v(T), 1−v(T)}`" [LWX, p. 26] are
  both instances of `IsNewtonPolygonOf.twoSlope_le_height`: a two-slope broken line lying
  on/below every point lies on/below the polygon (`isGreatest` applied to the competitor
  `NewtonPolygon₀.ofSlopes`).  With slopes `b − μ/N, b` it gives the strict inequality left of
  `n_k^−` (margin `μ(N−x)/N`); with slopes `b, b + μ/(t+2)` the one right of `n_k^+`; with
  `N = n_k ± 1` the bridge from touching to units.  No "vertices are data points" API is
  needed — it was checked that `IsNewtonPolygonOf` (Spec.lean) has no such field and that the
  competitor route avoids it entirely.
- **No polygon-scaling API.**  Theorem 1.5's `T`-independence is proved by comparing the
  specialized polygon with the polygon of the `T`-free shape `shapeVal` through two
  `isGreatest` applications, where the competitors are `ofSlopes` of the *scaled unit-slope
  sequences* (finite by the touching hypothesis).  The only new polygon API is `Support.lean`:
  the competitor lemma, the unit slope as a height increment, the `⊥`-exclusion for
  constructed polygons, and a `Monotone` packaging — everything else (`height_eq_heightFun`,
  `heightFun_succ`, `unitSlope_ne_top_of_height_ne_top`, `height_le_chord`, and the `private`
  `unitSlope_eq_top_of_height_eq_top` / `toReal_unitSlope_le` / `slopes_zero_ne_bot`) already
  exists in `Height.lean` / `OfSlopes.lean` (library audit 2026-09-05).  A planning-time
  two-hulls lemma was found to be an artifact (never consumed) and deleted; a planned
  `unitSlope_ne_bot` was found false (the degenerate one-point polygon has a finite height at
  `x = 1` but a `⊥` unit slope) and replaced by the constructed-polygon exclusion.
- **`m(l)` is explicit**: `unitIndex D ω l = sInf {m | b_{l,m} ∈ ℤ_p^×}`; the Claim's proof
  shows the `T₀`-minimal dominant index is this `sInf`.  "Strictly below the upper bound
  polygon" becomes the `T`-free predicate `IsBelowUpper : 2·m(l) < lwxUpperTwice l` (both
  polygons scale linearly in `v(T)`).
- **Half-integers are avoided**: the upper polygon is stored doubled (`lwxUpperTwice`), the
  radius condition `v(T₀) < 8/((p²−1)t+8)` is the elementary
  `hκ : p⁻⁸ < ‖T₀‖^{(p²−1)t+8}`, and all polygon-level statements are in `negLogNorm`
  units (`v(T₀) := −log‖T₀‖`, `v(p) = log p`) exactly as `Halo.lean`'s `lwxSlopes`.

## Key design decisions

1. **New files only**; `Halo.lean` and the NewtonPolygons library are consumed unchanged
   (same policy as `lwx-halo`).  `Support.lean` is placed in `PhD/NewtonPolygons/` because it
   is LWX-free polygon API.
2. **`p` odd** via `hp2 : p ≠ 2` as on `lwx-halo`; pure-`ℕ` lemmas in `UpperPolygon.lean` take
   `Odd p` / `0 < p` / `1 < p` (only what each needs — attack 3 found `p = 1` counterexamples
   to the strict-excess lemmas).  `t > 0` via `[Nonempty ι]` in the LWX files, `0 < t` in the
   `ℕ` lemmas.
3. **Per-term estimates are public** (`norm_coeff_mul_zpow_le_of_lt` …): [LWX, (3.18.1)] is
   consumed by the sharpness clauses, the Claim's core and its `T`-independence, so the
   three cases `m < λ`, `m = λ`, `m > λ` are separate leaves, and the ultrametric
   "unique dominant term" principle is one general lemma (`TateFredholm.norm_tsum_eq_of_forall_lt`).
4. **Definitions with API**: `touchX`, `lwxUpperTwice`, `IsUnitCoeff`, `leftIndex`/`rightIndex`
   (`sInf`/`sSup` with `_mem`/minimality/maximality spec), `HasUnitBand`, `bandLine`
   (`_touchX`, `_add_one`, `_eq_of_mem_band`), `unitIndex` (`isUnit_`, `not_isUnit_of_lt_`,
   `_le`, `lwxLambda_le_`), `IsBelowUpper`, `shapeVal`/`shapePolygon`/`slopeRatio`.
5. **Single-conclusion statements**; the one bundled leaf `exists_isUnit_and_coeffVal_eq`
   is a shared-witness existential (documented exception).  Two-part *hypothesis*
   definitions (`HasUnitBand`, `IsBelowUpper`) are definitions, not theorems.

## Mathlib/project inventory (verified at planning time, `#check` batch 2026-09-05)

| Concept | Status | Action |
|---|---|---|
| `IsNewtonPolygonOf` (fields `height_le`, `isGreatest`), `pointHeight(_coe/_eq_top_iff)`, `height_eq` | `PhD/NewtonPolygons/Spec.lean` | USE (the competitor lemma is `isGreatest`) |
| `NewtonPolygon₀.ofSlopes`, `ofSlopes_starting_point`, `height_ofSlopes`, `unitSlope_ofSlopes`, `isNewtonPolygonOf_ofSlopes` | `PhD/NewtonPolygons/OfSlopes.lean` | USE as competitors |
| `heightFun`, `heightFun_succ`, `height_eq_heightFun`, `unitSlope_mono`, `unitSlope_cases`, `unitSlope_ne_top_of_height_ne_top`, `height_eq_bot_iff`, `height_eq_top_mono`, `height_le_chord`, `slopes_zero_eq_bot_of_unitSlope_eq_bot` | `PhD/NewtonPolygons/Height.lean` | USE directly (V9–V16, P3) |
| `unitSlope_eq_top_of_height_eq_top` (Height.lean:542), `toReal_unitSlope_le` (Height.lean:658), `slopes_zero_ne_bot` (OfSlopes.lean:170) | were `private`; **made public 2026-09-05** (user decision, `renames.jsonl`) | USE directly (NP4, NP5, V15) |
| `isBelow_iff_height`, `NewtonPolygon.toReal(_coe/_top/_bot)` | `PhD/ForMathlib/NumberTheory/NewtonPolygon/Basic.lean` | USE |
| `newtonPolygon₀OfSeq`, `isNewtonPolygonOf_newtonPolygon₀OfSeq`, `IsAdmissible`, `isAdmissible_of_affine_bound`, `isNewtonPolygonOf_powerSeries`, `coeffVal(_of_ne_zero/_eq_top_iff)`, `newtonPolygon₀_starting_point_of_coeff_zero_eq_one` | `PhD/NewtonPolygons/{SpecConstruction,CoeffVal}.lean` | USE |
| `TateFredholm.norm_tsum_le_iSup`, `summable_of_tendsto_cofinite` | `PhD/TateFredholm/Tate.lean` | USE; the strict/dominant-term variants are new (S1/S2) |
| `HaloInt.specialize` (= `∑' j : ℤ, ψ (f j) * T₀ ^ j`), `summable_specialize`, `norm_specialize_le`, `norm_le_zpow_iff`, `specialize_one` | `PhD/LWX/HaloRing.lean` | USE |
| `lwxLambda(_succ)`, `monotone_sub_div`, `lwxLambda_eq_sum_comp`, `norm_coeff_charCoeff_upOp_le`, `specCharSeries(_coeff_zero)`, `norm_specCharSeries_coeff_le`, `lwxSlopes`, `isBelow_newtonPolygon_specCharSeries` | `PhD/LWX/Halo.lean` | USE (F2/F3 exports) |
| `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, `Summable.tsum_eq_add_tsum_ite`, `Finset.exists_max_image`, `Filter.eventually_cofinite` | Mathlib (verified) | USE for S1/S2 |
| `PadicInt.isUnit_iff` (`IsUnit z ↔ ‖z‖ = 1`), `PadicInt.norm_le_pow_iff_norm_lt_pow_add_one`, `PadicInt.norm_le_one`, `PadicInt.norm_p` | Mathlib (verified) | USE for units ↔ norm 1 / `≤ p⁻¹` |
| `Nat.sInf_mem`, `Nat.sInf_le`, `Nat.sSup_mem`, `Nat.sSup_def`, `le_csSup`, `Nat.find_min'` | Mathlib (verified) | USE for the index definitions |
| `Finset.sum_range_add`, `Finset.sum_range_id_mul_two`, `Finset.sum_tsub_distrib`, `Finset.sum_le_sum_of_subset_of_nonneg`, `Nat.add_mul_div_left`, `Nat.mul_add_div`, `Nat.div_eq_of_lt`, `Nat.div_div_eq_div_mul` | Mathlib (verified) | USE for the `ℕ` combinatorics |
| `Real.log_pow`, `Real.log_zpow`, `Real.log_lt_log`, `Real.log_le_log_iff`, `Real.log_nonneg/pos`, `zpow_le_zpow_right_of_le_one₀`, `zpow_lt_zpow_right_of_lt_one₀` | Mathlib (verified) | USE for norm ↔ valuation |
| `Nat.Prime.odd_of_ne_two` | Mathlib (verified) | USE to feed `Odd p` |
| "vertices are data points" for `IsNewtonPolygonOf` | NOT in library, NOT needed | avoided by the competitor route |
| scaling of `NewtonPolygon₀` by a positive real | NOT in library, NOT needed | avoided via `ofSlopes` of scaled unit slopes |

## File structure (all new; no existing file is edited)

```
PhD/NewtonPolygons/Support.lean — competitor lemma, supporting line, unit slope as height
                                  increment, ⊥-exclusion for constructed polygons, Monotone
                                  packaging (LWX-free; 5 lemmas after the library audit)
PhD/LWX/Sharpness.lean          — ultrametric strict/dominant-term lemmas; (3.18.1) per term;
                                  Cor 3.18 equality / margin / iff
PhD/LWX/UpperPolygon.lean       — touchX, (3.23.1), lwxUpperTwice, Lemma 4.1, band identities
PhD/LWX/Vertices.lean           — IsUnitCoeff, leftIndex/rightIndex, HasUnitBand, bandLine,
                                  Step II at every T, the bridge, the Thm 1.3 slope reading
PhD/LWX/Claim.lean              — unitIndex, IsBelowUpper, the §4.2 Claim
PhD/LWX/SlopeRatios.lean        — shapeVal/shapePolygon/slopeRatio, Thm 1.5 first half
```

Import spine: `Halo ← {Sharpness, UpperPolygon}`; `Support` imports only
`NewtonPolygons.{OfSlopes,SpecConstruction}`; `Vertices ← {Sharpness, UpperPolygon, Support}`;
`Claim ← {Sharpness, UpperPolygon}`; `SlopeRatios ← {Vertices, Claim}`.  Namespaces: `LWX`
(LWX files), `NewtonPolygon₀` / `IsNewtonPolygonOf` (Support), `TateFredholm` (the two
ultrametric `tsum` lemmas).

## Dependency graph (tranche level)

```
NP (Support) ───────────────┐
S  (Sharpness) ──┬──────────┼──► V (Vertices: Step II, Thm 1.3 reading) ──┐
U  (UpperPolygon)┴──► C (Claim) ────────────────────────────────────────┴──► P (SlopeRatios: Thm 1.5)
```

Parallel capacity at start: NP ∥ S ∥ U (3 workers); C after S+U; V after NP+S+U; P last.

## Generality decisions

- `Support.lean` over `Γ = ℝ` (the only instance used; the spec is generic but the
  arithmetic is real).
- All polygon statements are for the concrete `newtonPolygon₀OfPowerSeries negLogNorm
  (specCharSeries D ω ψ T₀)` — the object [LWX] talks about — rather than an abstract
  `IsNewtonPolygonOf`, mirroring `isBelow_newtonPolygon_specCharSeries`.
- Hypotheses `h0 h1 hκ` are kept explicit and separate (`hκ` implies `h0`, but redundancy
  keeps every ticket's call pattern identical to `Halo.lean`'s).
- The `ℕ` lemmas of `UpperPolygon.lean` are stated for arbitrary `p t` with the minimal
  positivity/parity hypotheses found by attack 2 (edge cases `p = 0, 1, 2`, `t = 0`).

## Deferred (no ticket here)

- **Board outcome (2026-09-05):** all 81 tickets done in one beastmode session; the two
  milestones `unitSlope_specCharSeries_eq_iff` / `_mem_Ioo` (Theorem 1.3 at the polygon level)
  and `unitSlope_specCharSeries_eq_slopeRatio` (Theorem 1.5 (1.5.1)) are sorry-free on
  `propext`/`Classical.choice`/`Quot.sound`.  `slopeRatio → ∞` was not needed by any consumer
  and remains deferred (see below); it is a natural first item for a follow-up board together
  with Remark 3.25's integral factorization (`tate-riesz`).

- `slopeRatio j → ∞` and `slopeRatio` increasing (Theorem 1.5's "in increasing order and
  tending to infinity"): increasing is `unitSlope_mono`; tending to infinity needs a
  slope-comparison lemma against the lower polygon (`lwxSlopes → ∞`) — small, but not
  consumed by anything on this board.
- Theorem 1.5's second half; Corollary 1.8; Theorem 1.3 Steps I/III (see out of scope).

## ChatGPT validation

Skipped: the `chatgpt-math` MCP server failed to connect this session (cached failure).
To be run at the user's discretion before execution if desired.
