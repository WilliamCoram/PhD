# Decomposition — test.lean refactor: blueprint §5.4–§5.14 on the IsNewtonPolygonOf spec

Started 2026-08-03. Predecessor board archived in `archive-2026-08-newtonpolygon-spec/`.

## Skeleton location (gate: PASSED)

`lake build PhD.NewtonPolygons.PowerSeriesZeros` succeeds (2481 jobs); every declaration is
`:= by sorry`; per-file sorry counts: CoeffVal 15 · FirstBreak 12 · PolynomialRoots 21 ·
RadiusOfConvergence 15 · PowerSeriesZeros 9 — **73 total** (post statement-surgery; FirstBreak 13 incl. the segment-data bridge), zero errors, zero other warnings.
Import DAG: CoeffVal → FirstBreak → PolynomialRoots → PowerSeriesZeros; CoeffVal →
RadiusOfConvergence → PowerSeriesZeros. Import policy (binding): Mathlib + PhD.ForMathlib.* +
PhD.NewtonPolygons.* only.

## Sources and the source-faithfulness argument

- **[T]** `PhD/Test/test.lean` — the PRIMARY source: a complete, formerly sorry-free
  formalisation of §5.4–§5.14 whose proofs are the routes this board re-executes on new APIs.
  Every skeleton declaration's docstring carries its [T] source line; the statement
  transcription was done declaration-by-declaration by extraction agents reading [T] directly
  (their per-decl reports are the Step-3 tension record). [T]'s own proofs ARE the Step-1
  prose — cited by line per ticket instead of re-transcribed here.
- **[BP]** `blueprint/src/chapter/NP.tex` §Properties — the blueprint statements 5.4–5.14
  (verbatim quotes were pulled during the previous board and in this session's planning read).
- `.mathlib-quality/references/test-inventory.md` — the [T] map (sections, decls, old-API
  usage).
- Previous board (archived) — the spec API these statements now consume.

## Statement changes vs [T] (the complete list; everything else is transcription + renames)

1. **`HasFirstBreak` reformulated** ([T]:153 `newtonPolygon (coeffVal K f) 0 = some
   (.nextVertex j₀ j₁ l m)` → `0 < i ∧ slopes 0 = m ∧ lengths 0 = i` on the constructed
   polygon). The `j₁` binder disappears from every downstream statement (5.7–5.10). Bridge
   back: `hasFirstBreak_iff_newtonPolygon_zero` (needs the `a₀ = 1` anchor, which [T] carried
   anyway). Attack note: the reformulation is *data on the constructed polygon*, so no
   collinear-representation subtlety arises (that attack applies only to arbitrary spec'd P;
   recorded in the previous board's L2/L18).
2. **`MemDivisibleValueGroup` machinery deleted** (user-approved; Martin's arbitrary-radius WP
   removed the hypothesis): [T]:934, 974, 2551 not ported; `exists_factor_aux` ([T]:1007)
   survives with the hypothesis deleted; `card_roots_le_of_distinguished` loses `hcval`.
   Attack note: [T]'s §5.7 proof detoured through value-group density to find a radius in the
   divisible closure — the new route applies `weierstrassPreparation_polynomial_of_isMulDistinguished`
   at `c = exp m` directly ([Fact (0 < c)] via `Real.exp_pos`). Nothing else in the proofs
   consumed density.
3. **One-conclusion splits**: [T]:689 `distinguished_of_firstBreak` (3-way `∧`) →
   `firstBreak_gaussTerm_le` / `_break_eq` / `_lt` + assembly-flavoured
   `isMulDistinguished_of_hasFirstBreak` (which is not a bare `⟨…⟩`: the `IsNormMulUnit` field
   is new content over a field, via `norm_mul`). [T]'s other multi-clause conclusions
   (5.7's `∃ g h, …` bundle, 5.13's 7-clause `∃`) are shared-witness existentials — kept
   bundled per `references/statement-splitting.md`'s exception, as [T] and [BP] state them.
4. **New micro-lemmas** (gaps G1/G2 from the inventory):
   `norm_coeff_mul_pow_lt_of_isUnit_toRestricted` (PolynomialRoots:65) — polynomial wrapper of
   `Restricted.norm_coeff_lt_norm_constantCoeff_of_isUnit`; G2's `Restricted.C_isUnit/C_one`
   conveniences are proof-time (`IsUnit.map`, `map_one`), not skeleton decls.
5. **5.6 kept in [BP]'s iff-to-conjunction form** ([T]:476 verbatim); the RHS conjunction is
   the blueprint's phrasing of "n-distinguished", documented exception.
6. **`isPureSeries_of_bounds`** ([T]:735): hypothesis set reconstructed from [T]'s docstring
   (general start, domination by constant term, equality at top degree) — flagged
   `VERIFY vs [T]:735` in the skeleton docstring; the T107 worker must diff against [T] before
   proving and fix the skeleton if drifted (allowed: it is a statement-fidelity correction,
   report in ticket notes).

## Per-file leaf map (leaf = skeleton declaration; discharge = [T] proof route + new APIs)

### CoeffVal.lean (base layer; no [T] counterpart file — [T] lines 79–133 + 435–452 + 661–684)
- Basic API (`coeffVal_eq_top_iff`, `_of_ne_zero`, `_zero_of_coeff_zero_eq_one`,
  `exists_coeffVal_ne_top`): discharge from `negLogNorm_eq_top/of_ne_zero/one` + field
  norm-faithfulness; [T]:94–107 routes. Attacks: ⊤-at-zero convention matches `coeffSeq`'s ✓;
  `negLogNorm_one = 0` needs `NormOneClass K` — a field has it ✓.
- Term dictionary (6): pure `Real.exp/log` arithmetic; [T]:435–452, 661–684 proofs port
  verbatim (they never touched the polygon). Attacks: `a ≠ 0` hypotheses match [T]; the
  `exp_log` step needs `0 < ‖a‖` ✓.
- Admissibility (2): polynomial — `isAdmissible_of_affine_bound` with `m := 0`,
  `b := (finite image).min'`-style floor (or direct BddBelow per point; worker's choice);
  restricted — `‖aₖ‖ cᵏ ≤ B` from `IsRestricted.hasGaussNorm` + `le_gaussNorm`, floor
  `k·log c − log B` (B > 0 from a nonzero coefficient; f = 0 case is vacuous admissibility).
  Attacks: c ≤ 1 sign of `log c` handled by the affine form (m may be negative) ✓; B = 0
  impossible when some coefficient ≠ 0 at c > 0 ✓.
- Spec corollaries (2): assemble `isNewtonPolygonOf_powerSeries` + `exists_coeffVal_ne_top` +
  admissibility. Anchor lemma: `newtonPolygon₀OfSeq_start_mem/le` publics + `coeffVal_zero…`
  pin `(0,0)` (WithTop.coe_inj for the y-coordinate).

### FirstBreak.lean ([T] 146–213, 392–413, 420–626, 689–733, 735–806, 1175–1225)
- Bridge `hasFirstBreak_iff_newtonPolygon_zero`: unfold `newtonPolygon₀OfSeq` slopes/lengths at
  index 0 (`newtonPolygon_slopes/lengths` on the step-0 output) + anchor-at-origin; the
  `nextVertex` inversion directions via `Construction` API. [T]:156–178 analogues.
- Line bounds: `slope_mul_le/lt` from `nextStep_slope_le/lt` (SpecConstruction, proved) +
  bridge + `coeffVal_of_ne_zero`; `norm_coeff_break_eq` from `nextVertex_slope_eq_sInf'` +
  `nextVertex_j₁_eq` ([T]:689's hνi step). `coeff_break_ne_zero` from `nextVertex_j₀Finite` +
  `coeffVal_eq_top_iff`.
- Gauss-term trio: [T]:689–733 route with the term dictionary; `_le` splits k = 0 (a₀ = 1) /
  coeff = 0 / line bound; `_lt` uses `slope_mul_lt`.
- `isMulDistinguished_of_hasFirstBreak`: fields = (IsNormMulUnit from `coeff_break_ne_zero` +
  field `norm_mul`; gaussNorm_eq from `_le` + `_break_eq` via `gaussNorm_eq` iSup + le_antisymm
  as [T]:541–549; gaussTerm_lt from `_lt` — mind `Polynomial.coeff_coe` shuttling).
- 5.6 / of_bounds / 5.5: [T]:476–626, 735–806, 1175–1225 routes; purity now via
  `NewtonPolygon₀.IsPure` + `isPure_of_support_eq_one` / `IsPure.support_eq_one` +
  construction structure lemmas (`newtonPolygon_slopes/lengths/numSegments` unfolds); 5.5
  consumes 5.7 (ticket-ordered after T110).

### PolynomialRoots.lean ([T] 627–1920; per-decl lines in skeleton docstrings)
- Ultrametric no-zero estimates (`aeval_ne_zero_of_dominant_const/lt/top`): [T]:807–883,
  1617–1669 — pure valuation estimates over an extension L, API-neutral, port near-verbatim.
- 5.7: `exists_factor_aux` ([T]:1007, MINUS divisibility) →
  `weierstrassPreparation_polynomial_of_isMulDistinguished` at `exp m` with
  `isMulDistinguished_of_hasFirstBreak`; unpack to coefficient norms via
  `Restricted.norm_def`/`Polynomial.norm_toRestricted` + G1 wrapper; then
  `exists_factorisation_of_firstBreak'`/`…_firstBreak` as [T]:1051–1174 (purity of the factor
  via `isPureSeries_of_bounds`). Attacks: Martin gives `IsUnit e` as `∃! ω, ∃! e` polynomial
  form — matches [T]'s consumption; `NormOneClass K` ✓ field.
- 5.8/5.9: [T]:1237–1350 with term dictionary; `gaussNorm` iSup manipulation as [T].
- 5.10: [T]:1363–1486; roots in `AlgebraicClosure K` with `w`/`hw` — no API change
  (mathlib-only statements), proofs port with 5.7's output.
- 5.11: `vertex_line_le/lt` ([T]:1537–1616) are the general-vertex line bounds — now thin
  consequences of `nextStep_slope_le/lt` + the chain lemmas (`newtonPolygon_nextVertex_of_lt`)
  + dictionary; `card_roots_*` family [T]:1670–1920 ports with `hcval` deleted (Martin at
  arbitrary radius) — the induction along segments is unchanged.

### RadiusOfConvergence.lean ([T] 1969–2099 + 2100–2550)
- Infra 4 + radius API 4: [T] proofs are Restricted/summability arguments on the L-extension —
  new names per rename table (`norm_def`, global `NormMulClass` instance, `HasGaussNorm`
  witnesses); no polygon content.
- Privates (`exists_nextStep_of_succ`, `slope_le_of_sInf`, `newtonPolygon_succ_eq`):
  Construction-layer chain facts, some possibly already derivable from
  `newtonPolygon_nextVertex_of_lt`/`nextStep_nextVertex''` — workers should check before
  re-proving ([T]:2103, 2120, 2209).
- 5.12 workhorses + halves: [T]:2145–2550 routes (convergence from below any slope via the
  line bound; sharpness via infinite support + slopes ≤ m); `hdense` and infinite-support
  hypotheses kept verbatim.

### PowerSeriesZeros.lean ([T] 2538–3553)
- Privates: `coeffVal_eq_coe_iff` (trivial from CoeffVal API), `vertex_line_le'/lt'`
  (power-series versions of the 5.11 bounds, [T]:2588/2646), `gaussNorm_le_of_radius_le`
  ([T]:2703 — mind `le_gaussNorm` witness insertion), `nextStep_congr` ([T]:2715),
  `aeval_ne_zero_of_dominant_at` ([T]:3229).
- 5.13 ([T]:2795–3228): the big induction along the first k segments;
  `weierstrassPreparation_exists_of_isMulDistinguished` replaces the divisible version
  (conclusion `IsNormMulUnit e` — weaken via `.isUnit` where [T] used `IsUnit`); polygon
  agreement clause via the constructed-polygon structure data as [T].
- 5.14 ([T]:3271–3553): `HasSum` zero-counting over L; consumes 5.13 + 5.10/5.11 facts through
  the factor polynomial.

## Adversarial notes (project-level; per-leaf attacks are [T]-transcription checks recorded in
the extractor reports, kept in the task outputs)

- [statement-drift risk] The extractors transcribed 46 statements; two flagged spots need
  worker-side verification against [T] before proving: `isPureSeries_of_bounds` (hypothesis
  set reconstructed, see change 6) and 5.13's 7-clause conclusion (scale-corrected
  `|f−g|_c < |f|_c` form — [T]'s own documented deviation from [BP], kept).
- [B2-log consultation] `b2_log.jsonl` (2 entries, both resolved) — no name/shape overlap with
  this board's leaves; the `unitSlope_cases` resolution *benefits* this board (hypothesis-free
  cases available).
- [dependency freshness] All five ForMathlib pillars verified sorry-free this session; nothing
  outside NewtonPolygons imports them wrongly; `Mathlib.RingTheory.Polynomial.GaussNorm`
  shadowing rule propagated to every file's import list (verified: none import it).

## Confidence gate

1. Every leaf is a skeleton declaration discharged by a cited [T] proof route + inventoried
   ForMathlib/mathlib API (names verified by the pillar inventory), or one of the 2 flagged
   verify-spots above. No API gaps requiring sub-development (G1 is a skeleton decl; G2 is
   proof-time). ✓
2. Skeleton compiles, 72 sorries, zero errors. ✓
3. Source record: [BP] quotes (planning read + previous board) + per-decl [T] line citations
   in every docstring + extractor transcription reports. ✓
4. Adversarial: statement changes enumerated exhaustively (6 items) with rationale; two
   drift-risk spots explicitly gated on workers. ✓
5. b2 log consulted (2 resolved entries, no overlap). ✓
6. Tree mirrors [T]'s own structure (§-by-§, same lemma granularity apart from sanctioned
   splits/deletions). ✓
7. Single-conclusion: splits applied ([T]:689); documented shared-witness exceptions (5.7,
   5.13 existentials; 5.6 iff). ✓

### Statement-change 7 (user decision, 2026-08-03, pre-approval statement surgery)

Blueprint-numbered public theorems must be phrased in TEXTBOOK polygon data — hypotheses of the
form `(NP f).slopes k = (m : WithBotTop ℝ)`, `(NP f).lengths k = (l : WithTop ℕ)`,
`(NP f).vertexX (k+1) = ((j₀ : ℤ) : WithTop ℤ)` (NP f = `newtonPolygon₀OfPowerSeries negLogNorm f`)
— never raw step equations `newtonPolygon (coeffVal f) k = some (.nextVertex j₀ j₁ l m)`; the
`j₁` binder disappears from public statements (recoverable as `-log ‖coeff j₀‖`). Rationale:
matches [BP]/Gouvêa's "slopes and lengths as lists"; a real-coe `slopes k` equality certifies
by itself that the k-th slope exists. PRIVATE/internal lemmas keep the step form (easier to
prove with); the two are interchanged by the new bridge lemma
`newtonPolygon_eq_nextVertex_of_segment_data` (FirstBreak.lean): finite nonzero length at k
forces a `nextVertex` step, recovering the step equation from the data. Affected publics:
`vertex_line_le/lt`, the 5.11 `card_roots_*` family, the four 5.12 statements, and the three
5.13/5.14 statements.
