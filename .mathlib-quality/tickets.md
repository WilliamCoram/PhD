# Ticket Board — test.lean refactor: blueprint §5.4–§5.14 on IsNewtonPolygonOf

Project: re-derive [T] = `PhD/Test/test.lean`'s content (blueprint 5.4–5.14) in
`PhD/NewtonPolygons/{CoeffVal,FirstBreak,PolynomialRoots,RadiusOfConvergence,PowerSeriesZeros}.lean`.
The skeleton EXISTS and BUILDS (73 sorries, 0 errors; statements in TEXTBOOK polygon-data form per decomposition §change-7); every ticket is "fill the sorries at the
named declarations, following [T]'s proof at the cited lines with the API swaps of plan.md's
rename table". Statements live in the skeleton (each docstring cites its [T] line); statements
are ticket-protected — the ONLY sanctioned statement edits are the two VERIFY-spots (T107,
T120). Sources/attack notes: `.mathlib-quality/decomposition.md`.
IMPORT POLICY: Mathlib + PhD.ForMathlib.* + PhD.NewtonPolygons.* only; [T] is read-only
reference (it does not compile).

## Summary
- Total: 29 tickets (21 proof + 5 per-file cleanups + 1 cleanup-all + 1 final + 1 doc)
- Open: 0 | Done: all (summary line corrected 2026-09-02; every per-ticket status below
  was already `done` — project completed 2026-08-04, blueprint §5.4–§5.14 sorry-free in
  `PhD/NewtonPolygons/`, `test.lean` superseded)
- Milestones: T110 (§5.7), T114 (§5.11), T118 (§5.12), T121 (§5.14 — project end)
- Parallel at start: T101 ∥ T102 ∥ T109 ∥ T113 ∥ T115 (5 workers)
- Build: `lake build PhD.NewtonPolygons.PowerSeriesZeros` (whole chain). Axioms at each
  milestone: standard three only.

---

### [T101] CoeffVal basic API + anchor
- **Status**: done (2026-08-03T23:05Z; 15/15 across the three tickets, axioms standard, no name drift) | **File**: CoeffVal.lean | **Depends**: none | **Parallel**: yes
- Decls: `coeffVal_eq_top_iff`, `coeffVal_of_ne_zero`, `coeffVal_zero_of_coeff_zero_eq_one`,
  `exists_coeffVal_ne_top`, `newtonPolygon₀_starting_point_of_coeff_zero_eq_one` (5).
- Route: `negLogNorm_eq_top/of_ne_zero/one` (NegLogNorm.lean) + field norm-faithfulness;
  anchor via `newtonPolygon₀OfSeq_start_mem/le` + `WithTop.coe_inj`; [T]:94–125 analogues.
- Mathlib: `PowerSeries.ext_iff`-style coefficient extraction for `exists_…`.

### [T102] Term dictionary
- **Status**: done (2026-08-03T23:05Z; 15/15 across the three tickets, axioms standard, no name drift) | **File**: CoeffVal.lean | **Depends**: none | **Parallel**: yes
- Decls: `norm_mul_exp_pow_{eq_exp,le_one_iff,eq_one_iff,lt_one_iff,le_norm_iff,eq_norm_iff}` (6).
- Route: [T]:435–452, 661–684 proofs port verbatim (`Real.exp_add/exp_log/exp_le_one_iff`…).

### [T103] Admissibility + spec corollaries
- **Status**: done (2026-08-03T23:05Z; 15/15 across the three tickets, axioms standard, no name drift) | **File**: CoeffVal.lean | **Depends**: T101 | **Parallel**: after T101
- Decls: `isAdmissible_coeffVal_coe`, `isAdmissible_coeffVal_of_isRestricted`,
  `isNewtonPolygonOf_coeffVal_coe`, `isNewtonPolygonOf_coeffVal_of_isRestricted` (4).
- Route: `isAdmissible_of_affine_bound` (SpecConstruction) with per-case floors
  (decomposition §CoeffVal); Gauss bound via `IsRestricted.hasGaussNorm` + `le_gaussNorm`;
  assemble with `isNewtonPolygonOf_powerSeries`. Watch: f = 0 vacuous case; B > 0.

### [CLEANUP-A] golf CoeffVal.lean
- **Status**: done (2026-08-04T00:45Z; 213→173 lines, signatures+axioms diff-verified identical; NOTE: IsUltrametricDist was never used in CoeffVal - variable+omits removed, file now holds over any NontriviallyNormedField; header rewording deferred to CLEANUP-ALL) | **Depends**: T103 | Blocks T104.

### [T104] HasFirstBreak bridge + break point facts + segment-data bridge
- **Status**: done (2026-08-04T01:05Z; 12/12 sorries filled, build 2087 jobs, axioms std, VERIFY-spot T107: NO DRIFT vs [T]:735, sanctioned edit not needed; 16 private helpers re-derive SpecConstruction privates - dedup at CLEANUP-B/C1) | **File**: FirstBreak.lean | **Depends**: CLEANUP-A | **Parallel**: yes
- Decls: `hasFirstBreak_iff_newtonPolygon_zero`, `HasFirstBreak.coeff_break_ne_zero`,
  `HasFirstBreak.norm_coeff_break_eq`, `newtonPolygon_eq_nextVertex_of_segment_data` (4).
- NOTE (statement-form rule, decomposition §change-7): blueprint-numbered publics are stated
  in textbook polygon data (`slopes k = m`, `lengths k = l`, `vertexX (k+1) = j₀`); the new
  bridge lemma recovers the algorithm step from that data (finite nonzero length forces
  `nextVertex`) and is how every converted proof starts.
- Route: unfold `newtonPolygon₀OfSeq` slopes/lengths at 0 against the step-0 output (match on
  `newtonPolygon (coeffVal f) 0`; anchor via T101's origin lemma); inversions from
  Construction API; break value via `nextVertex_slope_eq_sInf'` + `nextVertex_j₁_eq` +
  `coeffVal_of_ne_zero` ([T]:156–178, 689's hνi step).

### [T105] First-break line bounds
- **Status**: done (2026-08-04T01:05Z; 12/12 sorries filled, build 2087 jobs, axioms std, VERIFY-spot T107: NO DRIFT vs [T]:735, sanctioned edit not needed; 16 private helpers re-derive SpecConstruction privates - dedup at CLEANUP-B/C1) | **File**: FirstBreak.lean | **Depends**: T104 | **Parallel**: no
- Decls: `HasFirstBreak.slope_mul_le`, `HasFirstBreak.slope_mul_lt` (2).
- Route: `nextStep_slope_le/lt` (SpecConstruction, proved) through the T104 bridge;
  [T]:184–213 shape with the algebraMap ℝ ℝ = id simplification.

### [T106] Gauss-term trio + IsMulDistinguished
- **Status**: done (2026-08-04T01:05Z; 12/12 sorries filled, build 2087 jobs, axioms std, VERIFY-spot T107: NO DRIFT vs [T]:735, sanctioned edit not needed; 16 private helpers re-derive SpecConstruction privates - dedup at CLEANUP-B/C1) | **File**: FirstBreak.lean | **Depends**: T105, T102 | **Parallel**: no
- Decls: `firstBreak_gaussTerm_le/_break_eq/_lt`, `isMulDistinguished_of_hasFirstBreak` (4).
- Route: [T]:689–733 + dictionary; the packaging's `isNormMulUnit_coeff` from field `norm_mul`
  (`IsNormMulUnit` def in ForMathlib NormMulUnit.lean); `gaussNorm_eq` field via iSup
  `le_antisymm` as [T]:541–549 (`HasGaussNorm` witness: `hasGaussNorm_of_finite_support` or
  Restricted route). Mind `Polynomial.coeff_coe`.

### [T107] Purity: of_bounds + blueprint 5.6
- **Status**: done (2026-08-04T01:05Z; 12/12 sorries filled, build 2087 jobs, axioms std, VERIFY-spot T107: NO DRIFT vs [T]:735, sanctioned edit not needed; 16 private helpers re-derive SpecConstruction privates - dedup at CLEANUP-B/C1) | **File**: FirstBreak.lean | **Depends**: T106 | **Parallel**: no
- Decls: `isPureSeries_of_bounds`, `isPureSeries_iff_distinguished` (2).
- **VERIFY-spot**: diff `isPureSeries_of_bounds`'s hypotheses against [T]:735 before proving;
  fix skeleton if drifted (statement-fidelity correction, note it). Route: [T]:476–626,
  735–806 on `NewtonPolygon₀.IsPure` via construction structure lemmas
  (`newtonPolygon_slopes/lengths` unfolds, `isPure_of_support_eq_one`, `IsPure.support_eq_one`)
  + T104/T105 machinery for both iff directions.

### [CLEANUP-B] golf FirstBreak.lean
- **Status**: done (2026-08-04T03:10Z; 636->554 lines -12.9%, signatures diff-empty, 12/12 axioms std; new shared step-inversion helper + coercion layer, 5.6 forward now factors through 5.7 gauss lemmas; omit NOT added on 3 decls where instance is a genuine binder - sanction correctly declined; T108 decl untouched) | **Depends**: T107 (T108 lands later — re-golf its decl in CLEANUP-ALL) |
  Blocks T110.

### [T109] Ultrametric no-zero estimates + G1
- **Status**: done (2026-08-04T00:15Z; 8/8 across both, axioms standard no sorryAx; 10 private helpers incl. step_of_segment_data re-derived locally since CoeffVal was mid-flight - DEDUP vs CoeffVal publics in CLEANUP-C1; 2 unused-IsUltrametricDist linter warnings on vertex_line_le/lt left for cleanup omit) | **File**: PolynomialRoots.lean | **Depends**: none | **Parallel**: yes
- Decls: `norm_coeff_mul_pow_lt_of_isUnit_toRestricted` (G1),
  `aeval_ne_zero_of_dominant_const`, `aeval_ne_zero_of_dominant_lt` (3).
- Route: G1 = `Restricted.norm_coeff_lt_norm_constantCoeff_of_isUnit` + `coeff_coe` shuttling
  (~5 lines); estimates = [T]:807–883 (valuation triangle arguments over L, API-neutral).

### [T110] MILESTONE §5.7 — factorisation at the first break
- **Status**: done (2026-08-04T01:45Z; 4/4 sorry-free, build 2479 jobs, MILESTONE axioms [propext, Classical.choice, Quot.sound] no sorryAx; exists_factor_aux re-derived on IsMulDistinguished packet, MemDivisibleValueGroup dropped; 0 new helpers; statements unchanged) | **File**: PolynomialRoots.lean | **Depends**: CLEANUP-B, T109 |
  **Parallel**: no
- Decls: `eq_of_prod_eq_pow_card` (private), `exists_factor_aux` (private),
  `exists_factorisation_of_firstBreak'`, `exists_factorisation_of_firstBreak` (4).
- Route: [T]:884–1174 with the Martin swap: `isMulDistinguished_of_hasFirstBreak` →
  `weierstrassPreparation_polynomial_of_isMulDistinguished` at `c = exp m`
  (`haveI : Fact (0 < Real.exp m) := ⟨Real.exp_pos m⟩`); unpack via
  `Restricted.norm_def`, `Polynomial.norm_toRestricted`, G1; purity of the factor via
  `isPureSeries_of_bounds`. ALL divisible-value-group steps of [T] are skipped. Axiom-check
  the milestone.

### [T108] Blueprint 5.5 — irreducible ⇒ pure
- **Status**: done (2026-08-04T04:10Z; sorry-free, axioms std; dependency inversion resolved via private degree-only shadow of 5.7 (exists_factorisation_natDegree_of_hasFirstBreak) - [T] only used f=g*h + natDegree from the 8-field result; 1 ForMathlib import added (MulWeierstrassPrep, non-circular); FirstBreak.lean now FULLY sorry-free) | **File**: FirstBreak.lean | **Depends**: T110 | **Parallel**: yes
- Decl: `isPureSeries_of_irreducible` (1). Route: [T]:1175–1225 (break in the interior gives a
  proper factor via 5.7).

### [T111] §5.8 + §5.9
- **Status**: done (2026-08-04T02:30Z; 3/3 ported [T]:1237-1349, axioms std no sorryAx, statements byte-identical) | **File**: PolynomialRoots.lean | **Depends**: T110 | **Parallel**: yes
- Decls: `coeff_mul_pow_le_of_lt_firstBreak`, `gaussNorm_eq_one_of_lt_firstBreak`,
  `aeval_ne_zero_of_lt_firstBreak` (3). Route: [T]:1237–1350 + dictionary.

### [T112] §5.10 root counting at the first slope
- **Status**: done (2026-08-04T02:30Z; 2/2 ported [T]:1363-1485, axioms std no sorryAx; hgtop coeff-natDegree form was defeq to leadingCoeff need - no bridge) | **File**: PolynomialRoots.lean | **Depends**: T110 | **Parallel**: yes
- Decls: `aeval_ne_zero_of_norm_lt_firstBreak`, `card_roots_firstBreak` (2).
- Route: [T]:1363–1486 (AlgebraicClosure w/hw; multiset root counting through 5.7's factor).

### [T113] Vertex-line bounds + dominant-top
- **Status**: done (2026-08-04T00:15Z; 8/8 across both, axioms standard no sorryAx; 10 private helpers incl. step_of_segment_data re-derived locally since CoeffVal was mid-flight - DEDUP vs CoeffVal publics in CLEANUP-C1; 2 unused-IsUltrametricDist linter warnings on vertex_line_le/lt left for cleanup omit) | **File**: PolynomialRoots.lean | **Depends**: none | **Parallel**: yes
- Decls: `term_le_term_iff'`, `term_lt_term_iff'` (privates), `vertex_line_le`,
  `vertex_line_lt`, `aeval_ne_zero_of_dominant_top` (5).
- Route: [T]:1514–1669; line bounds are `nextStep_slope_le/lt` + chain lemmas
  (`newtonPolygon_nextVertex_of_lt`) + dictionary; dominant-top is the mirror ultrametric
  estimate.

### [CLEANUP-C1] golf PolynomialRoots.lean (cadence: after 3rd ticket on file)
- **Status**: done (2026-08-04T04:50Z; 943->829 lines -12.1%, 0 unusedSectionVars, axioms std byte-identical; dedup: 4 privates deleted vs CoeffVal publics, rest documented-kept; ACCEPTED signature change: omit dropped IsUltrametricDist binder from vertex_line_le/lt printed signatures - sanctioned, no users repo-wide, mathlib-preferred generalization) | **Depends**: T111, T112, T113 | Blocks T114.

### [T114] MILESTONE §5.11 — root counting along the polygon
- **Status**: done (2026-08-04T05:55Z; 4/4 sorry-free, MILESTONE axioms std no sorryAx, 0 warnings, statements byte-identical; hcval deletion clean - exists_between replaces divisible-closure radius, memDivisibleValueGroup_exp_slope gone; 2 new privates step_of_slope_length + exists_radius_between; PolynomialRoots.lean FULLY sorry-free) | **File**: PolynomialRoots.lean | **Depends**: CLEANUP-C1 | **Parallel**: no
- Decls: `card_roots_le_of_distinguished`, `card_roots_le_slope`, `card_roots_lt_slope`,
  `card_roots_slope` (4).
- Route: [T]:1670–1920 with `hcval` DELETED (Martin at arbitrary radius); segment induction
  unchanged. Axiom-check.

### [CLEANUP-C2] golf PolynomialRoots.lean (final per-file)
- **Status**: done (2026-08-04T06:30Z; 1040->980 lines, 0 warnings, signatures diff-empty, axioms std; dominant-trio unified into one private core (83->56 lines), step-extraction unified; structural golf saturated) | **Depends**: T114.

### [T115] Restricted ↔ summable infra
- **Status**: done (2026-08-03T22:20Z; direct port, no helpers, axioms standard) | **File**: RadiusOfConvergence.lean | **Depends**: none | **Parallel**: yes
- Decls: `isRestricted_of_le`, `summable_of_isRestricted`, `isRestricted_iff_summable`,
  `isRestricted_of_summable` (4). Route: [T]:1973–2030 with rename table.

### [T116] radiusOfConvergence API
- **Status**: done (2026-08-03T22:20Z; direct port, no helpers, axioms standard) | **File**: RadiusOfConvergence.lean | **Depends**: T115 | **Parallel**: no
- Decls: `le_radiusOfConvergence_of_summable`, `summable_of_lt_radiusOfConvergence`,
  `isRestricted_of_lt_radiusOfConvergence`, `le_radiusOfConvergence_of_isRestricted` (4).
- Route: [T]:2038–2099 (ENNReal iSup gymnastics; `hdense` half as [T]).

### [T117] §5.12 workhorses
- **Status**: done (2026-08-04T00:25Z; MILESTONE 5.12 landed - RadiusOfConvergence fully proved, axioms standard; privates simplified via existing Construction/SpecConstruction lemmas, limitingRay branch 55 lines shorter than [T]) | **File**: RadiusOfConvergence.lean | **Depends**: T116, T103 |
  **Parallel**: no
- Decls: privates `exists_nextStep_of_succ`, `slope_le_of_sInf`, `newtonPolygon_succ_eq` +
  `isRestricted_of_lt_slope`, `not_isRestricted_of_slopes_le` (5).
- Route: [T]:2103–2495; CHECK the three privates against existing Construction/SpecConstruction
  lemmas before re-proving (may be one-liners now).

### [T118] MILESTONE §5.12 — the radius is exp(sup slopes)
- **Status**: done (2026-08-04T00:25Z; MILESTONE 5.12 landed - RadiusOfConvergence fully proved, axioms standard; privates simplified via existing Construction/SpecConstruction lemmas, limitingRay branch 55 lines shorter than [T]) | **File**: RadiusOfConvergence.lean | **Depends**: T117 | **Parallel**: no
- Decls: `ofReal_exp_le_radiusOfConvergence`, `radiusOfConvergence_le_ofReal_exp` (2).
- Route: [T]:2496–2550. Axiom-check.

### [CLEANUP-D] golf RadiusOfConvergence.lean
- **Status**: done (2026-08-04T03:10Z; 617->581 lines, 0 warnings, axioms std, signatures preserved; NOTE: omit on the two workhorses cascaded - golfer kept IsUltrametricDist on the two HEADLINE publics and silenced linter via set_option instead, since removal would change public signatures; full-omit generalization deferred to CLEANUP-ALL/user) | **Depends**: T118.

### [T119] PowerSeriesZeros privates
- **Status**: done (2026-08-04T03:55Z; 6/6, axioms std no sorryAx (in-file check, privates unaddressable from imports); vertex_line_lt- re-derived in 6 lines via incoming-step nextStep_slope_lt (~50 [T] lines dead); MemDivisibleValueGroup analogue confirmed dead; NOTE for CLEANUP-E: 4 frozen decls now flag unused IsUltrametricDist - omit needs sanction) | **File**: PowerSeriesZeros.lean | **Depends**: T113, T117 | **Parallel**: yes
- Decls: `coeffVal_eq_coe_iff`, `vertex_line_le'`, `vertex_line_lt'`,
  `gaussNorm_le_of_radius_le`, `nextStep_congr`, `aeval_ne_zero_of_dominant_at` (6).
- Route: [T]:2538–2794 + 3229–3270; power-series versions of T113's bounds; mind the
  `le_gaussNorm` HasGaussNorm witness.

### [T120] §5.13 — Weierstrass factorisation along the polygon
- **Status**: done (2026-08-04T05:20Z; sorry-free, axioms std no sorryAx; VERIFY-spot: NO DRIFT - clauses 1-6 verbatim, clause 7 congrArg-level textbook projection of [T] form, hypotheses in packaged slopes/vertexX form per statement rule; divisibility route fully excised; 5 privates incl. 190-line slopeSet_lb_and_achievingSet_eq workhorse) | **File**: PowerSeriesZeros.lean | **Depends**: T119, T110 | **Parallel**: no
- Decl: `exists_weierstrass_factorisation` (1).
- **VERIFY-spot**: the 7-clause conclusion vs [T]:2795 (scale-corrected form is [T]'s own).
- Route: [T]:2795–3228 segment induction; `weierstrassPreparation_exists_of_isMulDistinguished`
  (conclusion `IsNormMulUnit e` — `.isUnit` where [T] used `IsUnit`); no divisibility steps.
  This is the LONGEST single port (~430 [T] lines) — expect sub-helpers; spawn per A2 freely.

### [T121] MILESTONE §5.14 — power-series zero counting (PROJECT END)
- **Status**: done (2026-08-04T07:05Z; 2/2 sorry-free, PROJECT-END axioms std no sorryAx, full-chain build 2481 jobs; ray cases re-derived under weaker textbook hypotheses (limitingRay handled via ray-window recursion, infiniteRay refuted from convergence); 11 privates incl newtonPolygon_transfer + norm_eq_exp_slope_aux; no divisibility needed; maxHeartbeats 1e6 inherited from [T] - retune in CLEANUP-E) | **File**: PowerSeriesZeros.lean | **Depends**: T120, T112, T114 |
  **Parallel**: no
- Decls: `hasSum_zero_iff_aeval_eq_zero`, `norm_eq_exp_slope_of_hasSum_zero` (2).
- Route: [T]:3271–3553. Axiom-check; full-chain build.

### [CLEANUP-E] golf PowerSeriesZeros.lean
- **Status**: done (2026-08-04T07:50Z; 1396->1345 lines, 0 warnings, signatures diff-empty, axioms std; BOTH maxHeartbeats prefixes DELETED - root cause was a 25.8s failing isDefEq on a redundant type ascription, elaboration 26s->12s; omit on 5 privates, module docstring fixed) | **Depends**: T121.

### [CLEANUP-ALL] project-wide pass over PhD/NewtonPolygons/ (incl. re-golf of T108's decl)
- **Status**: done (2026-08-04T08:20Z; FirstBreak 0 warnings — T108 block golfed, 3 unusedSectionVars silenced CLEANUP-E-style, signatures diff-empty, axioms std, saturation reached; cross-file dedup of slopeReal_real-type privates documented-deferred as follow-up — needs new Spec/Construction publics, low value) | **Depends**: all proof tickets + per-file cleanups.

### [DOC-1] Update blueprint pointers + memory
- **Status**: done (2026-08-04T08:00Z; SUPERSEDED header added to [T] test.lean (file NOT deleted per keep-PRd-history), memory entry written; lakefile-glob question deferred to user in final report) | **Depends**: CLEANUP-ALL | Note in [T] header that the file is superseded
  (do NOT delete [T] — Keep-PR'd-history rule); consider `PhD.lean` root-module entries if the
  user wants the lakefile glob fixed (ask first).

### [CLEANUP-FINAL] /cleanup-all + endpoint axiom sweep
- **Status**: done (2026-08-04T08:30Z; full-chain build all 8 modules OK 2481 jobs, 0 sorries project-wide, 16/16 blueprint endpoints on [propext, Classical.choice, Quot.sound], style sweep clean) | **Depends**: everything.
