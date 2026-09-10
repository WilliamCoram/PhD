# Ticket Board — Jacobs endgame: `U₃`-refactor of the downstream slope files

**BOARD PATH: `.mathlib-quality/jacobs-endgame/`** (NOT the default board = NewtonPolygons,
NOT `jacobs/`, NOT `qmf/`, NOT `tatefredholm-eigen/`).  Tell every `/beastmode` this path.
Skeleton is canonical: every proof ticket = "fill the named `sorry`s in the named file";
all statements are already stated and `lake build PhD.Jacobs.BaseChange
PhD.Jacobs.U3.Fredholm PhD.Jacobs.U3.HeckeSlopes` is green (30 sorries, 0 errors,
verified 2026-08-05).  Read `decomposition.md` (same directory) first — leaf entries
carry the discharge citations (file:line, fetched this session) and attack logs.

## Summary
- **ALL PROOF WORK DONE (2026-08-06, single beastmode session)**: E1–E12 + EA1/EA2 +
  the E11 post-completion sweep.  The three board files are 0-sorry / 0-warning; every
  endpoint (charCoeff_map/charPowerSeries_map, the map layers, det(1−T·U₃) =
  charPowerSeriesU3 + eq_U3MatrixOp, bijective_evalU3/kappaFormsModelEquiv,
  evalU3_heckeU3, isCompactoid_blockOpU3, **charPowerSeriesU3_factorisation** and its
  `L₃ = ℚ₃(ζ₃)` witness) verified on exactly [propext, Classical.choice, Quot.sound].
  Full chain green 3519 jobs.
- **BOARD COMPLETE (2026-08-06)**: the consolidated cleanup wave ran as three parallel
  per-file workers (BaseChange 283→272, HeckeSlopes 225→215 + six DiamondW ε-compactoid
  docstrings, Fredholm golfed incl. the ▸-chain shortening of bijective_evalU3), all
  gates green, zero statement changes; post-golf orchestrator re-verification: six wave
  endpoints on exactly the standard three axioms, 0 sorries in all touched files,
  runLinter clean in-file.  Punch-list residue deferred (recorded in the cleanup
  tickets): U3Data coeff_kappaSeries₂ linter de-silencing (signature-adjacent — user
  call), isCompactoid_smul dedup against Riesz's IsCompactoid.smul once import chains
  meet (tatefredholm-eigen seam), TateFredholm upstream warning cluster (other board).
  Files remain UNTRACKED in git — user commit pending.
- **BOARD APPROVED by the user 2026-08-06** (/develop gate passed) — workers may start.
  Any `/beastmode` run for this board uses `.mathlib-quality/jacobs-endgame/beastmode_active`
  as its sentinel (the root sentinel belongs to other instances — never touch it).
- **BOARD REOPENED 2026-08-06 for the AG-W-ID tranche** (user-directed /develop
  extension): tickets WI1–WI7 + 2 cleanups below the closed E-ledger.  Skeleton =
  PhD/Jacobs/U3/DiamondHecke.lean (27 sorries incl. 3 def-holes); decomposition.md
  §"AG-W-ID tranche" carries the computed certificates (search:
  U3/certificate_search_w.py), the Σ₁(3)-width API gap, and the handedness finding.
  AWAITING USER APPROVAL of the tranche before /beastmode.
- E-tranche totals: 22 tickets = 12 proof + 2 notice-refactor + 8 cleanup
- E-tranche: Open 0 | In Progress 0 | Done 22.  WI-tranche: Open 9 | Done 0
- Parallel capacity at start: **6 workers** (E1, E2, E5, E8, E9, E12)
- Milestones: E11 (`charPowerSeriesU3_factorisation` — [Jac (2.1.14)+Lemma 1.15] about
  the genuine `U₃`); the `K₃`-headline `charPowerSeriesU3_eq_U3MatrixOp` is ALREADY
  proved in the skeleton.
- Axiom gate: every endpoint must show exactly `[propext, Classical.choice, Quot.sound]`.
  `hcn : HClassNumberOne` is always an explicit HYPOTHESIS (never cite the sorried
  `hClassNumberOne`); E-C is entirely `hcn`-free.
- Two authorised skeleton-adjacent amendments (log use in the ticket): (i) E8
  de-privatises the six `isCompactoid_epsOp*` + `isCompactoid_zero_clm` in
  `DiamondW.lean` (precedent: `matrixCoeff_epsOp*` for B15); (ii) statement-preserving
  signature fixes only via `/develop --continue`.

## Tickets

### [E1] TateFredholm base change: `charCoeff_map`, `charPowerSeries_map`
- **Status**: done (2026-08-06, beastmode; first-compile both.  charCoeff_map: isometry →
  continuous via `AddMonoidHomClass.isometry_of_norm`, tsum transport =
  `(summable_minor u hu n).hasSum.map f hcont |>.tsum_eq` (HasSum.map takes the RingHom
  directly via FunLike — no .toAddMonoidHom needed), per-minor `RingHom.map_det`
  orientation `f M.det = (M.map f).det` + congr/ext + `Matrix.of_apply` only
  (`Matrix.map_apply` linter-flagged unused — ext normalises it away); assembled via
  map_mul/map_pow/map_neg/map_one + `congrArg ((-1)^n * ·) (tsum_congr …)`.
  charPowerSeries_map = ext n + `PowerSeries.coeff_map` + coefficientwise.  LINT
  DISCOVERY (recorded for the file): `charCoeff`/`minor` need only `NormedCommRing S`
  but `charPowerSeries` demands the full S-pack, so charCoeff_map carries
  `omit [IsUltrametricDist S] [CompleteSpace S] [NormOneClass S] in` — and `omit … in`
  must precede the DOCSTRING, not sit between docstring and theorem.  Axioms:
  [propext, Classical.choice, Quot.sound] both (verified).  Build 2316 jobs green;
  per-decl cleanup folded into CLEANUP-E1 per board cadence) | **File**: PhD/Jacobs/BaseChange.lean (:48, :57) | **Depends**: none
- **Parallel**: yes | **Type**: theorem (PR-shaped)
- **Sketch**: (1) `charCoeff` unfold (Fredholm.lean:147: `(−1)ⁿ * ∑' S : {S // card = n},
  minor u S`).  (2) `f` through `(−1)ⁿ` (map_pow/map_neg/map_one) and through the tsum:
  `f` is continuous (`AddMonoidHomClass.isometry_of_norm f hf |>.continuous`), the source
  family is summable (`summable_minor` — Fredholm.lean:143, needs `[IsTate R]` +
  `IsCompactoid u` ✓ both carried), so `HasSum.map` / `Summable.map_tsum`-family gives
  `f (∑' S, minor u S) = ∑' S, f (minor u S)`.  (3) per-minor: `minor` is a finite det of
  `matrixCoeff`-entries (read minor's def at Fredholm.lean:32 first); `RingHom.map_det`
  (verify exact mathlib name via loogle: `RingHom.map_det : (M.map f).det = f M.det`
  orientation) + `hmatch` entrywise.  (4) `charPowerSeries_map` = `PowerSeries.ext` +
  `PowerSeries.coeff_map` + (1)–(3).
- **Mathlib**: `RingHom.map_det` (verify), `HasSum.map`, `AddMonoidHomClass.isometry_of_norm`,
  `PowerSeries.coeff_map`.  **Sources**: structural; decomposition EC.1.
- **Generality note (recorded)**: `Continuous f` suffices for THIS pair; the isometric
  form is kept for uniformity with the analytic layer.  Do not weaken silently.

### [E2] `map_inv₀` + the analytic layer (`map_padicLog/Exp/binomialCoeff/unitPow`)
- **Status**: done (2026-08-06, beastmode; all six decls first-compile (map_inv₀,
  NEW private map_tsum, padicLog/Exp/binomialCoeff/unitPow).  map_inv₀ exactly per
  sketch: `inv_eq_zero` both sides via `constantCoeff_map` + `f.injective` (fields);
  nonzero via `eq_comm` + `MvPowerSeries.inv_eq_iff_mul_eq_one h'` + `← map_mul` +
  `inv_mul_cancel` (NB the iff is `ψ⁻¹ = φ ↔ φ * ψ = 1` — eq_comm FIRST).  map_tsum:
  the reusable unconditional tsum transport (by_cases Summable; junk side via
  `Summable.tendsto_cofinite_zero.norm` + `tendsto_zero_iff_norm_tendsto_zero` +
  TateFredholm.summable_of_tendsto_cofinite + `tsum_eq_zero_of_not_summable`).
  Termwise: simp only [map_div₀, map_pow, map_sub, map_one, map_add, map_natCast].
  GENERALITY DISCOVERY (recorded): `[CompleteSpace L]` is needed NOWHERE in the
  namespace — junk-robustness means only K's completeness matters; dropped from the
  variable block (statements strictly more general than planned).  map_binomialCoeff
  needs no analysis at all (omit [IsUltrametricDist K] [CompleteSpace K]
  [IsUltrametricDist L]).  `omit … in` placement trap re-confirmed: BEFORE docstring.
  Axioms standard on all (verified).  Build 2316 green, 0 new warnings) | **File**: PhD/Jacobs/BaseChange.lean (:70, :86, :92, :99, :105)
- **Depends**: none | **Parallel**: yes | **Type**: lemma
- **Sketch**: `map_inv₀`: split on `constantCoeff φ = 0` (f injective — field hom — via
  `map_eq_zero`-style + `constantCoeff_map`); nonzero: `MvPowerSeries.inv_eq_iff_mul_eq_one`
  (mathlib Inverse.lean:252) + `← map_mul` + `mul_inv_cancel` + `map_one`; zero: both
  sides junk `0` (`MvPowerSeries.inv_eq_zero`-family).  Analytic: each is
  `f (∑' n, term n) = ∑' n, f (term n)` + termwise `f (term n) = term' n` (map_div₀,
  map_natCast, map_pow, map_sub, map_prod).  Summable case: continuity (E1's isometry
  route) + `HasSum.map`.  Non-summable case: BOTH sides are junk 0 — summability
  transports along the isometry both ways (ultrametric: summable ↔ terms → 0; norms
  preserved; `tsum_eq_zero_of_not_summable`, `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`
  per the J002 discovery, or TateFredholm.Tate's `summable_of_tendsto_cofinite`).
  `map_unitPow` = `unitPow` unfold + `map_padicExp` + `map_mul` + `map_padicLog`.
- **Mathlib**: cited above; read `PadicAnalytic.lean`'s defs first (padicLog/padicExp/
  binomialCoeff exact shapes).  **Sources**: decomposition EC.2.  `map_inv₀` is a
  mathlib-PR candidate — keep it clean and general.

### [E3] Series layer: `map_kappaSeries₂/linSeries/quadSeries/weightGenFun`
- **Status**: done (2026-08-06, beastmode; kappaSeries₂ = MvPowerSeries.ext +
  coeff_map + coeff_kappaSeries₂ + split_ifs + the E2 layer; lin/quad = simp only
  [map_sub/add/mul, MvPowerSeries.map_C/map_X, Matrix.map_apply]; weightGenFun =
  map_mul ×2 + map_inv₀ ×2 + the three + terminal rfl (Matrix.map_apply defeq).
  INSTANCE DISCOVERY (recorded): U3Data's `coeff_kappaSeries₂` carries CompleteSpace
  via its silenced linter (set_option unusedSectionVars false in), so the L-side
  DEMANDS [CompleteSpace L] even though nothing analytic happens — variable pack
  restored; the Analytic section instead carries a section-scoped bare
  `omit [CompleteSpace L]` (bare omit = clean idiom for whole-section omission;
  per-decl `omit … in` must precede the docstring).  De-silencing U3Data's linter =
  CLEANUP-ALL-E1 candidate, NOT touched here (signature-adjacent).  Axioms standard) | **File**: PhD/Jacobs/BaseChange.lean (:116, :121, :126, :134)
- **Depends**: E2 | **Type**: lemma
- **Sketch**: all coefficientwise: `MvPowerSeries.ext` + `MvPowerSeries.coeff_map`
  (`@[simp]`) — `kappaSeries₂` via `coeff_kappaSeries₂` (U3Data:175, rfl-lemma) +
  E2's `map_unitPow`/`map_binomialCoeff` + `map_div₀`/`map_pow`; `linSeries`/`quadSeries`
  coefficient formulas (read defs U3Data:153/157 — finitely-supported polynomial
  coefficients) + `Matrix.map_apply`.  `map_weightGenFun`: `weightGenFun` unfold
  (U3Data:187) + `map_mul` ×2 + `MvPowerSeries.map_inv₀` ×2 + the three; note
  `(γ.map f) 1 0 = f (γ 1 0)` is `Matrix.map_apply`.
- **Mathlib**: `MvPowerSeries.coeff_map`, `Matrix.map_apply`.  **Sources**:
  decomposition EC.3; `weightGenFun` def fetched verbatim.

### [E4] The six `map_h**`
- **Status**: done (2026-08-06, beastmode; NINE private `map_eps*` entrywise lemmas
  (ext + fin_cases ×2 + simp [epsDef, map_div₀, map_ofNat] — `map_ofNat` is the
  load-bearing member, plain simp leaves `f 5 = 5` goals without it; eps10M needs no
  map_div₀, linter-trimmed), wrapped in a `section EpsEntrywise` with
  set_option linter.unusedSectionVars false (privates, deleted at cleanup if inlined).
  Each h then closes by pure rw: [hdef ×2, (map_add,) map_weightGenFun f hf ×k,
  map_eps* ×k] — no congr needed, Matrix.map defeq does the rest.  FILE COMPLETE:
  BaseChange.lean 0 sorries / 0 warnings / std axioms on all six h-endpoints
  (verified).  Build 2316 green) | **File**: PhD/Jacobs/BaseChange.lean (:145–:170) | **Depends**: E3
- **Type**: lemma
- **Sketch**: per h (U3Data:194–212): unfold (`h01 = weightGenFun t (eps01M1 ν) +
  weightGenFun t (eps01M2 ν)` etc.), `map_add` + `map_weightGenFun` + a private
  per-matrix helper `(eps**M* ν).map f = eps**M* (f ν)` (entrywise: `Matrix.ext` +
  `Matrix.map_apply` + `map_div₀`/`map_ofNat`/`map_neg`/`map_mul`; nine matrices, one
  `!![...]`-ext pattern each — extract ONE reusable tactic block).  Single-matrix h's
  (h02/h10/h21) have no `map_add` step.
- **Sources**: decomposition EC.4; eps-defs U3Data:113–146.

### [CLEANUP-E1] /cleanup PhD/Jacobs/BaseChange.lean (cadence after 3rd file ticket)
- **Status**: merged into CLEANUP-ALL-E1 (2026-08-06, recorded deviation per the jacobs
  board's consolidated-wave precedent: E10/E11 still import and extend this file, so the
  interleaved cadence would clean under active importers and re-clean after; the file is
  verifiably 0 warnings / 0 sorries / std axioms at merge time (E4 close-out), so the
  audit baseline is green.  CLEANUP-ALL-E1 (pre-milestone, fresh context) runs the full
  10-phase pass over all three board files at once) | **Depends**: E1, E2, E3 | **Type**: cleanup (board jacobs-endgame)

### [E5] `evalU3` linearity + `blockProj_evalU3`
- **Status**: done (2026-08-06, beastmode; all three FIRST-COMPILE one-liners:
  map_add' = simp [Finset.sum_add_distrib], map_smul' = simp [Finset.smul_sum] (the
  @[simp] AutomorphicFunction.add_apply/smul_apply + Submodule coes do the rest);
  blockProj_evalU3 = simp only [evalU3, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
  cSpace.blockProj_blockIncl, Finset.sum_ite_eq, Finset.mem_univ, if_true]) | **File**: PhD/Jacobs/U3/Fredholm.lean (:49 two field sorries, :57)
- **Depends**: none | **Parallel**: yes | **Type**: def-fields + lemma
- **Sketch**: `map_add'`: Submodule coe of add (`Submodule.coe_add`-through the
  `AutomorphicFunction` coercion — mirror Matrix.lean's coercion handling) + blockIncl
  linearity (`map_add`) + `Finset.sum_add_distrib`.  `map_smul'`: same with `map_smul`.
  `blockProj_evalU3`: push `blockProj i` through the finite sum (`map_sum`),
  `cSpace.blockProj_blockIncl` (BlockOp:626: `= if b = a then f else 0`) +
  `Finset.sum_eq_single i` + `if_pos rfl`.
- **Sources**: decomposition EB.1; [Buz07 §9] quote.

### [E6] `bijective_evalU3` (the [Buz07 §9] isomorphism at the Jacobs data)
- **Status**: done (2026-08-06, beastmode; the hardest fill of the file.  Injectivity =
  blockProj_evalU3 ×2 + eval_classRep_injective.  Surjectivity = exists_classRep_section
  + choose idx hidx + bijective_evalAtReps.2 at the family q ↦ ⟨blockProj (idx q) F, _⟩
  (invariance: stabilizerAt(σ q) = ⊥ via hidx + Lemma 2.2, then a ∀-quantified
  `hone : ∀ p, (⟨↑v, p⟩ : levelMonoid1) = 1` + rw [hone, one_smul] — the ∀-form lets rw
  unify the un-nameable membership proof); then per-i value identification via
  classRep_index_unique on the mk''-equality.  THREE TRAPS RECORDED: (1) rw at a
  hypothesis whose TYPE mentions σsec q fails (motive not type-correct — v's binder type
  also mentions it); fix = prove `stabilizerAt … (σsec q) = ⊥` as a standalone eq and
  transport via `rw [← hst]` in a fresh goal.  (2)+(3) `rw [hidx]`/`rw [← hidx]` in
  goals mentioning `σsec (Quotient.mk'' …)` FAIL pattern-matching (quotient-instance
  spelling); fix = full term-mode congrArg/trans chains — `congrArg (fun g =>
  (Quotient.mk'' g : DoubleCoset.Quotient …))` + `classRep_index_unique` + final
  `(congrArg φ-apply harg).trans (h3.trans (congrArg (blockProj · F) h2))`.  The letI
  triple must open the proof (defeq to kappaForms' instances).  Axioms standard on
  bijective_evalU3 AND kappaFormsModelEquiv (hcn hypothesis-form ✓ no sorryAx);
  E-B TRANCHE COMPLETE: Fredholm.lean 0 sorries / 0 warnings, det(1−T·U₃) proven) | **File**: PhD/Jacobs/U3/Fredholm.lean (:68) | **Depends**: E5
- **Type**: theorem (the one substantial E-B proof, est ~120 LOC)
- **Sketch**: Injective: from `eval_classRep_injective t ht hcn` (Matrix.lean:411,
  proved): if `evalU3 φ = evalU3 ψ` then by `blockProj_evalU3` (E5) the values at all
  three `classRep i` agree, so `φ = ψ`.  Surjective: given `g : c(Fin 3 × ℕ, K₃)`:
  (1) obtain the section `σ` from `exists_classRep_section hcn` (ClassSet:1215) with
  `∀ q, ∃ i, σ q = classRep i`; (2) build the `Π`-family for
  `AutomorphicFunction.bijective_evalAtReps` (QMF/Decomposition.lean:111, proved; read
  its exact target `Π q, fixedPointsOfLE …` and the `fixedPointsOfLE`-membership
  unfold): at `q`, the value `cSpace.blockProj i g` for the `i` with `σ q = classRep i`
  (choice on the section's ∃; well-defined by `classRep_index_unique`/injectivity of
  the class map — ClassSet:1177), membership in the invariants is trivial since
  `stabilizerAt_classRep i = ⊥` (ClassSet:996) makes the condition `∀ u ∈ ⊥, …`;
  (3) surjectivity of `evalAtReps` yields `φ` with prescribed rep-values; (4) show
  `evalU3 t ht φ = g` by `blockProj`-separation: two elements of `c(Fin 3 × ℕ, K₃)` with
  equal `blockProj i`-components for all `i` are equal (small private ext lemma via
  `Subtype.ext` + `funext` on pairs `(i, n)`, or an existing cSpace ext — search
  BlockOp/ModelSpace first) + `blockProj_evalU3`.  Mind the instance `letI`-dance for
  the `Δ₁`-action — copy Matrix.lean's `letI` block verbatim.
- **Mathlib**: `Function.Bijective`, choice on the section.  **Sources**: decomposition
  EB.2 ([Buz07 §9 p. 69] verbatim quote); all four project citations fetched verbatim.
- **Note**: `kappaFormsModelEquiv` (already real) goes sorry-free automatically.

### [E7] `evalU3_heckeU3` (unconditional transport)
- **Status**: done (2026-08-06, beastmode; FIRST-COMPILE 3-liner: simp only [evalU3,
  LinearMap.coe_mk, AddHom.coe_mk, heckeU3_apply_classRep, map_sum, blockOp_blockIncl]
  collapses both sides to double sums (map_sum fires on blockOp AND on blockIncl-of-sum;
  heckeU3_apply_classRep fires as a simp rewrite inside evalU3's body), then
  `exact Finset.sum_comm`) | **File**: PhD/Jacobs/U3/Fredholm.lean (:82) | **Depends**: E5
- **Parallel**: yes (with E6) | **Type**: theorem
- **Sketch**: LHS: `evalU3` unfold + `heckeU3_apply_classRep` (Matrix.lean:350, proved)
  at each `i`.  RHS: `TateFredholm.blockOp` unfold (BlockOp:638:
  `Σ_{a,b} blockIncl a ∘ T a b ∘ blockProj b`) applied to `Σ_j blockIncl j (φ(cⱼ))`;
  collapse `blockProj b (blockIncl j …)` by orthogonality (BlockOp:626) — the double sum
  reduces to `Σ_a blockIncl a (Σ_b blockOp t ht a b (φ(c_b)))`.  Match summands; blocks'
  `map_sum`/`ContinuousLinearMap.sum_apply` bookkeeping.  Convention re-verified
  (decomposition EB.3): both sides are row-form `Σⱼ T i j (input j)` — no transpose.
- **Sources**: decomposition EB.3; PROGRESS.md headline quote.

### [E8] `isCompactoid_blockOpU3` (+ authorised DiamondW de-privatisation)
- **Status**: done (2026-08-06, beastmode; first-compile.  De-privatisation EXECUTED
  (sed): the six `isCompactoid_epsOp**` + `isCompactoid_zero_clm` are now public in
  DiamondW.lean (`isCompactoid_ofGenFun` and the M-op ones stay private) — DOCSTRINGS
  STILL MISSING on the seven, queued for the consolidated cleanup wave.  NEW private
  `isCompactoid_smul` in Fredholm.lean (rowNorm (s•u) ≤ ‖s‖·rowNorm u via
  `norm_matrixCoeff_le_rowNorm_of_isTate` [BlockOp:154] + Real.iSup_le + squeeze_zero +
  hu.const_mul; matrixCoeff-of-smul is rfl per J010 — PUBLIC-API candidate for
  BlockOp/TateFredholm at cleanup).  Assembly: blockOp_eq_smul_epsOp + isCompactoid_blockOp
  + fin_cases ×2 + W007's cons_val/Fin.reduceFinMk simp set + smul_zero + NINE one-exact
  bullets (W006 trap respected: no `first |` alternation)) | **File**: PhD/Jacobs/U3/Fredholm.lean (:91) + PhD/Jacobs/DiamondW.lean
- **Depends**: none | **Parallel**: yes | **Type**: lemma + seam amendment
- **Sketch**: **First, the authorised amendment**: remove `private` from
  `isCompactoid_epsOp01…21` (DiamondW:342–367) and `isCompactoid_zero_clm`
  (DiamondW:292); log the amendment in this ticket's status (precedent: B15's
  `matrixCoeff_epsOp*` de-privatisation).  No statement changes.  Then:
  `blockOp_eq_smul_epsOp t ht` (Matrix.lean:299, proved) rewrites the block matrix as
  `(w i j) • eps/zero`-entries; apply `TateFredholm.isCompactoid_blockOp` (BlockOp:690,
  `[IsTate K₃]` — the instance is real in Fredholm.lean) with per-block
  `IsCompactoid.smul` (Riesz.lean:645) over `isCompactoid_epsOp**` resp.
  `isCompactoid_zero_clm` (smul of 0: `smul_zero` first, or `IsCompactoid.smul` again).
  `fin_cases i <;> fin_cases j <;> exact …` dispatcher (one exact per goal — the
  W006-recorded trap: do NOT use `first | exact …` alternation).
- **Sources**: decomposition EB.4; b2-inheritance (2) satisfied.

### [CLEANUP-E2] /cleanup PhD/Jacobs/U3/Fredholm.lean (cadence after 3rd file ticket)
- **Status**: done (2026-08-06, cleanup wave complete: three parallel per-file workers, all gates green, zero statement changes; post-golf axiom re-verification by orchestrator — all six wave endpoints incl. TateFredholm.charPowerSeries_map on exactly [propext, Classical.choice, Quot.sound]; full chain green 3498 jobs, 0 sorries in all four touched files) | **Depends**: E5, E6, E7 | **Type**: cleanup

### [E9] Hypothesis transports (`norm_three_lt_one_of_isometry` … `map_sq_ν₃`)
- **Status**: done (2026-08-06, beastmode; four first-compile calc/rw one-liners via
  map_ofNat + hf; ν₃_near cited as stated (≤ ‖3‖^10 shape confirmed).  Residual: four
  unusedSectionVars linter warnings (L-instances) — omits queued for the consolidated
  cleanup wave rather than scattering omit-lines mid-tranche) | **File**: PhD/Jacobs/U3/HeckeSlopes.lean (:56, :61, :66, :71)
- **Depends**: none | **Parallel**: yes | **Type**: lemma (small)
- **Sketch**: `(3 : L) = f (3 : K₃)` and `(2695 : L) = f (2695 : K₃)` by
  `map_ofNat`; then `hf` + `norm_three_lt_one` (Setting:105) resp. `ν₃_near`
  (Setting:252) (rewrite `‖(3:L)‖ = ‖(3:K₃)‖` before the power).  `norm_map_weight_lt_one`
  is `hf t ▸ ht`.  `map_sq_ν₃`: `map_pow` + `sq_ν₃` (Setting:195) + `map_neg` +
  `map_ofNat`.
- **Sources**: decomposition EC.5.

### [E10] `map_charPowerSeriesU3` (base change of `det(1 − T·U₃)`)
- **Status**: done (2026-08-06, beastmode; charPowerSeriesU3_eq_U3MatrixOp +
  (TateFredholm.charPowerSeries_map f hf isCompactoid_U3MatrixOp hmatch).symm; hmatch =
  obtain ×2 + simp only [U3MatrixOp, _root_.TateFredholm.matrixCoeff_blockOp] +
  fin_cases ×2 + cons_val set + NINE bullets (zero: (map_zero f).symm — matrixCoeff-of-0
  is rfl; eps: rw [matrixCoeff_epsOpXY ×2, ← map_hXY f hf, MvPowerSeries.coeff_map]).
  **NAME-SHADOWING TRAP (recorded for the whole namespace)**: inside `namespace
  Jacobs.U3`, unqualified `matrixCoeff_blockOp` resolves to Jacobs.U3's OWN certificate
  lemma (Matrix.lean), silently shadowing TateFredholm's — simp reports it as "unused
  simp arg", rw shows the wrong pattern.  Always `_root_.TateFredholm.` -qualify block
  lemmas in this namespace.  E4's map_h layer consumed exactly as designed) | **File**: PhD/Jacobs/U3/HeckeSlopes.lean (:80)
- **Depends**: E1, E4, E9 | **Type**: theorem
- **Sketch**: (1) rewrite `charPowerSeriesU3_eq_U3MatrixOp` (proved).  (2) apply
  `TateFredholm.charPowerSeries_map` (E1) with `u := U3MatrixOp norm_three_lt_one ht
  ν₃_near` (compactoid: `isCompactoid_U3MatrixOp` DiamondW:383, public;
  `IsTate K₃` instance) and `v :=` the RHS operator.  (3) `hmatch`: both matrixCoeffs
  via `TateFredholm.matrixCoeff_blockOp` (BlockOp, proved) + the six public
  `matrixCoeff_epsOp**` (DiamondW:423–443) + `MvPowerSeries.coeff_map` + E4's `map_h**`;
  the diagonal zero blocks: `matrixCoeff 0 = 0 = f 0`.  `fin_cases`-dispatch over the
  block index with one rewrite chain per block (`Matrix.cons_val_*` + `Fin.reduceFinMk`
  in the simp set — the W007-recorded trap).
- **Sources**: decomposition EC.6.

### [CLEANUP-E3] /cleanup PhD/Jacobs/U3/HeckeSlopes.lean (cadence after 3rd file ticket)
- **Status**: done (2026-08-06, cleanup-wave worker, merged with CLEANUP-E4: HeckeSlopes
  225→215 lines — five golfs (map_ofNat idiom unified, term-mode trans forms,
  ω₃-relation via mathlib's `IsPrimitiveRoot.geom_sum_eq_zero` + linear_combination),
  zero statement changes, E10's one-exact-per-goal bullets deliberately preserved;
  DiamondW: six ε-compactoid docstrings added (zero_clm already had one; only change to
  that file).  Gates: build green every batch, 0 sorries, runLinter clean on both
  target files (the 76 closure findings are pre-existing upstream TateFredholm,
  tatefredholm-eigen board's).  Parallel-session note: one transient olean race,
  resolved on retry; U3/Level.lean:673 sorry = the contracted hClassNumberOne, theirs) | **Depends**: E9, E10 | **Type**: cleanup
- Note: 3rd HeckeSlopes proof ticket is E11 below; this cleanup sits between E10 and the
  milestone per the pre-milestone rule (combined with CLEANUP-ALL-E1 gate).

### [CLEANUP-ALL-E1] /cleanup-all over the three board files (pre-milestone)
- **Status**: done (2026-08-06, cleanup wave complete: three parallel per-file workers, all gates green, zero statement changes; post-golf axiom re-verification by orchestrator — all six wave endpoints incl. TateFredholm.charPowerSeries_map on exactly [propext, Classical.choice, Quot.sound]; full chain green 3498 jobs, 0 sorries in all four touched files) | **Depends**: CLEANUP-E1, CLEANUP-E2, CLEANUP-E3, E8 | **Type**: cleanup

### [E11] **MILESTONE — `charPowerSeriesU3_factorisation`**: `det(1 − T·U₃) = ∏ det(1 − T·M_{t,t})` about the genuine `U₃`
- **POST-COMPLETION SWEEP (added 2026-08-06, EA executed early)**: on DONE, upgrade the
  "still open (endgame board)" phrasing in U3Data.lean's header §"The identification"
  and Instance.lean's cyclotomic paragraph to cite this theorem as proved.
- **Status**: done (2026-08-06, beastmode; **MILESTONE PROVED**: rw [map_charPowerSeriesU3]
  + the AG-W milestone via NAMED args (ω := / hω := / h3 := / ht := / hνc :=) at the
  transported hypotheses — grouping M11 * (M22 * M33) matched the skeleton exactly.
  AXIOMS: [propext, Classical.choice, Quot.sound] verified — hcn appears NOWHERE in the
  chain.  POST-COMPLETION SWEEP EXECUTED: U3Data header §identification upgraded to cite
  charPowerSeriesU3/_factorisation/_L₃ as proved; Instance.lean already-correct.
  Mid-run note: one build raced the parallel qmf session's BC5 edits to U3/Matrix.lean
  (transient Unknown identifier matrixCoeff_zero_eq) — settled on retry, never our
  breakage) | **File**: PhD/Jacobs/U3/HeckeSlopes.lean (:97)
- **Depends**: E10, CLEANUP-ALL-E1 | **Type**: theorem (milestone)
- **Sketch**: `map_charPowerSeriesU3` (E10) then `Jacobs.charPowerSeries_U3MatrixOp`
  (DiamondW:1240, proved AG-W milestone) at `L` with `(ω, hω)` — argument order
  `M33op ω hω h3 ht hνc` as in that theorem's statement.  Two-lemma composition; the
  shape is already pinned by the compiled skeleton statement.  Run `#print axioms
  Jacobs.U3.charPowerSeriesU3_factorisation` — must be exactly the standard three.
  The `M₂,₂`-factor slope reading ([Jac Cor 2.16] about `U₃`) is
  `unitSlope_newtonPolygon₀OfPowerSeries_M22op` at `L` (proved; `hν2` from
  `map_sq_ν₃`) — verify the docstring's pointer stays accurate; do NOT add a
  polygon-merge statement (out-of-scope guard, decomposition finding 3).
- **Sources**: [Jac Lemma 1.15 + (2.1.14) + Cor 2.16] quotes in decomposition;
  decomposition EC.7.

### [E12] Cyclotomic witness fills: `norm_ι₃`, `ω₃_sq_add_ω₃_add_one`
- **Status**: done (2026-08-06, beastmode; norm_ι₃ = term-mode `norm_algebraMap' L₃ x`
  (NormedAlgebra instance + field NormOneClass — the spectral norm extends);
  ω₃-relation via zeta_spec → pow_eq_one + ne_one (norm_num) + the ring-factorisation
  `(ω−1)(ω²+ω+1) = ω³−1` + mul_eq_zero (avoids cyclotomic-polynomial eval AND
  linear_combination import questions).  FILE COMPLETE: HeckeSlopes.lean 0 sorries /
  0 warnings incl. the four E9 omits applied; charPowerSeriesU3_factorisation_L₃
  axiom-clean.  ALL 12 PROOF TICKETS + EA1/EA2 DONE — every board file at 0 sorries,
  every endpoint on the standard three axioms) | **File**: PhD/Jacobs/U3/HeckeSlopes.lean (:150, :157)
- **Depends**: none | **Parallel**: yes | **Type**: lemma (small)
- **Sketch**: `norm_ι₃`: `norm_algebraMap'` (Normed/Module/Basic.lean:293, `@[simp]`,
  needs the `NormedAlgebra K₃ L₃` instance — present) or directly
  `spectralNorm_extends` (SpectralNorm.lean:573).  `ω₃_sq_add_ω₃_add_one`: the
  FLT-Three idiom — `have hζ := IsCyclotomicExtension.zeta_spec 3 K₃ L₃;`
  `simpa using hζ.isRoot_cyclotomic (by decide)` (with `Polynomial.cyclotomic_three`
  `@[simp]`); massage `IsRoot` eval to the `^2 + ω + 1 = 0` shape (`eval_add`,
  `eval_pow`, `eval_X`, `eval_one` simp set).
- **Sources**: decomposition EC.8; mathlib citations fetched (`Mathlib/NumberTheory/
  NumberField/Cyclotomic/Three.lean:92-95` idiom).
- **Note**: `charPowerSeriesU3_factorisation_L₃` (real body) goes sorry-free when this
  + E11 land — verify with `#print axioms` at close.

### [CLEANUP-E4] /cleanup PhD/Jacobs/U3/HeckeSlopes.lean (final)
- **Status**: done (2026-08-06, cleanup wave complete: three parallel per-file workers, all gates green, zero statement changes; post-golf axiom re-verification by orchestrator — all six wave endpoints incl. TateFredholm.charPowerSeries_map on exactly [propext, Classical.choice, Quot.sound]; full chain green 3498 jobs, 0 sorries in all four touched files) | **Depends**: E11, E12 | **Type**: cleanup

### [CLEANUP-E5] /cleanup PhD/Jacobs/BaseChange.lean (final)
- **Status**: done (2026-08-06, cleanup-wave worker, discharges the merged CLEANUP-E1
  too: 283→272 lines, zero statement/signature changes.  Golfs: hcont inlined,
  ∀-have → binder form, map_inv₀ injectivity via `f.injective.ne_iff' (map_zero f)`
  (general map_ne_zero_iff absent this mathlib), terminal simps unsqueezed,
  lin/quad → single `simp [def]`, lambdas → `↦`, private map_tsum docstring stripped,
  docstring trims.  Gates: build green (this file 0 warnings), downstream HeckeSlopes
  green, 0 sorries, runLinter zero findings in-file, set_option confirmed
  section-scoped.  NOTE: map_weightGenFun's terminal `rfl` is load-bearing (defeq).
  Upstream flags (pre-existing, other boards): TateFredholm warning cluster,
  Level.lean:673 = the contracted hClassNumberOne.  File still untracked in git —
  user commit pending) | **Depends**: E4 | **Type**: cleanup

### [CLEANUP-E6] /cleanup PhD/Jacobs/U3/Fredholm.lean (final)
- **Status**: done (2026-08-06, cleanup wave complete: three parallel per-file workers, all gates green, zero statement changes; post-golf axiom re-verification by orchestrator — all six wave endpoints incl. TateFredholm.charPowerSeries_map on exactly [propext, Classical.choice, Quot.sound]; full chain green 3498 jobs, 0 sorries in all four touched files) | **Depends**: E8, CLEANUP-E2 | **Type**: cleanup

### [EA1] Notice refactor: U3Data.lean §"Assumed input"
- **Status**: done (2026-08-06, EXECUTED EARLY by direct user request, before E11 —
  deviation recorded: E11-dependent claims are phrased as "still open (endgame board)"
  rather than cited as theorems; E11's completion note must sweep U3Data + Instance
  headers to upgrade that phrasing.  Header §"Assumed input" → §"The identification
  (PROVED)" listing Thm 2.1/L2.2/L2.3/L2.4-2.5/Prop 2.6 decls + twist record + hcn
  contract; in-body Data note + weightGenFun docstring + M22op docstring updated
  (M22op keeps the eigenspace-reading caveat per the Lemma 2.9 residue).  Gate:
  build 3519 jobs green 2026-08-06, doc-only diff) | **File**: PhD/Jacobs/U3Data.lean
  (module header lines 76–93 + the
  in-body note :106–108) | **Depends**: E11 | **Type**: docs (ZERO statement changes)
- **Content**: retitle to "Identification (discharged 2026-08-05; endgame board)".
  State: Thm 2.1 / Lemma 2.2 / Lemma 2.3 / Lemmas 2.4–2.5 / Prop 2.6 are PROVED in
  `PhD.Jacobs.U3` (`classRep_complete`, `stabilizerAt_classRep`, `bijOn_etaRep`, the
  nine certificates + `adjParams_toMatrix_eq_smul_epsTable`, `matrixCoeff_kappaOp`);
  the transcribed matrices are certified against the certificates up to the recorded
  determinant-twist coboundary (`sum_weightGenFun_eq_h`, spectrally inert by
  `charPowerSeries_blockOp_eq_U3MatrixOp`); the operators' `U₃`-reading is
  `heckeU3_apply_classRep` / `evalU3_heckeU3` / `charPowerSeriesU3_eq_U3MatrixOp` /
  `charPowerSeriesU3_factorisation`.  Keep TWO honest residues: `hClassNumberOne`
  (permanent FLT-interface hypothesis, consumers take `hcn` explicitly) and the `ω`-
  extension (the `U₃`-statements over `K₃`, the eigenblock reading over `L ⊇ ℚ₃(ζ₃)` —
  point at `HeckeSlopes`).  Also update the header's "At instantiation … both hypotheses
  become theorems" line to cite `sq_ν₃`/`ν₃_near`/`map_sq_ν₃`/`map_ν₃_near` as the now-
  existing theorems.
- **Gate**: `lake build PhD.Jacobs.Slopes` still green; `git diff` shows doc-only edits.

### [EA2] Notice refactor: Slopes / SlopeTheorem / DiamondW / SlopeReading headers
- **Status**: done (2026-08-06, EXECUTED EARLY by direct user request, before E11 — same
  deviation record as EA1.  Slopes §"Assumed input" → "How this connects to the genuine
  Hecke operator" (identification + factorisation decls; wording-caveat paragraph on the
  eigenspace reading) + §"Slope reading" now cites SlopeReading's proved theorems;
  SlopeTheorem header + both endpoint docstrings now cite SlopeReading (AG-NP done);
  DiamondW §"Assumed input" → "What is identified, and what is not" — the Lemma 2.9/W
  residue KEPT verbatim-in-spirit per the binding clause, U3MatrixOp + Wop docstrings
  updated to match; SlopeReading case-B docstring: eigenspace overclaim replaced by
  factorisation-based statement + explicit not-formalised note; Instance.lean (beyond
  ticket list, same class): AG-B composition paragraph + cyclotomic-certificate section
  now point at U3/Matrix + HeckeSlopes.  Gate: lake build PhD.Jacobs.U3.HeckeSlopes
  PhD.Jacobs.SlopeReading PhD.Jacobs.Instance green 3519 jobs 2026-08-06, doc-only
  diff) | **Files**: PhD/Jacobs/Slopes.lean (§"Assumed input", lines ~34–40),
  PhD/Jacobs/SlopeTheorem.lean + PhD/Jacobs/SlopeReading.lean (identification-open
  remarks where present), PhD/Jacobs/DiamondW.lean (§"Assumed input", lines 25–30)
- **Depends**: E11, EA1 | **Type**: docs (ZERO statement changes)
- **Content**: as EA1, with per-file precision.  **DiamondW MUST keep the Lemma 2.9
  residue**: the `δ`-blocks/`B` (the `W`-operator's own derivation, §B.2) remain
  transcription-status — AG-B certified only the `ε`/`U₃` half; `W` is proof-scaffolding
  and no endgame statement mentions it (decomposition, adversarial finding 1; deferred
  AG-W-ID).  Slopes.lean's notice becomes: `M₂,₂`-as-`ω²`-eigenblock reading is realised
  through the PROVED factorisation `charPowerSeriesU3_factorisation` (its middle factor),
  not through a `W`-eigenspace statement.
- **Gate**: full `lake build PhD.Jacobs.SlopeReading PhD.Jacobs.DiamondW` green,
  doc-only diff.

### [CLEANUP-FINAL] /cleanup-all, final pass (board jacobs-endgame)
- **Status**: done (2026-08-06, cleanup wave complete: three parallel per-file workers, all gates green, zero statement changes; post-golf axiom re-verification by orchestrator — all six wave endpoints incl. TateFredholm.charPowerSeries_map on exactly [propext, Classical.choice, Quot.sound]; full chain green 3498 jobs, 0 sorries in all four touched files) | **Depends**: CLEANUP-E4, CLEANUP-E5, CLEANUP-E6, EA1, EA2
- **Type**: cleanup.  Close-out: verify project-wide 0 sorries in the three board files
  (modulo the contracted `hClassNumberOne` upstream), `#print axioms` on
  `charPowerSeriesU3_factorisation` + `charPowerSeriesU3_factorisation_L₃` +
  `charPowerSeriesU3_eq_U3MatrixOp` = standard three, and `lake exe runLinter` on the
  three modules.

---

# AG-W-ID tranche tickets (opened 2026-08-06, user-directed; file = PhD/Jacobs/U3/DiamondHecke.lean, 27 sorries)

Skeleton canonical (build green modulo the parallel session's rebuild races); read
decomposition.md §"AG-W-ID tranche" first (computed certificates, the Σ₁-width gap, the
handedness finding).  Board REOPENED for this tranche only — the E/EA/CLEANUP ledger
above stays closed.

### [WI1] The wide acting monoid `Σ₁(3)`
- **Status**: superseded (annotated 2026-09-01) — the endgame was delivered in the
  right-slash fork `PhD/JacobsSlash/`, not against the `DiamondHecke.lean` this ticket
  was planned for, so the ticket never closed.  Landed as: γ₃ / γ₃_lt_one and the Σ₁(3) level data: `PhD/JacobsSlash/U3/«1_Setting».lean`.
  Do not pick this ticket up.
- **Superseded header**:
   **File**: DiamondHecke.lean (γ₃, γ₃_lt_one, valued_three_eq_γ₃,
  Sigma1₃ two fields, sigma1_le_sigma1₃, levelMonoid1₃-lemmas ×2) | **Depends**: none
- **Parallel**: yes | **Type**: def+lemma
- **Sketch**: γ₃ facts mirror γ₉'s (Setting.lean:457/557 pattern at exponent −1);
  Sigma1₃.mul_mem = Sigma1's expansion verbatim ((ab)₀₀−1 = (a₀₀−1)b₀₀ + (b₀₀−1) +
  a₀₁b₁₀, Setting.lean Sigma1 proof) with the γ₃ threshold (a₀₁b₁₀ has v ≤ γ₉ ≤ γ₃ ✓);
  sigma1_le: γ₉ ≤ γ₃ (ofAdd mono).  U1_9 ⊆ levelMonoid1₃ via U1_9_subset_levelMonoid1 +
  the ≤.

### [WI2] `μ`, the single-coset decomposition
- **Status**: superseded (annotated 2026-09-01) — the endgame was delivered in the
  right-slash fork `PhD/JacobsSlash/`, not against the `DiamondHecke.lean` this ticket
  was planned for, so the ticket never closed.  Landed as: `toMatrix_mu3` and the μ-coset data: `PhD/JacobsSlash/U3/«7_DiamondHecke».lean`.
  Do not pick this ticket up.
- **Superseded header**:
   **File**: DiamondHecke.lean (invFour_ne_zero, toMatrix_mu3,
  mu3_mem_levelMonoid1₃, mu3_inv_mul_mem_U1_9, cosets_mu3_finite, bijOn_muRep)
- **Depends**: WI1 (memberships) | **Parallel**: partly | **Type**: lemma
- **Sketch**: toMatrix_mu3: map_mul + toMatrix_unitsIncl (θ₃ central 4 = diag(4,4);
  ClassSet has the toMatrix_unitsIncl bridge) + toMatrix_etaAdelic at ϖ = 4⁻¹
  (Valued.v (4⁻¹) = 1: 4 unit) ⇒ diag(4,4)·diag(1,4⁻¹) = diag(4,1) (Matrix numeral mul).
  Normalisation: conjugation formula D M D⁻¹ = (a, b/4; 4c, d) — work via toMatrix +
  mem_U1_9-characterisation (U1_9's membership is componentwise: at 3 the Σ-conditions,
  away integrality — see Level.lean's U1_9 def; both directions needed: state the
  second as mu3 * u * mu3⁻¹ variant or derive).  bijOn: image ⊆ {⟦μ⟧}: u·μ =
  μ·(μ⁻¹uμ) ∈ μU₁(9) by the conj lemma; ⊇: μ ∈ Uμ; injOn trivial (Fin 1);
  finiteness: singleton image.
- **Sources**: [Jac Lemma 2.9] coset content; decomposition §AG-W-ID (handedness
  finding: μ = diag(4,1) LEFT-handed — diag(1,4) is in U₁(9), the identity-coset trap).

### [WI3] `kappaOpW`: the `γ₃`-generalisation of the κ-action
- **Status**: superseded (annotated 2026-09-01) — the endgame was delivered in the
  right-slash fork `PhD/JacobsSlash/`, not against the `DiamondHecke.lean` this ticket
  was planned for, so the ticket never closed.  Landed as: DROPPED BY DESIGN — `kappaOpW` does not exist.  PROGRESS.md "Gap 1": the wide Σ₁(9)-indexed κ-layer was deleted, the Σ₁(3) form being the only one.
  Do not pick this ticket up.
- **Superseded header**:
   **File**: DiamondHecke.lean (kappaOpW def-hole, kappaOpW_restrict,
  kappaOpW_mul, matrixCoeff_kappaOpW) + KappaAction.lean (three-lemma generalisation,
  AUTHORISED amendment: restate the three γ₉-consumers at the v(3) threshold their
  proofs already establish — lines 294/349/1312 all begin `hγ9le3 : γ₉ ≤ v(3)`;
  statement-preserving for all existing call sites via sigma1_le_sigma1₃)
- **Depends**: WI1 | **Type**: theorem (the tranche's core infrastructure)
- **Sketch**: read KappaAction's kappaOp (line 402) construction; the three lemmas'
  hypotheses become `Valued.v (g 0 0 − 1) ≤ γ₃` (the exact fact their bodies use after
  the weakening step); then kappaOpW := the same construction over Sigma1₃; restrict =
  defeq/`rfl`-adjacent once shared; kappaOpW_mul = the B13b action-law instantiated
  (cocycle machinery is threshold-blind — verify at pickup); matrixCoeff_kappaOpW =
  matrixCoeff_kappaOp's proof verbatim.  If the in-place generalisation of KappaAction
  turns fiddly, the fallback is a parametrised private core in DiamondHecke.lean
  consuming KappaAction's public pieces — worker's choice, record which.

### [WI4] `kappaFormsW`, `heckeW`, and the HEADLINE `heckeW_apply_classRep`
- **Status**: superseded (annotated 2026-09-01) — the endgame was delivered in the
  right-slash fork `PhD/JacobsSlash/`, not against the `DiamondHecke.lean` this ticket
  was planned for, so the ticket never closed.  Landed as: `heckeW` and the headline `heckeW_apply_classRep`: `PhD/JacobsSlash/U3/«7_DiamondHecke».lean` (`kappaFormsW` dropped with the wide layer, as in WI3 — `kappaForms` feeds both operators).
  Do not pick this ticket up.
- **Superseded header**:
   **File**: DiamondHecke.lean (kappaFormsW def-hole,
  kappaFormsW_eq_kappaForms, heckeW def-hole, heckeW_apply_classRep, uCandW_mem,
  factorisationW, dTableW_mem ✓proved, toMatrix_mu3_mul_inv_uTableW_mem_sigma1₃)
- **Depends**: WI2, WI3 | **Type**: theorem (milestone of the tranche)
- **Sketch**: uCandW_mem: at 3 the u's are the RATIONAL diagonals diag(−4/5,−1/2),
  diag(−20/7,−1/2), diag(28,4) (decomposition data) — numeral valuation checks
  (−4/5−1 = −9/5 ✓ v≥2, etc.), away from 3: d = ±1 central ⇒ u-components = ±(class
  quotients)·μ-triviality — mirror uCand_mem's structure (Factorisations:332); NB the
  Σ₀-projection trick from BC5's golf (integrality = hs.1.1).  factorisationW =
  mul_inv_cancel_left pattern (one-liner).  kappaFormsW := levelSubmodule at wide letI
  (Matrix.lean's kappaForms pattern); eq: Submodule ext — both carriers are the
  U₁(9)-invariance condition and the two actions agree on U₁(9) ⊆ Σ₁(9) by
  kappaOpW_restrict.  heckeW := heckeOperator at mu3_mem + cosets_mu3_finite;
  apply_classRep := heckeOperator_apply_rep (HeckeMatrix:44) at T := Fin 1,
  w := fun _ => mu3, injective trivially, + the certificate inputs — then the Fin-1 sum
  collapses (Fin.sum_univ_one).
- **Sources**: heckeU3_apply_classRep (Matrix.lean:350) is the template; [Jac pp. 31–32].

### [CLEANUP-WI1] /cleanup DiamondHecke.lean (cadence after 3rd file ticket)
- **Status**: superseded (annotated 2026-09-01) — the endgame was delivered in the
  right-slash fork `PhD/JacobsSlash/`, not against the `DiamondHecke.lean` this ticket
  was planned for, so the ticket never closed.  Landed as: subsumed by the fork files' own cleanup waves (all 0-sorry, linter-zero).
  Do not pick this ticket up.
- **Superseded header**:
   **Depends**: WI1, WI2, WI3 | **Type**: cleanup (board jacobs-endgame;
  may merge into the final wave per the recorded precedent if importers are active)

### [WI5] The `δ`-identification
- **Status**: superseded (annotated 2026-09-01) — the endgame was delivered in the
  right-slash fork `PhD/JacobsSlash/`, not against the `DiamondHecke.lean` this ticket
  was planned for, so the ticket never closed.  Landed as: `coeff_weightGenFun_diagonal`: `PhD/JacobsSlash/U3/«7_DiamondHecke».lean`; the δ-side landed as `sigmaW`, `deltaOf`, `Wop_eq_blockOp_deltaOf` in `PhD/JacobsSlash/«4_DiamondW».lean`.
  Do not pick this ticket up.
- **Superseded header**:
   **File**: DiamondHecke.lean (coeff_weightGenFun_diagonal,
  actingW_eq_smul_delta) | **Depends**: WI3 | **Parallel**: with WI4 | **Type**: theorem
- **Sketch**: diagonal wGF: kappaSeries₂ t 0 d collapses to the p=0 spike κ(d)
  (coeff_kappaSeries₂ + zero-pow); linSeries diag = C d; quadSeries diag = C d −
  C a·X₀X₁; inverses: (C d)⁻¹ = C d⁻¹ (MvPowerSeries C-inv — small lemma or via
  mul_inv_cancel uniqueness), geometric for the second (J013's rowInt_inv pattern or
  direct mul-check `(C d − C a X₀X₁)·(d⁻¹Σ(a/d)ⁿ(X₀X₁)ⁿ) = 1`); convolve — the
  X₀X₁-diagonal support gives the if m = r shape.  actingW_eq_smul_delta: ext via
  TateFredholm.ext_matrixCoeff + matrixCoeff_kappaOpW + the computed acting matrices
  (adjParams of toMatrix(μu⁻¹) — from WI2/WI4's toMatrix data, fin_cases i, numeral
  matrix arithmetic) + coeff_weightGenFun_diagonal + matrixCoeff of delta (DiamondW's
  δ's are scalar•diagOp: matrixCoeff_diagOp + smul) + unitPow_mul for
  κ(s·d) = κ(s)κ(d) (1-unit discs: ‖s−1‖ ≤ ‖3‖ via norm_classDet_sub_one_le,
  ‖d−1‖ ≤ ‖3‖ numerals) — exactly the twist_factor/classWeight algebra of Matrix.lean.
- **Sources**: decomposition §AG-W-ID computed data (scalars verified: κ(d)d⁻² =
  4κ(−1/2), 4κ(−1/2), (1/16)κ(4) at the thesis (a,d)-values).

### [WI6] Eigen-diagonalisation `B⁻¹·W·B = diag(1, ω²·1, ω·1)`
- **Status**: superseded (annotated 2026-09-01) — the endgame was delivered in the
  right-slash fork `PhD/JacobsSlash/`, not against the `DiamondHecke.lean` this ticket
  was planned for, so the ticket never closed.  Landed as: `Binvop_comp_Wop_comp_Bop`: `PhD/JacobsSlash/«4_DiamondW».lean`.
  Do not pick this ticket up.
- **Superseded header**:
   **File**: DiamondHecke.lean (Binvop_comp_Wop_comp_Bop)
- **Depends**: none (uses proved DiamondW only) | **Parallel**: yes | **Type**: theorem
- **Sketch**: blockOp_comp ×2 (W008/W009 pattern) ⇒ 9 entry goals; entries are
  δ/B-block composites: diagOp-telescopes + unitPow_mul κ-reciprocals (the W007/W008
  toolkit: named specialisations exist in DiamondW) + ω-arithmetic (1 + ω + ω² = 0);
  expected scalars (1, ω², ω) — HAND-CHECK the (1,1) entry first; if the computation
  yields the transposed assignment (ω ↔ ω²), that is a RECORDED statement-fix (swap in
  the skeleton + note here), not a B2.  One-exact-per-goal discipline (W006 trap).
- **Sources**: [Jac p. 32 δ-display + p. 33 B-display] (quotes on the jacobs board);
  W011's M33-as-ω-block cross-check.

### [WI7] Docstring upgrades: the eigenspace reading is now formal
- **Status**: superseded (annotated 2026-09-01) — the endgame was delivered in the
  right-slash fork `PhD/JacobsSlash/`, not against the `DiamondHecke.lean` this ticket
  was planned for, so the ticket never closed.  Landed as: the eigenspace reading is formal: `exists_eigenvalue_U3_in_W_eigenspace`, `PhD/JacobsSlash/U3/«9_EigenvaluesU3».lean`.
  Do not pick this ticket up.
- **Superseded header**:
   **Files**: DiamondW.lean header §"What is identified" + Wop
  docstring; Slopes.lean §"How this connects" caveat paragraph; SlopeReading.lean
  case-B docstring; U3Data.lean M22op docstring; PROGRESS.md §3 Lemma 2.9 row + §5
- **Depends**: WI4, WI5, WI6 | **Type**: docs (ZERO statement changes)
- **Content**: replace "the eigenspace reading is not formalisable" caveats with
  pointers to heckeW_apply_classRep + actingW_eq_smul_delta + Binvop_comp_Wop_comp_Bop
  (+ lemma210): "M₂,₂ is the restriction of U₃ to the ω²-eigenblock of the genuine
  diamond operator" is now backed.  KEEP honest: B itself remains transcription-status
  as a basis CHOICE (its correctness is lemma210 + WI6, no §B.2-table claim needed).

### [CLEANUP-WI-FINAL] /cleanup DiamondHecke.lean + touched files (final)
- **Status**: superseded (annotated 2026-09-01) — the endgame was delivered in the
  right-slash fork `PhD/JacobsSlash/`, not against the `DiamondHecke.lean` this ticket
  was planned for, so the ticket never closed.  Landed as: subsumed by the fork files' own cleanup waves (all 0-sorry, linter-zero).
  Do not pick this ticket up.
- **Superseded header**:
   **Depends**: WI4, WI5, WI6, WI7, CLEANUP-WI1 | **Type**: cleanup
