# Ticket Board — laweights (locally analytic weight characters for QMF)

**BOARD PATH: `.mathlib-quality/laweights/`** (tickets/plan/decomposition all here).
Parallel boards (`.mathlib-quality/` = NewtonPolygons, `qmf/`, `jacobs/`,
`jacobs-endgame/`, `tatefredholm-eigen/`, `slashRefactor/`, `hurwitz-cn1/`) are other
projects' property — never touch them.  Every `/beastmode` run for this project must
name this board path explicitly.

**Skeleton compiles** (3788 jobs, sorries only; verified 2026-08-11): every proof
ticket = "fill the sorries of the named declarations".  **Statements are canonical in
the `.lean` files**; leaf ids (L…) refer to `decomposition.md` (verbatim source quotes
+ the design-refinement log there).  Source: [Jacobs, *Slopes of Compact Hecke
Operators*, 2003] — local PDF `~/Desktop/Papers/Jacobs - Slopes of Compact Hecke
Operators.pdf`; the **fork template** for ported proofs is
`PhD/JacobsSlash/U3/4_KappaSlash.lean` (sorry-free; line refs below are into it).
Build: `lake build PhD.QMF.Weight.Algebraic PhD.QMF.Weight.Char
PhD.JacobsSlash.U3.«5_KappaWeight»` covers the new surface;
`PhD.JacobsSlash.U3.«9_EigenvaluesU3»` guards the fork.
NOTE: other agents build this repo concurrently — expect waiting on the lake lock;
never kill another build.

## Summary
- Total: 35 tickets (21 proof/def + 14 cleanup)
- Open: 35 | Done: 0
- Milestone: T-M1 (classical quaternionic forms embed Hecke-equivariantly in the
  overconvergent space — "algebraic weights as an application, no recertification")
- Second milestone: T017 (the thesis's `U₃`-action = the general action at the Jacobs
  weight, and that weight is the expansion of `u ↦ uᵗ`)
- **R6 tranche (T018–T020, USER-DIRECTED 2026-08-11)**: the subspace uniformisation —
  `polySubmodule` + slash-equivariant iso + "classical = polynomial-valued
  overconvergent"; gated on T010/T-M1 (decision record in decomposition.md R6).
- Tier 2 (T012–T015, CLEANUP-7/8) is **severable**: if T014 stalls, tiers 0/1, both
  milestones and R6 are unaffected.
- Parallel capacity at start: 5 (T001 ∥ T006 ∥ T009 ∥ T011 ∥ T012 ∥ T016)

## R0 (DONE at planning time, recorded for history)
Infrastructure re-homing: `1_GenFun` → `PhD/TateFredholm/GenFun.lean` (namespace
`TateFredholm`; redundant `ext_matrixCoeff` deleted), `U3/1_Compose` →
`PhD/TateFredholm/Compose.lean`, generic layer of `2_U3Data` →
`PhD/TateFredholm/WeightGenFun.lean` (+`RowIntAt`); all fork references rewritten
(decl-name-set grep); `3_BaseChange` gained `open TateFredholm`.  Full fork chain
green.  Record the renames in `.mathlib-quality/renames.jsonl` during CLEANUP-R0.

---

### [T001] SigmaNorm monoid + LevelBounds + yExtend basics (L1.1, L1.2a)
- **Status**: done (2026-08-11, laweights beastmode) | **File**:
  PhD/QMF/Weight/Series.lean | **Depends**: none | **Parallel**: yes | **Type**: def API
- **Progress**:
  - 2026-08-11: statement amendment applied as recorded — `SigmaNorm` gained
    `(hρ0 : 0 ≤ ρ)`, `LevelBounds` gained `rho_nonneg` field, `Sigma0'.levelBounds`
    (SlashAction.lean) gained the `hρ0` hypothesis.  All downstream files rebuilt green
    (3445 jobs).
  - All T001 declarations proven: `SigmaNorm` (one_mem'/mul_mem' via
    `IsUltrametricDist.norm_add_le_max` + the isosceles
    `norm_add_eq_max_of_norm_ne_norm` for the d-entry), `mem_sigmaNorm_iff` (rfl),
    `levelBounds_sigmaNorm`, `LevelBounds.mono`, `LevelBounds.d_ne_zero`,
    `constantCoeff_linX`, `yExtend_yDeg0` (if_neg), `yExtend_one` (case split via
    `TateFredholm.fin2_eq_zero`).  Axioms: standard set (verified via #print axioms).
  - Post-proof cleanup: ✓ ran (Mode-A /cleanup on `SigmaNorm`: 35 → 24 lines, all
    gates pass incl. line-packing repack of the signature; no renames; worker
    checklist all ✓).  Small decls are one-liners already in final form; file-wide
    pass is CLEANUP-1 per board cadence.
  - Worker note for CLEANUP-1: `NormedField K` would suffice for `SigmaNorm` itself
    (nontriviality unused in-body) — flagged as possible generalisation, deferred.
  - DONE — remaining sorries in the file are T002's three lemmas (now at ~201–214).
- Fill: `SigmaNorm.one_mem'/mul_mem'` (:53), `levelBounds_sigmaNorm` (:73),
  `LevelBounds.mono` (:76), `LevelBounds.d_ne_zero` (:80), `constantCoeff_linX` (:97),
  `yExtend_yDeg0` (:137), `yExtend_one` (:140).
- Sketch: `one_mem`: entries of `1` are `0/1`, `‖0‖ = 0 ≤ ρ` (ρ ≥ 0 not assumed —
  use `‖g 1 0‖ ≤ ρ` never at `g = 1`… it IS at `g = 1`: `‖0‖ = 0 ≤ ρ` needs `0 ≤ ρ`;
  derive from nothing? NO — take the `det ≠ 0`/norm arithmetic: `0 ≤ ρ` is NOT free;
  use `le_trans (norm_nonneg _).le`?  `‖(1:M₂) 1 0‖ = ‖0‖ = 0 ≤ ρ` requires `0 ≤ ρ`.
  Resolution (recorded): prove `0 ≤ ρ` is needed and thread it — amend `SigmaNorm`/
  `LevelBounds` with `0 ≤ ρ` OR state `one_mem` via `max ρ 0`… simplest statement-safe
  fix: add hypothesis `hρ0 : 0 ≤ ρ` alongside `hρ : ρ < 1` in `SigmaNorm` and a
  `rho_nonneg` field in `LevelBounds` (statement amendment, allowed at ticket time —
  update the two instance sites `levelBounds_sigma1₃`, `Sigma0'.levelBounds`).
  `mul_mem`: `(gh)₁₁ = c_g b_h + d_g d_h`, `‖c_g b_h‖ ≤ ρ < 1 = ‖d_g d_h‖` ⇒ norm `= 1`
  (ultrametric `norm_add_eq_left/max`); `(gh)₁₀ = c_g a_h + d_g c_h ≤ max ρ ρ`;
  entries by `norm_sum/mul` bounds; `det_mul` + `mul_ne_zero`.  Template: the fork's
  `Sigma1₃.mul_mem'` (`U3/1_Setting.lean:713`) at valuation level.
  `yExtend_yDeg0/one`: unfold + `if_neg`/`MvPowerSeries.coeff_one` case split
  (template: fork `yDeg0_kappaSeries₂` :688, `kappaSeries₂_zero_one` :1476).
- Mathlib: `IsUltrametricDist.norm_add_le_max`, `norm_mul`, `Matrix.mul_apply`,
  `Fin.sum_univ_two`, `Matrix.det_mul`, `MvPowerSeries.coeff_one`.
- Source: Def 1.27 p. 19 ("It is an easy check that Σ_α is a monoid") — quote in
  decomposition L1.1.

### [T002] genFun integrality + column decay (L1.3)
- **Status**: done (2026-08-11, laweights beastmode) | **File**:
  PhD/QMF/Weight/Series.lean | **Depends**: T001 | **Parallel**: after T001 |
  **Type**: lemma
- **Progress**:
  - 2026-08-11: the ρ-based decay-predicate algebra went to its natural home
    `PhD/TateFredholm/WeightGenFun.lean` (design refinement): `RowIntAt` algebra
    (`rowIntAt_monomial`, `RowIntAt.add/neg/sub/mul/inv`, `rowIntAt_linSeries`,
    `rowIntAt_quadSeries`), `CoeffInt` (+`of_rowIntAt`, `coeffInt_monomial`,
    `CoeffInt.add/neg/sub/mul/inv`), `ShiftIntAt` (+`of_rowIntAt`,
    `shiftIntAt_monomial`, `.add/neg/sub/mul/inv`, private `shift_mul_le`) — all
    proven (ports of fork `4_KappaSlash:111–285` / `2_U3Data` rowInt family at base ρ).
  - Series.lean assembly proven: `rowIntAt_yExtend`, `rowIntAt_linSeries_of_mem`,
    `shiftIntAt_quadSeries_of_mem` (quad enters via SHIFT, not row — the fork's L5.2
    finding), `norm_constantCoeff_linSeries/quadSeries`, `coeffInt_genFun`,
    `norm_coeff_genFun_le_one`, `shiftIntAt_genFun`, `norm_coeff_genFun_le_shift`,
    `tendsto_coeff_genFun` (squeeze + `tendsto_pow_atTop_nhds_zero_of_lt_one`).
  - Series.lean + WeightGenFun.lean now **sorry-free**; downstream chain green
    (3445 jobs); axioms standard on all endpoints (#print verified).
  - Post-proof cleanup: file-level pass = CLEANUP-1, next in sequence (picked up
    immediately); WeightGenFun.lean additions fold into CLEANUP-R0's scope.
  - DONE.
- Fill: `norm_coeff_genFun_le_one` (:151), `norm_coeff_genFun_le_shift` (:158),
  `tendsto_coeff_genFun` (:164).
- Sketch: port fork `4_KappaSlash.lean:111–393` with base `‖3‖ ↦ ρ`: (1) private
  `CoeffInt`/`ShiftInt`-at-ρ closure algebra (monomial/add/neg/sub/mul/inv — the two
  `inv` inductions on `p 0 + p 1` via `MvPowerSeries.coeff_inv` are verbatim);
  (2) `RowIntAt ρ` versions of `rowInt_linSeries/quadSeries`
  (template `2_U3Data.lean:519,527`) from the `LevelBounds` fields; (3) assemble the
  three factors: the κ-factor is the `rowDecay` field via `yExtend` (coeffs vanish off
  `y`-degree 0), the `lin⁻¹` factor by `coeffInt_inv`+`constantCoeff_linSeries` +
  `d_unit`, the `quad⁻¹` by `shiftInt_inv`+`quadSeries_eq`; (4) decay: squeeze by
  `ρ^(j−i) → 0` (`tendsto_pow_atTop_nhds_zero_of_lt_one`, `Nat.cofinite_eq_atTop`,
  `Filter.tendsto_sub_atTop_nat`) — needs `0 ≤ ρ` and ρ < 1 from bounds.
- Mathlib: `MvPowerSeries.coeff_mul/coeff_inv`, `Finset.mem_antidiagonal`,
  `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `squeeze_zero_norm`,
  `tendsto_pow_atTop_nhds_zero_of_lt_one`.
- Source: p. 29 ("converges to an element of 𝒪₃[[x]]") + p. 30 Lemma 2.7 pattern;
  fork lines cited per step.  Edge recorded (fork L5.2 adversarial finding): full row
  decay is FALSE at `γ = 1` — only the shifted bound holds; statements already shaped
  for it.

### [CLEANUP-1] /cleanup PhD/QMF/Weight/Series.lean
- **Status**: done (2026-08-11, laweights beastmode; INLINE MODE per user direction —
  the user rejected the per-declaration subagent loop for this fresh small file) |
  **Depends**: T002 | **Type**: cleanup (final per-file)
- **Progress**:
  - Phase 0–3: baseline green; module docstring updated (`SigmaNorm K ρ hρ0 hρ`);
    zero λ/$-/push_neg/dividers/set_option; imports ordered.
  - Linter: **runLinter now ZERO findings** on Series.lean AND WeightGenFun.lean —
    removed the file-wide `linter.unusedSectionVars` suppression in WeightGenFun.lean,
    dropped the unused `[CompleteSpace K]` from its variable block, and added precise
    `omit` clauses across both files (≈30 declarations).
  - Phase 4: `SigmaNorm` had the full Mode-A deep-clean earlier (all gates, 35→24
    lines); remaining decls audited inline (all fresh, ≤12-line bodies, term-mode or
    tight tactic proofs; 9 missing public docstrings CREATED; line packing applied by
    the earlier passes; zero ≥/> in signatures; no renames needed — names follow
    mathlib `mem_X_iff`/`_of_mem` conventions).
  - Phase 5a/5b: no refactors, empty rename queue.  Phase 6: build green, downstream
    chain green (3445 jobs), no signature changes beyond docstrings/omits.
  - Phase 6.5 (holistic, inline): file uniform; no duplicated skeletons; deferred
    note — `NormedField K` might suffice for `SigmaNorm` (worker finding, recorded
    T001) — left for a future /generalise.
  - DONE.

### [T003] yCoeff calculus + the column identity (L1.5)
- **Status**: done (2026-08-11, laweights beastmode) | **File**:
  PhD/QMF/Weight/SlashAction.lean | **Depends**: T002 | **Parallel**: with T004 |
  **Type**: lemma
- **Progress**: full port of fork 4_KappaSlash:413-826 compiled FIRST TRY: the
  y-grading calculus (coeff_mul_of_yDeg0/1, yNum, quadSeries_eq_sub, yCoeff_linSeries/
  yNum/_inv, yDeg0_inv, yCoeff_sub/one_zero, + new yCoeff_yExtend_zero),
  matrixCoeff_kappaSlash (= matrixCoeff_ofGenFun, Prop 2.6 by design), yCoeff_genFun
  (base/step induction, kappaSeries2 -> yExtend col via yExtend_yDeg0), kappaSlash_apply.
  Axioms standard. DONE.
- Fill: `coeff_yCoeff` (:56), `matrixCoeff_kappaSlash` (:78, `:= matrixCoeff_ofGenFun …`),
  `yCoeff_genFun` (:84), `kappaSlash_apply` (:89).
- Sketch: port fork `:413–826` — the `yDeg0/yDeg1` column-grading lemmas
  (`coeff_mul_of_yDeg0/1`, `yCoeff_mul_yDeg0/1`, `yDeg0_inv`, `yCoeff_linSeries(_inv)`,
  `yCoeff_yNum`, `quadSeries_eq_sub` with `yNum`) as private lemmas, then the
  base/step induction of `yCoeff_weightGenFun` verbatim with `kappaSeries₂ ↦ yExtend
  (W.col …)` (its `y`-degree-0 input is `yExtend_yDeg0`).  `kappaSlash_apply` =
  `ofCoeffs_apply` + the column identity (fork :814).
- Mathlib: `PowerSeries.eq_inv_iff_mul_eq_one`, `MvPowerSeries.mul_inv_cancel`,
  `Finset.sum_nbij'`, `PowerSeries.coeff_mk`.
- Source: (2.1.3) p. 29 (quote in decomposition L1.5); fork B13a design note :718.

### [T004] The Möbius layer (L1.6)
- **Status**: done (2026-08-11, laweights beastmode) | **File**:
  PhD/QMF/Weight/SlashAction.lean | **Depends**: T001 | **Parallel**: with T003 |
  **Type**: lemma
- **Progress**: full port of fork :828-1029 compiled: linX_mul, numX_mul,
  linX_mul_eq, numX_mul_eq, mobius_mul_eq (closed form, NEW public intermediate),
  mobius_mul (skeleton's cross form, derived from _eq), absSummable_linX/numX/
  linX_inv, compAn_linX/numX, linX_inv_eq (geometric inverse), coeffLeOne_numX/
  linX_inv/mobius' (+ W-versions coeffLeOne_mobius/absSummable_mobius),
  constantCoeff_compAn_linX_ne_zero, compAn_mobius, compAn_mobius_mobius
  (W-version; (δ*γ)-nonzero via S.mul_mem + d_ne_zero).  5 cosmetic
  unusedSectionVars warnings deferred to CLEANUP-2.  DONE.
- Fill: `linX_mul` (:94), `numX_mul` (:98), `mobius_mul` (:104), `coeffLeOne_mobius`
  (:110), `absSummable_mobius` (:113), `compAn_mobius_mobius` (:118).
- Sketch: port fork `:828–1029` + the Σ-extraction forms `:1326–1345`: `linX_mul/
  numX_mul` are `Matrix.mul_apply` + `Fin.sum_univ_two` + `C`-algebra; `mobius_mul` is
  the cross-multiplied identity (statement here is already the substitution-free
  form); `coeffLeOne_mobius` from `LevelBounds` (entries ≤ 1, `d` unit — template
  `coeffLeOne_mobius` :978 + `coeffLeOne_numX/linX_inv` :955/:969); `absSummable` via
  geometric domination (template `absSummable_linX_inv` :934: needs `‖c‖ < ‖d‖ = 1`,
  i.e. ρ < 1); `compAn_mobius_mobius` via `compAn_mul/inv` + `compAn_linX/numX`
  (template `compAn_mobius` :1001, `compAn_mobius_mobius` :1017 — note the fork's
  hypothesis set maps to `LevelBounds` fields).
- Mathlib: `PowerSeries.C_mul`, `map_mul`, geometric `Summable` lemmas; the moved
  `PowerSeries.compAn_mul/compAn_inv/compAn_add` (TateFredholm/Compose).
- Source: fork lines above; character-free (no thesis quote needed beyond Def 1.27's
  display).

### [T005] The action laws (L1.7, L1.8)
- **Status**: done (2026-08-11, laweights beastmode) | **File**:
  PhD/QMF/Weight/SlashAction.lean | **Depends**: T003, T004 | **Parallel**: no |
  **Type**: theorem
- **Progress**: Def 1.27's "easy check" PROVEN ABSTRACTLY: absSummable_autFactor,
  autFactor_cocycle (the cocycle FIELD + compAn_mul/pow/inv — no hz hypothesis needed
  in the general form, unlike the fork), absSummable_yCoeff_genFun, yCoeff_genFun_mul
  (the column cocycle), kappaSlash_one (diagSeries collapse, fork-faithful),
  kappaSlash_mul (ext_matrixCoeff + column cocycle + coeff_mul_compAn),
  kappaSlashAction : RightSlashAction S c(N,K), smulSlashClass.  Axioms standard.
  DONE.
- Fill: `kappaSlash_one` (:124), `kappaSlash_mul` (:129), `smulSlashClass` (:150).
- Sketch: `_one`: port fork :1462–1494 (`quadSeries_one`, `linSeries_one`,
  `col_zero_one` field, diagonal series ↦ identity via `ext_matrixCoeff`).  `_mul`:
  port fork :1388–1460 — `ext_matrixCoeff`, both sides via `yCoeff` columns
  (`yCoeff_weightGenFun_mul` template :1400): LHS column = `autFactor(δγ)·w_{δγ}^r`,
  RHS = tsum-product; the κ-half is the **cocycle field** (where the fork invokes
  `kappaCol_cocycle`/`autFactor_cocycle` :1353, here `W.cocycle` + `mobius_mul` +
  `compAn_mobius_mobius`); convergence inputs are `absSummable` field +
  `norm_coeff_genFun_le_*`.  `smulSlashClass`: `map_smul` of the CLM.
- Mathlib: `ContinuousLinearMap.ext`, `tsum` algebra
  (`Summable.tsum_mul_left/right`), `TateFredholm.ext_matrixCoeff`.
- Source: Def 1.27 p. 19 ("‖κ is a right-action…"); expansion = the fork's honest
  proof (template lines above); quote in decomposition R1.

### [CLEANUP-2] /cleanup PhD/QMF/Weight/SlashAction.lean (interim)
- **Status**: done (2026-08-11, merged with CLEANUP-3 inline — file complete at that
  point) | **Depends**: T005 | **Type**: cleanup

### [T006] Transports: comap, twist, valuation dictionary (L1.9, L1.10)
- **Status**: done (2026-08-11, laweights beastmode) | **File**:
  PhD/QMF/Weight/SlashAction.lean | **Depends**: none | **Parallel**: yes (day-one) |
  **Type**: def API
- **Progress**: comap (one-liners via map_one/map_mul), twist (STATEMENT AMENDMENT:
  `[Semiring R]` -> `[CommSemiring R]` — slash_mul needs the two character scalars to
  commute; the classical instantiation is over a field so nothing is lost; recorded),
  Sigma0'.levelBounds (three dictionary hypotheses applied to Sigma0'.mem_iff's
  clauses).  Axioms: comap axiom-free, twist [propext], levelBounds standard.  DONE.
- Fill: `RightSlashAction.comap` fields (:162), `RightSlashAction.twist` fields
  (:179), `Sigma0'.levelBounds` (:207).
- Sketch: `comap`: one-liners (`map_one/map_mul` of τ + the source action's axioms).
  `twist`: `χ(δ₁δ₂) = χδ₁·χδ₂`, `mul_smul`, and the `hsmul` hypothesis to commute the
  scalar past the slash; `zero/add` by `smul_zero/smul_add`.  `Sigma0'.levelBounds`:
  the three dictionary hypotheses applied to `Sigma0'.mem_iff`'s four clauses
  (fork template: `norm_le_of_valued_le`/`norm_eq_one_of_valued_eq_one`
  `4_KappaSlash.lean:92–109` — those two lemmas are the generic dictionary at a
  rank-one completion).  Statement amendment from T001 lands here too (`rho_nonneg`).
- Mathlib: `MonoidHom.map_one/map_mul`, `smul_smul`, `Units.smul_def`, `mul_smul`.
- Source: elementary (decomposition L1.9 attack log); Def 1.27's Σ_α ↔ `Sigma0'`
  match is decomposition R1's design note.

### [CLEANUP-3] /cleanup PhD/QMF/Weight/SlashAction.lean (final)
- **Status**: done (2026-08-11, laweights beastmode; INLINE MODE per session
  convention) | **Depends**: T006, CLEANUP-2 | **Type**: cleanup (final per-file)
- **Progress**: runLinter to ZERO on SlashAction.lean (auto-fixpoint omit pass over
  the unusedSectionVars family; final section's variable line slimmed instead of
  omit); all public decls docstringed at write time; file fully sorry-free; downstream
  chain green (3445 jobs).  DONE.

### [T007] The forms space plumbing (L2.1, L2.2)
- **Status**: done (2026-08-11, laweights beastmode) | **File**:
  PhD/QMF/Weight/Forms.lean | **Depends**: T005, T006 | **Parallel**: no |
  **Type**: def API
- **Progress**: levelMonoidOfToS (Subtype.ext + simp), kappaLevelSMulSlashClass
  (map_smul through the comap).  Forms + heckeOperator were definitional and now
  elaborate against the proven instances.  **Forms.lean sorry-free — Def 1.30/1.32 at
  abstract weight COMPLETE**; with T001–T006 the whole tier-1 general layer
  (Series/SlashAction/Forms) is sorry-free on standard axioms.  DONE.
- Fill: `levelMonoidOfToS.map_one'/map_mul'` (:58), `kappaLevelSMulSlashClass` (:72).
- Sketch: corestriction one-liners (`Subtype.ext` + `map_one/map_mul` of θ);
  `SMulSlashClass` transports through `comap_slash` + `smulSlashClass` (T005).
  `Forms`/`heckeOperator` are already definitional (no sorry) — verify they elaborate
  against the filled instances and add `@[simp] mem_Forms_iff` if cheap.
- Source: Def 1.28 + 1.30 p. 19 (verbatim quotes in decomposition R2).

### [CLEANUP-4] /cleanup PhD/QMF/Weight/Forms.lean (final)
- **Status**: done (2026-08-11, inline — fresh 106-line file, all docstrings present,
  runLinter zero on the module) | **Depends**: T007 | **Type**: cleanup

### [T008] The algebraic weight datum (L4.1)
- **Status**: done (2026-08-11, laweights beastmode) | **File**:
  PhD/QMF/Weight/Algebraic.lean | **Depends**: T004 | **Parallel**: with T009, T011 |
  **Type**: def
- **Progress**: algWeightSeries PROVEN — col = linX^(n+2) on the nose (rfl bridge
  hcol); col_zero_one by simp; rowDecay via new private norm_coeff_linear_pow_le
  (induction on exponent, two-term ultrametric convolution); absSummable via
  absSummable_pow; cocycle = linX_mul_eq raised to the (n+2)-nd power through
  compAn_pow/compAn_linX — polynomial algebra, no ODE, exactly as planned.  Axioms
  standard.  DONE.
- Fill: `algWeightSeries` fields (:54): `col_zero_one`, `rowDecay`, `absSummable`,
  `cocycle`.
- Sketch: `col_zero_one`: `(C 1 + C 0·X)^(n+2) = 1` by `simp`.  `rowDecay`:
  `coeff m ((C d + C c X)^(n+2))` via `add_pow`/`PowerSeries.coeff_pow` (or induction):
  `= choose(n+2, m)·c^m·d^(n+2−m)` for `m ≤ n+2`, else 0; bound by
  `‖ℤ-cast‖ ≤ 1` (ultrametric: `IsUltrametricDist.norm_natCast_le_one`-form),
  `‖c‖^m ≤ ρ^m`, `‖d‖ = 1`; needs `0 ≤ ρ` for the `m > n+2` case (`0 ≤ ρ^m`).
  `absSummable`: finitely many nonzero coefficients
  (`summable_of_finite_support`-style).  `cocycle`: `linX (δγ) = C δ₁₀·numX γ +
  C δ₁₁·linX γ` (T004's `linX_mul`) ⇒ raise to `(n+2)`: LHS `col(lin(δγ))` =
  `(linX(δγ)-as-binomial)^(n+2)`; RHS = `col(lin γ)·compAn (col (lin δ)) (mobius γ)`
  with `compAn_pow`, `compAn_add`, `compAn_C`, `compAn_X`, `compAn_mul` and
  `mobius = numX·linX⁻¹`: both sides equal `(C δ₁₀·numX γ + C δ₁₁·linX γ)^(n+2)`
  after clearing `(linX γ)^(n+2)·(linX γ)⁻¹^(n+2)` (needs `constantCoeff (linX γ) =
  d ≠ 0` from `LevelBounds.d_ne_zero`).  No ODE, no binomial series.
- Mathlib: `add_pow`, `PowerSeries.coeff_pow`, `Commute.add_pow`, `map_pow`,
  the moved `compAn_*` family.
- Source: decomposition R4 prose (expansion by us; the recomputation
  `κ(u)=u^(n+2)` ⇒ `(cz+d)^(n−k)(az+b)^k` is Def 1.27's display evaluated).

### [T009] Dehomogenisation + the determinant twist (L4.2)
- **Status**: done (2026-08-11, laweights beastmode) | **File**: PhD/QMF/Weight/Algebraic.lean | **Depends**: none |
  **Parallel**: yes (day-one) | **Type**: def API
- Fill: `detTwist` fields (:75), `polyEmbed` fields (:83), `polyEmbed_apply` (:91),
  `polyEmbed_injective` (:96).
- Sketch: `detTwist`: `Sigma0'.adj_one`, `adj_mul` (anti-hom) + commutativity of `Kˣ`.
  `polyEmbed` linearity: `map_add/map_smul` of `MvPolynomial.coeff` pushed through the
  finite sum of `cSpace.single`; `_apply`: `cSpace.single`-orthogonality
  (`Finset.sum_apply'`-style, single evaluation); `injective`: a homogeneous `P` of
  degree `n` is determined by the coefficients of `X^k Y^(n−k)`, `k ≤ n`
  (`MvPolynomial.mem_homogeneousSubmodule` support argument: any monomial in the
  support has `deg₀ + deg₁ = n`).
- Mathlib: `MvPolynomial.coeff_add/coeff_smul`, `MvPolynomial.ext`,
  `mem_homogeneousSubmodule`, `Finsupp.single` arithmetic.
- Source: decomposition L4.2 (elementary; dehomogenisation `P ↦ P(z, 1)`).
- **Progress**: DONE, axioms standard.  detTwist via adj_one/adj_mul + `mul_comm`
  (+`detTwist_apply` rfl-simp); polyEmbed linearity via private `single_add/smul` +
  `DFunLike.ext` (c(ℕ,K) is a def-wrapper — plain `ext` has no lemma; use
  `DFunLike.ext` + rfl `add_apply/smul_apply/zero_apply`); `polyEmbed_apply` via
  private `sum_apply` + `Finset.sum_eq_single`; `injective` via homogeneous-support:
  `Finsupp.weight_apply`+`sum_fintype`+`Fin.sum_univ_two` massage; also
  `polyEmbed_apply_of_gt`/`polyEmbed_eq_coeff` (unrestricted index, T010 prep).

### [T010] THE BRIDGE: `polyEmbed_slash` (L4.3)
- **Status**: done (2026-08-11, laweights beastmode) | **File**: PhD/QMF/Weight/Algebraic.lean | **Depends**: T003,
  T008, T009 | **Parallel**: no | **Type**: theorem (KEY)
- Fill: `polyEmbed_slash` (:103).
- Sketch: (1) both sides `K`-linear in `P`; reduce to the basis `P = X^k Y^(n−k)`,
  `k ≤ n` (`homogeneousSubmodule` spanned by monomials).  (2) LHS: `slash_coe`
  (`QMF/Slash/WeightModule.lean:113`) + `matrixSubstR_X`: `P ∣ₛ δ = ν(adj δ) •
  (aX+bY)^k (cX+dY)^(n−k)`; dehomogenise: coefficient sequence of
  `(az+b)^k (cz+d)^(n−k)`.  (3) RHS: `kappaSlash_apply`/`yCoeff_genFun` (T003) at
  `algWeightSeries`: column `k` = `autFactor·mobius^k = (C d + C c X)^(n+2)·
  (linX δ)⁻²·(numX/linX)^k`; since `col = linX^(n+2)` on the nose
  (`algWeightSeries_col` + `linX` def match), cancel to
  `linX^(n−k)·numX^k` — a POLYNOMIAL; `polyEmbed` of a basis vector is
  `cSpace.single`-supported, and the tsum in `kappaSlash_apply` truncates to the
  single `i = k` term.  (4) Compare coefficientwise: both sides are the coefficient
  family of `(az+b)^k (cz+d)^(n−k)`; the scalar `detTwist ν δ = ν (adj δ)` matches
  (2)'s twist.  Seam check (recorded attack, decomposition R4): `matrixSubstR` is
  UNtransposed, `X ↦ aX + bY` — verified orientation on `P = X` gives `az + b` =
  numerator ✓; the `jTwist` seam of the LEFT library never enters (all right-tower).
- Mathlib: `MvPolynomial.aeval_X`, `map_pow`, `PowerSeries.coeff_mul`,
  `tsum_eq_single`, `Finset.sum_congr`.
- Source: decomposition R4 (the (1.5.13) display at `κ(u) = u^(n+2)`; expansion by
  us, self-contained route above).
- **R6 hand-off (binding)**: factor step (3)'s cancellation as a PUBLIC lemma —
  `autFactor_mul_mobius_pow_eq (algWeightSeries hb n) : autFactor · mobius^k =
  (linX γ)^(n−k) · (numX γ)^k` (for `k ≤ n`, `d ≠ 0`) — T018 consumes it for the
  degree bound instead of re-deriving the cancellation.
- **Progress**: PROVEN, axioms standard.  Route executed differs from sketch step (1)
  (no span-induction): coefficientwise via a dehomogenisation AlgHom `dehom :=
  aeval ![PowerSeries.X, 1]` — `coeff_dehom` (homogeneous seam, all `j`, both sides
  vanish `j > n`), `dehom_comp_matrixSubstR` (= `aeval ![numX, linX]`, algHom_ext),
  `homog_repr` (bidegree decomposition), `polyEmbed_eq_coeff` (unrestricted index) —
  then `kappaSlash_apply` + `tsum_mul_eq_sum_range` truncation and per-term
  `autFactor_mul_mobius_pow_eq` (public, hyps `d ≠ 0`, `i ≤ n`, exported with
  `autFactor_algWeightSeries`).  R6 hand-off satisfied.  TWO SEAM TRAPS recorded:
  (a) `tsum_eq_sum` must be stated OUTSIDE `section Valued` (Valued.toUniformSpace vs
  norm topology diamond breaks instance defeq); (b) `omit [CompleteSpace K]` cannot
  match inside `section Valued` (same diamond re-elaborates the binder type) — fixed
  by NAMING the binders `[iu :] [cs :]` and `omit iu cs in`.

### [CLEANUP-5] /cleanup PhD/QMF/Weight/Algebraic.lean (interim)
- **Status**: done (2026-08-11, inline — zero warnings on module build; runLinter
  findings all in other boards' TateFredholm deps, none in QMF/Weight; generic
  helpers hoisted out of Valued section; orphaned polyEmbed docstring reattached) | **Depends**: T010 | **Type**: cleanup (3rd proof ticket on file)

### [T011] Coefficient-module functoriality (L4.4)
- **Status**: done (2026-08-11, laweights beastmode) | **File**: PhD/QMF/Weight/Algebraic.lean | **Depends**: none |
  **Parallel**: yes (day-one) | **Type**: lemma
- Fill: `mapCoeff` fields (:120), `mapCoeff_slash` (:134),
  `mapCoeff_mem_levelSubmoduleSlash` (:143), `mapCoeff_mem_slashFixedPointsOfLE`
  (:151), `heckeOperatorSlash_mapCoeff` (:162).
- Sketch: `mapCoeff` well-defined: `left_invt` preserved by postcomposition;
  linearity pointwise.  `_slash`: unfold `AutomorphicFunction`'s slash instance
  (`Slash/AutomorphicFunction.lean:slash_apply`) + `hT`.  Membership: transformation
  law preserved (two-line, Def 1.30's display).  Hecke commutation:
  `heckeOperatorSlash_apply` finsum + `map_finsum` of the additive `T`-postcomposition
  + `_slash` per term (Def 1.32's `[UvU]φ = Σ_t φ|v_t`).
- Mathlib: `finsum` API (`map_finsum` needs `AddMonoidHom`), `DFunLike.ext`.
- Source: Def 1.30/1.32 pp. 19–20 (verbatim quotes in decomposition R2/L4.4).
- **Progress**: DONE first-compile, axioms standard (mapCoeff/mapCoeff_slash
  axiom-light: [propext, Quot.sound]).  mapCoeff via `left_invt'`; `_slash` =
  `ext + simp [hT]`; memberships by `mem_*_iff` rewrite + `← mapCoeff_slash`; Hecke
  commutation via `h.fintype` + `finsum_eq_sum_of_fintype` + `map_sum` (not
  map_finsum) + per-term `mapCoeff_slash` — exactly Def 1.32's display.

### [CLEANUP-6] /cleanup PhD/QMF/Weight/Algebraic.lean (final)
- **Status**: done (2026-08-11, inline with CLEANUP-5 — module builds warning-free,
  lint-zero on QMF/Weight; docstrings audited with the T010 fills) | **Depends**:
  T011, CLEANUP-5 | **Type**: cleanup

### [T012] Series evaluation basics (L5.1) — tier 2
- **Status**: done (2026-08-11) | **File**: PhD/QMF/Weight/Char.lean | **Depends**: none |
  **Parallel**: yes (day-one) | **Type**: lemma
- Fill: `hasSum_evalAt` (:53), `evalAt_one` (:56), `evalAt_mul` (:58).
- Sketch: `hasSum`: `‖coeff n f·zⁿ‖ ≤ ‖coeff n f‖` (‖z‖ ≤ 1) + comparison with the
  `AbsSummable` hypothesis (`Summable.of_norm_bounded`, ultrametric completeness
  `HasSum` from `Summable`).  `_one`: `tsum_eq_single 0`.  `_mul`: Cauchy product —
  `PowerSeries.coeff_mul` + `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`-form
  (the moved Compose file has `tsum_prod_eq_tsum_sum_antidiagonal` as template).
- Mathlib: `Summable.of_norm_bounded`, `Summable.hasSum`, `tsum_eq_single`.
- Source: decomposition L5.1.

- **Progress**: DONE (2026-08-11): `norm_coeff_mul_pow_le`/`summable_norm_evalAt`
  helpers + hasSum via `.of_norm.hasSum`; `evalAt_one` by `tsum_eq_single 0`;
  `evalAt_mul` by `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm` +
  antidiagonal reindex.  Axioms standard.
### [T013] Evaluation injectivity — Strassman (L5.2) — tier 2
- **Status**: done (2026-08-11) | **File**: PhD/QMF/Weight/Char.lean | **Depends**: T012 |
  **Parallel**: no | **Type**: theorem
- Fill: `eq_zero_of_forall_evalAt_eq_zero` (:67), `evalAt_injOn` (:71).
- Sketch: contrapose; `n₀ := Nat.find` minimal with `coeff n₀ f ≠ 0`.  For
  `0 < ‖z‖ ≤ r < min 1 (‖coeff n₀ f‖ / (sup-bound))`: split
  `evalAt f z = coeff n₀ f·z^n₀ + ∑'_{n>n₀}`; ultrametric: the tail has norm
  `≤ (sup ‖coeff‖)·‖z‖^(n₀+1) < ‖coeff n₀ f‖·‖z‖^n₀` — so `‖evalAt f z‖ =
  ‖coeff n₀ f‖·‖z‖^n₀ ≠ 0`.  Witness `z`: `NontriviallyNormedField` gives `x₀` with
  `1 < ‖x₀‖`; take `z = x₀⁻ᵏ` small.  `evalAt_injOn` := apply to `f − g`
  (AbsSummable closed under sub).  The sup-bound: `AbsSummable ⇒ BddAbove` of coeff
  norms (`Summable.tendsto_atTop_zero` + boundedness).
- Mathlib: `Nat.find_spec/min`, `IsUltrametricDist.norm_tsum_le_of_forall`-form,
  `NontriviallyNormedField.non_trivial`, `norm_zpow`.
- Source: [Koblitz, *p-adic Numbers…*, Ch. IV (Strassman)] — PDF in
  `~/Desktop/Papers/`; elementary smallest-index route (decomposition L5.2, our
  expansion; the residue-field-independence attack is recorded there).

- **Progress**: DONE (2026-08-11, proof co-authored by user in IDE): Strassman via
  minimal nonzero coefficient (`Nat.find`), small-`z` choice
  (`NormedField.exists_norm_lt`), `tsum_eq_add_tsum_ite` split, tail bounded by
  `C·‖z‖^(n₀+1)` through `norm_tsum_le_iSup`, strict-inequality contradiction; plus
  `evalAt_sub` and `evalAt_injOn`.
### [T014] Evaluation of compAn (L5.3) — tier 2 RISK LEAF
- **Status**: done (2026-08-11) | **File**: PhD/QMF/Weight/Char.lean | **Depends**: T012 |
  **Parallel**: with T013 | **Type**: theorem
- Fill: `evalAt_compAn` (:76).
- Sketch: `evalAt (compAn F w) z = ∑'_n (∑'_k coeff k F·coeff n (w^k))·zⁿ`
  (`coeff_compAn`); absolute convergence of the double family
  `(k,n) ↦ coeff k F·coeff n (w^k)·zⁿ` (bounds: `‖coeff n (w^k)‖ ≤ 1` from
  `CoeffLeOne.pow`, `‖z‖ ≤ 1`, `AbsSummable F` — dominated by `‖coeff k F‖` summed in
  `k`… the n-sum needs decay: use `‖coeff n (w^k)·zⁿ‖ ≤ 1` and interchange justified
  by `Summable.prod`-Fubini on the norm side; if the naive product bound is not
  summable in `(k,n)`, sharpen via the fork's `summable_norm_compAn_term` /
  `summable_coeff_mul` (moved Compose file :~100–170) which handle exactly this
  family).  Then `∑'_k coeff k F·(∑'_n coeff n (w^k) zⁿ) = ∑'_k coeff k F·
  (evalAt w z)^k` — the inner step is `evalAt` multiplicativity on powers (T012's
  `evalAt_mul` iterated: `evalAt (w^k) z = (evalAt w z)^k`) — `= evalAt F (evalAt w z)`
  (needs `‖evalAt w z‖ ≤ 1` from `CoeffLeOne` + ultrametric tsum bound).
  **HARD-STOP rule**: if the Fubini needs genuinely new summability infrastructure
  beyond `Summable.tsum_comm`-family + the Compose toolkit, stop with a B-report —
  tier 2 stalls here severably; do NOT weaken the statement.
- Mathlib: `Summable.tsum_comm`, `Summable.of_norm_bounded`,
  `tsum_mul_left`; Compose: `summable_norm_compAn_term`, `CoeffLeOne.pow`.
- Source: decomposition L5.3 (new mathematics; the risk leaf of tier 2).

- **Progress**: DONE (2026-08-11, risk leaf discharged; co-authored with user):
  Fubini via the ULTRAMETRIC cofinite criterion (`summable_of_tendsto_cofinite` on
  ℕ×ℕ — norm-Fubini is genuinely unavailable, `∑‖coeff w‖` may exceed 1); finite bad
  set = `biUnion` of finite fibres; `Summable.tsum_comm` swap split into
  `evalAt_compAn_step1`/`_inner` private lemmas to fit the heartbeat budget (no
  set_option).  `evalAt_pow` by induction over `evalAt_mul`.
### [CLEANUP-7] /cleanup PhD/QMF/Weight/Char.lean (interim)
- **Status**: done (2026-08-11) | **Depends**: T014 | **Type**: cleanup (3rd proof ticket on file)

- **Progress**: inline, folded into the T015 pass (omit-fixpoint to zero warnings).
### [T015] The honest-character constructor (L5.4, L5.5) — tier 2
- **Status**: done (2026-08-11) | **File**: PhD/QMF/Weight/Char.lean | **Depends**: T013, T014 |
  **Parallel**: no | **Type**: theorem
- Fill: `ExpansionData.absSummable_col` (:100), `lin_eval_cocycle` (:105),
  `toWeightSeries.col_zero_one/cocycle` (:113).
- Sketch: `absSummable_col`: from `rowDecay` + geometric comparison (`0 ≤ ρ < 1`).
  `lin_eval_cocycle`: 2×2 algebra — `evalAt (mobius γ) z = (a z + b)/(c z + d)`
  (evalAt of `numX·linX⁻¹` via T012 `_mul` + geometric inverse evaluation:
  `evalAt (linX γ)⁻¹ z = (cz+d)⁻¹` — prove via `evalAt_mul` on
  `linX·linX⁻¹ = 1` + `evalAt_one`), then `field_simp`+`Matrix.mul_apply`.
  `col_zero_one`: `evalAt (col 0 1) z = κ 1 = 1` for all `z` (the `eval` field at
  `g = 1`, `IsUnit 1`), so `col 0 1 − 1` vanishes on the ball ⇒ `= 0` by T013 (both
  sides AbsSummable).  `cocycle`: evaluate both sides at `‖z‖ ≤ 1`:
  LHS `= κ(lin(δγ)(z))`; RHS `= κ(lin γ z)·evalAt (compAn (col δ) (mobius γ)) z
  = κ(lin γ z)·κ(lin δ (w_γ z))` by T014 + the `eval` field at the point `w_γ z`
  (`‖w_γ z‖ ≤ 1` from `CoeffLeOne`-boundedness; `IsUnit` of the evaluated linear
  forms from `d_unit` + ultrametric 1-unit arithmetic); conclude by κ.map_mul +
  `lin_eval_cocycle` + T013 injectivity.
- Mathlib: `Units.isUnit`, `IsUnit.unit_spec`, `map_mul`, `field_simp`.
- Source: Def 1.27 p. 19 (the "power series expansion" phrase = the `eval` field);
  p. 29's pointwise move (quote in decomposition R5); j-cocycle is classical 2×2
  algebra.

- **Progress**: DONE — the honest-character constructor is sorry-free, axioms
  standard.  SKETCH GAP FOUND AND CLOSED (recorded): the cocycle RHS
  `col γ · compAn (col δ) (mobius γ)` is NOT provably `AbsSummable` (compAn of an
  abs-summable outer along a CoeffLeOne inner is only coefficient-BOUNDED —
  `∑‖coeff w‖` may exceed 1, so the norm-tsum can diverge); the designed
  `evalAt_injOn` route was therefore supplemented by **bounded-coefficient Strassman
  on the OPEN unit ball** (`eq_zero_of_forall_evalAt_eq_zero_of_le`,
  `evalAt_injOn_of_le`, private) plus `CoeffLeOne.mul` (ultrametric convolution),
  `coeffLeOne_compAn`, `norm_evalAt_le_one`, `evalAt_C/X/add/linX/numX/linX_inv/
  mobius` evaluation calculus, and `lin_value_ne_zero` (isosceles).  The cocycle is
  then: evaluate at `‖z‖ < 1`, both factors are units (dominant `d`),
  `lin_eval_cocycle` (field identity through `evalAt_mobius`), κ-multiplicativity +
  `Units.ext`.  `col_zero_one` via the unprimed injOn at `g = 1` (nth_rewrite to
  dodge a dependent motive).  Fields reference standalone private lemmas
  (heartbeat discipline).  Co-authored with user's IDE session.
### [CLEANUP-8] /cleanup PhD/QMF/Weight/Char.lean (final)
- **Status**: done (2026-08-11) | **Depends**: T015, CLEANUP-7 | **Type**: cleanup

- **Progress**: inline — Char.lean at zero module warnings and zero runLinter
  findings; docstrings on all public declarations.
### [T016] The Jacobs weight datum (L3.1, L3.3)
- **Status**: done (2026-08-11, laweights beastmode) | **File**: PhD/JacobsSlash/U3/5_KappaWeight.lean | **Depends**:
  none (statements ready; T001's `rho_nonneg` amendment lands here as a field fill) |
  **Parallel**: yes (day-one) | **Type**: def
- Fill: `levelBounds_sigma1₃` (:45), `qmfMobius_eq` (:48), `jacobsWeightSeries`
  fields (:55).
- Sketch: `levelBounds_sigma1₃`: package `norm_sigma1_entry_le_one` (:1279),
  `norm_sigma1_lower_left_le` (:1296, gives `≤ ‖3‖² ≤ ‖3‖`), `norm_sigma1_lower_right`
  (:1291); `ρ < 1` = `norm_three_lt_one`; `0 ≤ ρ` = `norm_nonneg`.  `qmfMobius_eq`:
  `rfl` or `unfold`-refl (identical bodies).  Fields: `col_zero_one` — 3-line reproof
  of the fork's private `kappaSeries₂_zero_one` at the 1-variable level (`unitPow t 1
  = 1` via `unitPow_one`, `binomialCoeff t 0 = 1`, `(0/1)^n` kills `n > 0`) OR make
  the private lemma public (fork edit, one line) and derive; `rowDecay` ←
  `rowInt_kappaSeries₂` (`2_U3Data`) read through `coeff_yCoeff`-style index
  translation (the 1-var coeff at `n` = the 2-var coeff at `idx n 0`), hypotheses from
  `norm_sigma1_*`; `absSummable` ← `absSummable_kappaCol` (:1307) +
  `norm_sigma1_lower_right_sub_one_le`/`norm_sigma1_ratio_le`; `cocycle` ←
  `kappaCol_cocycle` (:1251) with its hypothesis set discharged by the `norm_sigma1_*`
  family (exactly as `kappaSlash_mul` :1434 does) + `qmfMobius_eq` to translate
  `QMF.mobius` ↔ fork `mobius` and `yCoeff (kappaSeries₂ …) 0 = col` (coeff_mk).
- Mathlib: none beyond the fork's own lemmas.
- Source: p. 29 (quote in decomposition R3); every discharge is an existing
  sorry-free fork theorem — **zero re-certification** (M2's contract).
- **Progress**: DONE, axioms standard.  `levelBounds_sigma1₃` = packaged
  `norm_sigma1_*`; `qmfMobius_eq` is `rfl` (definitional agreement of the two Möbius
  layers); `col_eq_yCoeff` (private) transports every field to the fork lemma:
  rowDecay ← `norm_unitPow_le_one`+`norm_binomialCoeff_mul_pow_le` (direct, no index
  translation needed — `coeff_mk`), absSummable ← `absSummable_kappaCol_sigma1`,
  cocycle ← `kappaCol_cocycle` with the `kappaSlash_mul` hypothesis-discharge pattern.
  TRAPS: (a) per-declaration heartbeat budget — the four field proofs are standalone
  private theorems (`jacobsCol_*`), the `where`-def is pure assembly; (b) the
  `⟨δ,hδS⟩ * ⟨γ,hγS⟩` Submonoid-mul coercion is a defeq bomb on K₃ (isDefEq timeout
  at 32× budget!) — use the literal `⟨δ * γ, mul_mem hδS hγS⟩` instead.

### [T017] The identification + the honest-character statement (L3.2, L3.4) — MILESTONE M2
- **Status**: done (2026-08-11, laweights beastmode) — **MILESTONE M2 REACHED** | **File**: PhD/JacobsSlash/U3/5_KappaWeight.lean | **Depends**:
  T016 | **Parallel**: no | **Type**: theorem
- Fill: `yExtend_jacobsCol` (:66), `genFun_jacobsWeightSeries` (:72),
  `kappaSlash_eq_general` (:78), `hasSum_jacobsCol_unitPow` (:84).
- Sketch: `yExtend_jacobsCol`: `MvPowerSeries.ext` + `coeff_yExtend` +
  `coeff_kappaSeries₂` + `PowerSeries.coeff_mk` — both sides are the same
  if-then-else.  `genFun_…`: rewrite by it + `weightGenFun` def (same three factors).
  `kappaSlash_eq_general`: both sides `ofGenFun` of equal series; `ofGenFun` is
  proof-irrelevant in the bound arguments — `TateFredholm.ext_matrixCoeff` +
  `matrixCoeff_ofGenFun` on both sides + `genFun_…`.  `hasSum_…`:
  `tsum_binomialCoeff_eq_unitPow` (`3_BinomialTheorem.lean:252`) at `e = c/d`, times
  the constant `unitPow t d`; `unitPow_mul` (`1_PadicAnalytic`) assembles
  `unitPow t d · unitPow t (1 + (c/d)z) = unitPow t (cz + d)` (1-unit hypotheses from
  `hd`/`hcd`/`hz` — boundary `‖z‖ = 1` attack recorded in decomposition R3: the
  binomial domain bound comes from `‖c/d‖ ≤ ‖3‖²`, not from `‖z‖ < 1`).
- Mathlib: `HasSum.mul_left`, `MvPowerSeries.ext`.
- Source: p. 29 verbatim (decomposition R3); [Jacobs, §2.1] as formalised in the
  fork's `3_BinomialTheorem`.
- **Progress**: ALL FOUR PROVEN, axioms standard, file sorry-free + zero warnings.
  `jacobsWeightSeries_col` rfl-simp added; `yExtend_jacobsCol` by ext + split_ifs;
  `genFun_…` a 1-line rw (same three factors, shared `TateFredholm.linSeries/quadSeries`);
  `kappaSlash_eq_general` by `ext_matrixCoeff` + both `matrixCoeff_kappaSlash`es +
  `genFun_…` — **the fork action IS the general action**; `hasSum_…` via
  `summable_binomialCoeff_mul_pow`.hasSum + `tsum_binomialCoeff_eq_unitPow`
  (hdense := `exists_natCast_close`) + `HasSum.mul_left` + `unitPow_mul` (NB leading
  `h3` section arg!) + `field_simp; ring` for `d(1 + (c/d)z) = cz + d`.

### [CLEANUP-9] /cleanup PhD/JacobsSlash/U3/5_KappaWeight.lean (final)
- **Status**: done (2026-08-11, inline — zero module warnings, docstrings on all
  public decls, private helpers docstring-free) | **Depends**: T017 | **Type**: cleanup

### [CLEANUP-R0] Post-refactor hygiene on the moved surface
- **Status**: done (2026-08-11, laweights beastmode — 3 rename records appended;
  2_U3Data stale refs fixed to `matrixCoeff_kappaSlash`/`«4_KappaSlash»`; GenFun.lean's
  two per-decl + one FILE-WIDE `set_option linter.unusedSectionVars false` replaced by
  8 targeted omits; runLinter clean on all three moved modules; residual warnings all
  in tatefredholm-eigen board files, untouched) | **Depends**: none | **Parallel**: yes | **Type**: cleanup
- Scope: `PhD/TateFredholm/GenFun.lean` (+`Compose`, `WeightGenFun`),
  `PhD/JacobsSlash/2_U3Data.lean`, `3_BaseChange.lean`: (1) record the three moves in
  `.mathlib-quality/renames.jsonl`; (2) fix the STALE docstring cross-references the
  inventory found (`2_U3Data` cites `JacobsSlash.U3.matrixCoeff_kappaOp` /
  `PhD.JacobsSlash.U3.KappaAction` — live names are `matrixCoeff_kappaSlash` /
  `U3.«4_KappaSlash»`; module-name cites need guillemet forms); (3) drop the
  file-wide `set_option linter.unusedSectionVars false` in `WeightGenFun.lean` in
  favour of per-lemma `omit`s; (4) `lake exe runLinter` on the three TateFredholm
  modules.

### [CLEANUP-ALL-1] /cleanup-all on the board surface
- **Status**: done (2026-08-11 — full surface build warning-free after adding
  `@[instance_reducible]` to `RightSlashAction.comap`/`twist`/`kappaLevelSlashAction`
  per classDefReducibility; runLinter clean on QMF/Weight + moved TateFredholm
  modules; Char.lean excluded, tier-2 still open) | **Depends**: CLEANUP-1, CLEANUP-3, CLEANUP-4, CLEANUP-6,
  CLEANUP-9, CLEANUP-R0 (CLEANUP-8 too if tier 2 ran) | **Type**: cleanup-all
  (pre-milestone gate)

### [T-M1] MILESTONE: classical forms embed in the overconvergent space (L4.5)
- **Status**: done (2026-08-11, laweights beastmode) — **MILESTONE REACHED** | **File**: PhD/JacobsSlash/U3/5_KappaWeight.lean (or a new
  `U3/6_…` file if the import depth demands) + possibly a thin general lemma in
  PhD/QMF/Weight/Algebraic.lean | **Depends**: T007, T010, T011, CLEANUP-ALL-1 |
  **Parallel**: no | **Type**: theorem (MILESTONE)
- **Statement to author** (per decomposition L4.5; canonicalise at pickup): at the
  `K₃` instantiation (`G = Dfx ℚ D`, `θ = toMatrix ℚ D v₃`, `S` ⊇ the classical
  level), the map `AutomorphicFunction.mapCoeff (polyEmbed n ν)` sends the classical
  right-slash quaternionic space (`SpaceSlash`-shaped, coefficient `WeightModule K₃ n ν`)
  into `QMF.Weight.Forms` at `algWeightSeries` **twisted by `detTwist ν`**
  (`RightSlashAction.twist` on the level action), Hecke-equivariantly for `[UηU]`.
  Route: T010 (pointwise intertwining incl. twist) + T011 (functoriality) + T007
  (the spaces); the twist enters as the `letI` action choice on the target level
  space.  NO recertification: `SpaceSlash`/`WeightModule` results are consumed as-is.
- Source: Def 1.30's "any right Σ_α-module" + decomposition R4; this is the board's
  raison d'être ("the current algebraic weights should exist as a nice application").
- **Progress**: PROVEN (first-compile), axioms standard, in
  PhD/QMF/Weight/Algebraic.lean (final section) — **canonicalised statement is the
  GENERAL (G, θ) form** with `S := Sigma0' K γv hγv` itself (via `Sigma0'.levelBounds`
  no inclusion hypothesis is needed; both sides share the level monoid
  `Weight.levelMonoidOf θ Σ₀'`).  The quaternionic K₃ reading is definitional:
  `levelMonoid' = levelMonoidOf (toMatrix)`, `SpaceSlash = levelSubmoduleSlash`,
  Quaternionic's WeightModule instance = `classicalWeightAction` (all comap-shaped),
  so no U3/6 file is needed.  Pieces: `classicalWeightAction`/`twistedKappaLevelAction`
  (comap + twist by `(detTwist ν).comp levelMonoidOfToS`, both `@[instance_reducible]`),
  SMulSlash companions, `polyEmbed_slash_level` (T010 through the plumbing, a `show` +
  `exact polyEmbed_slash`), `classicalToOverconvergent_mem` (= T011's
  `mapCoeff_mem_levelSubmoduleSlash`), `heckeOperatorSlash_classicalToOverconvergent`
  (= T011's `heckeOperatorSlash_mapCoeff`).  Zero recertification, exactly as
  contracted.

---

## R6 tranche — the subspace uniformisation (USER-DIRECTED 2026-08-11)

Decision record + leaves + attack notes: decomposition.md §R6.  Skeleton note: these
three tickets' declarations are NOT yet in the `.lean` skeleton (they are gated on
T010/T-M1, whose proven forms fix the statements) — **the first R6 ticket picked up
begins by adding its declarations with `:= by sorry` and `lake build`-gating them**,
per the board's skeleton discipline; the drafts below are near-final.

### [T018] The polynomial submodule and its stability (L6.1)
- **Status**: done (2026-08-11, laweights beastmode) | **File**: PhD/QMF/Weight/Algebraic.lean | **Depends**: T010,
  CLEANUP-6 | **Parallel**: with T-M1 | **Type**: def API
- Declarations to add (skeleton-first):
  ```lean
  def polySubmodule (K) [NontriviallyNormedField K] [IsUltrametricDist K]
      [CompleteSpace K] (n : ℕ) : Submodule K c(ℕ, K) where
    carrier := {f | ∀ m : ℕ, n < m → f m = 0}
    …
  @[simp] theorem mem_polySubmodule_iff …
  theorem single_mem_polySubmodule (hk : k ≤ n) : cSpace.single k r ∈ polySubmodule K n
  theorem polySubmodule_stable (hb : LevelBounds S ρ) (n : ℕ) (g : S) {f : c(ℕ, K)}
      (hf : f ∈ polySubmodule K n) :
      (algWeightSeries hb n).kappaSlash g f ∈ polySubmodule K n
  ```
- Sketch: membership/closure one-liners.  Stability: `kappaSlash_apply` (T003) writes
  coefficient `j` of the image as `∑' i, coeff j (autFactor·mobius^i) · f i`; the
  tsum truncates to `i ≤ n` (`tsum_eq_sum` on the support bound `hf`); for `i ≤ n`,
  T010's hand-off lemma `autFactor_mul_mobius_pow_eq` gives
  `autFactor·mobius^i = (linX g)^(n−i)·(numX g)^i`, a polynomial of `X`-degree
  `≤ n`, so `coeff j = 0` for `j > n` (`PowerSeries.coeff_mul`-degree bound or
  `Polynomial`-cast argument).
- Mathlib: `tsum_eq_sum`, `PowerSeries.coeff_pow` degree vanishing
  (`coeff_eq_zero_of_natDegree_lt`-style via `Polynomial.coe`), `Finset.sum_eq_zero`.
- Source: decomposition R6 L6.1 (degree computation = R4's, already attack-logged).
- **Progress**: PROVEN, axioms standard.  New private `coeff_linear_pow_eq_zero`
  (induction; same convolution split as the norm bound) + `coeff_linX_pow_mul_numX_pow_
  eq_zero` (antidiagonal); stability = `kappaSlash_apply` + `tsum_mul_eq_sum_range` +
  the R6 hand-off `autFactor_mul_mobius_pow_eq`, exactly per sketch.  NB
  `cSpace.single` captures IsUltrametricDist/CompleteSpace from ModelSpace's section —
  no omit on `single_mem_polySubmodule`.

### [T019] The slash-equivariant isomorphism (L6.2)
- **Status**: done (2026-08-11, laweights beastmode) | **File**: PhD/QMF/Weight/Algebraic.lean | **Depends**: T018
  (and T009, T010 already via T018) | **Parallel**: no | **Type**: def + theorem
- Declarations to add (skeleton-first):
  ```lean
  theorem range_polyEmbed (n ν) :
      LinearMap.range (polyEmbed n ν) = polySubmodule K n
  noncomputable def polyEmbedEquiv (n ν) :
      WeightModule K n ν ≃ₗ[K] polySubmodule K n      -- polyEmbed corestricted
  @[simp] theorem polyEmbedEquiv_coe (P) : (polyEmbedEquiv n ν P : c(ℕ, K)) = polyEmbed n ν P
  theorem polyEmbedEquiv_slash (hb) (δ : Sigma0' K γv hγv) (hδ : δ.1 ∈ S) (P) :
      (polyEmbedEquiv n ν (P ∣ₛ δ) : c(ℕ, K))
        = detTwist ν δ • (algWeightSeries hb n).kappaSlash ⟨δ.1, hδ⟩ (polyEmbedEquiv n ν P)
  ```
- Sketch: `range ⊆` is T018's support bound on `polyEmbed`'s finite sum; `⊇` by the
  homogenisation section `f ↦ ∑_{k ≤ n} f k · X^k Y^(n−k)` (lands in
  `homogeneousSubmodule` by monomial degrees; `polyEmbed ∘ section = id` by
  `polyEmbed_apply`, `section ∘ polyEmbed = id` by `MvPolynomial.ext` on the
  homogeneous support — the T009 injectivity argument reused).  `polyEmbedEquiv` :=
  `LinearEquiv.ofLinear` of the corestriction and the section.  `_slash` is
  `polyEmbed_slash` (T010) conjugated by `_coe` — one `Subtype.ext` rewrite.
  Note the underlying equivalence is ν-uniform (`WeightModule`'s ν is a phantom);
  only the `_slash` statement mentions ν.
- Mathlib: `LinearEquiv.ofLinear`, `LinearMap.codRestrict`,
  `MvPolynomial.sum_monomial` API, `mem_homogeneousSubmodule`.
- Source: decomposition R6 L6.2.
- **Progress**: PROVEN, axioms standard.  `homogenise` linear section (explicit
  `show`-forms for the coe-through-sum linearity; `isHomogeneous_monomial` +
  `Finsupp.degree_single`), `polyEmbed_homogenise`/`homogenise_polyEmbed` (the second
  is `homog_repr` + `polyEmbed_apply` on the nose), `polyEmbed_mem_polySubmodule`,
  `range_polyEmbed`, `polyEmbedEquiv` via `LinearEquiv.ofLinear`+`codRestrict`,
  `polyEmbedEquiv_coe` rfl-simp, `polyEmbedEquiv_slash` = T010 conjugated.

### [T020] Classical = polynomial-valued overconvergent (L6.3) — R6 ENDPOINT
- **Status**: done (2026-08-11, laweights beastmode) — **R6 ENDPOINT REACHED** | **File**: PhD/JacobsSlash/U3/5_KappaWeight.lean (or T-M1's file)
  | **Depends**: T-M1, T019 | **Parallel**: no | **Type**: theorem
- Statement (author against T-M1's proven form; near-final draft):
  ```lean
  theorem mem_range_classicalToOverconvergent_iff (ψ) :
      (∃ φ ∈ <classical space>, AutomorphicFunction.mapCoeff (polyEmbed n ν) φ = ψ)
        ↔ ψ ∈ <twisted Weight.Forms at algWeightSeries> ∧ ∀ g, ψ g ∈ polySubmodule K n
  ```
- Sketch: (→) T-M1 (membership) + `mapCoeff_apply` + T018/T019 range (pointwise
  values).  (←) define `φ g := polyEmbedEquiv.symm ⟨ψ g, h.2 g⟩`; `Γ`-left-invariance
  is pointwise transport; the classical `U`-transformation law follows from the
  overconvergent one by applying `polyEmbedEquiv.symm` to `polyEmbedEquiv_slash`
  (T019) — the twist scalar cancels on both sides; `mapCoeff … φ = ψ` by
  `Subtype.ext`-pointwise.  This makes the classical space literally the
  polynomial-valued subspace of the overconvergent space, with `WeightModule` kept
  primary (decision record, decomposition R6).
- Source: decomposition R6 L6.3; [Buzzard, *Eigenvarieties*, §9] (the classical
  subspace of the Banach module).
- **Progress**: PROVEN in T-M1's file (final section of PhD/QMF/Weight/Algebraic.lean
  — no new U3 file needed since T-M1 was canonicalised at general (G, θ)), axioms
  standard.  `mem_range_classicalToOverconvergent_iff` exactly as drafted; (→) =
  T-M1 + `polyEmbed_mem_polySubmodule`; (←) builds `φ g := polyEmbedEquiv.symm ⟨ψ g,
  h.2 g⟩` (left-invariance via `congrArg symm ∘ Subtype.ext` — avoids the dependent-
  motive rw), membership by `polyEmbed_injective` + `polyEmbed_slash_level` +
  the `hE` symm-cancellation, `mapCoeff` identity pointwise.  NB
  `mem_levelSubmoduleSlash_iff` takes explicit `(R := K)`.

### [CLEANUP-10] /cleanup PhD/QMF/Weight/Algebraic.lean (post-R6)
- **Status**: done (2026-08-11, inline — module builds warning-free, runLinter zero
  on QMF/Weight; docstrings on all new public decls) | **Depends**: T019 | **Type**:
  cleanup (T018+T019 = 2 new proof tickets after CLEANUP-6; final re-clean of the file)

### [CLEANUP-11] /cleanup on T020's file (post-R6)
- **Status**: done (2026-08-11 — T020 landed in Algebraic.lean, covered by
  CLEANUP-10's pass; 5_KappaWeight untouched by R6) | **Depends**: T020 | **Type**:
  cleanup

### [CLEANUP-FINAL] /cleanup-all (whole project surface)
- **Status**: done (2026-08-11) — full board surface (QMF/Weight ×5, JacobsSlash
  5_KappaWeight, TateFredholm GenFun/Compose/WeightGenFun) builds with ZERO
  warnings, zero sorries, runLinter-clean; all milestone declarations on standard
  axioms [propext, Classical.choice, Quot.sound]. | **Depends**: T-M1, T020, CLEANUP-10, CLEANUP-11 (and
  T015/CLEANUP-8 if tier 2 ran) | **Type**: cleanup-all (last ticket)

---

## Dependency fronts

Day-one parallel starts: **T001 ∥ T006 ∥ T009 ∥ T011 ∥ T012 ∥ T016** (+CLEANUP-R0).
Critical path to M2: T016 → T017.
Critical path to M1: T001 → T002 → T003 → T005 → T007 → T-M1 (with T004 feeding T005,
T008/T009 feeding T010 → T-M1).
R6 tranche: T010 → T018 → T019 → (with T-M1) T020 → CLEANUP-10/11 → CLEANUP-FINAL.
Tier 2 path: T012 → {T013 ∥ T014} → T015 (severable; hard-stop rule in T014).


---

## R7 tranche — one-unit characters (USER-DIRECTED 2026-08-12)

Decision record + leaves + attack log: decomposition.md §R7.  Skeleton discipline:
the first R7 ticket picked up adds its declarations `:= by sorry` and `lake build`-
gates them before filling.  Blast radius of the in-place `ExpansionData` amendment is
ZERO (no importer of Weight.Char — grep-verified 2026-08-12); the T012–T015 ticket
Statements remain the record of the OLD form, amended per this tranche (T006
precedent).

### [T021] The `oneUnits` subgroup + membership criterion (L7.1)
- **Status**: done (2026-08-12, laweights beastmode R7) | **File**: PhD/QMF/Weight/Char.lean (pre-`ExpansionData` section)
  | **Depends**: none | **Parallel**: with T022 skeleton | **Type**: def API
- Declarations to add (skeleton-first):
  ```lean
  def oneUnits (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) : Subgroup Kˣ where
    carrier := {u | ‖(u : K) - 1‖ ≤ r} …
  @[simp] theorem mem_oneUnits_iff …
  theorem norm_eq_one_of_mem_oneUnits …          -- ‖u‖ = 1 for members
  theorem levelUnit_mem_oneUnits {c d z : K}      -- the discharge criterion
      (hc : ‖c‖ ≤ r) (hd : ‖d - 1‖ ≤ r) (hz : ‖z‖ ≤ 1)
      (hu : IsUnit (c * z + d)) : hu.unit ∈ oneUnits r hr0 hr1
  ```
- Sketch: members have norm 1 by isosceles (`‖u−1‖ ≤ r < 1 = ‖1‖`,
  `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` on `u = 1 + (u−1)`); `mul_mem`
  via `uv − 1 = u(v−1) + (u−1)` + `norm_add_le_max` + norm-1; `inv_mem` via
  `u⁻¹ − 1 = u⁻¹(1 − u)`, `norm_mul`, `norm_inv`; criterion via
  `cz + d − 1 = cz + (d−1)` + `norm_add_le_max` + `IsUnit.unit_spec`.
- Mathlib: `IsUltrametricDist.norm_add_le_max`, `norm_inv`, `Units.val_inv_eq_inv_val`.
- Source: §R7 L7.1 (elementary; the principal-unit subgroup of Def 1.27's domain).
- **Progress**: DONE, axioms standard, zero warnings (inline cleanup).  `K` made an
  EXPLICIT arg of `oneUnits` (deviation from draft spelling, recorded: `r : ℝ` cannot
  infer `K`); private isosceles helper `norm_eq_one_of_norm_sub_one_le'` (needs
  IsUltrametricDist — only CompleteSpace omitted); `mul_mem` via
  `uv − 1 = u(v−1) + (u−1)`, `inv_mem` via `inv_mul_cancel₀`, criterion via
  `cz + d − 1 = cz + (d−1)` + `IsUnit.unit_spec`, all per sketch.

### [T022] Generalise `ExpansionData` to a subgroup character (L7.2, L7.3)
- **Status**: done (2026-08-12, laweights beastmode R7) | **File**: PhD/QMF/Weight/Char.lean + PhD/QMF/Weight/Series.lean
  (for `WeightSeries.ext`) | **Depends**: T021 (only for the build to stay green if
  done together; the amendment itself is T021-free) | **Parallel**: no | **Type**:
  def amendment + theorem
- **STATEMENT AMENDMENT (recorded)**: `ExpansionData (S) (ρ)` gains parameters
  `(U : Subgroup Kˣ) (κ : U →* Kˣ)` replacing `(κ : Kˣ →* Kˣ)`; new Prop field
  `mem_level : ∀ {g}, g ∈ S → ∀ z : K, ‖z‖ ≤ 1 →
    ∀ hu : IsUnit (g 1 0 * z + g 1 1), hu.unit ∈ U`
  (declared BEFORE `eval`); `eval` becomes
  `… evalAt (col (g 1 0) (g 1 1)) z = (κ ⟨hu.unit, mem_level hg z hz hu⟩ : K)`.
  Old behaviour = `U := ⊤`.  T012–T015 artifacts amended in place (zero consumers).
- Fill: adapt `col_zero_one'` (`⟨hu.unit, _⟩ = 1` by `Subtype.ext (Units.ext …)`,
  then `map_one`), `cocycle'` (three memberships from `mem_level` at `(γ,z)`,
  `(δ,z′)`, `(δγ,z)`; unit identification becomes
  `Subtype.ext (Units.ext (lin_eval_cocycle …))`; `map_mul` in `U`);
  `absSummable_col`/`lin_eval_cocycle`/`toWeightSeries` shape unchanged.
  Add `WeightSeries.ext {W₁ W₂ : WeightSeries S ρ} (h : W₁.col = W₂.col) : W₁ = W₂`
  in Series.lean (`bounds : LevelBounds` is a Prop-structure, all other fields
  Props; `cases` + `subst` + proof irrelevance).
- Mathlib: `Subtype.ext`, `Units.ext`, proof irrelevance (rfl after subst).
- Source: §R7 L7.2/L7.3 + Def 1.27 p. 15 quote; attacks A1/A2/A5/A7.
- **Progress**: DONE, axioms standard, zero warnings, full downstream surface
  rebuilds clean.  AMENDMENT APPLIED as drafted: `(U : Subgroup Kˣ) (κ : U →* Kˣ)`
  params, `mem_level` field before `eval`, `eval` with named binders returning
  `κ ⟨hu.unit, mem_level hg z hz hu⟩`.  `col_zero_one'`/`cocycle'` adapted — the unit
  identifications lift to the subgroup by `Subtype.ext (Units.ext …)` (with an
  explicit `show` for the val-coercion); `absSummable_col`/`lin_eval_cocycle`/
  `toWeightSeries` shape unchanged.  `WeightSeries.ext` added in Series.lean
  (placed AFTER the namespace's variable line; cases+subst+rfl works — proof
  irrelevance closes the Prop fields).

### [T023] Jacobs as an honest `ExpansionData` instance (L7.4) — R7 ENDPOINT
- **Status**: done (2026-08-12, laweights beastmode R7) — **R7 ENDPOINT REACHED** | **File**: PhD/JacobsSlash/U3/5_KappaWeight.lean | **Depends**:
  T021, T022 | **Parallel**: no | **Type**: def + theorem (KEY)
- Declarations to add (skeleton-first):
  ```lean
  noncomputable def jacobsChar (t : K₃) (ht : ‖t‖ < 1) :
      oneUnits ‖(3 : K₃)‖ (norm_nonneg _) norm_three_lt_one →* K₃ˣ …
    -- u ↦ unitPow t ↑u; unit-ness via norm_unitPow_sub_one_le;
    -- map_mul' := unitPow_mul norm_three_lt_one ht.le u.2 v.2
  noncomputable def jacobsExpansionData (t : K₃) (ht : ‖t‖ < 1) :
      QMF.ExpansionData Sigma1₃ ‖(3 : K₃)‖ (oneUnits …) (jacobsChar t ht) …
    -- mem_level := levelUnit_mem_oneUnits + norm_sigma1_lower_left_le (≤ ‖3‖² ≤ ‖3‖)
    --   + norm_sigma1_lower_right_sub_one_le
    -- eval := (hasSum_jacobsCol_unitPow t ht … ).tsum_eq  + unit bookkeeping
  theorem jacobsWeightSeries_eq_toWeightSeries (t : K₃) (ht : ‖t‖ < 1) :
      jacobsWeightSeries t ht = (jacobsExpansionData t ht).toWeightSeries
  theorem kappaSlash_eq_toWeightSeries (t : K₃) (ht : ‖t‖ < 1) (g : Sigma1₃) :
      kappaSlash t ht g = (jacobsExpansionData t ht).toWeightSeries.kappaSlash g
  ```
- Sketch: `jacobsChar` unit-ness: `‖unitPow t u − 1‖ ≤ ‖t‖‖3‖ < 1` ⇒ `‖·‖ = 1` ⇒
  `≠ 0` ⇒ `IsUnit` (or `Units.mkOfMulEqOne` with `unitPow t ↑u⁻¹` via `unitPow_mul` +
  `unitPow_one`).  `eval`: the value in `hasSum_jacobsCol_unitPow` is
  `unitPow t (c·z + d)`; identify with `↑(jacobsChar t ht ⟨hu.unit, _⟩)` by
  `IsUnit.unit_spec` (the coercion of `jacobsChar` at the unit IS
  `unitPow t (c·z+d)` definitionally).  Endpoint by `WeightSeries.ext rfl`
  (both `col`s are the same `PowerSeries.mk` term — `jacobsWeightSeries_col` +
  `toWeightSeries_col`); corollary by rewriting `kappaSlash_eq_general`.
- Mathlib: none beyond fork lemmas.
- Source: §R7 L7.4; [Jacobs, p. 29] (§R3 quote); attacks A3/A4/A6.
- **Progress**: DONE, axioms standard, zero warnings, sorry-free.  Exactly as
  drafted: private `isUnit_unitPow` (via `norm_unitPow_sub_one_le` — NB leading `h3`
  section arg, the usual fork pattern); `jacobsChar` (map_mul' := `unitPow_mul … u.2
  v.2` — the memberships are literally the hypotheses) + `jacobsChar_apply` rfl-simp;
  `jacobsExpansionData` (mem_level := `levelUnit_mem_oneUnits` + the two
  `norm_sigma1_*` lemmas; eval := `hasSum_jacobsCol_unitPow`.tsum_eq + congrArg);
  **`jacobsWeightSeries_eq_toWeightSeries := QMF.WeightSeries.ext rfl`** — the
  identification is definitional in the column, as planned.  5_KappaWeight's import
  upgraded SlashAction → Char (Char imports SlashAction transitively).
- **Optional follow-up recorded, NOT ticketed**: with T023 done, the fork's ODE-based
  cocycle machinery (`kappaCol_ode`, `eq_of_ode`, `constantCoeff_compAn_kappaCol`)
  is derivable-in-principle from the Strassman route; retiring it is a fork slim-down
  with recertification-shaped risk — user decision, out of R7 scope.

### [CLEANUP-12] /cleanup on Char.lean + Series.lean + 5_KappaWeight.lean (post-R7)
- **Status**: done (2026-08-12, inline — all three files zero module warnings, zero
  runLinter findings, docstrings on all new public decls, private helpers bare) | **Depends**: T023 | **Type**: cleanup (final per-file re-clean;
  omit-fixpoint to zero warnings, runLinter zero, docstring audit)

### [CLEANUP-FINAL-R7] /cleanup-all (board surface re-verification)
- **Status**: done (2026-08-12 — full nine-module board surface rebuilds with zero
  warnings, zero sorries; all R7 declarations on standard axioms) | **Depends**: T023, CLEANUP-12 | **Type**: cleanup-all (last
  ticket of R7; re-run the CLEANUP-FINAL gate over the full surface)

## R7 dependency front

T021 → T022 → T023 → CLEANUP-12 → CLEANUP-FINAL-R7 (T021 ∥ T022-skeleton possible;
board is otherwise complete, so R7 is the only open front).

## R8 addendum — the headline reading `Forms κ U` (USER-DIRECTED 2026-08-18)

User concern: `Forms θ W U hU` took the *engine* `W : WeightSeries S ρ`, so the level
was baked into the "weight" type and the character κ appeared nowhere — unlike
Buzzard's `S^D_κ(U)` / Jacobs's `L(U, A_κ)`, where κ is a character, `U` a level, and
"U of wild level ≥ p^α, κ α-analytic" is a side condition.  Considered and rejected:
deriving the monoid `S` from κ (α is a genuinely free parameter ≥ the analyticity
threshold — Hecke/`U_p`/classicality need it; no canonical `S` for a κ).  Adopted:
κ primary, level as hypotheses; the `WeightSeries` engine kept below `Forms` but no
longer *exposed* by it (a first cut kept a `FormsOfSeries` layer + congruence lemmas;
user asked to bypass it — with `IsAnalyticOn` a Prop, choice-independence of the space
is proof irrelevance, so nothing was lost).  Done inline (no tickets), sorry-free on
standard axioms, runLinter zero on the Weight modules, chain green through Algebraic +
`5_KappaWeight` (3445 jobs):

- `SlashAction.lean`: `WeightSeries.kappaSlash_congr` (the action of `g` depends only
  on the column at `g`'s lower row).
- `Char.lean`: `ExpansionData.isUnit_lin`, **`ExpansionData.col_eq_of_mem`**
  (uniqueness of the expansion on the level, via `evalAt_injOn`),
  `ExpansionData.kappaSlash_toWeightSeries_eq`; **`QMF.IsAnalyticOn κ S ρ : Prop :=
  Nonempty (ExpansionData S ρ U κ)`** (Def 1.27's standing hypothesis made explicit),
  `ExpansionData.isAnalyticOn`, `IsAnalyticOn.toWeightSeries`/`kappaSlash_eq`;
  **`QMF.AnalyticWeight U S ρ`** (structure: `toChar : U →* Kˣ`, `analytic :
  IsAnalyticOn toChar S ρ` — Buzzard's `t`-analytic weights) with `ofExpansionData`,
  `toWeightSeries`, `kappaSlash_eq` (the action is that of any expansion datum),
  `kappaSlash_ofExpansionData`.
- `Forms.lean` (now imports Char): **headline `Forms θ (κ : AnalyticWeight UK S ρ) U
  hU`** = `levelSubmoduleSlash` at `kappaLevelSlashAction θ κ.toWeightSeries`;
  `mem_forms_iff` (Def 1.30's `φ(gu) = φ(g)‖_κ u_p`, via `mem_levelSubmoduleSlash_iff'`);
  `heckeOperator κ U hU hη h`.  The old `WeightSeries`-input `Forms`/`heckeOperator`
  are gone (no downstream users; Algebraic.lean's bridge is at the `kappaSlash` level).
- `5_KappaWeight.lean`: **`jacobsWeight t ht : AnalyticWeight (oneUnits …) Sigma1₃ ‖3‖`**
  (`ofExpansionData (jacobsExpansionData t ht)`), `jacobsWeight_toChar`,
  `kappaSlash_eq_jacobsWeight` (the fork's operator is the headline action of `κ_t`).
- Docs: `WeightModule.lean` header + `WeightModule` docstring and `Quaternionic.lean`
  now explain ν as a character of `Σ₀(γ)` (`Symⁿ ⊗ ν`) and point to `Weight/` for the
  p-adic weights.

R8.2 (USER-DIRECTED 2026-08-18, same session) — "make WeightSeries internal, all
instances through AnalyticWeight, restrict, and record the α decision":

- `SlashAction.lean`: `kappaSlash_congr` generalised across levels (`W₁ : WeightSeries
  S₁ ρ₁`, `W₂ : WeightSeries S₂ ρ₂`, `g₁.1 = g₂.1`); header marked **engine, not API**.
- `Series.lean`: header marked **engine, not API** (points to `AnalyticWeight`).
- `Char.lean`: `evalAt_pow` made public; `ExpansionData.restrict`/`restrict_col`;
  `IsAnalyticOn.mono`; **`AnalyticWeight` API re-exports**: `kappaSlash` (def),
  `kappaSlash_def`, `kappaSlash_eq`, `kappaSlash_ofExpansionData`, `kappaSlash_one`,
  `kappaSlash_mul`, `matrixCoeff_kappaSlash` (Prop 2.6), `kappaSlashAction`,
  `smulSlashClass`; **`AnalyticWeight.restrict (hS : S' ≤ S)`**, `restrict_toChar`,
  `kappaSlash_restrict`.  `AnalyticWeight` docstring carries the α-in-the-weight
  rationale.
- `Forms.lean`: **design note "the wild level belongs to the weight"** (three reasons:
  analyticity is a joint condition on κ and α — the action evaluates κ on the disc of
  radius ρ about `d`, and over general `K` the expansion data *is* the analyticity;
  `A_κ` is a right-`Σ_α`-module so κ and `U` must share `Σ_α`; α is free above the
  threshold with no canonical `S` per κ, so carry it and `restrict`); `mem_forms_iff`
  now stated via `κ.kappaSlash`; the stray `letI` in `heckeOperator`'s finiteness
  hypothesis dropped.
- `Algebraic.lean`: **`algExpansionData hb n : ExpansionData S ρ ⊤ (powMonoidHom (n+2)
  ∘ subtype)`** (col := `algWeightSeries`'s, eval by `evalAt_pow` + `evalAt_linX`),
  `algWeightSeries_eq_toWeightSeries := WeightSeries.ext rfl`, **`algWeight hb n :
  AnalyticWeight ⊤ S ρ`**, `algWeight_toChar`, `kappaSlash_algWeight`.  So every
  instance (Jacobs, algebraic) is now an `AnalyticWeight`.
- `5_KappaWeight.lean`: `kappaSlash_eq_jacobsWeight` restated with
  `(jacobsWeight t ht).kappaSlash g`.
- NOT done, deliberately: a literal namespace rename of `QMF.WeightSeries` to an
  `Internal` namespace — ~6 files + the fork, `renames.jsonl` churn, no semantic gain;
  the demotion is by API (nothing headline names `WeightSeries`; `AnalyticWeight`
  re-exports what downstream needs) and by the header notes.  Revisit only if a
  downstream file is caught reaching for `WeightSeries` directly.
- Gates: chain green (3445 jobs); runLinter zero on all five Weight modules; all new
  decls on standard axioms; zero sorries in Weight/ + 5_KappaWeight.

Open (user's call): threading T020's "classical ⊆ overconvergent" through the headline
`Forms θ (algWeight hb n) U hU` (it is currently stated at the `kappaLevelSlashAction θ
(algWeightSeries hb n)` level; with `kappaSlash_algWeight` this is a rewrite).
