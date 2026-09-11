# Ticket Board — `lwx-conductor` (Step I / H1 at conductor `p^{h+1}`, and the slope reflection)

**BOARD PATH: `.mathlib-quality/lwx-conductor/`.**  The default `.mathlib-quality/` board belongs to
the completed NewtonPolygons project — NEVER touch it; `.mathlib-quality/qmf/` and its
`beastmode_active` sentinel belong to a parallel run — NEVER touch them either.  Every
`/beastmode` run must name this board path explicitly, and delete only
`.mathlib-quality/lwx-conductor/beastmode_active` (cat before rm).

**Files owned by this board** (all new; every proof ticket proved on 2026-09-11, no `sorry` left):
`PhD/LWX/TouchingH.lean` (Part T), `PhD/LWX/ClassicalPointH.lean` (Part C),
`PhD/LWX/TargetPointH.lean` (Part G), `PhD/LWX/NebCharH.lean` (Part N),
`PhD/LWX/AtkinLehnerLocalH.lean` (Part L), `PhD/LWX/AtkinLehnerMapH.lean` (Part W),
`PhD/LWX/AtkinLehnerIdentityH.lean` (Part I), `PhD/LWX/AtkinLehnerFamily.lean` (Part F),
`PhD/LWX/ConductorSlopes.lean` (Part R).  Do not
edit any other file except where a ticket names it (`CLEANUP-FINAL`: `JL-AUDIT.md`, `FINDINGS.md`,
`PhD.lean`).  The level-`1` files are the templates: every transplant ticket cites the level-`1`
declaration and its line range in `PhD/LWX/{Touching, ClassicalPoint, TargetPoint, NebChar,
AtkinLehnerLocal, AtkinLehnerMap, AtkinLehnerIdentity, StepThree}.lean`.

**Build**: `lake build PhD.LWX.TouchingH PhD.LWX.ClassicalPointH PhD.LWX.TargetPointH
PhD.LWX.NebCharH PhD.LWX.AtkinLehnerLocalH PhD.LWX.AtkinLehnerMapH PhD.LWX.AtkinLehnerIdentityH
PhD.LWX.AtkinLehnerFamily PhD.LWX.ConductorSlopes`.  Statements are transcribed verbatim from the compiling skeleton and are
**protected** — if a statement is wrong, append to this board's `b2_log.jsonl` rather than editing
it.  `_hx`-slack convention applies to a hypothesis that turns out unneeded (candidates recorded in
`decomposition.md`: `ClassicalDataH.norm_eq.hh`, G2's `hh`/`hζ`, the `hh` of W30/W31/W35–W38).
`lake exe runLinter PhD.LWX.<Module>` is a gate for every cleanup.  `omega` not `lia`.  No
`timeout` binary on this machine.  Cleanup tickets are done inline by the main agent.  Traps from
`lwx-h1`: never `set` an abbreviation that lemma instantiations re-introduce unfolded; `congr 1`
on `ψ.mapMatrix (big term)`/`toMatrix` can time out — state generic-matrix identities; `simp
[Matrix.mul_apply]` on a product with a generic matrix folds into `vecMul` — `simp only
[Matrix.mul_apply, Fin.sum_univ_two]` first; inline `(⟨x, h⟩ : ℤ_[p])` loses `Norm` — use
`let z : ℤ_[p] := ⟨x, h⟩`; `omit … in` goes before the docstring; `include hU in` where a section
hypothesis is used only in a proof; `Matrix.mul_eq_one_comm` is the root `mul_eq_one_comm`.

**Read before working any ticket**: `plan.md`, `decomposition.md` (the per-leaf attack records,
in particular T-b, C-d, N-f, L-c, I-d/I-e, R-e), and `.mathlib-quality/lwx-stepone/JL-AUDIT.md`.
Nothing here depends on Jacquet–Langlands; if a ticket seems to need it (e.g. classicality,
Prop 2.15), the route has drifted — file a B2.

**Tickets that ADD a declaration** (marked `[NEW DECL]`): none at planning time; a worker who
spawns a helper must give it a ticket in this format.

## Summary

Planned 2026-09-11 (`/develop`), revised the same day (user: fold `hband`/`hband'` in — the
Atkin–Lehner data becomes a family over every classical weight, Part F, and [LWX, Thm 1.5]'s
second half is now on the board); executed the same day (see the execution record).  167 proof/definition tickets in nine parts
plus cleanups; milestones **I15** (`atkinLehnerHypothesis_of_atkinLehnerDataH`, H1 at level `h`),
**R13** (`slopeRatio_add_slopeRatio_partnerChar_of_atkinLehnerFamilyH`, the slope reflection with
no hypothesis left) and **R17** (`slopeRatio_add_period`, the arithmetic progressions of
[LWX, Thm 1.5]).  Parts T+C+G+N (the point layer), Part L (matrices) and Part F's character
lemmas are independent; W needs N and L; I needs W; R needs I, F and G.

### Skeleton build record (2026-09-11)
First skeleton (eight modules): **Build completed successfully (3828 jobs)**, `sorry` warnings
only.  Revised skeleton after the user's decision to fold `hband`/`hband'` in (nine modules:
`AtkinLehnerFamily.lean` added, `ConductorSlopes.lean` rewired): `lake build PhD.LWX.AtkinLehnerFamily
PhD.LWX.ConductorSlopes` — **Build completed successfully (3829 jobs)**, `sorry` warnings only
(no errors, no other warnings in the new files).  `sorry` inventory: TouchingH 6, ClassicalPointH 19,
TargetPointH 5, NebCharH 25, AtkinLehnerLocalH 36, AtkinLehnerMapH 46 (40 tickets:
`AtkinLehnerData.toH`, `locPolyFormsH`, `discHeckeOperatorClH`, `atkinLehnerMapH`,
`atkinLehnerMapHInv` carry several fields each), AtkinLehnerIdentityH 15, AtkinLehnerFamily 4,
ConductorSlopes 17 — 173 in 167 tickets.  Corrections made during the skeleton builds: three
`omit … in` clauses (structures carrying the `K`-instances cannot omit them; every remaining
`omit` mirrors the level-`1` file), and the fully-applied spelling
`AtkinLehnerFamily.toData θG ψ U F ω k` / `AtkinLehnerFamilyH.toDataH θG ψ U F X ω k` (dot
notation would fill the explicit section variables `θG ψ` positionally).

### Execution record (2026-09-11, `/beastmode`)
All 167 proof/definition tickets proved and all 63 cleanup tickets done inline.  Final gate:
`lake build PhD.LWX.TouchingH … PhD.LWX.ConductorSlopes` — **Build completed successfully (3829
jobs)**, no errors and no warnings in the nine board files; no `sorry` in any board file;
`#print axioms` = `[propext, Classical.choice, Quot.sound]` for the milestones
`atkinLehnerHypothesis_of_atkinLehnerDataH` (I15),
`slopeRatio_add_slopeRatio_partnerChar_of_atkinLehnerFamilyH` (R13) and `slopeRatio_add_period`
(R17), and for fifteen further key declarations (T6, `classicalDataH`, `wQH_conj_mem_Iw`,
`targetData_classicalPointH`, N13, N17, `atkinLehnerEquivH`, `discEvalAtRepsClH`, I12, F4, R8,
R9, R11, R12, R15).  `lake exe runLinter PhD.LWX.ConductorSlopes` lints the whole `PhD` package
closure: no finding in any board file (its 100 findings are all in pre-existing modules outside
this board — TateFredholm, QMF/FLTstuff, ForMathlib, NewtonPolygons, LWX/ClassicalPoint).  Slack
hypotheses renamed under the `_hx` convention: `ClassicalDataH.norm_eq._hh` (T4),
`_hpK` (C4), `inv_pow_lt_norm_pow_of_norm_pow_eq._hh` (R1), `atkinLehnerFunH_slash._hh` (W30),
`atkinLehnerFunHInv_slash._hh` (W35).  `omit … in` clauses added at the linter's request (unused
`[Fintype ι] [DecidableEq ι]`, `[CharZero K]`, `hp`).  One statement repair (B2, below).

### B2 log
Empty at planning time.  2026-09-11 (beastmode): **one statement defect, repaired in place** and
logged in `b2_log.jsonl` (five entries, R13–R17): the skeleton's `include hfin hv hvinj c hc hstab
d hd hfact hdet in` omitted the level-`h` family `X : AtkinLehnerFamilyH θG ψ U F h ζ`, which no
binder mentions, so the elaborated theorems had no level-`h` Hecke characters and were unprovable
for abstract data (the docstrings name the level-`h` family).  Fix: `X` added to the five include
lists; nothing else changed.  Separately, the R8 ticket sketch had the root map of
`A'.charpolyRev` backwards (`y/c` where it is `x/c`); the proof counts over the roots of
`A.charpoly` instead (no statement change).

## Ticket index

| ID | Declaration | File | Type |
|---|---|---|---|
| T1 | `touchX_mul_prime_pow` | TouchingH | proof/def |
| T2 | `two_mul_lwxLambda_touchX_mul_eq_prime_pow` | TouchingH | proof/def |
| T3 | `ClassicalDataH.mul_neg_log_norm_eq` | TouchingH | proof/def |
| CLEANUP-T1 | `CLEANUP-T1` | TouchingH | cleanup |
| T4 | `ClassicalDataH.norm_eq` | TouchingH | proof/def |
| T5 | `ClassicalData.toH` | TouchingH | proof/def |
| T6 | `isStepOneTouching_of_atkinLehnerHypothesisH` | TouchingH | proof/def |
| CLEANUP-T-FINAL | `CLEANUP-T-FINAL` | TouchingH | cleanup |
| C1 | `norm_eq_one_of_pow_eq_one` | ClassicalPointH | proof/def |
| C2 | `norm_sub_one_lt_one_of_norm_pow_sub_one_lt` | ClassicalPointH | proof/def |
| C3 | `norm_sub_one_lt_one_of_pow_prime_pow_eq_one` | ClassicalPointH | proof/def |
| CLEANUP-C1 | `CLEANUP-C1` | ClassicalPointH | cleanup |
| C4 | `norm_one_sub_pow_of_isPrimitiveRoot_prime_pow` | ClassicalPointH | proof/def |
| C5 | `norm_sub_one_pow_of_isPrimitiveRoot_prime_pow` | ClassicalPointH | proof/def |
| C6 | `inv_lt_norm_sub_one_of_isPrimitiveRoot_prime_pow` | ClassicalPointH | proof/def |
| CLEANUP-C2 | `CLEANUP-C2` | ClassicalPointH | cleanup |
| C7 | `norm_weightPoint_prime_pow` | ClassicalPointH | proof/def |
| C8 | `norm_weightPoint_pow_prime_pow` | ClassicalPointH | proof/def |
| C9 | `inv_lt_norm_weightPoint_prime_pow` | ClassicalPointH | proof/def |
| CLEANUP-C3 | `CLEANUP-C3` | ClassicalPointH | cleanup |
| C10 | `norm_weightPoint_lt_one_prime_pow` | ClassicalPointH | proof/def |
| C11 | `TH_weightPoint` | ClassicalPointH | proof/def |
| C12 | `norm_TH_weightPoint_sq_lt` | ClassicalPointH | proof/def |
| CLEANUP-C4 | `CLEANUP-C4` | ClassicalPointH | cleanup |
| C13 | `haloExponentH_weightPoint` | ClassicalPointH | proof/def |
| C14 | `norm_classicalPoint_pow_prime_pow` | ClassicalPointH | proof/def |
| C15 | `inv_lt_norm_classicalPoint_prime_pow` | ClassicalPointH | proof/def |
| CLEANUP-C5 | `CLEANUP-C5` | ClassicalPointH | cleanup |
| C16 | `norm_classicalPoint_lt_one_prime_pow` | ClassicalPointH | proof/def |
| C17 | `norm_TH_classicalPoint_sq_lt` | ClassicalPointH | proof/def |
| C18 | `haloExponentH_classicalPoint` | ClassicalPointH | proof/def |
| CLEANUP-C6 | `CLEANUP-C6` | ClassicalPointH | cleanup |
| C19 | `autFactor_haloWeightH_classicalPoint_prime_pow` | ClassicalPointH | proof/def |
| CLEANUP-C-FINAL | `CLEANUP-C-FINAL` | ClassicalPointH | cleanup |
| G1 | `autFactor_haloWeightH_weightPoint_neg_prime_pow` | TargetPointH | proof/def |
| G2 | `oneAddPow_weightPoint_mul_padicExp_prime_pow` | TargetPointH | proof/def |
| G3 | `specialize_univChar_targetChar_prime_pow` | TargetPointH | proof/def |
| CLEANUP-G1 | `CLEANUP-G1` | TargetPointH | cleanup |
| G4 | `targetConst_eq_classicalDataH_u` | TargetPointH | proof/def |
| G5 | `targetData_classicalPointH` | TargetPointH | proof/def |
| CLEANUP-G-FINAL | `CLEANUP-G-FINAL` | TargetPointH | cleanup |
| N1 | `coe_oneAddPPowMul` | NebCharH | proof/def |
| N2 | `oneAddPPowMul_one` | NebCharH | proof/def |
| N3 | `nebCharH_apply` | NebCharH | proof/def |
| CLEANUP-N1 | `CLEANUP-N1` | NebCharH | cleanup |
| N4 | `classicalDataH_u_eq_nebCharH` | NebCharH | proof/def |
| N5 | `nebCharH_mul` | NebCharH | proof/def |
| N6 | `nebCharH_one` | NebCharH | proof/def |
| CLEANUP-N2 | `CLEANUP-N2` | NebCharH | cleanup |
| N7 | `nebCharH_ne_zero` | NebCharH | proof/def |
| N8 | `nebCharH_of_norm_sub_one_le_pow` | NebCharH | proof/def |
| N9 | `continuous_zeta_pow_toZModPow` | NebCharH | proof/def |
| CLEANUP-N3 | `CLEANUP-N3` | NebCharH | cleanup |
| N10 | `oneAddPow_sub_one_intHom_prime_pow` | NebCharH | proof/def |
| N11 | `nebCharH_oneAddPPowMul` | NebCharH | proof/def |
| N12 | `norm_logQuot_oneAddPPowMul_one` | NebCharH | proof/def |
| CLEANUP-N4 | `CLEANUP-N4` | NebCharH | cleanup |
| N13 | `isPrimitiveRoot_nebCharH_oneAddPPowMul_one` | NebCharH | proof/def |
| N14 | `nebCharH_oneAddPPowMul_natCast` | NebCharH | proof/def |
| N15 | `sum_nebCharH_oneAddPPowMul_mul_eq_zero` | NebCharH | proof/def |
| CLEANUP-N5 | `CLEANUP-N5` | NebCharH | cleanup |
| N16 | `sum_inv_nebCharH_oneAddPPowMul_mul_eq_zero` | NebCharH | proof/def |
| N17 | `sum_inv_nebCharKH_eq_zero` | NebCharH | proof/def |
| N18 | `nebCharKH_psi_mul` | NebCharH | proof/def |
| CLEANUP-N6 | `CLEANUP-N6` | NebCharH | cleanup |
| N19 | `nebCharKH_psi_ne_zero` | NebCharH | proof/def |
| N20 | `nebCharKH_psi_of_norm_sub_one_le_pow` | NebCharH | proof/def |
| N21 | `oneAddPow_inv_sub_one_mul_prime_pow` | NebCharH | proof/def |
| CLEANUP-N7 | `CLEANUP-N7` | NebCharH | cleanup |
| N22 | `nebCharH_eq` | NebCharH | proof/def |
| N23 | `nebCharH_partnerChar` | NebCharH | proof/def |
| N24 | `autFactor_haloWeightH_partner_eq_inv_nebCharKH` | NebCharH | proof/def |
| CLEANUP-N8 | `CLEANUP-N8` | NebCharH | cleanup |
| N25 | `classicalDataH_partnerChar_u` | NebCharH | proof/def |
| CLEANUP-N-FINAL | `CLEANUP-N-FINAL` | NebCharH | cleanup |
| L1 | `wQH_one` | AtkinLehnerLocalH | proof/def |
| L2 | `ℓQH_one` | AtkinLehnerLocalH | proof/def |
| L3 | `tMatH_one` | AtkinLehnerLocalH | proof/def |
| CLEANUP-L1 | `CLEANUP-L1` | AtkinLehnerLocalH | cleanup |
| L4 | `det_wQH` | AtkinLehnerLocalH | proof/def |
| L5 | `det_ℓQH` | AtkinLehnerLocalH | proof/def |
| L6 | `det_tMatH` | AtkinLehnerLocalH | proof/def |
| CLEANUP-L2 | `CLEANUP-L2` | AtkinLehnerLocalH | cleanup |
| L7 | `wQH_mul_wQHinv` | AtkinLehnerLocalH | proof/def |
| L8 | `wQHinv_mul_wQH` | AtkinLehnerLocalH | proof/def |
| L9 | `ℓQH_mul_ℓQHinv` | AtkinLehnerLocalH | proof/def |
| CLEANUP-L3 | `CLEANUP-L3` | AtkinLehnerLocalH | cleanup |
| L10 | `ℓQHinv_mul_ℓQH` | AtkinLehnerLocalH | proof/def |
| L11 | `tMatH_mul_tMatHInv` | AtkinLehnerLocalH | proof/def |
| L12 | `tMatHInv_mul_tMatH` | AtkinLehnerLocalH | proof/def |
| CLEANUP-L4 | `CLEANUP-L4` | AtkinLehnerLocalH | cleanup |
| L13 | `sQ_mul_tMatH` | AtkinLehnerLocalH | proof/def |
| L14 | `tMatHInv_zero_mul_sQ_neg` | AtkinLehnerLocalH | proof/def |
| L15 | `tMatHInv_zero_mul_sQ_mul_tMatH_zero` | AtkinLehnerLocalH | proof/def |
| CLEANUP-L5 | `CLEANUP-L5` | AtkinLehnerLocalH | cleanup |
| L16 | `discConjMat_wQH` | AtkinLehnerLocalH | proof/def |
| L17 | `wQH_mul_vQ_mul_wQHinv` | AtkinLehnerLocalH | proof/def |
| L18 | `upAdjRepH_mul_vQ` | AtkinLehnerLocalH | proof/def |
| CLEANUP-L6 | `CLEANUP-L6` | AtkinLehnerLocalH | cleanup |
| L19 | `wQH_mul_vQ_mul_wQHinv_mul_vQ` | AtkinLehnerLocalH | proof/def |
| L20 | `ℓQHinv_mul_wQH_mul_vQ_mul_wQHinv_mul_vQ` | AtkinLehnerLocalH | proof/def |
| L21 | `wQH_mul_mul_wQHinv` | AtkinLehnerLocalH | proof/def |
| CLEANUP-L7 | `CLEANUP-L7` | AtkinLehnerLocalH | cleanup |
| L22 | `wQHinv_mul_mul_wQH` | AtkinLehnerLocalH | proof/def |
| L23 | `ℓQH_mem_Iw` | AtkinLehnerLocalH | proof/def |
| L24 | `ℓQHinv_mem_Iw` | AtkinLehnerLocalH | proof/def |
| CLEANUP-L8 | `CLEANUP-L8` | AtkinLehnerLocalH | cleanup |
| L25 | `wQH_conj_mem_Iw` | AtkinLehnerLocalH | proof/def |
| L26 | `discImage_zero_of_norm_apply_zero_one_le_pow` | AtkinLehnerLocalH | proof/def |
| L27 | `discConjMat_eq_tMatHInv_mul_mul_tMatH` | AtkinLehnerLocalH | proof/def |
| CLEANUP-L9 | `CLEANUP-L9` | AtkinLehnerLocalH | cleanup |
| L28 | `discConjMat_zero_of_discImage_zero_prime_pow` | AtkinLehnerLocalH | proof/def |
| L29 | `conj_sQ_eq_tMatH_mul_discConjMat` | AtkinLehnerLocalH | proof/def |
| L30 | `discImage_vQ_zero_prime_pow` | AtkinLehnerLocalH | proof/def |
| CLEANUP-L10 | `CLEANUP-L10` | AtkinLehnerLocalH | cleanup |
| L31 | `discImage_ℓQH_zero` | AtkinLehnerLocalH | proof/def |
| L32 | `discImage_ℓQHinv_zero` | AtkinLehnerLocalH | proof/def |
| L33 | `discConj_ℓQH_zero_one_one` | AtkinLehnerLocalH | proof/def |
| CLEANUP-L11 | `CLEANUP-L11` | AtkinLehnerLocalH | cleanup |
| L34 | `discConj_ℓQHinv_zero_one_one` | AtkinLehnerLocalH | proof/def |
| L35 | `discImage_sQ_zero_prime_pow` | AtkinLehnerLocalH | proof/def |
| L36 | `discConj_sQ_zero_prime_pow` | AtkinLehnerLocalH | proof/def |
| CLEANUP-L-FINAL | `CLEANUP-L-FINAL` | AtkinLehnerLocalH | cleanup |
| W1 | `coe_wGLH_inv` | AtkinLehnerMapH | proof/def |
| W2 | `coe_ℓGLH_inv` | AtkinLehnerMapH | proof/def |
| W3 | `wGLH_one` | AtkinLehnerMapH | proof/def |
| CLEANUP-W1 | `CLEANUP-W1` | AtkinLehnerMapH | cleanup |
| W4 | `wGLH_mul_vGL_mul_wGLH_inv_mul_vGL` | AtkinLehnerMapH | proof/def |
| W5 | `atkinLehnerKH_mul_atkinLehnerKHinv` | AtkinLehnerMapH | proof/def |
| W6 | `atkinLehnerKHinv_mul_atkinLehnerKH` | AtkinLehnerMapH | proof/def |
| CLEANUP-W2 | `CLEANUP-W2` | AtkinLehnerMapH | cleanup |
| W7 | `atkinLehnerKH_eq` | AtkinLehnerMapH | proof/def |
| W8 | `atkinLehnerKHinv_eq` | AtkinLehnerMapH | proof/def |
| W9 | `AtkinLehnerData.toH` | AtkinLehnerMapH | proof/def |
| CLEANUP-W3 | `CLEANUP-W3` | AtkinLehnerMapH | cleanup |
| W10 | `discShiftH_mem_U` | AtkinLehnerMapH | proof/def |
| W11 | `theta_discShiftH` | AtkinLehnerMapH | proof/def |
| W12 | `mul_ιp_sGL_eqH` | AtkinLehnerMapH | proof/def |
| CLEANUP-W4 | `CLEANUP-W4` | AtkinLehnerMapH | cleanup |
| W13 | `norm_theta_discShiftH_zero_one_le` | AtkinLehnerMapH | proof/def |
| W14 | `discImage_discShiftH_zero` | AtkinLehnerMapH | proof/def |
| W15 | `discConjMat_discShiftH_zero` | AtkinLehnerMapH | proof/def |
| CLEANUP-W5 | `CLEANUP-W5` | AtkinLehnerMapH | cleanup |
| W16 | `cSpace_ext_blockProjH` | AtkinLehnerMapH | proof/def |
| W17 | `nebK_one_of_cond_pow` | AtkinLehnerMapH | proof/def |
| W18 | `nebK_mul_nebK_eq_nebK_detH` | AtkinLehnerMapH | proof/def |
| CLEANUP-W6 | `CLEANUP-W6` | AtkinLehnerMapH | cleanup |
| W19 | `nebK_one_sub_eq_invH` | AtkinLehnerMapH | proof/def |
| W20 | `locPolyFormsH` | AtkinLehnerMapH | proof/def |
| W21 | `discHeckeOperator_mem_classicalDiscFormsH` | AtkinLehnerMapH | proof/def |
| CLEANUP-W7 | `CLEANUP-W7` | AtkinLehnerMapH | cleanup |
| W22 | `discHeckeOperatorClH` | AtkinLehnerMapH | proof/def |
| W23 | `apply_mul_of_theta_eq_oneH` | AtkinLehnerMapH | proof/def |
| W24 | `blockProj_zero_apply_mul_mem_UH` | AtkinLehnerMapH | proof/def |
| CLEANUP-W8 | `CLEANUP-W8` | AtkinLehnerMapH | cleanup |
| W25 | `shapiro_blockProjH` | AtkinLehnerMapH | proof/def |
| W26 | `atkinLehnerFunH_blockProj` | AtkinLehnerMapH | proof/def |
| W27 | `atkinLehnerFunH_blockProj_zero` | AtkinLehnerMapH | proof/def |
| CLEANUP-W9 | `CLEANUP-W9` | AtkinLehnerMapH | cleanup |
| W28 | `atkinLehnerFunH_left_invt` | AtkinLehnerMapH | proof/def |
| W29 | `atkinLehnerFunH_mem_locPolyDegSubmodule` | AtkinLehnerMapH | proof/def |
| W30 | `atkinLehnerFunH_slash` | AtkinLehnerMapH | proof/def |
| CLEANUP-W10 | `CLEANUP-W10` | AtkinLehnerMapH | cleanup |
| W31 | `atkinLehnerMapH` | AtkinLehnerMapH | proof/def |
| W32 | `atkinLehnerFunHInv_blockProj_zero` | AtkinLehnerMapH | proof/def |
| W33 | `atkinLehnerFunHInv_left_invt` | AtkinLehnerMapH | proof/def |
| CLEANUP-W11 | `CLEANUP-W11` | AtkinLehnerMapH | cleanup |
| W34 | `atkinLehnerFunHInv_mem_locPolyDegSubmodule` | AtkinLehnerMapH | proof/def |
| W35 | `atkinLehnerFunHInv_slash` | AtkinLehnerMapH | proof/def |
| W36 | `atkinLehnerMapHInv` | AtkinLehnerMapH | proof/def |
| CLEANUP-W12 | `CLEANUP-W12` | AtkinLehnerMapH | cleanup |
| W37 | `atkinLehnerMapHInv_atkinLehnerMapH` | AtkinLehnerMapH | proof/def |
| W38 | `atkinLehnerMapH_atkinLehnerMapHInv` | AtkinLehnerMapH | proof/def |
| W39 | `discEvalAtReps_mem_locPolyDegSubmoduleBlockH` | AtkinLehnerMapH | proof/def |
| CLEANUP-W13 | `CLEANUP-W13` | AtkinLehnerMapH | cleanup |
| W40 | `discEvalAtRepsClH` | AtkinLehnerMapH | proof/def |
| CLEANUP-W-FINAL | `CLEANUP-W-FINAL` | AtkinLehnerMapH | cleanup |
| I1 | `vRepDH_mem_levelM1` | AtkinLehnerIdentityH | proof/def |
| I2 | `upEltDH_mem_levelM1` | AtkinLehnerIdentityH | proof/def |
| I3 | `discHeckeOperator_apply_eq_sumH` | AtkinLehnerIdentityH | proof/def |
| CLEANUP-I1 | `CLEANUP-I1` | AtkinLehnerIdentityH | cleanup |
| I4 | `blockProj_zero_discSlash_of_shapeH` | AtkinLehnerIdentityH | proof/def |
| I5 | `apply_mul_ιp_pGLH` | AtkinLehnerIdentityH | proof/def |
| I6 | `apply_mul_ιp_pGL_invH` | AtkinLehnerIdentityH | proof/def |
| CLEANUP-I2 | `CLEANUP-I2` | AtkinLehnerIdentityH | cleanup |
| I7 | `blockProj_zero_apply_mul_ιpH` | AtkinLehnerIdentityH | proof/def |
| I8 | `term_elt_eqH` | AtkinLehnerIdentityH | proof/def |
| I9 | `blockProj_zero_apply_term_eltH` | AtkinLehnerIdentityH | proof/def |
| CLEANUP-I3 | `CLEANUP-I3` | AtkinLehnerIdentityH | cleanup |
| I10 | `atkinLehner_term_eqH` | AtkinLehnerIdentityH | proof/def |
| I11 | `blockProj_zero_discHecke_atkinLehnerH` | AtkinLehnerIdentityH | proof/def |
| I12 | `discHeckeClH_comp_atkinLehnerH` | AtkinLehnerIdentityH | proof/def |
| CLEANUP-I4 | `CLEANUP-I4` | AtkinLehnerIdentityH | cleanup |
| I13 | `discEvalAtRepsClH_discHeckeOperatorClH` | AtkinLehnerIdentityH | proof/def |
| I14 | `atkinLehnerHypothesis_of_conjH` | AtkinLehnerIdentityH | proof/def |
| CLEANUP-ALL-1 | `CLEANUP-ALL-1` | AtkinLehnerIdentityH | cleanup |
| I15 | `atkinLehnerHypothesis_of_atkinLehnerDataH` **[MILESTONE]** | AtkinLehnerIdentityH | proof/def |
| CLEANUP-I-FINAL | `CLEANUP-I-FINAL` | AtkinLehnerIdentityH | cleanup |
| F1 | `invChar_eq_inv` | AtkinLehnerFamily | proof/def |
| F2 | `partnerChar_succ` | AtkinLehnerFamily | proof/def |
| F3 | `partnerChar_invChar_mul_teichChar_pow` | AtkinLehnerFamily | proof/def |
| CLEANUP-F1 | `CLEANUP-F1` | AtkinLehnerFamily | cleanup |
| F4 | `teichChar_pow_sub_one` | AtkinLehnerFamily | proof/def |
| CLEANUP-F-FINAL | `CLEANUP-F-FINAL` | AtkinLehnerFamily | cleanup |
| R1 | `inv_pow_lt_norm_pow_of_norm_pow_eq` | ConductorSlopes | proof/def |
| R2 | `ClassicalDataH.inv_pow_lt_norm_pow` | ConductorSlopes | proof/def |
| R3 | `atkinLehnerHypothesis_symm` | ConductorSlopes | proof/def |
| CLEANUP-R1 | `CLEANUP-R1` | ConductorSlopes | cleanup |
| R4 | `norm_pow_le_of_mem_roots_charpoly_matrixH` | ConductorSlopes | proof/def |
| R5 | `unitSlope_charpolyRev_matrix_leH` | ConductorSlopes | proof/def |
| R6 | `specCharSeries_eq_mul_charpolyRevH` | ConductorSlopes | proof/def |
| CLEANUP-R2 | `CLEANUP-R2` | ConductorSlopes | cleanup |
| R7 | `unitSlope_specCharSeries_eq_unitSlope_charpolyRev_matrixH` | ConductorSlopes | proof/def |
| R8 | `toReal_unitSlope_charpolyRev_reflect` | ConductorSlopes | proof/def |
| R9 | `slopeRatio_add_slopeRatio_eq_of_atkinLehnerHypothesisH` | ConductorSlopes | proof/def |
| CLEANUP-R3 | `CLEANUP-R3` | ConductorSlopes | cleanup |
| R10 | `hasUnitBand_of_atkinLehnerData` | ConductorSlopes | proof/def |
| R11 | `hasUnitBand_of_atkinLehnerFamily` | ConductorSlopes | proof/def |
| R12 | `unitSlope_discHeckeCharPowerSeries_eq_slopeRatio_of_atkinLehnerFamily` | ConductorSlopes | proof/def |
| CLEANUP-R4 | `CLEANUP-R4` | ConductorSlopes | cleanup |
| CLEANUP-ALL-2 | `CLEANUP-ALL-2` | ConductorSlopes | cleanup |
| R13 | `slopeRatio_add_slopeRatio_partnerChar_of_atkinLehnerFamilyH` **[MILESTONE]** | ConductorSlopes | proof/def |
| R14 | `slopeRatio_partnerChar_succ` | ConductorSlopes | proof/def |
| R15 | `slopeRatio_mul_teichChar_sq` | ConductorSlopes | proof/def |
| CLEANUP-R5 | `CLEANUP-R5` | ConductorSlopes | cleanup |
| R16 | `slopeRatio_mul_teichChar_pow` | ConductorSlopes | proof/def |
| CLEANUP-ALL-3 | `CLEANUP-ALL-3` | ConductorSlopes | cleanup |
| R17 | `slopeRatio_add_period` **[MILESTONE]** | ConductorSlopes | proof/def |
| CLEANUP-R-FINAL | `CLEANUP-R-FINAL` | ConductorSlopes | cleanup |
| CLEANUP-FINAL | `CLEANUP-FINAL` | all | cleanup |

## Tickets

### [T1] `touchX_mul_prime_pow`
- **Status**: done
- **File**: PhD/LWX/TouchingH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit hp [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The level-`h` vertex `(k+1)·p^h·t` is the level-`1` vertex `n_{(k+1)p^{h−1}}`
([LWX, §4.2]: "`(k+1)q^{−1}p^M t`" with `q = p`, `M = h + 1`). -/
theorem touchX_mul_prime_pow (h : ℕ) (hh : 0 < h) (t k : ℕ) :
    touchX p t ((k + 1) * p ^ (h - 1)) = t * ((k + 1) * p ^ h) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. Unfold `touchX` (`UpperPolygon.lean:34`: `touchX p t k = k * (p * t)`).
2. `obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩` (from `hh`); then `h - 1 = h'` by `omega`
   (`Nat.add_sub_cancel`), and the goal is `(k + 1) * p ^ h' * (p * t) = t * ((k + 1) * p ^ (h' + 1))`.
3. `rw [pow_succ]; ring`.

- **Mathlib/project lemmas needed**: `touchX` (unfold), `pow_succ`, `Nat.sub_add_cancel`/`omega`, `ring`
- **Sources**: `lwx.txt:2340` ((k+1)q⁻¹p^M t), `lwx.txt:1798` (n_k = kqt); `decomposition.md` T-a.
- **Generality decision**: Pure ℕ arithmetic; `hh` is necessary (false at `h = 0`).
- **Progress**: 2026-09-11: DONE — `obtain ⟨h', rfl⟩`, `touchX`, `pow_succ`, `ring`; build clean, std axioms.

### [T2] `two_mul_lwxLambda_touchX_mul_eq_prime_pow`
- **Status**: done
- **File**: PhD/LWX/TouchingH.lean
- **Depends on**: T1 (only for the vertex spelling; not used in the proof)
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- **[LWX, (3.23.1)] at conductor `p^{h+1}`**: at a point with
`v(T₀) = v(p)/(p^{h−1}(p−1))` ([LWX, §4.2]: "`v(T_{(k,ψ)}) = q/((p−1)p^{M−1})`"),
`2·λ(n)·v(T₀) = n·(k+1)·v(p)` for the vertex `n = t·(k+1)·p^h`. -/
theorem two_mul_lwxLambda_touchX_mul_eq_prime_pow (h : ℕ) (hh : 0 < h) (t k : ℕ) {T₀ c : K}
    (hT : ‖T₀‖ ^ (p ^ (h - 1) * (p - 1)) = ‖c‖) :
    2 * ((lwxLambda p t (touchX p t ((k + 1) * p ^ (h - 1))) : ℝ) * (-Real.log ‖T₀‖))
      = ((t * ((k + 1) * p ^ h) : ℕ) : ℝ) * ((k + 1) * (-Real.log ‖c‖)) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `two_mul_lwxLambda_touchX_mul_eq` (`Touching.lean:614–636`) with the exponent
`e := p ^ (h - 1) * (p - 1)`:
1. `have hp1 : 1 ≤ p := hp.out.one_le`; `obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1` from `hh`.
2. `hcast : (2 : ℝ) * (lwxLambda p t (touchX p t ((k+1) * p^h')) : ℝ) = ((k+1) * p^h' : ℝ)^2 * p * (p - 1) * t`
   from `two_mul_lwxLambda_touchX p t ((k+1) * p^h')` cast to `ℝ` (`push_cast [Nat.cast_sub hp1]`, `linarith`).
3. `hlog : -Real.log ‖c‖ = ((p ^ h' * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖)` from `hT` via
   `← hT, Real.log_pow` (with `h' + 1 - 1 = h'` rewritten by `Nat.add_sub_cancel`), `push_cast [Nat.cast_sub hp1]`, `ring`.
4. `rw [hlog]; push_cast; linear_combination (-Real.log ‖T₀‖) * hcast` — the exponent identity
   `p^h' * p^h' * p = p^(h'+1) * p^h'` is handled by `ring` after `pow_succ`.

- **Mathlib/project lemmas needed**: `two_mul_lwxLambda_touchX` (`UpperPolygon.lean:59`), `Real.log_pow`, `Nat.cast_sub`, `pow_succ`, `linear_combination`
- **Sources**: [LWX, (3.23.1)] `lwx.txt:1826–1838` at `v(T) = 1/(p^{h−1}(p−1))` (`lwx.txt:2323`); `decomposition.md` T-b.
- **Generality decision**: `hh` necessary (false at `h = 0`); no positivity of `‖T₀‖` needed (`Real.log_pow` is unconditional).
- **Progress**: 2026-09-11: DONE — transplanted from `two_mul_lwxLambda_touchX_mul_eq` with the exponent `p^h'(p−1)`; build clean.

### [T3] `ClassicalDataH.mul_neg_log_norm_eq`
- **Status**: done
- **File**: PhD/LWX/TouchingH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `v(T₀)·p^{h−1}(p−1) = v(p)` at a classical datum. -/
theorem mul_neg_log_norm_eq (c : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k) :
    ((p ^ (h - 1) * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖) = -Real.log ‖ψ p‖ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `rw [← c.hnorm, Real.log_pow]` turns `-Real.log ‖ψ p‖` into `-(e * Real.log ‖T₀‖)` with
   `e = ((p ^ (h - 1) * (p - 1) : ℕ) : ℝ)`; `push_cast; ring`.

- **Mathlib/project lemmas needed**: `Real.log_pow`, `ClassicalDataH.hnorm`
- **Sources**: `lwx.txt:476–478`; `decomposition.md` T-c.
- **Generality decision**: Holds for every `h` (no `hh`): it is `Real.log_pow` on `hnorm`.
- **Progress**: 2026-09-11: DONE — `rw [← c.hnorm, Real.log_pow]; ring`; added `omit [Fintype ι] [DecidableEq ι] in` (unused-section-variable warning).

### [CLEANUP-T1] Cleanup `PhD/LWX/TouchingH.lean`
- **Status**: done
- **File**: PhD/LWX/TouchingH.lean
- **Depends on**: T1, T2, T3
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.TouchingH` and `lake exe runLinter PhD.LWX.TouchingH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build PhD.LWX.TouchingH` clean (no warnings), `lake exe runLinter PhD.LWX.TouchingH` reports no finding in TouchingH.lean, no unused simp args, `omit` clauses added where the unused-section-variable linter asked.

### [T4] `ClassicalDataH.norm_eq`
- **Status**: done
- **File**: PhD/LWX/TouchingH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- Two classical data at the same level have points of the same norm (`hnorm` at both, with
the exponent `p^{h−1}(p−1) ≥ 1`). -/
theorem norm_eq (hh : 0 < h) {ω' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀' : K} {k' : ℕ}
    (c : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k') : ‖T₀‖ = ‖T₀'‖ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `have he : 0 < p ^ (h - 1) * (p - 1)` (`Nat.mul_pos (Nat.pos_pow_of_pos _ hp.out.pos) (by have := hp.out.two_le; omega)`).
2. `c.hnorm`, `c'.hnorm` give `‖T₀‖ ^ e = ‖ψ p‖ = ‖T₀'‖ ^ e`; conclude by
   `pow_left_injective`/`(pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) he.ne').1`.

- **Mathlib/project lemmas needed**: `pow_left_inj₀` (or `pow_left_injective`), `norm_nonneg`, `Nat.pos_pow_of_pos`
- **Sources**: `decomposition.md` T-c.
- **Generality decision**: `hh` is slack (`e ≥ p − 1 ≥ 1` for every `h`); keep it and record `_hh` at cleanup (`_hx` convention).
- **Progress**: 2026-09-11: DONE — `pow_left_inj₀` on `c.hnorm.trans c'.hnorm.symm`; `hh` was slack, renamed `_hh` (`_hx` convention); `omit [Fintype ι] [DecidableEq ι] in` added.

### [T5] `ClassicalData.toH`
- **Status**: done
- **File**: PhD/LWX/TouchingH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: definition (the `hnorm` field)

**Statement** (verbatim from the skeleton; protected):
```lean
/-- Level `1` is the case `h = 1`: a `ClassicalData` is a `ClassicalDataH 1`
(`p^{1−1}(p−1) = p − 1`). -/
def _root_.LWX.ClassicalData.toH {hp2 : p ≠ 2} {hψ : ∀ x, ‖ψ x‖ = ‖x‖}
    {ω : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ : K} {k : ℕ}
    (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k) :
    ClassicalDataH θG 1 ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k where
  h0 := c.h0
  h1 := c.h1
  hT := c.hT
  hnorm := by sorry
  u := c.u
  shape := c.shape
```

- **Depends on (declarations)**: —

**Proof sketch**:
Only `hnorm` is `sorry`: the goal is `‖T₀‖ ^ (p ^ (1 - 1) * (p - 1)) = ‖ψ p‖`;
`simpa using c.hnorm` (`Nat.sub_self`, `pow_zero`, `one_mul`), or `rw [Nat.sub_self, pow_zero, one_mul]; exact c.hnorm`.
`toH_matrix` is already `rfl` in the skeleton (compiled).

- **Mathlib/project lemmas needed**: `pow_zero`, `one_mul`, `Nat.sub_self`
- **Sources**: `decomposition.md` T-c.
- **Generality decision**: Bridge only.
- **Progress**: 2026-09-11: DONE — `rw [Nat.sub_self, pow_zero, one_mul]; exact c.hnorm`.

### [T6] `isStepOneTouching_of_atkinLehnerHypothesisH`
- **Status**: done
- **File**: PhD/LWX/TouchingH.lean
- **Depends on**: T1, T2
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **[LWX, §3.23 Step I] at conductor `p^{h+1}`: the touching**, granted H1 at level `h`.  At
a classical point `T₀` of weight `k` and conductor `p^{h+1}` whose Atkin–Lehner partner is the
classical point `T₀'` (of the conjugate nebentypus), the Newton polygon of `∑ c_n(T₀) Xⁿ`
passes through `(n, λ(n)·v(T₀))` at `n = (k+1)p^h t = n_{(k+1)p^{h−1}}` — the squeeze of
`Touching.lean` with [LWX, (3.23.1)] replaced by `two_mul_lwxLambda_touchX_mul_eq_prime_pow`. -/
theorem isStepOneTouching_of_atkinLehnerHypothesisH (hp2 : p ≠ 2) [Nonempty ι] (hh : 0 < h)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    {ω ω' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' : K} {k : ℕ}
    (c : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ h k (c.matrix idx) B
      (c'.matrix idx)) :
    IsStepOneTouching (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (intHom ψ) T₀
      ((k + 1) * p ^ (h - 1)) := by
  sorry
```

- **Depends on (declarations)**: `ClassicalDataH.matrix`, `ClassicalDataH.weight`

**Proof sketch**:
Transplant `isStepOneTouching_of_atkinLehnerHypothesis` (`Touching.lean:695–770`) with `1 → h`:
1. `obtain ⟨B, hAB, P, Q, hQP, hA'⟩ := hAL`; `hT0 : 0 < ‖T₀‖`, `hT0'` from `c.h0`, `c'.h0`; `hψp`, `hcne`,
   `hA0 := det_ne_zero_of_mul_eq_smul' hcne hAB`, `hA'0 := det_ne_zero_of_mul_eq_smul_conj hcne hAB hQP hA'`.
2. `hidx : ((Fintype.card ι : ℤ) * (((k : ℤ) + 1) * (p : ℤ) ^ h)) = ((touchX p (Fintype.card ι) ((k + 1) * p ^ (h - 1)) : ℕ) : ℤ)`
   from T1 (`rw [touchX_mul_prime_pow h hh]; push_cast; ring`).
3. `hup` (Minkowski upper bound at both points): rewrite the seam
   `specCharSeries_ofCerts_eq_discHeckeCharPowerSeries ψ hψ T₁ ω₁ h θG U hU vRep hvΔ idx uu hp2 c₁.h0 c₁.h1 c₁.hT hshape`
   and `← hidx`, then `height_le_negLogNorm_det θG h ψ U hU vRep hvΔ idx uu c₁.weight c₁.shape (haloRhoH_nonneg h T₁) (max_lt (haloRhoH_lt_one h T₁ c₁.hT) inv_lt_one_p) hshape`.
4. `hlow` (Cor 3.18 lower bound): `lwxLambda_mul_le_height_specCharSeries hp2 _ _ (intHom ψ) (norm_intHom ψ hψ) c₁.h0 c₁.h1 _`.
5. `hsq`: chain `hlow.trans hup`, `negLogNorm_of_ne_zero`, `coe_withTop_coe` (re-prove the private
   `coe_withTop_coe : ((x : WithTop ℝ) : WithBotTop ℝ) = (x : WithBotTop ℝ) := rfl` locally), `WithBotTop.coe_le_coe`.
6. `har`: T2 with `t := Fintype.card ι`, `hT := c₁.hnorm` (both points).
7. `hsum`: `neg_log_norm_det_add_of_mul_eq_smul hcne hAB hQP hA'`, `Fintype.card_fin`, `norm_pow`, `Real.log_pow`, `push_cast; ring`.
8. `key`: `linarith` from `hsq c hA0`, `hsq c' hA'0`, `har … c.hnorm`, `har … c'.hnorm`; finish with
   `le_antisymm ((hup c).trans (le_of_eq _)) (hlow c)` and `negLogNorm_of_ne_zero hA0, coe_withTop_coe, key`.

- **Mathlib/project lemmas needed**: `height_le_negLogNorm_det`, `specCharSeries_ofCerts_eq_discHeckeCharPowerSeries`, `lwxLambda_mul_le_height_specCharSeries`, `neg_log_norm_det_add_of_mul_eq_smul`, `det_ne_zero_of_mul_eq_smul'`, `det_ne_zero_of_mul_eq_smul_conj`, `haloRhoH_nonneg`, `haloRhoH_lt_one`, `inv_lt_one_p`, `negLogNorm_of_ne_zero`, `WithBotTop.coe_le_coe`, `Fintype.card_fin`
- **Sources**: [LWX, §3.23 Step I] `lwx.txt:1807–1846` at conductor `p^{h+1}`; `decomposition.md` T-d; `Touching.lean:695–770`.
- **Generality decision**: `hh` needed through T1/T2; `[Nonempty ι]` for `classicalMatrix`.
- **Progress**: 2026-09-11: DONE — transplanted from `isStepOneTouching_of_atkinLehnerHypothesis` (Touching.lean:695–770); added the private helper `coe_withTop_coeH` (level-`h` copy of the private `coe_withTop_coe`); build clean, `#print axioms` = [propext, Classical.choice, Quot.sound] for T6 and `hasUnitBand_of_atkinLehnerHypothesisH`.

### [CLEANUP-T-FINAL] Cleanup `PhD/LWX/TouchingH.lean` (final)
- **Status**: done
- **File**: PhD/LWX/TouchingH.lean
- **Depends on**: T6 (and every earlier ticket of the file)
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.TouchingH` and `lake exe runLinter PhD.LWX.TouchingH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build PhD.LWX.TouchingH` clean (no warnings), `lake exe runLinter PhD.LWX.TouchingH` reports no finding in TouchingH.lean, no unused simp args, `omit` clauses added where the unused-section-variable linter asked.

### [C1] `norm_eq_one_of_pow_eq_one`
- **Status**: done
- **File**: PhD/LWX/ClassicalPointH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- A root of unity has norm one. -/
theorem norm_eq_one_of_pow_eq_one {ζ : K} {n : ℕ} (hn : n ≠ 0) (hζ : ζ ^ n = 1) : ‖ζ‖ = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `have h1 : ‖ζ‖ ^ n = 1 := by rw [← norm_pow, hζ, norm_one]`.
2. `exact (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) hn).1 h1` (or the trichotomy argument of
   `norm_of_isPrimitiveRoot`, `ClassicalPoint.lean:108–118`, with `pow_lt_one₀`/`one_lt_pow₀`).

- **Mathlib/project lemmas needed**: `norm_pow`, `pow_eq_one_iff_of_nonneg`
- **Sources**: `decomposition.md` C-a.
- **Generality decision**: Any normed field; replaces `norm_of_isPrimitiveRoot`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ClassicalPointH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [C2] `norm_sub_one_lt_one_of_norm_pow_sub_one_lt`
- **Status**: done
- **File**: PhD/LWX/ClassicalPointH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CompleteSpace K] [CharZero K] in
/-- **The inductive step of `‖ζ − 1‖ < 1`**: `(ζ − 1)^p ≡ ζ^p − 1 (mod p)` on the unit ball
(`add_pow` with `p ∣ C(p, i)` for `0 < i < p`), so `‖ζ^p − 1‖ < 1` forces `‖ζ − 1‖ < 1`. -/
theorem norm_sub_one_lt_one_of_norm_pow_sub_one_lt {ζ : K} (hζ : ‖ζ‖ ≤ 1)
    (hpK : ‖((p : ℕ) : K)‖ < 1) (h : ‖ζ ^ p - 1‖ < 1) : ‖ζ - 1‖ < 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. Expand `(ζ - 1) ^ p = (ζ + (-1)) ^ p` by `add_pow`: `∑ i ∈ range (p+1), ζ^i * (-1)^(p-i) * C(p,i)`.
2. Split off `i = p` (`ζ^p`) and `i = 0` (`(-1)^p`) with `Finset.sum_range_succ`/`Finset.sum_range_succ'`;
   the rest is `S := ∑ i ∈ Ico 1 p, ζ^i (-1)^(p-i) C(p,i)`.
3. `hS : ‖S‖ ≤ ‖((p:ℕ):K)‖`: each term has `‖(C(p,i) : K)‖ ≤ ‖p‖` because `p ∣ C(p,i)` for `0 < i < p`
   (`Nat.Prime.dvd_choose_self hp.out (by omega) hi`; write `C(p,i) = p * m`, `Nat.cast_mul`, `norm_mul`,
   `IsUltrametricDist.norm_natCast_le_one`), times `‖ζ‖^i ≤ 1`, `‖-1‖ = 1`; `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`.
4. `hend : ‖((-1:K)^p + 1)‖ ≤ ‖((p:ℕ):K)‖`: `rcases hp.out.eq_two_or_odd' with rfl | hodd`; odd: `Odd.neg_one_pow`, `neg_add_cancel`, `norm_zero`;
   `p = 2`: `= 2 = ((2:ℕ):K)`, `le_refl`.
5. `(ζ - 1)^p = (ζ^p - 1) + ((-1)^p + 1) + S` (`ring_nf`/`linear_combination`), so
   `‖(ζ-1)^p‖ ≤ max ‖ζ^p - 1‖ (max ‖(-1)^p+1‖ ‖S‖) < 1` (`IsUltrametricDist.norm_add_le_max`, `hpK`).
6. `‖ζ - 1‖ ^ p < 1` with `p ≠ 0` gives `‖ζ - 1‖ < 1` (`pow_lt_one_iff_of_nonneg`).

- **Mathlib/project lemmas needed**: `add_pow`, `Finset.sum_range_succ`, `Nat.Prime.dvd_choose_self`, `Nat.Prime.eq_two_or_odd'`, `Odd.neg_one_pow`, `IsUltrametricDist.norm_add_le_max`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `IsUltrametricDist.norm_natCast_le_one`, `pow_lt_one_iff_of_nonneg`
- **Sources**: `decomposition.md` C-b; the level-`1` `norm_sub_one_lt_one_of_isPrimitiveRoot` (`ClassicalPoint.lean:51–104`) for the technique.
- **Generality decision**: Stated for every prime `p` (the `p = 2` case handled by `eq_two_or_odd'`); only `‖ζ‖ ≤ 1` needed.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ClassicalPointH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [C3] `norm_sub_one_lt_one_of_pow_prime_pow_eq_one`
- **Status**: done
- **File**: PhD/LWX/ClassicalPointH.lean
- **Depends on**: C1, C2
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CompleteSpace K] [CharZero K] in
/-- A `p^h`-th root of unity is a `1`-unit (induction on `h` through
`norm_sub_one_lt_one_of_norm_pow_sub_one_lt`). -/
theorem norm_sub_one_lt_one_of_pow_prime_pow_eq_one {ζ : K} (hpK : ‖((p : ℕ) : K)‖ < 1) {h : ℕ}
    (hζ : ζ ^ p ^ h = 1) : ‖ζ - 1‖ < 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Induction on `h` generalising `ζ`:
- `h = 0`: `ζ ^ 1 = 1` gives `ζ = 1` (`pow_one`), `‖1 - 1‖ = 0 < 1`.
- `h + 1`: `(ζ ^ p) ^ p ^ h = 1` (`← pow_mul`, `pow_succ'`/`mul_comm`), so `‖ζ ^ p - 1‖ < 1` by IH;
  `‖ζ‖ ≤ 1` by C1 (`n := p ^ (h+1)`, `pow_ne_zero`); conclude by C2.

- **Mathlib/project lemmas needed**: `pow_mul`, `pow_succ`, `pow_ne_zero`
- **Sources**: `decomposition.md` C-b.
- **Generality decision**: Every `h` (including `0`), every prime.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ClassicalPointH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-C1] Cleanup `PhD/LWX/ClassicalPointH.lean`
- **Status**: done
- **File**: PhD/LWX/ClassicalPointH.lean
- **Depends on**: C1, C2, C3
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.ClassicalPointH` and `lake exe runLinter PhD.LWX.ClassicalPointH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of ClassicalPointH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [C4] `norm_one_sub_pow_of_isPrimitiveRoot_prime_pow`
- **Status**: done
- **File**: PhD/LWX/ClassicalPointH.lean
- **Depends on**: C1
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CompleteSpace K] [CharZero K] in
/-- `‖1 − ζ^i‖ = ‖1 − ζ‖` for `p ∤ i` and `ζ` a primitive `p^h`-th root of unity: `≤` by the
geometric sum `1 − ζ^i = (1 − ζ)(1 + ζ + ⋯ + ζ^{i−1})`, and `≥` by the same with `ζ = (ζ^i)^j`
for `ij ≡ 1 (mod p^h)` (`Nat.exists_mul_mod_eq_one_of_coprime`). -/
theorem norm_one_sub_pow_of_isPrimitiveRoot_prime_pow {ζ : K} {h : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ < 1) {i : ℕ} (hi : ¬ p ∣ i) :
    ‖1 - ζ ^ i‖ = ‖1 - ζ‖ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `hζn : ‖ζ‖ = 1` (C1 with `hζ.pow_eq_one`, `pow_ne_zero`); `hgeom : ∀ m, ‖∑ j ∈ range m, ζ ^ j‖ ≤ 1`
   (ultrametric sum bound); `hpow : ∀ j, ‖ζ ^ j - 1‖ ≤ ‖ζ - 1‖` via `geom_sum_mul` (as `ClassicalPoint.lean:151–165`).
2. `≤`: `‖1 - ζ ^ i‖ = ‖ζ ^ i - 1‖ ≤ ‖ζ - 1‖ = ‖1 - ζ‖` (`norm_sub_rev`, `hpow i`).
3. `≥`: `rcases Nat.eq_zero_or_pos h with rfl | hh`; if `h = 0` then `ζ = 1` (`hζ.pow_eq_one` with `pow_zero`, `pow_one`) and both sides are `0`.
   Otherwise `1 < p ^ h` (`Nat.one_lt_pow hh.ne' hp.out.one_lt`); `hcop : Nat.Coprime i (p ^ h)` from
   `Nat.Coprime.pow_right h ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hi).symm`;
   `obtain ⟨j, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop.symm? ` — check the exact argument order of
   `Nat.exists_mul_mod_eq_one_of_coprime {k n} (hkn : Coprime n k) (hk : 1 < k) : ∃ m, n * m % k = 1`;
   then `ζ = (ζ ^ i) ^ j`: `← pow_mul`, and `ζ ^ (i*j) = ζ ^ ((i*j) % p^h) = ζ ^ 1` by `hζ.pow_eq_one_iff_dvd`/`Nat.mod_add_div` (`pow_add`, `pow_mul`, `hζ.pow_eq_one`, `one_pow`).
   Hence `‖1 - ζ‖ = ‖(ζ^i)^j - 1‖ ≤ ‖ζ^i - 1‖` by `hpow`-style bound for the root `ζ ^ i` (same geometric-sum argument with `‖ζ^i‖ = 1`).
4. `le_antisymm`.

- **Mathlib/project lemmas needed**: `geom_sum_mul`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `Nat.Coprime.pow_right`, `Nat.Prime.coprime_iff_not_dvd`, `Nat.exists_mul_mod_eq_one_of_coprime` (`Mathlib/Data/Int/GCD.lean:140`), `IsPrimitiveRoot.pow_eq_one_iff_dvd`, `Nat.mod_add_div`, `pow_mul`, `norm_sub_rev`
- **Sources**: `decomposition.md` C-c; `ClassicalPoint.lean:151–189` for the geometric-sum bound.
- **Generality decision**: No `hh` (true at `h = 0` with both sides `0`); no `hp2`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ClassicalPointH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [C5] `norm_sub_one_pow_of_isPrimitiveRoot_prime_pow`
- **Status**: done
- **File**: PhD/LWX/ClassicalPointH.lean
- **Depends on**: C4
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CompleteSpace K] [CharZero K] in
/-- **`v(ζ − 1) = v(p)/ϕ(p^h)`** for a primitive `p^h`-th root of unity, `h ≥ 1`:
`∏_{μ primitive} (1 − μ) = Φ_{p^h}(1) = p` (`Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots`,
`Polynomial.eval_one_cyclotomic_prime_pow`), with `ϕ(p^h) = p^{h−1}(p−1)` factors
(`IsPrimitiveRoot.card_primitiveRoots`, `Nat.totient_prime_pow`), all of norm `‖1 − ζ‖`. -/
theorem norm_sub_one_pow_of_isPrimitiveRoot_prime_pow {ζ : K} {h : ℕ} (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ < 1) :
    ‖ζ - 1‖ ^ (p ^ (h - 1) * (p - 1)) = ‖((p : ℕ) : K)‖ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1` from `hh`; rewrite `h' + 1 - 1 = h'`.
2. `hev : Polynomial.eval 1 (Polynomial.cyclotomic (p ^ (h'+1)) K) = p := Polynomial.eval_one_cyclotomic_prime_pow h'`.
3. `rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at hev`; `simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hev`.
4. Take norms: `‖((p:ℕ):K)‖ = ∏ μ ∈ primitiveRoots (p^(h'+1)) K, ‖1 - μ‖` (`← hev`, `norm_prod`).
5. Every factor equals `‖1 - ζ‖`: for `μ ∈ primitiveRoots _ K` (`mem_primitiveRoots (pow_pos hp.out.pos _)`),
   `haveI : NeZero (p ^ (h'+1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩`, `obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one`,
   `hi : i.Coprime (p^(h'+1)) := (hζ.pow_iff_coprime (pow_pos _ _) i).1 hμ`, so `¬ p ∣ i`
   (`Nat.Prime.coprime_iff_not_dvd`, `Nat.Coprime.coprime_dvd_right (dvd_pow_self p (Nat.succ_ne_zero _))`), and C4.
6. `Finset.prod_congr rfl …`, `Finset.prod_const`, `hζ.card_primitiveRoots`, `Nat.totient_prime_pow hp.out (Nat.succ_pos h')`
   (`= p ^ h' * (p - 1)`), then `norm_sub_rev`.

- **Mathlib/project lemmas needed**: `Polynomial.eval_one_cyclotomic_prime_pow`, `Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots`, `Polynomial.eval_prod`, `Polynomial.eval_sub`, `norm_prod`, `mem_primitiveRoots`, `IsPrimitiveRoot.eq_pow_of_pow_eq_one`, `IsPrimitiveRoot.pow_iff_coprime`, `IsPrimitiveRoot.card_primitiveRoots`, `Nat.totient_prime_pow`, `Nat.Coprime.coprime_dvd_right`, `Finset.prod_const`
- **Sources**: [LWX, §2.1] `lwx.txt:476–478` (`v(T) = 1/p^{m−2}(p−1)`); `decomposition.md` C-d.
- **Generality decision**: `hh` necessary (false at `h = 0`).
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ClassicalPointH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [C6] `inv_lt_norm_sub_one_of_isPrimitiveRoot_prime_pow`
- **Status**: done
- **File**: PhD/LWX/ClassicalPointH.lean
- **Depends on**: C5
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CompleteSpace K] [CharZero K] in
/-- `p⁻¹ < ‖ζ − 1‖`: the exponent `p^{h−1}(p−1) ≥ 2` for odd `p`. -/
theorem inv_lt_norm_sub_one_of_isPrimitiveRoot_prime_pow (hp2 : p ≠ 2) {ζ : K} {h : ℕ}
    (hh : 0 < h) (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) :
    (p : ℝ)⁻¹ < ‖ζ - 1‖ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `inv_lt_norm_sub_one_of_isPrimitiveRoot` (`ClassicalPoint.lean:242–260`) with the exponent
`e = p ^ (h - 1) * (p - 1)`: `hp3 : 3 ≤ p`; `he2 : 2 ≤ e` (`Nat.one_le_pow`, `p - 1 ≥ 2`, `Nat.le_mul_of_pos_left`);
`hpow := norm_sub_one_pow_of_isPrimitiveRoot_prime_pow hh hζ (by rw [hpK]; exact inv_lt_one_p)`, `rw [hpK] at hpow`;
`by_contra`; `‖ζ - 1‖ ^ e ≤ (p⁻¹) ^ e ≤ (p⁻¹) ^ 2` (`pow_le_pow_left₀`, `pow_le_pow_of_le_one` with `he2`) `< p⁻¹` (`nlinarith`/`sq` with `p⁻¹ < 1`), contradiction with `hpow`.

- **Mathlib/project lemmas needed**: `pow_le_pow_left₀`, `pow_le_pow_of_le_one`, `inv_lt_one_p`, `Nat.one_le_pow`, `nlinarith`
- **Sources**: `decomposition.md` C-e; `ClassicalPoint.lean:242–260`.
- **Generality decision**: `hp2` necessary (`p = 2`, `h = 1` has `‖ζ − 1‖ = p⁻¹`).
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ClassicalPointH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-C2] Cleanup `PhD/LWX/ClassicalPointH.lean`
- **Status**: done
- **File**: PhD/LWX/ClassicalPointH.lean
- **Depends on**: C4, C5, C6
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.ClassicalPointH` and `lake exe runLinter PhD.LWX.ClassicalPointH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of ClassicalPointH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [C7] `norm_weightPoint_prime_pow`
- **Status**: done
- **File**: PhD/LWX/ClassicalPointH.lean
- **Depends on**: C6
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `‖T_{(s,ψ)}‖ = ‖ζ − 1‖`: the factor `exp(ps)` is a `1`-unit closer to `1` than `ζ`
(`norm_weightPoint` with `inv_lt_norm_sub_one_of_isPrimitiveRoot_prime_pow`). -/
theorem norm_weightPoint_prime_pow (hp2 : p ≠ 2) {ζ : K} {h : ℕ} (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    ‖weightPoint p s ζ‖ = ‖ζ - 1‖ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `norm_weightPoint` (`TargetPoint.lean:133–152`): re-prove locally the private helpers
`inv_p_pos`, `norm_sq_lt_of_le_inv`, `norm_p_mul_le_inv`, `norm_p_mul_sq_lt`, `norm_padicExp_p_mul_sub_one_le`
(`TargetPoint.lean:88–131`, five short lemmas — copy them as `private` into this file, they are level-free), then:
`hE1 : ‖E - 1‖ ≤ p⁻¹` for `E = padicExp (p * s)`, `hEn : ‖E‖ = 1` (`norm_eq_one_of_norm_sub_le`),
`hgt : p⁻¹ < ‖ζ - 1‖` (C6), `weightPoint = (ζ - 1) * E + (E - 1)` (`ring`), and
`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` + `max_eq_left`.

- **Mathlib/project lemmas needed**: `PadicExpLog.norm_padicExp_sub_one_le`, `norm_eq_one_of_norm_sub_le`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, `IsUltrametricDist.norm_intCast_le_one`
- **Sources**: `lwx.txt:1794–1798`, `2323`; `decomposition.md` C-f; `TargetPoint.lean:88–152`.
- **Generality decision**: Every `s : ℤ`; `hh`, `hp2` through C6.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ClassicalPointH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [C8] `norm_weightPoint_pow_prime_pow`
- **Status**: done
- **File**: PhD/LWX/ClassicalPointH.lean
- **Depends on**: C5, C7
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The classical norm condition at conductor `p^{h+1}`: `‖T_{(s,ψ)}‖^{p^{h−1}(p−1)} = ‖p‖`. -/
theorem norm_weightPoint_pow_prime_pow (hp2 : p ≠ 2) {ζ : K} {h : ℕ} (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    ‖weightPoint p s ζ‖ ^ (p ^ (h - 1) * (p - 1)) = ‖((p : ℕ) : K)‖ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [norm_weightPoint_prime_pow hp2 hh hζ hpK s]; exact norm_sub_one_pow_of_isPrimitiveRoot_prime_pow hh hζ (by rw [hpK]; exact inv_lt_one_p)`.

- **Mathlib/project lemmas needed**: —
- **Sources**: `decomposition.md` C-f.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ClassicalPointH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [C9] `inv_lt_norm_weightPoint_prime_pow`
- **Status**: done
- **File**: PhD/LWX/ClassicalPointH.lean
- **Depends on**: C6, C7
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The weight point lies in the halo annulus: `p⁻¹ < ‖T_{(s,ψ)}‖`. -/
theorem inv_lt_norm_weightPoint_prime_pow (hp2 : p ≠ 2) {ζ : K} {h : ℕ} (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    (p : ℝ)⁻¹ < ‖weightPoint p s ζ‖ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [norm_weightPoint_prime_pow hp2 hh hζ hpK s]; exact inv_lt_norm_sub_one_of_isPrimitiveRoot_prime_pow hp2 hh hζ hpK`.

- **Mathlib/project lemmas needed**: —
- **Sources**: `decomposition.md` C-f.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ClassicalPointH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-C3] Cleanup `PhD/LWX/ClassicalPointH.lean`
- **Status**: done
- **File**: PhD/LWX/ClassicalPointH.lean
- **Depends on**: C7, C8, C9
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.ClassicalPointH` and `lake exe runLinter PhD.LWX.ClassicalPointH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of ClassicalPointH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [C10] `norm_weightPoint_lt_one_prime_pow`
- **Status**: done
- **File**: PhD/LWX/ClassicalPointH.lean
- **Depends on**: C3, C7
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The weight point lies in the halo annulus: `‖T_{(s,ψ)}‖ < 1`. -/
theorem norm_weightPoint_lt_one_prime_pow (hp2 : p ≠ 2) {ζ : K} {h : ℕ} (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    ‖weightPoint p s ζ‖ < 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [norm_weightPoint_prime_pow hp2 hh hζ hpK s]; exact norm_sub_one_lt_one_of_pow_prime_pow_eq_one (by rw [hpK]; exact inv_lt_one_p) hζ.pow_eq_one`.

- **Mathlib/project lemmas needed**: —
- **Sources**: `decomposition.md` C-f.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ClassicalPointH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [C11] `TH_weightPoint`
- **Status**: done
- **File**: PhD/LWX/ClassicalPointH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- At level `h` the wild part disappears: `(1 + T_{(s,ψ)})^{p^h} − 1 = exp(p^{h+1}s) − 1`,
since `ζ^{p^h} = 1` (`PadicExpLog.padicExp_natCast_mul`). -/
theorem TH_weightPoint (hp2 : p ≠ 2) {ζ : K} {h : ℕ} (hζ : ζ ^ p ^ h = 1)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    TH p h (weightPoint p s ζ)
      = PadicExpLog.padicExp (((p : ℕ) : K) ^ (h + 1) * (s : K)) - 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `TH_one_weightPoint` (`TargetPoint.lean:175–186`): `rw [TH, weightPoint, show ∀ x : K, (1 : K) + (x - 1) = x from fun x => by ring, mul_pow, hζ, one_mul]`
(the exponent is `p ^ h`, not `p`), then `← PadicExpLog.padicExp_natCast_mul h3 hp2 (norm_p_mul_sq_lt hpK hs) (p ^ h)` with
`hs : ‖(s : K)‖ ≤ 1` (`IsUltrametricDist.norm_intCast_le_one`); `congr 2; push_cast; ring` (`p ^ h * (p * s) = p ^ (h+1) * s`, `pow_succ`).

- **Mathlib/project lemmas needed**: `PadicExpLog.padicExp_natCast_mul`, `mul_pow`, `pow_succ`, `IsUltrametricDist.norm_intCast_le_one`
- **Sources**: `lwx.txt:466–470`; `decomposition.md` C-g; `TargetPoint.lean:175–186`.
- **Generality decision**: Only `ζ ^ p ^ h = 1` is used; every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ClassicalPointH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [C12] `norm_TH_weightPoint_sq_lt`
- **Status**: done
- **File**: PhD/LWX/ClassicalPointH.lean
- **Depends on**: C11
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The level-`h` analyticity condition at the weight point: `‖T'_h‖ ≤ p^{−(h+1)}`. -/
theorem norm_TH_weightPoint_sq_lt (hp2 : p ≠ 2) {ζ : K} {h : ℕ} (hζ : ζ ^ p ^ h = 1)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    ‖TH p h (weightPoint p s ζ)‖ ^ 2 < (p : ℝ)⁻¹ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `norm_TH_one_weightPoint_sq_lt` (`TargetPoint.lean:187–203`): `hx : ‖(p:K)^h * s‖ ≤ 1`
(`norm_mul`, `norm_pow`, `hpK`, `pow_le_one₀`, `norm_intCast_le_one`); `rw [TH_weightPoint hp2 hζ hpK s, show (p:K)^(h+1) * s = p * (p^h * s) by ring]`;
`hle : ‖TH …‖ ≤ p⁻¹` by `norm_padicExp_p_mul_sub_one_le hp2 hpK hx`; then `‖·‖^2 ≤ (p⁻¹)^2 < p⁻¹` (`nlinarith`).

- **Mathlib/project lemmas needed**: `PadicExpLog.norm_padicExp_sub_one_le`, `pow_le_one₀`, `nlinarith`
- **Sources**: `decomposition.md` C-g; `TargetPoint.lean:187–203`.
- **Generality decision**: Only `ζ ^ p ^ h = 1`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ClassicalPointH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-C4] Cleanup `PhD/LWX/ClassicalPointH.lean`
- **Status**: done
- **File**: PhD/LWX/ClassicalPointH.lean
- **Depends on**: C10, C11, C12
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.ClassicalPointH` and `lake exe runLinter PhD.LWX.ClassicalPointH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of ClassicalPointH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [C13] `haloExponentH_weightPoint`
- **Status**: done
- **File**: PhD/LWX/ClassicalPointH.lean
- **Depends on**: C11
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The level-`h` halo exponent at the weight point is `s`**:
`s_h = log(exp(p^{h+1}s))/p^{h+1} = s`. -/
theorem haloExponentH_weightPoint (hp2 : p ≠ 2) {ζ : K} {h : ℕ} (hζ : ζ ^ p ^ h = 1)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    haloExponentH p h (weightPoint p s ζ) = (s : K) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `haloExponentH_one_weightPoint` (`TargetPoint.lean:204–224`): `hdisc : ‖(p:K)^(h+1) * s‖^2 < ‖(p:K)‖`
(`norm_p_mul_sq_lt` after `show (p:K)^(h+1) * s = p * (p^h * s)`); `rw [haloExponentH, TH_weightPoint hp2 hζ hpK s, show ∀ x : K, 1 + (x - 1) = x …, PadicExpLog.padicLog_padicExp h3 hp2 hdisc]`;
`field_simp` (`(p:K)^(h+1) ≠ 0` from `Nat.cast_ne_zero`/`pow_ne_zero`); `ring`.

- **Mathlib/project lemmas needed**: `PadicExpLog.padicLog_padicExp`, `field_simp`, `pow_ne_zero`
- **Sources**: `decomposition.md` C-g; `TargetPoint.lean:204–224`.
- **Generality decision**: Only `ζ ^ p ^ h = 1`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ClassicalPointH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [C14] `norm_classicalPoint_pow_prime_pow`
- **Status**: done
- **File**: PhD/LWX/ClassicalPointH.lean
- **Depends on**: C8
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The classical norm condition at the classical point of conductor `p^{h+1}`. -/
theorem norm_classicalPoint_pow_prime_pow (hp2 : p ≠ 2) {ζ : K} {h : ℕ} (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    ‖classicalPoint p k ζ‖ ^ (p ^ (h - 1) * (p - 1)) = ‖((p : ℕ) : K)‖ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [← weightPoint_natCast]; exact norm_weightPoint_pow_prime_pow hp2 hh hζ hpK k`.

- **Mathlib/project lemmas needed**: `weightPoint_natCast` (`TargetPoint.lean:84`)
- **Sources**: `decomposition.md` C-h.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ClassicalPointH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [C15] `inv_lt_norm_classicalPoint_prime_pow`
- **Status**: done
- **File**: PhD/LWX/ClassicalPointH.lean
- **Depends on**: C9
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `p⁻¹ < ‖T_{χ_k}‖` at conductor `p^{h+1}`. -/
theorem inv_lt_norm_classicalPoint_prime_pow (hp2 : p ≠ 2) {ζ : K} {h : ℕ} (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    (p : ℝ)⁻¹ < ‖classicalPoint p k ζ‖ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [← weightPoint_natCast]; exact inv_lt_norm_weightPoint_prime_pow hp2 hh hζ hpK k`.

- **Mathlib/project lemmas needed**: `weightPoint_natCast`
- **Sources**: `decomposition.md` C-h.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ClassicalPointH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-C5] Cleanup `PhD/LWX/ClassicalPointH.lean`
- **Status**: done
- **File**: PhD/LWX/ClassicalPointH.lean
- **Depends on**: C13, C14, C15
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.ClassicalPointH` and `lake exe runLinter PhD.LWX.ClassicalPointH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of ClassicalPointH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [C16] `norm_classicalPoint_lt_one_prime_pow`
- **Status**: done
- **File**: PhD/LWX/ClassicalPointH.lean
- **Depends on**: C10
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `‖T_{χ_k}‖ < 1` at conductor `p^{h+1}`. -/
theorem norm_classicalPoint_lt_one_prime_pow (hp2 : p ≠ 2) {ζ : K} {h : ℕ} (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    ‖classicalPoint p k ζ‖ < 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [← weightPoint_natCast]; exact norm_weightPoint_lt_one_prime_pow hp2 hh hζ hpK k`.

- **Mathlib/project lemmas needed**: `weightPoint_natCast`
- **Sources**: `decomposition.md` C-h.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ClassicalPointH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [C17] `norm_TH_classicalPoint_sq_lt`
- **Status**: done
- **File**: PhD/LWX/ClassicalPointH.lean
- **Depends on**: C12
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The level-`h` analyticity condition at the classical point. -/
theorem norm_TH_classicalPoint_sq_lt (hp2 : p ≠ 2) {ζ : K} {h : ℕ} (hζ : ζ ^ p ^ h = 1)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    ‖TH p h (classicalPoint p k ζ)‖ ^ 2 < (p : ℝ)⁻¹ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [← weightPoint_natCast]; exact norm_TH_weightPoint_sq_lt hp2 hζ hpK k`.

- **Mathlib/project lemmas needed**: `weightPoint_natCast`
- **Sources**: `decomposition.md` C-h.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ClassicalPointH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [C18] `haloExponentH_classicalPoint`
- **Status**: done
- **File**: PhD/LWX/ClassicalPointH.lean
- **Depends on**: C13
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The level-`h` halo exponent at a classical point is `k`**. -/
theorem haloExponentH_classicalPoint (hp2 : p ≠ 2) {ζ : K} {h : ℕ} (hζ : ζ ^ p ^ h = 1)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    haloExponentH p h (classicalPoint p k ζ) = k := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [← weightPoint_natCast, haloExponentH_weightPoint hp2 hζ hpK k, Int.cast_natCast]`.

- **Mathlib/project lemmas needed**: `weightPoint_natCast`, `Int.cast_natCast`
- **Sources**: `decomposition.md` C-h.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ClassicalPointH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-C6] Cleanup `PhD/LWX/ClassicalPointH.lean`
- **Status**: done
- **File**: PhD/LWX/ClassicalPointH.lean
- **Depends on**: C16, C17, C18
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.ClassicalPointH` and `lake exe runLinter PhD.LWX.ClassicalPointH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of ClassicalPointH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [C19] `autFactor_haloWeightH_classicalPoint_prime_pow`
- **Status**: done
- **File**: PhD/LWX/ClassicalPointH.lean
- **Depends on**: C18
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The automorphy factor of the level-`h` halo weight at a classical point** is
`haloCharFunH(d)·d^{−k}·(cz + d)^k` (`autFactor_haloWeightH` with the halo exponent `k`,
`haloExponentH_classicalPoint`, and `mk_choose_natCast_mul_pow`). -/
theorem autFactor_haloWeightH_classicalPoint_prime_pow (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    {ζ : K} (h : ℕ) (hζ : ζ ^ p ^ h = 1) (k : ℕ) (h0 : (p : ℝ)⁻¹ < ‖classicalPoint p k ζ‖)
    (h1 : ‖classicalPoint p k ζ‖ < 1) (hT : ‖TH p h (classicalPoint p k ζ)‖ ^ 2 < (p : ℝ)⁻¹)
    (g : M1Kh h ψ) :
    (haloWeightH h ψ (classicalPoint p k ζ) ω hp2 hψ h0 h1 hT).toWeightSeries.autFactor g.1
        * linX g.1
      = PowerSeries.C (haloCharFunH h ψ (classicalPoint p k ζ) ω (g.1 1 1) * (g.1 1 1)⁻¹ ^ k)
        * linX g.1 ^ (k + 1) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `autFactor_haloWeightH_classicalPoint` (`ClassicalPoint.lean:412–436`) with `1 → h`:
`hd0 := (levelBounds_M1Kh h ψ _ hψ hT).d_ne_zero g.2`; `hlin` as at level `1`;
`rw [autFactor_haloWeightH h ψ (classicalPoint p k ζ) ω hp2 hψ h0 h1 hT g, haloExponentH_classicalPoint hp2 hζ hpK k, mk_choose_natCast_mul_pow k (g.1 1 0 / g.1 1 1), hlin, mul_pow, ← map_pow, map_mul, pow_succ]; ring`
with `hpK := norm_natCast_p ψ hψ`.

- **Mathlib/project lemmas needed**: `autFactor_haloWeightH`, `levelBounds_M1Kh`, `mk_choose_natCast_mul_pow` (`ClassicalPoint.lean:384`), `norm_natCast_p`
- **Sources**: `lwx.txt:466–470`, (2.3.2) `lwx.txt:600–604`; `decomposition.md` C-i; `ClassicalPoint.lean:412–436`.
- **Generality decision**: Only `ζ ^ p ^ h = 1`; the shape lemma and `classicalDataH` are terms in the skeleton.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ClassicalPointH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-C-FINAL] Cleanup `PhD/LWX/ClassicalPointH.lean` (final)
- **Status**: done
- **File**: PhD/LWX/ClassicalPointH.lean
- **Depends on**: C19 (and every earlier ticket of the file)
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.ClassicalPointH` and `lake exe runLinter PhD.LWX.ClassicalPointH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of ClassicalPointH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [G1] `autFactor_haloWeightH_weightPoint_neg_prime_pow`
- **Status**: done
- **File**: PhD/LWX/TargetPointH.lean
- **Depends on**: C13
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The automorphy factor of the level-`h` halo weight at the target point** satisfies
`autFactor · L^{k+2} = C(κ(d)·d^{k+2})`: `autFactor_haloWeightH` with the halo exponent
`−(k+2)` (`haloExponentH_weightPoint`) and `mk_choose_neg_natCast_mul_pow`. -/
theorem autFactor_haloWeightH_weightPoint_neg_prime_pow (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    {ζ : K} (h : ℕ) (hζ : ζ ^ p ^ h = 1) (k : ℕ)
    (h0 : (p : ℝ)⁻¹ < ‖weightPoint p (-(k + 2 : ℤ)) ζ‖)
    (h1 : ‖weightPoint p (-(k + 2 : ℤ)) ζ‖ < 1)
    (hT : ‖TH p h (weightPoint p (-(k + 2 : ℤ)) ζ)‖ ^ 2 < (p : ℝ)⁻¹) (g : M1Kh h ψ) :
    (haloWeightH h ψ (weightPoint p (-(k + 2 : ℤ)) ζ) ω hp2 hψ h0 h1 hT).toWeightSeries.autFactor
          g.1 * linX g.1 ^ (k + 2)
      = PowerSeries.C (haloCharFunH h ψ (weightPoint p (-(k + 2 : ℤ)) ζ) ω (g.1 1 1)
          * (g.1 1 1) ^ (k + 2)) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `autFactor_haloWeightH_weightPoint_neg` (`TargetPoint.lean:262–292`) with `1 → h` and
`haloExponentH_weightPoint hp2 hζ (norm_natCast_p ψ hψ) (-(k+2 : ℤ))` in place of `haloExponentH_one_weightPoint`;
`hcast`, `hlin`, `mk_choose_neg_natCast_mul_pow (k + 2) _`, `linear_combination` as at level `1`.

- **Mathlib/project lemmas needed**: `autFactor_haloWeightH`, `haloExponentH_weightPoint`, `mk_choose_neg_natCast_mul_pow` (`TargetPoint.lean:250`), `levelBounds_M1Kh`
- **Sources**: `lwx.txt:2070–2076`; `decomposition.md` G-a; `TargetPoint.lean:262–292`.
- **Generality decision**: Only `ζ ^ p ^ h = 1`; the `IsClassicalShape'` lemma is a term in the skeleton.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/TargetPointH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [G2] `oneAddPow_weightPoint_mul_padicExp_prime_pow`
- **Status**: done
- **File**: PhD/LWX/TargetPointH.lean
- **Depends on**: C10
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The binomial series at two weight points differ by an exponential**:
`(1+T_s)^{ψ y}·exp(p(t−s)·ψ y) = (1+T_t)^{ψ y}` for every `y ∈ ℤ_p` — both sides are continuous
in `y` and agree on `ℕ` (`oneAddPow_weightPoint_mul_padicExp` with the level-`h` norm bound
`norm_weightPoint_lt_one_prime_pow`). -/
theorem oneAddPow_weightPoint_mul_padicExp_prime_pow (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    {ζ : K} {h : ℕ} (hh : 0 < h) (hζ : IsPrimitiveRoot ζ (p ^ h))
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s t : ℤ) (y : ℤ_[p]) :
    oneAddPow (weightPoint p s ζ) (intHom ψ y)
        * PadicExpLog.padicExp (((p : ℕ) : K) * ((t - s : ℤ) : K) * intHom ψ y)
      = oneAddPow (weightPoint p t ζ) (intHom ψ y) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `oneAddPow_weightPoint_mul_padicExp` (`TargetPoint.lean:387–426`) verbatim, replacing the two uses of
`norm_weightPoint_lt_one hp2 hζ hpK _` by `norm_weightPoint_lt_one_prime_pow hp2 hh hζ hpK _` (continuity of
`oneAddPow`); the `ℕ`-agreement step (`oneAddPow_natCast`, `padicExp_natCast_mul`, `padicExp_add`) is unchanged.

- **Mathlib/project lemmas needed**: `continuous_oneAddPow_intHom`, `continuous_padicExp_mul_intHom`, `PadicInt.denseRange_natCast`, `oneAddPow_natCast`, `PadicExpLog.padicExp_natCast_mul`, `PadicExpLog.padicExp_add`
- **Sources**: `decomposition.md` G-b; `TargetPoint.lean:387–426`.
- **Generality decision**: `hh`, `hζ` are slack beyond `‖weightPoint‖ < 1` — record at cleanup (`_hx`), do not edit.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/TargetPointH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [G3] `specialize_univChar_targetChar_prime_pow`
- **Status**: done
- **File**: PhD/LWX/TargetPointH.lean
- **Depends on**: C9, C10, C15, C16, G2
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The specialised universal characters at the source and the target agree up to the
classical factors** at conductor `p^{h+1}`:
`[a]_{T₁}(ω·ω₀^{−2k−2})·(ψa)^{k+2} = [a]_{T₀}(ω)·(ψa)^{−k}` (`specialize_univChar_targetChar`
with the level-`h` inputs). -/
theorem specialize_univChar_targetChar_prime_pow (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K}
    {h : ℕ} (hh : 0 < h) (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹)
    (k : ℕ) (a : ℤ_[p]ˣ) :
    HaloInt.specialize (intHom ψ) (weightPoint p (-(k + 2 : ℤ)) ζ) (univChar (targetChar p ω k) a)
        * intHom ψ (a : ℤ_[p]) ^ (k + 2)
      = HaloInt.specialize (intHom ψ) (classicalPoint p k ζ) (univChar ω a)
        * (intHom ψ (a : ℤ_[p]))⁻¹ ^ k := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `specialize_univChar_targetChar` (`TargetPoint.lean:429–476`) verbatim with the level-`h` inputs:
`inv_lt_norm_weightPoint_prime_pow`, `norm_weightPoint_lt_one_prime_pow`, `inv_lt_norm_classicalPoint_prime_pow`,
`norm_classicalPoint_lt_one_prime_pow` in the two `specialize_univChar` calls, and `oneAddPow_weightPoint_mul_padicExp_prime_pow hp2 hψ hh hζ hpK (-(k+2:ℤ)) (k:ℤ) (logQuot a)` for `hbin`;
`specialize_univChar` (`Specialize.lean:217`) is level-free.

- **Mathlib/project lemmas needed**: `specialize_univChar`, `coe_eq_teichRes_mul_oneUnitPart`, `intHom_oneUnitPart_eq_padicExp`, `targetChar_apply`, `weightPoint_natCast`
- **Sources**: `lwx.txt:2070–2076`; `decomposition.md` G-c; `TargetPoint.lean:429–476`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/TargetPointH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-G1] Cleanup `PhD/LWX/TargetPointH.lean`
- **Status**: done
- **File**: PhD/LWX/TargetPointH.lean
- **Depends on**: G1, G2, G3
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.TargetPointH` and `lake exe runLinter PhD.LWX.TargetPointH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of TargetPointH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [G4] `targetConst_eq_classicalDataH_u`
- **Status**: done
- **File**: PhD/LWX/TargetPointH.lean
- **Depends on**: G3, C9, C10, C12, C15–C17
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **AG-ζ at level `h`**: the target-shape constants at the target point are the classical
datum's constants (`certConj_apply_one_one`, `haloCharFunH_psi` at both points,
`specialize_univChar_targetChar_prime_pow`). -/
theorem targetConst_eq_classicalDataH_u (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K} {h : ℕ}
    (hh : 0 < h) (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ)
    (i : ι) (t : Fin p) (a : ZMod (p ^ h)) :
    haloCharFunH h ψ (weightPoint p (-(k + 2 : ℤ)) ζ) (targetChar p ω k)
          (certConj θG h ψ U hU vRep hvΔ uu i t a 1 1)
        * (certConj θG h ψ U hU vRep hvΔ uu i t a 1 1) ^ (k + 2)
      = (classicalDataH ψ ω θG U hU vRep hvΔ uu hp2 hψ hh hζ hpK k).u i t a := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `targetConst_eq_classicalData_u` (`TargetPoint.lean:478–502`): `show` the unfolded `u`-field of `classicalDataH`,
`rw [certConj_apply_one_one, haloCharFunH_psi h ψ (weightPoint …) (targetChar p ω k) hp2 hψ (inv_lt_norm_weightPoint_prime_pow …) (norm_weightPoint_lt_one_prime_pow …) (norm_TH_weightPoint_sq_lt hp2 hζ.pow_eq_one hpK _) _, haloCharFunH_psi h ψ (classicalPoint p k ζ) ω hp2 hψ … _]`, then `exact specialize_univChar_targetChar_prime_pow ψ ω hp2 hψ hh hζ hpK k _`.

- **Mathlib/project lemmas needed**: `certConj_apply_one_one`, `haloCharFunH_psi`
- **Sources**: `decomposition.md` G-c; `TargetPoint.lean:478–502`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/TargetPointH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [G5] `targetData_classicalPointH`
- **Status**: done
- **File**: PhD/LWX/TargetPointH.lean
- **Depends on**: G1, G4
- **Parallel**: yes (within the dependency order)
- **Type**: proof (the `shape` field)

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The theta target of the classical datum at a classical point of conductor `p^{h+1}`**:
the halo point `T_{(−k−2,ψ)}` with the nebentypus `ω·ω₀^{−2k−2}`. -/
theorem targetData_classicalPointH (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K} {h : ℕ}
    (hh : 0 < h) (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    TargetDataH (classicalDataH ψ ω θG U hU vRep hvΔ uu hp2 hψ hh hζ hpK k) (targetChar p ω k)
      (weightPoint p (-(k + 2 : ℤ)) ζ) where
  h0 := inv_lt_norm_weightPoint_prime_pow hp2 hh hζ hpK _
  h1 := norm_weightPoint_lt_one_prime_pow hp2 hh hζ hpK _
  hT := norm_TH_weightPoint_sq_lt hp2 hζ.pow_eq_one hpK _
  shape := by sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Only `shape` is `sorry`: `have hu : (fun i t a => haloCharFunH h ψ (weightPoint …) (targetChar p ω k) (certConj θG h ψ U hU vRep hvΔ uu i t a 1 1) * (certConj … i t a 1 1) ^ (k + 2)) = (classicalDataH …).u := funext (fun i => funext fun t => funext fun a => targetConst_eq_classicalDataH_u ψ ω θG U hU vRep hvΔ uu hp2 hψ hh hζ hpK k i t a)`;
`rw [← hu]; exact isClassicalShape'_haloWeightH_weightPoint_neg_prime_pow ψ (targetChar p ω k) θG U hU vRep hvΔ uu hp2 hψ h hζ.pow_eq_one k _ _ _` (as `TargetPoint.lean:504–526`).

- **Mathlib/project lemmas needed**: `funext`
- **Sources**: `decomposition.md` G-d; `TargetPoint.lean:504–526`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/TargetPointH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-G-FINAL] Cleanup `PhD/LWX/TargetPointH.lean` (final)
- **Status**: done
- **File**: PhD/LWX/TargetPointH.lean
- **Depends on**: G5 (and every earlier ticket of the file)
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.TargetPointH` and `lake exe runLinter PhD.LWX.TargetPointH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of TargetPointH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [N1] `coe_oneAddPPowMul`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem coe_oneAddPPowMul (h : ℕ) (hh : 0 < h) (x : ℤ_[p]) :
    (oneAddPPowMul p h x : ℤ_[p]) = 1 + (p : ℤ_[p]) ^ h * x := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [oneAddPPowMul, coe_oneAddPMul, ← mul_assoc, ← pow_succ']` (or `pow_succ`), then `Nat.sub_add_cancel hh` to turn `h - 1 + 1` into `h`
(`obtain ⟨h', rfl⟩` first if easier).

- **Mathlib/project lemmas needed**: `coe_oneAddPMul` (`NebChar.lean:58`), `pow_succ`, `Nat.sub_add_cancel`
- **Sources**: `decomposition.md` N-a.
- **Generality decision**: `hh` necessary (junk at `h = 0`).
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/NebCharH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [N2] `oneAddPPowMul_one`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
@[simp] theorem oneAddPPowMul_one (x : ℤ_[p]) : oneAddPPowMul p 1 x = oneAddPMul p x := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`simp [oneAddPPowMul]` (`Nat.sub_self`, `pow_zero`, `one_mul`); or `Units.ext` + `coe_oneAddPMul`.

- **Mathlib/project lemmas needed**: `pow_zero`, `one_mul`
- **Sources**: `decomposition.md` N-a.
- **Generality decision**: Bridge only.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/NebCharH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [N3] `nebCharH_apply`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: C15, C16, C17
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem nebCharH_apply (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (a : ℤ_[p]ˣ) :
    nebCharH h ψ ω k ζ a
      = HaloInt.specialize (intHom ψ) (classicalPoint p k ζ) (univChar ω a)
        * (intHom ψ (a : ℤ_[p]))⁻¹ ^ k := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [nebCharH, nebCharKH, haloCharFunH_psi h ψ (classicalPoint p k ζ) ω hp2 hψ (inv_lt_norm_classicalPoint_prime_pow hp2 hh hζ hpK k) (norm_classicalPoint_lt_one_prime_pow hp2 hh hζ hpK k) (norm_TH_classicalPoint_sq_lt hp2 hζ.pow_eq_one hpK k) a]`
(as `NebChar.lean:72–79`).

- **Mathlib/project lemmas needed**: `haloCharFunH_psi`
- **Sources**: `decomposition.md` N-b; `NebChar.lean:72–79`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/NebCharH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-N1] Cleanup `PhD/LWX/NebCharH.lean`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N1, N2, N3
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.NebCharH` and `lake exe runLinter PhD.LWX.NebCharH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of NebCharH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [N4] `classicalDataH_u_eq_nebCharH`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The level-`h` classical datum's constants are the nebentypus at the `d`-entries of the disc
conjugates (`certConj_apply_one_one`). -/
theorem classicalDataH_u_eq_nebCharH (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (i : ι) (t : Fin p)
    (a : ZMod (p ^ h)) :
    (classicalDataH ψ ω θG U hU vRep hvΔ uu hp2 hψ hh hζ hpK k).u i t a
      = nebCharH h ψ ω k ζ (M1.toLocalMat (discConj h (certM1 θG U hU vRep hvΔ uu i t) a)).d := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `classicalData_u_eq_nebChar` (`NebChar.lean:88–98`): `show haloCharFunH h ψ _ ω (certConj …) * (certConj …)⁻¹ ^ k = _`;
`rw [certConj_apply_one_one]; rfl` (the RHS unfolds to `nebCharKH … (intHom ψ (d : ℤ_[p]))`).

- **Mathlib/project lemmas needed**: `certConj_apply_one_one` (`TargetPoint.lean:312`)
- **Sources**: `decomposition.md` N-b.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/NebCharH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [N5] `nebCharH_mul`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N3
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem nebCharH_mul (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (a b : ℤ_[p]ˣ) :
    nebCharH h ψ ω k ζ (a * b) = nebCharH h ψ ω k ζ a * nebCharH h ψ ω k ζ b := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `nebChar_mul` (`NebChar.lean:111–119`): `rw [nebCharH_apply … (a*b), nebCharH_apply … a, nebCharH_apply … b, univChar_mul hp2 ω a b, HaloInt.specialize_mul (intHom ψ) (norm_intHom ψ hψ) (inv_lt_norm_classicalPoint_prime_pow …) (norm_classicalPoint_lt_one_prime_pow …), Units.val_mul, map_mul, mul_inv, mul_pow]; ring`.

- **Mathlib/project lemmas needed**: `univChar_mul`, `HaloInt.specialize_mul`, `mul_inv`, `mul_pow`
- **Sources**: `decomposition.md` N-c; `NebChar.lean:111–119`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/NebCharH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [N6] `nebCharH_one`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N3
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem nebCharH_one (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) :
    nebCharH h ψ ω k ζ 1 = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `nebChar_one` (`NebChar.lean:120–124`): `rw [nebCharH_apply …, univChar_one?]` — as at level `1`: `univChar ω 1 = 1` (`NebChar.lean:122` uses `Units.val_one, map_one, inv_one, one_pow, one_mul` after unfolding `univChar`; copy the exact rewrite chain).

- **Mathlib/project lemmas needed**: as `NebChar.lean:120–124`
- **Sources**: `decomposition.md` N-c.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/NebCharH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-N2] Cleanup `PhD/LWX/NebCharH.lean`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N4, N5, N6
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.NebCharH` and `lake exe runLinter PhD.LWX.NebCharH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of NebCharH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [N7] `nebCharH_ne_zero`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N5, N6
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem nebCharH_ne_zero (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (a : ℤ_[p]ˣ) :
    nebCharH h ψ ω k ζ a ≠ 0 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `nebChar_ne_zero` (`NebChar.lean:125–133`): the specialisation is a unit (`HaloInt.specialize` of `univChar` is `ψ(ω ā) * oneAddPow …`, each nonzero — or use `nebCharH_mul`/`nebCharH_one` with `a * a⁻¹ = 1` to get `nebCharH a * nebCharH a⁻¹ = 1`, hence `≠ 0` (`left_ne_zero_of_mul_eq_one`)).  The second route is shortest.

- **Mathlib/project lemmas needed**: `left_ne_zero_of_mul_eq_one`, `mul_inv_cancel`
- **Sources**: `decomposition.md` N-c.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/NebCharH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [N8] `nebCharH_of_norm_sub_one_le_pow`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N3, C15–C18
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The conductor divides `p^{h+1}`**: the nebentypus is trivial on `1 + p^{h+1}ℤ_p`
(`specialize_univChar_eq_padicExp` at level `h`, with the halo exponent `k`). -/
theorem nebCharH_of_norm_sub_one_le_pow (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {a : ℤ_[p]ˣ}
    (ha : ‖(a : ℤ_[p]) - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1)) : nebCharH h ψ ω k ζ a = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `nebChar_of_norm_sub_one_le_sq` (`NebChar.lean:134–160`) with level `h`: `h3 : ‖(p:K)‖ < 1`; `hle : ‖a - 1‖ ≤ p⁻¹` (from `ha` and `pow_le_inv_p h`);
`hL : ‖padicLog (intHom ψ a)‖ ≤ ‖intHom ψ a - 1‖ ≤ p⁻¹^(h+1)` … as at level `1`;
`rw [nebCharH_apply …, specialize_univChar_eq_padicExp h ψ (classicalPoint p k ζ) ω hp2 hψ (inv_lt_norm_classicalPoint_prime_pow …) (norm_classicalPoint_lt_one_prime_pow …) (norm_TH_classicalPoint_sq_lt hp2 hζ.pow_eq_one hpK k) ha, haloExponentH_classicalPoint hp2 hζ.pow_eq_one hpK k, PadicExpLog.padicExp_natCast_mul h3 hp2 hL k, PadicExpLog.padicExp_padicLog h3 hp2 hu, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hne)]`
where `hu : ‖intHom ψ a - 1‖ ≤ p⁻¹` and `hne : intHom ψ a ≠ 0`.

- **Mathlib/project lemmas needed**: `specialize_univChar_eq_padicExp` (`HaloWeightH.lean:458`), `haloExponentH_classicalPoint`, `PadicExpLog.padicExp_natCast_mul`, `PadicExpLog.padicExp_padicLog`, `pow_le_inv_p`
- **Sources**: [LWX, §2.1] `lwx.txt:462–464`; `decomposition.md` N-d; `NebChar.lean:134–160`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/NebCharH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [N9] `continuous_zeta_pow_toZModPow`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `ℓ ↦ ζ^{ℓ mod p^h}` is locally constant on `ℤ_p`, hence continuous. -/
theorem continuous_zeta_pow_toZModPow (h : ℕ) (ζ : K) :
    Continuous fun ℓ : ℤ_[p] => ζ ^ (PadicInt.toZModPow h ℓ).val := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Locally constant ⇒ continuous: `refine continuous_iff_continuousAt.2 fun ℓ => ?_`; use `Metric.continuousAt_iff`/`IsOpen` of the ball: for `‖ℓ' - ℓ‖ ≤ p⁻¹^h` (`PadicInt.norm_le_pow_iff_mem_span_pow`, `Ideal.mem_span_singleton`), `toZModPow h ℓ' = toZModPow h ℓ` (`← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow`), so the function is constant on the ball (`Filter.EventuallyEq`, `continuousAt_const.congr`).  Level-`1` template: `continuous_zeta_pow_toZMod` (`NebChar.lean:169–181`) with `ker_toZMod` → `ker_toZModPow`.

- **Mathlib/project lemmas needed**: `PadicInt.ker_toZModPow`, `PadicInt.norm_le_pow_iff_mem_span_pow`, `Ideal.mem_span_singleton`, `continuousAt_const`, `ContinuousAt.congr`, `Metric.eventually_nhds_iff`
- **Sources**: `decomposition.md` N-e; `NebChar.lean:169–181`.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/NebCharH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-N3] Cleanup `PhD/LWX/NebCharH.lean`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N7, N8, N9
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.NebCharH` and `lake exe runLinter PhD.LWX.NebCharH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of NebCharH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [N10] `oneAddPow_sub_one_intHom_prime_pow`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N9, C3
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **`(1 + T)^ℓ` at `T = ζ − 1` is `ζ^{ℓ mod p^h}`** for a primitive `p^h`-th root of unity:
both sides are continuous in `ℓ ∈ ℤ_p` and agree on `ℕ`. -/
theorem oneAddPow_sub_one_intHom_prime_pow (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (ℓ : ℤ_[p]) :
    oneAddPow (ζ - 1) (intHom ψ ℓ) = ζ ^ (PadicInt.toZModPow h ℓ).val := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `oneAddPow_sub_one_intHom` (`NebChar.lean:183–196`): both sides continuous in `ℓ` (`continuous_oneAddPow_intHom ψ hψ (hT : ‖ζ - 1‖ < 1)` with `hT` from C5's power `< 1` or `norm_sub_one_lt_one_of_pow_prime_pow_eq_one`, and N9), agree on `ℕ` (`PadicInt.denseRange_natCast`, `oneAddPow_natCast`: `(1 + (ζ-1))^n = ζ^n`, and `ζ ^ n = ζ ^ (toZModPow h n).val` by `ZMod.val_natCast`, `Nat.mod_add_div`, `pow_add`, `pow_mul`, `hζ.pow_eq_one`); `Continuous.ext_on`/`DenseRange.equalizer`.

- **Mathlib/project lemmas needed**: `continuous_oneAddPow_intHom`, `PadicInt.denseRange_natCast`, `DenseRange.equalizer`, `oneAddPow_natCast`, `ZMod.val_natCast`, `map_natCast`, `Nat.mod_add_div`
- **Sources**: `decomposition.md` N-e; `NebChar.lean:183–196`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/NebCharH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [N11] `nebCharH_oneAddPPowMul`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N1, N3, N10, G2
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The nebentypus on `1 + p^hℤ_p`** is `ζ^{ℓ⟨a⟩ mod p^h}`. -/
theorem nebCharH_oneAddPPowMul (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (x : ℤ_[p]) :
    nebCharH h ψ ω k ζ (oneAddPPowMul p h x)
      = ζ ^ (PadicInt.toZModPow h (logQuot (oneAddPPowMul p h x))).val := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `nebChar_oneAddPMul` (`NebChar.lean:205–245`): `set a := oneAddPPowMul p h x`; `hL`, `hpL`; `nebCharH_apply`, `specialize_univChar … ω a`; `ā = 1` (`unitsMap_toZMod_eq_one_of_norm_sub_one_le` with `‖a - 1‖ ≤ p⁻¹` from `coe_oneAddPPowMul hh` and `pow_le_inv_p`); `hbin` from `oneAddPow_weightPoint_mul_padicExp_prime_pow … 0 k (logQuot a)` (`weightPoint_natCast`, `weightPoint p 0 ζ = ζ - 1`); `hexp := intHom_oneUnitPart_eq_padicExp ψ hp2 hψ a` with `oneUnitPart_oneAddPMul` at `p^(h-1) x`; `oneAddPow_sub_one_intHom_prime_pow`; cancel `(ψ⟨a⟩)^k · (ψ a)^{−k}` (`inv_pow`, `mul_inv_cancel₀`).

- **Mathlib/project lemmas needed**: `specialize_univChar`, `unitsMap_toZMod_eq_one_of_norm_sub_one_le`, `intHom_oneUnitPart_eq_padicExp`, `oneUnitPart_oneAddPMul`, `pow_le_inv_p`
- **Sources**: `decomposition.md` N-f; `NebChar.lean:205–245`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/NebCharH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [N12] `norm_logQuot_oneAddPPowMul_one`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N1
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `ℓ⟨1 + p^h⟩ = log(1 + p^h)/p` has norm `p^{−(h−1)}` (`norm_padicLog_eq`). -/
theorem norm_logQuot_oneAddPPowMul_one (hp2 : p ≠ 2) (hh : 0 < h) :
    ‖(logQuot (oneAddPPowMul p h 1) : ℤ_[p])‖ = (p : ℝ)⁻¹ ^ (h - 1) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `norm_logQuot_oneAddPMul_one` (`NebChar.lean:247–262`): `hsub : ((oneAddPPowMul p h 1 : ℤ_[p]) : ℚ_[p]) - 1 = p^h` (`coe_oneAddPPowMul hh`, `push_cast; ring`), `hnp : ‖(p^h : ℚ_[p])‖ = p⁻¹^h`; `‖log(1 + p^h)‖ = ‖p^h‖` by `PadicExpLog.norm_padicLog_eq h3 hp2 hu2` (`‖p^h‖ ≤ p⁻¹ < 1`, and the disc condition `‖p^h‖² < ‖p‖` for `h ≥ 1`); `logQuot = log/p` (`coe_logQuot`), `norm_div`, `Padic.norm_p`, `PadicInt.norm_def`; then `p⁻¹^h / p⁻¹ = p⁻¹^(h-1)` (`pow_sub₀`/`obtain ⟨h', rfl⟩`, `pow_succ`, `mul_div_cancel_right₀`).

- **Mathlib/project lemmas needed**: `PadicExpLog.norm_padicLog_eq`, `coe_logQuot`, `PadicInt.norm_def`, `Padic.norm_p`, `pow_succ`
- **Sources**: `decomposition.md` N-f; `NebChar.lean:247–262`.
- **Generality decision**: `hh` necessary.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/NebCharH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-N4] Cleanup `PhD/LWX/NebCharH.lean`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N10, N11, N12
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.NebCharH` and `lake exe runLinter PhD.LWX.NebCharH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of NebCharH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [N13] `isPrimitiveRoot_nebCharH_oneAddPPowMul_one`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N11, N12
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The conductor is exactly `p^{h+1}`**: `nebCharH (1 + p^h)` is a primitive `p`-th root of
unity (`ℓ⟨1 + p^h⟩ ≡ p^{h−1}·u (mod p^h)` with `p ∤ u`, and `ζ^{p^{h−1}}` is a primitive `p`-th
root, `IsPrimitiveRoot.pow_of_dvd`). -/
theorem isPrimitiveRoot_nebCharH_oneAddPPowMul_one (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hh : 0 < h) (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) :
    IsPrimitiveRoot (nebCharH h ψ ω k ζ (oneAddPPowMul p h 1)) p := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `rw [nebCharH_oneAddPPowMul … 1]`; set `ℓ := logQuot (oneAddPPowMul p h 1)`, `v := (PadicInt.toZModPow h ℓ).val`.
2. From N12: `ℓ ∈ span {p^(h-1)}` and `ℓ ∉ span {p^h}` (`PadicInt.norm_le_pow_iff_mem_span_pow`, strictness via `‖ℓ‖ = p⁻¹^(h-1) > p⁻¹^h`).
   Write `ℓ = p^(h-1) * u` (`Ideal.mem_span_singleton`) with `‖u‖ = 1`, i.e. `¬ p ∣ (toZMod u).val`-type fact: `toZModPow h ℓ = p^(h-1) * toZModPow h u` (`map_mul`, `map_pow`, `map_natCast`).
3. `v = p^(h-1) * (toZModPow h u).val` modulo `p^h`; show `IsPrimitiveRoot (ζ ^ v) p`: `ζ ^ v = (ζ ^ p^(h-1)) ^ ((toZModPow h u).val)` up to `ζ^{p^h} = 1` (`pow_mul`, `ZMod.val_mul`, `Nat.mod`), `hζ.pow_of_dvd (pow_ne_zero _ hp.out.ne_zero) (pow_dvd_pow p (Nat.sub_le h 1))` gives `IsPrimitiveRoot (ζ ^ p^(h-1)) (p^h / p^(h-1)) = p` (`Nat.pow_div`, `hh`), then `.pow_of_coprime _ (coprime since ¬ p ∣ (toZModPow h u).val ← ‖u‖ = 1 ← PadicInt.norm_eq_one_iff / cast_toZModPow 1 h)`.
   Alternative (as the level-`1` proof `NebChar.lean:263–281`): `hζ.pow_of_coprime` cannot be used directly since `p^h ∤ v`; the two-step route above is the one to take.  Expect ~60 lines; use `Nat.Coprime` API (`Nat.Prime.coprime_iff_not_dvd`, `Nat.Coprime.symm`).

- **Mathlib/project lemmas needed**: `PadicInt.norm_le_pow_iff_mem_span_pow`, `Ideal.mem_span_singleton`, `PadicInt.cast_toZModPow`, `IsPrimitiveRoot.pow_of_dvd`, `IsPrimitiveRoot.pow_of_coprime`, `Nat.pow_div`, `pow_dvd_pow`, `ZMod.val_mul`, `Nat.Prime.coprime_iff_not_dvd`
- **Sources**: [LWX, §2.1] `lwx.txt:462–464` (conductor exactly `p^m`); `decomposition.md` N-f; `NebChar.lean:263–281`.
- **Generality decision**: `hh` necessary.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/NebCharH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [N14] `nebCharH_oneAddPPowMul_natCast`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N1, N5, N6, N8
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `nebCharH (1 + p^h n) = nebCharH (1 + p^h)^n`: `(1 + p^h)^n ≡ 1 + p^h n (mod p^{h+1})`. -/
theorem nebCharH_oneAddPPowMul_natCast (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (n : ℕ) :
    nebCharH h ψ ω k ζ (oneAddPPowMul p h n)
      = nebCharH h ψ ω k ζ (oneAddPPowMul p h 1) ^ n := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `nebChar_oneAddPMul_natCast` (`NebChar.lean:282–306`): induction on `n`; `zero`: `oneAddPPowMul p h 0 = 1` (`Units.ext`, `coe_oneAddPPowMul hh`, `mul_zero`), `nebCharH_one`; `succ`: `u := oneAddPPowMul p h n * oneAddPPowMul p h 1`, `(1 + p^h n)(1 + p^h) = (1 + p^h (n+1)) * (1 + w)` with `‖w‖ ≤ p⁻¹^(h+1)` (`w = p^{2h} n / (1 + p^h(n+1))`, `2h ≥ h+1`), `nebCharH_mul`, N8 on `1 + w`, `pow_succ`.

- **Mathlib/project lemmas needed**: `nebCharH_mul`, `nebCharH_of_norm_sub_one_le_pow`, `pow_succ`, `Units.ext`
- **Sources**: `decomposition.md` N-f; `NebChar.lean:282–306`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/NebCharH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [N15] `sum_nebCharH_oneAddPPowMul_mul_eq_zero`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N13, N14
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The character sum**: for `p ∤ b`, `∑_{c < p} ψ_neb(1 + p^h b c) = 0`
(`IsPrimitiveRoot.geom_sum_eq_zero` at the primitive root `nebCharH (1 + p^h)^b`). -/
theorem sum_nebCharH_oneAddPPowMul_mul_eq_zero (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hh : 0 < h) (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {b : ℕ}
    (hb : ¬ p ∣ b) :
    ∑ c ∈ Finset.range p, nebCharH h ψ ω k ζ (oneAddPPowMul p h ((b : ℤ_[p]) * c)) = 0 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `sum_nebChar_oneAddPMul_mul_eq_zero` (`NebChar.lean:309–318`): `hξ := (isPrimitiveRoot_nebCharH_oneAddPPowMul_one …).pow_of_coprime b (coprime from hb)`; `rw [← hξ.geom_sum_eq_zero hp.out.one_lt]`; termwise `(b : ℤ_[p]) * c = ((b * c : ℕ) : ℤ_[p])`, `nebCharH_oneAddPPowMul_natCast`, `pow_mul`.

- **Mathlib/project lemmas needed**: `IsPrimitiveRoot.pow_of_coprime`, `IsPrimitiveRoot.geom_sum_eq_zero`, `pow_mul`
- **Sources**: `decomposition.md` N-g; `NebChar.lean:309–318`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/NebCharH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-N5] Cleanup `PhD/LWX/NebCharH.lean`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N13, N14, N15
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.NebCharH` and `lake exe runLinter PhD.LWX.NebCharH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of NebCharH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [N16] `sum_inv_nebCharH_oneAddPPowMul_mul_eq_zero`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N13, N14
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The character sum, inverted**: for `p ∤ b`, `∑_{c < p} ψ_neb(1 + p^h b c)⁻¹ = 0`. -/
theorem sum_inv_nebCharH_oneAddPPowMul_mul_eq_zero (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hh : 0 < h) (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {b : ℕ}
    (hb : ¬ p ∣ b) :
    ∑ c ∈ Finset.range p, (nebCharH h ψ ω k ζ (oneAddPPowMul p h ((b : ℤ_[p]) * c)))⁻¹ = 0 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As N15 with `hξ := (…).inv.pow_of_coprime b _` and `inv_pow` (`NebChar.lean:322–332`).

- **Mathlib/project lemmas needed**: `IsPrimitiveRoot.inv`, `inv_pow`
- **Sources**: `decomposition.md` N-g; `NebChar.lean:322–332`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/NebCharH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [N17] `sum_inv_nebCharKH_eq_zero`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N1, N16
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The same in terms of `nebCharKH` at `ψ(1 + b c p^h)`, the spelling that appears in the
identity computation (the `d`-entry of `ℓQH b c` is `1 + bcp^h`). -/
theorem sum_inv_nebCharKH_eq_zero (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {b : ℕ}
    (hb : ¬ p ∣ b) :
    ∑ c ∈ Finset.range p,
      (nebCharKH h ψ ω k ζ (ψ (1 + (b : ℚ_[p]) * c * (p : ℚ_[p]) ^ h)))⁻¹ = 0 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `sum_inv_nebCharK_eq_zero` (`NebChar.lean:334–345`): `rw [← sum_inv_nebCharH_oneAddPPowMul_mul_eq_zero …]`; termwise `nebCharH`, `intHom_apply`, `coe_oneAddPPowMul hh`, and `(((1 + p^h * (b * c) : ℤ_[p]) : ℚ_[p])) = 1 + b * c * p^h` (`push_cast; ring`).

- **Mathlib/project lemmas needed**: `intHom_apply`, `push_cast`
- **Sources**: `decomposition.md` N-g; `NebChar.lean:334–345`.
- **Generality decision**: The spelling `ψ (1 + (b : ℚ_[p]) * c * (p : ℚ_[p]) ^ h)` is the one consumed by I11/I12.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/NebCharH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [N18] `nebCharKH_psi_mul`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N5
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `hmul`: `nebCharKH` is multiplicative on `ψ`-images of `p`-adic units. -/
theorem nebCharKH_psi_mul (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {x y : ℚ_[p]}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    nebCharKH h ψ ω k ζ (ψ (x * y)) = nebCharKH h ψ ω k ζ (ψ x) * nebCharKH h ψ ω k ζ (ψ y) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `nebCharK_psi_mul` (`NebChar.lean:347–362`): `let z : ℤ_[p] := ⟨x, hx.le⟩` (never inline), `PadicInt.isUnit_iff`, units `ux, uy`; `nebCharH_mul` at `ux * uy`.

- **Mathlib/project lemmas needed**: `PadicInt.isUnit_iff`, `IsUnit.unit`
- **Sources**: `decomposition.md` N-h; `NebChar.lean:347–362`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/NebCharH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-N6] Cleanup `PhD/LWX/NebCharH.lean`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N16, N17, N18
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.NebCharH` and `lake exe runLinter PhD.LWX.NebCharH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of NebCharH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [N19] `nebCharKH_psi_ne_zero`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N7
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `hne`: `nebCharKH` does not vanish on `ψ`-images of `p`-adic units. -/
theorem nebCharKH_psi_ne_zero (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {x : ℚ_[p]}
    (hx : ‖x‖ = 1) : nebCharKH h ψ ω k ζ (ψ x) ≠ 0 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `nebCharK_psi_ne_zero` (`NebChar.lean:363–374`) with N7.

- **Mathlib/project lemmas needed**: `PadicInt.isUnit_iff`
- **Sources**: `decomposition.md` N-h.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/NebCharH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [N20] `nebCharKH_psi_of_norm_sub_one_le_pow`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N8
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `hcond`: `nebCharKH` is trivial on `ψ(1 + p^{h+1}ℤ_p)`. -/
theorem nebCharKH_psi_of_norm_sub_one_le_pow (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {x : ℚ_[p]}
    (hx : ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1)) : nebCharKH h ψ ω k ζ (ψ x) = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `nebCharK_psi_of_norm_sub_one_le_sq` (`NebChar.lean:375–392`): `‖x‖ = 1` from `hx` (`p⁻¹^(h+1) < 1`), the unit `⟨x, _⟩`, N8 with `‖⟨x,_⟩ - 1‖ = ‖x - 1‖` (`PadicInt.norm_def`, `PadicInt.coe_sub`, `PadicInt.coe_one`).

- **Mathlib/project lemmas needed**: `PadicInt.norm_def`, `PadicInt.coe_sub`, `pow_lt_one₀`
- **Sources**: `decomposition.md` N-h; `NebChar.lean:375–392`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/NebCharH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [N21] `oneAddPow_inv_sub_one_mul_prime_pow`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N10
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `(1+T)^ℓ` at `T = ζ⁻¹ − 1` and at `T = ζ − 1` are inverse to each other. -/
theorem oneAddPow_inv_sub_one_mul_prime_pow (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (ℓ : ℤ_[p]) :
    oneAddPow (ζ⁻¹ - 1) (intHom ψ ℓ) * oneAddPow (ζ - 1) (intHom ψ ℓ) = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [oneAddPow_sub_one_intHom_prime_pow ψ ζ⁻¹ hp2 hψ hh hζ.inv hpK, oneAddPow_sub_one_intHom_prime_pow ψ ζ hp2 hψ hh hζ hpK, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ (hζ.ne_zero (pow_ne_zero _ hp.out.ne_zero)))]` (as `NebChar.lean:406–412`).

- **Mathlib/project lemmas needed**: `IsPrimitiveRoot.inv`, `IsPrimitiveRoot.ne_zero`, `inv_pow`, `inv_mul_cancel₀`
- **Sources**: `decomposition.md` N-i; `NebChar.lean:406–412`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/NebCharH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-N7] Cleanup `PhD/LWX/NebCharH.lean`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N19, N20, N21
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.NebCharH` and `lake exe runLinter PhD.LWX.NebCharH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of NebCharH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [N22] `nebCharH_eq`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N3, N10, G2
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **`nebCharH` in closed form**: `ψ_neb(a) = ω(ā) · ζ^{ℓ⟨a⟩ mod p^h} · ω₀(ā)^{−k}`. -/
theorem nebCharH_eq (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (a : ℤ_[p]ˣ) :
    nebCharH h ψ ω k ζ a
      = intHom ψ (ω (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p])
        * ζ ^ (PadicInt.toZModPow h (logQuot a)).val
        * (intHom ψ (teichRes (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) :
            ℤ_[p]))⁻¹ ^ k := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `nebChar_eq` (`NebChar.lean:416–461`) with `oneAddPow_sub_one_intHom_prime_pow` in place of `oneAddPow_sub_one_intHom` (so `toZMod → toZModPow h`), `oneAddPow_weightPoint_mul_padicExp_prime_pow` at `(0, k)`, `intHom_oneUnitPart_eq_padicExp`, `coe_eq_teichRes_mul_oneUnitPart`, `specialize_univChar`; the closing `field_simp; ring` as at level `1`.

- **Mathlib/project lemmas needed**: `specialize_univChar`, `coe_eq_teichRes_mul_oneUnitPart`, `intHom_oneUnitPart_eq_padicExp`
- **Sources**: `decomposition.md` N-i; `NebChar.lean:416–461`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/NebCharH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [N23] `nebCharH_partnerChar`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N22
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The partner point carries the inverse nebentypus** at conductor `p^{h+1}`:
at `T_{χ_k}(ζ⁻¹)` with tame character `ω⁻¹ω₀^{2k}`, the nebentypus is `ψ_neb⁻¹`. -/
theorem nebCharH_partnerChar (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (a : ℤ_[p]ˣ) :
    nebCharH h ψ (partnerChar p ω k) k ζ⁻¹ a = (nebCharH h ψ ω k ζ a)⁻¹ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `nebChar_partnerChar` (`NebChar.lean:463–478`): `rw [nebCharH_eq h ψ (partnerChar p ω k) k ζ⁻¹ hp2 hψ hh hζ.inv hpK, nebCharH_eq h ψ ω k ζ hp2 hψ hh hζ hpK, partnerChar_apply, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, map_units_inv]; simp only [inv_pow, mul_inv, inv_inv]; field_simp; ring` with `hω, ht, hz` nonvanishing facts.

- **Mathlib/project lemmas needed**: `partnerChar_apply`, `map_units_inv`, `field_simp`
- **Sources**: `lwx.txt:2028–2036`; `decomposition.md` N-i; `NebChar.lean:463–478`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/NebCharH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [N24] `autFactor_haloWeightH_partner_eq_inv_nebCharKH`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N23
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The shape constant of the partner level-`h` halo weight at `g ∈ M1Kh h ψ` is
`nebCharKH(g 1 1)⁻¹` (`g 1 1 = ψ d` with `d` a unit, `mem_M1Kh_iff`, `mem_Mh_iff`). -/
theorem autFactor_haloWeightH_partner_eq_inv_nebCharKH (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h) (hζ : IsPrimitiveRoot ζ (p ^ h))
    (h0 : (p : ℝ)⁻¹ < ‖classicalPoint p k ζ⁻¹‖) (h1 : ‖classicalPoint p k ζ⁻¹‖ < 1)
    (hT : ‖TH p h (classicalPoint p k ζ⁻¹)‖ ^ 2 < (p : ℝ)⁻¹) (g : M1Kh h ψ) :
    (haloWeightH h ψ (classicalPoint p k ζ⁻¹) (partnerChar p ω k) hp2 hψ h0 h1
          hT).toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebCharKH h ψ ω k ζ (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1) := by
  sorry
```

- **Depends on (declarations)**: `autFactor_haloWeightH_classicalPoint_eq_nebCharKH`, `nebCharKH_partnerChar` (terms in the skeleton)

**Proof sketch**:
Transplant `autFactor_haloWeightH_partner_eq_inv_nebCharK` (`NebChar.lean:489–507`): `rw [autFactor_haloWeightH_classicalPoint_eq_nebCharKH h ψ (partnerChar p ω k) k ζ⁻¹ hp2 hψ hζ.inv.pow_eq_one h0 h1 hT g]`; `obtain ⟨δ, hδ, hδg⟩ := (mem_M1Kh_iff h ψ).1 g.2`; `hd : ‖δ 1 1‖ = 1 := (mem_Mh_iff.1 hδ).2.2.1`; `let z : ℤ_[p] := ⟨δ 1 1, hd.le⟩`, unit `d`; `hg11 : g.1 1 1 = intHom ψ d`; `rw [hg11, nebCharKH_partnerChar … d]`.

- **Mathlib/project lemmas needed**: `mem_M1Kh_iff`, `mem_Mh_iff`, `PadicInt.isUnit_iff`, `RingHom.mapMatrix_apply`, `Matrix.map_apply`
- **Sources**: `decomposition.md` N-i; `NebChar.lean:489–507`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/NebCharH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-N8] Cleanup `PhD/LWX/NebCharH.lean`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N22, N23, N24
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.NebCharH` and `lake exe runLinter PhD.LWX.NebCharH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of NebCharH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [N25] `classicalDataH_partnerChar_u`
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N4, N23
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The constants of the partner level-`h` classical datum are the inverses of the datum's. -/
theorem classicalDataH_partnerChar_u (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h)
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (i : ι) (t : Fin p)
    (a : ZMod (p ^ h)) :
    (classicalDataH ψ (partnerChar p ω k) θG U hU vRep hvΔ uu hp2 hψ hh hζ.inv hpK k).u i t a
      = ((classicalDataH ψ ω θG U hU vRep hvΔ uu hp2 hψ hh hζ hpK k).u i t a)⁻¹ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [classicalDataH_u_eq_nebCharH h ψ (partnerChar p ω k) k ζ⁻¹ θG U hU vRep hvΔ uu hp2 hψ hh hζ.inv hpK, classicalDataH_u_eq_nebCharH h ψ ω k ζ θG U hU vRep hvΔ uu hp2 hψ hh hζ hpK, nebCharH_partnerChar h ψ ω k ζ hp2 hψ hh hζ hpK]` (as `NebChar.lean:509–516`).

- **Mathlib/project lemmas needed**: —
- **Sources**: `decomposition.md` N-i; `NebChar.lean:509–516`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/NebCharH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-N-FINAL] Cleanup `PhD/LWX/NebCharH.lean` (final)
- **Status**: done
- **File**: PhD/LWX/NebCharH.lean
- **Depends on**: N25 (and every earlier ticket of the file)
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.NebCharH` and `lake exe runLinter PhD.LWX.NebCharH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of NebCharH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L1] `wQH_one`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem wQH_one : wQH p 1 = wQ p := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`simp [wQH, wQ]` (`pow_one`).

- **Mathlib/project lemmas needed**: `pow_one`
- **Sources**: `decomposition.md` L-a.
- **Generality decision**: Bridge.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L2] `ℓQH_one`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem ℓQH_one (b c : ℚ_[p]) : ℓQH p 1 b c = ℓQ p b c := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`ext i j; fin_cases i <;> fin_cases j <;> simp [ℓQH, ℓQ] <;> field_simp <;> ring` (`p ^ 1 * p ^ 1 / p = p`, `hp0 : (p : ℚ_[p]) ≠ 0`).

- **Mathlib/project lemmas needed**: `pow_one`, `field_simp`
- **Sources**: `decomposition.md` L-a.
- **Generality decision**: Bridge.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L3] `tMatH_one`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem tMatH_one (a : ℚ_[p]) : tMatH p 1 a = tMat p a := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`simp [tMatH, tMat]`.

- **Mathlib/project lemmas needed**: `pow_one`
- **Sources**: `decomposition.md` L-a.
- **Generality decision**: Bridge.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-L1] Cleanup `PhD/LWX/AtkinLehnerLocalH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: L1, L2, L3
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerLocalH` and `lake exe runLinter PhD.LWX.AtkinLehnerLocalH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerLocalH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L4] `det_wQH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
@[simp] theorem det_wQH (h : ℕ) : (wQH p h).det = (p : ℚ_[p]) ^ (h + 1) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [wQH, Matrix.det_fin_two_of]; ring` (`0 * 0 - p^h * (-p) = p^(h+1)`, `pow_succ`).

- **Mathlib/project lemmas needed**: `Matrix.det_fin_two_of`, `pow_succ`
- **Sources**: `decomposition.md` L-a; `AtkinLehnerLocal.lean:84–86`.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L5] `det_ℓQH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
@[simp] theorem det_ℓQH (h : ℕ) (b c : ℚ_[p]) : (ℓQH p h b c).det = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [ℓQH, Matrix.det_fin_two_of]; field_simp; ring` with `hp0 : (p : ℚ_[p]) ≠ 0` (`Nat.cast_ne_zero.2 hp.out.ne_zero`): `(1 − X)(1 + X) + b²c(p^h p^h/p)(cp) = 1 − X² + b²c²p^{2h} = 1`.

- **Mathlib/project lemmas needed**: `Matrix.det_fin_two_of`, `field_simp`
- **Sources**: `decomposition.md` L-a; `AtkinLehnerLocal.lean:88–90`.
- **Generality decision**: Every `h` (the `p^h·p^h/p` spelling).
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L6] `det_tMatH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
@[simp] theorem det_tMatH (h : ℕ) (a : ℚ_[p]) : (tMatH p h a).det = (p : ℚ_[p]) ^ h := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [tMatH, Matrix.det_fin_two_of]; ring`.

- **Mathlib/project lemmas needed**: `Matrix.det_fin_two_of`
- **Sources**: `decomposition.md` L-a.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-L2] Cleanup `PhD/LWX/AtkinLehnerLocalH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: L4, L5, L6
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerLocalH` and `lake exe runLinter PhD.LWX.AtkinLehnerLocalH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerLocalH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L7] `wQH_mul_wQHinv`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem wQH_mul_wQHinv (h : ℕ) : wQH p h * wQHinv p h = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`ext i j; fin_cases i <;> fin_cases j <;> simp [wQH, wQHinv, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp` with `hp0` and `hph : (p:ℚ_[p])^h ≠ 0` (`AtkinLehnerLocal.lean:92–96`).

- **Mathlib/project lemmas needed**: `Matrix.mul_apply`, `Fin.sum_univ_two`, `pow_ne_zero`
- **Sources**: `decomposition.md` L-a.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L8] `wQHinv_mul_wQH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem wQHinv_mul_wQH (h : ℕ) : wQHinv p h * wQH p h = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As L7.

- **Mathlib/project lemmas needed**: as L7
- **Sources**: `AtkinLehnerLocal.lean:97–101`.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L9] `ℓQH_mul_ℓQHinv`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem ℓQH_mul_ℓQHinv (h : ℕ) (b c : ℚ_[p]) : ℓQH p h b c * ℓQHinv p h b c = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`ext i j; fin_cases i <;> fin_cases j <;> simp [ℓQH, ℓQHinv, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring` (`AtkinLehnerLocal.lean:102–106`); the off-diagonal entries cancel identically, the diagonal is `1 − X² + b²c²p^{2h}`.

- **Mathlib/project lemmas needed**: as L7
- **Sources**: `decomposition.md` L-a.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-L3] Cleanup `PhD/LWX/AtkinLehnerLocalH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: L7, L8, L9
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerLocalH` and `lake exe runLinter PhD.LWX.AtkinLehnerLocalH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerLocalH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L10] `ℓQHinv_mul_ℓQH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem ℓQHinv_mul_ℓQH (h : ℕ) (b c : ℚ_[p]) : ℓQHinv p h b c * ℓQH p h b c = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As L9.

- **Mathlib/project lemmas needed**: as L7
- **Sources**: `AtkinLehnerLocal.lean:107–111`.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L11] `tMatH_mul_tMatHInv`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem tMatH_mul_tMatHInv (h : ℕ) (a : ℚ_[p]) : tMatH p h a * tMatHInv p h a = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`ext i j; fin_cases i <;> fin_cases j <;> simp [tMatH, tMatHInv, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp` (`AtkinLehnerLocal.lean:112–118`).

- **Mathlib/project lemmas needed**: as L7
- **Sources**: `decomposition.md` L-a.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L12] `tMatHInv_mul_tMatH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem tMatHInv_mul_tMatH (h : ℕ) (a : ℚ_[p]) : tMatHInv p h a * tMatH p h a = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As L11.

- **Mathlib/project lemmas needed**: as L7
- **Sources**: `AtkinLehnerLocal.lean:119–125`.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-L4] Cleanup `PhD/LWX/AtkinLehnerLocalH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: L10, L11, L12
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerLocalH` and `lake exe runLinter PhD.LWX.AtkinLehnerLocalH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerLocalH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L13] `sQ_mul_tMatH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem sQ_mul_tMatH (h : ℕ) (a b : ℚ_[p]) : sQ p b * tMatH p h a = tMatH p h (a + b) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`ext i j; fin_cases i <;> fin_cases j <;> simp [sQ, tMatH, Matrix.mul_apply, Fin.sum_univ_two]` (`AtkinLehnerLocal.lean:127–131`).

- **Mathlib/project lemmas needed**: as L7
- **Sources**: `decomposition.md` L-b.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L14] `tMatHInv_zero_mul_sQ_neg`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem tMatHInv_zero_mul_sQ_neg (h : ℕ) (a : ℚ_[p]) :
    tMatHInv p h 0 * sQ p (-a) = tMatHInv p h a := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`ext i j; fin_cases i <;> fin_cases j <;> simp [sQ, tMatHInv, Matrix.mul_apply, Fin.sum_univ_two] <;> ring` (`AtkinLehnerLocal.lean:132–138`): the `(0,1)`-entry is `(p^h)⁻¹ * (-a) = -(a / p^h)` (`div_eq_mul_inv`).

- **Mathlib/project lemmas needed**: as L7, `div_eq_mul_inv`
- **Sources**: `decomposition.md` L-b.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L15] `tMatHInv_zero_mul_sQ_mul_tMatH_zero`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The translation `sQ b` in the disc-`0` coordinate is `(1, b/p^h; 0, 1)`. -/
theorem tMatHInv_zero_mul_sQ_mul_tMatH_zero (h : ℕ) (b : ℚ_[p]) :
    tMatHInv p h 0 * sQ p b * tMatH p h 0 = !![1, b / (p : ℚ_[p]) ^ h; 0, 1] := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`ext i j; fin_cases i <;> fin_cases j <;> simp [sQ, tMatH, tMatHInv, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp` (`AtkinLehnerLocal.lean:139–146`).

- **Mathlib/project lemmas needed**: as L7
- **Sources**: `decomposition.md` L-b.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-L5] Cleanup `PhD/LWX/AtkinLehnerLocalH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: L13, L14, L15
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerLocalH` and `lake exe runLinter PhD.LWX.AtkinLehnerLocalH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerLocalH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L16] `discConjMat_wQH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `t₀⁻¹ wQH t₀ = (0 1; −p^{h+1} 0)` is the level-`p^{h+1}` Atkin–Lehner element of
`AtkinLehner.lean`. -/
theorem discConjMat_wQH (h : ℕ) :
    tMatHInv p h 0 * wQH p h * tMatH p h 0 = atkinLehner p (h + 1) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`ext i j; fin_cases i <;> fin_cases j <;> simp [wQH, tMatH, tMatHInv, atkinLehner, Matrix.mul_apply, Fin.sum_univ_two, hp0] <;> field_simp <;> ring` (`AtkinLehnerLocal.lean:147–156`); `−p·p^h = −p^(h+1)` (`pow_succ`).

- **Mathlib/project lemmas needed**: as L7, `pow_succ`, `atkinLehner` (`AtkinLehner.lean:62`)
- **Sources**: `decomposition.md` L-b.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L17] `wQH_mul_vQ_mul_wQHinv`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The `U'_p`-representative: `wQH · vQ b · wQH⁻¹ = (1 −bp^h; 0 p)`. -/
theorem wQH_mul_vQ_mul_wQHinv (h : ℕ) (b : ℚ_[p]) :
    wQH p h * vQ p b * wQHinv p h = !![1, -(b * (p : ℚ_[p]) ^ h); 0, (p : ℚ_[p])] := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`ext i j; fin_cases i <;> fin_cases j <;> simp [wQH, vQ, wQHinv, Matrix.mul_apply, Fin.sum_univ_two, hp0] <;> field_simp` (`AtkinLehnerLocal.lean:157–164`).

- **Mathlib/project lemmas needed**: as L7
- **Sources**: `decomposition.md` L-c.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L18] `upAdjRepH_mul_vQ`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The key factorisation at level `h`**:
`(1 −bp^h; 0 p) · vQ c = ℓQH b c · (p • sQ (−b p^{h−1}))`. -/
theorem upAdjRepH_mul_vQ (h : ℕ) (b c : ℚ_[p]) :
    !![1, -(b * (p : ℚ_[p]) ^ h); 0, (p : ℚ_[p])] * vQ p c
      = ℓQH p h b c * ((p : ℚ_[p]) • sQ p (-(b * (p : ℚ_[p]) ^ h / p))) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`ext i j; fin_cases i <;> fin_cases j <;> simp [vQ, ℓQH, sQ, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring` (`AtkinLehnerLocal.lean:165–173`); verified entry-wise in `decomposition.md` L-c (unconditional in `h`).

- **Mathlib/project lemmas needed**: as L7
- **Sources**: `decomposition.md` L-c.
- **Generality decision**: Every `h` (design decision 4).
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-L6] Cleanup `PhD/LWX/AtkinLehnerLocalH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: L16, L17, L18
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerLocalH` and `lake exe runLinter PhD.LWX.AtkinLehnerLocalH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerLocalH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L19] `wQH_mul_vQ_mul_wQHinv_mul_vQ`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: L17, L18
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The factorisation with the Atkin–Lehner conjugate spelled out. -/
theorem wQH_mul_vQ_mul_wQHinv_mul_vQ (h : ℕ) (b c : ℚ_[p]) :
    wQH p h * vQ p b * wQHinv p h * vQ p c
      = ℓQH p h b c * ((p : ℚ_[p]) • sQ p (-(b * (p : ℚ_[p]) ^ h / p))) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [wQH_mul_vQ_mul_wQHinv, upAdjRepH_mul_vQ]`.

- **Mathlib/project lemmas needed**: —
- **Sources**: `AtkinLehnerLocal.lean:174–178`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L20] `ℓQHinv_mul_wQH_mul_vQ_mul_wQHinv_mul_vQ`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: L10, L19
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The factorisation solved for the Iwahori element. -/
theorem ℓQHinv_mul_wQH_mul_vQ_mul_wQHinv_mul_vQ (h : ℕ) (b c : ℚ_[p]) :
    ℓQHinv p h b c * (wQH p h * vQ p b * wQHinv p h * vQ p c)
      = (p : ℚ_[p]) • sQ p (-(b * (p : ℚ_[p]) ^ h / p)) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [wQH_mul_vQ_mul_wQHinv_mul_vQ, ← mul_assoc, ℓQHinv_mul_ℓQH, one_mul]`.

- **Mathlib/project lemmas needed**: —
- **Sources**: `AtkinLehnerLocal.lean:179–183`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L21] `wQH_mul_mul_wQHinv`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- Conjugation by the level-`h` Atkin–Lehner element:
`wQH · g · wQH⁻¹ = (d, −c p^h/p; −b p/p^h, a)`. -/
theorem wQH_mul_mul_wQHinv (h : ℕ) (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) :
    wQH p h * g * wQHinv p h
      = !![g 1 1, -(g 1 0 * (p : ℚ_[p]) ^ h / p);
          -(g 0 1 * (p : ℚ_[p]) / (p : ℚ_[p]) ^ h), g 0 0] := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`ext i j; fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two] <;> simp [wQH, wQHinv] <;> (try field_simp)` (`AtkinLehnerLocal.lean:184–191`); entries `(d, −c p^h/p; −b p/p^h, a)`.

- **Mathlib/project lemmas needed**: as L7
- **Sources**: `decomposition.md` L-c (derivation in `plan.md`).
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-L7] Cleanup `PhD/LWX/AtkinLehnerLocalH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: L19, L20, L21
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerLocalH` and `lake exe runLinter PhD.LWX.AtkinLehnerLocalH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerLocalH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L22] `wQHinv_mul_mul_wQH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- Conjugation by the inverse: the same matrix (`wQH² = −p^{h+1}` is central). -/
theorem wQHinv_mul_mul_wQH (h : ℕ) (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) :
    wQHinv p h * g * wQH p h
      = !![g 1 1, -(g 1 0 * (p : ℚ_[p]) ^ h / p);
          -(g 0 1 * (p : ℚ_[p]) / (p : ℚ_[p]) ^ h), g 0 0] := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As L21 (`AtkinLehnerLocal.lean:192–199`).

- **Mathlib/project lemmas needed**: as L7
- **Sources**: `decomposition.md` L-c.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L23] `ℓQH_mem_Iw`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: L5
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `ℓQH b c ∈ Iw_p` for `b, c` integral and `h ≥ 1`. -/
theorem ℓQH_mem_Iw {h : ℕ} (hh : 0 < h) {b c : ℚ_[p]} (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    ℓQH p h b c ∈ Iw p 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `ℓQ_mem_Iw` (`AtkinLehnerLocal.lean:227–251`): `mem_Iw_iff`; entries: `‖1 ± bcp^h‖ ≤ 1` (ultrametric, `‖p^h‖ ≤ 1`), `‖b²c(p^h p^h/p)‖ = ‖b‖²‖c‖ p^{−(2h−1)} ≤ 1` (needs `2h ≥ 1`, `hh`; `norm_div`, `norm_pow`, `Padic.norm_p`, `pow_le_one₀`), `‖cp‖ ≤ p⁻¹`; `‖det‖ = 1` from L5.

- **Mathlib/project lemmas needed**: `mem_Iw_iff`, `Padic.norm_p`, `norm_div`, `norm_pow`, `IsUltrametricDist.norm_add_le_max`, `pow_le_one₀`
- **Sources**: `decomposition.md` L-d; `AtkinLehnerLocal.lean:227–251`.
- **Generality decision**: `hh` necessary.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L24] `ℓQHinv_mem_Iw`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `ℓQHinv b c ∈ Iw_p` for `b, c` integral and `h ≥ 1`. -/
theorem ℓQHinv_mem_Iw {h : ℕ} (hh : 0 < h) {b c : ℚ_[p]} (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    ℓQHinv p h b c ∈ Iw p 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As L23 (`AtkinLehnerLocal.lean:252–279`), `det ℓQHinv = 1` computed inline (`Matrix.det_fin_two_of; field_simp; ring`).

- **Mathlib/project lemmas needed**: as L23
- **Sources**: `decomposition.md` L-d.
- **Generality decision**: `hh` necessary.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-L8] Cleanup `PhD/LWX/AtkinLehnerLocalH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: L22, L23, L24
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerLocalH` and `lake exe runLinter PhD.LWX.AtkinLehnerLocalH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerLocalH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L25] `wQH_conj_mem_Iw`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: L21, L22
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **`wQH` normalises the disc-`0` part of `Iw_p` at level `h`**: for `g ∈ Iw_p` with
`p^h ∣ b`, both `wQH g wQH⁻¹` and `wQH⁻¹ g wQH` lie in `Iw_p` with `p^h ∣ b`. -/
theorem wQH_conj_mem_Iw (h : ℕ) {g : Matrix (Fin 2) (Fin 2) ℚ_[p]} (hg : g ∈ Iw p 1)
    (hb : ‖g 0 1‖ ≤ (p : ℝ)⁻¹ ^ h) :
    (wQH p h * g * wQHinv p h ∈ Iw p 1 ∧ ‖(wQH p h * g * wQHinv p h) 0 1‖ ≤ (p : ℝ)⁻¹ ^ h)
      ∧ (wQHinv p h * g * wQH p h ∈ Iw p 1
        ∧ ‖(wQHinv p h * g * wQH p h) 0 1‖ ≤ (p : ℝ)⁻¹ ^ h) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `wQ_conj_mem_Iw` (`AtkinLehnerLocal.lean:280–296`): `obtain ⟨h1, h2, h3⟩ := hg`; `hswap` for the matrix `(d, −c p^h/p; −b p/p^h, a)`: entries `≤ 1` (`‖c p^h/p‖ = ‖c‖ p^{−h} p ≤ p⁻¹ p^{−h} p = p^{−h} ≤ 1`; `‖b p/p^h‖ ≤ p^{−h} p⁻¹ p^h = p⁻¹ ≤ 1`), `(1,0)`-entry `≤ p⁻¹`, `det` equal to `g.det` (`Matrix.det_fin_two_of`, `field_simp`, `ring`), `(0,1)`-entry `≤ p⁻¹^h`; `rw [wQH_mul_mul_wQHinv, wQHinv_mul_mul_wQH]; exact ⟨hswap, hswap⟩`.

- **Mathlib/project lemmas needed**: `mem_Iw_iff`, `norm_div`, `norm_pow`, `Padic.norm_p`, `Matrix.det_fin_two_of`
- **Sources**: `decomposition.md` L-d; `AtkinLehnerLocal.lean:280–296`.
- **Generality decision**: Every `h` (no `hh`).
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L26] `discImage_zero_of_norm_apply_zero_one_le_pow`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **A matrix with `p^h ∣ b` fixes disc `0`** (`discImage h δ 0 = (b/d) mod p^h`). -/
theorem discImage_zero_of_norm_apply_zero_one_le_pow (h : ℕ) (δ : M1 p)
    (hb : ‖(δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1‖ ≤ (p : ℝ)⁻¹ ^ h) : discImage h δ 0 = 0 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `discImage_zero_of_norm_apply_zero_one_le` (`AtkinLehnerLocal.lean:323–332`) with `PadicInt.ker_toZModPow h` / `PadicInt.norm_le_pow_iff_mem_span_pow` in place of the `p ∣` facts: `discImage h δ 0 = toZModPow h (mobius(δ)(0)) = toZModPow h (b/d)`; `‖b/d‖ = ‖b‖ ≤ p⁻¹^h` (`d` a unit: `PadicInt.norm_units`, `Ring.inverse_unit`, `M1.coe_toLocalMat_b`, `LocalMat.mobiusFun`).

- **Mathlib/project lemmas needed**: `PadicInt.ker_toZModPow`, `PadicInt.norm_le_pow_iff_mem_span_pow`, `RingHom.mem_ker`, `LocalMat.mobiusFun`, `M1.coe_toLocalMat_b`, `PadicInt.norm_units`
- **Sources**: `decomposition.md` L-e; `AtkinLehnerLocal.lean:323–332`.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L27] `discConjMat_eq_tMatHInv_mul_mul_tMatH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The disc conjugate is `t_{a'}⁻¹ δ t_a`** at level `h` (`a' = discImage h δ a`). -/
theorem discConjMat_eq_tMatHInv_mul_mul_tMatH (h : ℕ) (δ : M1 p) (a : ZMod (p ^ h)) :
    discConjMat h δ a
      = tMatHInv p h (((discImage h δ a).val : ℕ) : ℚ_[p]) * (δ : Matrix (Fin 2) (Fin 2) ℚ_[p])
          * tMatH p h ((a.val : ℕ) : ℚ_[p]) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `discConjMat_eq_tMatInv_mul_mul_tMat` (`AtkinLehnerLocal.lean:333–343`): `ext i j; fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two] <;> simp [discConjMat, tMatH, tMatHInv] <;> (try field_simp) <;> (try ring)` against `DiscModel.lean:172–178`'s entries.

- **Mathlib/project lemmas needed**: as L7, `discConjMat` (unfold)
- **Sources**: `decomposition.md` L-e.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-L9] Cleanup `PhD/LWX/AtkinLehnerLocalH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: L25, L26, L27
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerLocalH` and `lake exe runLinter PhD.LWX.AtkinLehnerLocalH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerLocalH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L28] `discConjMat_zero_of_discImage_zero_prime_pow`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: L27
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- At a matrix fixing disc `0`, the disc-`0` conjugate is `t₀⁻¹ δ t₀`. -/
theorem discConjMat_zero_of_discImage_zero_prime_pow (h : ℕ) (δ : M1 p)
    (hδ : discImage h δ 0 = 0) :
    discConjMat h δ 0 = tMatHInv p h 0 * (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) * tMatH p h 0 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [discConjMat_eq_tMatHInv_mul_mul_tMatH, hδ]; simp` (`ZMod.val_zero`, `Nat.cast_zero`) (`AtkinLehnerLocal.lean:344–349`).

- **Mathlib/project lemmas needed**: `ZMod.val_zero`
- **Sources**: `decomposition.md` L-e.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L29] `conj_sQ_eq_tMatH_mul_discConjMat`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: L27
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `s_{−a'} δ s_a = t₀ · discConjMat δ a · t₀⁻¹` at level `h`. -/
theorem conj_sQ_eq_tMatH_mul_discConjMat (h : ℕ) (δ : M1 p) (a : ZMod (p ^ h)) :
    sQ p (-(((discImage h δ a).val : ℕ) : ℚ_[p])) * (δ : Matrix (Fin 2) (Fin 2) ℚ_[p])
        * sQ p ((a.val : ℕ) : ℚ_[p])
      = tMatH p h 0 * discConjMat h δ a * tMatHInv p h 0 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `conj_sQ_eq_tMat_mul_discConjMat` (`AtkinLehnerLocal.lean:350–361`): `rw [discConjMat_eq_tMatHInv_mul_mul_tMatH]`; then `ext` + `simp [tMatH, tMatHInv, sQ, hp0]` + `field_simp` (with `(p^h)⁻¹ p^h = 1`).

- **Mathlib/project lemmas needed**: as L7
- **Sources**: `decomposition.md` L-e.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L30] `discImage_vQ_zero_prime_pow`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: L26
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `vQ c` fixes disc `0` at every level. -/
theorem discImage_vQ_zero_prime_pow (h : ℕ) {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) :
    discImage h (⟨vQ p c, vQ_mem_M1 hc⟩ : M1 p) 0 = 0 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`discImage_zero_of_norm_apply_zero_one_le_pow h _ (by simp [vQ])` (`(vQ p c) 0 1 = 0`) (`AtkinLehnerLocal.lean:362–366`).

- **Mathlib/project lemmas needed**: —
- **Sources**: `decomposition.md` L-e.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-L10] Cleanup `PhD/LWX/AtkinLehnerLocalH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: L28, L29, L30
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerLocalH` and `lake exe runLinter PhD.LWX.AtkinLehnerLocalH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerLocalH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L31] `discImage_ℓQH_zero`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: L23, L26
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `ℓQH b c` fixes disc `0` (its `b`-entry is divisible by `p^{2h−1}`, hence by `p^h`). -/
theorem discImage_ℓQH_zero {h : ℕ} (hh : 0 < h) {b c : ℚ_[p]} (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    discImage h (⟨ℓQH p h b c, Iw_one_le_M1 (ℓQH_mem_Iw hh hb hc)⟩ : M1 p) 0 = 0 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`discImage_zero_of_norm_apply_zero_one_le_pow h _ ?_` with `‖-(b²c(p^h p^h/p))‖ ≤ p⁻¹^h`: `norm_neg`, `norm_mul`, `norm_div`, `norm_pow`, `Padic.norm_p`, `‖b‖,‖c‖ ≤ 1`, `p^{−(2h−1)} ≤ p^{−h}` (`hh`) (`AtkinLehnerLocal.lean:367–376`).

- **Mathlib/project lemmas needed**: as L23
- **Sources**: `decomposition.md` L-e.
- **Generality decision**: `hh` necessary.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L32] `discImage_ℓQHinv_zero`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: L24, L26
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `ℓQHinv b c` fixes disc `0`. -/
theorem discImage_ℓQHinv_zero {h : ℕ} (hh : 0 < h) {b c : ℚ_[p]} (hb : ‖b‖ ≤ 1)
    (hc : ‖c‖ ≤ 1) :
    discImage h (⟨ℓQHinv p h b c, Iw_one_le_M1 (ℓQHinv_mem_Iw hh hb hc)⟩ : M1 p) 0 = 0 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As L31 (`AtkinLehnerLocal.lean:377–386`).

- **Mathlib/project lemmas needed**: as L23
- **Sources**: `decomposition.md` L-e.
- **Generality decision**: `hh` necessary.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L33] `discConj_ℓQH_zero_one_one`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: L28, L31
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The `d`-entry of the disc-`0` conjugate of `ℓQH b c` is `1 + bcp^h`. -/
theorem discConj_ℓQH_zero_one_one {h : ℕ} (hh : 0 < h) {b c : ℚ_[p]} (hb : ‖b‖ ≤ 1)
    (hc : ‖c‖ ≤ 1) :
    (discConj h (⟨ℓQH p h b c, Iw_one_le_M1 (ℓQH_mem_Iw hh hb hc)⟩ : M1 p) 0 :
      Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 = 1 + b * c * (p : ℚ_[p]) ^ h := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [coe_discConj, discConjMat_zero_of_discImage_zero_prime_pow h _ (discImage_ℓQH_zero hh hb hc)]; simp [tMatH, tMatHInv, ℓQH, Matrix.mul_apply, Fin.sum_univ_two]` (the `(1,1)`-entry of `t₀⁻¹ ℓ t₀` is `ℓ 1 1`) (`AtkinLehnerLocal.lean:387–392`).

- **Mathlib/project lemmas needed**: `coe_discConj`
- **Sources**: `decomposition.md` L-e.
- **Generality decision**: `hh`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-L11] Cleanup `PhD/LWX/AtkinLehnerLocalH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: L31, L32, L33
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerLocalH` and `lake exe runLinter PhD.LWX.AtkinLehnerLocalH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerLocalH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L34] `discConj_ℓQHinv_zero_one_one`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: L28, L32
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The `d`-entry of the disc-`0` conjugate of `ℓQHinv b c` is `1 − bcp^h`. -/
theorem discConj_ℓQHinv_zero_one_one {h : ℕ} (hh : 0 < h) {b c : ℚ_[p]} (hb : ‖b‖ ≤ 1)
    (hc : ‖c‖ ≤ 1) :
    (discConj h (⟨ℓQHinv p h b c, Iw_one_le_M1 (ℓQHinv_mem_Iw hh hb hc)⟩ : M1 p) 0 :
      Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 = 1 - b * c * (p : ℚ_[p]) ^ h := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As L33 with L32 (`AtkinLehnerLocal.lean:393–398`).

- **Mathlib/project lemmas needed**: `coe_discConj`
- **Sources**: `decomposition.md` L-e.
- **Generality decision**: `hh`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L35] `discImage_sQ_zero_prime_pow`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The translation `sQ b` moves disc `0` to disc `b mod p^h`. -/
theorem discImage_sQ_zero_prime_pow (h : ℕ) (b : ℕ) :
    discImage h (⟨sQ p b, Iw_one_le_M1 (sQ_mem_Iw (by
      exact IsUltrametricDist.norm_natCast_le_one ℚ_[p] b))⟩ : M1 p) 0 = (b : ZMod (p ^ h)) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `discImage_sQ_zero` (`AtkinLehnerLocal.lean:399–415`): `discImage h ⟨sQ b, _⟩ 0 = toZModPow h (mobius (sQ b) 0) = toZModPow h ((b : ℤ_[p]) * 1) = (b : ZMod (p^h))` (`M1.coe_toLocalMat_b`, `M1.coe_toLocalMat_d` `= 1`, `Ring.inverse_one`, `map_natCast`).

- **Mathlib/project lemmas needed**: `M1.coe_toLocalMat_b`, `M1.coe_toLocalMat_d`, `Ring.inverse_one`, `map_natCast`
- **Sources**: `decomposition.md` L-e.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [L36] `discConj_sQ_zero_prime_pow`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: L27, L35
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The translation `sQ b`, `b < p^h`, has trivial disc-`0` conjugate. -/
theorem discConj_sQ_zero_prime_pow (h : ℕ) {b : ℕ} (hb : b < p ^ h) :
    discConj h (⟨sQ p b, Iw_one_le_M1 (sQ_mem_Iw (by
      exact IsUltrametricDist.norm_natCast_le_one ℚ_[p] b))⟩ : M1 p) 0 = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `discConj_sQ_zero` (`AtkinLehnerLocal.lean:416–427`): `Subtype.ext`; `discConjMat h ⟨sQ b,_⟩ 0 = t_{b'}⁻¹ (sQ b) t₀` with `b' = discImage … 0 = b` (L35), `(b : ZMod (p^h)).val = b` (`ZMod.val_natCast`, `Nat.mod_eq_of_lt hb`), so `= (1/p^h, −b/p^h; 0, 1)(1 b; 0 1)(p^h 0; 0 1) = 1` (`ext`, `simp`, `field_simp`).

- **Mathlib/project lemmas needed**: `ZMod.val_natCast`, `Nat.mod_eq_of_lt`, `Subtype.ext`
- **Sources**: `decomposition.md` L-e.
- **Generality decision**: `hb : b < p ^ h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerLocalH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-L-FINAL] Cleanup `PhD/LWX/AtkinLehnerLocalH.lean` (final)
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocalH.lean
- **Depends on**: L36 (and every earlier ticket of the file)
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerLocalH` and `lake exe runLinter PhD.LWX.AtkinLehnerLocalH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerLocalH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W1] `coe_wGLH_inv`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem coe_wGLH_inv (h : ℕ) :
    ((wGLH p h)⁻¹ : GL (Fin 2) ℚ_[p]) = (wQHinv p h : Matrix _ _ _) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `coe_wGL_inv` (`AtkinLehnerMap.lean:84–87`): `Units.inv_eq_of_mul_eq_one_right`-style: the inverse of `mkOfDetNeZero A _` is characterised by `A * B = 1`; use `wQH_mul_wQHinv` (`Matrix.inv_eq_right_inv`, `Units.val_inv_eq_inv_val`, `Matrix.coe_units_inv`).

- **Mathlib/project lemmas needed**: `Matrix.coe_units_inv`, `Matrix.inv_eq_right_inv`, `wQH_mul_wQHinv`
- **Sources**: `decomposition.md` W-a; `AtkinLehnerMap.lean:84–87`.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W2] `coe_ℓGLH_inv`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem coe_ℓGLH_inv (h : ℕ) (b c : ℚ_[p]) :
    ((ℓGLH p h b c)⁻¹ : GL (Fin 2) ℚ_[p]) = (ℓQHinv p h b c : Matrix _ _ _) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As W1 with `ℓQH_mul_ℓQHinv` (`AtkinLehnerMap.lean:88–96`).

- **Mathlib/project lemmas needed**: as W1
- **Sources**: `decomposition.md` W-a.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W3] `wGLH_one`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: L1
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem wGLH_one : wGLH p 1 = wGL p := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`Units.ext wQH_one` (both coercions are `rfl`: `coe_wGLH`, `coe_wGL`).

- **Mathlib/project lemmas needed**: `Units.ext`
- **Sources**: `decomposition.md` W-a.
- **Generality decision**: Bridge.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-W1] Cleanup `PhD/LWX/AtkinLehnerMapH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W1, W2, W3
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMapH` and `lake exe runLinter PhD.LWX.AtkinLehnerMapH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerMapH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W4] `wGLH_mul_vGL_mul_wGLH_inv_mul_vGL`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W1, L19
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The key factorisation in `GL₂(ℚ_p)` at level `h`**:
`w_h v_b w_h⁻¹ v_c = ℓ_{b,c} · (p·1) · s_{−b p^{h−1}}`. -/
theorem wGLH_mul_vGL_mul_wGLH_inv_mul_vGL (h : ℕ) (b c : ℚ_[p]) :
    wGLH p h * vGL p b * (wGLH p h)⁻¹ * vGL p c
      = ℓGLH p h b c * (pGL p * sGL p (-(b * (p : ℚ_[p]) ^ h / p))) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `wGL_mul_vGL_mul_wGL_inv_mul_vGL` (`AtkinLehnerMap.lean:110–118`): `Units.ext`; `simp only [Units.val_mul, coe_wGLH, coe_vGL, coe_wGLH_inv, coe_ℓGLH, coe_pGL?, coe_sGL]`; `wQH_mul_vQ_mul_wQHinv_mul_vQ`; `p • sQ(−β) = (p•1) * sQ(−β)` (`smul_eq_mul`/`Matrix.smul_one_mul`? — as at level `1`).

- **Mathlib/project lemmas needed**: `Units.ext`, `Units.val_mul`, `wQH_mul_vQ_mul_wQHinv_mul_vQ`
- **Sources**: `decomposition.md` W-a; `AtkinLehnerMap.lean:110–118`.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W5] `atkinLehnerKH_mul_atkinLehnerKHinv`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [IsUltrametricDist K] [CompleteSpace K] in
theorem atkinLehnerKH_mul_atkinLehnerKHinv (ψ : ℚ_[p] →+* K) (h : ℕ) :
    atkinLehnerKH ψ h * atkinLehnerKHinv ψ h = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`ext i j; fin_cases i <;> fin_cases j <;> simp [atkinLehnerKH, atkinLehnerKHinv, atkinLehner, Matrix.mul_apply, Fin.sum_univ_two, map_pow]` with `(ψ p)^(h+1) ≠ 0` (`AtkinLehnerMap.lean:127–133`).

- **Mathlib/project lemmas needed**: `map_pow`, `map_neg`, `mul_inv_cancel₀`
- **Sources**: `decomposition.md` W-b.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W6] `atkinLehnerKHinv_mul_atkinLehnerKH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [IsUltrametricDist K] [CompleteSpace K] in
theorem atkinLehnerKHinv_mul_atkinLehnerKH (ψ : ℚ_[p] →+* K) (h : ℕ) :
    atkinLehnerKHinv ψ h * atkinLehnerKH ψ h = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As W5 (`AtkinLehnerMap.lean:134–140`).

- **Mathlib/project lemmas needed**: as W5
- **Sources**: `decomposition.md` W-b.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-W2] Cleanup `PhD/LWX/AtkinLehnerMapH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W4, W5, W6
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMapH` and `lake exe runLinter PhD.LWX.AtkinLehnerMapH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerMapH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W7] `atkinLehnerKH_eq`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: L16
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `w_{2,h} = t₀⁻¹ w_h t₀` in `K`. -/
theorem atkinLehnerKH_eq (ψ : ℚ_[p] →+* K) (h : ℕ) :
    atkinLehnerKH ψ h = RingHom.mapMatrix ψ (tMatHInv p h 0 * wQH p h * tMatH p h 0) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [atkinLehnerKH, ← discConjMat_wQH]` (`AtkinLehnerMap.lean:261–267`).

- **Mathlib/project lemmas needed**: —
- **Sources**: `decomposition.md` W-b.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W8] `atkinLehnerKHinv_eq`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [IsUltrametricDist K] [CompleteSpace K] in
theorem atkinLehnerKHinv_eq (ψ : ℚ_[p] →+* K) (h : ℕ) :
    atkinLehnerKHinv ψ h
      = RingHom.mapMatrix ψ (tMatHInv p h 0 * wQHinv p h * tMatH p h 0) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Compute `tMatHInv 0 * wQHinv * tMatH 0 = (0, −1/p^(h+1); 1, 0)` (`ext; simp [...]; field_simp`), then `ext i j; fin_cases i <;> fin_cases j <;> simp [atkinLehnerKHinv, RingHom.mapMatrix_apply, map_pow]` (`AtkinLehnerMap.lean:268–278`).

- **Mathlib/project lemmas needed**: `RingHom.mapMatrix_apply`, `map_inv₀`, `map_pow`
- **Sources**: `decomposition.md` W-b.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W9] `AtkinLehnerData.toH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W3
- **Parallel**: yes (within the dependency order)
- **Type**: definition (two Prop fields)

**Statement** (verbatim from the skeleton; protected):
```lean
/-- Level `1` is the case `h = 1` (`wGLH_one`). -/
def _root_.LWX.AtkinLehnerData.toH (D₁ : AtkinLehnerData θG ψ U Γ nebK) :
    AtkinLehnerDataH θG ψ U 1 Γ nebK where
  ιp := D₁.ιp
  theta_ιp := D₁.theta_ιp
  ιp_mem_U := D₁.ιp_mem_U
  central := D₁.central
  χ := D₁.χ
  χ_Γ := D₁.χ_Γ
  χ_U := D₁.χ_U
  χ_vGL := D₁.χ_vGL
  χ_wGLH := by sorry
  w_conj_mem_U := by sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Two `sorry` fields: `χ_wGLH := by rw [wGLH_one]; exact D₁.χ_wGL`; `w_conj_mem_U := fun u hu hb => by rw [wGLH_one]; exact D₁.w_conj_mem_U u hu (by simpa using hb)` (`pow_one`).

- **Mathlib/project lemmas needed**: `wGLH_one`, `pow_one`
- **Sources**: `decomposition.md` W-c.
- **Generality decision**: Bridge.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-W3] Cleanup `PhD/LWX/AtkinLehnerMapH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W7, W8, W9
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMapH` and `lake exe runLinter PhD.LWX.AtkinLehnerMapH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerMapH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W10] `discShiftH_mem_U`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem discShiftH_mem_U (u : U) (a : ZMod (p ^ h)) : discShiftH θG ψ U hU h D u a ∈ U := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`mul_mem (mul_mem (D.ιp_mem_U _ (sQ_mem_Iw ?_)) u.2) (D.ιp_mem_U _ (sQ_mem_Iw ?_))` with `norm_neg`, `IsUltrametricDist.norm_natCast_le_one` (`AtkinLehnerMap.lean:202–206`).

- **Mathlib/project lemmas needed**: `sQ_mem_Iw`, `IsUltrametricDist.norm_natCast_le_one`
- **Sources**: `decomposition.md` W-d.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W11] `theta_discShiftH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem theta_discShiftH (u : U) (a : ZMod (p ^ h)) :
    θG (discShiftH θG ψ U hU h D u a)
      = sQ p (-(((discImage h ⟨θG u, hU u.2⟩ a).val : ℕ) : ℚ_[p])) * θG u
        * sQ p ((a.val : ℕ) : ℚ_[p]) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [discShiftH, map_mul, map_mul, D.theta_ιp, D.theta_ιp, coe_sGL, coe_sGL]` (`AtkinLehnerMap.lean:208–214`).

- **Mathlib/project lemmas needed**: `coe_sGL`
- **Sources**: `decomposition.md` W-d.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W12] `mul_ιp_sGL_eqH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `u s_a = s_{a'} u'`. -/
theorem mul_ιp_sGL_eqH (u : U) (a : ZMod (p ^ h)) :
    (u : G) * D.ιp (sGL p ((a.val : ℕ) : ℚ_[p]))
      = D.ιp (sGL p (((discImage h ⟨θG u, hU u.2⟩ a).val : ℕ) : ℚ_[p]))
        * discShiftH θG ψ U hU h D u a := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [discShiftH, ← mul_assoc, ← mul_assoc, ← map_mul, sGL_mul, add_neg_cancel, sGL_zero, map_one, one_mul]` (`AtkinLehnerMap.lean:216–222`).

- **Mathlib/project lemmas needed**: `sGL_mul`, `sGL_zero`
- **Sources**: `decomposition.md` W-d.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-W4] Cleanup `PhD/LWX/AtkinLehnerMapH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W10, W11, W12
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMapH` and `lake exe runLinter PhD.LWX.AtkinLehnerMapH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerMapH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W13] `norm_theta_discShiftH_zero_one_le`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W11, L29
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The disc-shifted element lies in the level-`p^{h+1}` part: `p^h ∣ b(θ u')`
(`conj_sQ_eq_tMatH_mul_discConjMat`, `discConjMat_mem_Mh`). -/
theorem norm_theta_discShiftH_zero_one_le (u : U) (a : ZMod (p ^ h)) :
    ‖(θG (discShiftH θG ψ U hU h D u a)) 0 1‖ ≤ (p : ℝ)⁻¹ ^ h := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `norm_theta_discShift_zero_one_le` (`AtkinLehnerMap.lean:224–237`): `hc := conj_sQ_eq_tMatH_mul_discConjMat h _ a`; `hM := discConjMat_mem_Mh h _ a`; `h01 : (tMatH 0 * M * tMatHInv 0) 0 1 = p^h * M 0 1` (`simp only [Matrix.mul_apply, Fin.sum_univ_two]; simp [tMatH, tMatHInv]`); `rw [theta_discShiftH, hc, h01, norm_mul, norm_pow, Padic.norm_p]`; `mul_le_of_le_one_right` with `(mem_Mh_iff.1 hM).1 0 1`.

- **Mathlib/project lemmas needed**: `conj_sQ_eq_tMatH_mul_discConjMat`, `discConjMat_mem_Mh`, `mem_Mh_iff`, `Padic.norm_p`
- **Sources**: `decomposition.md` W-d; `AtkinLehnerMap.lean:224–237`.
- **Generality decision**: Bound `p⁻¹^h` (feeds `w_conj_mem_U`).
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W14] `discImage_discShiftH_zero`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W13, L26
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem discImage_discShiftH_zero (u : U) (a : ZMod (p ^ h)) :
    discImage h (⟨θG (discShiftH θG ψ U hU h D u a),
      hU (discShiftH_mem_U θG ψ U hU h D u a)⟩ : M1 p) 0 = 0 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`discImage_zero_of_norm_apply_zero_one_le_pow h _ (norm_theta_discShiftH_zero_one_le θG ψ U hU h D u a)` (`AtkinLehnerMap.lean:239–244`).

- **Mathlib/project lemmas needed**: —
- **Sources**: `decomposition.md` W-d.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W15] `discConjMat_discShiftH_zero`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W11, W14, L12, L28, L29
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The disc-`0` conjugate of `u'` is the disc-`a` conjugate of `θ u`. -/
theorem discConjMat_discShiftH_zero (u : U) (a : ZMod (p ^ h)) :
    discConjMat h
        (⟨θG (discShiftH θG ψ U hU h D u a),
          hU (discShiftH_mem_U θG ψ U hU h D u a)⟩ : M1 p) 0
      = discConjMat h (⟨θG u, hU u.2⟩ : M1 p) a := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `discConjMat_discShift_zero` (`AtkinLehnerMap.lean:246–259`): `hc` as W13; `rw [discConjMat_zero_of_discImage_zero_prime_pow h _ (discImage_discShiftH_zero …)]`; `change tMatHInv p h 0 * θG (discShiftH …) * tMatH p h 0 = _`; `rw [theta_discShiftH, hc, ← mul_assoc, ← mul_assoc, tMatHInv_mul_tMatH, one_mul, mul_assoc, tMatHInv_mul_tMatH, mul_one]`.

- **Mathlib/project lemmas needed**: `tMatHInv_mul_tMatH`
- **Sources**: `decomposition.md` W-d.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-W5] Cleanup `PhD/LWX/AtkinLehnerMapH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W13, W14, W15
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMapH` and `lake exe runLinter PhD.LWX.AtkinLehnerMapH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerMapH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W16] `cSpace_ext_blockProjH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CharZero K] in
/-- Two functions on `ℤ/p^h × ℕ` agreeing on every disc are equal. -/
theorem cSpace_ext_blockProjH {f g : c(ZMod (p ^ h) × ℕ, K)}
    (hfg : ∀ a, cSpace.blockProj a f = cSpace.blockProj a g) : f = g := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `cSpace_ext_blockProj` (`AtkinLehnerMap.lean:280–284`): `DFunLike.ext _ _ fun x => ?_`; `congrArg (fun F => F x.2) (hfg x.1)`; `simpa [cSpace.blockProj_apply]`.

- **Mathlib/project lemmas needed**: `cSpace.blockProj_apply`, `DFunLike.ext`
- **Sources**: `decomposition.md` W-e.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W17] `nebK_one_of_cond_pow`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `nebK 1 = 1` (from the conductor hypothesis at level `h`). -/
theorem nebK_one_of_cond_pow
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) → nebK (ψ x) = 1) :
    nebK (ψ 1) = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`hcond 1 (by rw [sub_self, norm_zero]; positivity)` (`AtkinLehnerMap.lean:286–290`).

- **Mathlib/project lemmas needed**: `positivity`
- **Sources**: `decomposition.md` W-e.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W18] `nebK_mul_nebK_eq_nebK_detH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- **`nebK(a)·nebK(d) = nebK(det)`** on the level-`p^{h+1}` part of `Iw_p` (`ad = det + bc`
with `p^h ∣ b`, `p ∣ c`, so `ad/det ≡ 1 (mod p^{h+1})`). -/
theorem nebK_mul_nebK_eq_nebK_detH
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) → nebK (ψ x) = 1)
    {g : Matrix (Fin 2) (Fin 2) ℚ_[p]} (hg : g ∈ Iw p 1) (hb : ‖g 0 1‖ ≤ (p : ℝ)⁻¹ ^ h) :
    nebK (ψ (g 0 0)) * nebK (ψ (g 1 1)) = nebK (ψ g.det) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `nebK_mul_nebK_eq_nebK_det` (`AtkinLehnerMap.lean:292–320`) with `hen : ‖g 0 1 * g 1 0 / g.det‖ ≤ p⁻¹^(h+1)` (`hb` times `‖g 1 0‖ ≤ p⁻¹`, `pow_succ`), `hel : … < 1` (`pow_lt_one₀`), `h1e`, `hsplit`, and `hcond _ hen`.

- **Mathlib/project lemmas needed**: `norm_apply_zero_zero_of_mem_Iw`, `Iw_one_le_M1`, `Matrix.det_fin_two`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, `pow_succ`, `pow_lt_one₀`
- **Sources**: `decomposition.md` W-e; `AtkinLehnerMap.lean:292–320`.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-W6] Cleanup `PhD/LWX/AtkinLehnerMapH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W16, W17, W18
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMapH` and `lake exe runLinter PhD.LWX.AtkinLehnerMapH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerMapH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W19] `nebK_one_sub_eq_invH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `nebK(1 − x) = nebK(1 + x)⁻¹` for `‖x‖ ≤ p^{−h}`, `h ≥ 1` (`(1−x)(1+x) ≡ 1 (mod p^{h+1})`). -/
theorem nebK_one_sub_eq_invH (hh : 0 < h)
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) → nebK (ψ x) = 1)
    {x : ℚ_[p]} (hx : ‖x‖ ≤ (p : ℝ)⁻¹ ^ h) :
    nebK (ψ (1 - x)) = (nebK (ψ (1 + x)))⁻¹ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `nebK_one_sub_eq_inv` (`AtkinLehnerMap.lean:322–345`): `hxl : ‖x‖ < 1`; `hn1`, `hn2`; `hprod` with `hcond _ ?_` where `‖x^2‖ = ‖x‖^2 ≤ (p⁻¹^h)^2 = p⁻¹^(2h) ≤ p⁻¹^(h+1)` (`pow_le_pow_of_le_one`, `2h ≥ h+1` from `hh`); `eq_inv_of_mul_eq_one_left`.

- **Mathlib/project lemmas needed**: `pow_le_pow_left₀`, `pow_le_pow_of_le_one`, `eq_inv_of_mul_eq_one_left`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`
- **Sources**: `decomposition.md` W-e.
- **Generality decision**: `hh` necessary.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W20] `locPolyFormsH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: definition (submodule proofs)

**Statement** (verbatim from the skeleton; protected):
```lean
variable (p K) in
/-- The automorphic functions whose every value is locally polynomial of degree `≤ k` on the
`p^h` discs. -/
def locPolyFormsH : Submodule K (AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) where
  carrier := {φ | ∀ x, φ x ∈ locPolyDegSubmodule p K h k}
  add_mem' := by sorry
  zero_mem' := by sorry
  smul_mem' := by sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Three `sorry` fields: copy `locPolyForms` (`AtkinLehnerMap.lean:349–354`) — pointwise `(locPolyDegSubmodule p K h k).add_mem (hφ x) (hφ' x)`, `zero_mem`, `smul_mem` after `change`/`AutomorphicFunction.add_apply`-style unfolding.

- **Mathlib/project lemmas needed**: `Submodule.add_mem`, `Submodule.zero_mem`, `Submodule.smul_mem`
- **Sources**: `decomposition.md` W-f; `AtkinLehnerMap.lean:349–354`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W21] `discHeckeOperator_mem_classicalDiscFormsH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CharZero K] in
/-- `U_p` preserves the classical disc forms at a classical-shape weight. -/
theorem discHeckeOperator_mem_classicalDiscFormsH {u : K → K}
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    {η : G} (hη : η ∈ levelM1 (p := p) θG)
    (hfin : (((Quotient.mk'' : G → RightCosets U) '' (({η} : Set G) * (U : Set G))) :
      Set (RightCosets U)).Finite)
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ) :
    ((discHeckeOperator θG h ψ κ U hU hη hfin ⟨φ, hφ.1⟩ : DiscForms (Γ := Γ) θG h ψ κ U hU) :
        AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K))
      ∈ ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `discHeckeOperator_mem_classicalDiscForms` (`AtkinLehnerMap.lean:372–400`) with `1 → h`: `Fintype` from `hfin`, `heckeOperatorSlash_eq_finsetSum`, the sum-evaluation `map_sum`, `Submodule.sum_mem`, and `discSlash_mem_locPolyDegSubmodule_of_shape h ψ κ _ (fun a => hκ _) (hφ.2 _)`.

- **Mathlib/project lemmas needed**: `discSlash_mem_locPolyDegSubmodule_of_shape`, `Submodule.sum_mem`, `heckeOperatorSlash_eq_finsetSum`
- **Sources**: `decomposition.md` W-f; `AtkinLehnerMap.lean:372–400`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-W7] Cleanup `PhD/LWX/AtkinLehnerMapH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W19, W20, W21
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMapH` and `lake exe runLinter PhD.LWX.AtkinLehnerMapH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerMapH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W22] `discHeckeOperatorClH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W21
- **Parallel**: yes (within the dependency order)
- **Type**: definition (`map_add'`, `map_smul'`)

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **`U_p` on the classical disc forms at level `h`.** -/
def discHeckeOperatorClH {u : K → K}
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    {η : G} (hη : η ∈ levelM1 (p := p) θG)
    (hfin : (((Quotient.mk'' : G → RightCosets U) '' (({η} : Set G) * (U : Set G))) :
      Set (RightCosets U)).Finite) :
    ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ →ₗ[K]
      ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ where
  toFun φ := ⟨(discHeckeOperator θG h ψ κ U hU hη hfin ⟨φ.1, φ.2.1⟩ :
      DiscForms (Γ := Γ) θG h ψ κ U hU).1,
    discHeckeOperator_mem_classicalDiscFormsH θG ψ U hU h k κ hκ hη hfin φ.2⟩
  map_add' φ φ' := by sorry
  map_smul' r φ := by sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`map_add'`/`map_smul'` (`sorry` in the skeleton): `Subtype.ext`; `change (discHeckeOperator θG h ψ κ U hU hη hfin (⟨φ.1, φ.2.1⟩ + ⟨φ'.1, φ'.2.1⟩) : DiscForms …).1 = _`; `rw [map_add]; rfl` (resp. `map_smul`) (`AtkinLehnerMap.lean:402–428`).

- **Mathlib/project lemmas needed**: `map_add`, `map_smul`, `Subtype.ext`
- **Sources**: `decomposition.md` W-f.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W23] `apply_mul_of_theta_eq_oneH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CharZero K] in
/-- **A level element with trivial `p`-component acts trivially**: `φ(x u) = φ(x)` for `u ∈ U`,
`θ u = 1`. -/
theorem apply_mul_of_theta_eq_oneH {φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)}
    (hφ : φ ∈ DiscForms (Γ := Γ) θG h ψ κ U hU) (x : G) {u : G} (hu : u ∈ U) (hθ : θG u = 1) :
    φ (x * u) = φ x := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `apply_mul_of_theta_eq_one` (`AtkinLehnerMap.lean:430–440`): `(mem_discForms_iff θG h ψ κ U hU φ).1 hφ ⟨u, hu⟩ x`, then `discSlash h ψ κ ⟨1, _⟩ = id` (`discSlash_one` after `Subtype.ext hθ`).

- **Mathlib/project lemmas needed**: `mem_discForms_iff`, `discSlash_one`
- **Sources**: `decomposition.md` W-g.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W24] `blockProj_zero_apply_mul_mem_UH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CharZero K] in
/-- **Level-equivariance on disc `0`** at a level element fixing disc `0`, for a classical form
at a classical-shape weight. -/
theorem blockProj_zero_apply_mul_mem_UH {u : K → K}
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ) (x : G) (v : U)
    (hv0 : discImage h (⟨θG v, hU v.2⟩ : M1 p) 0 = 0) :
    cSpace.blockProj 0 (φ (x * v))
      = u (ψ ((discConj h (⟨θG v, hU v.2⟩ : M1 p) 0 : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1)) •
        symAct K k (RingHom.mapMatrix ψ (discConj h (⟨θG v, hU v.2⟩ : M1 p) 0 :
          Matrix (Fin 2) (Fin 2) ℚ_[p])) (cSpace.blockProj 0 (φ x)) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `blockProj_zero_apply_mul_mem_U` (`AtkinLehnerMap.lean:442–460`): `mem_discForms_iff`, `blockProj_discSlash h`, `hv0` to put the disc at `0`, `kappaSlash_eq_smul_symAct_of_shape κ _ (hκ _) (hf : blockProj 0 (φ x) ∈ polySubmodule K k)` (from `hφ.2 x 0`).

- **Mathlib/project lemmas needed**: `blockProj_discSlash`, `kappaSlash_eq_smul_symAct_of_shape`, `cSpace.blockProj_apply`
- **Sources**: `decomposition.md` W-g; `AtkinLehnerMap.lean:442–460`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-W8] Cleanup `PhD/LWX/AtkinLehnerMapH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W22, W23, W24
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMapH` and `lake exe runLinter PhD.LWX.AtkinLehnerMapH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerMapH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W25] `shapiro_blockProjH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: L35, L36
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CharZero K] in
/-- **Disc `a` of `φ(x)` is disc `0` of `φ(x·s_a)`** at level `h` (`discImage_sQ_zero_prime_pow`,
`discConj_sQ_zero_prime_pow`). -/
theorem shapiro_blockProjH {φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)}
    (hφ : φ ∈ DiscForms (Γ := Γ) θG h ψ κ U hU) (x : G) (a : ZMod (p ^ h)) :
    cSpace.blockProj a (φ x)
      = cSpace.blockProj 0 (φ (x * D.ιp (sGL p (a.val : ℚ_[p])))) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `shapiro_blockProj` (`AtkinLehnerMap.lean:462–484`): `haveI : NeZero (p ^ h)`; `(mem_discForms_iff …).1 hφ ⟨D.ιp (sGL p a.val), D.ιp_mem_U _ (sQ_mem_Iw _)⟩ x`; `blockProj_discSlash h`; the disc image `discImage h ⟨sQ a.val, _⟩ 0 = a` (`discImage_sQ_zero_prime_pow`, `ZMod.natCast_zmod_val`), the conjugate `= 1` (`discConj_sQ_zero_prime_pow (ZMod.val_lt a)`), `kappaSlash` at `1` is `id` (`AnalyticWeight.kappaSlash_one`?  as at level `1`).

- **Mathlib/project lemmas needed**: `discImage_sQ_zero_prime_pow`, `discConj_sQ_zero_prime_pow`, `ZMod.natCast_zmod_val`, `ZMod.val_lt`, `blockProj_discSlash`
- **Sources**: `decomposition.md` W-g; `AtkinLehnerMap.lean:462–484`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W26] `atkinLehnerFunH_blockProj`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CharZero K] in
theorem atkinLehnerFunH_blockProj (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) (x : G)
    (a : ZMod (p ^ h)) :
    cSpace.blockProj a (atkinLehnerFunH θG ψ U h k D φ x)
      = ((D.χ (x * D.ιp (sGL p (a.val : ℚ_[p]))) : Kˣ) : K)⁻¹ •
        symAct K k (atkinLehnerKH ψ h)
          (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (a.val : ℚ_[p])) * (D.ιp (wGLH p h))⁻¹))) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [atkinLehnerFunH, map_sum, Finset.sum_eq_single a]`; `cSpace.blockProj_blockIncl`, `if_pos rfl` / `if_neg`, `Finset.mem_univ` (`AtkinLehnerMap.lean:494–507`).

- **Mathlib/project lemmas needed**: `cSpace.blockProj_blockIncl`, `Finset.sum_eq_single`
- **Sources**: `decomposition.md` W-h.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W27] `atkinLehnerFunH_blockProj_zero`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W26
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CharZero K] in
/-- Disc `0` of `Wφ(x)`: `χ(x)⁻¹ · (disc 0 of φ(x w_h⁻¹)) ∣_k w_{2,h}`. -/
theorem atkinLehnerFunH_blockProj_zero (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K))
    (x : G) :
    cSpace.blockProj 0 (atkinLehnerFunH θG ψ U h k D φ x)
      = ((D.χ x : Kˣ) : K)⁻¹ •
        symAct K k (atkinLehnerKH ψ h) (cSpace.blockProj 0 (φ (x * (D.ιp (wGLH p h))⁻¹))) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [atkinLehnerFunH_blockProj]; simp [ZMod.val_zero, sGL_zero, map_one, mul_one]` (`AtkinLehnerMap.lean:509–516`).

- **Mathlib/project lemmas needed**: `sGL_zero`, `ZMod.val_zero`
- **Sources**: `decomposition.md` W-h.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-W9] Cleanup `PhD/LWX/AtkinLehnerMapH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W25, W26, W27
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMapH` and `lake exe runLinter PhD.LWX.AtkinLehnerMapH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerMapH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W28] `atkinLehnerFunH_left_invt`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CharZero K] in
/-- `Wφ` is left `Γ`-invariant. -/
theorem atkinLehnerFunH_left_invt (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K))
    {γ : G} (hγ : γ ∈ Γ) (x : G) :
    atkinLehnerFunH θG ψ U h k D φ (γ * x) = atkinLehnerFunH θG ψ U h k D φ x := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`simp only [atkinLehnerFunH, mul_assoc, AutomorphicFunction.left_invt' φ hγ, map_mul D.χ, D.χ_Γ γ hγ, one_mul]` (`AtkinLehnerMap.lean:518–527`).

- **Mathlib/project lemmas needed**: `AutomorphicFunction.left_invt'`, `AtkinLehnerDataH.χ_Γ`
- **Sources**: `decomposition.md` W-h.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W29] `atkinLehnerFunH_mem_locPolyDegSubmodule`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W26
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CharZero K] in
/-- `Wφ` is locally polynomial of degree `≤ k`. -/
theorem atkinLehnerFunH_mem_locPolyDegSubmodule
    (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) (x : G) :
    atkinLehnerFunH θG ψ U h k D φ x ∈ locPolyDegSubmodule p K h k := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`intro a j hj`; `rw [← cSpace.blockProj_apply, atkinLehnerFunH_blockProj]`; `symAct_mem_polySubmodule` at `j` (`AtkinLehnerMap.lean:529–537`).

- **Mathlib/project lemmas needed**: `symAct_mem_polySubmodule`, `cSpace.blockProj_apply`
- **Sources**: `decomposition.md` W-h.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W30] `atkinLehnerFunH_slash`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W13–W16, W18, W24–W26, W7, L21, L26
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CharZero K] in
/-- **`W` maps `ψ`-forms to `ψ⁻¹`-forms** at level `h`: for `u ∈ U`,
`(Wφ)(x u) = (Wφ)(x) ∣_{κ'} u` (`shapiro_blockProjH`, `mul_ιp_sGL_eqH`, `w_conj_mem_U` at the
disc-shifted element, `wQH_mul_mul_wQHinv`, `nebK_mul_nebK_eq_nebK_detH`). -/
theorem atkinLehnerFunH_slash (hh : 0 < h)
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh h ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ) (u : U) (x : G) :
    atkinLehnerFunH θG ψ U h k D φ (x * u)
      = discSlash h ψ κ' ⟨θG u, hU u.2⟩ (atkinLehnerFunH θG ψ U h k D φ x) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `atkinLehnerFun_slash` (`AtkinLehnerMap.lean:547–638`, `maxHeartbeats 1000000`) with: `cSpace_ext_blockProjH`, `blockProj_discSlash h`, `atkinLehnerFunH_blockProj` on both sides, `mul_ιp_sGL_eqH` (`u s_a = s_{a'} u'`), `D.w_conj_mem_U _ (discShiftH_mem_U …) (norm_theta_discShiftH_zero_one_le …)` for `w_h u' w_h⁻¹ ∈ U`, `blockProj_zero_apply_mul_mem_UH` at `w_h u' w_h⁻¹` (which fixes disc `0`: L26 with the `(0,1)`-entry `−c p^h/p` of `wQH_mul_mul_wQHinv`, norm `≤ p⁻¹^h`), the `d`-entry of the conjugate being `a(θ u')` (`wQH_mul_mul_wQHinv`), `nebK_mul_nebK_eq_nebK_detH` (`theta_mem_Iw`, `norm_theta_discShiftH_zero_one_le`), `D.χ_U`, `discConjMat_discShiftH_zero`, `atkinLehnerKH_eq`, `symAct_mul`, and the final `field_simp` with `hχ0`.  Follow the level-`1` proof line by line; the only new lemma names are the `H`-versions.

- **Mathlib/project lemmas needed**: `symAct_mul`, `theta_mem_Iw`, `AtkinLehnerDataH.χ_U`, `AtkinLehnerDataH.w_conj_mem_U`, `blockProj_discSlash`
- **Sources**: `decomposition.md` W-h; `lwx-h1/decomposition.md` W-f (the derivation); `AtkinLehnerMap.lean:547–638`.
- **Generality decision**: `hh` may be slack — record, do not edit; keep `maxHeartbeats 1000000` if needed (as at level `1`).
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-W10] Cleanup `PhD/LWX/AtkinLehnerMapH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W28, W29, W30
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMapH` and `lake exe runLinter PhD.LWX.AtkinLehnerMapH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerMapH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W31] `atkinLehnerMapH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W28–W30
- **Parallel**: yes (within the dependency order)
- **Type**: definition (`map_add'`, `map_smul'`)

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The Atkin–Lehner map** `W : S^D_{k+2}(ψ) → S^D_{k+2}(ψ⁻¹)` on classical disc forms at
level `h`. -/
def atkinLehnerMapH (hh : 0 < h)
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh h ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1)) :
    ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ →ₗ[K]
      ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ' where
  toFun φ := ⟨⟨atkinLehnerFunH θG ψ U h k D φ.1, fun γ hγ x =>
      atkinLehnerFunH_left_invt θG ψ U h k D φ.1 hγ x⟩,
    ⟨(mem_discForms_iff θG h ψ κ' U hU _).2 fun u x =>
        atkinLehnerFunH_slash θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ' φ.2 u x,
      fun x => atkinLehnerFunH_mem_locPolyDegSubmodule θG ψ U h k D φ.1 x⟩⟩
  map_add' φ φ' := by sorry
  map_smul' r φ := by sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`map_add'`/`map_smul'`: `Subtype.ext (AutomorphicFunction.ext fun x => ?_)`; `change atkinLehnerFunH … (φ.1 + φ'.1) x = …`; `simp only [atkinLehnerFunH, AutomorphicFunction.add_apply, map_add, smul_add, Finset.sum_add_distrib]`; for `smul`: `Finset.smul_sum`, `AutomorphicFunction.smul_apply`, `map_smul`, `smul_comm` (`AtkinLehnerMap.lean:640–666`).

- **Mathlib/project lemmas needed**: `Finset.sum_add_distrib`, `Finset.smul_sum`, `smul_comm`
- **Sources**: `decomposition.md` W-h.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W32] `atkinLehnerFunHInv_blockProj_zero`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CharZero K] in
theorem atkinLehnerFunHInv_blockProj_zero (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K))
    (x : G) :
    cSpace.blockProj 0 (atkinLehnerFunHInv θG ψ U h k D φ x)
      = ((D.χ x : Kˣ) : K) •
        symAct K k (atkinLehnerKHinv ψ h) (cSpace.blockProj 0 (φ (x * D.ιp (wGLH p h)))) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As W26/W27 for `atkinLehnerFunHInv` (`AtkinLehnerMap.lean:676–689`).

- **Mathlib/project lemmas needed**: `cSpace.blockProj_blockIncl`, `Finset.sum_eq_single`, `sGL_zero`
- **Sources**: `decomposition.md` W-i.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W33] `atkinLehnerFunHInv_left_invt`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CharZero K] in
/-- `W'φ` is left `Γ`-invariant. -/
theorem atkinLehnerFunHInv_left_invt (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K))
    {γ : G} (hγ : γ ∈ Γ) (x : G) :
    atkinLehnerFunHInv θG ψ U h k D φ (γ * x) = atkinLehnerFunHInv θG ψ U h k D φ x := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As W28 (`AtkinLehnerMap.lean:691–700`).

- **Mathlib/project lemmas needed**: as W28
- **Sources**: `decomposition.md` W-i.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-W11] Cleanup `PhD/LWX/AtkinLehnerMapH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W31, W32, W33
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMapH` and `lake exe runLinter PhD.LWX.AtkinLehnerMapH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerMapH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W34] `atkinLehnerFunHInv_mem_locPolyDegSubmodule`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CharZero K] in
/-- `W'φ` is locally polynomial of degree `≤ k`. -/
theorem atkinLehnerFunHInv_mem_locPolyDegSubmodule
    (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) (x : G) :
    atkinLehnerFunHInv θG ψ U h k D φ x ∈ locPolyDegSubmodule p K h k := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As W29 (`AtkinLehnerMap.lean:702–723`).

- **Mathlib/project lemmas needed**: as W29
- **Sources**: `decomposition.md` W-i.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W35] `atkinLehnerFunHInv_slash`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W30's prerequisites, W8, L22
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CharZero K] in
/-- **`W'` maps `ψ⁻¹`-forms to `ψ`-forms** at level `h` (the mirror of `atkinLehnerFunH_slash`,
with `w_h⁻¹ u' w_h`). -/
theorem atkinLehnerFunHInv_slash (hh : 0 < h)
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh h ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ') (u : U) (x : G) :
    atkinLehnerFunHInv θG ψ U h k D φ (x * u)
      = discSlash h ψ κ ⟨θG u, hU u.2⟩ (atkinLehnerFunHInv θG ψ U h k D φ x) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `atkinLehnerFunInv_slash` (`AtkinLehnerMap.lean:725–835`, `maxHeartbeats 1000000`) — the mirror of W30 with `w_h⁻¹ u' w_h` (`wQHinv_mul_mul_wQH`, the second component of `w_conj_mem_U`), `atkinLehnerKHinv_eq`.

- **Mathlib/project lemmas needed**: as W30
- **Sources**: `decomposition.md` W-i; `AtkinLehnerMap.lean:725–835`.
- **Generality decision**: as W30.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W36] `atkinLehnerMapHInv`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W33–W35
- **Parallel**: yes (within the dependency order)
- **Type**: definition (`map_add'`, `map_smul'`)

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The inverse map on classical disc forms at level `h`. -/
def atkinLehnerMapHInv (hh : 0 < h)
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh h ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1)) :
    ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ' →ₗ[K]
      ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ where
  toFun φ := ⟨⟨atkinLehnerFunHInv θG ψ U h k D φ.1, fun γ hγ x =>
      atkinLehnerFunHInv_left_invt θG ψ U h k D φ.1 hγ x⟩,
    ⟨(mem_discForms_iff θG h ψ κ U hU _).2 fun u x =>
        atkinLehnerFunHInv_slash θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ' φ.2 u x,
      fun x => atkinLehnerFunHInv_mem_locPolyDegSubmodule θG ψ U h k D φ.1 x⟩⟩
  map_add' φ φ' := by sorry
  map_smul' r φ := by sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As W31 (`AtkinLehnerMap.lean:837–862`).

- **Mathlib/project lemmas needed**: as W31
- **Sources**: `decomposition.md` W-i.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-W12] Cleanup `PhD/LWX/AtkinLehnerMapH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W34, W35, W36
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMapH` and `lake exe runLinter PhD.LWX.AtkinLehnerMapH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerMapH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W37] `atkinLehnerMapHInv_atkinLehnerMapH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W5, W16, W25, W27, W32
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `W' ∘ W = 1` at level `h`. -/
theorem atkinLehnerMapHInv_atkinLehnerMapH (hh : 0 < h)
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh h ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    (φ : ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ) :
    atkinLehnerMapHInv θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ'
        (atkinLehnerMapH θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ' φ) = φ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `atkinLehnerMapInv_atkinLehnerMap` (`AtkinLehnerMap.lean:864–890`): `Subtype.ext (AutomorphicFunction.ext fun y => cSpace_ext_blockProjH fun a => ?_)`; `shapiro_blockProjH` on both sides; `atkinLehnerFunHInv_blockProj_zero`, `atkinLehnerFunH_blockProj_zero`; `map_mul D.χ y (D.ιp (wGLH p h))`, `D.χ_wGLH`, `mul_inv_cancel_right`/`inv_mul_cancel_right` in `G`; `symAct_mul`, `atkinLehnerKH_mul_atkinLehnerKHinv`, `symAct_one k hf`, `smul_smul`, `mul_inv_cancel₀ (Units.ne_zero _)`, `one_smul`.

- **Mathlib/project lemmas needed**: `symAct_mul`, `symAct_one`, `AtkinLehnerDataH.χ_wGLH`
- **Sources**: `decomposition.md` W-i; `AtkinLehnerMap.lean:864–890`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W38] `atkinLehnerMapH_atkinLehnerMapHInv`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W6, W16, W25, W27, W32
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `W ∘ W' = 1` at level `h`. -/
theorem atkinLehnerMapH_atkinLehnerMapHInv (hh : 0 < h)
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh h ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    (φ : ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ') :
    atkinLehnerMapH θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ'
        (atkinLehnerMapHInv θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ' φ) = φ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As W37 with `atkinLehnerKHinv_mul_atkinLehnerKH`, `map_inv D.χ` (`AtkinLehnerMap.lean:892–918`).

- **Mathlib/project lemmas needed**: as W37
- **Sources**: `decomposition.md` W-i.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W39] `discEvalAtReps_mem_locPolyDegSubmoduleBlockH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CharZero K] in
/-- Evaluation at the representatives sends classical disc forms into the block-model
classical subspace. -/
theorem discEvalAtReps_mem_locPolyDegSubmoduleBlockH (c : ι → G)
    (φ : ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ) :
    discEvalAtReps θG h ψ κ U hU c ⟨φ.1, φ.2.1⟩ ∈ locPolyDegSubmoduleBlock p ι K h k := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`intro i a j hj`; `rw [discEvalAtReps_apply]`; `exact φ.2.2 (c i) a j hj` (`AtkinLehnerMap.lean:943–952`).

- **Mathlib/project lemmas needed**: `discEvalAtReps_apply`
- **Sources**: `decomposition.md` W-j.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-W13] Cleanup `PhD/LWX/AtkinLehnerMapH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W37, W38, W39
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMapH` and `lake exe runLinter PhD.LWX.AtkinLehnerMapH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerMapH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [W40] `discEvalAtRepsClH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W39
- **Parallel**: yes (within the dependency order)
- **Type**: definition (the bijectivity proof)

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The block model of the classical disc forms at a neat level**, at level `h`
(`bijective_discEvalAtReps_of_stabilizer_eq_bot`). -/
def discEvalAtRepsClH {u : K → K}
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i, AutomorphicFunction.stabilizerAtSlash Γ U (c i) = ⊥) :
    ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ ≃ₗ[K] locPolyDegSubmoduleBlock p ι K h k :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict (locPolyDegSubmoduleBlock p ι K h k)
      ((discEvalAtReps θG h ψ κ U hU c).comp (Submodule.inclusion inf_le_left))
      (fun φ => discEvalAtReps_mem_locPolyDegSubmoduleBlockH θG ψ U hU h k κ c φ))
    (by
      have _hκ := hκ
      have _hc := hc
      have _hstab := hstab
      sorry)
```

- **Depends on (declarations)**: —

**Proof sketch**:
The bijectivity `sorry`: transplant `AtkinLehnerMap.lean:965–988`: `hbij := bijective_discEvalAtReps_of_stabilizer_eq_bot θG h ψ κ U hU c hc hstab`; injective via `Submodule.inclusion_injective`; surjective: `obtain ⟨Φ, hΦ⟩ := hbij.2 F.1`, `hloc` from `hc.2`, `DoubleCoset.rel_iff`, `left_invt'`, `mem_discForms_iff h`, `discSlash_mem_locPolyDegSubmodule_of_shape h ψ κ _ (fun a => hκ _) hci`; `⟨⟨Φ.1, Φ.2, hloc⟩, Subtype.ext hΦ⟩`.  (Remove the three `have _h… := …` placeholders when writing the proof.)

- **Mathlib/project lemmas needed**: `bijective_discEvalAtReps_of_stabilizer_eq_bot`, `Submodule.inclusion_injective`, `DoubleCoset.rel_iff`, `AutomorphicFunction.left_invt'`, `discSlash_mem_locPolyDegSubmodule_of_shape`, `discEvalAtReps_apply`
- **Sources**: `decomposition.md` W-j; `AtkinLehnerMap.lean:955–988`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerMapH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-W-FINAL] Cleanup `PhD/LWX/AtkinLehnerMapH.lean` (final)
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMapH.lean
- **Depends on**: W40 (and every earlier ticket of the file)
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMapH` and `lake exe runLinter PhD.LWX.AtkinLehnerMapH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerMapH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [I1] `vRepDH_mem_levelM1`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentityH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem vRepDH_mem_levelM1 (c : Fin p) : vRepDH θG ψ U h D c ∈ levelM1 (p := p) θG := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `vRepD_mem_levelM1` (`AtkinLehnerIdentity.lean:57–61`): `levelM1` membership of `D.ιp (vGL p c)` via `D.theta_ιp`, `coe_vGL`, `vQ_mem_M1 (norm_natCast_le_one …)`.

- **Mathlib/project lemmas needed**: `vQ_mem_M1`, `AtkinLehnerDataH.theta_ιp`
- **Sources**: `decomposition.md` I-a.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerIdentityH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [I2] `upEltDH_mem_levelM1`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentityH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem upEltDH_mem_levelM1 : upEltDH θG ψ U h D ∈ levelM1 (p := p) θG := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As I1 with `c = 0` (`AtkinLehnerIdentity.lean:66–70`).

- **Mathlib/project lemmas needed**: as I1
- **Sources**: `decomposition.md` I-a.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerIdentityH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [I3] `discHeckeOperator_apply_eq_sumH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentityH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CharZero K] in
/-- **The naive Hecke formula** at level `h`: `(U_p φ)(x) = ∑_c φ(x v_c⁻¹) ∣ v_c`. -/
theorem discHeckeOperator_apply_eq_sumH
    (hfin : (((Quotient.mk'' : G → RightCosets U) ''
      (({upEltDH θG ψ U h D} : Set G) * (U : Set G))) : Set (RightCosets U)).Finite)
    (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range (vRepDH θG ψ U h D))
      (((Quotient.mk'' : G → RightCosets U) ''
        (({upEltDH θG ψ U h D} : Set G) * (U : Set G))) : Set (RightCosets U)))
    (hvinj : Function.Injective (vRepDH θG ψ U h D))
    (φ : DiscForms (Γ := Γ) θG h ψ κ U hU) (x : G) :
    ((discHeckeOperator θG h ψ κ U hU (upEltDH_mem_levelM1 θG ψ U h D) hfin φ :
        DiscForms (Γ := Γ) θG h ψ κ U hU) : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) x
      = ∑ c : Fin p, discSlash h ψ κ ⟨θG (vRepDH θG ψ U h D c), vRepDH_mem_levelM1 θG ψ U h D c⟩
          ((φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K))
            (x * (vRepDH θG ψ U h D c)⁻¹)) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `discHeckeOperator_apply_eq_sum` (`AtkinLehnerIdentity.lean:74–103`): `heckeOperatorSlash_eq_finsetSum` at the representatives `vRepDH`, with `hv`, `hvinj`, and the trivial `Γ`-parts (`fun _ => 1`); `AutomorphicFunction.slash_apply`.

- **Mathlib/project lemmas needed**: `heckeOperatorSlash_eq_finsetSum`, `AutomorphicFunction.slash_apply`
- **Sources**: `decomposition.md` I-a; `AtkinLehnerIdentity.lean:74–103`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerIdentityH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-I1] Cleanup `PhD/LWX/AtkinLehnerIdentityH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentityH.lean
- **Depends on**: I1, I2, I3
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerIdentityH` and `lake exe runLinter PhD.LWX.AtkinLehnerIdentityH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerIdentityH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [I4] `blockProj_zero_discSlash_of_shapeH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentityH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CharZero K] in
/-- Disc `0` of a classical-shape disc slash at a matrix fixing disc `0` is the nebentypus
constant times the `Sym^k`-action of the disc conjugate. -/
theorem blockProj_zero_discSlash_of_shapeH {u : K → K}
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    (δ : M1 p) (hδ : discImage h δ 0 = 0) {f : c(ZMod (p ^ h) × ℕ, K)}
    (hf : f ∈ locPolyDegSubmodule p K h k) :
    cSpace.blockProj 0 (discSlash h ψ κ δ f)
      = u (ψ ((discConj h δ 0 : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1)) •
        symAct K k (RingHom.mapMatrix ψ (discConj h δ 0 : Matrix (Fin 2) (Fin 2) ℚ_[p]))
          (cSpace.blockProj 0 f) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [blockProj_discSlash h, hδ]`; `kappaSlash_eq_smul_symAct_of_shape κ (discConjK h δ 0 ψ) (hκ _) (hf' : blockProj 0 f ∈ polySubmodule K k)`; `coe_discConjK` (`AtkinLehnerIdentity.lean:105–120`).

- **Mathlib/project lemmas needed**: `blockProj_discSlash`, `kappaSlash_eq_smul_symAct_of_shape`, `coe_discConjK`
- **Sources**: `decomposition.md` I-b.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerIdentityH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [I5] `apply_mul_ιp_pGLH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentityH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CharZero K] in
/-- **The central element acts trivially** on level-`h` disc forms. -/
theorem apply_mul_ιp_pGLH {φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)}
    (hφ : φ ∈ DiscForms (Γ := Γ) θG h ψ κ U hU) (x : G) :
    φ (x * D.ιp (pGL p)) = φ x := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `apply_mul_ιp_pGL` (`AtkinLehnerIdentity.lean:122–128`): `obtain ⟨γ, hγ, u, hu, hP, hθu, hcomm⟩ := D.central`; `rw [hP, ← mul_assoc, ← hcomm? …]` — as at level `1`: `φ(x γ u) = φ(γ x u) = φ(x u) = φ(x)` by centrality, `left_invt'`, `apply_mul_of_theta_eq_oneH`.

- **Mathlib/project lemmas needed**: `AtkinLehnerDataH.central`, `AutomorphicFunction.left_invt'`, `apply_mul_of_theta_eq_oneH`
- **Sources**: `decomposition.md` I-b.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerIdentityH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [I6] `apply_mul_ιp_pGL_invH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentityH.lean
- **Depends on**: I5
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CharZero K] in
theorem apply_mul_ιp_pGL_invH {φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)}
    (hφ : φ ∈ DiscForms (Γ := Γ) θG h ψ κ U hU) (x : G) :
    φ (x * (D.ιp (pGL p))⁻¹) = φ x := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
From I5: `φ(x p⁻¹) = φ(x p⁻¹ p) = φ(x)` (`AtkinLehnerIdentity.lean:130–138`).

- **Mathlib/project lemmas needed**: `inv_mul_cancel_right`
- **Sources**: `decomposition.md` I-b.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerIdentityH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-I2] Cleanup `PhD/LWX/AtkinLehnerIdentityH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentityH.lean
- **Depends on**: I4, I5, I6
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerIdentityH` and `lake exe runLinter PhD.LWX.AtkinLehnerIdentityH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerIdentityH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [I7] `blockProj_zero_apply_mul_ιpH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentityH.lean
- **Depends on**: W24
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CharZero K] in
/-- Level-equivariance at a lift `ιp g` of an Iwahori element fixing disc `0`, read on disc `0`
(`blockProj_zero_apply_mul_mem_UH`). -/
theorem blockProj_zero_apply_mul_ιpH {u : K → K}
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ) (x : G) {g : GL (Fin 2) ℚ_[p]}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) ∈ Iw p 1)
    (hg0 : discImage h (⟨(g : Matrix (Fin 2) (Fin 2) ℚ_[p]), Iw_one_le_M1 hg⟩ : M1 p) 0 = 0) :
    cSpace.blockProj 0 (φ (x * D.ιp g))
      = u (ψ ((discConj h (⟨(g : Matrix (Fin 2) (Fin 2) ℚ_[p]), Iw_one_le_M1 hg⟩ : M1 p) 0 :
            Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1)) •
        symAct K k (RingHom.mapMatrix ψ (discConj h
          (⟨(g : Matrix (Fin 2) (Fin 2) ℚ_[p]), Iw_one_le_M1 hg⟩ : M1 p) 0 :
            Matrix (Fin 2) (Fin 2) ℚ_[p])) (cSpace.blockProj 0 (φ x)) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `blockProj_zero_apply_mul_ιp` (`AtkinLehnerIdentity.lean:140–165`): `blockProj_zero_apply_mul_mem_UH … x ⟨D.ιp g, D.ιp_mem_U g hg⟩ hv0` with `he : (⟨θG (D.ιp g), _⟩ : M1 p) = ⟨g, Iw_one_le_M1 hg⟩` (`Subtype.ext (D.theta_ιp g)`), transported by the `rintro _ _ rfl; rfl` congruence.

- **Mathlib/project lemmas needed**: `blockProj_zero_apply_mul_mem_UH`, `Iw_one_le_M1`
- **Sources**: `decomposition.md` I-b.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerIdentityH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [I8] `term_elt_eqH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentityH.lean
- **Depends on**: W4
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- **The group element of the `(b,c)`-term** at level `h`:
`x v_c⁻¹ w_h v_b⁻¹ w_h⁻¹ = x s_{b p^{h−1}} · (ιp p)⁻¹ · ℓ_{b,c}⁻¹`
(`wGLH_mul_vGL_mul_wGLH_inv_mul_vGL`, inverted). -/
theorem term_elt_eqH (x : G) (b c : ℚ_[p]) :
    x * (D.ιp (vGL p c))⁻¹ * D.ιp (wGLH p h) * (D.ιp (vGL p b))⁻¹ * (D.ιp (wGLH p h))⁻¹
      = x * D.ιp (sGL p (b * (p : ℚ_[p]) ^ h / p)) * (D.ιp (pGL p))⁻¹
        * (D.ιp (ℓGLH p h b c))⁻¹ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `term_elt_eq` (`AtkinLehnerIdentity.lean:171–181`): `h := congrArg (fun g => (D.ιp g)⁻¹) (wGLH_mul_vGL_mul_wGLH_inv_mul_vGL h b c)`; `hs : (D.ιp (sGL p (-(b * p^h / p))))⁻¹ = D.ιp (sGL p (b * p^h / p))` (`map_inv`, `sGL_inv`, `neg_neg`); `simp only [map_mul, map_inv, mul_inv_rev, inv_inv, hs] at h`; `simp only [mul_assoc] at h ⊢; rw [h]`.

- **Mathlib/project lemmas needed**: `sGL_inv`, `mul_inv_rev`
- **Sources**: `decomposition.md` I-c.
- **Generality decision**: Every `h`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerIdentityH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [I9] `blockProj_zero_apply_term_eltH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentityH.lean
- **Depends on**: I5, I7, W25, L23, L24, L28, L32, L34, W2
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CharZero K] in
/-- **Disc `0` of `φ(x s_{b p^{h−1}} p⁻¹ ℓ⁻¹)`**: the central `p` acts trivially and `ℓ⁻¹` fixes
disc `0` with `d`-entry `1 − bcp^h`, so it is
`nebK(1 − bcp^h) · symAct(conj ℓ⁻¹)(φ(x)|_{b p^{h−1}})`. -/
theorem blockProj_zero_apply_term_eltH (hh : 0 < h)
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ) (x : G) (b c : Fin p) :
    cSpace.blockProj 0
        (φ (x * D.ιp (sGL p ((b : ℕ) * (p : ℚ_[p]) ^ h / p)) * (D.ιp (pGL p))⁻¹
          * (D.ιp (ℓGLH p h (b : ℕ) (c : ℕ)))⁻¹))
      = nebK (ψ (1 - (b : ℚ_[p]) * c * (p : ℚ_[p]) ^ h)) •
        symAct K k (RingHom.mapMatrix ψ (tMatHInv p h 0 * ℓQHinv p h (b : ℕ) (c : ℕ)
          * tMatH p h 0))
          (cSpace.blockProj ((((b : ℕ) * p ^ (h - 1) : ℕ) : ZMod (p ^ h))) (φ x)) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `blockProj_zero_apply_term_elt` (`AtkinLehnerIdentity.lean:183–233`) with: `hℓU := D.ιp_mem_U _ (ℓQH_mem_Iw hh hb hc)`; the central-element move (`D.central`, `apply_mul_of_theta_eq_oneH`); `hg : ((ℓGLH p h b c)⁻¹ : Matrix) ∈ Iw p 1` via `coe_ℓGLH_inv`, `ℓQHinv_mem_Iw hh hb hc`; `hg0` via `discImage_ℓQHinv_zero hh hb hc`; `hmain := blockProj_zero_apply_mul_ιpH … y hg hg0`; `hsh : blockProj 0 (φ y) = blockProj (b p^{h−1}) (φ x)` by `shapiro_blockProjH … x ((b * p^(h-1) : ℕ) : ZMod (p^h))` with `((… : ZMod (p^h)).val : ℚ_[p]) = b * p^h / p` (`ZMod.val_natCast`, `Nat.mod_eq_of_lt` (`b * p^(h-1) < p^h` from `b < p`, `hh`), `Nat.cast_mul`, `pow_succ`, `field_simp`); `discConj_ℓQHinv_zero_one_one hh hb hc`, `coe_discConj`, `discConjMat_zero_of_discImage_zero_prime_pow`.

- **Mathlib/project lemmas needed**: `ZMod.val_natCast`, `Nat.mod_eq_of_lt`, `Nat.mul_lt_mul_right?`, `pow_succ`
- **Sources**: `decomposition.md` I-d; `AtkinLehnerIdentity.lean:183–233`.
- **Generality decision**: `hh` necessary (integrality of `ℓQH`, the disc index).
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerIdentityH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-I3] Cleanup `PhD/LWX/AtkinLehnerIdentityH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentityH.lean
- **Depends on**: I7, I8, I9
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerIdentityH` and `lake exe runLinter PhD.LWX.AtkinLehnerIdentityH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerIdentityH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [I10] `atkinLehner_term_eqH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentityH.lean
- **Depends on**: I8, I9, W7, W8, W27, W19, L30, L28
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The `(b, c)`-term of the double-coset expansion at level `h`, read on disc `0`: with
`w_h v_b w_h⁻¹ v_c = ℓ_{b,c} · p · s_{−b p^{h−1}}` the term is `ψ_neb(1 + bcp^h)⁻¹` times a
vector independent of `c`: `p^k · (disc `b p^{h−1}` of φ(x)) ∣_k (1 −b/p; 0 1)`. -/
theorem atkinLehner_term_eqH (hh : 0 < h)
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh h ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    (φ : ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ) (x : G) (b c : Fin p) :
    symAct K k (RingHom.mapMatrix ψ (discConj h (⟨vQ p (c : ℕ), vQ_mem_M1 (by
        exact IsUltrametricDist.norm_natCast_le_one ℚ_[p] (c : ℕ))⟩ : M1 p) 0 :
          Matrix (Fin 2) (Fin 2) ℚ_[p]))
      (((D.χ (x * (vRepDH θG ψ U h D c)⁻¹) : Kˣ) : K) •
        symAct K k (atkinLehnerKHinv ψ h)
          (symAct K k (RingHom.mapMatrix ψ (discConj h (⟨vQ p (b : ℕ), vQ_mem_M1 (by
              exact IsUltrametricDist.norm_natCast_le_one ℚ_[p] (b : ℕ))⟩ : M1 p) 0 :
                Matrix (Fin 2) (Fin 2) ℚ_[p]))
            (cSpace.blockProj 0
              ((atkinLehnerMapH θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ' φ :
                  AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K))
                (x * (vRepDH θG ψ U h D c)⁻¹ * D.ιp (wGLH p h)
                  * (vRepDH θG ψ U h D b)⁻¹)))))
      = (nebK (ψ (1 + (b : ℚ_[p]) * c * (p : ℚ_[p]) ^ h)))⁻¹ •
        ((ψ p) ^ k • symAct K k (RingHom.mapMatrix ψ !![1, -((b : ℚ_[p]) / p); 0, 1])
          (cSpace.blockProj ((((b : ℕ) * p ^ (h - 1) : ℕ) : ZMod (p ^ h))) (φ.1 x))) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `atkinLehner_term_eq` (`AtkinLehnerIdentity.lean:242–326`): `hMb, hMc` (`coe_discConj`, `discConjMat_zero_of_discImage_zero_prime_pow _ _ (discImage_vQ_zero_prime_pow h hb)`); `atkinLehnerFunH_blockProj_zero`; `hχ` (`vRepDH`, `map_mul`, `map_inv`, `D.χ_wGLH`, `D.χ_vGL`); `hy := term_elt_eqH …`; `blockProj_zero_apply_term_eltH hh …`; `symAct_mul` twice; the scalar identity `hscal : ψ p • 1 = …` and the matrix identity
`mapMatrix ψ (tMatHInv 0 * vQ c * tMatH 0) * atkinLehnerKH * mapMatrix ψ (tMatHInv 0 * vQ b * tMatH 0) * atkinLehnerKHinv * mapMatrix ψ (tMatHInv 0 * ℓQHinv b c * tMatH 0) = (ψ p • 1) * mapMatrix ψ !![1, -(b/p); 0, 1]`
(`atkinLehnerKH_eq`, `atkinLehnerKHinv_eq`, `← map_mul`…, `congr 1`, `ext; fin_cases; simp [tMatH, tMatHInv, ℓQHinv, wQH, wQHinv, vQ, Matrix.mul_apply, Fin.sum_univ_two, hp0]; field_simp; ring` — with `(p^h)⁻¹` factors, add `pow_ne_zero` to the simp set); `‖bcp^h‖ ≤ p⁻¹^h` (`norm_mul`, `norm_pow`, `Padic.norm_p`); `symAct_smul_one`, `nebK_one_sub_eq_invH hh hmul hcond hbcp`.

- **Mathlib/project lemmas needed**: `symAct_mul`, `symAct_smul_one`, `atkinLehnerKH_eq`, `atkinLehnerKHinv_eq`, `nebK_one_sub_eq_invH`, `RingHom.mapMatrix` (`map_mul`)
- **Sources**: `decomposition.md` I-e; `AtkinLehnerIdentity.lean:242–326`.
- **Generality decision**: `hh` necessary; the translation `(1, −b/p; 0, 1)` is level-independent (design decision 5).
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerIdentityH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [I11] `blockProj_zero_discHecke_atkinLehnerH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentityH.lean
- **Depends on**: I3, I4, I10, W17, W32, N17-shape `hsum`
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **`U_p ∘ W⁻¹ ∘ U_p^{(ψ⁻¹)} ∘ W = p^{k+1}` on disc `0`** at level `h`: the double-coset
expansion, the key factorisation, and the character sum `hsum`. -/
theorem blockProj_zero_discHecke_atkinLehnerH (hh : 0 < h)
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) → nebK (ψ x) = 1)
    (hsum : ∀ b : ℕ, ¬ p ∣ b →
      ∑ c ∈ Finset.range p, (nebK (ψ (1 + (b : ℚ_[p]) * c * (p : ℚ_[p]) ^ h)))⁻¹ = 0)
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh h ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    (hfin : (((Quotient.mk'' : G → RightCosets U) ''
      (({upEltDH θG ψ U h D} : Set G) * (U : Set G))) : Set (RightCosets U)).Finite)
    (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range (vRepDH θG ψ U h D))
      (((Quotient.mk'' : G → RightCosets U) ''
        (({upEltDH θG ψ U h D} : Set G) * (U : Set G))) : Set (RightCosets U)))
    (hvinj : Function.Injective (vRepDH θG ψ U h D))
    (φ : ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ) (x : G) :
    cSpace.blockProj 0
      ((discHeckeOperatorClH θG ψ U hU h k κ hκ (upEltDH_mem_levelM1 θG ψ U h D) hfin
        (atkinLehnerMapHInv θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ'
          (discHeckeOperatorClH θG ψ U hU h k κ' (u := fun x => (nebK x)⁻¹) hκ'
            (upEltDH_mem_levelM1 θG ψ U h D) hfin
            (atkinLehnerMapH θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ' φ))) :
        AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) x)
      = (ψ p) ^ (k + 1) • cSpace.blockProj 0 (φ.1 x) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `blockProj_zero_discHecke_atkinLehner` (`AtkinLehnerIdentity.lean:328–427`, `maxHeartbeats 1000000`): unfold the two `discHeckeOperatorClH` through `discHeckeOperator_apply_eq_sumH` (both weights), `map_sum`, `blockProj_zero_discSlash_of_shapeH` with `hvc : ⟨θG (vRepDH c), _⟩ = ⟨vQ p c, _⟩` and `hvc11 : (discConj … vQ c … 0) 1 1 = 1` (so the constants are `nebK (ψ 1) = 1`, W17); `atkinLehnerFunHInv_blockProj_zero`; then the double sum of `atkinLehner_term_eqH`; split `b = 0` (`Finset.sum_eq_single 0`-style / `Fin.sum_univ_succ`): the `b ≠ 0` terms vanish by `hsum b (Nat.not_dvd_of_pos_of_lt (Fin.pos_of_ne_zero …) b.isLt)` after `Fin.sum_univ_eq_sum_range` and factoring the `c`-independent vector (`← Finset.sum_smul`); the `b = 0` term: disc `((0 * p^(h-1) : ℕ) : ZMod (p^h)) = 0` (`simp`), `nebK (ψ 1) = 1`, `!![1, -(0/p); 0, 1] = 1`, `symAct_one`, `∑ c, (ψ p)^k • v = p • (ψ p)^k • v` (`Finset.sum_const`, `Finset.card_fin`, `nsmul_eq_mul`, `map_natCast`), `pow_succ`.

- **Mathlib/project lemmas needed**: `Fin.sum_univ_eq_sum_range`, `Finset.sum_eq_single`, `Finset.sum_smul`, `Finset.sum_const`, `Nat.not_dvd_of_pos_of_lt`, `symAct_one`, `pow_succ`
- **Sources**: `lwx.txt:1783–1785`; `decomposition.md` I-f; `AtkinLehnerIdentity.lean:328–427`.
- **Generality decision**: `maxHeartbeats 1000000` as at level `1`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerIdentityH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [I12] `discHeckeClH_comp_atkinLehnerH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentityH.lean
- **Depends on**: I11, W16, W25
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The operator identity** `U_p ∘ (W⁻¹ ∘ U_p^{(ψ⁻¹)} ∘ W) = p^{k+1}` on the classical disc
forms at level `h` (`shapiro_blockProjH` carries the disc-`0` identity to every disc). -/
theorem discHeckeClH_comp_atkinLehnerH (hh : 0 < h)
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) → nebK (ψ x) = 1)
    (hsum : ∀ b : ℕ, ¬ p ∣ b →
      ∑ c ∈ Finset.range p, (nebK (ψ (1 + (b : ℚ_[p]) * c * (p : ℚ_[p]) ^ h)))⁻¹ = 0)
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh h ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    (hfin : (((Quotient.mk'' : G → RightCosets U) ''
      (({upEltDH θG ψ U h D} : Set G) * (U : Set G))) : Set (RightCosets U)).Finite)
    (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range (vRepDH θG ψ U h D))
      (((Quotient.mk'' : G → RightCosets U) ''
        (({upEltDH θG ψ U h D} : Set G) * (U : Set G))) : Set (RightCosets U)))
    (hvinj : Function.Injective (vRepDH θG ψ U h D)) :
    (discHeckeOperatorClH θG ψ U hU h k κ hκ (upEltDH_mem_levelM1 θG ψ U h D) hfin).comp
        ((atkinLehnerMapHInv θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ').comp
          ((discHeckeOperatorClH θG ψ U hU h k κ' (u := fun x => (nebK x)⁻¹) hκ'
            (upEltDH_mem_levelM1 θG ψ U h D) hfin).comp
            (atkinLehnerMapH θG ψ U hU h k D κ κ' hh hmul hne hcond hκ hκ')))
      = (ψ p) ^ (k + 1) • LinearMap.id := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `discHeckeCl_comp_atkinLehner` (`AtkinLehnerIdentity.lean:429–465`, `maxHeartbeats 1000000`): `LinearMap.ext fun φ => Subtype.ext (AutomorphicFunction.ext fun x => cSpace_ext_blockProjH fun a => ?_)`; `shapiro_blockProjH` (both sides, the LHS is a classical disc form: `.2.1`) reduces disc `a` at `x` to disc `0` at `x s_a`; `blockProj_zero_discHecke_atkinLehnerH … (x * D.ιp (sGL p a.val))`; `LinearMap.smul_apply`, `map_smul`.

- **Mathlib/project lemmas needed**: `LinearMap.ext`, `cSpace_ext_blockProjH`, `shapiro_blockProjH`
- **Sources**: `decomposition.md` I-f; `AtkinLehnerIdentity.lean:429–465`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerIdentityH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-I4] Cleanup `PhD/LWX/AtkinLehnerIdentityH.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentityH.lean
- **Depends on**: I10, I11, I12
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerIdentityH` and `lake exe runLinter PhD.LWX.AtkinLehnerIdentityH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerIdentityH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [I13] `discEvalAtRepsClH_discHeckeOperatorClH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentityH.lean
- **Depends on**: I1, I2
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [CharZero K] in
/-- Under the block model at a neat level, the classical Hecke operator at level `h` is the
block operator of the certificates restricted to the classical subspace
(`discEvalAtReps_discHeckeOperator`). -/
theorem discEvalAtRepsClH_discHeckeOperatorClH {u : K → K}
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hfin : (((Quotient.mk'' : G → RightCosets U) ''
      (({upEltDH θG ψ U h D} : Set G) * (U : Set G))) : Set (RightCosets U)).Finite)
    (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i, AutomorphicFunction.stabilizerAtSlash Γ U (c i) = ⊥)
    (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range (vRepDH θG ψ U h D))
      (((Quotient.mk'' : G → RightCosets U) ''
        (({upEltDH θG ψ U h D} : Set G) * (U : Set G))) : Set (RightCosets U)))
    (hvinj : Function.Injective (vRepDH θG ψ U h D)) (idx : ι → Fin p → ι)
    (uu : ι → Fin p → U) (d : ι → Fin p → G) (hd : ∀ i t, d i t ∈ Γ)
    (hfact : ∀ i t, c i * (vRepDH θG ψ U h D t)⁻¹ = d i t * c (idx i t) * (uu i t : G))
    (φ : ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ) :
    (discEvalAtRepsClH θG ψ U hU h k κ hκ c hc hstab
        (discHeckeOperatorClH θG ψ U hU h k κ hκ (upEltDH_mem_levelM1 θG ψ U h D) hfin φ) :
          c(ι × (ZMod (p ^ h) × ℕ), K))
      = discHeckeBlockOp θG h ψ κ U hU (vRepDH θG ψ U h D) (vRepDH_mem_levelM1 θG ψ U h D) idx
          uu (discEvalAtRepsClH θG ψ U hU h k κ hκ c hc hstab φ) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [discEvalAtRepsClH_apply, discEvalAtRepsClH_apply]`; `exact discEvalAtReps_discHeckeOperator θG h ψ κ U hU (vRepDH …) (vRepDH_mem_levelM1 …) idx uu (upEltDH_mem_levelM1 …) hfin c hv hvinj d hd hfact ⟨φ.1, φ.2.1⟩` (`AtkinLehnerIdentity.lean:472–498`).

- **Mathlib/project lemmas needed**: `discEvalAtReps_discHeckeOperator`
- **Sources**: `decomposition.md` I-g.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerIdentityH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [I14] `atkinLehnerHypothesis_of_conjH`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentityH.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq ι] in
/-- **Hypothesis H1 transports along similarities** at level `h`. -/
theorem atkinLehnerHypothesis_of_conjH
    {A B A' S S' S₁ S₁' : Matrix (Fin (Fintype.card ι * ((k + 1) * p ^ h)))
      (Fin (Fintype.card ι * ((k + 1) * p ^ h))) K}
    (hAL : AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ h k A B A')
    (hS : S₁ * S = 1) (hS' : S₁' * S' = 1) :
    AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ h k (S * A * S₁) (S * B * S₁)
      (S' * A' * S₁') := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `atkinLehnerHypothesis_of_conj` (`AtkinLehnerIdentity.lean:500–526`) without `_hS''`: `obtain ⟨hAB, P, Q, hQP, hA'⟩ := hAL`; `hSS₁ := mul_eq_one_comm.mp hS`; witnesses `S' * P * S₁`, `S * Q * S₁'`; the three `calc` blocks with `Matrix.mul_assoc`, `Matrix.mul_smul`, `Matrix.smul_mul`, `hS`, `hS'`, `hQP`, `hSS₁`.

- **Mathlib/project lemmas needed**: `mul_eq_one_comm`, `Matrix.mul_assoc`, `Matrix.mul_smul`, `Matrix.smul_mul`
- **Sources**: `decomposition.md` I-g; `AtkinLehnerIdentity.lean:500–526`.
- **Generality decision**: Level `h`; `S' * S₁' = 1` not needed.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerIdentityH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-ALL-1] `/cleanup-all` before the milestone I15
- **Status**: done
- **File**: all files of this board
- **Depends on**: every ticket before I15
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup-all` over the nine modules of this board before the milestone I15: cross-file naming consistency, dead helpers, docstrings of the H-definitions, `lake exe runLinter` on every module; full `lake build PhD` green.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of all nine modules clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [I15] `atkinLehnerHypothesis_of_atkinLehnerDataH` **[MILESTONE]**
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentityH.lean
- **Depends on**: I12, I13, W40, N17–N20, N24, C19-shape, T-c
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **Hypothesis H1 at the classical points of conductor `p^{h+1}`, from the level-`h`
Atkin–Lehner data** ([LWX, Prop 3.22] at conductor `p^m`, `m = h + 1`).  With `A` the matrix
of `U_p` at `(k, ψ)`, `A'` at the partner `(k, ψ⁻¹)` (nebentypus `ω⁻¹ω₀^{2k}`, point
`T_{χ_k}(ζ⁻¹)`), and `B := W⁻¹ A' W`: `A B = p^{k+1}` is `discHeckeClH_comp_atkinLehnerH` in
the block model, and `A' = W B W⁻¹` by construction. -/
theorem atkinLehnerHypothesis_of_atkinLehnerDataH [Nonempty ι]
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h) {ζ : K}
    (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹)
    (D : AtkinLehnerDataH θG ψ U h Γ (nebCharKH h ψ ω k ζ))
    (hfin : (((Quotient.mk'' : G → RightCosets U) ''
      (({upEltDH θG ψ U h D} : Set G) * (U : Set G))) : Set (RightCosets U)).Finite)
    (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range (vRepDH θG ψ U h D))
      (((Quotient.mk'' : G → RightCosets U) ''
        (({upEltDH θG ψ U h D} : Set G) * (U : Set G))) : Set (RightCosets U)))
    (hvinj : Function.Injective (vRepDH θG ψ U h D))
    (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i, AutomorphicFunction.stabilizerAtSlash Γ U (c i) = ⊥)
    (idx : ι → Fin p → ι) (uu : ι → Fin p → U) (d : ι → Fin p → G) (hd : ∀ i t, d i t ∈ Γ)
    (hfact : ∀ i t, c i * (vRepDH θG ψ U h D t)⁻¹ = d i t * c (idx i t) * (uu i t : G)) :
    ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ h k
      ((classicalDataH ψ ω θG U hU (vRepDH θG ψ U h D) (vRepDH_mem_levelM1 θG ψ U h D) uu hp2
        hψ hh hζ hpK k).matrix idx) B
      ((classicalDataH ψ (partnerChar p ω k) θG U hU (vRepDH θG ψ U h D)
        (vRepDH_mem_levelM1 θG ψ U h D) uu hp2 hψ hh hζ.inv hpK k).matrix idx) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `atkinLehnerHypothesis_of_atkinLehnerData` (`AtkinLehnerIdentity.lean:528–625`, `maxHeartbeats 2000000`) with `1 → h`: `cd, cd'` the two `classicalDataH`; `hκ := autFactor_haloWeightH_classicalPoint_eq_nebCharKH h ψ ω k ζ hp2 hψ hζ.pow_eq_one cd.h0 cd.h1 cd.hT`, `hκ' := autFactor_haloWeightH_partner_eq_inv_nebCharKH h ψ ω k ζ hp2 hψ hh hζ cd'.h0 cd'.h1 cd'.hT`; `hmul/hne/hcond/hsum` from N18/N19/N20/N17 (all with `hh`); `bas := Module.finBasisOfFinrankEq K _ (finrank_locPolyDegSubmoduleBlock h k)`; `T, T'` the restricted block operators (`mem_locPolyDegSubmoduleBlock_discHeckeBlockOp_of_isClassicalShape θG h …`); `E, E'` via `discEvalAtRepsClH`; `AL := atkinLehnerEquivH … hh …`; `Wb := E.symm.trans (AL.trans E')`; `hTE, hTE'` from I13; `hkey` from I12 (`LinearMap.congr_fun`, `LinearEquiv.trans_apply`, `symm_apply_apply`); witnesses `toMatrix bas bas (Wb.symm ∘ₗ T' ∘ₗ Wb)`, `toMatrix Wb`, `toMatrix Wb.symm`; `LinearMap.toMatrix_comp`, `LinearEquiv.symm_comp`, `LinearMap.toMatrix_id`.

- **Mathlib/project lemmas needed**: `Module.finBasisOfFinrankEq`, `finrank_locPolyDegSubmoduleBlock`, `LinearMap.toMatrix_comp`, `LinearEquiv.symm_comp`, `LinearMap.toMatrix_id`, `LinearMap.congr_fun`
- **Sources**: [LWX, Prop 3.22] `lwx.txt:1763–1768` at conductor `p^{h+1}`; `decomposition.md` I-g; `AtkinLehnerIdentity.lean:528–625`.
- **Generality decision**: **Milestone M1.** `maxHeartbeats 2000000` as at level `1`; `#print axioms` must be standard.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerIdentityH.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-I-FINAL] Cleanup `PhD/LWX/AtkinLehnerIdentityH.lean` (final)
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentityH.lean
- **Depends on**: I15 (and every earlier ticket of the file)
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerIdentityH` and `lake exe runLinter PhD.LWX.AtkinLehnerIdentityH` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerIdentityH clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [F1] `invChar_eq_inv`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerFamily.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `invChar ω` is the group inverse of `ω` in `(ℤ/p)^× →* ℤ_p^×`. -/
theorem invChar_eq_inv (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) : invChar ω = ω⁻¹ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`MonoidHom.ext fun u => rfl` (`invChar_apply` and `MonoidHom.inv_apply` are both `rfl`); if the `rfl` fails to see through the instance, `ext u; simp [invChar_apply, MonoidHom.inv_apply]`.

- **Mathlib/project lemmas needed**: `MonoidHom.ext`, `MonoidHom.inv_apply`, `invChar_apply` (`ConjChar.lean:41`)
- **Sources**: `decomposition.md` F-b.
- **Generality decision**: Pure group theory in `(ℤ/p)^× →* ℤ_p^×`.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerFamily.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [F2] `partnerChar_succ`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerFamily.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The partner disc at exponent `k + 1` is the partner disc at `k` times `ω₀²`
([LWX, §4.2]: "Replacing ψ by ψω₀⁻¹ and k by k + 1"). -/
theorem partnerChar_succ (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    partnerChar p ω (k + 1) = partnerChar p ω k * teichChar p ^ 2 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [partnerChar, partnerChar, show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, mul_assoc]` (or `simp [partnerChar, pow_add, pow_succ, mul_assoc]`).

- **Mathlib/project lemmas needed**: `pow_add`, `mul_assoc`, `partnerChar` (`NebChar.lean:397`)
- **Sources**: `lwx.txt:2351`; `decomposition.md` F-b.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerFamily.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [F3] `partnerChar_invChar_mul_teichChar_pow`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerFamily.lean
- **Depends on**: F1
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Every disc is a partner disc: `partnerChar p (ω⁻¹ω₀^{2k}) k = ω`
([LWX, §4.2]: "Choose ψ so that ψ|_Δ·ω₀^k = ω"). -/
theorem partnerChar_invChar_mul_teichChar_pow (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    partnerChar p (invChar ω * teichChar p ^ (2 * k)) k = ω := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [partnerChar, invChar_eq_inv, invChar_eq_inv, mul_inv, inv_inv, mul_assoc, inv_mul_cancel, mul_one]` in the commutative group of monoid homs (`mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹`); or `simp [partnerChar, invChar_eq_inv, mul_assoc]`/`group` after `invChar_eq_inv`.

- **Mathlib/project lemmas needed**: `mul_inv`, `inv_inv`, `inv_mul_cancel`, `mul_one`
- **Sources**: `lwx.txt:2358` (‘Choose ψ so that ψ|_Δ·ω₀^k = ω’); `decomposition.md` F-b.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerFamily.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-F1] Cleanup `PhD/LWX/AtkinLehnerFamily.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerFamily.lean
- **Depends on**: F1, F2, F3
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerFamily` and `lake exe runLinter PhD.LWX.AtkinLehnerFamily` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerFamily clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [F4] `teichChar_pow_sub_one`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerFamily.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `ω₀^{p−1} = 1` ([LWX, §4.2]: "since ω₀^{ϕ(q)} = 1"): `teichRes` is multiplicative and
`r^{p−1} = 1` in `(ℤ/p)^×`. -/
theorem teichChar_pow_sub_one : teichChar p ^ (p - 1) = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`MonoidHom.ext fun r => by rw [MonoidHom.pow_apply, MonoidHom.one_apply, ← map_pow, ZMod.units_pow_card_sub_one_eq_one, map_one]` (check the exact name of Fermat for units: `ZMod.units_pow_card_sub_one_eq_one` in `Mathlib/FieldTheory/Finite/Basic.lean`; fallback `ZMod.pow_card_sub_one_eq_one` on `(r : ZMod p) ≠ 0` with `Units.ext`).

- **Mathlib/project lemmas needed**: `MonoidHom.pow_apply`, `MonoidHom.one_apply`, `map_pow`, `map_one`, `ZMod.units_pow_card_sub_one_eq_one`
- **Sources**: `lwx.txt:2361` (‘since ω₀^{ϕ(q)} = 1’); `decomposition.md` F-b.
- **Generality decision**: No analytic property of `teichmuller` — only that `teichChar` is a monoid hom.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/AtkinLehnerFamily.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-F-FINAL] Cleanup `PhD/LWX/AtkinLehnerFamily.lean` (final)
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerFamily.lean
- **Depends on**: F4 (and every earlier ticket of the file)
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerFamily` and `lake exe runLinter PhD.LWX.AtkinLehnerFamily` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerFamily clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [R1] `inv_pow_lt_norm_pow_of_norm_pow_eq`
- **Status**: done
- **File**: PhD/LWX/ConductorSlopes.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- **"The assumption on `M`"** ([LWX, Thm 1.5]: "`p^{−q/p^{M−1}(p−1)} > λ`" with
`λ = p^{−8/((p²−1)t+8)}`): at a point with `v(T₀) = v(p)/(p^{h−1}(p−1))`, the radius
condition `v(T₀) < 8/((p²−1)t+8)` of the slope reading is `(p²−1)t + 8 < 8p^{h−1}(p−1)`. -/
theorem inv_pow_lt_norm_pow_of_norm_pow_eq (h : ℕ) (hh : 0 < h) {t : ℕ}
    (hM : (p ^ 2 - 1) * t + 8 < 8 * (p ^ (h - 1) * (p - 1))) {T₀ : K} (h1 : ‖T₀‖ < 1)
    (hnorm : ‖T₀‖ ^ (p ^ (h - 1) * (p - 1)) = (p : ℝ)⁻¹) :
    (p : ℝ)⁻¹ ^ 8 < ‖T₀‖ ^ ((p ^ 2 - 1) * t + 8) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `hT0 : 0 < ‖T₀‖`: from `hnorm` (`‖T₀‖ ^ e = p⁻¹ ≠ 0`, so `‖T₀‖ ≠ 0`; `pow_ne_zero_iff`/`pow_eq_zero_iff`).
2. `(p⁻¹)^8 = (‖T₀‖ ^ e) ^ 8 = ‖T₀‖ ^ (8 * e)` (`← hnorm`, `← pow_mul`).
3. `‖T₀‖ ^ (8 * e) < ‖T₀‖ ^ ((p²−1)t + 8)` by `pow_lt_pow_right_of_lt_one₀ hT0 h1 hM'` with `hM' : (p²−1)t + 8 < 8 * e` (that is `hM`, with `8 * (p^(h-1)*(p-1))` — `mul_comm` if needed).

- **Mathlib/project lemmas needed**: `pow_mul`, `pow_lt_pow_right_of_lt_one₀`, `pow_eq_zero_iff`
- **Sources**: [LWX, Thm 1.5] `lwx.txt:181–186`, `lwx.txt:2323`; `decomposition.md` R-a.
- **Generality decision**: `hh` is slack (unused) — record `_hh` at cleanup; do not edit.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ConductorSlopes.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [R2] `ClassicalDataH.inv_pow_lt_norm_pow`
- **Status**: done
- **File**: PhD/LWX/ConductorSlopes.lean
- **Depends on**: R1
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The region condition at a level-`h` classical datum. -/
theorem ClassicalDataH.inv_pow_lt_norm_pow (hh : 0 < h) {ω : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ : K}
    {k : ℕ} (c : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (hM : (p ^ 2 - 1) * Fintype.card ι + 8 < 8 * (p ^ (h - 1) * (p - 1))) :
    (p : ℝ)⁻¹ ^ 8 < ‖T₀‖ ^ ((p ^ 2 - 1) * Fintype.card ι + 8) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`inv_pow_lt_norm_pow_of_norm_pow_eq h hh hM c.h1 (by rw [c.hnorm, hψ, Padic.norm_p])` (`‖ψ (p : ℚ_[p])‖ = ‖(p:ℚ_[p])‖ = p⁻¹`).

- **Mathlib/project lemmas needed**: `Padic.norm_p`
- **Sources**: `decomposition.md` R-a.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ConductorSlopes.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [R3] `atkinLehnerHypothesis_symm`
- **Status**: done
- **File**: PhD/LWX/ConductorSlopes.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq ι] in
/-- **Hypothesis H1 is symmetric in the two points**: `B' := P A Q` (the roles of `A` and
`A'` exchanged, `mul_eq_one_comm`). -/
theorem atkinLehnerHypothesis_symm {k : ℕ}
    {A B A' : Matrix (Fin (Fintype.card ι * ((k + 1) * p ^ h)))
      (Fin (Fintype.card ι * ((k + 1) * p ^ h))) K}
    (hAL : AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ h k A B A') :
    ∃ B', AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ h k A' B' A := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `obtain ⟨hAB, P, Q, hQP, hA'⟩ := hAL`; `hψp : ψ p ≠ 0`; `c := (ψ p)^(k+1) ≠ 0`.
2. `hPQ : P * Q = 1 := mul_eq_one_comm.mp hQP`.
3. `hBA : B * A = c • 1`: from `A * (c⁻¹ • B) = 1` (`Matrix.mul_smul`, `hAB`, `smul_smul`, `inv_mul_cancel₀`) and `mul_eq_one_comm`, then rescale.
4. `refine ⟨P * A * Q, ?_, Q, P, hPQ, ?_⟩`: `A' * (P * A * Q) = P * B * Q * P * A * Q = P * (B * A) * Q = c • (P * Q) = c • 1` (`Matrix.mul_assoc`, `hQP`, `hBA`, `Matrix.mul_smul`, `Matrix.smul_mul`); `A = Q * (P * A * Q) * P` (`hQP`, `Matrix.mul_assoc`, `Matrix.one_mul`, `Matrix.mul_one`).

- **Mathlib/project lemmas needed**: `mul_eq_one_comm`, `Matrix.mul_smul`, `Matrix.smul_mul`, `smul_smul`, `inv_mul_cancel₀`, `Matrix.mul_assoc`
- **Sources**: `decomposition.md` R-b.
- **Generality decision**: Every level; general helper.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ConductorSlopes.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-R1] Cleanup `PhD/LWX/ConductorSlopes.lean`
- **Status**: done
- **File**: PhD/LWX/ConductorSlopes.lean
- **Depends on**: R1, R2, R3
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.ConductorSlopes` and `lake exe runLinter PhD.LWX.ConductorSlopes` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of ConductorSlopes clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [R4] `norm_pow_le_of_mem_roots_charpoly_matrixH`
- **Status**: done
- **File**: PhD/LWX/ConductorSlopes.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The classical eigenvalues at `ψ` have norm at least `‖p‖^{k+1}`** at level `h`: their
Atkin–Lehner partners are eigenvalues of `U_p` at the partner point, hence of norm at most
one (`norm_le_one_of_isRoot_charpoly_upMatrix`, general in `h`). -/
theorem norm_pow_le_of_mem_roots_charpoly_matrixH [Nonempty ι] [IsAlgClosed K]
    {ω ω' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' : K} {k : ℕ}
    (c : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ h k (c.matrix idx) B
      (c'.matrix idx))
    {x : K} (hx : x ∈ (c.matrix idx).charpoly.roots) :
    ‖(ψ (p : ℚ_[p])) ^ (k + 1)‖ ≤ ‖x‖ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `norm_pow_le_of_mem_roots_charpoly_matrix` (`StepThree.lean:415–436`) with `ClassicalDataH` and `norm_le_one_of_isRoot_charpoly_upMatrix idx c'.weight k _ (Polynomial.mem_roots'.1 hy).2` (general in `h`), `norm_roots_charpoly_atkinLehner hcne hAB hQP hA'`, `Multiset.mem_map`, `div_le_one`.

- **Mathlib/project lemmas needed**: `norm_le_one_of_isRoot_charpoly_upMatrix`, `norm_roots_charpoly_atkinLehner`, `det_ne_zero_of_mul_eq_smul'`, `Matrix.det_eq_prod_roots_charpoly`, `Multiset.mem_map`, `div_le_one`
- **Sources**: `lwx.txt:2336–2340`; `decomposition.md` R-c; `StepThree.lean:415–436`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ConductorSlopes.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [R5] `unitSlope_charpolyRev_matrix_leH`
- **Status**: done
- **File**: PhD/LWX/ConductorSlopes.lean
- **Depends on**: R4
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The classical slopes are at most `k+1`** at level `h` ([LWX, §4.2]: the `U_p`-slopes of
`S^D_{k+2}(K^pIw_{p^M}, ψ)`; derived from H1 and `‖U_p‖ ≤ 1`, never from classicality). -/
theorem unitSlope_charpolyRev_matrix_leH [Nonempty ι] [IsAlgClosed K]
    {ω ω' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' : K} {k : ℕ}
    (c : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ h k (c.matrix idx) B
      (c'.matrix idx)) {j : ℕ} (hj : j < Fintype.card ι * ((k + 1) * p ^ h)) :
    (newtonPolygon₀OfPowerSeries negLogNorm
        (((c.matrix idx).charpolyRev : Polynomial K) : PowerSeries K)).unitSlope j
      ≤ ((((k + 1 : ℕ) : ℝ) * (-Real.log ‖ψ p‖) : ℝ) : WithBotTop ℝ) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant `unitSlope_charpolyRev_matrix_le` (`StepThree.lean:437–500`) with `1 → h` (`Fintype.card_fin` on the level-`h` size, `coeff_charpolyRev_card`, `height_le_coeffVal`, `unitSlope_ne_top_of_height_natCast`, `exists_coe_of_ne_bot_of_ne_top`, `exists_evalT_eq_zero_of_unitSlope_eq`, `PowerSeries.evalT_coe`, `Matrix.roots_charpolyRev hA0`, R4 for `hlow`, `Real.log_le_log`, `Real.log_pow`, `linarith`).

- **Mathlib/project lemmas needed**: as listed; `Polynomial.isRestricted_toPowerSeries`, `isEntireNewtonPolygonOf_coeffVal`
- **Sources**: `decomposition.md` R-c; `StepThree.lean:437–500`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ConductorSlopes.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [R6] `specCharSeries_eq_mul_charpolyRevH`
- **Status**: done
- **File**: PhD/LWX/ConductorSlopes.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The Fredholm determinant at a level-`h` classical datum splits** as the complement factor
times the characteristic polynomial of the classical matrix
(`charPowerSeries_eq_mul_of_stable`, `charpolyRev_classicalCoordMatrix_eq_charpolyRev_upMatrix`,
and the seam `specCharSeries_ofCerts_eq_discHeckeCharPowerSeries`). -/
theorem specCharSeries_eq_mul_charpolyRevH [Nonempty ι]
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    {ω : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ : K} {k : ℕ}
    (c : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k) :
    specCharSeries (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (intHom ψ) T₀
      = charPowerSeries ((discHeckeBlockOp θG h ψ c.weight U hU vRep hvΔ idx uu).comp
          (1 - truncation (R := K) (classicalSupport p ι h k)))
        * (((c.matrix idx).charpolyRev : Polynomial K) : PowerSeries K) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Transplant the private `specCharSeries_eq_mul_charpolyRev` (`StepThree.lean:576–600`): `hst` from `mem_locPolyDegSubmoduleBlock_discHeckeBlockOp_of_isClassicalShape θG h … c.weight c.shape`; `hcomp := isCompactoid_discHeckeBlockOp θG h ψ c.weight U hU vRep hvΔ idx uu (haloRhoH_nonneg h T₀) (max_lt (haloRhoH_lt_one h T₀ c.hT) inv_lt_one_p) hshape`; `rw [specCharSeries_ofCerts_eq_discHeckeCharPowerSeries ψ hψ T₀ ω h θG U hU vRep hvΔ idx uu hp2 c.h0 c.h1 c.hT hshape, discHeckeCharPowerSeries, charPowerSeries_eq_mul_of_stable h k hcomp hst, charpolyRev_classicalCoordMatrix_eq_charpolyRev_upMatrix h k _ hst]`; `rfl` (`ClassicalDataH.matrix` unfolds to `classicalMatrix … = upMatrix … hst'` with `hst'` proof-irrelevant).

- **Mathlib/project lemmas needed**: `charPowerSeries_eq_mul_of_stable`, `charpolyRev_classicalCoordMatrix_eq_charpolyRev_upMatrix`, `specCharSeries_ofCerts_eq_discHeckeCharPowerSeries`, `isCompactoid_discHeckeBlockOp`
- **Sources**: `decomposition.md` R-d; `StepThree.lean:576–600`.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ConductorSlopes.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-R2] Cleanup `PhD/LWX/ConductorSlopes.lean`
- **Status**: done
- **File**: PhD/LWX/ConductorSlopes.lean
- **Depends on**: R4, R5, R6
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.ConductorSlopes` and `lake exe runLinter PhD.LWX.ConductorSlopes` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of ConductorSlopes clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [R7] `unitSlope_specCharSeries_eq_unitSlope_charpolyRev_matrixH`
- **Status**: done
- **File**: PhD/LWX/ConductorSlopes.lean
- **Depends on**: R5, R6, G-d
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The first `N = t(k+1)p^h` slopes of the Fredholm determinant at a level-`h` classical
datum are the slopes of the classical factor** ([LWX, §4.2]: "the `U_p`-slopes of
`S^D_{k+2}(K^pIw_{p^M}, ψ)` are `q²p^{−M}α̃_0, …, q²p^{−M}α̃_{(k+1)q^{−1}p^Mt−1}`"): the
classical slopes are `≤ k+1`, the complement's are `≥ k+1`
(`le_unitSlope_compl` at the theta target `d`), and the product polygon starts with the
smaller factor (`unitSlope_newtonPolygon₀OfPowerSeries_mul_of_forall_le`). -/
theorem unitSlope_specCharSeries_eq_unitSlope_charpolyRev_matrixH [Nonempty ι] [IsAlgClosed K]
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    (hdet : ∀ i t, (certM1 θG U hU vRep hvΔ uu i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p)
    {ω ω' ω₁ : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' T₁ : K} {k : ℕ}
    (c : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (d : TargetDataH c ω₁ T₁)
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ h k (c.matrix idx) B
      (c'.matrix idx)) {j : ℕ} (hj : j < Fintype.card ι * ((k + 1) * p ^ h)) :
    (newtonPolygon₀OfPowerSeries negLogNorm
        (specCharSeries (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (intHom ψ)
          T₀)).unitSlope j
      = (newtonPolygon₀OfPowerSeries negLogNorm
          (((c.matrix idx).charpolyRev : Polynomial K) : PowerSeries K)).unitSlope j := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `rw [specCharSeries_eq_mul_charpolyRevH idx hshape c]`; set `R := charPowerSeries (… .comp (1 - truncation …))`, `G := (c.matrix idx).charpolyRev`.
2. `hRres : ∀ c, 0 < c → IsRestricted c R` (`charPowerSeries_isEntire`, compactoid as in R6), `hGres` (`Polynomial.isRestricted_toPowerSeries`), `hR0 : coeff 0 R ≠ 0` (`charPowerSeries_coeff`, `charCoeff_zero`), `hG0` (`Polynomial.coeff_coe`, `Matrix.eval_charpolyRev`).
3. `hle : ∀ i, i < N → ∀ j, unitSlope_G i ≤ unitSlope_R j`: `(unitSlope_charpolyRev_matrix_leH idx c c' hAL hi).trans (le_unitSlope_compl θG h ψ U hU vRep hvΔ idx uu c.weight d.weight c.shape d.shape hdet (haloRhoH_nonneg h T₀) (max_lt (haloRhoH_lt_one h T₀ c.hT) inv_lt_one_p) hshape j)`.
4. `exact unitSlope_newtonPolygon₀OfPowerSeries_mul_of_forall_le hRres hGres hR0 hG0 hle hj`.

- **Mathlib/project lemmas needed**: `unitSlope_newtonPolygon₀OfPowerSeries_mul_of_forall_le` (`Product.lean:1366`), `le_unitSlope_compl` (`StepThree.lean:285`), `charPowerSeries_isEntire`, `charPowerSeries_coeff`, `charCoeff_zero`, `Matrix.eval_charpolyRev`
- **Sources**: `lwx.txt:2336–2340`; `decomposition.md` R-d.
- **Generality decision**: `[IsAlgClosed K]` (R5), `hdet` (through `le_unitSlope_compl`).
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ConductorSlopes.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [R8] `toReal_unitSlope_charpolyRev_reflect`
- **Status**: done
- **File**: PhD/LWX/ConductorSlopes.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **[LWX, Prop 3.22] in sorted-slope form**: if the characteristic roots of `A'` are
`c/x` for the roots `x` of `A` (with multiplicity), then the `(n−1−i)`-th unit slope of
`det(1 − X·A')` is `v(c)` minus the `i`-th unit slope of `det(1 − X·A)`.  Counting roots in
balls (`faceRight_eq_card_roots_le_self`, `faceLeft_eq_card_roots_lt_self`, `roots_charpolyRev`):
`faceRight_{A'} σ = n − faceLeft_A (v(c) − σ)`, and the face API of `Face.lean` turns that into
the reflection of the unit slopes. -/
theorem toReal_unitSlope_charpolyRev_reflect [IsAlgClosed K] {n : Type*} [Fintype n]
    [DecidableEq n] {A A' : Matrix n n K} {c : K} (hc : c ≠ 0) (hA : A.det ≠ 0)
    (hroots : A'.charpoly.roots = A.charpoly.roots.map (fun x => c / x)) {i : ℕ}
    (hi : i < Fintype.card n) :
    NewtonPolygon.toReal ((newtonPolygon₀OfPowerSeries negLogNorm
        ((A'.charpolyRev : Polynomial K) : PowerSeries K)).unitSlope (Fintype.card n - 1 - i))
      = -Real.log ‖c‖ - NewtonPolygon.toReal ((newtonPolygon₀OfPowerSeries negLogNorm
          ((A.charpolyRev : Polynomial K) : PowerSeries K)).unitSlope i) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. Setup: `f := A.charpolyRev`, `f' := A'.charpolyRev`, `hf0 : f.coeff 0 = 1`, `hf'0` (`Polynomial.coeff_zero_eq_eval_zero`, `Matrix.eval_charpolyRev`); `hA' : A'.det ≠ 0` (`Matrix.det_eq_prod_roots_charpoly`, `hroots`, `Multiset.prod_map_div`-free: every `c / x ≠ 0`); `n := Fintype.card n`; `hdeg : f.natDegree = n`, `hdeg'` (`coeff_charpolyRev_card`, `Polynomial.natDegree_eq_of_le_of_coeff_ne_zero`/`charpolyRev_natDegree`?) and `hcard : f.roots.card = n` (`Polynomial.natDegree_eq_card_roots (IsAlgClosed.splits f)`).
2. `hroots' : f'.roots = f.roots.map (fun y => y / c)`: `Matrix.roots_charpolyRev hA'`, `hroots`, `Matrix.roots_charpolyRev hA`, `Multiset.map_map`, `inv_div`/`div_inv_eq_mul` bookkeeping.
3. `hcount : ∀ σ, (NP f').faceRight σ = n - (NP f).faceLeft (-Real.log ‖c‖ - σ)`: `faceRight_eq_card_roots_le_self f' hf'0 σ`, `faceLeft_eq_card_roots_lt_self f hf0 _`, `hroots'`, `Multiset.filter_map`, `Multiset.card_map`, and `‖y/c‖ ≤ e^σ ↔ ¬ (‖y‖ < e^{−log‖c‖−σ})` (`norm_div`, `div_le_iff₀`, `Real.exp_sub`, `Real.exp_log`), then `Multiset.card_filter + card_filter_not = card` (`Multiset.filter_add_not`/`Multiset.card_add`).
4. `hsu : (NP f').SlopesUnbounded`, `hsu'` (`slopesUnbounded_newtonPolygon₀OfPowerSeries`); real-valuedness: `unitSlope_ne_top_of_lt_natDegree hf0 (i < n)` and for `f'` at `n − 1 − i < n`; `unitSlope_ne_bot` (`isEntireNewtonPolygonOf_coeffVal`).
5. For every `σ : ℝ`: `unitSlope_{f'}(n−1−i) ≤ σ ↔ n−1−i < faceRight_{f'} σ` (`unitSlope_le_of_lt_faceRight`, `lt_unitSlope_of_faceRight_le hsu` + `not_le`) `↔ faceLeft_f τ ≤ i` (arithmetic with `hcount`, `faceLeft ≤ n` from the card bound, `omega`) `↔ τ ≤ unitSlope_f i` (`le_unitSlope_of_faceLeft_le hsu'`, `faceLeft_le_of_le_unitSlope`).
6. Extract reals `m := toReal (unitSlope_f i)`, `m' := toReal (unitSlope_{f'} (n−1−i))` (`coe_toReal_eq_self`) and conclude `m' = −log‖c‖ − m` by `le_antisymm` from step 5 at `σ := −log‖c‖ − m` and `σ := m'`.

- **Mathlib/project lemmas needed**: `faceRight_eq_card_roots_le_self`, `faceLeft_eq_card_roots_lt_self` (`RootFaces.lean:439, 452`), `unitSlope_ne_top_of_lt_natDegree` (`RootFaces.lean:92`), `unitSlope_le_of_lt_faceRight`, `lt_unitSlope_of_faceRight_le`, `le_unitSlope_of_faceLeft_le`, `faceLeft_le_of_le_unitSlope` (`Face.lean:293–320`), `slopesUnbounded_newtonPolygon₀OfPowerSeries`, `Matrix.roots_charpolyRev` (`CharpolyPairing.lean:157`), `Polynomial.natDegree_eq_card_roots`, `IsAlgClosed.splits`, `Multiset.filter_map`, `Multiset.card_map`, `Multiset.filter_add_not`, `coe_toReal_eq_self` (`Face.lean:53`), `Real.exp_sub`, `Real.exp_log`, `norm_div`
- **Sources**: [LWX, Prop 3.22] `lwx.txt:1765` (sorted-slope form), `lwx.txt:2340–2350`; `decomposition.md` R-e.
- **Generality decision**: General matrices over an algebraically closed complete ultrametric field; no LWX-specific input.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ConductorSlopes.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [R9] `slopeRatio_add_slopeRatio_eq_of_atkinLehnerHypothesisH`
- **Status**: done
- **File**: PhD/LWX/ConductorSlopes.lean
- **Depends on**: R2, R3, R7, R8, T3, T4
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **[LWX, (4.2.5)'s input] at a pair of level-`h` classical data with targets**: for
`i < N = t(k+1)p^h`,
`slopeRatio ω' (N − 1 − i) + slopeRatio ω i = (k+1)·p^{h−1}(p−1)`.
The unit-band hypotheses are the level-`1` output at every vertex
(`hasUnitBand_of_atkinLehnerData`, one `k` at a time). -/
theorem slopeRatio_add_slopeRatio_eq_of_atkinLehnerHypothesisH [Nonempty ι] [IsAlgClosed K]
    (hh : 0 < h)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    (hdet : ∀ i t, (certM1 θG U hU vRep hvΔ uu i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p)
    (hM : (p ^ 2 - 1) * Fintype.card ι + 8 < 8 * (p ^ (h - 1) * (p - 1)))
    {ω ω' ω₁ ω₁' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' T₁ T₁' : K} {k : ℕ}
    (c : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (d : TargetDataH c ω₁ T₁) (d' : TargetDataH c' ω₁' T₁')
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ h k (c.matrix idx) B
      (c'.matrix idx))
    (hband : ∀ n, HasUnitBand (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω n)
    (hband' : ∀ n, HasUnitBand (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω' n)
    {i : ℕ} (hi : i < Fintype.card ι * ((k + 1) * p ^ h)) :
    slopeRatio (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω'
          (Fintype.card ι * ((k + 1) * p ^ h) - 1 - i)
        + slopeRatio (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω i
      = ((k + 1 : ℕ) : ℝ) * ((p ^ (h - 1) * (p - 1) : ℕ) : ℝ) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `N := Fintype.card ι * ((k+1) * p^h)`; `hi' : N - 1 - i < N` (`omega`); `hAL' := atkinLehnerHypothesis_symm ψ hAL` (for the partner's slope bounds); `hv : -Real.log ‖T₀‖ = -Real.log ‖T₀'‖` (`c.norm_eq hh c'`); `hvpos : 0 < -Real.log ‖T₀‖` (`Real.log_neg` from `c.h0.trans?`… `‖T₀‖ < 1`, `‖T₀‖ > 0`).
2. Slope readings: `hread := unitSlope_discHeckeCharPowerSeries_eq_slopeRatio ψ hψ T₀ ω θG U hU vRep hvΔ idx uu h hp2 c.h0 c.h1 c.hT (c.inv_pow_lt_norm_pow hh hM) hshape hband i` and the partner's at `N - 1 - i`; rewrite each through the seam (`← specCharSeries_ofCerts_eq_discHeckeCharPowerSeries …`, as in `SlopesSeam.lean:155–159`) so both are about `specCharSeries`.
3. Identification: `unitSlope_specCharSeries_eq_unitSlope_charpolyRev_matrixH idx hshape hdet c c' d hAL hi` and, at the partner, `… c' c d' hAL' hi'`.
4. Reflection: `toReal_unitSlope_charpolyRev_reflect (pow_ne_zero _ hψp) hA0 (roots_charpoly_of_atkinLehnerHypothesis h k hAL') …`? — careful with the direction: `roots_charpoly_of_atkinLehnerHypothesis h k hAL : A'.charpoly.roots = A.charpoly.roots.map (c / ·)` with `A = c.matrix idx`, `A' = c'.matrix idx`; so R8 with `A := c.matrix idx`, `A' := c'.matrix idx`, `Fintype.card (Fin N) = N` (`Fintype.card_fin`), `hA0 : (c.matrix idx).det ≠ 0` (`det_ne_zero_of_mul_eq_smul'`).
5. Combine in `ℝ`: from 2–4, `(-Real.log ‖T₀'‖) * r'_{N−1−i} = -Real.log ‖(ψ p)^(k+1)‖ - (-Real.log ‖T₀‖) * r_i` (`WithBotTop.coe_inj`, `NewtonPolygon.toReal_coe`); `norm_pow`, `Real.log_pow`; `hv`; `c.mul_neg_log_norm_eq` (`e * v = -Real.log ‖ψ p‖`); divide by `v` (`mul_left_cancel₀ hvpos.ne'` / `field_simp`), `push_cast`, `ring`/`linarith`.

- **Mathlib/project lemmas needed**: `unitSlope_discHeckeCharPowerSeries_eq_slopeRatio` (`SlopesSeam.lean:145`), `specCharSeries_ofCerts_eq_discHeckeCharPowerSeries`, `roots_charpoly_of_atkinLehnerHypothesis` (`AtkinLehnerInst.lean`), `WithBotTop.coe_inj`, `NewtonPolygon.toReal_coe`, `Real.log_pow`, `Real.log_neg`?, `mul_left_cancel₀`
- **Sources**: [LWX, §4.2] `lwx.txt:2322–2350`; `decomposition.md` R-f.
- **Generality decision**: Abstract in the data; `hband`, `hband'` are genuine hypotheses (design decision 9).
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ConductorSlopes.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-R3] Cleanup `PhD/LWX/ConductorSlopes.lean`
- **Status**: done
- **File**: PhD/LWX/ConductorSlopes.lean
- **Depends on**: R7, R8, R9
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.ConductorSlopes` and `lake exe runLinter PhD.LWX.ConductorSlopes` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of ConductorSlopes clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [R10] `hasUnitBand_of_atkinLehnerData`
- **Status**: done
- **File**: PhD/LWX/ConductorSlopes.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **Row 1 of the dependency ledger closed at level `1`**: the touching hypothesis at
`n_{k+1}` with no hypothesis left, granted the adelic data
(`hasUnitBand_of_atkinLehnerHypothesis` at `classicalData` and its partner, with H1 from
`atkinLehnerHypothesis_of_atkinLehnerData`). -/
theorem hasUnitBand_of_atkinLehnerData [Nonempty ι] (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K} (hζ : IsPrimitiveRoot ζ p) (k : ℕ)
    (D : AtkinLehnerData θG ψ U Γ (nebCharK ψ ω k ζ))
    (hfin : (((Quotient.mk'' : G → RightCosets U) ''
      (({upEltD θG ψ U D} : Set G) * (U : Set G))) : Set (RightCosets U)).Finite)
    (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range (vRepD θG ψ U D))
      (((Quotient.mk'' : G → RightCosets U) ''
        (({upEltD θG ψ U D} : Set G) * (U : Set G))) : Set (RightCosets U)))
    (hvinj : Function.Injective (vRepD θG ψ U D))
    (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i, AutomorphicFunction.stabilizerAtSlash Γ U (c i) = ⊥)
    (idx : ι → Fin p → ι) (uu : ι → Fin p → U) (d : ι → Fin p → G) (hd : ∀ i t, d i t ∈ Γ)
    (hfact : ∀ i t, c i * (vRepD θG ψ U D t)⁻¹ = d i t * c (idx i t) * (uu i t : G))
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU (vRepD θG ψ U D)
      (vRepD_mem_levelM1 θG ψ U D) uu i t)).IsUpShape) :
    HasUnitBand (UpDatum.ofCerts θG U hU (vRepD θG ψ U D) (vRepD_mem_levelM1 θG ψ U D) idx uu
      hshape) ω (k + 1) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`exact hasUnitBand_of_atkinLehnerHypothesis θG ψ U hU (vRepD θG ψ U D) (vRepD_mem_levelM1 θG ψ U D) idx uu hp2 hψ hshape (classicalData ψ ω θG U hU (vRepD θG ψ U D) (vRepD_mem_levelM1 θG ψ U D) uu hp2 hψ hζ (norm_natCast_p ψ hψ) k) (classicalData ψ (partnerChar p ω k) θG U hU (vRepD θG ψ U D) (vRepD_mem_levelM1 θG ψ U D) uu hp2 hψ hζ.inv (norm_natCast_p ψ hψ) k) (atkinLehnerHypothesis_of_atkinLehnerData θG ψ U hU k ω hp2 hψ hζ (norm_natCast_p ψ hψ) D hfin hv hvinj c hc hstab idx uu d hd hfact)` (the body of `degX_succ_of_atkinLehnerData`, `AtkinLehnerIdentity.lean:649–655`, minus the degree step).

- **Mathlib/project lemmas needed**: `hasUnitBand_of_atkinLehnerHypothesis` (`Touching.lean:772`), `atkinLehnerHypothesis_of_atkinLehnerData` (`AtkinLehnerIdentity.lean:528`), `classicalData`, `norm_natCast_p`
- **Sources**: Ledger row 1, `.mathlib-quality/lwx-stepone/FINDINGS.md:187–195`; `decomposition.md` R-g.
- **Generality decision**: Level `1`; one `k` at a time (design decision 9).
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ConductorSlopes.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [R11] `hasUnitBand_of_atkinLehnerFamily`
- **Status**: done
- **File**: PhD/LWX/ConductorSlopes.lean
- **Depends on**: R10, F-a (the structures, no sorry)
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
include hfin hv hvinj c hc hstab d hd hfact in
/-- **Row 1 of the dependency ledger closed**: the unit-band hypothesis at **every** vertex and
**every** disc, granted the adelic data at every classical weight of conductor `p²`
(`hasUnitBand_zero` at `n = 0`, `hasUnitBand_of_atkinLehnerData` at `F.toData ω k` for
`n = k + 1`; the `UpDatum` is the same for every `(ω, k)` by `vRepD_toData`). -/
theorem hasUnitBand_of_atkinLehnerFamily [Nonempty ι] (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ₁ : IsPrimitiveRoot ζ₁ p) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
    HasUnitBand (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
      hshape) ω n := by
  sorry
```

- **Depends on (declarations)**: `AtkinLehnerFamily.toData`, `vRepD_toData`, `upEltD_toData`

**Proof sketch**:
1. `rcases n with _ | k`.
2. `n = 0`: `exact hasUnitBand_zero _ ω`.
3. `n = k + 1`: `exact hasUnitBand_of_atkinLehnerData θG ψ U hU ω hp2 hψ hζ₁ k (AtkinLehnerFamily.toData θG ψ U F ω k) hfin hv hvinj c hc hstab idx uu d hd hfact hshape` — the hypotheses are stated for `upEltF`/`vRepF` and expected at `upEltD (AtkinLehnerFamily.toData θG ψ U F ω k)`/`vRepD (AtkinLehnerFamily.toData θG ψ U F ω k)`, which are the same terms by `upEltD_toData`, `vRepD_toData` (`rfl`); if `exact` does not unfold, `simpa only [upEltD_toData, vRepD_toData] using hasUnitBand_of_atkinLehnerData …` or `show` the goal with `vRepD (AtkinLehnerFamily.toData θG ψ U F ω k)`.

- **Mathlib/project lemmas needed**: `hasUnitBand_zero` (`Vertices.lean:80`)
- **Sources**: Ledger row 1; `decomposition.md` R-h.
- **Generality decision**: Every disc `ω`, every vertex `n`; `[Nonempty ι]` and `hζ₁` through R10.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ConductorSlopes.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [R12] `unitSlope_discHeckeCharPowerSeries_eq_slopeRatio_of_atkinLehnerFamily`
- **Status**: done
- **File**: PhD/LWX/ConductorSlopes.lean
- **Depends on**: R11
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
include hfin hv hvinj c hc hstab d hd hfact in
/-- **[LWX, Thm 1.5 (1.5.1)] for the genuine `U_p`, with no hypothesis left**: at every halo
point of the slope-reading region and every analyticity level, every slope of `det(1 − X·U_p)`
is `v(T₀)` times a `T`-free ratio (`unitSlope_discHeckeCharPowerSeries_eq_slopeRatio` with the
unit band supplied by `hasUnitBand_of_atkinLehnerFamily`). -/
theorem unitSlope_discHeckeCharPowerSeries_eq_slopeRatio_of_atkinLehnerFamily [Nonempty ι]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ₁ : IsPrimitiveRoot ζ₁ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {T₀ : K} (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1)
    (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹)
    (hκ : (p : ℝ)⁻¹ ^ 8 < ‖T₀‖ ^ ((p ^ 2 - 1) * Fintype.card ι + 8)) (j : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm
          (discHeckeCharPowerSeries θG h ψ (haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT) U hU
            (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu)).unitSlope j
      = (((-Real.log ‖T₀‖)
          * slopeRatio (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F)
              idx uu hshape) ω j : ℝ) : WithBotTop ℝ) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`exact unitSlope_discHeckeCharPowerSeries_eq_slopeRatio ψ hψ T₀ ω θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu h hp2 h0 h1 hT hκ hshape (fun n => hasUnitBand_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape hp2 hψ hζ₁ ω n) j` — check the argument order of `unitSlope_discHeckeCharPowerSeries_eq_slopeRatio` (`SlopesSeam.lean:145`: `ψ hψ T₀ ω θ U hU vRep hvΔ idx u h hp2 h0 h1 hT hκ hshape hband j`) and of R11 (section variables `θG ψ U hU idx uu F` then the included `hfin … hfact`, then `hshape`).

- **Mathlib/project lemmas needed**: `unitSlope_discHeckeCharPowerSeries_eq_slopeRatio` (`SlopesSeam.lean:145`)
- **Sources**: [LWX, Thm 1.5 (1.5.1)] `lwx.txt:175–180`; `decomposition.md` R-h.
- **Generality decision**: Every halo point of the region at every level `h`; unconditional.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ConductorSlopes.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-R4] Cleanup `PhD/LWX/ConductorSlopes.lean`
- **Status**: done
- **File**: PhD/LWX/ConductorSlopes.lean
- **Depends on**: R10, R11, R12
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.ConductorSlopes` and `lake exe runLinter PhD.LWX.ConductorSlopes` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of ConductorSlopes clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-ALL-2] `/cleanup-all` before the milestone R13
- **Status**: done
- **File**: all files of this board
- **Depends on**: every ticket before R13
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup-all` over the nine modules of this board before the milestone R13: cross-file naming consistency, dead helpers, docstrings of the H-definitions, `lake exe runLinter` on every module; full `lake build PhD` green.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of all nine modules clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [R13] `slopeRatio_add_slopeRatio_partnerChar_of_atkinLehnerFamilyH` **[MILESTONE]**
- **Status**: done
- **File**: PhD/LWX/ConductorSlopes.lean
- **Depends on**: R9, R11, I15, G5, F-a
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- **[LWX, §4.2]'s displayed relation, with no hypothesis left**
("α̃_{(k+1)q^{−1}p^Mt−1−i}(ψ⁻¹|_Δ·ω₀^k) = (k+1)q^{−2}p^M − α̃_i(ψ|_Δ·ω₀^k)", `lwx.txt:2345–2350`):
at conductor `p^{h+1}`, for `i < N = t(k+1)p^h`,
`slopeRatio (ω⁻¹ω₀^{2k}) (N − 1 − i) + slopeRatio ω i = (k+1)·p^{h−1}(p−1)`
(`slopeRatio_add_slopeRatio_eq_of_atkinLehnerHypothesisH` at the classical points of the level-`h`
family, with the unit bands from the level-`1` family). -/
theorem slopeRatio_add_slopeRatio_partnerChar_of_atkinLehnerFamilyH [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h) (hζ₁ : IsPrimitiveRoot ζ₁ p)
    (hζ : IsPrimitiveRoot ζ (p ^ h))
    (hM : (p ^ 2 - 1) * Fintype.card ι + 8 < 8 * (p ^ (h - 1) * (p - 1)))
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) {i : ℕ} (hi : i < Fintype.card ι * ((k + 1) * p ^ h)) :
    slopeRatio (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (partnerChar p ω k) (Fintype.card ι * ((k + 1) * p ^ h) - 1 - i)
        + slopeRatio (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx
          uu hshape) ω i
      = ((k + 1 : ℕ) : ℝ) * ((p ^ (h - 1) * (p - 1) : ℕ) : ℝ) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`exact slopeRatio_add_slopeRatio_eq_of_atkinLehnerHypothesisH idx hh hshape hdet hM (classicalDataH ψ ω θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) uu hp2 hψ hh hζ (norm_natCast_p ψ hψ) k) (classicalDataH ψ (partnerChar p ω k) θG U hU (vRepF …) (vRepF_mem_levelM1 …) uu hp2 hψ hh hζ.inv (norm_natCast_p ψ hψ) k) (targetData_classicalPointH ψ ω θG U hU (vRepF …) (…) uu hp2 hψ hh hζ (norm_natCast_p ψ hψ) k) (targetData_classicalPointH ψ (partnerChar p ω k) θG U hU (vRepF …) (…) uu hp2 hψ hh hζ.inv (norm_natCast_p ψ hψ) k) (atkinLehnerHypothesis_of_atkinLehnerDataH θG ψ U hU h k ω hp2 hψ hh hζ (norm_natCast_p ψ hψ) (AtkinLehnerFamilyH.toDataH θG ψ U F X ω k) hfin hv hvinj c hc hstab idx uu d hd hfact) (hasUnitBand_of_atkinLehnerFamily … ω) (hasUnitBand_of_atkinLehnerFamily … (partnerChar p ω k)) hi`; the `hAL` term's type mentions `vRepDH θG ψ U h (AtkinLehnerFamilyH.toDataH θG ψ U F X ω k)` = `vRepF θG ψ U F` (`vRepDH_toDataH`, `rfl`) — `exact` should accept it; otherwise `simpa only [vRepDH_toDataH] using …`.

- **Mathlib/project lemmas needed**: —
- **Sources**: [LWX, §4.2] `lwx.txt:2345–2350`; `decomposition.md` R-i.
- **Generality decision**: **Milestone M2.** `#print axioms` must be standard.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ConductorSlopes.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files. B2 (repaired in place, logged in `b2_log.jsonl`): the skeleton's `include` list omitted the level-`h` family `X`; `X` added, nothing else changed.

### [R14] `slopeRatio_partnerChar_succ`
- **Status**: done
- **File**: PhD/LWX/ConductorSlopes.lean
- **Depends on**: R13
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- **[LWX, (4.2.5)]**: "α̃_{(k+2)q^{−1}p^Mt−1−i}(ψ⁻¹|_Δ·ω₀^{k+2}) = α̃_{(k+1)q^{−1}p^Mt−1−i}(ψ⁻¹|_Δ·ω₀^k)
+ q^{−2}p^M" (`lwx.txt:2353–2355`) — the displayed relation at `(ω, k)` and at `(ω, k+1)`,
subtracted. -/
theorem slopeRatio_partnerChar_succ [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h) (hζ₁ : IsPrimitiveRoot ζ₁ p)
    (hζ : IsPrimitiveRoot ζ (p ^ h))
    (hM : (p ^ 2 - 1) * Fintype.card ι + 8 < 8 * (p ^ (h - 1) * (p - 1)))
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) {i : ℕ} (hi : i < Fintype.card ι * ((k + 1) * p ^ h)) :
    slopeRatio (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (partnerChar p ω (k + 1)) (Fintype.card ι * ((k + 2) * p ^ h) - 1 - i)
      = slopeRatio (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx
          uu hshape) (partnerChar p ω k) (Fintype.card ι * ((k + 1) * p ^ h) - 1 - i)
        + ((p ^ (h - 1) * (p - 1) : ℕ) : ℝ) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `hi' : i < Fintype.card ι * ((k + 2) * p ^ h)` from `hi` (`Nat.lt_of_lt_of_le`, `Nat.mul_le_mul_left`, `omega`-free: `gcongr`).
2. `h1 := slopeRatio_add_slopeRatio_partnerChar_of_atkinLehnerFamilyH … ω k hi`, `h2 := … ω (k + 1) hi'`.
3. `push_cast at h1 h2 ⊢; linarith` (the `(k + 1 + 1 : ℕ)` cast).

- **Mathlib/project lemmas needed**: `linarith`, `push_cast`
- **Sources**: [LWX, (4.2.5)] `lwx.txt:2353–2355`; `decomposition.md` R-j.
- **Generality decision**: Every `i < N_k` (wider than [LWX]'s `i ≤ q⁻¹p^Mt − 1`).
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ConductorSlopes.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files. B2 (repaired in place, logged in `b2_log.jsonl`): the skeleton's `include` list omitted the level-`h` family `X`; `X` added, nothing else changed.

### [R15] `slopeRatio_mul_teichChar_sq`
- **Status**: done
- **File**: PhD/LWX/ConductorSlopes.lean
- **Depends on**: R14, F2, F3
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- **[LWX, Thm 1.5, (1.5.2)] at the polygon level** — (4.2.6), `lwx.txt:2356–2360`:
"α̃_{j+q^{−1}p^Mt}(ωω₀²) = α̃_j(ω) + q^{−2}p^M for any j ≥ 0".  With `slopeRatio = ϕ(q)·α̃`,
`M = h + 1`, `q = p`: `slopeRatio (ωω₀²) (j + p^h t) = slopeRatio ω j + p^{h−1}(p−1)`
(`slopeRatio_partnerChar_succ` at the disc `ω⁻¹ω₀^{2k}` with `k = j / (p^h t)`,
`partnerChar_invChar_mul_teichChar_pow`, `partnerChar_succ`). -/
theorem slopeRatio_mul_teichChar_sq [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h) (hζ₁ : IsPrimitiveRoot ζ₁ p)
    (hζ : IsPrimitiveRoot ζ (p ^ h))
    (hM : (p ^ 2 - 1) * Fintype.card ι + 8 < 8 * (p ^ (h - 1) * (p - 1)))
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (j : ℕ) :
    slopeRatio (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (ω * teichChar p ^ 2) (j + p ^ h * Fintype.card ι)
      = slopeRatio (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx
          uu hshape) ω j + ((p ^ (h - 1) * (p - 1) : ℕ) : ℝ) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `set T := p ^ h * Fintype.card ι`; `hT : 0 < T` (`Nat.pos_pow_of_pos`, `Fintype.card_pos`); `set k := j / T`.
2. `hj : j < Fintype.card ι * ((k + 1) * p ^ h)`: from `Nat.lt_div_mul_add hT : j < j / T * T + T` and `Fintype.card ι * ((k + 1) * p ^ h) = k * T + T` (`ring`).
3. `hk : j ≤ Fintype.card ι * ((k + 1) * p ^ h) - 1` (`omega`); `set i := Fintype.card ι * ((k + 1) * p ^ h) - 1 - j`; `hi : i < Fintype.card ι * ((k + 1) * p ^ h)` (`omega`).
4. `have h45 := slopeRatio_partnerChar_succ … (invChar ω * teichChar p ^ (2 * k)) k hi`.
5. `rw [partnerChar_succ, partnerChar_invChar_mul_teichChar_pow] at h45`; rewrite the indices: `Fintype.card ι * ((k + 1) * p ^ h) - 1 - i = j` and `Fintype.card ι * ((k + 2) * p ^ h) - 1 - i = j + T` (both `omega` after `have : Fintype.card ι * ((k + 2) * p ^ h) = Fintype.card ι * ((k + 1) * p ^ h) + T := by ring`).
6. `exact h45` (modulo `mul_comm` in `T`'s spelling `p ^ h * Fintype.card ι`).

- **Mathlib/project lemmas needed**: `Nat.lt_div_mul_add`, `Fintype.card_pos`, `Nat.pos_pow_of_pos`, `omega`, `ring`
- **Sources**: [LWX, (4.2.6) = (1.5.2)] `lwx.txt:2356–2360`; `decomposition.md` R-j.
- **Generality decision**: Every disc `ω` and every `j`; the disc `invChar ω * teichChar p ^ (2k)` is the `ψ` of ‘Choose ψ so that ψ|_Δ·ω₀^k = ω’.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ConductorSlopes.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files. B2 (repaired in place, logged in `b2_log.jsonl`): the skeleton's `include` list omitted the level-`h` family `X`; `X` added, nothing else changed.

### [CLEANUP-R5] Cleanup `PhD/LWX/ConductorSlopes.lean`
- **Status**: done
- **File**: PhD/LWX/ConductorSlopes.lean
- **Depends on**: R13, R14, R15
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.ConductorSlopes` and `lake exe runLinter PhD.LWX.ConductorSlopes` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of ConductorSlopes clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [R16] `slopeRatio_mul_teichChar_pow`
- **Status**: done
- **File**: PhD/LWX/ConductorSlopes.lean
- **Depends on**: R15
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- (1.5.2) iterated `m` times. -/
theorem slopeRatio_mul_teichChar_pow [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h) (hζ₁ : IsPrimitiveRoot ζ₁ p)
    (hζ : IsPrimitiveRoot ζ (p ^ h))
    (hM : (p ^ 2 - 1) * Fintype.card ι + 8 < 8 * (p ^ (h - 1) * (p - 1)))
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (m j : ℕ) :
    slopeRatio (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (ω * teichChar p ^ (2 * m)) (j + m * (p ^ h * Fintype.card ι))
      = slopeRatio (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx
          uu hshape) ω j + (m : ℝ) * ((p ^ (h - 1) * (p - 1) : ℕ) : ℝ) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Induction on `m`: `zero`: `simp` (`pow_zero`, `mul_one`, `zero_mul`, `add_zero`, `Nat.cast_zero`); `succ`: `rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add, ← mul_assoc, show j + (m + 1) * T = (j + m * T) + T by ring, slopeRatio_mul_teichChar_sq … (ω * teichChar p ^ (2 * m)) (j + m * T), ih]; push_cast; ring`.

- **Mathlib/project lemmas needed**: `pow_add`, `mul_assoc`, `Nat.succ_mul`, `push_cast`
- **Sources**: `decomposition.md` R-k.
- **Generality decision**: —
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ConductorSlopes.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files. B2 (repaired in place, logged in `b2_log.jsonl`): the skeleton's `include` list omitted the level-`h` family `X`; `X` added, nothing else changed.

### [CLEANUP-ALL-3] `/cleanup-all` before the milestone R17
- **Status**: done
- **File**: all files of this board
- **Depends on**: every ticket before R17
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup-all` over the nine modules of this board before the milestone R17: cross-file naming consistency, dead helpers, docstrings of the H-definitions, `lake exe runLinter` on every module; full `lake build PhD` green.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of all nine modules clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [R17] `slopeRatio_add_period` **[MILESTONE]**
- **Status**: done
- **File**: PhD/LWX/ConductorSlopes.lean
- **Depends on**: R16, F4
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- **[LWX, Thm 1.5, second half] at the polygon level** (`lwx.txt:2361–2366`): "since
ω₀^{ϕ(q)} = 1, we have α̃_{j+(p−1)p^{M−1}t/2}(ω) = α̃_j(ω) + ϕ(q)p^M/(2q²). Therefore the sequence
α̃_0(ω), α̃_1(ω), … is the disjoint union of arithmetic progressions … which have common
difference ϕ(q)p^M/(2q²)."  Here: the slope ratios of every disc `ω` are periodic of period
`(p−1)/2·p^h t` up to the constant `(p−1)/2·p^{h−1}(p−1)`
(`slopeRatio_mul_teichChar_pow` at `m = (p−1)/2` and `teichChar_pow_sub_one`). -/
theorem slopeRatio_add_period [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h) (hζ₁ : IsPrimitiveRoot ζ₁ p)
    (hζ : IsPrimitiveRoot ζ (p ^ h))
    (hM : (p ^ 2 - 1) * Fintype.card ι + 8 < 8 * (p ^ (h - 1) * (p - 1)))
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (j : ℕ) :
    slopeRatio (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) ω (j + (p - 1) / 2 * (p ^ h * Fintype.card ι))
      = slopeRatio (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx
          uu hshape) ω j + (((p - 1) / 2 : ℕ) : ℝ) * ((p ^ (h - 1) * (p - 1) : ℕ) : ℝ) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `have hev : Even (p - 1)`: from `hp.out.eq_two_or_odd'` and `hp2` (`Nat.Odd.sub_odd`, `odd_one`).
2. `have h2 : 2 * ((p - 1) / 2) = p - 1 := Nat.two_mul_div_two_of_even hev`.
3. `have := slopeRatio_mul_teichChar_pow … ω ((p - 1) / 2) j`; `rw [h2, teichChar_pow_sub_one, mul_one] at this`; `exact this`.

- **Mathlib/project lemmas needed**: `Nat.two_mul_div_two_of_even`, `Nat.Prime.eq_two_or_odd'`, `Nat.Odd.sub_odd`, `teichChar_pow_sub_one`
- **Sources**: [LWX, Thm 1.5, second half] `lwx.txt:2361–2366`; `decomposition.md` R-k.
- **Generality decision**: **Milestone M3.** `#print axioms` must be standard.
- **Progress**: 2026-09-11: DONE — proved in the beastmode run (`PhD/LWX/ConductorSlopes.lean`); final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files. B2 (repaired in place, logged in `b2_log.jsonl`): the skeleton's `include` list omitted the level-`h` family `X`; `X` added, nothing else changed.

### [CLEANUP-R-FINAL] Cleanup `PhD/LWX/ConductorSlopes.lean` (final)
- **Status**: done
- **File**: PhD/LWX/ConductorSlopes.lean
- **Depends on**: R17 (and every earlier ticket of the file)
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.ConductorSlopes` and `lake exe runLinter PhD.LWX.ConductorSlopes` must be clean.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of ConductorSlopes clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.

### [CLEANUP-FINAL] `/cleanup-all`, the JL-audit addendum, and the hand-off
- **Status**: done
- **File**: all files of this board; `.mathlib-quality/lwx-stepone/JL-AUDIT.md`; `PhD.lean`
- **Depends on**: every other ticket
- **Parallel**: no
- **Type**: cleanup

Final `/cleanup-all` (every module linter-clean, `#print axioms` on the two milestones = `[propext, Classical.choice, Quot.sound]`), then: (1) append to `.mathlib-quality/lwx-stepone/JL-AUDIT.md` the addendum "Prop 3.22 at every conductor `p^{h+1}`, `h ≥ 1`, avoided concretely (`atkinLehnerHypothesis_of_atkinLehnerDataH`); the slope identification of [LWX, §4.2] done without Prop 2.15"; (2) change the `PhD.lean` comment of the `lwx-conductor` block to "(complete, sorry-free)"; (3) update `.mathlib-quality/lwx-stepone/FINDINGS.md` ledger row 1 to "closed at level 1 (`hasUnitBand_of_atkinLehnerData`)" and row 3 to "the polygon-level input `slopeRatio_add_slopeRatio_partnerChar_of_atkinLehnerDataH` proved; the ψ-varying bookkeeping (4.2.5)–(4.2.6) remains"; (4) record slack hypotheses found (`_hx`) in this board's Summary.

- **Progress**: 2026-09-11: DONE — inline cleanup: `lake build` of AtkinLehnerFamily clean (no warnings), `lake exe runLinter` no finding in the board files, no unused simp args, `omit … in` added where the unused-section-variable linter asked; final gate 2026-09-11: nine-module build clean (3829 jobs, no warnings), 0 sorry, std axioms, runLinter no finding in board files.
