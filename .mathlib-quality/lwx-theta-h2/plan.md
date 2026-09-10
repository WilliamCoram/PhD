# Development Plan — `lwx-theta-h2` (H2 discharged; the theta target at the classical points)

**BOARD PATH: `.mathlib-quality/lwx-theta-h2/`.**  The default `.mathlib-quality/` board is the
completed NewtonPolygons project — never touch it.  A parallel run owns `.mathlib-quality/qmf/`
and its `beastmode_active` sentinel — never touch that either.  Every `/beastmode` run must name
this board path explicitly.  Planned 2026-09-10, immediately after `lwx-theta` closed.

## STATUS: COMPLETE (2026-09-10)

Planned and executed the same day.  All 70 tickets are done; `PhD/LWX/ThetaExact.lean`,
`PhD/LWX/TargetPoint.lean` and `PhD/LWX/DegreeFormula.lean` are **sorry-free**, `lake build PhD`
is green, `lake exe runLinter` is clean on all three, and `#print axioms` on every headline is
`[propext, Classical.choice, Quot.sound]`.

**Milestone**: `LWX.degX_succ_classicalPoint` — [LWX, Thm 1.3]'s degree formula at the classical
points, **granted H1 alone**.  H2 (`IsThetaExact`) is discharged by
`LWX.isThetaExact_classicalData`; `TargetData` is inhabited by `LWX.targetData_classicalPoint`
(gap **AG-ζ** closed).  Two general lemmas were relocated upstream by CLEANUP-A-FINAL:
`TateFredholm.matrixCoeff_truncation` → `PhD/TateFredholm/Matrix.lean`,
`TateFredholm.charPowerSeries_smul` → `PhD/TateFredholm/Riesz.lean`.  See `tickets.md`'s Summary
for the two engineering traps this run recorded.

## Goal

The completed `lwx-theta` board proved [LWX, Thm 1.3]'s degree formula `LWX.degX_succ` granted
two hypotheses: **H1** (`AtkinLehnerHypothesis`, [LWX, Prop 3.22]) and **H2** (`IsThetaExact`,
the determinant form of the theta sequence's right-exactness).  It also left `TargetData` — the
package Step III needs of the theta target `(−k−2, ψ)` — without an inhabitant.  This board does
the two things that were ranked first when the user asked what to develop next:

1. **Discharge H2** from the classical shapes of the two weights: `LWX.isThetaExact_of_isClassicalShape`
   and, at a classical datum with its target, `LWX.isThetaExact_classicalData`.
2. **Construct `TargetData` at the classical points** of `ClassicalPoint.lean`:
   `LWX.targetData_classicalPoint`, at the halo point `T_{(−k−2,ψ)} = ζ·exp(−p(k+2)) − 1` with the
   nebentypus `ω·ω₀^{−2k−2}` (`LWX.targetChar`), including the identification of the nebentypus
   constants — the gap the previous board called **AG-ζ**.

**Deliverable**: `LWX.degX_succ_classicalPoint` — the degree formula
`deg X_{k+1,ω} = r_ord(ω') + r_ord(ω·ω₀^{−2k−2})` at the classical points, granted **H1 only**
(asserted at the classical point of nebentypus `ω` and its Atkin–Lehner partner of nebentypus
`ω'`).

**Out of scope, deliberately**: H1 itself (`PhD/Test/AtkinLehnerIdentity.lean`, board
`lwx-stepone`); identifying the partner's nebentypus `ω' = ω⁻¹ω₀^{2k}` (the other half of the
old gap AG-ω₀; [LWX] `lwx.txt:2040–2048`); [LWX, Thm 1.5]'s second half; the old tickets `B8`,
`T-AG5`.

## Jacquet–Langlands dependencies (standing requirement)

**The per-result audit is `.mathlib-quality/lwx-stepone/JL-AUDIT.md`; read it before working any
ticket.**  For this board:

- **Part A (H2) imports no Jacquet–Langlands.**  [LWX] cites the exact sequence to [Jo11]
  (locally analytic BGG), `lwx.txt:2049`; the audit's §"The other hard input" already records
  that this is "not a Jacquet–Langlands issue" and asks for "a direct argument there [on the disc
  model] … before importing BGG machinery".  That is what Part A is: the intertwining
  `θ^{k+1}∘U_p = p^{k+1}U_p'∘θ^{k+1}` is Buzzard's elementary Hecke relation
  (`bu04.txt:1093–1096`, already proved as `thetaBlock_comp_discHeckeBlockOp_of_isClassicalShape`),
  and everything else is linear algebra of principal minors.  Neither [Jo11] nor exactness of
  spaces is imported: only the determinant identity that `IsThetaExact` states.
- **Part B imports no Jacquet–Langlands.**  It is the arithmetic of `p`-adic characters
  ([LWX, Notation 2.1 and §2.1], `lwx.txt:413–433`, `456–470`) at explicit points.
- **H1 remains the only hypothesis** of the deliverable, exactly as in the audit's item 1.

An addendum recording Part A's route has been appended to `JL-AUDIT.md`.

## References

- [LWX] Liu–Wan–Xiao, *The eigencurve over the boundary of weight space*, arXiv:1412.2584v4 —
  `.mathlib-quality/tate-riesz/references/lwx.txt`.  Used: Notation 2.1 (`lwx.txt:413–433`),
  §2.1's `m`-locally-analytic extension formula (`456–463`) and the definition of classical
  characters `(k, ψ)` (`467–470`), §3.23's classical points (`1794–1798`) and Step III's exact
  sequence and degree count (`2049–2076`).
- [Bu04] Buzzard, *On p-adic families of automorphic forms* —
  `.mathlib-quality/lwx-stepone/references/bu04.txt`.  Used: §7's Hecke relation
  `[UηU]θ^{1−k} = |ν(η)|^{k−1}θ^{1−k}[UηU]` (`bu04.txt:1093–1096`) and Prop 4's kernel
  characterisation (`1103–1105`, `1111–1114`).
- Boards: `.mathlib-quality/lwx-theta/` (`plan.md`, `decomposition.md`, `tickets.md`,
  `b2_log.jsonl`) for everything this board builds on.

## Mathlib and project inventory (verified by `#check` on 2026-09-10)

Project, consumed as-is:
- `TateFredholm.charPowerSeries_eq_of_diag_intertwine` (`PhD/TateFredholm/Conjugation.lean:85`)
  — **the whole content of H2**, already in the project (found during planning; an earlier
  draft of this plan re-proved it under the name `charPowerSeries_eq_of_diag_conj` — deleted).
- `TateFredholm.charPowerSeries_comm` (`Fredholm.lean:773`), `charCoeff_smul` (`Riesz.lean:1514`),
  `IsCompactoid.comp_right` (`Matrix.lean:550`), `IsCompactoid.smul` (`Riesz.lean:694`),
  `matrixCoeff_comp` (`Matrix.lean:84`), `ext_matrixCoeff` (`Matrix.lean:66`), `matrixCoeff_one`
  (`Riesz.lean:729`), `matrixCoeff_blockMap`/`blockMap_comp`/`blockMap_id`
  (`BlockMap.lean:82,127,92`), `ofCoeffs`/`ofCoeffs_apply`/`matrixCoeff_ofCoeffs`
  (`GenFun.lean:178–191`), `truncation_apply` (`Matrix.lean:260`).
- `LWX.thetaBlock_comp_discHeckeBlockOp_of_isClassicalShape` (`StepThree.lean:205`),
  `LWX.isCompactoid_discHeckeBlockOp` (`DiscForms.lean:240`), `LWX.thetaBlock`,
  `LWX.thetaOne`, `LWX.matrixCoeff_thetaOne`, `LWX.blockMap_apply_prod`,
  `LWX.classicalSupport`/`mem_classicalSupport_iff` (`Touching.lean:305–309`),
  `LWX.haloRhoH_nonneg`/`haloRhoH_lt_one` (`HaloWeightH.lean:789,807`).
- `LWX.classicalPoint` and its six lemmas (`ClassicalPoint.lean`), `LWX.mk_choose_natCast_mul_pow`,
  `LWX.autFactor_haloWeightH` (`HaloWeightH.lean`), `LWX.haloCharFunH_psi` (`HaloWeightH.lean:731`),
  `LWX.specialize_univChar` (`Specialize.lean:217`), `LWX.oneAddPow_natCast`,
  `LWX.continuous_oneAddPow_intHom` (`PowSubOne.lean:50,67`), `LWX.teichRes`, `teichRes_one`,
  `teichRes_mul`, `teichRes_toZMod` (`HaloWeight.lean:128–181`), `LWX.oneUnitPart`,
  `norm_oneUnitPart_sub_one_le` (`UnitsLog.lean:193–195`), `LWX.logQuot`, `coe_logQuot`
  (`IntegralModel.lean:147–154`), `LWX.map_padicLog` (`HaloWeight.lean:452`),
  `LWX.PadicExpLog.{padicExp_add, padicExp_natCast_mul, padicExp_padicLog, padicLog_padicExp,
  norm_padicExp_sub_one_le}` (`PadicExpLog.lean`; all take `h3 : ‖p‖ < 1` **first**, then `hp2`),
  `LWX.M1.coe_toLocalMat_d` (`IntegralModel.lean:308`), `LWX.coe_discConjK` (`DiscModel.lean:333`).

Mathlib: `Ring.add_choose_eq` (Vandermonde), `Ring.choose_zero_ite`, `Ring.choose_natCast`,
`PowerSeries.coeff_mul`, `PowerSeries.coeff_rescale`, `PadicInt.denseRange_natCast`,
`DenseRange.equalizer`, `MonoidHom.{mul_apply, inv_apply, pow_apply}`, `Int.cast_natCast`,
`Nat.descFactorial_pos`, `isUnit_iff_ne_zero`, `ContinuousLinearMap.{comp_assoc, smul_comp,
comp_smul, one_def, comp_id}`, `LipschitzWith.of_dist_le_mul`.

**Nothing new is needed from mathlib.**  Two small general lemmas are stated locally
(`matrixCoeff_truncation`, `charPowerSeries_smul`) with a cleanup ticket to move them upstream.

## File structure

| File | Content | Board part |
|---|---|---|
| `PhD/LWX/ThetaExact.lean` (new) | shift/section/diagonal decomposition of `θ^{k+1}`; the determinant identity from an intertwining; `isThetaExact_of_isClassicalShape`, `isThetaExact_classicalData` | A |
| `PhD/LWX/TargetPoint.lean` (new) | `teichChar`, `targetChar`, `weightPoint` (all `s ∈ ℤ`), negative-exponent binomial series, the target shape, AG-ζ, `targetData_classicalPoint` | B |
| `PhD/LWX/DegreeFormula.lean` (new) | `degX_succ_of_targetData`, `degX_succ_classicalPoint` | assembly |

No existing file is edited except `PhD.lean` (imports, done) and, in the final cleanup, the two
relocations noted above.

## Design decisions

1. **H2 is proved at the level of Fredholm determinants, not of spaces.**  `θ^{k+1} = D∘σ` with
   `D` a diagonal whose inverse is unbounded; `θ` is not surjective at a fixed radius, and no
   exactness is claimed.  The intertwining composed with the section `τ` gives
   `D∘(σUτ) = (p^{k+1}U')∘D`, a *diagonal intertwining* of matrix coefficients by the units
   `(j+1)⋯(j+k+1)`; `charPowerSeries_eq_of_diag_intertwine` turns that into equality of all
   principal minors.  This is exactly [LWX]'s consequence ("the dimension of slope zero subspace
   of `S^{D,†}_{(−k−2,ψ)}`", read on the characteristic series) without [Jo11].
2. **`weightPoint p s ζ` for `s ∈ ℤ`** rather than a separate `targetPoint`: the halo conditions
   and `s_1 = s` are proved once; `classicalPoint` is the case `s = k` (`weightPoint_natCast`).
   `ClassicalPoint.lean`'s proofs are not touched (protected); the new lemmas mirror them with
   `Int` casts.
3. **`targetChar ω k = ω * (teichChar ^ (2k+2))⁻¹`** in the commutative group of characters, with
   `teichChar` packaging the existing `teichRes`.  This is [LWX]'s `ω·ω₀^{−2k−2}`
   (`lwx.txt:2074–2076`).
4. **AG-ζ by density.**  The identity `(1+T_s)^{ψy}·exp(p(t−s)ψy) = (1+T_t)^{ψy}` is proved for
   all `y ∈ ℤ_p` by `PadicInt.denseRange_natCast.equalizer` (the pattern of `oneAddPow_pow_mul`),
   checked at `y = n` where both sides are honest powers.  No `map_padicExp` is needed (none
   exists): the one-unit part is recovered as `exp(p·ψℓ)` through `map_padicLog` and
   `padicExp_padicLog`.
5. **Generality**: Part A's core (`charPowerSeries_comp_one_sub_truncation_eq_rescale`) is stated
   for arbitrary operators `U U'` on the block model with the intertwining as hypothesis — the
   Hecke operators enter only in the last two lemmas.  Part B's continuity lemma is stated for
   `‖c‖ ≤ p⁻¹`, the natural disc.

## Dependency graph

```
A1 A2 (general)      A3 A4 A5 (defs) → A6 A7 A8 → A9 A10 A11 → A12 A13 A14 → A15 A16 A17 → A18 A19
                                                                         ↓
                                                    A20 → A21 ; A22 (uses A17, comm) → A23 (A21, A22, A2)
                                                                         ↓
                                                    A24 (A23 + StepThree intertwining + compactoid) → A25
B1 B2 (characters)   B3 → B4 → B5 B6 B7 ; B8 → B9 → B10 ;  B11 → B12 → B13 → B14 (B10, B13) → B15
B16 B17 B18 B19 (AG-ζ leaves) → B20 (B18, B7) → B21 (B1 B2 B3 B17 B19 B20) → B22 (B16 B21) → B23 (B15 B22)
D1 (A25 + degX_succ) → CLEANUP-ALL-1 → D2 (D1 + B23 + classicalData)   [MILESTONE]
```

## Cleanup cadence (algorithmic)

Per file, a `[CLEANUP-…]` ticket after every third proof/definition ticket and a final per-file
cleanup after the last; `CLEANUP-ALL-1` before the milestone `D2`; `CLEANUP-FINAL` last.  Cleanup
tickets are done **inline by the main agent** (user decision 2026-09-05: no Agent-dispatched
workers).  The `lake exe runLinter PhD.LWX.<Module>` gate is part of every cleanup.

## Planning-pass notes

- Prior-B2 consultation (`.mathlib-quality/lwx-theta/b2_log.jsonl`, `.mathlib-quality/b2_log.jsonl`):
  the five retired theta-equivariance statements (arbitrary finite part `ν`) are not re-created —
  every intertwining here goes through `IsClassicalShape`/`IsClassicalShape'` with explicit
  constants; the S7.10 pattern ("`∀ j` past the degree") does not occur (no slope statements).
- The one planning correction: `charPowerSeries_eq_of_diag_conj` was going to be a new file
  `PhD/TateFredholm/DiagConj.lean`; `Conjugation.lean` already has it. File deleted.
- `TargetData` is a `Prop`-valued structure (all fields are proofs), so its inhabitant is a
  `theorem`, `targetData_classicalPoint`, not a `def`.
