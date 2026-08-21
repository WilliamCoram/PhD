# Ticket Board — forms-headline (`.mathlib-quality/forms-headline/`)

**BOARD PATH: `.mathlib-quality/forms-headline/`.**  Workers: `/beastmode` with this path.

**Governing principle (user, 2026-08-19): no duplicate code.**  Where the fork
(`PhD/JacobsSlash/`) or `Algebraic.lean` re-implements something the general layer now
provides, the fork/Algebraic object is *replaced by* (defined as / rewritten through) the
general one — not identified with it by a bridge theorem.  Bridge theorems exist only as
temporary scaffolding inside a ticket and are deleted before the ticket is marked done.

The Lean skeleton is in place: every *new* statement below exists as a `:= by sorry`
declaration at the cited file:line (25 sorries; `lake build PhD.QMF.Weight.Algebraic
PhD.QMF.Weight.Compact PhD.QMF.Slash.Quaternionic PhD.JacobsSlash.U3.«9_EigenvaluesU3»
PhD.JacobsSlash.U3.«5_KappaWeight»` green).  Refactoring tickets (A′, B′, U) have existing
theorems as their spec: the set of *theorem statements* in the touched files must be
preserved (modulo the listed renames) with the duplicated *definitions* removed.
Convention: `Forms Γ θ κ U hU (χ := 1)`, `heckeOperator θ κ U hU hη h φ` (Γ, χ implicit
from φ), `κ.kappaSlash g`, `AnalyticWeight.ofExpansionData`.

## Summary
- **BOARD COMPLETE 2026-08-19** (single beastmode run): all 16 proof/refactor tickets + 7 cleanup
  tickets done; surface sorry-free on standard axioms, `runLinter` zero on the board surface;
  README §1/§3/§4/§5 + `PhD/JacobsSlash/PROGRESS.md` + memory updated.  Planning defects met on
  the way (recorded in the tickets): `AnalyticWeight` became data-carrying (T002 — the Prop/choice
  version could not state `genFun_jacobsWeight` for all `g`); `norm_det_toMatrix_certificate_le`
  needed `LevelBounds` + `hU` (T014); `Forms` got explicit `Γ` (T001).
- Total: 16 proof/refactor tickets + 7 cleanup tickets = 23
- Open: 0 | In Progress: 0 | Done: 23
- Deliverables (user order 2 → 3 → 1, now by replacement): **A′** Jacobs at the headline
  (fork's space/action/Hecke *are* `Forms`/`heckeOperator`; `jacobsWeightSeries` and the
  ODE cocycle deleted), **B′** classical inclusion (`algWeightSeries`/`twistedKappaLevelAction`
  replaced by `algWeight`/`kappaLevelSlashActionTwisted`; R6 theorems restated on `Forms`),
  **C** compactness of `U_ϖ` at general weight (new `Weight/Compact.lean`), **U** the fork's
  block layer (`evalU3`, `blockEntry`, `evalU3_heckeU3`, `isCompactoid_blockOpU3`) as the
  instance of C.
- Parallel capacity at start: 5 (T001 ∥ T002 ∥ T008 ∥ T009 ∥ T012)
- Cleanup cadence: per-file after every 3rd proof ticket + final per-file; CLEANUP-ALL-1
  before the C milestone T015; CLEANUP-FINAL last (7 ≥ ⌈16/3⌉ + finals).

## Dependency fronts

```
T001 (mem_forms_iff, _one) ──────────────────────────────────┐
T002 (A′-1: 4_KappaSlash + 5_KappaWeight slim, genFun_jacobsWeight) ─► T003 (A′-2: 6_Matrix via Forms/heckeOperator)
        ─► T004 (A′-3: 7_DiamondHecke) ─► T005 (A′-4: 7_Fredholm/8/9 + renames) ─► CLEANUP-1
T006 (B′-1: algWeight replaces algWeightSeries; twistedKappaLevelAction deleted) ─► T007 (B′-2: Forms statements) ─► CLEANUP-2
T008 (TateFredholm API) ─┐
T009 (det/entry bounds) ─► T010 (rowIntAt_genFun) ─► T011 (isCompactoid_kappaSlash ×4) ─► CLEANUP-3
T012 (blockProj/injective) ─► T013 (transport) ─┐
T014 (coset/det certificates) ───────────────────┴─► CLEANUP-4a ─► CLEANUP-ALL-1 ─► T015 (C ENDPOINT) ─► CLEANUP-4b
T016 (U: fork block layer := instance of C; needs T005, T013, T015) ─► CLEANUP-FINAL
```

---

## T001 `mem_forms_iff`, `mem_forms_iff_one`
- **Status**: done (2026-08-19, forms-headline beastmode) | **File**: PhD/QMF/Weight/Forms.lean:156, 166 | **Depends on**: none | **Parallel**: yes | **Type**: lemma (2 sorries)
- **Progress**: DONE — `mem_forms_iff` is `letI`×2 + `mem_levelSubmoduleSlash_iff' K hU` (the
  `Forms` = `levelSubmoduleSlash` `rfl` and the twist/comap unfoldings are definitional, as
  planned — `Iff.rfl`-shaped); `mem_forms_iff_one` = `rw [mem_forms_iff]; simp only
  [MonoidHom.one_apply, one_smul]`.  `lake build PhD.QMF.Weight.Forms` clean, axioms standard,
  runLinter zero.  Post-proof cleanup: ✓ (proofs are 3 and 2 lines; file-level /cleanup is
  CLEANUP-0a).
#### Statement
```lean
theorem mem_forms_iff (κ : AnalyticWeight UK S ρ) {U : Subgroup G}
    (hU : (U : Set G) ⊆ levelMonoidOf θ S) (χ : S →* Kˣ)
    {φ : AutomorphicFunction G Γ c(ℕ, K)} :
    φ ∈ Forms Γ θ κ U hU χ ↔
      ∀ (u : U) (g : G), φ (g * u)
        = χ ⟨θ u, hU u.2⟩ • κ.kappaSlash ⟨θ u, hU u.2⟩ (φ g) := by
  sorry
theorem mem_forms_iff_one (κ : AnalyticWeight UK S ρ) {U : Subgroup G}
    (hU : (U : Set G) ⊆ levelMonoidOf θ S) {φ : AutomorphicFunction G Γ c(ℕ, K)} :
    φ ∈ Forms Γ θ κ U hU ↔
      ∀ (u : U) (g : G), φ (g * u) = κ.kappaSlash ⟨θ u, hU u.2⟩ (φ g) := by
  sorry
```
#### Proof sketch
1. `letI := kappaLevelSlashActionTwisted θ κ χ; letI := kappaLevelSMulSlashClassTwisted θ κ χ`;
   `Forms` unfolds to `slashFixedPointsOfLE`, `rfl`-equal to `levelSubmoduleSlash K U hU`
   (verified at planning); `exact (AutomorphicFunction.mem_levelSubmoduleSlash_iff' K hU).trans (by …)`:
   the slash on the right is definitionally `(χ.comp (levelMonoidOfToS θ S)) ⟨u,_⟩ • κ.toWeightSeries.kappaSlash (…) (φ g)`
   (`RightSlashAction.twist_slash`, `comap_slash`, `AnalyticWeight.kappaSlash_def`, all `rfl`) — expect `Iff.rfl`/`simp only`.
2. `rw [mem_forms_iff]; simp only [MonoidHom.one_apply, one_smul]`.
#### Lemmas: `mem_levelSubmoduleSlash_iff'` (Slash/AutomorphicFunction.lean:90), `twist_slash`, `comap_slash`, `kappaSlash_def`, `MonoidHom.one_apply`, `one_smul`.
#### Sources: [Jacobs, Def 1.30, p. 19]; [Buzzard §10 p. 72] `(h.γ)(z,x) := n(cz+d,x)(v(det γ)(x))h(…)`.
#### Generality: the definitional unfolding, any `κ`, `χ`.

---

## Tranche A′ — the Jacobs endpoint at the headline, by replacement (README §5.2 + fork slim-down)

Answer to "do we still need `jacobsWeightSeries`?": **no** — `jacobsWeight :=
AnalyticWeight.ofExpansionData (jacobsExpansionData t ht)` is the honest character
(`jacobsChar : oneUnits K₃ ‖3‖ →* K₃ˣ`, `u ↦ uᵗ`) with its expansion datum
(`kappaSeries₂` column, `jacobsCol_rowDecay`, `hasSum_jacobsCol_unitPow`); its cocycle is
derived by evaluation injectivity.  `jacobsWeightSeries` (the hand-built datum whose cocycle
is the fork's ODE proof) and everything that exists only to feed/identify it is deleted here.
What stays in the fork is the Jacobs-specific content: the κ-column and its analytic facts,
`Σ₁(3)`/`Σ₁(9)`/`U₁(9)` and their bounds, class representatives, certificates, the
transcribed matrices and the slope computation.

### [T002] A′-1: slim `U3/4_KappaSlash.lean` + `U3/5_KappaWeight.lean`; `genFun_jacobsWeight`, `matrixCoeff_kappaSlash_jacobsWeight`
- **Status**: done (2026-08-19, forms-headline beastmode) | **Files**: PhD/JacobsSlash/U3/4_KappaColumn.lean (was 4_KappaSlash.lean), U3/5_KappaWeight.lean, U3/5_Factorisations.lean (import) | **Depends on**: none | **Parallel**: yes | **Type**: refactor + lemma (2 sorries)
- **Progress**: DONE — `4_KappaSlash.lean` (1569 lines) replaced by `4_KappaColumn.lean` (≈110 lines:
  valuation↔norm dictionary, the five `Σ₁(3)` bounds, `coeff_yCoeff_kappaSeries₂` with `QMF.yCoeff`);
  `5_KappaWeight.lean` rewritten (≈200 lines): `levelBounds_sigma1₃`, `jacobsCol_rowDecay` (private),
  `hasSum_jacobsCol_unitPow` (explicit column), `jacobsChar`, `jacobsExpansionData`, `jacobsWeight`,
  `yExtend_jacobsCol`, **`genFun_jacobsWeight`** (`rw [genFun, weightGenFun, yExtend_jacobsCol]`),
  **`matrixCoeff_kappaSlash_jacobsWeight`** (`rw [AnalyticWeight.matrixCoeff_kappaSlash, genFun_jacobsWeight]`).
  Deleted: `jacobsWeightSeries` + all bridge lemmas, the ODE cocycle and every duplicated calculus
  declaration (list in `renames.jsonl`).  `5_Factorisations` import switched.  `lake build` green on
  `5_Factorisations`, `5_KappaWeight`, `Weight.SlashAction`; no sorries in the new files; stale docstring
  references to `4_KappaSlash` fixed (`SlashAction`, `2_U3Data`, `1_Setting`, `7_DiamondHecke`).
  `6_Matrix`/`7_DiamondHecke`/`7_Fredholm` now fail to build until T003–T005 (expected).
  Post-proof cleanup: ✓ (new files are minimal; CLEANUP-1 runs /cleanup on them).
#### Statement (new)
```lean
theorem genFun_jacobsWeight (t : K₃) (ht : ‖t‖ < 1) (g : Matrix (Fin 2) (Fin 2) K₃) :
    (jacobsWeight t ht).toWeightSeries.genFun g = weightGenFun t g := by
  sorry
theorem matrixCoeff_kappaSlash_jacobsWeight (t : K₃) (ht : ‖t‖ < 1) (g : Sigma1₃) (m r : ℕ) :
    TateFredholm.matrixCoeff ((jacobsWeight t ht).kappaSlash g) m r
      = MvPowerSeries.coeff (TateFredholm.idx m r) (weightGenFun t g.1) := by
  sorry
```
**Design note (2026-08-19).**  `AnalyticWeight` now carries its expansion *datum*
(`expansion : ExpansionData S ρ U toChar`), so `(jacobsWeight t ht).toWeightSeries.col c d`
is `rfl`-equal to `PowerSeries.mk fun n => unitPow t d * (binomialCoeff t n * (c/d)^n)`
(`AnalyticWeight.toWeightSeries_col`, `ExpansionData.toWeightSeries_col`) and both lemmas are
definitional-plus-`yExtend_jacobsCol`; no `Classical.choice` is involved anywhere.
#### Refactor spec
1. **Delete from `4_KappaSlash.lean`** (duplicates of the general layer; map old → new):
   `CoeffInt`/`coeffInt_*` → `TateFredholm.CoeffInt` (WeightGenFun.lean:181–); `ShiftInt`/`shiftInt_*`
   → `TateFredholm.ShiftIntAt` (:257–); `coeffInt_weightGenFun`, `norm_coeff_weightGenFun_le_one`,
   `shiftInt_weightGenFun`, `tendsto_coeff_weightGenFun` → `QMF.WeightSeries.coeffInt_genFun`,
   `norm_coeff_genFun_le_one`, `shiftIntAt_genFun`, `tendsto_coeff_genFun` (Series.lean:291–335, at
   `(jacobsWeight t ht).toWeightSeries` via `genFun_jacobsWeight`); `kappaSlash`, `matrixCoeff_kappaSlash`,
   `kappaSlash_apply`, `kappaSlash_one`, `kappaSlash_mul`, `kappaSlashAction` → `(jacobsWeight t ht).kappaSlash`,
   `AnalyticWeight.matrixCoeff_kappaSlash`/`kappaSlash_one`/`kappaSlash_mul`/`kappaSlashAction` (Char.lean);
   `yCoeff`, `coeff_yCoeff`, `linX`, `numX`, `mobius`, `autFactor`, `yNum`, `quadSeries_eq_sub`, the `yDeg0/yDeg1`
   lemmas, `yCoeff_mul_*`, `yDeg0_inv`, `yCoeff_linSeries_inv`, `yCoeff_eq_zero_of_yDeg0`, `yCoeff_weightGenFun`,
   `linX_mul`, `numX_mul`, `linX_mul_eq`, `numX_mul_eq`, `mobius_mul`, `absSummable_linX(_inv)`, `compAn_linX`,
   `linX_inv_eq`, `absSummable_numX`, `compAn_numX`, `coeffLeOne_numX`, `coeffLeOne_linX_inv`, `coeffLeOne_mobius`,
   `constantCoeff_compAn_linX_ne_zero`, `compAn_mobius`, `compAn_mobius_mobius`, `constantCoeff_mobius`
   → `QMF.yCoeff`, `QMF.coeff_yCoeff`, `QMF.linX/numX/mobius`, `QMF.WeightSeries.autFactor`, and the
   same-named lemmas in `QMF.WeightSeries` (SlashAction.lean §YGrading, §Möbius; Series.lean); the **ODE cocycle**
   `linX_eq_scaled`, `derivative_linX`, `kappaCol_ode`, `derivative_numX`, `derivative_mobius`,
   `C_lower_left_mul_numX_add_det`, `lower_left_cocycle`, `kappaCol_mul_compAn_ode`,
   `constantCoeff_compAn_kappaCol`, `lower_right_cocycle`, `kappaCol_cocycle` → nothing (the cocycle is
   `ExpansionData.cocycle'` at `jacobsExpansionData`).
   **Keep** (Jacobs-specific): `adjParams` (check use), the valued↔norm dictionary lemmas if used
   elsewhere, `sigma1_lower_right_ne_zero`, `norm_sigma1_entry_le_one`, `norm_sigma1_lower_right(_sub_one_le)`,
   `norm_sigma1_lower_left_le`, `norm_sigma1_ratio_le`, `coeffLeOne_mobius_sigma1`, `absSummable_kappaCol(_sigma1)`
   only if `hasSum_jacobsCol_unitPow`/`jacobsExpansionData` use them (else delete), `kappaSeries₂_zero_one`,
   `coeff_yCoeff_kappaSeries₂`, `constantCoeff_yCoeff_kappaSeries₂`, `yCoeff_kappaSeries₂_eq`, `yDeg0_kappaSeries₂`
   (restated with `QMF.yCoeff`).  Rename the file to `U3/4_KappaColumn.lean` ("the Jacobs κ-column and
   the `Σ₁(3)` bounds") and record in `renames.jsonl`; update the two importers (`5_Factorisations`, `5_KappaWeight`).
2. **`5_KappaWeight.lean`**: delete `jacobsWeightSeries`, `jacobsWeightSeries_col`, `yExtend_jacobsCol`
   (fold into `genFun_jacobsExpansionData`'s proof), `genFun_jacobsWeightSeries`, `kappaSlash_eq_general`,
   `jacobsWeightSeries_eq_toWeightSeries`, `kappaSlash_eq_toWeightSeries`, `kappaSlash_eq_jacobsWeight`,
   `jacobsCol_cocycle` (and any lemma existing only to feed them).  Keep `unitPow`-facts, `jacobsCol_zero_one`,
   `jacobsCol_rowDecay`, `jacobsCol_absSummable` (if `hasSum_jacobsCol_unitPow` needs it), `hasSum_jacobsCol_unitPow`,
   `jacobsChar`, `jacobsChar_apply`, `jacobsExpansionData`, `jacobsWeight`, `jacobsWeight_toChar`.
   Prove `genFun_jacobsWeight`: `rw [QMF.WeightSeries.genFun, weightGenFun]`; the column
   `(jacobsWeight t ht).toWeightSeries.col c d = PowerSeries.mk fun n => unitPow t d * (binomialCoeff t n * (c/d)^n)`
   (`rfl`), and `yExtend` of it is `kappaSeries₂ t c d`
   (the old `yExtend_jacobsCol` proof: `MvPowerSeries.ext`, `coeff_yExtend`, `coeff_kappaSeries₂`, `split_ifs`).
   Prove `matrixCoeff_kappaSlash_jacobsWeight`: `rw [AnalyticWeight.matrixCoeff_kappaSlash, genFun_jacobsWeight]`.
3. `5_Factorisations.lean`: change `import …«4_KappaSlash»` to the renamed file (it uses only `weightGenFun`
   and `Σ₁`-bounds); build `5_Factorisations`, `5_KappaWeight` green.  (`6_Matrix`, `7_DiamondHecke` break until T003/T004.)
#### Lemmas: `QMF.WeightSeries.genFun` (Series.lean:221), `AnalyticWeight.toWeightSeries`, `ExpansionData.toWeightSeries_col`, `QMF.WeightSeries.coeff_yExtend`, `coeff_kappaSeries₂`.
#### Sources: [Jacobs, Def 1.27, p. 19] (the expansion of `κ(cz+d)`), [Jacobs, p. 29] (`κ(cx+d) = (cx+d)^t`).
#### Generality: Jacobs-specific by design; LOC: the file shrinks from 1569 to ≈400.

### [T003] A′-2: `U3/6_Matrix.lean` — `kappaForms`/`heckeU3` ARE `Forms`/`heckeOperator`
- **Status**: done (2026-08-19, forms-headline beastmode) | **File**: PhD/JacobsSlash/U3/6_Matrix.lean | **Depends on**: T001, T002 | **Parallel**: no | **Type**: refactor
- **Progress**: DONE — `levelMonoid1₃` abbrev of `levelMonoidOf`, `kappaForms`/`heckeU3` abbrevs of
  `Forms`/`heckeOperator`, `levelMonoid1₃ToSigma1₃`/`kappaLevelSlashAction`/`kappaLevelSMulSlashClass`
  deleted; `blockEntry` via `(jacobsWeight t ht).kappaSlash`; `matrixCoeff_blockEntry` via
  `matrixCoeff_kappaSlash_jacobsWeight`; `heckeU3_apply_classRep`/`eval_classRep_injective` with the
  general twisted instances (+ new simp lemma `Weight.kappaLevelSlashActionTwisted_slash`, `one_smul`).
  All theorem statements preserved; `6_Matrix` green.
#### Spec (definitions replaced; all theorem statements of the file preserved)
```lean
import PhD.JacobsSlash.U3.«5_KappaWeight»   -- new (prefix 6 ≥ 5+1 ✓)
-- delete: kappaLevelSlashAction, kappaLevelSMulSlashClass, levelMonoid1₃ToSigma1₃
-- keep:   levelMonoid1₃ (as `abbrev levelMonoid1₃ := Weight.levelMonoidOf (toMatrix ℚ D v₃) Sigma1₃`, rfl to today's),
--         U1_9_subset_levelMonoid1₃, eta3_mem_levelMonoid1₃, etaRep_mem_levelMonoid1₃
/-- `L(U₁(9), A₃)` [Jacobs, Def 1.30 at p = 3]: the headline `Forms` at the Jacobs weight. -/
noncomputable abbrev kappaForms (t : K₃) (ht : ‖t‖ < 1) :
    Submodule K₃ (AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) :=
  Weight.Forms (globalUnits ℚ D) (toMatrix ℚ D v₃) (jacobsWeight t ht) U1_9 U1_9_subset_levelMonoid1₃
/-- `U₃ = [U₁(9)·η₃·U₁(9)]`, the headline Hecke operator at the Jacobs weight. -/
noncomputable abbrev heckeU3 (t : K₃) (ht : ‖t‖ < 1) : kappaForms t ht →ₗ[K₃] kappaForms t ht :=
  Weight.heckeOperator (toMatrix ℚ D v₃) (jacobsWeight t ht) U1_9 U1_9_subset_levelMonoid1₃
    eta3_mem_levelMonoid1₃ finite_image_eta3
```
`blockEntry t ht i j := ∑ t' ∈ {t' | sigmaTable i t' = j}, (jacobsWeight t ht).kappaSlash ⟨toMatrix ℚ D v₃ ((uTable i t' : Dfx ℚ D) * etaRep t'), toMatrix_uTable_mul_etaRep_mem_sigma1₃ i t'⟩`
(same shape, general action).  Re-prove with the new definitions: `matrixCoeff_blockEntry`
(`matrixCoeff_kappaSlash_jacobsWeight` in place of the fork's `matrixCoeff_kappaSlash`), `blockEntry_eq_epsOp` (unchanged), `charPowerSeries_blockEntry_eq_U3MatrixOp`
(unchanged), `heckeU3_apply_classRep` (the recipe `heckeOperatorSlash_apply_rep` is
instance-agnostic; the coefficient slash is now `(1 : K₃ˣ) • (jacobsWeight t ht).kappaSlash (…)` — `one_smul`,
`twist_slash`, `comap_slash`), `eval_classRep_injective(')` (uses `slash_apply_mul`; `letI` now
`kappaLevelSlashActionTwisted (toMatrix ℚ D v₃) (jacobsWeight t ht) 1` + `kappaLevelSMulSlashClassTwisted`).
#### Lemmas: `Weight.mem_forms_iff_one` (T001), `twist_slash`, `comap_slash`, `one_smul`, `matrixCoeff_kappaSlash_jacobsWeight` (T002), `heckeOperatorSlash_apply_rep`.
#### Sources: [Jacobs, Def 1.30, 1.32; pp. 20–21, 28].
#### Generality: n/a (instantiation).  All 296 lines stay except the ~45 replaced.

### [T004] A′-3: `U3/7_DiamondHecke.lean` on the general yCoeff/Möbius API
- **Status**: done (2026-08-19, forms-headline beastmode) | **File**: PhD/JacobsSlash/U3/7_DiamondHecke.lean | **Depends on**: T003 | **Parallel**: with T006 | **Type**: refactor
- **Progress**: DONE — `coeff_weightGenFun_diagonal` (still `ht`-free) via the NEW general column
  identity `QMF.WeightSeries.yCoeff_yExtend_mul_inv` (SlashAction.lean; `yCoeff_genFun` is now its
  instance) + `kappaSeries₂_eq_yExtend` (4_KappaColumn); `kappaSlash_acting_eq_delta`,
  `heckeW_apply_classRep` with `(jacobsWeight t ht).kappaSlash`; `heckeW := Weight.heckeOperator … mu3`.
  Green.
#### Spec
Replace the fork names by the general ones (`open QMF` already): `linX/numX/mobius` → `QMF.linX/numX/mobius`
(Series.lean:136–144, same definitions); `autFactor t γ` → `(jacobsWeight t ht).toWeightSeries.autFactor γ`
(SlashAction.lean:351, `W.col (γ 1 0) (γ 1 1) * ((linX γ)⁻¹)^2` — the col is `PowerSeries.mk …`, `rfl`, whose `yCoeff`
facts are `coeff_yCoeff_kappaSeries₂`-shaped: restate `coeff_weightGenFun_diagonal`'s `hcol` via
`genFun_jacobsWeight` + `QMF.WeightSeries.yCoeff_genFun` (SlashAction.lean:372, the column identity
`yCoeff (W.genFun γ) r = W.autFactor γ * mobius γ ^ r`) in place of `yCoeff_weightGenFun`); `kappaSlash t ht` →
`(jacobsWeight t ht).kappaSlash`; `matrixCoeff_kappaSlash` → `matrixCoeff_kappaSlash_jacobsWeight`; the `letI := kappaSlashAction t ht` / `kappaLevelSlashAction t ht` →
`(jacobsWeight t ht).kappaSlashAction` / `Weight.kappaLevelSlashActionTwisted (toMatrix ℚ D v₃) (jacobsWeight t ht) 1`
(+ `kappaLevelSMulSlashClassTwisted`); `heckeW` := `Weight.heckeOperator … mu3_mem finite_image_mu3` (same shape
as `heckeU3`).  All theorem statements (`coeff_weightGenFun_diagonal`, `kappaSlash_acting_eq_delta`,
`heckeW_apply_classRep`, `heckeW_apply_classRep_eq_delta`, …) preserved up to these renames.
#### Lemmas: `QMF.WeightSeries.yCoeff_genFun`, `QMF.coeff_yCoeff`, `genFun_jacobsWeight`, `matrixCoeff_kappaSlash_jacobsWeight`.
#### Sources: [Jacobs, (2.1.10)–(2.1.13), p. 31–32].

### [T005] A′-4: `U3/7_Fredholm.lean`, `U3/8_HeckeSlopes.lean`, `U3/9_EigenvaluesU3.lean` instance names; `evalU3_eq_evalAtReps`; renames
- **Status**: done (2026-08-19, forms-headline beastmode) | **Files**: the three files + `.mathlib-quality/renames.jsonl`, `PhD/JacobsSlash/PROGRESS.md` | **Depends on**: T004 | **Parallel**: no | **Type**: refactor + lemma
- **Progress**: DONE — `7_Fredholm` instances migrated, `evalU3_eq_evalAtReps := rfl` (imports
  `Weight.Compact`); `8`/`9` needed no change; whole fork (`9_EigenvaluesU3`) green;
  `#print axioms exists_eigenvalue_U3_halfIntegral` standard.  `renames.jsonl` + `PROGRESS.md`
  updated.  The `isCompactoid_zero_clm` deletion is deferred to T008 (it needs the general
  `isCompactoid_zero`, a T008 sorry) — recorded there.
#### Spec
1. `7_Fredholm`: `letI := kappaSlashAction t ht` etc. → general instances (as T003/T004); `evalU3`, `bijective_evalU3`,
   `kappaFormsModelEquiv`, `evalU3_heckeU3`, `isCompactoid_blockOpU3`, `charPowerSeriesU3` keep their
   statements; add
   ```lean
   /-- `evalU3` is the general block-model evaluation at the class representatives. -/
   theorem evalU3_eq_evalAtReps (φ : kappaForms t ht) :
       evalU3 t ht φ = Weight.evalAtReps (toMatrix ℚ D v₃) (jacobsWeight t ht) U1_9
         U1_9_subset_levelMonoid1₃ 1 classRep φ := by
     sorry   -- both are `∑ i, cSpace.blockIncl i (φ (classRep i))`: `rfl` after unfolding, or `ext ⟨i, n⟩` + `blockProj_evalU3`/`blockProj_evalAtReps`
   ```
   (import `PhD.QMF.Weight.Compact`).  Statement is fixed here because it cannot be written before T003
   (`kappaForms` must be `Forms`); this is the one deviation from "every leaf pre-stated in the skeleton".
2. `8_HeckeSlopes`, `9_EigenvaluesU3`: only instance/name fixes if any (they consume `charPowerSeriesU3`,
   `kappaForms` by name — abbrev keeps them compiling; check `letI`s).
   `4_DiamondW`: delete the fork-local `isCompactoid_zero_clm` (4 uses) in favour of the general
   `TateFredholm.isCompactoid_zero` (T008) — the one remaining duplicate of general API in the root files.
3. Record every deleted/renamed declaration in `renames.jsonl` (old → new, scope public) and update
   `PROGRESS.md` (module map: `4_KappaColumn`, "weight/action layer = QMF.Weight"; the headline chain now
   reads `heckeU3 := Weight.heckeOperator …`).  Rebuild the whole fork (`9_EigenvaluesU3`) green; verify
   `#print axioms exists_eigenvalue_U3_halfIntegral` standard.
#### Sources: [Buzzard §9 p. 69] (`f ↦ (f(τ_λ))`).

### [CLEANUP-1] /cleanup on the A′ files (4_KappaColumn, 5_KappaWeight, 6_Matrix, 7_DiamondHecke, 7_Fredholm) — final per-file
- **Status**: done (2026-08-19, inline mode per the laweights-board precedent) | **Depends on**: T005 | **Type**: cleanup (also the cadence cleanup: 4 proof/refactor tickets on the fork).
- **Progress**: runLinter zero on `4_KappaColumn`, `5_KappaWeight`, `6_Matrix`, `7_DiamondHecke`,
  `7_Fredholm`, `Weight.Forms`, `Weight.SlashAction`; one finding fixed — the new
  `kappaLevelSlashActionTwisted_slash` was not in simp-normal form (simpNF linter), `@[simp]`
  dropped (it is used via `rw`/`simp only`).  No module warnings on the touched files apart from
  the upstream skeleton `sorry`s.  Docstrings present on every new declaration; `PROGRESS.md`
  module map updated in T005.

---

## Tranche B′ — the classical inclusion at the headline, by replacement (README §5.3)

### [T006] B′-1: `algWeight` replaces `algWeightSeries`; `twistedKappaLevelAction` deleted
- **Status**: done (2026-08-19, forms-headline beastmode) | **File**: PhD/QMF/Weight/Algebraic.lean | **Depends on**: T001 | **Parallel**: with T002 | **Type**: refactor
- **Progress**: DONE — `algExpansionData` standalone (polynomial column, `eval` via `show evalAt (linX g ^ (n+2)) z = _`),
  `algWeightSeries`/`algWeightSeries_col`/`algWeightSeries_eq_toWeightSeries`/`kappaSlash_algWeight` deleted,
  every use → `(algWeight hb n).toWeightSeries` (`autFactor_algWeight`, `algWeight_col` simp-normal on
  `.expansion.col`); `kappaLevel_hsmul`/`twistedKappaLevelAction`/`twistedKappaSMulSlash` deleted,
  `polyEmbed_slash_level` restated at `Weight.kappaLevelSlashActionTwisted θ (algWeight hb n) (detTwist ν)`.
  Green, runLinter zero (one simpNF fix).
#### Spec
1. Make `algExpansionData hb n` standalone (`col c d := (PowerSeries.C d + PowerSeries.C c * PowerSeries.X) ^ (n + 2)`,
   `rowDecay := norm_coeff_linear_pow_le …`, `eval` as today) and **delete `algWeightSeries`** (its polynomial
   cocycle is no longer needed: `algWeight := ⟨_, algExpansionData hb n⟩`).  Replace every
   `algWeightSeries hb n` by **`(algWeight hb n).toWeightSeries`** (its column is definitionally the polynomial —
   `AnalyticWeight` carries the datum — so every `rfl`/`hcol` step survives).  `algWeightSeries_col` →
   `algWeight_col`, `autFactor_algWeightSeries` → `autFactor_algWeight`, `algWeightSeries_eq_toWeightSeries` and
   `kappaSlash_algWeight` deleted (now `rfl`), `yCoeff`/`polySubmodule_stable`/`polyEmbed_slash` statements
   re-pointed; proofs unchanged in substance.
2. **Delete `kappaLevel_hsmul`, `twistedKappaLevelAction`, `twistedKappaSMulSlash`**; restate
   `polyEmbed_slash_level` with `letI := Weight.kappaLevelSlashActionTwisted θ (algWeight hb n) (detTwist ν)`
   (proof: `show polyEmbed n ν (P ∣ₛ …) = detTwist ν (…) • (algWeight hb n).kappaSlash (…) (polyEmbed n ν P)`;
   `exact polyEmbed_slash hb n ν …` at `(algWeight hb n).toWeightSeries`).
3. `classicalWeightAction`, `classicalWeightSMulSlash`, `classicalForms`, `classicalHeckeOperator` stay (the classical side).
   The three R6 theorems `classicalToOverconvergent_mem`, `heckeOperatorSlash_classicalToOverconvergent`,
   `mem_range_classicalToOverconvergent_iff` are **replaced** by T007's `Forms`-statements (delete them in T007
   once the new ones are proven; their proofs port: same `mapCoeff_*` lemmas, instance now the general one).
#### Sources: [Buzzard §11 p. 73]; R6 decision record (`.mathlib-quality/laweights/decomposition.md` §R6).
#### Generality: unchanged.

### [T007] B′-2: `map_classicalForms_le_forms`, `mem_map_classicalForms_iff`, `heckeOperator_mapCoeff_polyEmbed` — **B ENDPOINT**
- **Status**: done (2026-08-19, forms-headline beastmode) | **File**: PhD/QMF/Weight/Algebraic.lean | **Depends on**: T006 | **Parallel**: no | **Type**: theorem (3 sorries)
- **Progress**: DONE — `map_classicalForms_le_forms` (= R6's `classicalToOverconvergent_mem` proof,
  `mapCoeff_mem_levelSubmoduleSlash` + `polyEmbed_slash_level`), `mem_map_classicalForms_iff` (R6's
  `mem_range_…` proof with `mem_slashFixedPointsOfLE_iff`), `heckeOperator_mapCoeff_polyEmbed`
  (`heckeOperatorSlash_mapCoeff` + `subst (Subtype.ext hψ)`); the three R6 originals deleted.  Axioms
  standard; Algebraic.lean sorry-free.
#### Statement
```lean
theorem map_classicalForms_le_forms (θ : G →* Matrix (Fin 2) (Fin 2) K)
    (hb : LevelBounds (Sigma0' K γv hγv) ρ) (n : ℕ) (ν : Sigma0 K γv hγv →* Kˣ)
    {U : Subgroup G} (hU : (U : Set G) ⊆ Weight.levelMonoidOf θ (Sigma0' K γv hγv)) :
    (classicalForms (Γ := Γ) θ n ν U hU).map (AutomorphicFunction.mapCoeff (polyEmbed n ν))
      ≤ Weight.Forms Γ θ (algWeight hb n) U hU (detTwist ν) := by
  sorry
theorem mem_map_classicalForms_iff (θ) (hb) (n) (ν) {U} (hU) (ψ : AutomorphicFunction G Γ c(ℕ, K)) :
    ψ ∈ (classicalForms (Γ := Γ) θ n ν U hU).map (AutomorphicFunction.mapCoeff (polyEmbed n ν))
      ↔ ψ ∈ Weight.Forms Γ θ (algWeight hb n) U hU (detTwist ν) ∧ ∀ g : G, ψ g ∈ polySubmodule K n := by
  sorry
theorem heckeOperator_mapCoeff_polyEmbed (θ) (hb) (n) (ν) {U} (hU) {η : G} (hη) (h)
    (φ : classicalForms (Γ := Γ) θ n ν U hU) (ψ : Weight.Forms Γ θ (algWeight hb n) U hU (detTwist ν))
    (hψ : (ψ : AutomorphicFunction G Γ c(ℕ, K)) = AutomorphicFunction.mapCoeff (polyEmbed n ν) φ) :
    (Weight.heckeOperator θ (algWeight hb n) U hU hη h ψ : AutomorphicFunction G Γ c(ℕ, K))
      = AutomorphicFunction.mapCoeff (polyEmbed n ν)
          (classicalHeckeOperator θ n ν U hU hη h φ : AutomorphicFunction G Γ (WeightModule K n ν)) := by
  sorry
```
#### Proof sketch (the R6 proofs, re-targeted; then delete the R6 originals)
1. `rintro _ ⟨φ, hφ, rfl⟩`; `letI`s (classical + `kappaLevelSlashActionTwisted θ (algWeight hb n) (detTwist ν)`);
   `Forms` is `slashFixedPointsOfLE` = `levelSubmoduleSlash` (`rfl`): `exact AutomorphicFunction.mapCoeff_mem_levelSubmoduleSlash (polyEmbed n ν) (fun P u => polyEmbed_slash_level θ hb n ν P u) hU hφ`
   (Algebraic.lean:~676; this *is* `classicalToOverconvergent_mem`'s proof).
2. `Submodule.mem_map` + the R6 proof of `mem_range_classicalToOverconvergent_iff` verbatim (its two directions use
   `polyEmbed_mem_polySubmodule`, `polyEmbedEquiv`, `polyEmbed_slash_level`, `polyEmbed_injective`, `mem_levelSubmoduleSlash_iff`).
3. `AutomorphicFunction.heckeOperatorSlash_mapCoeff (polyEmbed n ν) (fun P u => polyEmbed_slash_level θ hb n ν P u) hU hη h φ`
   (Algebraic.lean:~697) gives the identity at the element `⟨mapCoeff … φ, _⟩`; `Subtype.ext hψ` identifies it with `ψ`.
   Then **delete** `classicalToOverconvergent_mem`, `heckeOperatorSlash_classicalToOverconvergent`, `mem_range_classicalToOverconvergent_iff`.
#### Lemmas: `mapCoeff_mem_levelSubmoduleSlash`, `heckeOperatorSlash_mapCoeff`, `polyEmbed_slash_level`, `polyEmbed_injective`, `polyEmbedEquiv_coe`, `Submodule.mem_map`.
#### Sources: [Buzzard §11 p. 73] "S^D_{k,w}(U) = L(U, L_{n,v}) ⊆ L(U, A_{κ,r}) = S^D_κ(U; r)"; [Jacobs, Def 1.32].
#### Generality: abstract `(G, θ)`, any `(n, ν)`, any `hb`.

### [CLEANUP-2] /cleanup PhD/QMF/Weight/Algebraic.lean (final) + README §3/§5 update
- **Status**: done (2026-08-19, inline mode) | **Depends on**: T007 | **Type**: cleanup
- **Progress**: runLinter zero on `Weight.Algebraic` (one simpNF fix: `algWeight_col` stated on
  `.expansion.col`); header "Main definitions/results" updated for `algWeight`, `classicalForms`,
  the three headline theorems; no module warnings beyond upstream skeleton sorries.

---

## Tranche C — compactness of `U_ϖ` at general weight (README §5.1)

### [T008] TateFredholm API: `isCompactoid_of_row_decay'`, `RowIntAt.mono`, `isCompactoid_zero`, `IsCompactoid.finset_sum`
- **Status**: done (2026-08-19, forms-headline beastmode) | **Files**: PhD/TateFredholm/GenFun.lean; WeightGenFun.lean; Matrix.lean (`isCompactoid_zero`, moved next to the `IsCompactoid` definition so `4_DiamondW`/`7_Fredholm` see it without importing Riesz); Riesz.lean (`IsCompactoid.finset_sum`) | **Depends on**: none | **Parallel**: yes | **Type**: lemma (API, 4 sorries)
- **Progress**: DONE — all four proven as sketched (`isCompactoid_of_row_decay'` with the `C`-nonnegativity
  read off `h j 0`; `RowIntAt.mono` via `pow_le_pow_left₀`; `isCompactoid_zero` by `rowNorm 0 = 0`;
  `finset_sum` by `Finset.induction_on` + `IsCompactoid.add`).  Fork's `isCompactoid_zero_clm` deleted
  (`4_DiamondW`, `7_Fredholm`: 12 uses → `isCompactoid_zero`).  Axioms standard; fork + Compact green.
  (runLinter on `Matrix.lean` reports two PRE-EXISTING unused `[DecidableEq J]` instances at
  `tendsto_matrixCoeff_column`/`matrixCoeff_sub`, lines 37/42 — not from this ticket; left for CLEANUP-3.)
#### Statement
```lean
theorem isCompactoid_of_row_decay' {u : c(ℕ, K) →L[K] c(ℕ, K)} {σ C : ℝ} (hσ0 : 0 ≤ σ)
    (hσ : σ < 1) (h : ∀ j i, ‖matrixCoeff u j i‖ ≤ C * σ ^ j) : IsCompactoid u := by sorry
lemma RowIntAt.mono {σ : ℝ} (hρ0 : 0 ≤ ρ) (hρσ : ρ ≤ σ) {φ : MvPowerSeries (Fin 2) K}
    (hφ : RowIntAt ρ φ) : RowIntAt σ φ := by sorry
theorem isCompactoid_zero : IsCompactoid (0 : c(I, R) →L[R] c(J, R)) := by sorry
theorem IsCompactoid.finset_sum [IsTate R] {ι : Type*} (s : Finset ι)
    {f : ι → c(I, R) →L[R] c(J, R)} (hf : ∀ i ∈ s, IsCompactoid (f i)) :
    IsCompactoid (∑ i ∈ s, f i) := by sorry
```
#### Proof sketch
1. Copy `isCompactoid_of_row_decay` (GenFun.lean:218–229) with `‖q‖ ↦ σ`: `hgeom` from `tendsto_pow_atTop_nhds_zero_of_lt_one hσ0 hσ`, `.const_mul C`, `Nat.cofinite_eq_atTop`; `hle j := Real.iSup_le (h j) (nonneg: from h j 0 and norm_nonneg)`; `tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgeom rowNorm_nonneg hle`.
2. `fun p => (hφ p).trans (pow_le_pow_left₀ hρ0 hρσ _)` (confirm name by `lean_loogle`).
3. (also: delete the fork's `JacobsSlash.isCompactoid_zero_clm` in `4_DiamondW.lean` (4 uses) in favour of
   this lemma — deferred here from T005.)  `unfold IsCompactoid rowNorm`; `matrixCoeff 0 j i = 0`; the `⨆` of `0` is `0` (`Real.iSup_le`/`ciSup_const` + `rowNorm_nonneg`); `tendsto_const_nhds`.
4. `classical; induction s using Finset.induction_on` with `isCompactoid_zero`, `Finset.sum_insert`, `IsCompactoid.add` (Riesz.lean:618).
#### Sources: [Jacobs, Cor 1.10, p. 10]; [Serre].

### [T009] `LevelBounds.norm_det_le_one`, `LevelBounds.norm_apply_zero_zero_le_of_norm_det_le`
- **Status**: done (2026-08-19, forms-headline beastmode) | **File**: PhD/QMF/Weight/Series.lean:136, 144 | **Depends on**: none | **Parallel**: yes | **Type**: lemma (2 sorries)
- **Progress**: DONE — both as sketched (`det_fin_two` + `sub_eq_add_neg` + `norm_add_le_max`;
  `‖a‖ = ‖a·d‖ = ‖det + b·c‖ ≤ max σ ρ`).  Series.lean now has the single remaining skeleton
  sorry `rowIntAt_genFun` (T010).
#### Statement
```lean
theorem LevelBounds.norm_det_le_one {S} {ρ : ℝ} (hb : LevelBounds S ρ) {g} (hg : g ∈ S) : ‖g.det‖ ≤ 1 := by sorry
theorem LevelBounds.norm_apply_zero_zero_le_of_norm_det_le {S} {ρ σ : ℝ} (hb : LevelBounds S ρ)
    (hρσ : ρ ≤ σ) {g} (hg : g ∈ S) (hdet : ‖g.det‖ ≤ σ) : ‖g 0 0‖ ≤ σ := by sorry
```
#### Proof sketch
1. `rw [Matrix.det_fin_two]`; `(IsUltrametricDist.norm_sub_le_max _ _).trans (max_le …)`, each product `≤ 1` by `norm_mul`, `mul_le_one₀ (hb.integral hg _ _) (norm_nonneg _) (hb.integral hg _ _)`.
2. `‖g 0 0‖ = ‖g 0 0 * g 1 1‖` (`hb.d_unit hg`); `g 0 0 * g 1 1 = g.det + g 0 1 * g 1 0` (`Matrix.det_fin_two`, `ring`); `IsUltrametricDist.norm_add_le_max`; `max_le hdet (…)` with `‖g 0 1 * g 1 0‖ ≤ 1 * ρ ≤ σ` (`hb.integral hg 0 1`, `hb.c_le hg`, `hρσ`).
#### Sources: [Buzzard, Lemma 12.2 proof, p. 79] ("det((x_δ)_p)/det(η_p) is a unit … factored through A_{κ,r|π|}").

### [T010] `WeightSeries.rowIntAt_genFun` (Jacobs Lemma 2.7's integrality)
- **Status**: done (2026-08-19, forms-headline beastmode) | **File**: PhD/QMF/Weight/Series.lean:~329 | **Depends on**: T008 | **Parallel**: with T009 | **Type**: theorem
- **Progress**: DONE exactly as sketched (`RowIntAt.mul`×2, `rowIntAt_yExtend … |>.mono`,
  `rowIntAt_linSeries … |>.inv`, `rowIntAt_quadSeries … |>.inv`).  Series.lean sorry-free.
#### Statement
```lean
theorem rowIntAt_genFun (W : WeightSeries S ρ) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ∈ S) {σ : ℝ} (hρσ : ρ ≤ σ) (ha : ‖g 0 0‖ ≤ σ) : RowIntAt σ (W.genFun g) := by sorry
```
#### Proof sketch
`hσ0 : 0 ≤ σ := W.bounds.rho_nonneg.trans hρσ`; `unfold genFun` (`yExtend col * linSeries⁻¹ * quadSeries⁻¹`, Series.lean:221);
`refine RowIntAt.mul hσ0 (RowIntAt.mul hσ0 ?_ ?_) ?_` — `(W.rowIntAt_yExtend hg).mono W.bounds.rho_nonneg hρσ`;
`(rowIntAt_linSeries hσ0 (W.bounds.integral hg 1 1) ((W.bounds.c_le hg).trans hρσ)).inv hσ0 (W.norm_constantCoeff_linSeries hg)`;
`(rowIntAt_quadSeries hσ0 (W.bounds.integral hg 1 1) ((W.bounds.c_le hg).trans hρσ) ha (W.bounds.integral hg 0 1)).inv hσ0 (W.norm_constantCoeff_quadSeries hg)`.
Mirror `coeffInt_genFun`/`shiftIntAt_genFun` (Series.lean:291–310).
#### Lemmas: `RowIntAt.mul` (WeightGenFun.lean:108), `RowIntAt.inv` (:123), `rowIntAt_linSeries` (:158), `rowIntAt_quadSeries` (:167), `rowIntAt_yExtend` (Series.lean:228), `norm_constantCoeff_linSeries/quadSeries` (:275/:282), `RowIntAt.mono` (T008).
#### Sources: [Jacobs, Lemma 2.7 proof, p. 30].

### [T011] `norm_matrixCoeff_kappaSlash_le`, `isCompactoid_kappaSlash`, `isCompactoid_kappaSlash_of_norm_det_le`, `AnalyticWeight.isCompactoid_kappaSlash` — **C headline (i)**
- **Status**: done (2026-08-19, forms-headline beastmode) | **Files**: PhD/QMF/Weight/SlashAction.lean; Char.lean | **Depends on**: T008, T009, T010 | **Parallel**: no | **Type**: theorem (4 sorries)
- **Progress**: DONE exactly as sketched: `norm_matrixCoeff_kappaSlash_le` (`matrixCoeff_kappaSlash` +
  `rowIntAt_genFun` at `idx j i`), `isCompactoid_kappaSlash` (`isCompactoid_of_row_decay' (C := 1)`),
  `_of_norm_det_le` (via `norm_apply_zero_zero_le_of_norm_det_le`), `AnalyticWeight.isCompactoid_kappaSlash`.
  **C headline (i) done**: `κ.kappaSlash g` compactoid for `‖det g‖ ≤ σ < 1`.  Axioms standard.
#### Statement
```lean
theorem norm_matrixCoeff_kappaSlash_le (W : WeightSeries S ρ) (g : S) {σ : ℝ} (hρσ : ρ ≤ σ) (ha : ‖g.1 0 0‖ ≤ σ) (j i : ℕ) :
    ‖matrixCoeff (W.kappaSlash g) j i‖ ≤ σ ^ j := by sorry
theorem isCompactoid_kappaSlash (W : WeightSeries S ρ) (g : S) {σ : ℝ} (hρσ : ρ ≤ σ) (hσ : σ < 1) (ha : ‖g.1 0 0‖ ≤ σ) :
    IsCompactoid (W.kappaSlash g) := by sorry
theorem isCompactoid_kappaSlash_of_norm_det_le (W : WeightSeries S ρ) (g : S) {σ : ℝ} (hρσ : ρ ≤ σ) (hσ : σ < 1) (hdet : ‖g.1.det‖ ≤ σ) :
    IsCompactoid (W.kappaSlash g) := by sorry
theorem AnalyticWeight.isCompactoid_kappaSlash (κ) (g : S) {σ : ℝ} (hρσ : ρ ≤ σ) (hσ : σ < 1) (hdet : ‖g.1.det‖ ≤ σ) :
    IsCompactoid (κ.kappaSlash g) := by sorry
```
#### Proof sketch
1. `rw [W.matrixCoeff_kappaSlash g j i]` (SlashAction.lean:364); `simpa [idx_apply_zero] using W.rowIntAt_genFun g.2 hρσ ha (idx j i)`.
2. `isCompactoid_of_row_decay' (C := 1) (W.bounds.rho_nonneg.trans hρσ) hσ (fun j i => by simpa using W.norm_matrixCoeff_kappaSlash_le g hρσ ha j i)`.
3. `W.isCompactoid_kappaSlash g hρσ hσ (W.bounds.norm_apply_zero_zero_le_of_norm_det_le hρσ g.2 hdet)`.
4. `κ.toWeightSeries.isCompactoid_kappaSlash_of_norm_det_le g hρσ hσ hdet` (`κ.kappaSlash g` is `rfl`).
#### Sources: [Jacobs, Lemma 2.7, p. 30]; [Jacobs, Cor 1.10]; [Buzzard, Lemma 12.2].

### [CLEANUP-3] /cleanup on the C engine files (Series, SlashAction, Char, TateFredholm/GenFun, WeightGenFun, Riesz — new decls only)
- **Status**: done (2026-08-19, inline mode) | **Depends on**: T011 | **Type**: cleanup
- **Progress**: runLinter on the closure: the only finding from this board's additions was
  `RowIntAt.mono`'s unused `[IsUltrametricDist K]` (fixed with `omit`); the remaining reports are
  PRE-EXISTING in `TateFredholm/Matrix.lean` (37–89, 415: unused `[DecidableEq J]`/instances on
  `tendsto_matrixCoeff_column`, `matrixCoeff_sub/_smul`, `rowNorm_nonneg`, …), `ModelSpace.lean`,
  `Tate.lean`, `Compact.lean` — older TateFredholm debt outside this board's scope (noted for the
  owner of those files; see `tatefredholm-eigen` board).  Series/SlashAction/Char: zero findings.

### [T012] `blockProj_evalAtReps`, `evalAtReps_injective`
- **Status**: done (2026-08-19, forms-headline beastmode) | **File**: PhD/QMF/Weight/Compact.lean:92, 99 | **Depends on**: none | **Parallel**: yes | **Type**: lemma (2 sorries)
- **Progress**: DONE as sketched (`blockProj_evalU3`'s simp set; injectivity via
  `bijective_evalAtRepsSlash K hU σ hσ |>.1` + `Subtype.ext` + `blockProj_evalAtReps`).
#### Statement
```lean
theorem blockProj_evalAtReps (c : ι → G) (φ : Forms Γ θ κ U hU χ) (i : ι) :
    cSpace.blockProj i (evalAtReps θ κ U hU χ c φ) = (φ : AutomorphicFunction G Γ c(ℕ, K)) (c i) := by sorry
theorem evalAtReps_injective [Fintype (DoubleCoset.Quotient (Γ : Set G) (U : Set G))]
    [DecidableEq (DoubleCoset.Quotient (Γ : Set G) (U : Set G))]
    (σ : DoubleCoset.Quotient (Γ : Set G) (U : Set G) → G)
    (hσ : ∀ q, (Quotient.mk'' (σ q) : DoubleCoset.Quotient (Γ : Set G) (U : Set G)) = q) :
    Function.Injective (evalAtReps (Γ := Γ) θ κ U hU χ σ) := by sorry
```
#### Proof sketch
1. As `blockProj_evalU3` (7_Fredholm.lean:59): `simp only [evalAtReps, LinearMap.coe_mk, AddHom.coe_mk, map_sum, cSpace.blockProj_blockIncl, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
2. `intro φ ψ h`; `letI`s; `refine (AutomorphicFunction.bijective_evalAtRepsSlash K hU σ hσ).1 ?_` (HeckeMatrix.lean:181; `Forms` = `slashFixedPointsOfLE` at these instances, `rfl`); `funext q; apply Subtype.ext`; `have := congrArg (cSpace.blockProj q) h; simpa only [blockProj_evalAtReps] using this`.
#### Sources: [Buzzard §9 p. 69] "f ∈ L(U,A) is determined by f(τ_λ)".

### [T013] `evalAtReps_heckeOperator` (transport, Jacobs pp. 20–21)
- **Status**: done (2026-08-19, forms-headline beastmode) | **File**: PhD/QMF/Weight/Compact.lean | **Depends on**: T012 | **Parallel**: with T014 | **Type**: theorem
- **Progress**: DONE — split as `heckeOperator_apply_rep` (the general `heckeU3_apply_classRep`:
  recipe + `kappaLevelSlashActionTwisted_slash` + `Units.smul_def` + `Finset.sum_fiberwise` +
  `heckeBlock` unfolding) and `evalAtReps_heckeOperator` (the general `evalU3_heckeU3`:
  `map_sum`, `blockOp_blockIncl`, `Finset.sum_comm`).  Green.
#### Statement — Compact.lean:128–143; conclusion
```lean
    evalAtReps θ κ U hU χ c (heckeOperator θ κ U hU hη h φ)
      = heckeBlockOp θ κ U hU χ vRep hvΔ idx u (evalAtReps θ κ U hU χ c φ) := by sorry
```
#### Proof sketch (mirror `evalU3_heckeU3` + `heckeU3_apply_classRep`)
`letI`s; reduce to blocks (`ext` on `c(ι × ℕ, K)` / `blockProj`); LHS block `i`: `blockProj_evalAtReps` then
`AutomorphicFunction.heckeOperatorSlash_apply_rep K hU hη h φ vRep hvΔ hv hvinj (c i) (fun t => c (idx i t)) (d i) (hd i) (u i) (hfact i) (fun t => mul_mem (hU (u i t).2) (hvΔ t))`
(HeckeMatrix.lean:57) gives `∑ t, φ (c (idx i t)) ∣ₛ ⟨u i t * vRep t, _⟩`, each slash `= (χ … : K) • κ.kappaSlash (…) (φ (c (idx i t)))`
(`twist_slash`, `comap_slash`, `Units.smul_def`); RHS: `heckeBlockOp = blockOp (heckeBlock …)`, `blockOp_blockIncl` (BlockOp.lean:631),
`blockProj_blockIncl`, unfold `heckeBlock`, regroup by `j = idx i t` (`Finset.sum_fiberwise`/`Finset.sum_filter`, `ContinuousLinearMap.sum_apply`, `smul_apply`).
#### Sources: [Jacobs pp. 20–21] "(U_pφ)(c_i) = Σ_t φ(c(i,t))‖_κ(u(i,t)v_t)_p … ε_{i,j}".  LOC ≈ 40.

### [T014] `exists_mul_eta_mul_of_bijOn`, `norm_det_toMatrix_certificate_le`
- **Status**: done (2026-08-19, forms-headline beastmode) | **File**: PhD/QMF/Weight/Compact.lean | **Depends on**: T009 | **Parallel**: yes | **Type**: lemma (2 sorries)
- **Progress**: DONE.  **Statement amendment** (planning defect caught at execution):
  `norm_det_toMatrix_certificate_le` as drafted had no `LevelBounds`/`θ(U) ⊆ S` hypothesis and is
  unprovable without them (the outer factors' integrality); restated with `(hb : LevelBounds S ρ)`
  explicit and the section `hU` included (`include hU in`).  Proofs as sketched
  (`hv.mapsTo`, `Set.mem_mul`, `Quotient.eq''`, `QuotientGroup.rightRel_apply`, `group`;
  `Matrix.det_mul` ×2, `norm_det_le_one`).
#### Statement — as in the file; conclusions `∃ u₁ ∈ U, ∃ u₂ ∈ U, vRep t = u₁ * η * u₂` and `‖(θ ((u : G) * vRep t)).det‖ ≤ σ`.
#### Proof sketch
1. `obtain ⟨x, hx, hmk⟩ := hv.mapsTo ⟨t, rfl⟩`; `hx : x ∈ {η} * U` → `x = η * u₂` (`Set.mem_mul`, `Set.mem_singleton_iff`); `Quotient.eq''.mp hmk` + `QuotientGroup.rightRel_apply` (`vRep t * x⁻¹ ∈ U`); `u₁ := vRep t * (η * u₂)⁻¹`; `mul_assoc`, `inv_mul_cancel_right`.
2. `obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := exists_mul_eta_mul_of_bijOn hv t`; `map_mul` (`θ (u*u₁) * θ η * θ u₂`), `Matrix.det_mul` ×2, `norm_mul`; `hb.norm_det_le_one (hU (mul_mem u.2 hu₁))`, `hb.norm_det_le_one (hU hu₂)` with `hb := κ.toWeightSeries.bounds`; `mul_le_of_le_one_left/right`, `hdet`.
#### Sources: [Buzzard, Lemma 12.2 proof] "∐_δ U x_δ … det((x_δ)_p)/det(η_p) is a unit".

### [CLEANUP-4a] /cleanup PhD/QMF/Weight/Compact.lean (interim; after T012–T014)
- **Status**: done (2026-08-19, inline mode) | **Depends on**: T012, T013, T014 | **Type**: cleanup
- **Progress**: runLinter zero on `Weight.Compact` after three `omit`s (unused `[Fintype T]`,
  `[CompleteSpace K]`) and the deprecated `ContinuousLinearMap.sum_apply/smul_apply` → `sum_apply`/`smul_apply`.

### [CLEANUP-ALL-1] /cleanup-all on the surface touched so far (pre-milestone)
- **Status**: done (2026-08-19, inline mode) | **Depends on**: CLEANUP-1, CLEANUP-2, CLEANUP-3, CLEANUP-4a | **Type**: cleanup-all
- **Progress**: full surface build (`Algebraic`, `Compact`, `Slash.Quaternionic`, fork to `9_EigenvaluesU3`
  and `7_DiamondHecke`) green; sorry census = exactly the two T015 leaves; per-file linters zero on every
  module this board touched (pre-existing TateFredholm/Matrix.lean, ModelSpace.lean, Tate.lean, Compact.lean
  findings recorded under CLEANUP-3, out of scope).

### [T015] `isCompactoid_heckeBlock`, `isCompactoid_heckeBlockOp` — **C ENDPOINT / MILESTONE**
- **Status**: done (2026-08-19, forms-headline beastmode) | **File**: PhD/QMF/Weight/Compact.lean | **Depends on**: T011, T014, T008, CLEANUP-ALL-1 | **Parallel**: no | **Type**: theorem (2 sorries)
- **Progress**: DONE exactly as sketched (`IsCompactoid.finset_sum` + `.smul` + `AnalyticWeight.isCompactoid_kappaSlash`
  at `norm_det_toMatrix_certificate_le`; `isCompactoid_blockOp`).  **C ENDPOINT**: `U_ϖ` is compactoid on
  `Forms κ U` for every analytic weight (block model; `evalAtReps` injective at a section).  Axioms standard;
  Compact.lean sorry-free, runLinter zero.
#### Statement — as in the file; conclusions `IsCompactoid (heckeBlock θ κ U hU χ vRep hvΔ idx u i j)`, `IsCompactoid (heckeBlockOp θ κ U hU χ vRep hvΔ idx u)`.
#### Proof sketch
1. `unfold heckeBlock; refine IsCompactoid.finset_sum _ fun t _ => IsCompactoid.smul _ (κ.isCompactoid_kappaSlash _ hρσ hσ (norm_det_toMatrix_certificate_le θ κ U hU hdet hv (u i t) t))`.
2. `exact isCompactoid_blockOp fun i j => isCompactoid_heckeBlock θ κ U hU χ hρσ hσ hdet hvΔ hv idx u i j` (BlockOp.lean:678).
#### Sources: [Jacobs, Lemma 2.7]; [Buzzard, Lemma 12.2] "hence U_π … is also norm-decreasing and compact".

### [CLEANUP-4b] /cleanup PhD/QMF/Weight/Compact.lean (final)
- **Status**: done (2026-08-19, inline mode) | **Depends on**: T015 | **Type**: cleanup
- **Progress**: final lint of `Weight.Compact` zero (one `omit [Fintype ι]`); header "Main declarations" covers
  `heckeOperator_apply_rep` (added in T013 — documented below).

---

## Tranche U — the fork's block layer as the instance of C (no duplicate block model)

### [T016] `evalU3 := evalAtReps … classRep`, `blockEntry := heckeBlock …`, `evalU3_heckeU3`/`isCompactoid_blockOpU3` from C
- **Status**: done (2026-08-19, forms-headline beastmode) | **Files**: PhD/JacobsSlash/U3/6_Matrix.lean, 7_Fredholm.lean (+ `5_Factorisations` certificate shapes if needed) | **Depends on**: T005, T013, T015 | **Parallel**: no | **Type**: refactor
- **Progress**: DONE — shapes matched with no generalisation: `blockEntry t ht := Weight.heckeBlock … 1 etaRep
  etaRep_mem_levelMonoid1₃ sigmaTable uTable` (abbrev; `matrixCoeff_blockEntry` absorbs the `(1:K₃) •` by
  `one_smul`), `heckeU3_apply_classRep := Weight.heckeOperator_apply_rep … φ i` (term), `evalU3 := Weight.evalAtReps
  … classRep` (abbrev; `blockProj_evalU3 := blockProj_evalAtReps`), `evalU3_heckeU3 := evalAtReps_heckeOperator …`,
  `isCompactoid_blockOpU3 := isCompactoid_heckeBlockOp … le_rfl norm_three_lt_one norm_det_toMatrix_eta3_le …`
  (new one-liner `norm_det_toMatrix_eta3_le` via `toMatrix_eta3`/`det_fin_two_of`).  Deleted
  `toMatrix_uTable_mul_etaRep_mem_sigma1₃`, `sum_kappaSlash_eq_sum_blockEntry`, `evalU3_eq_evalAtReps`
  (renames.jsonl).  `4_DiamondW`'s `isCompactoid_epsOpXY` kept (still used by its own `isCompactoid_U3MatrixOp`
  over general `K`).  Fork rebuilt green through `9_EigenvaluesU3`/`7_DiamondHecke`; runLinter zero on both files.
#### Spec
1. `evalU3 t ht := Weight.evalAtReps (toMatrix ℚ D v₃) (jacobsWeight t ht) U1_9 U1_9_subset_levelMonoid1₃ 1 classRep` (abbrev; `blockProj_evalU3 := blockProj_evalAtReps …`; `evalU3_eq_evalAtReps` from T005 becomes `rfl` — delete it).
2. `blockEntry t ht := Weight.heckeBlock (toMatrix ℚ D v₃) (jacobsWeight t ht) U1_9 U1_9_subset_levelMonoid1₃ 1 etaRep etaRep_mem_levelMonoid1₃ sigmaTable uTable` (abbrev; note the `(1 : K₃) •` factor — `one_smul` in `matrixCoeff_blockEntry`), provided the fork's certificate functions (`sigmaTable : Fin 3 → Fin 3 → Fin 3`, `uTable : Fin 3 → Fin 3 → U1_9`, `etaRep : Fin 3 → Dfx ℚ D`, the factorisation `classRep i * (etaRep t')⁻¹ = d i t' * classRep (sigmaTable i t') * uTable i t'` from `5_Factorisations`) match `heckeBlock`'s `idx/u/vRep` shape — adapt by composing with the fork's tables; if a genuine mismatch appears (e.g. certificate indexed differently), generalise `heckeBlock` rather than duplicating.
3. `evalU3_heckeU3 := evalAtReps_heckeOperator …` (T013) at the fork's certificates (`hfact` from `5_Factorisations`, `hv`/`hvinj` from `3_EtaDecomposition`'s `bijOn_etaRep`, `hd` the `d i t' ∈ globalUnits` facts); `heckeU3_apply_classRep` follows (or is deleted if no longer used); `isCompactoid_blockOpU3 := isCompactoid_heckeBlockOp … (hdet : ‖(toMatrix ℚ D v₃ eta3).det‖ ≤ ‖3‖)` (T015; `toMatrix_eta3 = (3 0; 0 1)`, `det = 3`), replacing the per-ε `isCompactoid_epsOpXY` route for the K₃ operator (keep `4_DiamondW`'s `isCompactoid_epsOpXY` only if still needed for `isCompactoid_U3MatrixOp` over `ℂ₃`; otherwise delete them and `norm_coeff_hXY_le`'s compactness corollaries — the transcription bounds themselves stay for the slopes).
4. Rebuild the fork green; `renames.jsonl`, `PROGRESS.md`.
#### Sources: [Jacobs pp. 20–21, 28; Lemma 2.7]; [Buzzard §9 p. 69, Lemma 12.2].

### [CLEANUP-FINAL] /cleanup-all (whole board surface) + README/PROGRESS/memory update
- **Status**: done (2026-08-19, forms-headline beastmode) | **Depends on**: T016, CLEANUP-4b | **Type**: cleanup-all.  README §1 (`Weight/Compact.lean`, `TateFredholm/BlockOp.lean`, fork slim-down), §3 (χ, explicit Γ), §4 (dead-code sweep re-run), §5 (tick off 5.1–5.3); `PROGRESS.md`; memory `parallel-ticket-boards`/`analyticweight-headline`.
- **Progress**: DONE.  Whole-surface `runLinter` (9_EigenvaluesU3, 7_DiamondHecke, Weight.Algebraic/Compact,
  Slash.Quaternionic transitively) → zero findings on the board surface (pre-existing findings only in legacy
  `JacobsSlash/1_*–3_*`, `U3/2_Level` (`U1_9` thesis name) and `TateFredholm/BlockOp` — out of scope, listed in
  README §4/§5.7).  Sorry census 0 (doc mentions only).  `#print axioms` standard on all endpoints (A′: fork
  headline chain; B′: `mem_map_classicalForms_iff`, `heckeOperator_mapCoeff_polyEmbed`; C: `isCompactoid_heckeBlockOp`,
  `evalAtReps_heckeOperator`, `evalAtReps_injective`).  Dead-code sweep: deleted the untwisted
  `kappaLevelSMulSlashClass` (renames.jsonl); remaining zero-ref decls are endpoints / simp API (README §4).
  README status 2026-08-19, §1 (+Compact, BlockOp, fork slim), §3 (twisted action, compactness statement, bridge
  names), §4 rewritten, §5 ticked 5.1–5.3 + new 5.6 Fredholm-at-general-weight; PROGRESS.md headline chain
  item 2 + module rows; memory `parallel-ticket-boards` (board COMPLETE), `analyticweight-headline`, MEMORY.md.
  Final build green: 9_EigenvaluesU3, 7_DiamondHecke, 4_DiamondW, Weight.Algebraic/Compact, Slash.Quaternionic.
