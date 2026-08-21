# Development Plan: forms-headline — the headline `Forms` made load-bearing

**BOARD PATH: `.mathlib-quality/forms-headline/`** — all artifacts here.  Parallel boards
(`.mathlib-quality/` = NewtonPolygons, `qmf/`, `jacobs/`, `jacobs-endgame/`,
`tatefredholm-eigen/`, `slashRefactor/`, `hurwitz-cn1/`, `laweights/`) are other projects'
property.  Every `/beastmode` invocation for this project must be told this path.

**STATUS 2026-08-19: planning COMPLETE (revised to the no-duplication design), awaiting
user approval.**  The Lean skeleton (25 sorries across 9 files, listed in
`decomposition.md`) builds across the full chain (`PhD.QMF.Weight.Algebraic`,
`PhD.QMF.Weight.Compact`, `PhD.QMF.Slash.Quaternionic`, `PhD.JacobsSlash.U3.«9_EigenvaluesU3»`,
`PhD.JacobsSlash.U3.«5_KappaWeight»`).  R0 (the `BlockOp` module move) is executed and green.

**Revision 2026-08-19 (user: "not having duplicate code is important").**  The first cut
proved *bridge theorems* between the fork's objects and the headline ones
(`kappaForms_eq_forms`, `heckeU3_eq_heckeOperator`, `twistedKappaLevelAction_eq`, plus
`RightSlashAction.ext`/`slashFixedPointsOfLE_congr`/`heckeOperatorSlash_congr` as transport
plumbing).  That leaves the duplicates in place.  The revised board **replaces** them:
the fork's `kappaForms`/`heckeU3` become abbreviations of `Forms`/`heckeOperator`, the fork's
own action (`kappaSlash t ht`, `kappaSlashAction`, `kappaLevelSlashAction`), its ODE cocycle
and its copy of the yCoeff/Möbius/integrality calculus are deleted, `jacobsWeightSeries` is
deleted in favour of the honest character `jacobsWeight`, and in `Algebraic.lean` the
hand-built `algWeightSeries`/`twistedKappaLevelAction` are replaced by
`algWeight`/`kappaLevelSlashActionTwisted` with the R6 theorems restated on `Forms`.  The
bridge skeleton (`10_FormsHeadline.lean`, the three plumbing lemmas, `twistedKappaLevelAction_eq`)
was removed; the only new A′ lemmas are `genFun_jacobsWeight` and
`matrixCoeff_kappaSlash_jacobsWeight` (`5_KappaWeight.lean`).

**Revision 2026-08-19 (b) — `AnalyticWeight` carries its expansion as data.**  The user
asked whether `Classical.choice` in `AnalyticWeight.toWeightSeries` was needed; it was not
(it came from bundling the expansion as a `Nonempty`-Prop `IsAnalyticOn`).  `AnalyticWeight`
is now `⟨toChar, expansion : ExpansionData S ρ U toChar⟩` — Jacobs's "by κ(cz+d) we mean the
power series expansion", Buzzard's singled-out "thickening" — so `(jacobsWeight t ht)
.toWeightSeries.col` and `(algWeight hb n).toWeightSeries.col` are `rfl` the explicit
series; `IsAnalyticOn`, `ofExpansionData`, `kappaSlash_ofExpansionData`, `IsAnalyticOn.*`
are gone; uniqueness on the level stays as `ExpansionData.col_eq_of_mem` /
`AnalyticWeight.kappaSlash_eq`.  Skeleton rebuilt green (25 sorries).
A tranche **U** makes the fork's block layer (`evalU3`, `blockEntry`, `evalU3_heckeU3`,
`isCompactoid_blockOpU3`) the instance of the general block model of C.

## Goal

Three results, in the user's order of *deliverables* (2 → 3 → 1 of `PhD/QMF/README.md`
§5), on top of the R8 headline `QMF.Weight.Forms Γ θ κ U hU` (`κ : AnalyticWeight`):

* **A′ = README §5.2 — the Jacobs endpoint at the headline, by replacement.**
  `JacobsSlash.kappaForms t ht` *is defined as* `Forms Dˣ toMatrix (jacobsWeight t ht) U₁(9)`
  and `heckeU3` as `Weight.heckeOperator`; the fork keeps only Jacobs-specific content (the
  κ-column `kappaSeries₂` and its analytic facts → `jacobsExpansionData`/`jacobsWeight`, the
  `Σ₁(3)`/`Σ₁(9)`/`U₁(9)` data, certificates, transcribed matrices, slopes, base change).
  `jacobsWeightSeries`, the ODE cocycle, and the fork's copies of the general calculus are
  deleted (`4_KappaSlash.lean` 1569 → ≈400 lines, renamed `4_KappaColumn.lean`).  The crux
  `exists_eigenvalue_U3_halfIntegral` then *is* a statement about the headline operator
  (`charPowerSeriesU3` is the Fredholm determinant of `heckeU3 = heckeOperator …` in the block
  model `evalU3 = evalAtReps … classRep`).
* **B′ = README §5.3 — a `Forms`-level classical inclusion, by replacement.**
  `algWeightSeries` → `algWeight` (honest character `u ↦ u^(n+2)`), `twistedKappaLevelAction`
  → `kappaLevelSlashActionTwisted θ (algWeight hb n) (detTwist ν)`, R6's three theorems
  restated on `Forms` and the originals deleted.  `Forms` gains Buzzard's
  second weight component: an optional scalar character `χ : S →* Kˣ` of the acting monoid
  (`(h.γ)(z) = n(cz+d)·v(det γ)·h(…)`, [Buzzard §10 p. 72]; Def 1.27 is `χ = 1`), so that
  [Buzzard §11 p. 73] "`S^D_{k,w}(U) = L(U, L_{n,v}) ⊆ L(U, A_{κ,r}) = S^D_κ(U; r)`" is
  `map_classicalForms_le_forms : (classicalForms θ n ν U hU).map (mapCoeff (polyEmbed n ν))
  ≤ Forms Γ θ (algWeight hb n) U hU (detTwist ν)`, with the R6 endpoint and Hecke
  equivariance restated at the headline.
* **U** — the fork's block layer (`evalU3`, `blockEntry`, `evalU3_heckeU3`,
  `isCompactoid_blockOpU3`) becomes the instance of C's `evalAtReps`/`heckeBlock`/
  `evalAtReps_heckeOperator`/`isCompactoid_heckeBlockOp` (after A′ and C).
* **C = README §5.1 — compactness of `U_ϖ` at general weight.**  [Jacobs, Lemma 2.7] and
  [Buzzard, Lemma 12.2] at an arbitrary `AnalyticWeight`: `κ.kappaSlash g` is compactoid for
  `‖det g‖ ≤ σ < 1` (`ρ ≤ σ`), and the block model of `heckeOperator θ κ U hU hη h` (with
  respect to any finite family of class representatives and coset/factorisation
  certificates) is compactoid for `η` of `U_ϖ` type (`‖det θ(η)‖ ≤ σ`), the operator being
  the block operator under `evalAtReps` (injective at a section of `Γ\G/U`).

## Sources (all read in full for the cited passages; verbatim quotes in `decomposition.md`)

- [Jacobs] D. Jacobs, *Slopes of Compact Hecke Operators*, PhD thesis, Imperial College
  London 2003 (`~/Desktop/Papers/Jacobs - Slopes of Compact Hecke Operators.pdf`; PDF page
  = thesis page): Cor 1.10 (p. 10), Def 1.27–1.32 (pp. 19–20), the matrix recipe pp. 20–21,
  Prop 2.6 (p. 29), **Lemma 2.7 (p. 30)**, Cor 2.16 / (2.1.1) as in the fork.
- [Buzzard] K. Buzzard, *Eigenvarieties*, LMS 320 (2007) (`~/Desktop/Papers/Buzzard -
  Eiganvarieties.pdf`, PDF page = paper page + 0): §9 pp. 68–70 (`L(U,A)`, `f ↦ (f(τ_λ))`,
  `[UηU]`, `S^D_{k,w}(U)`), **§10 pp. 71–72** (`A_{κ,r}`, the action with `v(det γ)`),
  **§11 p. 73** (classical ⊆ overconvergent), **Lemma 12.2 pp. 78–79** (`U_π` compact).
- The current design: `PhD/QMF/README.md` (§§2–5), `PhD/JacobsSlash/PROGRESS.md`.

## Deliverable split / architecture

- **`PhD/QMF/Weight/Forms.lean` (B1, done in skeleton as definitions):**
  `kappaLevelSlashActionTwisted θ κ χ`, `Forms Γ θ κ U hU (χ := 1)` (now via
  `slashFixedPointsOfLE`, so `heckeOperator : Forms →ₗ Forms` on the nose),
  `mem_forms_iff` (χ), `mem_forms_iff_one`, `heckeOperator` with `{Γ} {χ}` implicit (read
  off the form it is applied to).  **Design decisions:** `χ` is an *optional last*
  argument of `Forms` (the headline `Forms Γ θ κ U hU` is unchanged; `Forms Γ θ κ U hU χ`
  is Buzzard's pair `κ = (n, v)`), and `Γ` is now **explicit** in `Forms` (nothing else
  determines it — the skeleton pass surfaced `don't know how to synthesize Γ` at every
  use; mathlib rule: explicit if not inferable).  `heckeOperator` cannot carry `χ` as an
  optParam (an optParam before the applied argument swallows the form: `heckeOperator … φ`
  parsed `φ` as `χ`) — hence implicit.
- **`PhD/QMF/Weight/Compact.lean` (NEW, C):** the block model `evalAtReps`, blocks
  `heckeBlock`/`heckeBlockOp` from certificate data, transport `evalAtReps_heckeOperator`,
  compactoidness.  Separate file so `Forms.lean` stays the headline definitions and the
  Riesz/BlockOp imports live only here.
- **`PhD/TateFredholm/BlockOp.lean` (R0 MOVE, done):** `PhD/JacobsSlash/1_BlockOp.lean`
  moved, namespace `JacobsSlash → TateFredholm` (the file's own header said "candidates
  for upstreaming"); one import fixed (`4_DiamondW`); whole fork rebuilt green; recorded in
  `.mathlib-quality/renames.jsonl`.  Needed because `Weight/Compact.lean` (QMF layer) must
  not import `JacobsSlash`.
- **`PhD/QMF/Weight/Algebraic.lean` (B′):** `classicalForms` (abstract `S^D_{k,w}(U)`),
  `classicalHeckeOperator`, `map_classicalForms_le_forms`, `mem_map_classicalForms_iff`,
  `heckeOperator_mapCoeff_polyEmbed` (skeleton); `algWeightSeries`, `kappaLevel_hsmul`,
  `twistedKappaLevelAction`, `twistedKappaSMulSlash` and R6's three `levelSubmoduleSlash`
  statements are deleted/replaced in T006–T007.
- **Fork (A′, U):** `U3/4_KappaSlash.lean` → `U3/4_KappaColumn.lean` (Jacobs-specific
  residue), `U3/5_KappaWeight.lean` (`jacobsWeight` + `genFun_jacobsWeight`,
  `matrixCoeff_kappaSlash_jacobsWeight`; `jacobsWeightSeries` gone), `U3/6_Matrix.lean` (`kappaForms`/`heckeU3` abbrevs of the headline, `blockEntry` via
  `(jacobsWeight t ht).kappaSlash`, later `heckeBlock`), `U3/7_DiamondHecke.lean` (general
  yCoeff API), `U3/7_Fredholm.lean` (`evalU3` → `evalAtReps … classRep`), `8`/`9` instance names.
- **Engine leaves (C):** `Series.lean` (`LevelBounds.norm_det_le_one`,
  `LevelBounds.norm_apply_zero_zero_le_of_norm_det_le`, `WeightSeries.rowIntAt_genFun`),
  `SlashAction.lean` (`norm_matrixCoeff_kappaSlash_le`, `isCompactoid_kappaSlash`,
  `_of_norm_det_le`), `Char.lean` (`AnalyticWeight.isCompactoid_kappaSlash`),
  `TateFredholm/GenFun.lean` (`isCompactoid_of_row_decay'`), `WeightGenFun.lean`
  (`RowIntAt.mono`), `Riesz.lean` (`isCompactoid_zero`, `IsCompactoid.finset_sum`).
- **No transport lemmas.**  With replacement there is nothing to transport; the
  `RightSlashAction.ext`/`*_congr` plumbing of the first cut was removed from the skeleton.

## Order of work

The user's order 2 → 3 → 1 is kept for the *deliverables*: A′ (T002–T005) first, B′
(T006–T007), C (T008–T015), then U (T016) which needs both A′ and C.  B1 (the `Forms`
signature: χ, explicit Γ) is already in the skeleton; its two lemma sorries are T001.  A′ and
B′ touch disjoint files from C, so C can run in parallel from the start.

## Mathlib Inventory (verified)

| Concept | Mathlib status | Action |
|---|---|---|
| right-coset relation `Quotient.mk'' x = mk'' y ↔ y x⁻¹ ∈ U` | `QuotientGroup.rightRel_apply` (`Mathlib/GroupTheory/Coset/Defs.lean:111`) | USE (T015) |
| `Submodule.map`, `mem_map_of_mem`, `SetLike.le_def` | mathlib | USE (T006/T007) |
| `LinearEquiv.ofEq` | mathlib | USE (`evalForms`) |
| `Matrix.det_fin_two`, `Matrix.det_mul` | mathlib | USE (T010, T015) |
| `IsUltrametricDist.norm_add_le_max`, `norm_add_eq_max_of_norm_ne_norm` | mathlib | USE (T010) |
| `tendsto_pow_atTop_nhds_zero_of_lt_one`, `Nat.cofinite_eq_atTop` | mathlib | USE (T009) |
| block operators / compactoid closure | absent | USE project `TateFredholm.BlockOp` (moved) |
| Serre/Jacobs Cor 1.10 row-decay criterion | absent | USE project `isCompactoid_of_row_decay` (+ real-σ variant T009) |
| `RowIntAt` calculus (`.mul`, `.inv`, `rowIntAt_quadSeries`) | absent | USE project `TateFredholm.WeightGenFun` |
| class-set decomposition / Hecke matrix recipe | absent | USE project `AutomorphicFunction.bijective_evalAtRepsSlash`, `heckeOperatorSlash_apply_rep` |

## Dependency graph

```
T001 (mem_forms_iff, _one)
T002 (A′-1: 4_KappaSlash/5_KappaWeight slim, genFun_jacobsWeight) ─► T003 (A′-2: 6_Matrix) ─► T004 (A′-3: 7_DiamondHecke)
      ─► T005 (A′-4: 7_Fredholm/8/9, evalU3_eq_evalAtReps, renames) ─► CLEANUP-1
T006 (B′-1: algWeight replaces algWeightSeries; twistedKappaLevelAction deleted) ─► T007 (B′-2: Forms statements) ─► CLEANUP-2
T008 (TateFredholm API) ─┐
T009 (det/entry bounds) ─► T010 (rowIntAt_genFun) ─► T011 (isCompactoid_kappaSlash ×4) ─► CLEANUP-3
T012 ─► T013 (transport) ─┐
T014 ─────────────────────┴─► CLEANUP-4a ─► CLEANUP-ALL-1 ─► T015 (C ENDPOINT) ─► CLEANUP-4b
T016 (U: fork block layer := instance of C; needs T005, T013, T015) ─► CLEANUP-FINAL
```
Parallel capacity at start: 5 (T001 ∥ T002 ∥ T008 ∥ T009 ∥ T012).

## Generality decisions

- Everything at the abstract `(G, θ)` level of `Forms` (any group `G`, any `θ : G →* M₂(K)`,
  any level `S` with `LevelBounds S ρ`, any `AnalyticWeight UK S ρ`, any twist `χ`).
- Compactness is stated for **`‖det θ(η)‖ ≤ σ` with `ρ ≤ σ < 1`** rather than for a specific
  `η = diag(ϖ, 1)`: this is Buzzard's own hypothesis ("`det((x_δ)_p)/det(η_p)` is a unit")
  and covers levels `p^t`, `t ≥ 2` (`‖π‖ > ρ = ‖π‖^t`) where the naive `‖a‖ ≤ ρ` fails.
- The block model is stated for an arbitrary finite family of representatives `c : ι → G`
  and arbitrary certificate data (`vRep`, `idx`, `d`, `u`); the class-set *bijectivity* is
  only used for `evalAtReps_injective` (section case).  This is exactly the fork's shape
  (`evalU3`, `blockEntry`) at general `ι`.
- No `HClassNumberOne` anywhere in the general layer; in A it enters only for
  `bijective_evalForms`, as in the fork.

## Inventory: what else in `PhD/JacobsSlash/` the general layers supersede (2026-08-19 audit)

Covered by this board: the weight/action/space/Hecke layer (`kappaSlash`, `kappaSlashAction`,
`kappaLevelSlashAction`, `kappaForms`, `heckeU3`, `heckeW`, `levelMonoid1₃`, `jacobsWeightSeries`,
the ODE cocycle, the duplicated CoeffInt/ShiftInt/yCoeff/Möbius calculus — A′), the block layer
(`evalU3`, `kappaFormsModelEquiv`, `blockEntry`, `evalU3_heckeU3`, `isCompactoid_blockOpU3` — U),
and `isCompactoid_zero_clm` (T005).

**Not on this board (follow-ups):**
- `weightGenFun t g` (`2_U3Data`, general `K` with `‖3‖ < 1`) is `WeightSeries.genFun` at the
  Jacobs datum (`genFun_jacobsWeight`) — but the datum exists only at `K₃` while the
  transcription (`h₀₁…h₂₁`, `U3MatrixOp`, base change to `ℂ₃`) runs over general `K`.
  Unifying them needs `jacobsExpansionData` over any `K` with `‖3‖ < 1` (`1_PadicAnalytic` is
  already general-`K`) and a general `Σ₁`-type level (`{‖c‖ ≤ ρ, ‖d − 1‖ ≤ ρ}`, the domain of
  `unitPow`) in `QMF.Weight` next to `SigmaNorm`.  Worth a tranche of its own.
- General content that merely *lives* in the fork and should be upstreamed (not duplicates of
  QMF, but misplaced): `3_BaseChange` §1 (`TateFredholm.charCoeff_map`, `charPowerSeries_map`
  for an isometric *hom*, complementing `BaseChange.lean`'s `_equiv`/`_baseChange` versions),
  `5_EigenSlopes` (`exists_evalT_zero_of_slope`, `exists_eigenvector_of_slope_charPowerSeries`:
  Riesz + Newton polygons, general), `4_SlopeReading` §1 (`NewtonPolygon₀.ofSlopes` witness
  layer), and the `p`-adic `exp`/`log`/binomial theorem of `1_PadicAnalytic`/`3_BinomialTheorem`
  (general `K` with `‖3‖ < 1`; mathlib has none of it — ForMathlib candidates after
  generalising `3 ↦ p`).  R0-style moves with `renames.jsonl` entries; a separate pass.
- Genuinely Jacobs-specific and staying: the κ-column `kappaSeries₂`/`unitPow` facts,
  `Σ₁(3)/Σ₁(9)/U₁(9)`, `1_Hurwitz`/`1_Setting`/`2_PadicEmbedding`/`3_ClassSet`/
  `3_EtaDecomposition`/`5_Factorisations`/`CN1`, the transcribed matrices, `3_Slopes`,
  `4_DiamondW`'s ε-operators and change of basis, `1_SlopeTheorem`, `8`/`9`.
