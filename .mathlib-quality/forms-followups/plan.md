# Development Plan — forms-followups (`.mathlib-quality/forms-followups/`)

**BOARD PATH: `.mathlib-quality/forms-followups/`** (not the default board).  Planned 2026-08-19
by `/develop` from the six follow-ups surfaced at the end of the forms-headline beastmode run
(`.mathlib-quality/forms-headline/`, complete).  Status: **AWAITING USER VERDICT** — items are
independent; strike any before `/beastmode`.

## Goal (six items, as the user numbered them)

1. **General bijectivity of `evalAtReps` at a neat level + fork dedup.**  Buzzard §9 p. 69 /
   Jacobs Lemma 1.31: `S_κ(U) ≅ ⊕_λ A_κ^{Γ_λ}`; when the stabilisers act trivially this is
   `S_κ(U) ≅ ⊕_λ A_κ` — make it general (`QMF.Weight.bijective_evalAtReps`, `formsModelEquiv`),
   restate `evalAtReps_injective` at any family meeting every double coset, and make the fork's
   `eval_classRep_injective`, `bijective_evalU3`, `kappaFormsModelEquiv` instances of it
   (deleting `exists_classRep_section`).
2. **Compactoid base change** — **DROPPED at planning time**: `TateFredholm.isCompactoid_baseChange`
   (BaseChange.lean:432) already is "compactoid is preserved by bounded base change of a
   matrix operator", and `isCompactoid_U3MatrixOp` (4_DiamondW) is genuinely needed over a
   general field `K` by the slope files (`4_DiamondW:430, 1426`, `9_EigenvaluesU3:73`), so there is
   nothing to delete or generalise.  No ticket.
3. **Fredholm determinant at general weight.**  `heckeCharPowerSeries := charPowerSeries
   (heckeBlockOp …)` (Jacobs p. 21 / Buzzard §13) with the **eigenform criterion**
   `evalT_heckeCharPowerSeries_eq_zero_iff` (Serre §7 Props 11–12 through the model isomorphism);
   the fork's `charPowerSeriesU3` becomes its instance.  *Optional*: the transition operator
   between two families of representatives and **independence of the determinant from
   representatives/certificates** (Buzzard Cor 2.6) — recommended to DEFER (certificates are
   weight-independent, so families never need it).
4. **Quaternionic instantiation**: `S^D_κ(U) = FormsQ F D v κ U hU χ`, `U_ϖ = heckeUpiQ`,
   `U_ϖ` compact at every analytic weight (Buzzard Lemma 12.2) from the general theorem at
   `‖det η_v‖ = ‖ϖ‖`, the Hecke finiteness hypothesis for compact open `U`, and the
   `NontriviallyNormedField (v.adicCompletion F)` instance (ForMathlib; replaces the fork's
   hand-made `K₃` instance).
5. **Linter housekeeping**: the 39 pre-existing `runLinter` findings (6 in
   `TateFredholm/BlockOp.lean`, 32 in the legacy `JacobsSlash/1_*–3_*`, `U1_9` naming).
6. **`AnalyticWeight` radius restriction + redundant-API decisions**: `restrictRadius` (finer
   decay as a hypothesis — honest; the saturation theorem that *derives* it is described, not
   ticketed), re-route `kappaLevelSlashAction` through `AnalyticWeight.kappaSlashAction` (so the
   re-exports are used and `WeightSeries` leaves `Forms.lean`), delete the unused `Sigma0'.adjEquiv`.

## References
- [Buz07] K. Buzzard, *Eigenvarieties*, LMS Lecture Notes 320 (2007): §2 Cor 2.6 (p. 14),
  §9 pp. 68–69, §10 p. 72, p. 73, §12 Lemma 12.2 (p. 78), §13 p. 79.  (`~/Desktop/Papers/Buzzard -
  Eiganvarieties.pdf`; extracted text in the planning scratchpad.)
- [Jac03] D. Jacobs, *Slopes of Compact Hecke Operators*, thesis (Imperial 2003): Lemma 1.31
  (p. 19), Defs 1.32–1.33 (p. 20), pp. 20–21 (matrix of `U_p`), Lemma 2.2, Lemma 2.7.
- [Ser62] J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  §7 Props 11–12 — formalised as `TateFredholm.evalT_charPowerSeries_eq_zero_iff`.

## Mathlib / project inventory
| Concept | Status | Action |
|---|---|---|
| `L(U,A) ≅ ∏ A^{Γ_λ}` (right slash) | project `AutomorphicFunction.bijective_evalAtRepsSlash` (Slash/HeckeMatrix.lean:181) | USE (surjectivity half) |
| Block model / transport / compactness | project `Weight/Compact.lean` (`evalAtReps`, `heckeBlockOp`, `evalAtReps_heckeOperator`, `isCompactoid_heckeBlockOp`) | USE |
| `det(1−Tu)`, conjugation invariance, Riesz criterion | project `TateFredholm.charPowerSeries`, `charPowerSeries_conj` (Fredholm.lean:953), `evalT_charPowerSeries_eq_zero_iff` (Riesz.lean:2233) | USE |
| compactoid base change | project `isCompactoid_baseChange` (BaseChange.lean:432) | already there → item 2 dropped |
| Hecke finiteness at compact open level (right cosets) | project `finite_image_doubleCoset_of_isOpen_of_isCompact` (Slash/HeckeMonoid.lean:231) | USE |
| Fujisaki finiteness of the class set | project `finite_classSet` (Finiteness.lean:39) | USE (remark only) |
| `NontriviallyNormedField (v.adicCompletion K)` | mathlib has `NormedField` (`instNormedFieldValuedAdicCompletion`) + *scoped* `Valued.toNontriviallyNormedField` | DEFINE global instance in ForMathlib (done in skeleton, defeq-checked) |
| `DoubleCoset.rel_iff`, `Quotient.eq''` | mathlib | USE |
| `LinearEquiv.ofBijective`, `ContinuousLinearEquiv` from `LinearEquiv.ofLinear` | mathlib | USE |

## File structure
- `PhD/QMF/Weight/Compact.lean` — + `ext_of_forall_rep`, `bijective_evalAtReps`,
  `bijective_evalAtReps_of_stabilizer_eq_bot`, `formsModelEquiv` (skeleton in place);
  `evalAtReps_injective` restated at families.
- `PhD/QMF/Weight/Fredholm.lean` (NEW, skeleton in place) — `heckeCharPowerSeries`,
  `evalT_heckeCharPowerSeries_eq_zero_iff`; optional `transitionOp`, `evalAtReps_eq_transitionOp`,
  `heckeCharPowerSeries_eq_of_reps`.
- `PhD/QMF/Weight/Quaternionic.lean` (NEW, skeleton in place) — `FormsQ`, `heckeUpiQ`,
  `etaAdelic'_mem_levelMonoidOf_sigma0'`, `norm_det_toMatrix_etaAdelic'`,
  `isCompactoid_heckeBlockOp_etaAdelic'`, `finite_image_etaAdelic'_of_isOpen_of_isCompact`.
- `PhD/ForMathlib/NumberTheory/NumberField/Completion/FinitePlace.lean` (NEW, DONE) — the instance.
- `PhD/QMF/Weight/Char.lean` — `ExpansionData.restrictRadius`, `AnalyticWeight.restrictRadius`
  (skeleton in place; one sorry).
- `PhD/QMF/Weight/Forms.lean`, `PhD/QMF/Slash/Sigma0.lean` — item 6 refactor.
- Fork: `U3/3_ClassSet.lean` (`classRep_bijective`), `U3/6_Matrix.lean`, `U3/7_Fredholm.lean`,
  `U3/1_Setting.lean` (instance swap).
- Item 5: `PhD/TateFredholm/BlockOp.lean`, `PhD/JacobsSlash/{1_PadicAnalytic,1_SlopeTheorem,2_U3Data,3_Slopes}.lean`, `U3/2_Level.lean`.

## Dependency graph
```
T001 ext_of_forall_rep (+ evalAtReps_injective at families) ─► T002 bijective_evalAtReps/_of_stabilizer_eq_bot/formsModelEquiv ─► T003 fork dedup ─► CLEANUP-1/2
T002 ─────────────────────────────────────────────────────────────────────────────► CLEANUP-ALL-1 ─► T006 heckeCharPowerSeries + eigenform criterion (MILESTONE) ─► CLEANUP-3
T002, T004 transitionOp transport (optional) ─► T005 independence (optional) ─► CLEANUP-3
T007 quaternionic (instance swap, FormsQ, heckeUpiQ, compactness, finiteness) ─► CLEANUP-4
T008 re-route level action + delete adjEquiv ; T009 kappaSlash_restrictRadius ─► CLEANUP-5
CLEANUP-6 BlockOp ; CLEANUP-7 2_U3Data ; CLEANUP-8 1_PadicAnalytic ; CLEANUP-9 1_SlopeTheorem ; CLEANUP-10 3_Slopes ; CLEANUP-11 U1_9 nolint
all ─► CLEANUP-FINAL
```

## Generality decisions
- Item 1 hypotheses: a family `c : ι → G` with `Function.Bijective (Quotient.mk'' ∘ c)` (no
  `Fintype` on the double-coset quotient; no section type) and **"stabilisers act trivially"**
  (`∀ i w (hw : w ∈ stabilizerAtSlash Γ U (c i)) a, χ(θ w) • κ.kappaSlash (θ w) a = a`) — Buzzard's
  actual condition (p. 73: `Γ_λ` acts through a finite quotient; trivial action is the case where
  `A^{Γ_λ} = A`), with `stabilizerAtSlash = ⊥` (Jacobs Lemma 2.2) as a corollary.
- Item 3: determinant defined at certificates (Jacobs's own convention: "the matrix of `U_p` with
  respect to the topological basis"); independence is a separate optional theorem.  Non-neat
  levels (Buzzard's property-(Pr) route, p. 73) are OUT of scope.
- Item 4: `S` stays general (Jacobs's `Σ₁(3)` ⊂ Buzzard's `M_t`); `η ∈ Δ` and the Hecke finiteness
  are hypotheses of `heckeUpiQ` (as in the left core's `heckeUpi`), each discharged by a lemma
  (`etaAdelic'_mem_levelMonoidOf_sigma0'`, `finite_image_etaAdelic'_of_isOpen_of_isCompact`).
- Item 6: radius restriction takes the finer decay as a hypothesis — the honest shape given that
  `ExpansionData` records a radius, not Taylor-coefficient integrality (see the ticket for the
  saturation theorem that would derive it).
