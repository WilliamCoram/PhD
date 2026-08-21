# Development Plan — forms-riesz (`.mathlib-quality/forms-riesz/`)

**BOARD PATH: `.mathlib-quality/forms-riesz/`** (not the default board).  Planned 2026-08-19 by
`/develop` for next-steps 1–4 after the forms-followups board.  Status: **AWAITING USER VERDICT**.

## Goal (four items)

1. **The Jacobs crux as a statement about eigenforms.**  `«9_EigenvaluesU3»` proves [Jacobs,
   Cor 2.16] about the base-changed *matrix* `U3MatrixOp` over `ℂ₃`.  Base-change the thesis's
   *space* instead: the Jacobs weight is field-generic (`jacobsWeightOf` over any complete
   ultrametric `K` with `‖3‖ < 1`, at the norm-defined level `sigma1Norm`), the component map over
   `L` is `mapTheta ι (toMatrix ℚ D v₃)`, level/certificates are unchanged; general comparison
   lemmas (`Weight/BaseChange.lean`: weight actions, Hecke blocks and the Fredholm determinant
   commute with `ι`) identify `U₃`'s block operator over `L` with the base-changed transcribed
   matrix and `det(1 − T·U₃)` over `L` with `map ι (charPowerSeriesU3)`; then
   **`exists_eigenform_U3_halfIntegral`**: for every `j` an eigenform `φ ∈ kappaFormsL ℂ₃` of `U₃`
   with eigenvalue of valuation `j + ½`.  (Dedup: `jacobsWeight t ht` becomes the generic weight
   restricted to `Σ₁(3)`; `MvPowerSeries.map_inv₀`, `map_linSeries`, `map_quadSeries` move to the
   general layer; `charPowerSeries_map` becomes the isometric corollary of `charPowerSeries_baseChange`.)
2. **Quaternionic remaining half.**  (c) the Fujisaki-indexed block model: `evalAtReps` at
   `Quotient.out` is injective / bijective at a neat level (`evalAtReps_out_injective`,
   `bijective_evalAtReps_out`), with `classSetFintype` from `finite_classSet` — Buzzard p. 73
   `S^D_κ(U) → ⊕_{λ=1}^{µ} (A_κ)^{Γ_λ}`, `µ` finite.  (a) compact open standard levels → Hecke
   finiteness: an **API gap** (the integral-adele order of `D` and its unit group are not in the
   project); ticketed as OPTIONAL with a sub-tree and recommended DEFERRED — nothing planned
   consumes it (`heckeUpiQ` takes finiteness as a hypothesis; the thesis level has it by explicit
   coset representatives).
3. **Serre's Riesz decomposition on `S_κ(U)`.**  `exists_riesz_decomposition_forms`: at a zero
   `a` of `det(1 − T·[UηU])` over a discretely valued `K`, `S_κ(U) = N ⊕ F` with `N` the
   `h`-dimensional generalised `a⁻¹`-eigenspace of `[UηU]` and `1 − a·[UηU]` bijective on `F`
   (transport of `TateFredholm.exists_riesz_decomposition` along `formsModelEquiv`).
4. **Non-neat levels via property (Pr).**  `Weight/Pr.lean`: the averaging projector `stabAvg`
   over a finite stabiliser, the block projector `stabProj` onto `∏ A^{Γ_λ}` = image of
   `evalAtReps`, the determinant `heckeCharPowerSeriesPr … E := det(1 − T·(heckeBlockOp ∘ E))` for
   any continuous projector `E` onto the image (Buzzard's `det(1 − X(φ ⊕ 0))`), its independence of
   `E` (Buzzard Lemma 2.12 via `charPowerSeries_comm`), agreement with `heckeCharPowerSeries` at a
   neat level (`E = 1`), and the eigenform criterion at an arbitrary level.

## References
- [Buz07] Buzzard, *Eigenvarieties*, LMS 320 (2007): §2 pp. 18–19 (det on (Pr) modules),
  Lemma 2.12 (uv/vu), Lemma 2.13 (base change), §3 Prop 3.2 p. 23 (Riesz decomposition), §9
  p. 69, §10 p. 73 (`Γ_λ` finite quotient ⇒ direct summand; `S^D_κ(U;r) → ⊕ (A_{κ,r})^{Γ_λ}`).
- [Jac03] Jacobs, thesis: Lemma 1.31 (p. 19), §2.1 p. 29 (the expansion `κ(cx+d)` with
  `c ≡ 0 mod 9, d ≡ 1 mod 9`), Prop 2.6, Cor 2.16 (p. 39).
- [Ser62] Serre, *Endomorphismes complètement continus*, §7 Prop 12 — formalised as
  `TateFredholm.exists_riesz_decomposition`.
- Scratchpad text extracts: `buzzard.txt`, `jacobs.txt` (planning session).

## Mathlib / project inventory
| Concept | Status | Action |
|---|---|---|
| `charPowerSeries` base change | project `TateFredholm.charPowerSeries_baseChange` (bounded ψ), fork `charPowerSeries_map` (isometric) | USE; dedup the fork copy |
| `MvPowerSeries.map_inv₀`, `map_linSeries`, `map_quadSeries`, `map_unitPow`, `map_binomialCoeff`, `map_weightGenFun` | fork `JacobsSlash/3_BaseChange.lean` | MOVE the generic three to ForMathlib / TateFredholm; USE the rest |
| Riesz decomposition on `c(I,K)` | project `exists_riesz_decomposition` (Riesz.lean:2832) | USE (transport) |
| `charPowerSeries_comm`, `charPowerSeries_conj` | project (Fredholm.lean) | USE (Pr independence) |
| averaging projector | mathlib `Representation.averageMap` (needs a `Representation`); we average the twisted slash directly | DEFINE `stabAvg` by hand (cite mathlib) |
| Fujisaki finiteness | project `finite_classSet` | USE (`classSetFintype`) |
| generic Jacobs analysis (`unitPow`, `binomialCoeff`, binomial theorem) | fork `1_PadicAnalytic`, `3_BinomialTheorem` (generic `K`, `h3`) | USE |
| compact open levels | NOT in project/FLT (only `finite_image_doubleCoset_of_isOpen_of_isCompact`) | API GAP (optional, item 2a) |

## File structure (skeleton in place, `lake build` green, 41 sorries)
- `PhD/QMF/Weight/BaseChange.lean` (NEW): `map_yExtend`, `WeightSeries.map_genFun`,
  `WeightSeries.matrixCoeff_kappaSlash_map`, `AnalyticWeight.matrixCoeff_kappaSlash_map`,
  `Weight.mapTheta`, `matrixCoeff_heckeBlock_map`, `matrixCoeff_heckeBlockOp_map`,
  `heckeCharPowerSeries_map`.
- `PhD/QMF/Weight/Compact.lean`: `evalAtReps_out_injective`, `bijective_evalAtReps_out`.
- `PhD/QMF/Weight/Quaternionic.lean`: `classSetFintype` (done).
- `PhD/QMF/Weight/Fredholm.lean`: `exists_riesz_decomposition_forms`.
- `PhD/QMF/Weight/Pr.lean` (NEW): `stabAvg` (+4 lemmas), `stabProj` (+2), `heckeCharPowerSeriesPr`,
  `heckeBlockOp_mem_range_evalAtReps`, `heckeCharPowerSeriesPr_eq_of_proj`, `heckeCharPowerSeriesPr_one`,
  `evalT_heckeCharPowerSeriesPr_eq_zero_iff`.
- `PhD/JacobsSlash/U3/5_KappaWeight.lean`: generic section `sigma1Norm`, `levelBounds_sigma1Norm`,
  `hasSum_jacobsColOf_unitPow`, `jacobsCharOf`, `jacobsExpansionDataOf`, `jacobsWeightOf`,
  `sigma1₃_le_sigma1Norm`; (ticket) `jacobsWeight := (jacobsWeightOf …).restrict …`.
- `PhD/JacobsSlash/U3/10_Eigenforms.lean` (NEW): `thetaL`, `map_mem_sigma1Norm`,
  `U1_9_subset_levelMonoidL`, `eta3_mem_levelMonoidL`, `etaRep_mem_levelMonoidL`,
  `exists_natCast_close_map`, `jacobsWeightL`, `kappaFormsL`, `heckeU3L`, `jacobsCol_map`,
  `heckeBlockOpL_eq_U3MatrixOp`, `heckeCharPowerSeriesL_eq_map`, `bijective_evalU3L`,
  `exists_eigenform_U3_halfIntegral`.
- Refactor (no skeleton): `PhD/ForMathlib/RingTheory/MvPowerSeries/Inverse.lean` (`map_inv₀`),
  `PhD/TateFredholm/WeightGenFun.lean` (`map_linSeries`, `map_quadSeries`),
  `PhD/TateFredholm/BaseChange.lean` (`charPowerSeries_map` corollary), `JacobsSlash/3_BaseChange.lean`.

## Dependency graph
```
T001 (moves/dedup) ─► T002 (weight action commutes with ι) ─► T003 (blocks/determinant) ─► CLEANUP-1
T004 (generic jacobsWeight + K₃ := restrict) ─► CLEANUP-2
T003, T004 ─► T005 (L-side data) ─► T006 (block op = U3MatrixOp_L, det = map, bijective) ─► CLEANUP-ALL-1 ─► T007 (CRUX for forms, MILESTONE) ─► CLEANUP-3
T008 (out-lemmas, Fujisaki model) ─► CLEANUP-4 ;  T009 (OPTIONAL API gap: compact levels) 
T010 (Riesz on Forms) ─► CLEANUP-5
T011 (averaging) ─► T012 (block projector) ─► T013 (Pr determinant: stability, E-independence, neat agreement) ─► CLEANUP-6 ─► T014 (Pr eigenform criterion) ─► CLEANUP-7
all ─► CLEANUP-FINAL
```

## Generality decisions
- Base change is stated as a *comparison* between two given weights with matching columns
  (`hcol`), not as a construction `AnalyticWeight.map` — the character over `L` must be supplied
  (a character on the `L`-disc is not determined by its `K`-points without an identity theorem);
  the algebraic parts (`matrixCoeff_kappaSlash_map`, blocks) need no norm hypotheses, the
  determinant needs `ι` bounded (`charPowerSeries_baseChange`).
- Generic Jacobs weight: hypotheses `h3 : ‖3‖ < 1`, `ht : ‖t‖ < 1`, `hnat` (t approximable by
  naturals — exactly what `tsum_binomialCoeff_eq_unitPow` consumes); level `sigma1Norm` (norm
  form); the `K₃` weight is its restriction to `Σ₁(3)`.
- Pr: the determinant takes an *arbitrary* continuous projector onto the image (independence
  proven), `stabAvg`/`stabProj` are one construction (finite stabilisers, `|Γ_λ| ≠ 0` in `K`);
  finiteness of `Γ_λ` at quaternionic levels (Dˣ discrete, U compact) is NOT formalised — hypothesis.
- Riesz on Forms: bundled existential as in Serre/Buzzard (shared witnesses `h`, `N`, `F`);
  `IsCompl` (algebraic) since `Forms` carries no topology; `hd` (discretely valued `K`) inherited
  from `finrank_ker_one_sub_smul_pow`.
