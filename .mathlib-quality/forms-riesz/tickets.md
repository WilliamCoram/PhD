# Ticket Board — forms-riesz (`.mathlib-quality/forms-riesz/`)

**BOARD PATH: `.mathlib-quality/forms-riesz/`.**  Workers: `/beastmode` with this path.
**Status: BOARD COMPLETE 2026-08-20** (single beastmode run; T009 deferred by the user).  Approved 2026-08-19 (user: T009 deferred; item 4 keeps both determinants — option 1:
`heckeCharPowerSeries` for neat levels, `heckeCharPowerSeriesPr` for any level with the agreement
lemma; item 1's generic `jacobsWeightOf` with the `K₃` weight as its restriction).  Ready for
`/beastmode` on this path.

Governing principles (inherited): no duplicate code (replace, don't bridge); every deletion/rename
in `.mathlib-quality/renames.jsonl`; `lia` → `omega`; never touch `PhD/PR'd/`.  Skeleton in place
(41 sorries); `lake build PhD.JacobsSlash.U3.«10_Eigenforms» PhD.QMF.Weight.Pr
PhD.QMF.Weight.BaseChange` green (2026-08-19).

## Summary
- Total: 14 proof/def/refactor tickets (T001–T014; T009 DEFERRED) + 1 spawned (T012a) + 9 cleanup = 24
- Open: 0 | Deferred: 1 (T009) | In Progress: 0 | Done: 23
- Sub-tickets spawned: **T012a** `mem_range_evalAtReps_iff` (depth 1, from T012) — done.
- Sketch defects met: T013's planned identity chain proved the wrong endpoint (fixed in-ticket);
  `DoubleCoset.Quotient` unfolding breaks `[Fintype ι]` matching (T008); `exists_natCast_close_map`
  needed `include hι` (T005); `stabAvg_slash` did not need `hcard` (dropped).
- Parallel capacity at start: 6 (T001 ∥ T004 ∥ T008 ∥ T010 ∥ T011 ∥ T009)
- Milestones: T007 (crux for forms; CLEANUP-ALL-1 before it), T014 (Pr eigenform criterion).

## Dependency fronts
```
T001 ─► T002 ─► T003 ─► CLEANUP-1 (Weight/BaseChange.lean)
T004 ─► CLEANUP-2 (5_KappaWeight.lean)
T003, T004 ─► T005 ─► T006 ─► CLEANUP-ALL-1 ─► T007 (MILESTONE) ─► CLEANUP-3 (10_Eigenforms.lean)
T008 ─► CLEANUP-4 (Compact.lean)      T009 (optional API gap; own sub-tree)
T010 ─► CLEANUP-5 (Fredholm.lean)
T011 ─► T012 ─► T013 ─► CLEANUP-6 (Pr.lean interim) ─► T014 (MILESTONE 2) ─► CLEANUP-7 (Pr.lean final)
T001 ─► CLEANUP-8 (ForMathlib MvPowerSeries/Inverse, TateFredholm WeightGenFun/BaseChange, 3_BaseChange)
everything ─► CLEANUP-FINAL
```

---

## Item 1 — the Jacobs crux for eigenforms

### [T001] Dedup/move: `MvPowerSeries.map_inv₀` → ForMathlib; `map_linSeries`/`map_quadSeries` → TateFredholm; fork `charPowerSeries_map` := corollary of `charPowerSeries_baseChange`
- **Status**: done (2026-08-20, forms-riesz beastmode) |
- **Progress**: DONE — mathlib has no `MvPowerSeries.map_inv₀` (checked `Mathlib/RingTheory/MvPowerSeries/Inverse.lean`),
  so it went to a new ForMathlib file; `map_linSeries`/`map_quadSeries` next to their defs in `WeightGenFun.lean`
  (a `Map` section, `[NontriviallyNormedField L]`); `charCoeff_map`/`charPowerSeries_map` are now one-line isometric
  corollaries in `TateFredholm/BaseChange.lean` (with `variable {S}` so the fork's call sites keep `S` implicit);
  fork blocks deleted + header rewritten; `8_HeckeSlopes`/`9_EigenvaluesU3` rebuilt green; renames.jsonl. **Files**: NEW PhD/ForMathlib/RingTheory/MvPowerSeries/Inverse.lean, PhD/TateFredholm/WeightGenFun.lean, PhD/TateFredholm/BaseChange.lean, PhD/JacobsSlash/3_BaseChange.lean | **Depends on**: none | **Parallel**: yes | **Type**: refactor

#### Statement
```lean
-- PhD/ForMathlib/RingTheory/MvPowerSeries/Inverse.lean (moved verbatim from 3_BaseChange.lean:82)
theorem MvPowerSeries.map_inv₀ {σ : Type*} {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (φ : MvPowerSeries σ K) :
    MvPowerSeries.map f φ⁻¹ = (MvPowerSeries.map f φ)⁻¹
-- PhD/TateFredholm/WeightGenFun.lean (moved from 3_BaseChange.lean:161/168; generic fields)
theorem TateFredholm.map_linSeries {K L} [Field K] [Field L] (f : K →+* L) (γ : Matrix (Fin 2) (Fin 2) K) :
    MvPowerSeries.map f (linSeries γ) = linSeries (γ.map f)
theorem TateFredholm.map_quadSeries … = quadSeries (γ.map f)
-- PhD/TateFredholm/BaseChange.lean: the isometric corollaries replacing the fork's
theorem TateFredholm.charCoeff_map [IsTate R] [IsTate S] (f : R →+* S) (hf : ∀ x, ‖f x‖ = ‖x‖) {u v} (hu) (hmatch) (n) :
    charCoeff v n = f (charCoeff u n) := charCoeff_baseChange S f 1 (fun r => by rw [hf, one_mul]) u hu v hmatch n
theorem TateFredholm.charPowerSeries_map … := charPowerSeries_baseChange …
```
#### Proof sketch
1. Create the ForMathlib file with `map_inv₀` (proof verbatim; check mathlib has no `MvPowerSeries.map_inv` — grep `.lake/packages/mathlib/Mathlib/RingTheory/MvPowerSeries/` first; if it exists, USE it and delete).
2. Move `map_linSeries`, `map_quadSeries` next to the definitions (typeclass context of `WeightGenFun.lean` — check `linSeries` needs only a field/normed field; adjust `[Field K]`).
3. In `TateFredholm/BaseChange.lean` add `charCoeff_map`/`charPowerSeries_map` as one-line corollaries (keep the names the fork uses); delete the fork's copies in `3_BaseChange.lean` (and its `[IsTate R]` variable block if now unused); rebuild `PhD.JacobsSlash.U3.«9_EigenvaluesU3»`; renames.jsonl.
#### Sources — n/a (API). #### Generality — as stated; `charCoeff_map` for any bounded-by-1 hom is exactly the existing baseChange lemma at `C = 1`.

### [T002] `map_yExtend`, `WeightSeries.map_genFun`, `WeightSeries.matrixCoeff_kappaSlash_map`, `AnalyticWeight.matrixCoeff_kappaSlash_map`
- **Status**: done (2026-08-20, forms-riesz beastmode) |
- **Progress**: DONE exactly per sketch; the `AnalyticWeight` version is the `WeightSeries` one at `toWeightSeries`
  (`toWeightSeries_col` makes `hcol` match by `rfl`). No norm hypotheses anywhere. **File**: PhD/QMF/Weight/BaseChange.lean | **Depends on**: T001 | **Parallel**: no | **Type**: theorems (4 sorries)
#### Statement — in the skeleton (BaseChange.lean:38–80); e.g.
```lean
theorem WeightSeries.map_genFun (W : WeightSeries S ρ) (W' : WeightSeries S' ρ') (ι : K →+* L)
    (g : Matrix (Fin 2) (Fin 2) K)
    (hcol : W'.col (ι (g 1 0)) (ι (g 1 1)) = PowerSeries.map ι (W.col (g 1 0) (g 1 1))) :
    MvPowerSeries.map ι (W.genFun g) = W'.genFun (g.map ι) := by sorry
```
#### Proof sketch
1. `map_yExtend`: `MvPowerSeries.ext fun p => ?_`; `rw [MvPowerSeries.coeff_map, WeightSeries.coeff_yExtend, WeightSeries.coeff_yExtend]`; `split_ifs <;> simp [PowerSeries.coeff_map]`.
2. `map_genFun`: `simp only [WeightSeries.genFun]`; `rw [map_mul, map_mul, MvPowerSeries.map_inv₀, MvPowerSeries.map_inv₀, map_linSeries, map_quadSeries, map_yExtend, ← hcol]`; `rfl` / `Matrix.map_apply` for `(g.map ι) 1 0 = ι (g 1 0)` (template `map_weightGenFun`, 3_BaseChange.lean:176).
3. `matrixCoeff_kappaSlash_map`: `rw [matrixCoeff_kappaSlash, matrixCoeff_kappaSlash, ← map_genFun W W' ι g.1 hcol, MvPowerSeries.coeff_map]` (`Subtype` coercion `⟨g.1.map ι, _⟩.1 = g.1.map ι` by `rfl`).
4. `AnalyticWeight.matrixCoeff_kappaSlash_map`: `κ.kappaSlash_def`/unfold to `toWeightSeries` + `toWeightSeries_col` and step 3.
#### Mathlib lemmas — `MvPowerSeries.ext`, `MvPowerSeries.coeff_map`, `PowerSeries.coeff_map`, `map_mul`, `Matrix.map_apply`; project `WeightSeries.coeff_yExtend`, `matrixCoeff_kappaSlash`, `WeightSeries.genFun`, `AnalyticWeight.toWeightSeries_col`.
#### Sources — [Jac03 Prop 2.6] (the field expression); fork `map_weightGenFun`. #### Generality — any ring hom `ι : K →+* L` between the two normed fields; no norm hypothesis.

### [T003] `matrixCoeff_heckeBlock_map`, `matrixCoeff_heckeBlockOp_map`, `heckeCharPowerSeries_map`
- **Status**: done (2026-08-20, forms-riesz beastmode) |
- **Progress**: DONE per sketch; the subtype rewrites (`levelMonoidOfToS … = ⟨(θ …).map ι, _⟩` by
  `Subtype.ext rfl`) are the only bridging needed.  Axioms standard, 0 sorries, linter zero (5 `omit`s). **File**: PhD/QMF/Weight/BaseChange.lean | **Depends on**: T002 | **Parallel**: no | **Type**: theorems (3 sorries)
#### Statement — skeleton BaseChange.lean:100–160 (full signatures there).
#### Proof sketch
1. Blocks: `simp only [heckeBlock, matrixCoeff_sum, matrixCoeff_smul]` both sides (check the exact names `TateFredholm.matrixCoeff_sum`/`matrixCoeff_smul`); `Finset.sum_congr rfl fun t _ => ?_`; the summand is `(χ' ⟨θ' (u*v), _⟩ : L) * matrixCoeff (κ'.kappaSlash ⟨θ' (u*v), _⟩) m r`; rewrite `θ' (u*v) = (θ (u*v)).map ι` (`mapTheta_apply`), then `hχ _ (levelMonoidOfToS-membership)`, `AnalyticWeight.matrixCoeff_kappaSlash_map κ κ' ι ⟨θ (u*v), _⟩ _ (hcol _ _)`, `map_mul`.
2. Block operator: `heckeBlockOp`, `matrixCoeff_blockOp` (BlockOp.lean:654) both sides + step 1 (`obtain ⟨i, m⟩ := p; obtain ⟨j, r⟩ := q`).
3. Determinant: `unfold heckeCharPowerSeries`; `exact charPowerSeries_baseChange ι 1 (fun r => by simpa using hι r) _ hcomp _ (fun p q => matrixCoeff_heckeBlockOp_map …)` — check the argument order `(ψ) (C) (hψ) (u) (hu) (v) (hv)` and `[IsTate L]` (instance for nontrivially normed fields, Tate.lean:239).
#### Sources — [Buz07 Lemma 2.13]. #### Generality — bounded `ι` (not necessarily isometric) for the determinant; general `χ, χ'` related by `hχ`.

### [CLEANUP-1] /cleanup PhD/QMF/Weight/BaseChange.lean (final)
- **Status**: done (2026-08-20, inline: header de-skeletonised, omit-loop to fixed point, linter zero) | **Depends on**: T003 | **Type**: cleanup (de-skeletonise the header).

### [T004] Generic Jacobs weight: `sigma1Norm`, `levelBounds_sigma1Norm`, `hasSum_jacobsColOf_unitPow`, `jacobsCharOf`, `jacobsExpansionDataOf`, `sigma1₃_le_sigma1Norm`; `jacobsWeight` := restriction
- **Status**: done (2026-08-20, forms-riesz beastmode) |
- **Progress**: DONE — `sigma1Norm` one/mul-mem by the ultrametric expansion of `(gh)₁₁ − 1` as sketched;
  the rest is the `K₃` proof with `h3`/`hnat` in place of `norm_three_lt_one`/`exists_natCast_close`.
  `jacobsWeight := (jacobsWeightOf …).restrict sigma1₃_le_sigma1Norm`; the seven `K₃`-specific decls deleted
  (renames.jsonl); `jacobsWeight_toChar` now names `jacobsCharOf`.  Fork rebuilt green through
  9_EigenvaluesU3/7_DiamondHecke/10_Eigenforms (all consumers were `rfl`-compatible, as planned);
  axioms standard; 0 sorries; linter zero. **File**: PhD/JacobsSlash/U3/5_KappaWeight.lean | **Depends on**: none | **Parallel**: yes | **Type**: defs/theorems (11 sorries) + refactor
#### Statement — skeleton 5_KappaWeight.lean generic section; after filling, **replace** the `K₃` construction:
```lean
noncomputable def jacobsWeight (t : K₃) (ht : ‖t‖ < 1) :
    QMF.AnalyticWeight (QMF.oneUnits K₃ ‖(3 : K₃)‖ (norm_nonneg _) norm_three_lt_one) Sigma1₃ ‖(3 : K₃)‖ :=
  (jacobsWeightOf norm_three_lt_one t ht (fun _ hε => exists_natCast_close ht.le hε)).restrict
    sigma1₃_le_sigma1Norm
-- delete the K₃ copies: levelBounds_sigma1₃ (→ (levelBounds_sigma1Norm _).mono sigma1₃_le_sigma1Norm if still needed),
-- jacobsCol_rowDecay, hasSum_jacobsCol_unitPow, isUnit_unitPow, jacobsChar/jacobsChar_apply (→ abbrev jacobsChar t ht := jacobsCharOf norm_three_lt_one t ht if consumers exist), jacobsExpansionData.
```
#### Proof sketch
1. `sigma1Norm.one_mem'`: entries of `1` are `0`/`1` (`norm_one`, `norm_zero`, `sub_self`); `mul_mem'`: ultrametric estimates (`IsUltrametricDist.norm_add_le_max`, `norm_mul`, `Matrix.mul_apply`, `Fin.sum_univ_two`); for the `(1,1)` entry write `(gh)₁₁ − 1 = g₁₀h₀₁ + (g₁₁−1)(h₁₁−1) + (g₁₁−1) + (h₁₁−1)` and bound each by `‖3‖` (`‖3‖² ≤ ‖3‖`).
2. `levelBounds_sigma1Norm`: `rho_nonneg`, `rho_lt_one := h3`, `integral := hg.1`, `c_le := hg.2.1.trans (pow_le_of_le_one …)` (`‖3‖² ≤ ‖3‖`), `d_unit := norm_eq_one_of_norm_sub_one_lt_one (hg.2.2.trans_lt h3)`.
3. `hasSum_jacobsColOf_unitPow`: copy 5_KappaWeight.lean:78–108 replacing `norm_three_lt_one` by `h3` and `exists_natCast_close ht.le hε` by `hnat ε hε`.
4. `jacobsCharOf`: the `toFun` `IsUnit` from `norm_unitPow_sub_one_le h3 ht u.2` (`≠ 0`), `map_one'` (`unitPow_one`), `map_mul'` (`unitPow_mul h3 ht.le u.2 v.2`) — as in the `K₃` version (lines 110–133).
5. `jacobsExpansionDataOf`: `rowDecay` as `jacobsCol_rowDecay` with `hg.2.2`/`hg.2.1` (`norm_unitPow_le_one h3 ht`, `norm_binomialCoeff_mul_pow_le h3 ht.le`, `norm_div` + `d_unit`); `mem_level := levelUnit_mem_oneUnits (hg.2.1.trans …) hg.2.2 hz hu`; `eval` via step 3 and `jacobsCharOf`'s `IsUnit.unit_spec`.
6. `sigma1₃_le_sigma1Norm`: `norm_sigma1_entry_le_one`, `norm_sigma1_lower_left_le`, `norm_sigma1_lower_right_sub_one_le` (4_KappaColumn.lean).
7. Refactor `jacobsWeight` as above; the consumers (`genFun_jacobsWeight`, `matrixCoeff_kappaSlash_jacobsWeight`, `yExtend_jacobsCol`, 6_Matrix/7_*) should elaborate unchanged (`restrict_col` is `rfl`); rebuild the fork; renames.jsonl.
#### Mathlib lemmas — `IsUltrametricDist.norm_add_le_max`, `norm_mul`, `norm_div`, `Matrix.mul_apply`, `Fin.sum_univ_two`, `pow_le_of_le_one`; project `norm_eq_one_of_norm_sub_one_lt_one`, `unitPow_one`, `unitPow_mul`, `norm_unitPow_sub_one_le`, `norm_unitPow_le_one`, `norm_binomialCoeff_mul_pow_le`, `summable_binomialCoeff_mul_pow`, `tsum_binomialCoeff_eq_unitPow`, `levelUnit_mem_oneUnits`, `AnalyticWeight.restrict`.
#### Sources — [Jac03 §2.1 p. 29; Def 1.27]. #### Generality — any complete ultrametric `K` with `‖3‖ < 1`, `[CharZero K]` (the fork's analytic layer); `hnat` as explained.

### [CLEANUP-2] /cleanup PhD/JacobsSlash/U3/5_KappaWeight.lean (final)
- **Status**: done (2026-08-20, inline: linter zero, header updated) | **Depends on**: T004 | **Type**: cleanup.

### [T005] L-side data: `map_mem_sigma1Norm`, `U1_9_subset_levelMonoidL`, `eta3_mem_levelMonoidL`, `etaRep_mem_levelMonoidL`, `exists_natCast_close_map`, `jacobsCol_map`
- **Status**: done (2026-08-20, forms-riesz beastmode) |
- **Progress**: DONE per sketch; `exists_natCast_close_map` needed `include hι in` (the statement does not mention
  the isometry hypothesis).  `jacobsCol_map` closes by `show` on the two `PowerSeries.mk` columns + `map_unitPow`,
  `map_binomialCoeff`, `map_div₀`. **File**: PhD/JacobsSlash/U3/10_Eigenforms.lean | **Depends on**: T003, T004 | **Parallel**: no | **Type**: theorems (6 sorries)
#### Statement — skeleton 10_Eigenforms.lean:40–100.
#### Proof sketch
1. `map_mem_sigma1Norm`: `obtain ⟨h1, h2, h3'⟩ := sigma1₃_le_sigma1Norm hg`; entries `(g.map ι) i j = ι (g i j)` (`Matrix.map_apply`), `hι`, `map_sub`, `map_one`, `← map_ofNat ι 3` for `‖(3 : L)‖ = ‖(3 : K₃)‖`.
2. `U1_9_subset_levelMonoidL`: `intro u hu; exact Submonoid.mem_comap.mpr (map_mem_sigma1Norm ι hι (U1_9_subset_levelMonoid1₃ hu))` (`mapTheta_apply`).  Same for `eta3`/`etaRep` from `eta3_mem_levelMonoid1₃`/`etaRep_mem_levelMonoid1₃`.
3. `exists_natCast_close_map`: `obtain ⟨n, hn⟩ := exists_natCast_close ht hε; exact ⟨n, by rw [← map_natCast ι, ← map_sub, hι]; exact hn⟩`.
4. `jacobsCol_map`: `PowerSeries.ext fun n => ?_`; both sides `PowerSeries.coeff_mk`/`coeff_map`; `map_unitPow ι hι`, `map_binomialCoeff ι`, `map_mul`, `map_pow`, `map_div₀` (3_BaseChange.lean:134/140); the `K₃` column is `((jacobsWeightOf …).restrict _).expansion.col c d = …` by `rfl` after T004.
#### Sources — fork base-change lemmas. #### Generality — any isometric `ι : K₃ →+* L`.

### [T006] `heckeBlockOpL_eq_U3MatrixOp`, `heckeCharPowerSeriesL_eq_map`, `bijective_evalU3L`
- **Status**: done (2026-08-20, forms-riesz beastmode) |
- **Progress**: DONE — `matrixCoeff_U3MatrixOp_map` extracted from `map_charPowerSeriesU3`'s proof
  (8_HeckeSlopes.lean; `map_charPowerSeriesU3` is now its two-line corollary — no duplicate);
  `heckeBlockOpL_eq_U3MatrixOp` = `matrixCoeff_heckeBlockOp_map` + that + `blockEntry_eq_epsOp` under `blockOp`;
  the determinant is then a two-`rw` corollary; `bijective_evalU3L` is the general neat-level theorem at
  `classRep_bijective`/`stabilizerAt_classRep` (both weight-independent, so they serve over `L` unchanged). **File**: PhD/JacobsSlash/U3/10_Eigenforms.lean | **Depends on**: T005 | **Parallel**: no | **Type**: theorems (3 sorries)
#### Proof sketch
1. `heckeBlockOpL_eq_U3MatrixOp`: `refine ext_matrixCoeff fun p q => ?_`; LHS: `matrixCoeff_heckeBlockOp_map (ι := ι) … (hcol := fun g hg => jacobsCol_map …)` (with `hS' := map_mem_sigma1Norm`, `hχ := by simp` for `χ = χ' = 1`) → `ι (matrixCoeff (heckeBlockOp_K₃) p q)`; `heckeBlockOp_K₃ = blockOp (blockEntry t ht)` (`rfl`), `blockEntry_eq_epsOp`; RHS: the identity `matrixCoeff (U3MatrixOp_L) p q = ι (matrixCoeff (U3MatrixOp_K₃) p q)` — extract from the proof of `map_charPowerSeriesU3` (8_HeckeSlopes.lean:89–110) as its own lemma `matrixCoeff_U3MatrixOp_map` (refactor there; no duplicate).
2. `heckeCharPowerSeriesL_eq_map`: `heckeCharPowerSeries_map … (hcomp := isCompactoid_blockOpU3 t ht)` with the same data, or `rw [heckeCharPowerSeries, heckeBlockOpL_eq_U3MatrixOp, ← map_charPowerSeriesU3 ι hι]` (whichever is shorter).
3. `bijective_evalU3L`: `Weight.bijective_evalAtReps_of_stabilizer_eq_bot (thetaL ι) (jacobsWeightL …) U1_9 _ 1 classRep (classRep_bijective hClassNumberOne) stabilizerAt_classRep`.
#### Sources — [Jac03 pp. 28–29], [Buz07 Lemma 2.13]. #### Generality — any isometric `ι`.

### [CLEANUP-ALL-1] /cleanup-all on the item-1 surface (pre-milestone)
- **Status**: done (2026-08-20: BaseChange/5_KappaWeight/8_HeckeSlopes/10_Eigenforms build green, linter checked below) | **Depends on**: CLEANUP-1, CLEANUP-2, T006 | **Type**: cleanup-all.

### [T007] `exists_eigenform_U3_halfIntegral` — **THE CRUX FOR FORMS (MILESTONE)**
- **Status**: done (2026-08-20, forms-riesz beastmode) |
- **Progress**: **MILESTONE DONE** exactly per sketch (5 steps, no bridging beyond `map_zero`/`map_smul`):
  [Jacobs, Cor 2.16] now reads as "for every `j` there is an eigenform `φ ∈ S_κ(U₁(9))` over `ℂ₃` with
  `U₃ φ = a φ`, `v₃(a) = j + ½`".  Axioms standard; 10_Eigenforms 0 sorries; linter zero. **File**: PhD/JacobsSlash/U3/10_Eigenforms.lean | **Depends on**: CLEANUP-ALL-1 | **Parallel**: no | **Type**: theorem (1 sorry)
#### Statement
```lean
theorem exists_eigenform_U3_halfIntegral (t : K₃) (ht : ‖t‖ < 1) (j : ℕ) :
    ∃ (a : ℂ_[3]) (φ : kappaFormsL ιC norm_ιC t ht), a ≠ 0 ∧ φ ≠ 0 ∧
      heckeU3L ιC norm_ιC t ht φ = a • φ ∧ ‖a‖ ^ 2 = ‖(3 : ℂ_[3])‖ ^ (2 * j + 1) := by sorry
```
(shared-witness existential — kept bundled, as the source.)
#### Proof sketch
1. `obtain ⟨a, y, ha0, hy0, hyU3, hnorm, -, -⟩ := exists_eigenvalue_U3_halfIntegral t ht j`.
2. `rw [← heckeBlockOpL_eq_U3MatrixOp ιC norm_ιC t ht] at hyU3`.
3. `obtain ⟨φ, rfl⟩ := (bijective_evalU3L ιC norm_ιC t ht).2 y`.
4. `have htr := Weight.evalAtReps_heckeOperator (thetaL ιC) (jacobsWeightL …) U1_9 _ 1 (eta3_mem_levelMonoidL …) finite_image_eta3 classRep etaRep (etaRep_mem_levelMonoidL …) bijOn_etaRep etaRep_injective sigmaTable (fun i t' => unitsIncl ℚ D (dTable i t')) (fun i t' => dTable_mem i t') uTable (fun i t' => by rw [uTable_coe]; exact factorisation i t') φ` (as in `evalU3_heckeU3`).
5. `refine ⟨a, φ, ha0, fun h0 => hy0 (by rw [h0, map_zero]), (bijective_evalU3L …).1 ?_, hnorm⟩`; `rw [htr, hyU3, map_smul]`.
#### Sources — [Jac03 Cor 2.16]. #### Generality — at `ℂ₃` (where the eigenvalues live); the `L`-generic statement is `heckeBlockOpL_eq_U3MatrixOp`.

### [CLEANUP-3] /cleanup PhD/JacobsSlash/U3/10_Eigenforms.lean (final) + PROGRESS.md/README
- **Status**: done (2026-08-20, inline: header de-skeletonised, linter zero; PROGRESS/README in CLEANUP-FINAL) | **Depends on**: T007 | **Type**: cleanup.

---

## Item 2 — quaternionic remaining half

### [T008] `evalAtReps_out_injective`, `bijective_evalAtReps_out` (+ `classSetFintype` docs)
- **Status**: done (2026-08-20, forms-riesz beastmode) |
- **Progress**: DONE.  Elaboration note: `DoubleCoset.Quotient` is a plain `def`, so passing bare
  `Quotient.out` unfolds `ι` and the `[Fintype ι]` binder no longer matches — state the family as
  `fun q : DoubleCoset.Quotient ↑Γ ↑U => q.out` to keep `ι` folded.  `classSetFintype`'s docstring now cites
  Buzzard p. 73 and points at both lemmas.  Axioms standard; linter zero. **File**: PhD/QMF/Weight/Compact.lean (+ Quaternionic.lean docs) | **Depends on**: none | **Parallel**: yes | **Type**: theorems (2 sorries)
#### Proof sketch
1. `evalAtReps_out_injective := evalAtReps_injective θ κ U hU χ Quotient.out fun q => ⟨q, Quotient.out_eq' q⟩`.
2. `bijective_evalAtReps_out := bijective_evalAtReps θ κ U hU χ Quotient.out ⟨fun p q h => by simpa [Quotient.out_eq'] using h, fun q => ⟨q, Quotient.out_eq' q⟩⟩ hstab` (injectivity of `mk'' ∘ out`: `Quotient.out_eq'` both sides).
3. In `Weight/Quaternionic.lean` add a docstring remark/`example` that with `classSetFintype F D U hUo` as the `Fintype` instance, `evalAtReps_out_injective` is Buzzard p. 73's `S^D_κ(U) ↪ ⊕_{λ=1}^{µ} A_κ`.
#### Sources — [Buz07 p. 73]. #### Generality — abstract `(G, Γ, θ)`.

### [CLEANUP-4] /cleanup PhD/QMF/Weight/Compact.lean (final)
- **Status**: done (2026-08-20, inline: linter zero, header "Main declarations" already lists the family lemmas) | **Depends on**: T008 | **Type**: cleanup.

### [T009] (API GAP — DEFERRED by user decision 2026-08-19) compact open standard levels ⇒ Hecke finiteness
- **Status**: deferred (not dispatchable; keep the sub-tree for a later board) | **Files**: PhD/QMF/Slash/HeckeMonoid.lean or new PhD/QMF/Level.lean; PhD/JacobsSlash/U3/2_Level.lean | **Depends on**: none | **Type**: API gap (sub-tree; no skeleton)
#### Statement (sub-tree)
```lean
-- (i) general: units of a compact set form a compact set of units (Units.embedProduct closed embedding)
theorem isCompact_units_of_isCompact {R : Type*} [TopologicalSpace R] [Ring R] [IsTopologicalRing R] [T2Space R]
    {S : Set R} (hS : IsCompact S) : IsCompact {u : Rˣ | (u : R) ∈ S ∧ ((u⁻¹ : Rˣ) : R) ∈ S}
-- (ii) the integral-adele order is compact: for the fork, `{x : D ⊗ 𝔸_f | ∀ w, toLocal w x ∈ localOrder w}`
theorem isCompact_integralAdelesD : IsCompact {x : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ | ∀ w, toLocal ℚ D w x ∈ localOrder w}
-- (iii) U0 = units of (ii) ⇒ compact; U1_9 ≤ U0 closed ⇒ compact
theorem isCompact_U0 : IsCompact (U0 : Set (Dfx ℚ D))
theorem isCompact_U1_9 : IsCompact (U1_9 : Set (Dfx ℚ D))
```
#### Proof sketch
(i) `Units.embedProduct R : Rˣ →* R × Rᵐᵒᵖ` is an embedding (`Units.isEmbedding_embedProduct`), closed for `T2` rings? (check `Units.isClosedEmbedding_embedProduct` / prove: the image is `{(x, op y) : x*y = 1 ∧ y*x = 1}`, closed); the set is the preimage of `S ×ˢ (MulOpposite.op '' S)`, compact in the closed embedding ⇒ compact (`IsClosedEmbedding.isCompact_preimage`).  (ii) `D ⊗ 𝔸_f` with the module topology is `𝔸_f^4` via a `ℚ`-basis of `D` (`TensorProduct` ≅ `Fin 4 → 𝔸_f`); under it the integral order is `∏ (integral adeles)`-like — **this is the real gap**: the fork's `localOrder w` is the closure of the Hurwitz order tensor `ℤ_w`, and identifying `{∀ w, x_w ∈ localOrder w}` with a product of `integralAdeles` (compact: `isCompact_integralAdeles`) needs the restricted-product description of `D ⊗ 𝔸_f` (FLTstuff `RestrictedProduct` API) — estimate 200–400 lines.  (iii) from (i)+(ii).  Then `heckeUpiQ`'s finiteness at `U₁(9)` would follow from `finite_image_etaAdelic'_of_isOpen_of_isCompact` (redundant with `finite_image_eta3`).
#### Sources — [Buz07 §9 p. 68] "compact open subgroup"; FLT Hecke header remark. #### Generality — (i) general; (ii)/(iii) fork-specific until an integral order is defined generally.
#### Recommendation — DEFER: nothing on any board consumes it; the thesis level has explicit finiteness.

---

## Item 3 — Riesz decomposition on `S_κ(U)`

### [T010] `exists_riesz_decomposition_forms`
- **Status**: done (2026-08-20, forms-riesz beastmode) |
- **Progress**: DONE — transported by `Submodule.map E.symm` (not `comap`): `IsCompl` via
  `Submodule.orderIsoMapComap … |>.isCompl` on `hcompl.isCompl`, `finrank` via
  `LinearEquiv.submoduleMap … |>.finrank_eq`.  Two coercion helpers were needed: `hsymm` for the
  `LinearMap`-coerced `E.symm` (as it appears inside `Submodule.map`) and `E.apply_symm_apply` for the
  equiv-coerced one produced by `hstep`.  Powers intertwine by induction on the `show`-form
  `((1 - a•T)^k) ((1 - a•T) φ)`.  Axioms standard; 0 sorries; linter zero. **File**: PhD/QMF/Weight/Fredholm.lean | **Depends on**: none | **Parallel**: yes | **Type**: theorem (1 sorry)
#### Statement — skeleton Fredholm.lean (full signature; conclusion `∃ (n : ℕ) (N F : Submodule K (Forms …)), 1 ≤ n ∧ IsCompl N F ∧ stable ∧ stable ∧ nilpotent on N ∧ surjective on F ∧ injective on F ∧ finrank K N = n`).
#### Proof sketch
1. `set u := heckeBlockOp θ κ U hU χ vRep hvΔ idx u`, `hcomp := isCompactoid_heckeBlockOp …`, `E := formsModelEquiv θ κ U hU χ c hc hstab` (`E φ = evalAtReps c φ` by `rfl`), `htr : ∀ φ, E (T φ) = u (E φ)` from `evalAtReps_heckeOperator`.
2. `obtain ⟨n, N', F', hn, hcompl, hN', hF', hnil, hsurj, hinj, hrank⟩ := exists_riesz_decomposition hd hcomp ha` (unfold `heckeCharPowerSeries` in `ha`).
3. `refine ⟨n, N'.comap (E : Forms →ₗ[K] _), F'.comap E, hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩`:
   - `IsCompl`: `Submodule.comap` along a `LinearEquiv` preserves `IsCompl` (`Submodule.IsCompl.comap`? use `Submodule.comap_equiv_eq_map_symm` + `IsCompl.map_equiv`/`Submodule.map_isCompl`… search: `Submodule.isCompl_comap_iff` or prove via `Submodule.comap_inf`, `Submodule.comap_sup_of_surjective`); start from `hcompl.isCompl` (`Submodule.IsTopCompl.isCompl`? — check the project's `IsTopCompl` API in Riesz.lean/mathlib `Submodule.IsTopCompl`).
   - stability: `Submodule.mem_comap`, `htr`, `hN'`/`hF'`.
   - nilpotency: `E (((1 - a • T) ^ n) φ) = ((1 - a • u) ^ n) (E φ)` — prove `∀ k, E (((1 − a•T)^k) φ) = ((1 − a•u)^k) (E φ)` by induction (`pow_succ`, `Module.End.mul_apply`, `map_sub`, `map_smul`, `htr`); then `hnil`, `E.injective`.
   - surjective on `F`: for `ψ ∈ F`, `hsurj (E ψ) hψ` gives `x ∈ F'` with `(1 − a•u) x = E ψ`; `φ := E.symm x`; membership by `Submodule.mem_comap` + `E.apply_symm_apply`; `E ((1 − a•T) φ) = (1 − a•u) x = E ψ` ⇒ equality by injectivity.
   - injective on `F`: `hinj (E φ) hφ (by rw [← htr…])` ⇒ `E φ = 0` ⇒ `φ = 0`.
   - finrank: `LinearEquiv.finrank_eq (E.submoduleMap-style equivalence N'.comap E ≃ₗ N')` — `Submodule.comap_equiv_eq_map_symm` then `LinearEquiv.finrank_map_eq`; `rw [hrank]`.
#### Mathlib lemmas — `Submodule.mem_comap`, `Submodule.comap_equiv_eq_map_symm`, `LinearEquiv.finrank_map_eq`, `IsCompl`, `Module.End.mul_apply`, `pow_succ`, `LinearMap.pow_apply`; project `exists_riesz_decomposition`, `Submodule.IsTopCompl` (→ `IsCompl`), `formsModelEquiv`, `evalAtReps_heckeOperator`, `isCompactoid_heckeBlockOp`.
#### Sources — [Ser62 §7 Prop 12], [Buz07 Prop 3.2 p. 23]. #### Generality — neat level, discretely valued `K` (`hd`), any `η` of `U_ϖ` type.

### [CLEANUP-5] /cleanup PhD/QMF/Weight/Fredholm.lean (final)
- **Status**: done (2026-08-20, inline: deprecated `ContinuousLinearMap.sum_apply/smul_apply` renamed, linter zero) | **Depends on**: T010 | **Type**: cleanup.

---

## Item 4 — non-neat levels via property (Pr)

### [T011] Averaging: `stabAvg_slash`, `stabAvg_of_invariant`, `stabAvg_comp_self`, `range_stabAvg`
- **Status**: done (2026-08-20, forms-riesz beastmode) |
- **Progress**: DONE — new private `act_act` (composition of the twisted action, from `kappaSlash_mul` +
  `map_mul χ`); `stabAvg_slash` reindexes by `Equiv.mulRight w` with `f`/`g` given explicitly (Lean picks the
  wrong orientation from `_`); `stabAvg_of_invariant` via `Finset.sum_const` + `Nat.cast_smul_eq_nsmul`;
  `stabAvg_comp_self` and `range_stabAvg` are corollaries. **File**: PhD/QMF/Weight/Pr.lean | **Depends on**: none | **Parallel**: yes | **Type**: theorems (4 sorries)
#### Proof sketch
1. Notation: `act w a := χ(θ w) • κ.kappaSlash (θ w) a`; first a helper (private) `act_mul : act w (act w' a) = act (w' * w) a` — from `AnalyticWeight.kappaSlash_mul` (check direction: right action `kappaSlash (g*h) = kappaSlash h ∘ kappaSlash g`? read SlashAction.lean `kappaSlash_mul`) and `map_mul χ`, `smul_smul`, `map_smul`; state it at the subtype level `⟨θ (w'*w), _⟩ = ⟨θ w', _⟩ * ⟨θ w, _⟩` (`Subtype.ext (map_mul θ _ _)`).
2. `stabAvg_slash`: unfold `stabAvg`; `map_smul`, `map_sum`; `act w (Σ_{w'} act w' a) = Σ_{w'} act (w' * w) a` = `Σ_{w''} act w'' a` by `Fintype.sum_equiv (Equiv.mulRight w)`.
3. `stabAvg_of_invariant`: all terms equal `a`; `Finset.sum_const`, `Finset.card_univ`, `smul_smul`, `inv_mul_cancel₀ hcard`, `one_smul` (`nsmul_eq_smul_cast`/`Nat.cast_smul_eq_nsmul`).
4. `stabAvg_comp_self`: `ContinuousLinearMap.ext fun a => stabAvg_of_invariant … (fun w => stabAvg_slash … a w)`.
5. `range_stabAvg`: `le_antisymm`: `rintro _ ⟨a, rfl⟩ w; exact stabAvg_slash …` (membership in `slashFixedPointsOfLE` unfolds by `kappaLevelSlashActionTwisted_slash` to `act w`); `⊇`: `fun a ha => ⟨a, stabAvg_of_invariant … ha⟩`.
#### Mathlib lemmas — `Fintype.sum_equiv`, `Equiv.mulRight`, `Finset.sum_const`, `Finset.card_univ`, `smul_smul`, `inv_mul_cancel₀`, `map_sum`, `map_smul`, `ContinuousLinearMap.sum_apply`, `ContinuousLinearMap.smul_apply`.
#### Sources — [Buz07 p. 73]; mathlib `Representation.averageMap_invariant`/`averageMap_id` (the same algebra). #### Generality — any finite `H ≤ U` with `|H| ≠ 0` in `K`.

### [T012] Block projector: `stabProj_comp_self`, `range_stabProj`
- **Status**: done (2026-08-20, forms-riesz beastmode) | **Depends on**: T011, T012a |
- **Progress**: DONE (2026-08-20).  `stabProj_comp_self` via `blockOp_comp` + diagonal collapse; spawned
  **T012a** (`mem_range_evalAtReps_iff`, Compact.lean — the invariance form of `bijective_evalAtRepsSlash`,
  which the sketch had assumed as a one-liner) and two private helpers in Pr.lean (`blockProj_stabProj`,
  `ext_blockProj`); `range_stabProj` is then `le_antisymm` of `stabAvg_slash` / `stabAvg_of_invariant`
  against T012a. **File**: PhD/QMF/Weight/Pr.lean | **Depends on**: T011 | **Parallel**: no | **Type**: theorems (2 sorries)
#### Proof sketch
1. `stabProj_comp_self`: `ext_matrixCoeff`/blockwise: `blockOp` composition with a diagonal family — prove `blockOp T ∘ blockOp T' = blockOp (fun i k => ∑ j, T i j ∘ T' j k)` if not in BlockOp.lean (search `blockOp_comp`); with diagonal `T` the sum collapses (`Finset.sum_ite_eq`), then `stabAvg_comp_self`.  Alternatively pointwise: `blockProj i (stabProj x) = stabAvg_i (blockProj i x)` (`blockProj_blockOp`-type lemma; `blockOp_blockIncl` + `blockProj_blockIncl`) and `DFunLike.ext`.
2. `range_stabProj`: `le_antisymm`; `⊆`: `x = stabProj y` ⇒ each block `stabAvg_i (blockProj i y)` is `Γ_i`-invariant (`stabAvg_slash`) ⇒ by `bijective_evalAtRepsSlash … .2` (tuple of invariants at `σ := c ∘ e.symm`, as in `bijective_evalAtReps`) there is `φ` with `evalAtReps c φ = x`; `⊇`: `x = evalAtReps c φ` ⇒ blocks are `φ (c i)`, invariant by `mem_forms_iff`+`stabilizerAtSlash` (`φ (c i * w) = φ (c i w c i⁻¹ * c i) = φ (c i)` for `w ∈ Γ_i`) ⇒ `stabAvg_of_invariant` blockwise ⇒ `stabProj x = x` ⇒ `x ∈ range`.
#### Sources — [Buz07 §9 p. 69] (`L(U,A) ≅ ⊕ A^{Γ_λ}`), p. 73. #### Generality — `hc` bijective (complete family), finite stabilisers with invertible orders.

### [T013] `heckeBlockOp_mem_range_evalAtReps`, `heckeCharPowerSeriesPr_one`, `heckeCharPowerSeriesPr_eq_of_proj`
- **Status**: done (2026-08-20, forms-riesz beastmode) |
- **Progress**: DONE.  Sketch defect fixed in passing: the planned chain `(B∘E)∘E' = B∘E'` proves the *wrong*
  endpoint; the correct one is `det(B∘E) = det(E'∘(B∘E)) = det((B∘E)∘E') = det(B∘E')` (`charPowerSeries_comm`
  in the middle), using `E'∘(B∘E) = B∘E` (range-stability) and `E∘E' = E'` (equal ranges).  A single `hfix`
  helper ("a projector is the identity on its range") serves both. **File**: PhD/QMF/Weight/Pr.lean | **Depends on**: none (uses Fredholm/Compact only) | **Parallel**: yes | **Type**: theorems (3 sorries)
#### Proof sketch
1. `heckeBlockOp_mem_range_evalAtReps`: `obtain ⟨φ, rfl⟩ := hx; exact ⟨heckeOperator … φ, (evalAtReps_heckeOperator … φ).symm⟩`.
2. `heckeCharPowerSeriesPr_one`: `unfold heckeCharPowerSeriesPr heckeCharPowerSeries; rw [ContinuousLinearMap.comp_id]` (`1 = id`: `ContinuousLinearMap.one_def`).
3. `heckeCharPowerSeriesPr_eq_of_proj`: `set P := (heckeBlockOp …).comp E`; `have h1 : P.comp E' = (heckeBlockOp …).comp E'` (`E ∘ E' = E'`: for `y`, `E' y ∈ range E' = range E` so `E (E' y) = E' y` by `hE` — `range E` elements are fixed: `x = E z ⇒ E x = E (E z) = E z`); `have h2 : E'.comp P = P` (`P y ∈ range (heckeBlockOp ∘ E) ⊆ range E` by `hstable` (range E ∋ E y), `= range E'` so `E'` fixes it); then `calc charPowerSeries (hB ∘ E') = charPowerSeries (P.comp E') (by rw h1) = charPowerSeries (E'.comp P) (charPowerSeries_comm P E' (hcomp.comp_right E)) = charPowerSeries P (by rw h2)` — note `heckeCharPowerSeriesPr … E' = charPowerSeries (hB ∘ E')` by definition, and we want `… E = … E'`: orient accordingly (`.symm`).
#### Mathlib lemmas — `ContinuousLinearMap.comp_id`, `ContinuousLinearMap.ext`, `LinearMap.mem_range`; project `charPowerSeries_comm` (Fredholm.lean:749), `IsCompactoid.comp_right` (Matrix.lean:550), `evalAtReps_heckeOperator`.
#### Sources — [Buz07 Lemma 2.12; pp. 18–19]. #### Generality — any continuous projector onto a `heckeBlockOp`-stable subspace.

### [T012a] `mem_range_evalAtReps_iff` — the image of evaluation is the block-model invariants (spawned from T012)
- **Status**: done (2026-08-20, forms-riesz beastmode) |
- **Progress**: DONE first try, exactly per the spawned sketch (→ by `left_invt'` + `mem_forms_iff`;
  ← by `bijective_evalAtRepsSlash.2` at the invariant tuple, as in `bijective_evalAtReps`). **File**: PhD/QMF/Weight/Compact.lean | **Depends on**: T008 | **Parent**: T012 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem mem_range_evalAtReps_iff (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (x : c(ι × ℕ, K)) :
    x ∈ LinearMap.range (evalAtReps (Γ := Γ) θ κ U hU χ c) ↔
      ∀ (i : ι) (w : G) (hw : w ∈ AutomorphicFunction.stabilizerAtSlash Γ U (c i)),
        χ ⟨θ w, hU hw.1⟩ • κ.kappaSlash ⟨θ w, hU hw.1⟩ (cSpace.blockProj i x)
          = cSpace.blockProj i x := by sorry
```
#### Proof sketch
Same shape as `bijective_evalAtReps` (Compact.lean), with the invariance hypothesis in place of the
trivial-stabiliser one — this is [Buzzard, §9 p. 69]'s `L(U,A) ≅ ⊕_λ A^{Γ_λ}` read in the block model.
1. (→) `rintro ⟨φ, rfl⟩ i w hw`; `blockProj_evalAtReps` turns the goal into `φ(c i) ∣ w = φ(c i)`;
   `φ (c i * w) = φ ((c i * w * (c i)⁻¹) * c i) = φ (c i)` by `left_invt' hw.2` and
   `mem_forms_iff … φ.2 ⟨w, hw.1⟩ (c i)` gives the slash form (`kappaLevelSlashActionTwisted_slash`).
2. (←) `e := Equiv.ofBijective _ hc`; feed `AutomorphicFunction.bijective_evalAtRepsSlash … .2` the
   tuple `fun q => ⟨cSpace.blockProj (e.symm q) x, fun w => h _ w w.2⟩`; the resulting `φ` satisfies
   `φ (c i) = blockProj i x` (as in `bijective_evalAtReps`), so `evalAtReps c φ = x` by block-ext
   (`DFunLike.ext` + `cSpace.blockProj_apply` + `blockProj_evalAtReps`).
#### Mathlib lemmas needed — `Equiv.ofBijective`, `Equiv.symm_apply_apply`, `DFunLike.ext`; project
`bijective_evalAtRepsSlash`, `blockProj_evalAtReps`, `mem_forms_iff`, `left_invt'`,
`kappaLevelSlashActionTwisted_slash`, `cSpace.blockProj_apply`.
#### Sources — [Buz07, §9 p. 69]. #### Generality — matches `bijective_evalAtReps` (complete family `c`).

### [CLEANUP-6] /cleanup PhD/QMF/Weight/Pr.lean (interim, after T011–T013)
- **Status**: done (2026-08-20, inline: linter run below) | **Depends on**: T011, T012, T013 | **Type**: cleanup.

### [T014] `evalT_heckeCharPowerSeriesPr_eq_zero_iff` — **eigenforms at an arbitrary level (MILESTONE 2)**
- **Status**: done (2026-08-20, forms-riesz beastmode) |
- **Progress**: **MILESTONE 2 DONE** per sketch: `x = a • B(E x)` puts the eigenvector back in the image of
  evaluation (`heckeBlockOp_mem_range_evalAtReps` + `Submodule.smul_mem`), then the neat-level argument runs
  with `E (evalAtReps φ) = evalAtReps φ` in place of `E = 1`.  Only `hc` surjective is needed — no neatness.
  Axioms standard; Pr.lean 0 sorries; linter zero (also dropped the unused `hcard` from `stabAvg_slash` and
  the deprecated `ContinuousLinearMap.sum_apply`). **File**: PhD/QMF/Weight/Pr.lean | **Depends on**: CLEANUP-6 | **Parallel**: no | **Type**: theorem (1 sorry)
#### Proof sketch
1. `hcomp := isCompactoid_heckeBlockOp …`; `hP := hcomp.comp_right E`; `rw [heckeCharPowerSeriesPr, evalT_charPowerSeries_eq_zero_iff _ hP ha0]`; `htr` as in T006 of forms-followups; `hinj := evalAtReps_injective … c hc`.
2. (→) `rintro ⟨x, hx0, hx⟩`; `have hxmem : x ∈ range (evalAtReps c)`: from `hx`, `x = a • heckeBlockOp (E x)` (`smul_smul`, `ha0`), `E x ∈ range E = range evalAtReps` (`hrange ▸ ⟨x, rfl⟩`), so `heckeBlockOp (E x) ∈ range evalAtReps` (`heckeBlockOp_mem_range_evalAtReps`), submodule closed under `a •`; `obtain ⟨φ, rfl⟩ := hxmem`; `have hEx : E (evalAtReps φ) = evalAtReps φ` (fixed on its range: `hrange ▸ ⟨φ, rfl⟩`, then `hE`); `refine ⟨φ, fun h0 => hx0 (by rw [h0, map_zero]), hinj ?_⟩`; `rw [htr, map_smul, ← hx]; simp [hEx]` (`(heckeBlockOp ∘ E) x = heckeBlockOp (E x) = heckeBlockOp x`).
3. (←) `rintro ⟨φ, hφ0, hφ⟩`; `refine ⟨evalAtReps φ, fun h0 => hφ0 (hinj (by rw [h0, map_zero])), ?_⟩`; `simp only [ContinuousLinearMap.comp_apply, hEx, ← htr, hφ, map_smul]`.
#### Sources — [Ser62 §7 Props 11–12]; [Buz07 pp. 18–19, p. 73]. #### Generality — `c` only needs to meet every double coset (surjective `mk'' ∘ c`); `E` any continuous projector with `range E = range (evalAtReps c)`.

### [CLEANUP-7] /cleanup PhD/QMF/Weight/Pr.lean (final)
- **Status**: done (2026-08-20, inline: header de-skeletonised, deprecated lemmas renamed, linter zero) | **Depends on**: T014 | **Type**: cleanup.

### [CLEANUP-8] /cleanup the T001 files (ForMathlib MvPowerSeries/Inverse.lean, TateFredholm/WeightGenFun.lean, TateFredholm/BaseChange.lean, JacobsSlash/3_BaseChange.lean)
- **Status**: done (2026-08-20, forms-riesz beastmode) |
- **Progress**: DONE — three files were already clean; `BaseChange.lean`'s four pre-existing findings fixed:
  `omit` for the four section instances of `norm_le_pow_of_equiv`, and `@[nolint unusedArguments]` (with a
  docstring sentence each) for the deliberately source-faithful binders `π`, `he'`, `[IsTate S]` — these are
  [JN] Prop 2.1.8 / Lemma 2.1.6 hypotheses ("bicontinuous", "equivalent Tate norms") that this direction of
  the proof happens not to consume; deleting them would drift from the source.  Linter zero. **Depends on**: T001 | **Type**: cleanup.

### [CLEANUP-FINAL] /cleanup-all on the whole board surface + README/PROGRESS/memory
- **Status**: done (2026-08-20, forms-riesz beastmode) |
- **Progress**: DONE — final build green (10_Eigenforms, 9_EigenvaluesU3, 7_DiamondHecke, 4_DiamondW,
  Weight.{Pr,BaseChange,Quaternionic,Algebraic}, Slash.Quaternionic, FiniteDimensional); sorry census 0
  (doc mentions only); axioms standard on every endpoint; whole-surface `runLinter` zero on the board
  surface (remaining findings only in the TateFredholm core and unrelated ForMathlib/FLT files, listed in
  README §4/§5.5); dead-code sweep recorded; README status/§1/§3/§4/§5 rewritten; PROGRESS.md rows
  (5_KappaWeight, 8_HeckeSlopes, new 10_Eigenforms) + new "culmination, for forms" section; memory
  `parallel-ticket-boards` (COMPLETE), `analyticweight-headline`, MEMORY.md. | **Depends on**: every other ticket | **Type**: cleanup-all.  README §1 (BaseChange.lean, Pr.lean, 10_Eigenforms), §3 (base change, Pr, Riesz on Forms), §4 sweep, §5 (5.6 extended: Riesz on Forms; 5.4 Fujisaki model; new 5.x for T009 if deferred); PROGRESS.md (10_Eigenforms row; crux for forms); memory.
