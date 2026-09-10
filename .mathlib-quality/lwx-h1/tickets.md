# Ticket Board — `lwx-h1` (hypothesis H1: the Atkin–Lehner symmetry at the classical points)

**BOARD PATH: `.mathlib-quality/lwx-h1/`.**  The default `.mathlib-quality/` board belongs to
the completed NewtonPolygons project — NEVER touch it; `.mathlib-quality/qmf/` and its
`beastmode_active` sentinel belong to a parallel run — NEVER touch them either.  Every
`/beastmode` run must name this board path explicitly, and delete only
`.mathlib-quality/lwx-h1/beastmode_active` (cat before rm).

**Files owned by this board**: `PhD/LWX/SymPow.lean` (Part S), `PhD/LWX/NebChar.lean` (Part N),
`PhD/LWX/AtkinLehnerLocal.lean` (Part L), `PhD/LWX/AtkinLehnerMap.lean` (Part W),
`PhD/LWX/AtkinLehnerIdentity.lean` (Part I) — all new, skeletoned and building.  Do not edit any
other file (a cleanup may relocate `cSpace_ext_blockProj` to `PhD/TateFredholm/BlockOp.lean`
and `coeff_mul_eq_zero_of_lt`/`coeff_pow_eq_zero_of_lt` next to the other `PowerSeries`
helpers; name the relocation in the cleanup ticket's progress notes).

**Build**: `lake build PhD.LWX.SymPow PhD.LWX.NebChar PhD.LWX.AtkinLehnerLocal
PhD.LWX.AtkinLehnerMap PhD.LWX.AtkinLehnerIdentity`; full `lake build PhD` is green with sorry
warnings only.  Statements are transcribed verbatim from the compiling skeleton and are
**protected** — if a statement is wrong, append to this board's `b2_log.jsonl` rather than
editing it.  `_hx`-slack convention applies to a hypothesis that turns out unneeded (known slack:
`symAct_mul.hf`, `atkinLehnerHypothesis_of_conj.hS''`).  `lake exe runLinter PhD.LWX.<Module>`
is a gate for every cleanup.  `omega` not `lia`.  No `timeout` binary on this machine.  Cleanup
tickets are done inline by the main agent.  Never `rw [tsum_eq_single x (fun z hz => by …)]`
over a compound index — name the vanishing as a `have` first; `omit … in` goes before the
docstring.

**Read before working any ticket**: `plan.md`, `decomposition.md` (the per-leaf attack records
and the full derivations of W-f and I-f), and `.mathlib-quality/lwx-stepone/JL-AUDIT.md`.
Nothing here depends on Jacquet–Langlands; if a ticket seems to need it, the route has drifted —
file a B2.

**Tickets that ADD a declaration** (marked `[NEW DECL]`): the statement below is to be inserted
into the file at the place named, then proved; it is protected like every other statement.

## Summary

**2026-09-10, `/beastmode` — BOARD COMPLETE.**  All five files (`PhD/LWX/SymPow.lean`,
`NebChar.lean`, `AtkinLehnerLocal.lean`, `AtkinLehnerMap.lean`, `AtkinLehnerIdentity.lean`) are
**sorry-free**; `lake exe runLinter` reports nothing in any of them.

**Milestone I16 — `LWX.degX_succ_of_atkinLehnerData`**: [LWX, Thm 1.3]'s degree formula
`deg X_{k+1,ω} = r_ord(ω⁻¹ω₀^{2k}) + r_ord(ω·ω₀^{−2k−2})` with **no hypothesis left**, granted
the adelic data (`AtkinLehnerData`, neatness, certificates).  `#print axioms` =
`[propext, Classical.choice, Quot.sound]`, also for `atkinLehnerHypothesis_of_atkinLehnerData`,
`discHeckeCl_comp_atkinLehner`, `atkinLehnerEquiv`, `nebChar_partnerChar`, `symAct_mul`.

### B2 log (both repaired in place; see `b2_log.jsonl`)
1. `theta_mem_Iw` had silently dropped the section hypothesis `hU` (used only in the proof), so
   the elaborated statement was false; fixed with `include hU in`.
2. The Part W/I API forced `κ` and `κ'` to share `UK, ρ`; the classical-point weights at `ζ` and
   `ζ⁻¹` have different `haloRhoH`, so H1 could not be assembled.  Generalised to
   `{UK' : Subgroup Kˣ} {ρ' : ℝ} (κ' : AnalyticWeight UK' (M1Kh 1 ψ) ρ')` (implicit, strictly weaker).

### Other deviations
- `symAct`'s body sums over `(range (k+1)).attach` (the in-definition `i < k+1` obligation is
  not available in a plain `range` sum); anticipated in ticket S10.
- New helper declarations beyond the plan: `coeff_linear_eq_zero`, `coeff_linX_eq_zero`,
  `coeff_numX_eq_zero` (sub-ticket S5a).
- Slack hypotheses renamed per the `_hx` convention: `symAct_mul._hf`, `nebK_one_sub_eq_inv._hne`,
  `atkinLehnerHypothesis_of_conj._hS''`.
- `atkinLehnerFun_slash`, `atkinLehnerFunInv_slash` use `maxHeartbeats 1000000`;
  `atkinLehnerHypothesis_of_atkinLehnerData` uses `maxHeartbeats 2000000`.

### Engineering traps found
- Never `set` an abbreviation that lemma instantiations will re-introduce unfolded: `rw` then
  fails to match (fvar vs. term head symbol).  Write the full terms or `generalize` at the end.
- `congr 1` on `ψ.mapMatrix (concrete big term)` (or on `toMatrix` of big maps) can time out in
  `whnf`; state the identity for a generic matrix / as an explicit `LinearMap.ext` lemma instead.
- `simp [Matrix.mul_apply]` on a product with a *generic* matrix folds rows into `vecMul`; run
  `simp only [Matrix.mul_apply, Fin.sum_univ_two]` first.
- `(⟨x, h⟩ : ℤ_[p])` inline elaborates at the underlying subtype and loses `Norm`; use
  `let z : ℤ_[p] := ⟨x, h⟩`.

## Ticket index

| ID | Declaration | File | Type |
|---|---|---|---|
| S1 | `hsub_mul` | SymPow | proof/def |
| S2 | `hsub_linX` | SymPow | proof/def |
| S3 | `hsub_numX` | SymPow | proof/def |
| CLEANUP-S1 | `CLEANUP-S1` | SymPow | cleanup |
| S4 | `coeff_mul_eq_zero_of_lt` | SymPow | proof/def |
| S5 | `coeff_pow_eq_zero_of_lt` | SymPow | proof/def |
| S6 | `hsub_pow_of_degree_le_one` | SymPow | proof/def |
| CLEANUP-S2 | `CLEANUP-S2` | SymPow | cleanup |
| S7 | `hsub_linX_pow_mul_numX_pow` | SymPow | proof/def |
| S8 | `polySeq_apply` | SymPow | proof/def |
| S9 | `coeff_linX_pow_mul_numX_pow_eq_zero` | SymPow | proof/def |
| CLEANUP-S3 | `CLEANUP-S3` | SymPow | cleanup |
| S10 | `symAct` | SymPow | proof/def |
| S11 | `symAct_apply` | SymPow | proof/def |
| S12 | `symAct_mem_polySubmodule` | SymPow | proof/def |
| CLEANUP-S4 | `CLEANUP-S4` | SymPow | cleanup |
| S13 | `symAct_mul` | SymPow | proof/def |
| S14 | `symAct_one` | SymPow | proof/def |
| S15 | `symAct_smul_one` | SymPow | proof/def |
| CLEANUP-S5 | `CLEANUP-S5` | SymPow | cleanup |
| S16 | `kappaSlash_eq_smul_symAct_of_shape` | SymPow | proof/def |
| CLEANUP-S-FINAL | `CLEANUP-S-FINAL` | SymPow | cleanup |
| N1 | `isUnit_one_add_p_mul` | NebChar | proof/def |
| N2 | `nebChar_apply` | NebChar | proof/def |
| N3 | `classicalData_u_eq_nebChar` | NebChar | proof/def |
| CLEANUP-N1 | `CLEANUP-N1` | NebChar | cleanup |
| N4 | `autFactor_haloWeightH_classicalPoint_eq_nebCharK` | NebChar | proof/def |
| N5 | `nebChar_mul` | NebChar | proof/def |
| N6 | `nebChar_one` | NebChar | proof/def |
| CLEANUP-N2 | `CLEANUP-N2` | NebChar | cleanup |
| N7 | `nebChar_ne_zero` | NebChar | proof/def |
| N8 | `nebChar_of_norm_sub_one_le_sq` | NebChar | proof/def |
| N9 | `continuous_zeta_pow_toZMod` | NebChar | proof/def |
| CLEANUP-N3 | `CLEANUP-N3` | NebChar | cleanup |
| N10 | `oneAddPow_sub_one_intHom` | NebChar | proof/def |
| N11 | `oneUnitPart_oneAddPMul` | NebChar | proof/def |
| N12 | `nebChar_oneAddPMul` | NebChar | proof/def |
| CLEANUP-N4 | `CLEANUP-N4` | NebChar | cleanup |
| N13 | `norm_logQuot_oneAddPMul_one` | NebChar | proof/def |
| N14 | `isPrimitiveRoot_nebChar_oneAddPMul_one` | NebChar | proof/def |
| N15 | `nebChar_oneAddPMul_natCast` | NebChar | proof/def |
| CLEANUP-N5 | `CLEANUP-N5` | NebChar | cleanup |
| N16 | `sum_nebChar_oneAddPMul_mul_eq_zero` | NebChar | proof/def |
| N17 | `sum_inv_nebChar_oneAddPMul_mul_eq_zero` | NebChar | proof/def |
| N18 | `sum_inv_nebCharK_eq_zero` | NebChar | proof/def |
| CLEANUP-N6 | `CLEANUP-N6` | NebChar | cleanup |
| N19 | `nebCharK_psi_mul` | NebChar | proof/def |
| N20 | `nebCharK_psi_ne_zero` | NebChar | proof/def |
| N21 | `nebCharK_psi_of_norm_sub_one_le_sq` | NebChar | proof/def |
| CLEANUP-N7 | `CLEANUP-N7` | NebChar | cleanup |
| N22 | `partnerChar_apply` | NebChar | proof/def |
| N23 | `oneAddPow_inv_sub_one_mul` | NebChar | proof/def |
| N24 | `nebChar_eq` | NebChar | proof/def |
| CLEANUP-N8 | `CLEANUP-N8` | NebChar | cleanup |
| N25 | `nebChar_partnerChar` | NebChar | proof/def |
| N26 | `nebCharK_partnerChar` | NebChar | proof/def |
| N27 | `autFactor_haloWeightH_partner_eq_inv_nebCharK` | NebChar | proof/def |
| CLEANUP-N9 | `CLEANUP-N9` | NebChar | cleanup |
| N28 | `classicalData_partnerChar_u` | NebChar | proof/def |
| CLEANUP-N-FINAL | `CLEANUP-N-FINAL` | NebChar | cleanup |
| L1 | `det_vQ` | AtkinLehnerLocal | proof/def |
| L2 | `det_sQ` | AtkinLehnerLocal | proof/def |
| L3 | `det_wQ` | AtkinLehnerLocal | proof/def |
| CLEANUP-L1 | `CLEANUP-L1` | AtkinLehnerLocal | cleanup |
| L4 | `det_ℓQ` | AtkinLehnerLocal | proof/def |
| L5 | `wQ_mul_wQinv` | AtkinLehnerLocal | proof/def |
| L6 | `wQinv_mul_wQ` | AtkinLehnerLocal | proof/def |
| CLEANUP-L2 | `CLEANUP-L2` | AtkinLehnerLocal | cleanup |
| L7 | `ℓQ_mul_ℓQinv` | AtkinLehnerLocal | proof/def |
| L8 | `ℓQinv_mul_ℓQ` | AtkinLehnerLocal | proof/def |
| L9 | `tMat_mul_tMatInv` | AtkinLehnerLocal | proof/def |
| CLEANUP-L3 | `CLEANUP-L3` | AtkinLehnerLocal | cleanup |
| L10 | `tMatInv_mul_tMat` | AtkinLehnerLocal | proof/def |
| L11 | `sQ_mul_tMat` | AtkinLehnerLocal | proof/def |
| L12 | `tMatInv_zero_mul_sQ_neg` | AtkinLehnerLocal | proof/def |
| CLEANUP-L4 | `CLEANUP-L4` | AtkinLehnerLocal | cleanup |
| L13 | `tMatInv_zero_mul_sQ_mul_tMat_zero` | AtkinLehnerLocal | proof/def |
| L14 | `discConjMat_wQ` | AtkinLehnerLocal | proof/def |
| L15 | `wQ_mul_vQ_mul_wQinv` | AtkinLehnerLocal | proof/def |
| CLEANUP-L5 | `CLEANUP-L5` | AtkinLehnerLocal | cleanup |
| L16 | `wQ_mul_mul_wQinv` | AtkinLehnerLocal | proof/def |
| L17 | `wQinv_mul_mul_wQ` | AtkinLehnerLocal | proof/def |
| L18 | `upAdjRep_mul_vQ` | AtkinLehnerLocal | proof/def |
| CLEANUP-L6 | `CLEANUP-L6` | AtkinLehnerLocal | cleanup |
| L19 | `wQ_mul_vQ_mul_wQinv_mul_vQ` | AtkinLehnerLocal | proof/def |
| L20 | `ℓQinv_mul_wQ_mul_vQ_mul_wQinv_mul_vQ` | AtkinLehnerLocal | proof/def |
| L21 | `vQ_mem_M1` | AtkinLehnerLocal | proof/def |
| CLEANUP-L7 | `CLEANUP-L7` | AtkinLehnerLocal | cleanup |
| L22 | `norm_vQ_zero_zero` | AtkinLehnerLocal | proof/def |
| L23 | `sQ_mem_Iw` | AtkinLehnerLocal | proof/def |
| L24 | `ℓQ_mem_Iw` | AtkinLehnerLocal | proof/def |
| CLEANUP-L8 | `CLEANUP-L8` | AtkinLehnerLocal | cleanup |
| L25 | `ℓQinv_mem_Iw` | AtkinLehnerLocal | proof/def |
| L26 | `wQ_conj_mem_Iw` | AtkinLehnerLocal | proof/def |
| L27 | `Iw_one_le_M1` | AtkinLehnerLocal | proof/def |
| CLEANUP-L9 | `CLEANUP-L9` | AtkinLehnerLocal | cleanup |
| L28 | `norm_det_fin_two_le_one` | AtkinLehnerLocal | proof/def |
| L29 | `discImage_zero_of_norm_apply_zero_one_le` | AtkinLehnerLocal | proof/def |
| L30 | `discConjMat_eq_tMatInv_mul_mul_tMat` | AtkinLehnerLocal | proof/def |
| CLEANUP-L10 | `CLEANUP-L10` | AtkinLehnerLocal | cleanup |
| L31 | `discConjMat_zero_of_discImage_zero` | AtkinLehnerLocal | proof/def |
| L32 | `conj_sQ_eq_tMat_mul_discConjMat` | AtkinLehnerLocal | proof/def |
| L33 | `discImage_vQ_zero` | AtkinLehnerLocal | proof/def |
| CLEANUP-L11 | `CLEANUP-L11` | AtkinLehnerLocal | cleanup |
| L34 | `discImage_ℓQ_zero` | AtkinLehnerLocal | proof/def |
| L35 | `discImage_ℓQinv_zero` | AtkinLehnerLocal | proof/def |
| L36 | `discConj_ℓQ_zero_one_one` | AtkinLehnerLocal | proof/def |
| CLEANUP-L12 | `CLEANUP-L12` | AtkinLehnerLocal | cleanup |
| L37 | `discConj_ℓQinv_zero_one_one` | AtkinLehnerLocal | proof/def |
| L38 | `discImage_sQ_zero` | AtkinLehnerLocal | proof/def |
| L39 | `discConj_sQ_zero` | AtkinLehnerLocal | proof/def |
| CLEANUP-L13 | `CLEANUP-L13` | AtkinLehnerLocal | cleanup |
| CLEANUP-L-FINAL | `CLEANUP-L-FINAL` | AtkinLehnerLocal | cleanup |
| W1 | `pGL` | AtkinLehnerMap | proof/def |
| W2 | `coe_wGL_inv` | AtkinLehnerMap | proof/def |
| W3 | `coe_ℓGL_inv` | AtkinLehnerMap | proof/def |
| CLEANUP-W1 | `CLEANUP-W1` | AtkinLehnerMap | cleanup |
| W4 | `sGL_zero` | AtkinLehnerMap | proof/def |
| W5 | `sGL_mul` | AtkinLehnerMap | proof/def |
| W6 | `sGL_inv` | AtkinLehnerMap | proof/def |
| CLEANUP-W2 | `CLEANUP-W2` | AtkinLehnerMap | cleanup |
| W7 | `wGL_mul_vGL_mul_wGL_inv_mul_vGL` | AtkinLehnerMap | proof/def |
| W8 | `atkinLehnerK_mul_atkinLehnerKinv` | AtkinLehnerMap | proof/def |
| W9 | `atkinLehnerKinv_mul_atkinLehnerK` | AtkinLehnerMap | proof/def |
| CLEANUP-W3 | `CLEANUP-W3` | AtkinLehnerMap | cleanup |
| W10 | `theta_mem_Iw` | AtkinLehnerMap | proof/def |
| W11 | `theta_ιp_pGL` | AtkinLehnerMap | proof/def |
| W12 | `discShift_mem_U` | AtkinLehnerMap | proof/def |
| CLEANUP-W4 | `CLEANUP-W4` | AtkinLehnerMap | cleanup |
| W13 | `theta_discShift` | AtkinLehnerMap | proof/def |
| W14 | `mul_ιp_sGL_eq` | AtkinLehnerMap | proof/def |
| W15 | `norm_theta_discShift_zero_one_le` | AtkinLehnerMap | proof/def |
| CLEANUP-W5 | `CLEANUP-W5` | AtkinLehnerMap | cleanup |
| W16 | `discImage_discShift_zero` | AtkinLehnerMap | proof/def |
| W17 | `discConjMat_discShift_zero` | AtkinLehnerMap | proof/def |
| W18 | `atkinLehnerK_eq` | AtkinLehnerMap | proof/def |
| CLEANUP-W6 | `CLEANUP-W6` | AtkinLehnerMap | cleanup |
| W19 | `atkinLehnerKinv_eq` | AtkinLehnerMap | proof/def |
| W20 | `cSpace_ext_blockProj` | AtkinLehnerMap | proof/def |
| W21 | `nebK_one` | AtkinLehnerMap | proof/def |
| CLEANUP-W7 | `CLEANUP-W7` | AtkinLehnerMap | cleanup |
| W22 | `nebK_mul_nebK_eq_nebK_det` | AtkinLehnerMap | proof/def |
| W23 | `nebK_one_sub_eq_inv` | AtkinLehnerMap | proof/def |
| W24 | `locPolyForms` | AtkinLehnerMap | proof/def |
| CLEANUP-W8 | `CLEANUP-W8` | AtkinLehnerMap | cleanup |
| W25 | `discHeckeOperator_mem_classicalDiscForms` | AtkinLehnerMap | proof/def |
| W26 | `discHeckeOperatorCl` | AtkinLehnerMap | proof/def |
| W27 | `apply_mul_of_theta_eq_one` | AtkinLehnerMap | proof/def |
| CLEANUP-W9 | `CLEANUP-W9` | AtkinLehnerMap | cleanup |
| W28 | `blockProj_zero_apply_mul_mem_U` | AtkinLehnerMap | proof/def |
| W29 | `shapiro_blockProj` | AtkinLehnerMap | proof/def |
| W30 | `atkinLehnerFun_blockProj` | AtkinLehnerMap | proof/def |
| CLEANUP-W10 | `CLEANUP-W10` | AtkinLehnerMap | cleanup |
| W31 | `atkinLehnerFun_blockProj_zero` | AtkinLehnerMap | proof/def |
| W32 | `atkinLehnerFun_left_invt` | AtkinLehnerMap | proof/def |
| W33 | `atkinLehnerFun_mem_locPolyDegSubmodule` | AtkinLehnerMap | proof/def |
| CLEANUP-W11 | `CLEANUP-W11` | AtkinLehnerMap | cleanup |
| W34 | `atkinLehnerFun_slash` | AtkinLehnerMap | proof/def |
| W35 | `atkinLehnerMap` | AtkinLehnerMap | proof/def |
| W36 | `atkinLehnerFunInv_blockProj_zero` | AtkinLehnerMap | proof/def |
| CLEANUP-W12 | `CLEANUP-W12` | AtkinLehnerMap | cleanup |
| W37 | `atkinLehnerFunInv_left_invt` | AtkinLehnerMap | proof/def |
| W38 | `atkinLehnerFunInv_mem_locPolyDegSubmodule` | AtkinLehnerMap | proof/def |
| W39 | `atkinLehnerFunInv_slash` | AtkinLehnerMap | proof/def |
| CLEANUP-W13 | `CLEANUP-W13` | AtkinLehnerMap | cleanup |
| W40 | `atkinLehnerMapInv` | AtkinLehnerMap | proof/def |
| W41 | `atkinLehnerMapInv_atkinLehnerMap` | AtkinLehnerMap | proof/def |
| W42 | `atkinLehnerMap_atkinLehnerMapInv` | AtkinLehnerMap | proof/def |
| CLEANUP-W14 | `CLEANUP-W14` | AtkinLehnerMap | cleanup |
| W43 | `discEvalAtReps_mem_locPolyDegSubmoduleBlock` | AtkinLehnerMap | proof/def |
| W44 | `discEvalAtRepsCl` | AtkinLehnerMap | proof/def |
| W45 | `discEvalAtRepsCl_apply` | AtkinLehnerMap | proof/def |
| CLEANUP-W15 | `CLEANUP-W15` | AtkinLehnerMap | cleanup |
| CLEANUP-W-FINAL | `CLEANUP-W-FINAL` | AtkinLehnerMap | cleanup |
| I1 | `vRepD_mem_levelM1` | AtkinLehnerIdentity | proof/def |
| I2 | `upEltD_mem_levelM1` | AtkinLehnerIdentity | proof/def |
| I3 | `discHeckeOperator_apply_eq_sum` | AtkinLehnerIdentity | proof/def |
| CLEANUP-I1 | `CLEANUP-I1` | AtkinLehnerIdentity | cleanup |
| I4 | `blockProj_zero_discSlash_of_shape` | AtkinLehnerIdentity | proof/def |
| I5 | `apply_mul_ιp_pGL` | AtkinLehnerIdentity | proof/def |
| I6 | `apply_mul_ιp_pGL_inv` | AtkinLehnerIdentity | proof/def |
| CLEANUP-I2 | `CLEANUP-I2` | AtkinLehnerIdentity | cleanup |
| I7 | `blockProj_zero_apply_mul_ιp` | AtkinLehnerIdentity | proof/def |
| I8 | `term_elt_eq` | AtkinLehnerIdentity | proof/def |
| I9 | `blockProj_zero_apply_term_elt` | AtkinLehnerIdentity | proof/def |
| CLEANUP-I3 | `CLEANUP-I3` | AtkinLehnerIdentity | cleanup |
| I10 | `atkinLehner_term_eq` | AtkinLehnerIdentity | proof/def |
| I11 | `blockProj_zero_discHecke_atkinLehner` | AtkinLehnerIdentity | proof/def |
| I12 | `discHeckeCl_comp_atkinLehner` | AtkinLehnerIdentity | proof/def |
| CLEANUP-I4 | `CLEANUP-I4` | AtkinLehnerIdentity | cleanup |
| I13 | `discEvalAtRepsCl_discHeckeOperatorCl` | AtkinLehnerIdentity | proof/def |
| I14 | `atkinLehnerHypothesis_of_conj` | AtkinLehnerIdentity | proof/def |
| I15 | `atkinLehnerHypothesis_of_atkinLehnerData` | AtkinLehnerIdentity | proof/def |
| CLEANUP-I5 | `CLEANUP-I5` | AtkinLehnerIdentity | cleanup |
| CLEANUP-ALL-1 | `CLEANUP-ALL-1` | AtkinLehnerIdentity | cleanup |
| I16 | `degX_succ_of_atkinLehnerData` | AtkinLehnerIdentity | milestone |
| CLEANUP-I-FINAL | `CLEANUP-I-FINAL` | AtkinLehnerIdentity | cleanup |
| CLEANUP-FINAL | `CLEANUP-FINAL` | AtkinLehnerIdentity | cleanup |


**Counts**: 144 proof/definition tickets, 54 cleanup tickets, total 198.


## Part S — `PhD/LWX/SymPow.lean`: the `Sym^k` action

### [S1] `hsub_mul`
- **Status**: done
- **File**: PhD/LWX/SymPow.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The substitution is multiplicative on products of polynomials of the declared degrees
(the Cauchy product of the coefficients matches the exponent bookkeeping). -/
theorem hsub_mul (k₁ k₂ : ℕ) {P Q : PowerSeries K}
    (hP : ∀ i, k₁ < i → PowerSeries.coeff i P = 0) (hQ : ∀ i, k₂ < i → PowerSeries.coeff i Q = 0)
    (N L : PowerSeries K) :
    hsub (k₁ + k₂) (P * Q) N L = hsub k₁ P N L * hsub k₂ Q N L := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. Unfold `hsub` on both sides; RHS is `(∑_{i≤k₁} C(P_i) L^{k₁-i} N^i) * (∑_{j≤k₂} C(Q_j) L^{k₂-j} N^j)`; expand with `Finset.sum_mul_sum` into a double sum over `range (k₁+1) ×ˢ range (k₂+1)`.
2. LHS: `coeff m (P*Q) = ∑_{(i,j) ∈ antidiagonal m} P_i Q_j` (`PowerSeries.coeff_mul`); push `C` through (`map_sum`, `map_mul`) and `Finset.sum_mul`, giving a sum over `m ≤ k₁+k₂` and `(i,j)` with `i+j = m`.
3. Rewrite the LHS double sum as a sum over pairs `(i,j)` with `i + j ≤ k₁ + k₂` (`Finset.sum_sigma'` / `Finset.Nat.antidiagonal` reindexing, or `Finset.sum_comm'`), then drop the pairs with `i > k₁` or `j > k₂` using `hP`/`hQ` (`Finset.sum_subset`, terms vanish by `map_zero`/`zero_mul`).
4. For the surviving pairs `i ≤ k₁`, `j ≤ k₂`: `L^{(k₁+k₂)-(i+j)} N^{i+j} = (L^{k₁-i} N^i)(L^{k₂-j} N^j)` by `pow_add` and `omega` on the exponents (`k₁+k₂-(i+j) = (k₁-i)+(k₂-j)`); `ring`.

- **Mathlib/project lemmas needed**: `PowerSeries.coeff_mul`, `Finset.sum_mul_sum`, `Finset.sum_product'`, `Finset.sum_sigma'`, `Finset.Nat.antidiagonal_eq_map`/`Finset.Nat.mem_antidiagonal`, `Finset.sum_subset`, `Finset.sum_comm`, `pow_add`, `map_sum`, `map_mul`, `omega`.
- **Sources**: Pure algebra; the binary-form model of `Sym^k` (`decomposition.md` S-a).
- **Generality decision**: General `K` (any commutative ring would do; keep the file's `K` to avoid a second variable block).
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/SymPow.lean` clean.

### [S2] `hsub_linX`
- **Status**: done
- **File**: PhD/LWX/SymPow.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The substitution of the linear factor `cz + d` is `c·N + d·L`. -/
theorem hsub_linX (γ : Matrix (Fin 2) (Fin 2) K) (N L : PowerSeries K) :
    hsub 1 (linX γ) N L = PowerSeries.C (γ 1 0) * N + PowerSeries.C (γ 1 1) * L := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `unfold hsub`; `Finset.sum_range_succ`, `Finset.sum_range_zero`, `Nat.sub_zero`, `pow_one`, `pow_zero`.
2. `coeff 0 (linX γ) = γ 1 1` and `coeff 1 (linX γ) = γ 1 0`: `linX γ = C (γ 1 1) + C (γ 1 0) * X` (`QMF/Weight/Series.lean:167`); `PowerSeries.coeff_C`, `PowerSeries.coeff_C_mul`, `PowerSeries.coeff_X`, `map_add`, `if_pos`/`if_neg`.
3. `ring`.

- **Mathlib/project lemmas needed**: `linX` (Series.lean:167), `PowerSeries.coeff_C`, `PowerSeries.coeff_C_mul`, `PowerSeries.coeff_X`, `Finset.sum_range_succ`.
- **Sources**: `decomposition.md` S-a.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/SymPow.lean` clean.

### [S3] `hsub_numX`
- **Status**: done
- **File**: PhD/LWX/SymPow.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The substitution of the numerator `az + b` is `a·N + b·L`. -/
theorem hsub_numX (γ : Matrix (Fin 2) (Fin 2) K) (N L : PowerSeries K) :
    hsub 1 (numX γ) N L = PowerSeries.C (γ 0 0) * N + PowerSeries.C (γ 0 1) * L := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Identical to `hsub_linX` with `numX γ = C (γ 0 1) + C (γ 0 0) * X` (Series.lean:171).

- **Mathlib/project lemmas needed**: `numX`, `PowerSeries.coeff_C`, `PowerSeries.coeff_C_mul`, `PowerSeries.coeff_X`.
- **Sources**: `decomposition.md` S-a.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/SymPow.lean` clean.

### [CLEANUP-S1] Cleanup `PhD/LWX/SymPow.lean`
- **Status**: done
- **File**: PhD/LWX/SymPow.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.SymPow` and `lake exe runLinter PhD.LWX.SymPow` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: no linter warnings, no unused simp args, build clean.

### [S4] `coeff_mul_eq_zero_of_lt` [NEW DECL]
- **Status**: done
- **File**: insert after `hsub_numX` in `PhD/LWX/SymPow.lean`
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem coeff_mul_eq_zero_of_lt {k₁ k₂ : ℕ} {P Q : PowerSeries K}
    (hP : ∀ i, k₁ < i → PowerSeries.coeff i P = 0) (hQ : ∀ j, k₂ < j → PowerSeries.coeff j Q = 0)
    {m : ℕ} (hm : k₁ + k₂ < m) : PowerSeries.coeff m (P * Q) = 0 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
New helper (add before `hsub_pow_of_degree_le_one`): `theorem coeff_mul_eq_zero_of_lt {k₁ k₂ : ℕ} {P Q : PowerSeries K} (hP : ∀ i, k₁ < i → coeff i P = 0) (hQ : ∀ j, k₂ < j → coeff j Q = 0) {m : ℕ} (hm : k₁ + k₂ < m) : coeff m (P * Q) = 0`.
1. `PowerSeries.coeff_mul`; `Finset.sum_eq_zero`; for `(i,j) ∈ antidiagonal m`, `i + j = m > k₁ + k₂` so `k₁ < i ∨ k₂ < j` (`omega`); `hP`/`hQ`, `zero_mul`/`mul_zero`.

- **Mathlib/project lemmas needed**: `PowerSeries.coeff_mul`, `Finset.Nat.mem_antidiagonal`, `Finset.sum_eq_zero`, `omega`.
- **Sources**: `decomposition.md` S-a (attack 1).
- **Generality decision**: General `K`.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/SymPow.lean` clean.

### [S5] `coeff_pow_eq_zero_of_lt` [NEW DECL]
- **Status**: done
- **File**: insert after `coeff_mul_eq_zero_of_lt` in `PhD/LWX/SymPow.lean`
- **Depends on**: S4
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem coeff_pow_eq_zero_of_lt {k : ℕ} {P : PowerSeries K}
    (hP : ∀ i, k < i → PowerSeries.coeff i P = 0) (n : ℕ) {m : ℕ} (hm : n * k < m) :
    PowerSeries.coeff m (P ^ n) = 0 := by
  sorry
```

- **Depends on (declarations)**: `coeff_mul_eq_zero_of_lt`

**Proof sketch**:
New helper: `theorem coeff_pow_eq_zero_of_lt {k : ℕ} {P : PowerSeries K} (hP : ∀ i, k < i → coeff i P = 0) (n : ℕ) {m : ℕ} (hm : n * k < m) : coeff m (P ^ n) = 0`.
Induction on `n`: `n = 0`: `pow_zero`, `PowerSeries.coeff_one`, `m ≠ 0`; step: `pow_succ`, `coeff_mul_eq_zero_of_lt` with `k₁ = n*k`, `k₂ = k` (`Nat.succ_mul`, `omega`).

- **Mathlib/project lemmas needed**: `coeff_mul_eq_zero_of_lt`, `pow_succ`, `PowerSeries.coeff_one`.
- **Sources**: `decomposition.md` S-a.
- **Generality decision**: General `K`.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/SymPow.lean` clean.

### [S5a] `coeff_linear_eq_zero`, `coeff_linX_eq_zero`, `coeff_numX_eq_zero` [SUB-TICKET]
- **Status**: done
- **File**: PhD/LWX/SymPow.lean (after `coeff_pow_eq_zero_of_lt`)
- **Parent**: S6
- **Depends on**: none
- **Type**: proof

**Statement**:
```lean
theorem coeff_linear_eq_zero {a b : K} {m : ℕ} (hm : 1 < m) :
    PowerSeries.coeff m (PowerSeries.C a + PowerSeries.C b * PowerSeries.X) = 0
theorem coeff_linX_eq_zero (γ : Matrix (Fin 2) (Fin 2) K) {m : ℕ} (hm : 1 < m) :
    PowerSeries.coeff m (linX γ) = 0
theorem coeff_numX_eq_zero (γ : Matrix (Fin 2) (Fin 2) K) {m : ℕ} (hm : 1 < m) :
    PowerSeries.coeff m (numX γ) = 0
```
**Proof sketch**: `map_add`, `coeff_C`, `coeff_C_mul`, `coeff_X`, two `if_neg`; the `linX`/`numX` forms unfold to the linear one.
- **Mathlib lemmas needed**: `PowerSeries.coeff_C`, `PowerSeries.coeff_C_mul`, `PowerSeries.coeff_X`.
- **Sources**: `decomposition.md` S-a.
- **Generality decision**: general `K`; one shared linear lemma, two specialisations.
- **Progress**: 2026-09-10: spawned from S6 (degree bound needed by S6, S7, S9); DONE.

### [S6] `hsub_pow_of_degree_le_one`
- **Status**: done
- **File**: PhD/LWX/SymPow.lean
- **Depends on**: S1, S5
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The substitution of a power of a polynomial of degree `≤ 1` is the power of the
substitution (`hsub_mul` iterated). -/
theorem hsub_pow_of_degree_le_one (n : ℕ) {P : PowerSeries K}
    (hP : ∀ i, 1 < i → PowerSeries.coeff i P = 0) (N L : PowerSeries K) :
    hsub n (P ^ n) N L = (hsub 1 P N L) ^ n := by
  sorry
```

- **Depends on (declarations)**: `hsub_mul`, `coeff_pow_eq_zero_of_lt`

**Proof sketch**:
Induction on `n`.
1. `n = 0`: `hsub 0 1 N L = C (coeff 0 1) * (L^0 * N^0) = 1` (`Finset.sum_range_one`, `PowerSeries.coeff_one`/`coeff_zero_eq_constantCoeff`, `map_one`).
2. Step: `P^(n+1) = P^n * P` (`pow_succ`); `hsub (n + 1) (P^n * P) = hsub n (P^n) * hsub 1 P` by `hsub_mul n 1` with `hP' := coeff_pow_eq_zero_of_lt hP n` (note `n * 1 = n`, `mul_one`) and `hP`; then `ih`, `pow_succ`.

- **Mathlib/project lemmas needed**: `hsub_mul`, `coeff_pow_eq_zero_of_lt`, `pow_succ`, `Finset.sum_range_one`, `PowerSeries.coeff_one`.
- **Sources**: `decomposition.md` S-a.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE. Spawned sub-ticket S5a (`coeff_linear_eq_zero`, `coeff_linX_eq_zero`, `coeff_numX_eq_zero`) for the degree-≤1 bound used by S6, S7, S9.

### [CLEANUP-S2] Cleanup `PhD/LWX/SymPow.lean`
- **Status**: done
- **File**: PhD/LWX/SymPow.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.SymPow` and `lake exe runLinter PhD.LWX.SymPow` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: no linter warnings, no unused simp args, build clean.

### [S7] `hsub_linX_pow_mul_numX_pow`
- **Status**: done
- **File**: PhD/LWX/SymPow.lean
- **Depends on**: S1, S6, S2, S3, S5
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The cocycle**: substituting `(numX γ', linX γ')` into the `i`-th column polynomial of `γ`
gives the `i`-th column polynomial of `γ * γ'`. -/
theorem hsub_linX_pow_mul_numX_pow (k i : ℕ) (hi : i ≤ k) (γ γ' : Matrix (Fin 2) (Fin 2) K) :
    hsub k (linX γ ^ (k - i) * numX γ ^ i) (numX γ') (linX γ')
      = linX (γ * γ') ^ (k - i) * numX (γ * γ') ^ i := by
  sorry
```

- **Depends on (declarations)**: `hsub_mul`, `hsub_pow_of_degree_le_one`, `hsub_linX`, `hsub_numX`, `coeff_pow_eq_zero_of_lt`

**Proof sketch**:
1. `hsub k (linX γ ^ (k-i) * numX γ ^ i) N' L'` with `N' = numX γ'`, `L' = linX γ'`: write `k = (k - i) + i` (`Nat.sub_add_cancel hi`, rewrite only the first `k` — use `obtain ⟨j, rfl⟩ : ∃ j, k = j + i` from `hi` to avoid motive issues, then `Nat.add_sub_cancel`), apply `hsub_mul (k-i) i` with the degree bounds `coeff_pow_eq_zero_of_lt` (degree of `linX`, `numX` is `≤ 1`: `coeff j (C d + C c * X) = 0` for `j > 1`).
2. `hsub_pow_of_degree_le_one` twice, then `hsub_linX`, `hsub_numX`: the factors are `(C (γ 1 0) * numX γ' + C (γ 1 1) * linX γ')^(k-i)` and `(C (γ 0 0) * numX γ' + C (γ 0 1) * linX γ')^i`.
3. `C (γ 1 0) * numX γ' + C (γ 1 1) * linX γ' = linX (γ * γ')`: unfold `linX`, `numX`, `Matrix.mul_apply`, `Fin.sum_univ_two`, `map_add`, `map_mul`; `ring`.  Same for `numX (γ * γ')`.  (`γ * γ'` — the second substitution acts first; see `decomposition.md` S-b attack 1.)

- **Mathlib/project lemmas needed**: `hsub_mul`, `hsub_pow_of_degree_le_one`, `hsub_linX`, `hsub_numX`, `coeff_pow_eq_zero_of_lt`, `Matrix.mul_apply`, `Fin.sum_univ_two`, `Nat.sub_add_cancel`.
- **Sources**: [LWX] (2.3.2), `lwx.txt:600–604`; right action `lwx.txt:560–562`; `decomposition.md` S-b.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — `hl`/`hn` are `(WeightSeries.linX_mul γ' γ).symm` / `(WeightSeries.numX_mul γ' γ).symm` (existing QMF lemmas, found at cleanup).

### [S8] `polySeq_apply`
- **Status**: done
- **File**: PhD/LWX/SymPow.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem polySeq_apply (k : ℕ) (P : PowerSeries K) (hP : ∀ i, k < i → PowerSeries.coeff i P = 0)
    (j : ℕ) : polySeq k P hP j = PowerSeries.coeff j P := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rfl` after `unfold polySeq` — `cSpace.ofTendsto_apply` (`BlockOp.lean:73`) is `rfl`.

- **Mathlib/project lemmas needed**: `cSpace.ofTendsto_apply`.
- **Sources**: `decomposition.md` S-c.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/SymPow.lean` clean.

### [S9] `coeff_linX_pow_mul_numX_pow_eq_zero`
- **Status**: done
- **File**: PhD/LWX/SymPow.lean
- **Depends on**: S4, S5
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The `i`-th column polynomial `(cz+d)^{k−i}(az+b)^i` has degree `≤ k`. -/
theorem coeff_linX_pow_mul_numX_pow_eq_zero (k i : ℕ) (hi : i ≤ k)
    (γ : Matrix (Fin 2) (Fin 2) K) {j : ℕ} (hj : k < j) :
    PowerSeries.coeff j (linX γ ^ (k - i) * numX γ ^ i) = 0 := by
  sorry
```

- **Depends on (declarations)**: `coeff_mul_eq_zero_of_lt`, `coeff_pow_eq_zero_of_lt`

**Proof sketch**:
`coeff_mul_eq_zero_of_lt` with `k₁ = (k - i) * 1`, `k₂ = i * 1` (from `coeff_pow_eq_zero_of_lt` applied to `linX γ`, `numX γ`, whose coefficients vanish above `1`: `linX = C d + C c * X`, `PowerSeries.coeff_C`, `coeff_C_mul`, `coeff_X`), and `(k - i) + i = k < j` (`Nat.sub_add_cancel hi`, `omega`).

- **Mathlib/project lemmas needed**: `coeff_mul_eq_zero_of_lt`, `coeff_pow_eq_zero_of_lt`, `PowerSeries.coeff_C`, `PowerSeries.coeff_C_mul`, `PowerSeries.coeff_X`.
- **Sources**: `decomposition.md` S-c.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/SymPow.lean` clean.

### [CLEANUP-S3] Cleanup `PhD/LWX/SymPow.lean`
- **Status**: done
- **File**: PhD/LWX/SymPow.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.SymPow` and `lake exe runLinter PhD.LWX.SymPow` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: no linter warnings, no unused simp args, build clean.

### [S10] `symAct`
- **Status**: done
- **File**: PhD/LWX/SymPow.lean
- **Depends on**: S9
- **Parallel**: yes (within the dependency order)
- **Type**: definition

**Statement** (verbatim from the skeleton; protected):
```lean
variable (K) in
/-- **The `Sym^k` action** of `γ` on coefficient sequences: `z^i ↦ (cz+d)^{k−i}(az+b)^i` for
`i ≤ k`, and `z^i ↦ 0` for `i > k`.  A finite-rank continuous linear map. -/
def symAct (k : ℕ) (γ : Matrix (Fin 2) (Fin 2) K) : c(ℕ, K) →L[K] c(ℕ, K) :=
  ∑ i ∈ Finset.range (k + 1), (cSpace.evalCLM i).smulRight
    (polySeq k (linX γ ^ (k - i) * numX γ ^ i) fun _ hj =>
      coeff_linX_pow_mul_numX_pow_eq_zero k i (Nat.lt_succ_iff.mp (by
        sorry)) γ hj)
```

- **Depends on (declarations)**: `coeff_linX_pow_mul_numX_pow_eq_zero`

**Proof sketch**:
The single `sorry` is the obligation `i < k + 1` for `i ∈ Finset.range (k + 1)`: replace `by sorry` by `Finset.mem_range.mp ‹_›` (name the membership hypothesis in the lambda: `fun i hi => …` — the binder is currently `fun _ hj`; adjust to bind the `Finset.mem_range` witness from `Finset.sum`'s attach or use `Finset.sum_attach`/`∑ i ∈ (range (k+1)).attach`).  Simplest: define the summand for all `i : ℕ` with `polySeq k _ (fun j hj => coeff_linX_pow_mul_numX_pow_eq_zero' …)` where the bound `i ≤ k` is not needed — **alternative**: generalise `coeff_linX_pow_mul_numX_pow_eq_zero` to drop `hi` by using `min i k`… Preferred: keep `hi` and sum over `(Finset.range (k+1)).attach`, then `Finset.sum_attach` in `symAct_apply`.

- **Mathlib/project lemmas needed**: `Finset.mem_range`, `Finset.sum_attach`, `ContinuousLinearMap.smulRight`, `cSpace.evalCLM`.
- **Sources**: `decomposition.md` S-c.
- **Generality decision**: As stated; the definition may change its internal sum to `attach` (statement of `symAct_apply` unchanged).
- **Progress**: 2026-09-10: DONE — the in-definition `sorry` (`i < k+1` for the bound variable) was undischargeable as a plain `range` sum; body changed to sum over `(range (k+1)).attach` as the ticket sketch anticipated (type unchanged); `symAct_apply` uses `Finset.sum_attach`.

### [S11] `symAct_apply`
- **Status**: done
- **File**: PhD/LWX/SymPow.lean
- **Depends on**: S10, S8
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem symAct_apply (k : ℕ) (γ : Matrix (Fin 2) (Fin 2) K) (f : c(ℕ, K)) (j : ℕ) :
    symAct K k γ f j
      = ∑ i ∈ Finset.range (k + 1), f i * PowerSeries.coeff j (linX γ ^ (k - i) * numX γ ^ i) := by
  sorry
```

- **Depends on (declarations)**: `symAct`, `polySeq_apply`

**Proof sketch**:
`unfold symAct`; `ContinuousLinearMap.sum_apply` (or `ContinuousLinearMap.coe_sum'`, `Finset.sum_apply`), `cSpace.sum_apply` (used in DiscForms.lean), `ContinuousLinearMap.smulRight_apply`, `cSpace.evalCLM_apply`, `cSpace.smul_apply`/`Pi.smul_apply`, `smul_eq_mul`, `polySeq_apply`; if `symAct` sums over `attach`, finish with `Finset.sum_attach`.

- **Mathlib/project lemmas needed**: `ContinuousLinearMap.sum_apply`, `ContinuousLinearMap.smulRight_apply`, `cSpace.evalCLM_apply` (ModelSpace.lean:74), `cSpace.sum_apply`, `polySeq_apply`.
- **Sources**: `decomposition.md` S-c.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/SymPow.lean` clean.

### [S12] `symAct_mem_polySubmodule`
- **Status**: done
- **File**: PhD/LWX/SymPow.lean
- **Depends on**: S11, S9
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The action lands in polynomials of degree `≤ k`. -/
theorem symAct_mem_polySubmodule (k : ℕ) (γ : Matrix (Fin 2) (Fin 2) K) (f : c(ℕ, K)) :
    symAct K k γ f ∈ polySubmodule K k := by
  sorry
```

- **Depends on (declarations)**: `symAct_apply`, `coeff_linX_pow_mul_numX_pow_eq_zero`

**Proof sketch**:
`intro j hj`; `symAct_apply`; `Finset.sum_eq_zero fun i hi => by rw [coeff_linX_pow_mul_numX_pow_eq_zero k i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) γ hj, mul_zero]` (`polySubmodule` carrier: `∀ m, n < m → f m = 0`, Algebraic.lean:258).

- **Mathlib/project lemmas needed**: `symAct_apply`, `coeff_linX_pow_mul_numX_pow_eq_zero`, `Finset.sum_eq_zero`, `polySubmodule`.
- **Sources**: `decomposition.md` S-c.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/SymPow.lean` clean.

### [CLEANUP-S4] Cleanup `PhD/LWX/SymPow.lean`
- **Status**: done
- **File**: PhD/LWX/SymPow.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.SymPow` and `lake exe runLinter PhD.LWX.SymPow` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: no linter warnings, no unused simp args, build clean.

### [S13] `symAct_mul`
- **Status**: done
- **File**: PhD/LWX/SymPow.lean
- **Depends on**: S11, S7
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The right-action law** on polynomials: `(f ∣ γ) ∣ γ' = f ∣ (γ γ')` (`hsub_linX_pow_mul_numX_pow`). -/
theorem symAct_mul (k : ℕ) (γ γ' : Matrix (Fin 2) (Fin 2) K) {f : c(ℕ, K)}
    (hf : f ∈ polySubmodule K k) :
    symAct K k γ' (symAct K k γ f) = symAct K k (γ * γ') f := by
  sorry
```

- **Depends on (declarations)**: `symAct_apply`, `hsub_linX_pow_mul_numX_pow`

**Proof sketch**:
1. `ext j` (`DFunLike.ext`), `symAct_apply` three times: LHS `= ∑_{i'≤k} (∑_{i≤k} f i * coeff i' (col_i γ)) * coeff j (col_{i'} γ')`, RHS `= ∑_{i≤k} f i * coeff j (col_i (γγ'))` where `col_i γ := linX γ^(k-i) * numX γ^i`.
2. `col_i (γ γ') = hsub k (col_i γ) (numX γ') (linX γ')` (`hsub_linX_pow_mul_numX_pow k i hi`, reversed) `= ∑_{i'≤k} C (coeff i' (col_i γ)) * col_{i'} γ'` (`hsub` unfolded); take `coeff j`: `map_sum`, `PowerSeries.coeff_C_mul`.
3. `Finset.sum_comm`, `Finset.mul_sum`, `Finset.sum_mul`, `mul_assoc`; `Finset.sum_congr`.
`hf` is not used (both sides only see `f i` for `i ≤ k`) — keep the binder (`_hx` convention), note at cleanup.

- **Mathlib/project lemmas needed**: `symAct_apply`, `hsub_linX_pow_mul_numX_pow`, `PowerSeries.coeff_C_mul`, `map_sum`, `Finset.sum_comm`, `Finset.mul_sum`, `Finset.sum_mul`.
- **Sources**: [LWX] right action, `lwx.txt:560–562`; `decomposition.md` S-d.
- **Generality decision**: As stated (`hf` slack).
- **Progress**: 2026-09-10: DONE — `hf` unused (anticipated slack), binder renamed `_hf` per the `_hx` convention.

### [S14] `symAct_one`
- **Status**: done
- **File**: PhD/LWX/SymPow.lean
- **Depends on**: S11
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The identity acts trivially on polynomials. -/
theorem symAct_one (k : ℕ) {f : c(ℕ, K)} (hf : f ∈ polySubmodule K k) :
    symAct K k 1 f = f := by
  sorry
```

- **Depends on (declarations)**: `symAct_apply`

**Proof sketch**:
1. `ext j`; `symAct_apply`; `linX 1 = 1`, `numX 1 = X` (`Matrix.one_apply`, `linX`, `numX`, `map_zero`, `map_one`, `zero_mul`, `add_zero`, `zero_add`, `one_mul`); `one_pow`, `one_mul`; `PowerSeries.coeff_X_pow : coeff j (X^i) = if j = i then 1 else 0`.
2. `Finset.sum_ite_eq'`/`Finset.sum_ite_eq` collapses to `if j ∈ range (k+1) then f j * 1 else 0`; for `j ≤ k` this is `f j`; for `j > k` it is `0 = f j` by `hf j hj`.

- **Mathlib/project lemmas needed**: `symAct_apply`, `PowerSeries.coeff_X_pow`, `Finset.sum_ite_eq'`, `Matrix.one_apply`, `polySubmodule`.
- **Sources**: `decomposition.md` S-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/SymPow.lean` clean.

### [S15] `symAct_smul_one`
- **Status**: done
- **File**: PhD/LWX/SymPow.lean
- **Depends on**: S11
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- A scalar matrix acts by its `k`-th power. -/
theorem symAct_smul_one (k : ℕ) (x : K) {f : c(ℕ, K)} (hf : f ∈ polySubmodule K k) :
    symAct K k (x • (1 : Matrix (Fin 2) (Fin 2) K)) f = x ^ k • f := by
  sorry
```

- **Depends on (declarations)**: `symAct_apply`

**Proof sketch**:
1. `ext j`; `symAct_apply`; `(x • 1) 1 0 = 0`, `(x • 1) 1 1 = x`, `(x • 1) 0 0 = x`, `(x • 1) 0 1 = 0` (`Matrix.smul_apply`, `Matrix.one_apply`, `smul_eq_mul`); so `linX (x•1) = C x`, `numX (x•1) = C x * X`.
2. `col_i = C x ^ (k-i) * (C x * X)^i = C (x^k) * X^i` (`mul_pow`, `← map_pow`, `← pow_add`, `Nat.sub_add_cancel hi`, `mul_assoc`); `PowerSeries.coeff_C_mul`, `PowerSeries.coeff_X_pow`; the sum collapses as in `symAct_one` to `x^k * f j` for `j ≤ k` and to `0 = x^k * f j` for `j > k` (`hf`); RHS `(x^k • f) j = x^k * f j` (`cSpace.smul_apply`).

- **Mathlib/project lemmas needed**: `symAct_apply`, `Matrix.smul_apply`, `Matrix.one_apply`, `PowerSeries.coeff_C_mul`, `PowerSeries.coeff_X_pow`, `Finset.sum_ite_eq'`, `mul_pow`, `map_pow`.
- **Sources**: `decomposition.md` S-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/SymPow.lean` clean.

### [CLEANUP-S5] Cleanup `PhD/LWX/SymPow.lean`
- **Status**: done
- **File**: PhD/LWX/SymPow.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.SymPow` and `lake exe runLinter PhD.LWX.SymPow` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: no linter warnings, no unused simp args, build clean.

### [S16] `kappaSlash_eq_smul_symAct_of_shape`
- **Status**: done
- **File**: PhD/LWX/SymPow.lean
- **Depends on**: S11
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **At a classical-shape matrix, `kappaSlash` is the constant times `symAct`**
(`kappaSlash_apply` and `autFactor_mul_mobius_pow_of_shape`, column by column). -/
theorem kappaSlash_eq_smul_symAct_of_shape {S : Submonoid (Matrix (Fin 2) (Fin 2) K)}
    (κ : AnalyticWeight UK S ρ) (g : S) {k : ℕ} {u : K}
    (hA : κ.toWeightSeries.autFactor g.1 * linX g.1 = PowerSeries.C u * linX g.1 ^ (k + 1))
    {f : c(ℕ, K)} (hf : f ∈ polySubmodule K k) :
    κ.kappaSlash g f = u • symAct K k g.1 f := by
  sorry
```

- **Depends on (declarations)**: `symAct_apply`

**Proof sketch**:
1. `ext j`; `AnalyticWeight.kappaSlash_def` (Char.lean:813) then `kappaSlash_apply` (SlashAction.lean:462): `(κ.kappaSlash g f) j = ∑' i, coeff j (autFactor g.1 * mobius g.1 ^ i) * f i`.
2. `have hd : g.1 1 1 ≠ 0 := κ.toWeightSeries.bounds.d_ne_zero g.2` (as in `kappaSlash_apply`'s own proof).
3. State the vanishing as a named `have hvan : ∀ i ∉ Finset.range (k+1), coeff j (…) * f i = 0` (from `hf i` for `i > k`: `mul_zero`) **before** `rw [tsum_eq_sum hvan]` (the `tsum_eq_single`-style inline-`by` trap of `lean-project-workflow.md`).
4. For `i ≤ k`: `autFactor_mul_mobius_pow_of_shape κ hd hA (Nat.lt_succ_iff.mp hi)` (Touching.lean:181; read its exact RHS at ticket time — it is `C u * (linX^(k-i) * numX^i)` up to association); `PowerSeries.coeff_C_mul`.
5. RHS: `(u • symAct K k g.1 f) j = u * ∑ i, f i * coeff j (col_i g.1)` (`cSpace.smul_apply`, `symAct_apply`); `Finset.mul_sum`; `Finset.sum_congr rfl`; `ring`.

- **Mathlib/project lemmas needed**: `AnalyticWeight.kappaSlash_def`, `kappaSlash_apply`, `autFactor_mul_mobius_pow_of_shape`, `WeightSeries.bounds.d_ne_zero`, `tsum_eq_sum`, `PowerSeries.coeff_C_mul`, `symAct_apply`, `Finset.mul_sum`.
- **Sources**: [LWX] (2.3.2) `lwx.txt:600–604`; `decomposition.md` S-e.
- **Generality decision**: General `S`, `κ`, as stated (the same generality as `autFactor_mul_mobius_pow_of_shape`).
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/SymPow.lean` clean.

### [CLEANUP-S-FINAL] Final cleanup `PhD/LWX/SymPow.lean`
- **Status**: done
- **File**: PhD/LWX/SymPow.lean
- **Depends on**: every proof ticket of Part S
- **Parallel**: no
- **Type**: cleanup

Whole-file `/cleanup`: sorry-free check (`grep -c sorry` = 0), `#print axioms` on the file's
headline declarations (standard axioms only), `lake exe runLinter PhD.LWX.SymPow` clean, module
docstring updated to describe what is proved (drop "skeleton"/"planned" wording), relocations
named in `tickets.md` performed with one rebuild.
- **Progress**: 2026-09-10: DONE — SymPow.lean sorry-free; variable block restructured (topological instances only from `### The action` on, removing all unused-section-variable warnings); unused simp args removed; `lake build PhD.LWX.SymPow` green; `lake exe runLinter PhD.LWX.SymPow` reports nothing in SymPow.lean; module docstring updated.


## Part N — `PhD/LWX/NebChar.lean`: the nebentypus at the classical point

### [N1] `isUnit_one_add_p_mul`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `1 + p·x` is a unit of `ℤ_p`. -/
theorem isUnit_one_add_p_mul (x : ℤ_[p]) : IsUnit (1 + (p : ℤ_[p]) * x) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`PadicInt.isUnit_iff`: `‖1 + p x‖ = 1`.  `‖(p : ℤ_[p]) * x‖ ≤ ‖p‖ * ‖x‖ ≤ p⁻¹ * 1 < 1 = ‖1‖` (`norm_mul`/`PadicInt.norm_mul`, `PadicInt.norm_p`, `PadicInt.norm_le_one`), then `PadicInt.norm_add_eq_max_of_ne` (`‖1‖ ≠ ‖px‖`) and `max_eq_left`.

- **Mathlib/project lemmas needed**: `PadicInt.isUnit_iff`, `PadicInt.norm_add_eq_max_of_ne`, `PadicInt.norm_p`, `PadicInt.norm_le_one`, `PadicInt.norm_mul`.
- **Sources**: [LWX] §2.1 `lwx.txt:456–474` (classical characters, conductor); `ClassicalPoint.lean:412–466`; `decomposition.md` N-a…N-g.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [N2] `nebChar_apply`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem nebChar_apply (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (a : ℤ_[p]ˣ) :
    nebChar ψ ω k ζ a
      = HaloInt.specialize (intHom ψ) (classicalPoint p k ζ) (univChar ω a)
        * (intHom ψ (a : ℤ_[p]))⁻¹ ^ k := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`unfold nebChar nebCharK`; `haloCharFunH_psi hp2 hψ h0 h1 hT a` (HaloWeightH.lean:731) with `h0 := inv_lt_norm_classicalPoint hp2 hζ hpK k`, `h1 := norm_classicalPoint_lt_one hp2 hζ hpK k`, `hT := norm_TH_one_classicalPoint_sq_lt hp2 hζ hpK k` (the three fields of `classicalData`, ClassicalPoint.lean:453–455); `inv_pow`.

- **Mathlib/project lemmas needed**: `haloCharFunH_psi`, `inv_lt_norm_classicalPoint`, `norm_classicalPoint_lt_one`, `norm_TH_one_classicalPoint_sq_lt`.
- **Sources**: [LWX] §2.1 `lwx.txt:456–474` (classical characters, conductor); `ClassicalPoint.lean:412–466`; `decomposition.md` N-a…N-g.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [N3] `classicalData_u_eq_nebChar`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The classical datum's constants are the nebentypus at the `d`-entries of the disc conjugates
(`certConj_apply_one_one`). -/
theorem classicalData_u_eq_nebChar (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (i : ι) (t : Fin p)
    (a : ZMod (p ^ 1)) :
    (classicalData ψ ω θG U hU vRep hvΔ uu hp2 hψ hζ hpK k).u i t a
      = nebChar ψ ω k ζ (M1.toLocalMat (discConj 1 (certM1 θG U hU vRep hvΔ uu i t) a)).d := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`show haloCharFunH … (certConj … i t a 1 1) * (certConj … 1 1)⁻¹ ^ k = _` (`classicalData.u` is that by definition, ClassicalPoint.lean:461); `rw [certConj_apply_one_one]` (TargetPoint.lean:312: `certConj … 1 1 = intHom ψ (toLocalMat (discConj …)).d`); `rfl` (`nebChar a = nebCharK (intHom ψ a)`).

- **Mathlib/project lemmas needed**: `certConj_apply_one_one`, `classicalData` (ClassicalPoint.lean:450).
- **Sources**: [LWX] §2.1 `lwx.txt:456–474` (classical characters, conductor); `ClassicalPoint.lean:412–466`; `decomposition.md` N-a…N-g.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [CLEANUP-N1] Cleanup `PhD/LWX/NebChar.lean`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.NebChar` and `lake exe runLinter PhD.LWX.NebChar` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: `lake env lean PhD/LWX/NebChar.lean` has no warnings; one `omit` added (`continuous_zeta_pow_toZMod`).

### [N4] `autFactor_haloWeightH_classicalPoint_eq_nebCharK`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The shape constant of the halo weight at the classical point, at an arbitrary `g ∈ M1Kh`,
is the nebentypus at its `d`-entry: `autFactor g · L = C (nebCharK (g 1 1)) · L^{k+1}`. -/
theorem autFactor_haloWeightH_classicalPoint_eq_nebCharK (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (h0 : (p : ℝ)⁻¹ < ‖classicalPoint p k ζ‖) (h1 : ‖classicalPoint p k ζ‖ < 1)
    (hT : ‖TH p 1 (classicalPoint p k ζ)‖ ^ 2 < (p : ℝ)⁻¹) (g : M1Kh 1 ψ) :
    (haloWeightH 1 ψ (classicalPoint p k ζ) ω hp2 hψ h0 h1 hT).toWeightSeries.autFactor g.1
        * linX g.1
      = PowerSeries.C (nebCharK ψ ω k ζ (g.1 1 1)) * linX g.1 ^ (k + 1) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`exact autFactor_haloWeightH_classicalPoint ψ ω hp2 hψ hζ k h0 h1 hT g` — its RHS `C (haloCharFunH … (g.1 1 1) * (g.1 1 1)⁻¹ ^ k)` is `C (nebCharK ψ ω k ζ (g.1 1 1))` by `rfl`.

- **Mathlib/project lemmas needed**: `autFactor_haloWeightH_classicalPoint` (ClassicalPoint.lean:412).
- **Sources**: [LWX] §2.1 `lwx.txt:456–474` (classical characters, conductor); `ClassicalPoint.lean:412–466`; `decomposition.md` N-a…N-g.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [N5] `nebChar_mul`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: N2
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem nebChar_mul (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (a b : ℤ_[p]ˣ) :
    nebChar ψ ω k ζ (a * b) = nebChar ψ ω k ζ a * nebChar ψ ω k ζ b := by
  sorry
```

- **Depends on (declarations)**: `nebChar_apply`

**Proof sketch**:
`nebChar_apply` three times; `univChar_mul hp2 ω a b` (IntegralModel.lean:208); `HaloInt.specialize_mul (intHom ψ) hψ' h0 h1` (Specialize.lean:85; `hψ' : ∀ x, ‖intHom ψ x‖ = ‖x‖` from `hψ` and `PadicInt.norm_def`/`intHom_apply`; `h0 h1` as in `nebChar_apply`); `Units.val_mul`, `map_mul`, `mul_inv`, `mul_pow`; `ring`.

- **Mathlib/project lemmas needed**: `nebChar_apply`, `univChar_mul`, `HaloInt.specialize_mul`, `inv_lt_norm_classicalPoint`, `norm_classicalPoint_lt_one`.
- **Sources**: [LWX] §2.1 `lwx.txt:456–474` (classical characters, conductor); `ClassicalPoint.lean:412–466`; `decomposition.md` N-a…N-g.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [N6] `nebChar_one`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: N2
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem nebChar_one (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) : nebChar ψ ω k ζ 1 = 1 := by
  sorry
```

- **Depends on (declarations)**: `nebChar_apply`

**Proof sketch**:
`nebChar_apply`; `univChar_one hp2 ω`; `HaloInt.specialize_one`; `Units.val_one`, `map_one`, `inv_one`, `one_pow`, `mul_one`.

- **Mathlib/project lemmas needed**: `nebChar_apply`, `univChar_one` (IntegralModel.lean:183), `HaloInt.specialize_one` (HaloRing.lean:754).
- **Sources**: [LWX] §2.1 `lwx.txt:456–474` (classical characters, conductor); `ClassicalPoint.lean:412–466`; `decomposition.md` N-a…N-g.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [CLEANUP-N2] Cleanup `PhD/LWX/NebChar.lean`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.NebChar` and `lake exe runLinter PhD.LWX.NebChar` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: `lake env lean PhD/LWX/NebChar.lean` has no warnings; one `omit` added (`continuous_zeta_pow_toZMod`).

### [N7] `nebChar_ne_zero`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: N5, N6
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem nebChar_ne_zero (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (a : ℤ_[p]ˣ) : nebChar ψ ω k ζ a ≠ 0 := by
  sorry
```

- **Depends on (declarations)**: `nebChar_mul`, `nebChar_one`

**Proof sketch**:
`have h := nebChar_mul … a a⁻¹`; `rw [mul_inv_cancel, nebChar_one] at h`; `exact left_ne_zero_of_mul_eq_one h.symm`.

- **Mathlib/project lemmas needed**: `nebChar_mul`, `nebChar_one`, `left_ne_zero_of_mul_eq_one`, `mul_inv_cancel`.
- **Sources**: [LWX] §2.1 `lwx.txt:456–474` (classical characters, conductor); `ClassicalPoint.lean:412–466`; `decomposition.md` N-a…N-g.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [N8] `nebChar_of_norm_sub_one_le_sq`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: N2
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The conductor divides `p²`**: the nebentypus is trivial on `1 + p²ℤ_p`
(`specialize_univChar_eq_padicExp` at level `1`, with the halo exponent `k`). -/
theorem nebChar_of_norm_sub_one_le_sq (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {a : ℤ_[p]ˣ}
    (ha : ‖(a : ℤ_[p]) - 1‖ ≤ (p : ℝ)⁻¹ ^ 2) : nebChar ψ ω k ζ a = 1 := by
  sorry
```

- **Depends on (declarations)**: `nebChar_apply`

**Proof sketch**:
1. `nebChar_apply`; `specialize_univChar_eq_padicExp hp2 hψ h0 h1 hT (h := 1) (u := a) (by simpa using ha)` (HaloWeightH.lean:458): `specialize (univChar ω a) = padicExp (haloExponentH p 1 T₀ * padicLog (intHom ψ a))`.
2. `haloExponentH_one_classicalPoint hp2 hζ hpK k : haloExponentH p 1 (classicalPoint p k ζ) = k` (ClassicalPoint.lean:360); `padicExp_natCast_mul hp2 (hw : ‖padicLog (intHom ψ a)‖^2 < ‖p‖) k : padicExp (k * w) = padicExp w ^ k` (PadicExpLog.lean:578); `padicExp (padicLog (intHom ψ a)) = intHom ψ a` (`PadicExpLog.padicExp_padicLog` — verify name; it is the exp∘log identity used by `intHom_oneUnitPart_eq_padicExp`, TargetPoint.lean:359, read that proof for the exact lemma).  The norm hypothesis: `‖padicLog (intHom ψ a)‖ = ‖intHom ψ a − 1‖ ≤ p⁻²` (`norm_padicLog_eq`, `hψ`, `ha`) so its square `≤ p⁻⁴ < p⁻¹`.
3. `(intHom ψ a)^k * (intHom ψ a)⁻¹^k = 1` (`inv_pow`, `mul_inv_cancel₀`, `pow_ne_zero`; `intHom ψ a ≠ 0` from `‖intHom ψ a‖ = 1`).

- **Mathlib/project lemmas needed**: `specialize_univChar_eq_padicExp`, `haloExponentH_one_classicalPoint`, `padicExp_natCast_mul`, `PadicExpLog.norm_padicLog_eq`, exp∘log identity (read `intHom_oneUnitPart_eq_padicExp`'s proof), `mul_inv_cancel₀`.
- **Sources**: [LWX] §2.1 `lwx.txt:456–474` (classical characters, conductor); `ClassicalPoint.lean:412–466`; `decomposition.md` N-a…N-g. Conductor `∣ p²`: `lwx.txt:470–474`.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [N9] `continuous_zeta_pow_toZMod` [NEW DECL]
- **Status**: done
- **File**: insert after `nebChar_of_norm_sub_one_le_sq` in `PhD/LWX/NebChar.lean`
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem continuous_zeta_pow_toZMod (ζ : K) :
    Continuous fun ℓ : ℤ_[p] => ζ ^ (PadicInt.toZMod ℓ).val := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
New helper (Part N, before `oneAddPow_sub_one_intHom`): `theorem continuous_zeta_pow_toZMod (ζ : K) : Continuous fun ℓ : ℤ_[p] => ζ ^ (PadicInt.toZMod ℓ).val`.
`continuous_iff_continuousAt`; at `ℓ₀`, the function is constant on the open ball `‖ℓ − ℓ₀‖ < 1` (`Metric.ball`, `Metric.isOpen_ball`): `toZMod ℓ = toZMod ℓ₀` iff `ℓ − ℓ₀ ∈ ker toZMod = maximalIdeal` (`PadicInt.ker_toZMod`, `PadicInt.mem_nonunits`/`PadicInt.norm_lt_one_iff_dvd`); `continuousAt_const.congr` with `Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds _ one_pos)`.

- **Mathlib/project lemmas needed**: `PadicInt.ker_toZMod`, `PadicInt.mem_nonunits`, `PadicInt.norm_lt_one_iff_dvd`, `Metric.ball_mem_nhds`, `ContinuousAt.congr`, `continuous_iff_continuousAt`.
- **Sources**: `decomposition.md` N-e attack 2.
- **Generality decision**: Any `K` (only `ζ : K`, no norm needed).
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [CLEANUP-N3] Cleanup `PhD/LWX/NebChar.lean`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.NebChar` and `lake exe runLinter PhD.LWX.NebChar` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: `lake env lean PhD/LWX/NebChar.lean` has no warnings; one `omit` added (`continuous_zeta_pow_toZMod`).

### [N10] `oneAddPow_sub_one_intHom`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: N9
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **`(1 + T)^ℓ` at `T = ζ − 1` is `ζ^{ℓ mod p}`**: both sides are continuous in `ℓ ∈ ℤ_p`
and agree on `ℕ` (`oneAddPow_natCast`, `hζ.pow_eq_one`). -/
theorem oneAddPow_sub_one_intHom (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (ℓ : ℤ_[p]) :
    oneAddPow (ζ - 1) (intHom ψ ℓ) = ζ ^ (PadicInt.toZMod ℓ).val := by
  sorry
```

- **Depends on (declarations)**: `continuous_zeta_pow_toZMod`

**Proof sketch**:
Continuity + density of `ℕ` in `ℤ_p`.
1. `hT : ‖ζ − 1‖ < 1` (`hζ`, `hpK`: `IsPrimitiveRoot` of odd prime order in a `p`-adic field has `‖ζ − 1‖ = p^{−1/(p−1)} < 1` — the project has this at `norm_classicalPoint`-level: use `norm_zeta_sub_one_lt_one`-style lemma from `ClassicalPoint.lean` (search `hζ` lemmas there: `norm_sub_one_lt_one_of_isPrimitiveRoot` or the private helper behind `norm_classicalPoint_lt_one`); if only private, re-prove: `ζ^p = 1`, `‖ζ‖ = 1`, and the factorisation `∏(ζ^i − 1) = p` forces `‖ζ − 1‖ < 1` — or read `weightPoint`/`classicalPoint` norm lemmas which already contain it).
2. LHS continuous: `continuous_oneAddPow_intHom ψ hψ hT` (PowSubOne.lean:67); RHS: `continuous_zeta_pow_toZMod`.
3. `(PadicInt.denseRange_natCast).equalizer hL hR (funext fun n => ?_)` (`DenseRange.equalizer`): at `ℓ = n`: `oneAddPow (ζ−1) (intHom ψ n) = oneAddPow (ζ−1) (n : K)` (`map_natCast`) `= (1 + (ζ − 1))^n = ζ^n` (`oneAddPow_natCast`, PowSubOne.lean:50, `add_sub_cancel`); and `ζ^n = ζ^(n % p)` (`Nat.div_add_mod n p`, `pow_add`, `pow_mul`, `hζ.pow_eq_one`, `one_pow`); `(toZMod (n : ℤ_p)).val = n % p` (`map_natCast`, `ZMod.val_natCast`).

- **Mathlib/project lemmas needed**: `continuous_oneAddPow_intHom`, `continuous_zeta_pow_toZMod`, `PadicInt.denseRange_natCast`, `DenseRange.equalizer`, `oneAddPow_natCast`, `ZMod.val_natCast`, `IsPrimitiveRoot.pow_eq_one`, `Nat.div_add_mod`.
- **Sources**: [LWX] `lwx.txt:430–433` (`T_χ = χ(exp q) − 1`); `decomposition.md` N-e.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [N11] `oneUnitPart_oneAddPMul` [NEW DECL]
- **Status**: done
- **File**: insert after `oneAddPow_sub_one_intHom` in `PhD/LWX/NebChar.lean`
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem oneUnitPart_oneAddPMul (x : ℤ_[p]) : oneUnitPart (oneAddPMul p x) = 1 + (p : ℤ_[p]) * x := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
New helper: `theorem oneUnitPart_oneAddPMul (x : ℤ_[p]) : oneUnitPart (oneAddPMul p x) = 1 + (p : ℤ_[p]) * x`.  `oneUnitPart` (UnitsLog.lean:193) is `u * (teichmuller u)⁻¹`; `teichmuller_eq_one_of_norm_sub_one_le` (HaloWeightH.lean:409) with `‖(1 + px) − 1‖ = ‖px‖ ≤ p⁻¹`; `inv_one`, `mul_one`, `coe_oneAddPMul`.

- **Mathlib/project lemmas needed**: `oneUnitPart`, `teichmuller_eq_one_of_norm_sub_one_le`, `coe_oneAddPMul`, `PadicInt.norm_p`.
- **Sources**: `decomposition.md` N-e.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [N12] `nebChar_oneAddPMul`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: N2, N10, N11
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The nebentypus on `1 + pℤ_p`** is `ζ^{ℓ⟨a⟩ mod p}` (`oneAddPow_weightPoint_mul_padicExp` at
`(s, t) = (0, k)`, `intHom_oneUnitPart_eq_padicExp`, `oneAddPow_sub_one_intHom`). -/
theorem nebChar_oneAddPMul (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (x : ℤ_[p]) :
    nebChar ψ ω k ζ (oneAddPMul p x)
      = ζ ^ (PadicInt.toZMod (logQuot (oneAddPMul p x))).val := by
  sorry
```

- **Depends on (declarations)**: `nebChar_apply`, `oneAddPow_sub_one_intHom`, `oneUnitPart_oneAddPMul`

**Proof sketch**:
1. `nebChar_apply`; `specialize_univChar (intHom ψ) hψ' h0 h1 ω a` (Specialize.lean:217): `= intHom ψ (ω (toZMod-units a)) * oneAddPow T₀ (intHom ψ (logQuot a)) * (intHom ψ a)⁻¹^k`.
2. `Units.map toZMod (oneAddPMul p x) = 1`: `Units.ext`, `Units.coe_map`, `coe_oneAddPMul`, `map_add`, `map_mul`, `map_natCast`, `ZMod.natCast_self`, `mul_zero`, `add_zero`, `map_one`; so `ω 1 = 1`, `map_one`, `one_mul`.
3. `T₀ = classicalPoint p k ζ = weightPoint p (k : ℤ) ζ` (unfold both: `Int.cast_natCast`; `rfl` up to the cast) and `weightPoint p 0 ζ = ζ − 1` (`Int.cast_zero`, `mul_zero`, `PadicExpLog.padicExp_zero`, `mul_one`); `oneAddPow_weightPoint_mul_padicExp hp2 hψ hζ hpK 0 k (logQuot a)` (TargetPoint.lean:387) gives `oneAddPow (classicalPoint) ℓ = oneAddPow (ζ − 1) ℓ * padicExp (p * k * intHom ψ ℓ)`.
4. `padicExp (p * k * intHom ψ ℓ) = (intHom ψ (oneUnitPart a))^k`: `intHom_oneUnitPart_eq_padicExp hp2 hψ a` (TargetPoint.lean:359: `intHom (oneUnitPart a) = padicExp (p * intHom (logQuot a))`) and `padicExp_natCast_mul hp2 hw k` (with `mul_comm`/`mul_assoc` to shape `k * (p * ℓ)`; `hw : ‖p * intHom ψ ℓ‖^2 < ‖p‖` from `‖ℓ‖ ≤ 1`, `hpK`).
5. `oneUnitPart_oneAddPMul`, `coe_oneAddPMul`: `(intHom ψ (1+px))^k * (intHom ψ (1+px))⁻¹^k = 1`; `oneAddPow_sub_one_intHom` for the remaining factor.

- **Mathlib/project lemmas needed**: `nebChar_apply`, `specialize_univChar`, `oneAddPow_weightPoint_mul_padicExp`, `intHom_oneUnitPart_eq_padicExp`, `padicExp_natCast_mul`, `oneUnitPart_oneAddPMul`, `oneAddPow_sub_one_intHom`, `PadicExpLog.padicExp_zero`, `ZMod.natCast_self`.
- **Sources**: [LWX] §2.1 `lwx.txt:456–474` (classical characters, conductor); `ClassicalPoint.lean:412–466`; `decomposition.md` N-a…N-g. `lwx.txt:430–433`.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [CLEANUP-N4] Cleanup `PhD/LWX/NebChar.lean`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.NebChar` and `lake exe runLinter PhD.LWX.NebChar` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: `lake env lean PhD/LWX/NebChar.lean` has no warnings; one `omit` added (`continuous_zeta_pow_toZMod`).

### [N13] `norm_logQuot_oneAddPMul_one`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: N11
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `ℓ⟨1 + p⟩ = log(1+p)/p` is a unit (`norm_padicLog_eq`). -/
theorem norm_logQuot_oneAddPMul_one (hp2 : p ≠ 2) :
    ‖(logQuot (oneAddPMul p 1) : ℤ_[p])‖ = 1 := by
  sorry
```

- **Depends on (declarations)**: `oneUnitPart_oneAddPMul`

**Proof sketch**:
`logQuot a = ⟨qlog (oneUnitPart a) / p, _⟩` (IntegralModel.lean:147); `PadicInt.norm_def`; `oneUnitPart_oneAddPMul` at `x = 1`; `qlog u = padicLog (u : ℚ_p)` (UnitsLog.lean:203); `PadicExpLog.norm_padicLog_eq norm_p_lt_one hp2 (sq_norm_coe_sub_one_lt _)` exactly as in `norm_qlog_le` (UnitsLog.lean:306): `‖qlog (1+p)‖ = ‖(1+p) − 1‖ = ‖p‖ = p⁻¹`; `norm_div`, `Padic.norm_p`, `div_self`.

- **Mathlib/project lemmas needed**: `logQuot`, `qlog`, `PadicExpLog.norm_padicLog_eq`, `norm_qlog_le` (proof pattern), `oneUnitPart_oneAddPMul`, `Padic.norm_p`, `PadicInt.norm_def`.
- **Sources**: `decomposition.md` N-e.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [N14] `isPrimitiveRoot_nebChar_oneAddPMul_one`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: N12, N13
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The conductor is exactly `p²`**: `nebChar (1 + p)` is a primitive `p`-th root of unity. -/
theorem isPrimitiveRoot_nebChar_oneAddPMul_one (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) :
    IsPrimitiveRoot (nebChar ψ ω k ζ (oneAddPMul p 1)) p := by
  sorry
```

- **Depends on (declarations)**: `nebChar_oneAddPMul`, `norm_logQuot_oneAddPMul_one`

**Proof sketch**:
1. `nebChar_oneAddPMul` at `x = 1`: `= ζ ^ (toZMod ℓ).val`, `ℓ := logQuot (oneAddPMul p 1)`.
2. `toZMod ℓ ≠ 0`: `‖ℓ‖ = 1` (`norm_logQuot_oneAddPMul_one`) so `ℓ ∉ maximalIdeal = ker toZMod` (`PadicInt.ker_toZMod`, `PadicInt.mem_nonunits`, `PadicInt.norm_lt_one_iff_dvd`/`PadicInt.isUnit_iff`).
3. `Nat.Coprime (toZMod ℓ).val p`: `(toZMod ℓ).val < p` (`ZMod.val_lt`) and `≠ 0` (`ZMod.val_eq_zero`), so `Nat.Coprime` by `(Nat.coprime_primes …)`/`Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 (Nat.not_dvd_of_pos_of_lt …))`.
4. `hζ.pow_of_coprime _ hcop`.

- **Mathlib/project lemmas needed**: `nebChar_oneAddPMul`, `norm_logQuot_oneAddPMul_one`, `PadicInt.ker_toZMod`, `ZMod.val_lt`, `ZMod.val_eq_zero`, `Nat.Prime.coprime_iff_not_dvd`, `IsPrimitiveRoot.pow_of_coprime`.
- **Sources**: [LWX] `lwx.txt:2028–2030` (conductor exactly `p²`); `decomposition.md` N-e.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [N15] `nebChar_oneAddPMul_natCast`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: N5, N8
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `nebChar (1 + p n) = nebChar (1 + p)^n`: `(1+p)^n ≡ 1 + pn (mod p²)` and the conductor. -/
theorem nebChar_oneAddPMul_natCast (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (n : ℕ) :
    nebChar ψ ω k ζ (oneAddPMul p n) = nebChar ψ ω k ζ (oneAddPMul p 1) ^ n := by
  sorry
```

- **Depends on (declarations)**: `nebChar_mul`, `nebChar_of_norm_sub_one_le_sq`

**Proof sketch**:
Induction on `n` (`n = 0`: `oneAddPMul p 0 = 1` (`Units.ext`, `Nat.cast_zero`, `mul_zero`, `add_zero`), `nebChar_one`, `pow_zero`).  Step: set `w := (oneAddPMul p n * oneAddPMul p 1)⁻¹ * oneAddPMul p (n+1)` (a unit); then `oneAddPMul p (n+1) = oneAddPMul p n * oneAddPMul p 1 * w` (`mul_inv_cancel_left`), `nebChar_mul` twice, `ih`, `pow_succ`, and `nebChar w = 1` by `nebChar_of_norm_sub_one_le_sq` with `‖(w : ℤ_p) − 1‖ ≤ p⁻²`: `(w − 1) = (oneAddPMul p n * oneAddPMul p 1)⁻¹ * ((1 + p(n+1)) − (1+pn)(1+p))` and `(1+p(n+1)) − (1+pn)(1+p) = −p² n` (`push_cast`, `ring`); `norm_mul`, `PadicInt.norm_units`, `‖p² n‖ ≤ ‖p‖² = p⁻²` (`norm_pow`, `PadicInt.norm_p`, `PadicInt.norm_le_one`).

- **Mathlib/project lemmas needed**: `nebChar_mul`, `nebChar_one`, `nebChar_of_norm_sub_one_le_sq`, `Units.ext`, `coe_oneAddPMul`, `PadicInt.norm_units`, `PadicInt.norm_p`, `mul_inv_cancel_left`.
- **Sources**: `decomposition.md` N-e attack 3.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [CLEANUP-N5] Cleanup `PhD/LWX/NebChar.lean`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.NebChar` and `lake exe runLinter PhD.LWX.NebChar` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: `lake env lean PhD/LWX/NebChar.lean` has no warnings; one `omit` added (`continuous_zeta_pow_toZMod`).

### [N16] `sum_nebChar_oneAddPMul_mul_eq_zero`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: N15, N14
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The character sum**: for `p ∤ b`, `∑_{c < p} ψ_neb(1 + p b c) = 0`
(`IsPrimitiveRoot.geom_sum_eq_zero` at the primitive root `nebChar (1+p)^b`). -/
theorem sum_nebChar_oneAddPMul_mul_eq_zero (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {b : ℕ} (hb : ¬ p ∣ b) :
    ∑ c ∈ Finset.range p, nebChar ψ ω k ζ (oneAddPMul p ((b : ℤ_[p]) * c)) = 0 := by
  sorry
```

- **Depends on (declarations)**: `nebChar_oneAddPMul_natCast`, `isPrimitiveRoot_nebChar_oneAddPMul_one`

**Proof sketch**:
1. Termwise: `oneAddPMul p ((b : ℤ_p) * c) = oneAddPMul p ((b * c : ℕ) : ℤ_p)` (`Nat.cast_mul`; `Units.ext`/`congrArg`), `nebChar_oneAddPMul_natCast (b*c)`, `pow_mul`: term `= (ξ^b)^c` with `ξ := nebChar (oneAddPMul p 1)`.
2. `hξ : IsPrimitiveRoot (ξ^b) p := (isPrimitiveRoot_nebChar_oneAddPMul_one …).pow_of_coprime b (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hb))`.
3. `hξ.geom_sum_eq_zero hp.out.one_lt`.

- **Mathlib/project lemmas needed**: `nebChar_oneAddPMul_natCast`, `isPrimitiveRoot_nebChar_oneAddPMul_one`, `IsPrimitiveRoot.pow_of_coprime`, `IsPrimitiveRoot.geom_sum_eq_zero`, `Nat.Prime.coprime_iff_not_dvd`, `pow_mul`.
- **Sources**: `scratch` `sum_diagUnit_eq_zero` (the same statement for an abstract character); `decomposition.md` N-f.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [N17] `sum_inv_nebChar_oneAddPMul_mul_eq_zero`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: N16, N15, N14
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The character sum, inverted** (the form the identity computation consumes: the `d`-entry of
`ℓQ b c` is `1 + bcp`, and its nebentypus enters inverted through the level-equivariance at
`ℓ⁻¹`): for `p ∤ b`, `∑_{c < p} ψ_neb(1 + p b c)⁻¹ = 0`. -/
theorem sum_inv_nebChar_oneAddPMul_mul_eq_zero (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {b : ℕ} (hb : ¬ p ∣ b) :
    ∑ c ∈ Finset.range p, (nebChar ψ ω k ζ (oneAddPMul p ((b : ℤ_[p]) * c)))⁻¹ = 0 := by
  sorry
```

- **Depends on (declarations)**: `sum_nebChar_oneAddPMul_mul_eq_zero`, `nebChar_oneAddPMul_natCast`, `isPrimitiveRoot_nebChar_oneAddPMul_one`

**Proof sketch**:
As `sum_nebChar_oneAddPMul_mul_eq_zero` with `ξ⁻¹` (`IsPrimitiveRoot.inv`) and `inv_pow`: term `= ((ξ⁻¹)^b)^c`.

- **Mathlib/project lemmas needed**: `IsPrimitiveRoot.inv`, `inv_pow`, `IsPrimitiveRoot.geom_sum_eq_zero`.
- **Sources**: `decomposition.md` N-f.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [N18] `sum_inv_nebCharK_eq_zero`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: N17
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The same in terms of `nebCharK` at `ψ(1 + b c p)`, the spelling that appears in the
identity computation. -/
theorem sum_inv_nebCharK_eq_zero (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {b : ℕ} (hb : ¬ p ∣ b) :
    ∑ c ∈ Finset.range p, (nebCharK ψ ω k ζ (ψ (1 + (b : ℚ_[p]) * c * p)))⁻¹ = 0 := by
  sorry
```

- **Depends on (declarations)**: `sum_inv_nebChar_oneAddPMul_mul_eq_zero`

**Proof sketch**:
`Finset.sum_congr rfl fun c _ => ?_` reducing each term to `(nebChar … (oneAddPMul p (b * c)))⁻¹`: `nebChar`, `coe_oneAddPMul`, `intHom_apply`, `push_cast`, `ring_nf` (`1 + b c p = 1 + p (b c)`); then `sum_inv_nebChar_oneAddPMul_mul_eq_zero hb`.

- **Mathlib/project lemmas needed**: `sum_inv_nebChar_oneAddPMul_mul_eq_zero`, `coe_oneAddPMul`, `intHom_apply`.
- **Sources**: `decomposition.md` N-f attack 3.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [CLEANUP-N6] Cleanup `PhD/LWX/NebChar.lean`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.NebChar` and `lake exe runLinter PhD.LWX.NebChar` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: `lake env lean PhD/LWX/NebChar.lean` has no warnings; one `omit` added (`continuous_zeta_pow_toZMod`).

### [N19] `nebCharK_psi_mul`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: N5
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `hmul`: `nebCharK` is multiplicative on `ψ`-images of `p`-adic units (`nebChar_mul` at the
units `⟨x, _⟩`, `⟨y, _⟩` of `ℤ_p`). -/
theorem nebCharK_psi_mul (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {x y : ℚ_[p]} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    nebCharK ψ ω k ζ (ψ (x * y)) = nebCharK ψ ω k ζ (ψ x) * nebCharK ψ ω k ζ (ψ y) := by
  sorry
```

- **Depends on (declarations)**: `nebChar_mul`

**Proof sketch**:
Let `a := ⟨x, hx.le⟩ : ℤ_[p]`, a unit (`PadicInt.isUnit_iff.2 hx`), `ua := (isUnit …).unit`; similarly `ub`.  `ψ (x * y) = intHom ψ ((ua * ub : ℤ_[p]ˣ) : ℤ_[p])` (`intHom_apply`, `Units.val_mul`, `PadicInt.coe_mul`), so LHS `= nebChar … (ua * ub)` (`nebChar` def); `nebChar_mul`; back to `nebCharK` on each factor.

- **Mathlib/project lemmas needed**: `nebChar_mul`, `PadicInt.isUnit_iff`, `IsUnit.unit_spec`, `intHom_apply`.
- **Sources**: `decomposition.md` I-f (ii).
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [N20] `nebCharK_psi_ne_zero`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: N7
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `hne`: `nebCharK` does not vanish on `ψ`-images of `p`-adic units. -/
theorem nebCharK_psi_ne_zero (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {x : ℚ_[p]} (hx : ‖x‖ = 1) :
    nebCharK ψ ω k ζ (ψ x) ≠ 0 := by
  sorry
```

- **Depends on (declarations)**: `nebChar_ne_zero`

**Proof sketch**:
As `nebCharK_psi_mul`: `ψ x = intHom ψ (ua : ℤ_p)`, then `nebChar_ne_zero`.

- **Mathlib/project lemmas needed**: `nebChar_ne_zero`, `PadicInt.isUnit_iff`.
- **Sources**: `decomposition.md` I-f (ii).
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [N21] `nebCharK_psi_of_norm_sub_one_le_sq`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: N8
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `hcond`: `nebCharK` is trivial on `ψ(1 + p²ℤ_p)`. -/
theorem nebCharK_psi_of_norm_sub_one_le_sq (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {x : ℚ_[p]}
    (hx : ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2) : nebCharK ψ ω k ζ (ψ x) = 1 := by
  sorry
```

- **Depends on (declarations)**: `nebChar_of_norm_sub_one_le_sq`

**Proof sketch**:
`‖x‖ = 1` from `‖x − 1‖ ≤ p⁻² < 1` (`norm_sub_rev`, ultrametric `norm_eq_of_norm_sub_lt`-type: `‖x‖ = ‖1 + (x−1)‖ = 1`); `ua` as above; `‖(ua : ℤ_p) − 1‖ ≤ p⁻²` is `hx` (`PadicInt.norm_def`); `nebChar_of_norm_sub_one_le_sq`.

- **Mathlib/project lemmas needed**: `nebChar_of_norm_sub_one_le_sq`, `PadicInt.isUnit_iff`, `PadicInt.norm_def`.
- **Sources**: `decomposition.md` I-f (ii).
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [CLEANUP-N7] Cleanup `PhD/LWX/NebChar.lean`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.NebChar` and `lake exe runLinter PhD.LWX.NebChar` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: `lake env lean PhD/LWX/NebChar.lean` has no warnings; one `omit` added (`continuous_zeta_pow_toZMod`).

### [N22] `partnerChar_apply`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem partnerChar_apply (r : (ZMod p)ˣ) :
    partnerChar p ω k r = (ω r)⁻¹ * teichRes r ^ (2 * k) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`unfold partnerChar`; `MonoidHom.mul_apply`, `MonoidHom.pow_apply`, `teichChar_apply` (TargetPoint.lean, used by `targetChar_apply`), and `invChar` applied is `(ω r)⁻¹` by `rfl` (ConjChar.lean:35).

- **Mathlib/project lemmas needed**: `MonoidHom.mul_apply`, `MonoidHom.pow_apply`, `teichChar_apply`, `invChar`.
- **Sources**: [LWX] `lwx.txt:2028–2036`.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [N23] `oneAddPow_inv_sub_one_mul`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: N10
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `(1+T)^ℓ` at `T = ζ⁻¹ − 1` and at `T = ζ − 1` are inverse to each other. -/
theorem oneAddPow_inv_sub_one_mul (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (ℓ : ℤ_[p]) :
    oneAddPow (ζ⁻¹ - 1) (intHom ψ ℓ) * oneAddPow (ζ - 1) (intHom ψ ℓ) = 1 := by
  sorry
```

- **Depends on (declarations)**: `oneAddPow_sub_one_intHom`

**Proof sketch**:
`oneAddPow_sub_one_intHom` for `ζ` (with `hζ`) and for `ζ⁻¹` (with `hζ.inv`): the product is `ζ⁻¹^v * ζ^v = 1` (`inv_pow`, `inv_mul_cancel₀ (pow_ne_zero _ hζ.ne_zero')` — `IsPrimitiveRoot.ne_zero` needs `p ≠ 0`).

- **Mathlib/project lemmas needed**: `oneAddPow_sub_one_intHom`, `IsPrimitiveRoot.inv`, `inv_pow`, `inv_mul_cancel₀`, `IsPrimitiveRoot.ne_zero`.
- **Sources**: `decomposition.md` N-g.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [N24] `nebChar_eq`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: N2, N10
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **`nebChar` in closed form**: `ψ_neb(a) = ω(ā) · ζ^{ℓ⟨a⟩ mod p} · ω₀(ā)^{−k}` — the `oneUnitPart`
factors `(oneUnitPart a)^k · a^{−k}` collapse to `teichmüller(a)^{−k}`
(`nebChar_apply`, `specialize_univChar`, `oneAddPow_weightPoint_mul_padicExp` at `(0, k)`,
`intHom_oneUnitPart_eq_padicExp`, `oneAddPow_sub_one_intHom`, `coe_eq_teichRes_mul_oneUnitPart`). -/
theorem nebChar_eq (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (a : ℤ_[p]ˣ) :
    nebChar ψ ω k ζ a
      = intHom ψ (ω (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p])
        * ζ ^ (PadicInt.toZMod (logQuot a)).val
        * (intHom ψ (teichRes (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p]))⁻¹ ^ k := by
  sorry
```

- **Depends on (declarations)**: `nebChar_apply`, `oneAddPow_sub_one_intHom`

**Proof sketch**:
1. `nebChar_apply`, `specialize_univChar` as in `nebChar_oneAddPMul` steps 1, 3, 4: `nebChar a = intHom ψ (ω ā) * oneAddPow (ζ−1) ℓ * padicExp (p k ℓ) * (intHom ψ a)⁻¹^k` with `ℓ = logQuot a`, `ā = Units.map toZMod a`.
2. `padicExp (p k ℓ) = (intHom ψ (oneUnitPart a))^k` (`intHom_oneUnitPart_eq_padicExp`, `padicExp_natCast_mul`).
3. `(a : ℤ_p) = teichRes ā * oneUnitPart a` (`coe_eq_teichRes_mul_oneUnitPart`, TargetPoint.lean:319); `map_mul`, `mul_inv`, `mul_pow`, `inv_pow`; the `oneUnitPart` powers cancel (`mul_inv_cancel₀`, `intHom ψ (oneUnitPart a) ≠ 0` from norm `1`).
4. `oneAddPow_sub_one_intHom`; `ring`.

- **Mathlib/project lemmas needed**: `nebChar_apply`, `specialize_univChar`, `oneAddPow_weightPoint_mul_padicExp`, `intHom_oneUnitPart_eq_padicExp`, `padicExp_natCast_mul`, `coe_eq_teichRes_mul_oneUnitPart`, `oneAddPow_sub_one_intHom`.
- **Sources**: `decomposition.md` N-g.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [CLEANUP-N8] Cleanup `PhD/LWX/NebChar.lean`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.NebChar` and `lake exe runLinter PhD.LWX.NebChar` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: `lake env lean PhD/LWX/NebChar.lean` has no warnings; one `omit` added (`continuous_zeta_pow_toZMod`).

### [N25] `nebChar_partnerChar`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: N24, N22
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The partner point carries the inverse nebentypus** (the other half of AG-ω₀):
at `T_{χ_k}(ζ⁻¹)` with tame character `ω⁻¹ω₀^{2k}`, the nebentypus is `ψ_neb⁻¹`. -/
theorem nebChar_partnerChar (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (a : ℤ_[p]ˣ) :
    nebChar ψ (partnerChar p ω k) k ζ⁻¹ a = (nebChar ψ ω k ζ a)⁻¹ := by
  sorry
```

- **Depends on (declarations)**: `nebChar_eq`, `partnerChar_apply`

**Proof sketch**:
`nebChar_eq` for `(ω, ζ)` and for `(partnerChar p ω k, ζ⁻¹)` (with `hζ.inv`); `partnerChar_apply`: `ω'(ā) = (ω ā)⁻¹ * teichRes ā ^ (2k)`; `Units.val_mul`, `Units.val_pow_eq_pow_val`, `Units.val_inv_eq_inv_val`, `map_mul`, `map_pow`, `map_inv₀`; `inv_pow`; then `eq_inv_of_mul_eq_one_left`: the product is `(ω ā)⁻¹ t^{2k} ζ^{-v} t^{-k} · ω(ā) ζ^{v} t^{-k} = 1` (`field_simp` with `intHom ψ (ω ā) ≠ 0`, `intHom ψ (teichRes ā) ≠ 0` (units), `ζ ≠ 0`; `ring`).

- **Mathlib/project lemmas needed**: `nebChar_eq`, `partnerChar_apply`, `eq_inv_of_mul_eq_one_left`, `Units.val_pow_eq_pow_val`, `map_inv₀`, `field_simp`.
- **Sources**: [LWX] `lwx.txt:2028–2036` (`ω' = ω⁻¹ω₀^{2k}`); `decomposition.md` N-g.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [N26] `nebCharK_partnerChar`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: N25
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The partner nebentypus function on `K`, at the image of a unit: `nebCharK` at
`(ω⁻¹ω₀^{2k}, ζ⁻¹)` is the inverse of `nebCharK` at `(ω, ζ)` (the spelling `hκ'` consumes:
every `g ∈ M1Kh 1 ψ` has `g 1 1 = intHom ψ d` for a unit `d`). -/
theorem nebCharK_partnerChar (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (a : ℤ_[p]ˣ) :
    nebCharK ψ (partnerChar p ω k) k ζ⁻¹ (intHom ψ (a : ℤ_[p]))
      = (nebCharK ψ ω k ζ (intHom ψ (a : ℤ_[p])))⁻¹ := by
  sorry
```

- **Depends on (declarations)**: `nebChar_partnerChar`

**Proof sketch**:
`exact nebChar_partnerChar … a` (both sides are `nebChar` at `a` by `rfl`).

- **Mathlib/project lemmas needed**: `nebChar_partnerChar`.
- **Sources**: `decomposition.md` I-k.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [N27] `autFactor_haloWeightH_partner_eq_inv_nebCharK`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: N4, N26
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The shape constant of the partner halo weight at `g ∈ M1Kh` is `nebCharK(g 1 1)⁻¹`
(`autFactor_haloWeightH_classicalPoint_eq_nebCharK` at the partner point, `nebCharK_partnerChar`,
and `g 1 1 = intHom ψ d` with `d` a unit: `mem_M1Kh` gives `g 1 1 = ψ (δ 1 1)` for `δ ∈ Mh`). -/
theorem autFactor_haloWeightH_partner_eq_inv_nebCharK (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (h0 : (p : ℝ)⁻¹ < ‖classicalPoint p k ζ⁻¹‖) (h1 : ‖classicalPoint p k ζ⁻¹‖ < 1)
    (hT : ‖TH p 1 (classicalPoint p k ζ⁻¹)‖ ^ 2 < (p : ℝ)⁻¹) (g : M1Kh 1 ψ) :
    (haloWeightH 1 ψ (classicalPoint p k ζ⁻¹) (partnerChar p ω k) hp2 hψ h0 h1 hT).toWeightSeries.autFactor
          g.1 * linX g.1
      = PowerSeries.C (nebCharK ψ ω k ζ (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1) := by
  sorry
```

- **Depends on (declarations)**: `autFactor_haloWeightH_classicalPoint_eq_nebCharK`, `nebCharK_partnerChar`

**Proof sketch**:
1. `autFactor_haloWeightH_classicalPoint_eq_nebCharK` at `(partnerChar p ω k, ζ⁻¹, hζ.inv)`: RHS `C (nebCharK ψ ω' k ζ⁻¹ (g.1 1 1))`.
2. `g.1 1 1 = intHom ψ d` for a unit `d`: `obtain ⟨δ, hδ, rfl⟩ := mem_M1Kh_iff.1 g.2` (HaloWeightH.lean:125); `RingHom.mapMatrix_apply`, `Matrix.map_apply`: `g.1 1 1 = ψ (δ 1 1)`; `‖δ 1 1‖ = 1` (`mem_Mh_iff`, :96) so `d := (PadicInt.isUnit_iff.2 …).unit` with `(d : ℤ_p) = ⟨δ 1 1, _⟩`.
3. `nebCharK_partnerChar … d`; `congr 1`.

- **Mathlib/project lemmas needed**: `autFactor_haloWeightH_classicalPoint_eq_nebCharK`, `nebCharK_partnerChar`, `mem_M1Kh_iff`, `mem_Mh_iff`, `PadicInt.isUnit_iff`, `RingHom.mapMatrix_apply`, `Matrix.map_apply`.
- **Sources**: `decomposition.md` I-k.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [CLEANUP-N9] Cleanup `PhD/LWX/NebChar.lean`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.NebChar` and `lake exe runLinter PhD.LWX.NebChar` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: `lake env lean PhD/LWX/NebChar.lean` has no warnings; one `omit` added (`continuous_zeta_pow_toZMod`).

### [N28] `classicalData_partnerChar_u`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: N3, N25
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The constants of the partner classical datum are the inverses of the datum's. -/
theorem classicalData_partnerChar_u (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (i : ι) (t : Fin p)
    (a : ZMod (p ^ 1)) :
    (classicalData ψ (partnerChar p ω k) θG U hU vRep hvΔ uu hp2 hψ hζ.inv hpK k).u i t a
      = ((classicalData ψ ω θG U hU vRep hvΔ uu hp2 hψ hζ hpK k).u i t a)⁻¹ := by
  sorry
```

- **Depends on (declarations)**: `classicalData_u_eq_nebChar`, `nebChar_partnerChar`

**Proof sketch**:
`classicalData_u_eq_nebChar` for both data (the partner's `u` is `nebChar ψ ω' k ζ⁻¹ d` at the same `d`); `nebChar_partnerChar … d`.

- **Mathlib/project lemmas needed**: `classicalData_u_eq_nebChar`, `nebChar_partnerChar`.
- **Sources**: `decomposition.md` N-g.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched. Engineering notes: an element of `ℤ_[p]` built by anonymous constructor must be `let z : ℤ_[p] := ⟨x, h⟩` (an inline `(⟨x, h⟩ : ℤ_[p])` elaborates at the subtype and loses the `Norm` instance); `nebChar_oneAddPMul_natCast` went through the conductor (`w ≡ 1 mod p²`) rather than `logQuot` arithmetic, as planned.

### [CLEANUP-N-FINAL] Final cleanup `PhD/LWX/NebChar.lean`
- **Status**: done
- **File**: PhD/LWX/NebChar.lean
- **Depends on**: every proof ticket of Part N
- **Parallel**: no
- **Type**: cleanup

Whole-file `/cleanup`: sorry-free check (`grep -c sorry` = 0), `#print axioms` on the file's
headline declarations (standard axioms only), `lake exe runLinter PhD.LWX.NebChar` clean, module
docstring updated to describe what is proved (drop "skeleton"/"planned" wording), relocations
named in `tickets.md` performed with one rebuild.
- **Progress**: 2026-09-10: DONE — inline cleanup: `lake env lean PhD/LWX/NebChar.lean` has no warnings; one `omit` added (`continuous_zeta_pow_toZMod`).


## Part L — `PhD/LWX/AtkinLehnerLocal.lean`: local matrices in the disc-model coordinate

### [L1] `det_vQ`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
@[simp] theorem det_vQ (c : ℚ_[p]) : (vQ p c).det = (p : ℚ_[p]) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`unfold`; `Matrix.det_fin_two_of`; `ring` (for `det_ℓQ`: `(1−bcp)(1+bcp) + b²cp·cp = 1`).

- **Mathlib/project lemmas needed**: `Matrix.det_fin_two_of`, `Matrix.mul_fin_two`, `Matrix.smul_of`, `Matrix.of_apply`, `Matrix.one_fin_two`, `Matrix.ext_iff`/`Matrix.ext`, `Fin.forall_fin_two`, `field_simp`, `ring`; `(p : ℚ_[p]) ≠ 0` from `Nat.cast_ne_zero.2 hp.out.ne_zero`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [L2] `det_sQ`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
@[simp] theorem det_sQ (b : ℚ_[p]) : (sQ p b).det = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`unfold`; `Matrix.det_fin_two_of`; `ring` (for `det_ℓQ`: `(1−bcp)(1+bcp) + b²cp·cp = 1`).

- **Mathlib/project lemmas needed**: `Matrix.det_fin_two_of`, `Matrix.mul_fin_two`, `Matrix.smul_of`, `Matrix.of_apply`, `Matrix.one_fin_two`, `Matrix.ext_iff`/`Matrix.ext`, `Fin.forall_fin_two`, `field_simp`, `ring`; `(p : ℚ_[p]) ≠ 0` from `Nat.cast_ne_zero.2 hp.out.ne_zero`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [L3] `det_wQ`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
@[simp] theorem det_wQ : (wQ p).det = (p : ℚ_[p]) ^ 2 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`unfold`; `Matrix.det_fin_two_of`; `ring` (for `det_ℓQ`: `(1−bcp)(1+bcp) + b²cp·cp = 1`).

- **Mathlib/project lemmas needed**: `Matrix.det_fin_two_of`, `Matrix.mul_fin_two`, `Matrix.smul_of`, `Matrix.of_apply`, `Matrix.one_fin_two`, `Matrix.ext_iff`/`Matrix.ext`, `Fin.forall_fin_two`, `field_simp`, `ring`; `(p : ℚ_[p]) ≠ 0` from `Nat.cast_ne_zero.2 hp.out.ne_zero`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [CLEANUP-L1] Cleanup `PhD/LWX/AtkinLehnerLocal.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerLocal` and `lake exe runLinter PhD.LWX.AtkinLehnerLocal` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: tactic tails tailored per linter (no unused simp args, no dead `field_simp`/`ring`), `lake env lean` clean.

### [L4] `det_ℓQ`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
@[simp] theorem det_ℓQ (b c : ℚ_[p]) : (ℓQ p b c).det = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`unfold`; `Matrix.det_fin_two_of`; `ring` (for `det_ℓQ`: `(1−bcp)(1+bcp) + b²cp·cp = 1`).

- **Mathlib/project lemmas needed**: `Matrix.det_fin_two_of`, `Matrix.mul_fin_two`, `Matrix.smul_of`, `Matrix.of_apply`, `Matrix.one_fin_two`, `Matrix.ext_iff`/`Matrix.ext`, `Fin.forall_fin_two`, `field_simp`, `ring`; `(p : ℚ_[p]) ≠ 0` from `Nat.cast_ne_zero.2 hp.out.ne_zero`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [L5] `wQ_mul_wQinv`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem wQ_mul_wQinv : wQ p * wQinv p = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`unfold`; `Matrix.mul_fin_two` (and `Matrix.one_fin_two` where the RHS is `1`); `Matrix.of` extensionality (`ext i j; fin_cases i <;> fin_cases j <;> simp`); `p ≠ 0`; `Matrix.mul_fin_two`, `Matrix.one_fin_two`, `field_simp`.

- **Mathlib/project lemmas needed**: `Matrix.det_fin_two_of`, `Matrix.mul_fin_two`, `Matrix.smul_of`, `Matrix.of_apply`, `Matrix.one_fin_two`, `Matrix.ext_iff`/`Matrix.ext`, `Fin.forall_fin_two`, `field_simp`, `ring`; `(p : ℚ_[p]) ≠ 0` from `Nat.cast_ne_zero.2 hp.out.ne_zero`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [L6] `wQinv_mul_wQ`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem wQinv_mul_wQ : wQinv p * wQ p = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`unfold`; `Matrix.mul_fin_two` (and `Matrix.one_fin_two` where the RHS is `1`); `Matrix.of` extensionality (`ext i j; fin_cases i <;> fin_cases j <;> simp`); same.

- **Mathlib/project lemmas needed**: `Matrix.det_fin_two_of`, `Matrix.mul_fin_two`, `Matrix.smul_of`, `Matrix.of_apply`, `Matrix.one_fin_two`, `Matrix.ext_iff`/`Matrix.ext`, `Fin.forall_fin_two`, `field_simp`, `ring`; `(p : ℚ_[p]) ≠ 0` from `Nat.cast_ne_zero.2 hp.out.ne_zero`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [CLEANUP-L2] Cleanup `PhD/LWX/AtkinLehnerLocal.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerLocal` and `lake exe runLinter PhD.LWX.AtkinLehnerLocal` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: tactic tails tailored per linter (no unused simp args, no dead `field_simp`/`ring`), `lake env lean` clean.

### [L7] `ℓQ_mul_ℓQinv`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem ℓQ_mul_ℓQinv (b c : ℚ_[p]) : ℓQ p b c * ℓQinv p b c = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`unfold`; `Matrix.mul_fin_two` (and `Matrix.one_fin_two` where the RHS is `1`); `Matrix.of` extensionality (`ext i j; fin_cases i <;> fin_cases j <;> simp`); `ring` (no division).

- **Mathlib/project lemmas needed**: `Matrix.det_fin_two_of`, `Matrix.mul_fin_two`, `Matrix.smul_of`, `Matrix.of_apply`, `Matrix.one_fin_two`, `Matrix.ext_iff`/`Matrix.ext`, `Fin.forall_fin_two`, `field_simp`, `ring`; `(p : ℚ_[p]) ≠ 0` from `Nat.cast_ne_zero.2 hp.out.ne_zero`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [L8] `ℓQinv_mul_ℓQ`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem ℓQinv_mul_ℓQ (b c : ℚ_[p]) : ℓQinv p b c * ℓQ p b c = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`unfold`; `Matrix.mul_fin_two` (and `Matrix.one_fin_two` where the RHS is `1`); `Matrix.of` extensionality (`ext i j; fin_cases i <;> fin_cases j <;> simp`); `ring`.

- **Mathlib/project lemmas needed**: `Matrix.det_fin_two_of`, `Matrix.mul_fin_two`, `Matrix.smul_of`, `Matrix.of_apply`, `Matrix.one_fin_two`, `Matrix.ext_iff`/`Matrix.ext`, `Fin.forall_fin_two`, `field_simp`, `ring`; `(p : ℚ_[p]) ≠ 0` from `Nat.cast_ne_zero.2 hp.out.ne_zero`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [L9] `tMat_mul_tMatInv`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem tMat_mul_tMatInv (a : ℚ_[p]) : tMat p a * tMatInv p a = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`unfold`; `Matrix.mul_fin_two` (and `Matrix.one_fin_two` where the RHS is `1`); `Matrix.of` extensionality (`ext i j; fin_cases i <;> fin_cases j <;> simp`); `field_simp`.

- **Mathlib/project lemmas needed**: `Matrix.det_fin_two_of`, `Matrix.mul_fin_two`, `Matrix.smul_of`, `Matrix.of_apply`, `Matrix.one_fin_two`, `Matrix.ext_iff`/`Matrix.ext`, `Fin.forall_fin_two`, `field_simp`, `ring`; `(p : ℚ_[p]) ≠ 0` from `Nat.cast_ne_zero.2 hp.out.ne_zero`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [CLEANUP-L3] Cleanup `PhD/LWX/AtkinLehnerLocal.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerLocal` and `lake exe runLinter PhD.LWX.AtkinLehnerLocal` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: tactic tails tailored per linter (no unused simp args, no dead `field_simp`/`ring`), `lake env lean` clean.

### [L10] `tMatInv_mul_tMat`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem tMatInv_mul_tMat (a : ℚ_[p]) : tMatInv p a * tMat p a = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`unfold`; `Matrix.mul_fin_two` (and `Matrix.one_fin_two` where the RHS is `1`); `Matrix.of` extensionality (`ext i j; fin_cases i <;> fin_cases j <;> simp`); `field_simp`.

- **Mathlib/project lemmas needed**: `Matrix.det_fin_two_of`, `Matrix.mul_fin_two`, `Matrix.smul_of`, `Matrix.of_apply`, `Matrix.one_fin_two`, `Matrix.ext_iff`/`Matrix.ext`, `Fin.forall_fin_two`, `field_simp`, `ring`; `(p : ℚ_[p]) ≠ 0` from `Nat.cast_ne_zero.2 hp.out.ne_zero`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [L11] `sQ_mul_tMat`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `s_b · t_a = t_{a+b}`. -/
theorem sQ_mul_tMat (a b : ℚ_[p]) : sQ p b * tMat p a = tMat p (a + b) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`unfold`; `Matrix.mul_fin_two` (and `Matrix.one_fin_two` where the RHS is `1`); `Matrix.of` extensionality (`ext i j; fin_cases i <;> fin_cases j <;> simp`); `ring`.

- **Mathlib/project lemmas needed**: `Matrix.det_fin_two_of`, `Matrix.mul_fin_two`, `Matrix.smul_of`, `Matrix.of_apply`, `Matrix.one_fin_two`, `Matrix.ext_iff`/`Matrix.ext`, `Fin.forall_fin_two`, `field_simp`, `ring`; `(p : ℚ_[p]) ≠ 0` from `Nat.cast_ne_zero.2 hp.out.ne_zero`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [L12] `tMatInv_zero_mul_sQ_neg`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `t₀⁻¹ · s_{−a} = t_a⁻¹`. -/
theorem tMatInv_zero_mul_sQ_neg (a : ℚ_[p]) : tMatInv p 0 * sQ p (-a) = tMatInv p a := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`unfold`; `Matrix.mul_fin_two` (and `Matrix.one_fin_two` where the RHS is `1`); `Matrix.of` extensionality (`ext i j; fin_cases i <;> fin_cases j <;> simp`); `neg_div`, `zero_div`, `ring`.

- **Mathlib/project lemmas needed**: `Matrix.det_fin_two_of`, `Matrix.mul_fin_two`, `Matrix.smul_of`, `Matrix.of_apply`, `Matrix.one_fin_two`, `Matrix.ext_iff`/`Matrix.ext`, `Fin.forall_fin_two`, `field_simp`, `ring`; `(p : ℚ_[p]) ≠ 0` from `Nat.cast_ne_zero.2 hp.out.ne_zero`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [CLEANUP-L4] Cleanup `PhD/LWX/AtkinLehnerLocal.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerLocal` and `lake exe runLinter PhD.LWX.AtkinLehnerLocal` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: tactic tails tailored per linter (no unused simp args, no dead `field_simp`/`ring`), `lake env lean` clean.

### [L13] `tMatInv_zero_mul_sQ_mul_tMat_zero`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `t₀⁻¹ · s_b · t₀ = (1, b/p; 0, 1)`: the translation in the disc-`0` coordinate. -/
theorem tMatInv_zero_mul_sQ_mul_tMat_zero (b : ℚ_[p]) :
    tMatInv p 0 * sQ p b * tMat p 0 = !![1, b / (p : ℚ_[p]); 0, 1] := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`unfold`; `Matrix.mul_fin_two` (and `Matrix.one_fin_two` where the RHS is `1`); `Matrix.of` extensionality (`ext i j; fin_cases i <;> fin_cases j <;> simp`); `field_simp`, `ring`.

- **Mathlib/project lemmas needed**: `Matrix.det_fin_two_of`, `Matrix.mul_fin_two`, `Matrix.smul_of`, `Matrix.of_apply`, `Matrix.one_fin_two`, `Matrix.ext_iff`/`Matrix.ext`, `Fin.forall_fin_two`, `field_simp`, `ring`; `(p : ℚ_[p]) ≠ 0` from `Nat.cast_ne_zero.2 hp.out.ne_zero`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [L14] `discConjMat_wQ`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `t₀⁻¹ wQ t₀ = (0 1; −p² 0)` is the level-`p²` Atkin–Lehner element of `AtkinLehner.lean`. -/
theorem discConjMat_wQ :
    !![(p : ℚ_[p])⁻¹, 0; 0, 1] * wQ p * !![(p : ℚ_[p]), 0; 0, 1] = atkinLehner p 2 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`unfold wQ atkinLehner`; `Matrix.mul_fin_two` twice; `field_simp`; `ring` (`(1/p)(0·p) = 0`, `(1/p)·p·1 = 1`, `−p·p = −p²`).

- **Mathlib/project lemmas needed**: `Matrix.det_fin_two_of`, `Matrix.mul_fin_two`, `Matrix.smul_of`, `Matrix.of_apply`, `Matrix.one_fin_two`, `Matrix.ext_iff`/`Matrix.ext`, `Fin.forall_fin_two`, `field_simp`, `ring`; `(p : ℚ_[p]) ≠ 0` from `Nat.cast_ne_zero.2 hp.out.ne_zero`. `atkinLehner` (AtkinLehner.lean:62).
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [L15] `wQ_mul_vQ_mul_wQinv`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The `U'_p`-representative: `wQ · vQ b · wQ⁻¹ = (1 −bp; 0 p)`. -/
theorem wQ_mul_vQ_mul_wQinv (b : ℚ_[p]) :
    wQ p * vQ p b * wQinv p = !![1, -(b * (p : ℚ_[p])); 0, (p : ℚ_[p])] := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`Matrix.mul_fin_two` twice; `field_simp`; `ring` (see `decomposition.md` L-b for the entry-by-entry check).

- **Mathlib/project lemmas needed**: `Matrix.det_fin_two_of`, `Matrix.mul_fin_two`, `Matrix.smul_of`, `Matrix.of_apply`, `Matrix.one_fin_two`, `Matrix.ext_iff`/`Matrix.ext`, `Fin.forall_fin_two`, `field_simp`, `ring`; `(p : ℚ_[p]) ≠ 0` from `Nat.cast_ne_zero.2 hp.out.ne_zero`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [CLEANUP-L5] Cleanup `PhD/LWX/AtkinLehnerLocal.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerLocal` and `lake exe runLinter PhD.LWX.AtkinLehnerLocal` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: tactic tails tailored per linter (no unused simp args, no dead `field_simp`/`ring`), `lake env lean` clean.

### [L16] `wQ_mul_mul_wQinv` [NEW DECL]
- **Status**: done
- **File**: insert after `wQ_mul_vQ_mul_wQinv` in `PhD/LWX/AtkinLehnerLocal.lean`
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem wQ_mul_mul_wQinv (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) :
    wQ p * g * wQinv p = !![g 1 1, -(g 1 0); -(g 0 1), g 0 0] := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
New helper (Part L): `theorem wQ_mul_mul_wQinv (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) : wQ p * g * wQinv p = !![g 1 1, -(g 1 0); -(g 0 1), g 0 0]`.  `Matrix.mul_fin_two` twice with `g = !![g 0 0, g 0 1; g 1 0, g 1 1]` (`Matrix.eta_fin_two`); `field_simp`; `ring`.

- **Mathlib/project lemmas needed**: `Matrix.eta_fin_two`, `Matrix.det_fin_two_of`, `Matrix.mul_fin_two`, `Matrix.smul_of`, `Matrix.of_apply`, `Matrix.one_fin_two`, `Matrix.ext_iff`/`Matrix.ext`, `Fin.forall_fin_two`, `field_simp`, `ring`; `(p : ℚ_[p]) ≠ 0` from `Nat.cast_ne_zero.2 hp.out.ne_zero`.
- **Sources**: `decomposition.md` W-f attack 3; W-b.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [L17] `wQinv_mul_mul_wQ` [NEW DECL]
- **Status**: done
- **File**: insert after `wQ_mul_mul_wQinv` in `PhD/LWX/AtkinLehnerLocal.lean`
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem wQinv_mul_mul_wQ (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) :
    wQinv p * g * wQ p = !![g 1 1, -(g 1 0); -(g 0 1), g 0 0] := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
New helper (Part L): `theorem wQinv_mul_mul_wQ (g) : wQinv p * g * wQ p = !![g 1 1, -(g 1 0); -(g 0 1), g 0 0]` — same proof.

- **Mathlib/project lemmas needed**: `Matrix.eta_fin_two`, `Matrix.det_fin_two_of`, `Matrix.mul_fin_two`, `Matrix.smul_of`, `Matrix.of_apply`, `Matrix.one_fin_two`, `Matrix.ext_iff`/`Matrix.ext`, `Fin.forall_fin_two`, `field_simp`, `ring`; `(p : ℚ_[p]) ≠ 0` from `Nat.cast_ne_zero.2 hp.out.ne_zero`.
- **Sources**: `decomposition.md` W-g attack 1.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [L18] `upAdjRep_mul_vQ`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The key factorisation**: `(1 −bp; 0 p) · vQ c = ℓQ b c · (p • sQ (−b))`. -/
theorem upAdjRep_mul_vQ (b c : ℚ_[p]) :
    !![1, -(b * (p : ℚ_[p])); 0, (p : ℚ_[p])] * vQ p c
      = ℓQ p b c * ((p : ℚ_[p]) • sQ p (-b)) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`Matrix.mul_fin_two`; RHS: `Matrix.smul_of`/`smul_eq_mul` turns `p • sQ (−b)` into `!![p, −bp; 0, p]`, then `Matrix.mul_fin_two`; `ring`.

- **Mathlib/project lemmas needed**: `Matrix.det_fin_two_of`, `Matrix.mul_fin_two`, `Matrix.smul_of`, `Matrix.of_apply`, `Matrix.one_fin_two`, `Matrix.ext_iff`/`Matrix.ext`, `Fin.forall_fin_two`, `field_simp`, `ring`; `(p : ℚ_[p]) ≠ 0` from `Nat.cast_ne_zero.2 hp.out.ne_zero`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [CLEANUP-L6] Cleanup `PhD/LWX/AtkinLehnerLocal.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerLocal` and `lake exe runLinter PhD.LWX.AtkinLehnerLocal` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: tactic tails tailored per linter (no unused simp args, no dead `field_simp`/`ring`), `lake env lean` clean.

### [L19] `wQ_mul_vQ_mul_wQinv_mul_vQ`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: L15, L18
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The factorisation with the Atkin–Lehner conjugate spelled out. -/
theorem wQ_mul_vQ_mul_wQinv_mul_vQ (b c : ℚ_[p]) :
    wQ p * vQ p b * wQinv p * vQ p c = ℓQ p b c * ((p : ℚ_[p]) • sQ p (-b)) := by
  sorry
```

- **Depends on (declarations)**: `wQ_mul_vQ_mul_wQinv`, `upAdjRep_mul_vQ`

**Proof sketch**:
`rw [wQ_mul_vQ_mul_wQinv, upAdjRep_mul_vQ]`.

- **Mathlib/project lemmas needed**: `wQ_mul_vQ_mul_wQinv`, `upAdjRep_mul_vQ`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [L20] `ℓQinv_mul_wQ_mul_vQ_mul_wQinv_mul_vQ`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: L19, L8
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The factorisation solved for the Iwahori element: `ℓ_{b,c}⁻¹ · w v_b w⁻¹ v_c = p • s_{−b}`. -/
theorem ℓQinv_mul_wQ_mul_vQ_mul_wQinv_mul_vQ (b c : ℚ_[p]) :
    ℓQinv p b c * (wQ p * vQ p b * wQinv p * vQ p c) = (p : ℚ_[p]) • sQ p (-b) := by
  sorry
```

- **Depends on (declarations)**: `wQ_mul_vQ_mul_wQinv_mul_vQ`, `ℓQinv_mul_ℓQ`

**Proof sketch**:
`rw [wQ_mul_vQ_mul_wQinv_mul_vQ, ← mul_assoc, ℓQinv_mul_ℓQ, one_mul]`.

- **Mathlib/project lemmas needed**: `wQ_mul_vQ_mul_wQinv_mul_vQ`, `ℓQinv_mul_ℓQ`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [L21] `vQ_mem_M1`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `vQ c ∈ M₁` for `c` integral. -/
theorem vQ_mem_M1 {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) : vQ p c ∈ M1 p := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`M1` carrier (IntegralModel.lean:226): `refine ⟨fun i j => ?_, ?_, ?_, ?_⟩`; entries: `‖p‖ = p⁻¹ ≤ 1`, `‖0‖`, `‖c p‖ ≤ 1·p⁻¹ ≤ 1`, `‖1‖`; `‖vQ 1 0‖ = ‖c p‖ ≤ p⁻¹`; `‖1‖ = 1`; `det = p ≠ 0` (`det_vQ`).

- **Mathlib/project lemmas needed**: `Padic.norm_p`, `norm_mul`, `norm_neg`, `norm_pow`, `norm_one`, `norm_zero`, `IsUltrametricDist.norm_add_le_max`/`padicNormE.nonarchimedean`, `inv_le_one_of_one_le₀`, `mul_le_one'`, `Fin.forall_fin_two`, `Matrix.of_apply`, `det_vQ`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [CLEANUP-L7] Cleanup `PhD/LWX/AtkinLehnerLocal.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerLocal` and `lake exe runLinter PhD.LWX.AtkinLehnerLocal` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: tactic tails tailored per linter (no unused simp args, no dead `field_simp`/`ring`), `lake env lean` clean.

### [L22] `norm_vQ_zero_zero`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `vQ c` has the `U_p`-shape `‖a‖ ≤ p⁻¹`. -/
theorem norm_vQ_zero_zero (c : ℚ_[p]) : ‖vQ p c 0 0‖ ≤ (p : ℝ)⁻¹ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`vQ p c 0 0 = p` (`Matrix.of_apply`/`simp [vQ]`); `Padic.norm_p`; `le_refl`.

- **Mathlib/project lemmas needed**: `Padic.norm_p`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [L23] `sQ_mem_Iw`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `sQ b ∈ Iw_p` for `b` integral. -/
theorem sQ_mem_Iw {b : ℚ_[p]} (hb : ‖b‖ ≤ 1) : sQ p b ∈ Iw p 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`mem_Iw_iff` (AtkinLehner.lean:167): entries `≤ 1` (`hb`), `‖sQ 1 0‖ = 0 ≤ p⁻¹`, `‖det‖ = ‖1‖ = 1` (`det_sQ`).

- **Mathlib/project lemmas needed**: `Padic.norm_p`, `norm_mul`, `norm_neg`, `norm_pow`, `norm_one`, `norm_zero`, `IsUltrametricDist.norm_add_le_max`/`padicNormE.nonarchimedean`, `inv_le_one_of_one_le₀`, `mul_le_one'`, `Fin.forall_fin_two`, `Matrix.of_apply`, `mem_Iw_iff`, `det_sQ`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [L24] `ℓQ_mem_Iw`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `ℓQ b c ∈ Iw_p` for `b, c` integral. -/
theorem ℓQ_mem_Iw {b c : ℚ_[p]} (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) : ℓQ p b c ∈ Iw p 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`mem_Iw_iff`: entries: `‖1 − bcp‖ ≤ max 1 ‖bcp‖ ≤ 1`, `‖b²cp‖ ≤ 1`, `‖cp‖ ≤ p⁻¹ ≤ 1`, `‖1 + bcp‖ ≤ 1` (ultrametric `norm_add_le_max`, `norm_sub_le_max`); `‖ℓQ 1 0‖ = ‖c p‖ ≤ p⁻¹`; `det_ℓQ`.

- **Mathlib/project lemmas needed**: `Padic.norm_p`, `norm_mul`, `norm_neg`, `norm_pow`, `norm_one`, `norm_zero`, `IsUltrametricDist.norm_add_le_max`/`padicNormE.nonarchimedean`, `inv_le_one_of_one_le₀`, `mul_le_one'`, `Fin.forall_fin_two`, `Matrix.of_apply`, `mem_Iw_iff`, `det_ℓQ`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [CLEANUP-L8] Cleanup `PhD/LWX/AtkinLehnerLocal.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerLocal` and `lake exe runLinter PhD.LWX.AtkinLehnerLocal` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: tactic tails tailored per linter (no unused simp args, no dead `field_simp`/`ring`), `lake env lean` clean.

### [L25] `ℓQinv_mem_Iw`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `ℓQinv b c ∈ Iw_p` for `b, c` integral. -/
theorem ℓQinv_mem_Iw {b c : ℚ_[p]} (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) : ℓQinv p b c ∈ Iw p 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As `ℓQ_mem_Iw` (entries `1 + bcp`, `b²cp`, `−cp`, `1 − bcp`; `norm_neg`; `det (ℓQinv) = 1` by `Matrix.det_fin_two_of; ring`).

- **Mathlib/project lemmas needed**: `Padic.norm_p`, `norm_mul`, `norm_neg`, `norm_pow`, `norm_one`, `norm_zero`, `IsUltrametricDist.norm_add_le_max`/`padicNormE.nonarchimedean`, `inv_le_one_of_one_le₀`, `mul_le_one'`, `Fin.forall_fin_two`, `Matrix.of_apply`, `mem_Iw_iff`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [L26] `wQ_conj_mem_Iw` [NEW DECL]
- **Status**: done
- **File**: insert after `ℓQinv_mem_Iw` in `PhD/LWX/AtkinLehnerLocal.lean`
- **Depends on**: L16
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem wQ_conj_mem_Iw {g : Matrix (Fin 2) (Fin 2) ℚ_[p]} (hg : g ∈ Iw p 1)
    (hb : ‖g 0 1‖ ≤ (p : ℝ)⁻¹) :
    (wQ p * g * wQinv p ∈ Iw p 1 ∧ ‖(wQ p * g * wQinv p) 0 1‖ ≤ (p : ℝ)⁻¹)
      ∧ (wQinv p * g * wQ p ∈ Iw p 1 ∧ ‖(wQinv p * g * wQ p) 0 1‖ ≤ (p : ℝ)⁻¹) := by
  sorry
```

- **Depends on (declarations)**: `wQ_mul_mul_wQinv`

**Proof sketch**:
New helper (Part L): `theorem wQ_conj_mem_Iw {g} (hg : g ∈ Iw p 1) (hb : ‖g 0 1‖ ≤ (p : ℝ)⁻¹) : wQ p * g * wQinv p ∈ Iw p 1 ∧ ‖(wQ p * g * wQinv p) 0 1‖ ≤ (p : ℝ)⁻¹` and the `wQinv * g * wQ` twin.  `wQ_mul_mul_wQinv`; `mem_Iw_iff`: entries of `g` bound the entries, the new `c`-entry is `−g 0 1` (`hb`), the new `b`-entry is `−g 1 0` (`hg.2.1`), `det` unchanged (`Matrix.det_fin_two_of`, `ring` — equals `g.det`).

- **Mathlib/project lemmas needed**: `wQ_mul_mul_wQinv`, `mem_Iw_iff`, `Matrix.det_fin_two_of`, `norm_neg`.
- **Sources**: `decomposition.md` W-f.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [L27] `Iw_one_le_M1`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `Iw_p ≤ M₁`: the Iwahori subgroup lies in the level monoid of the disc model. -/
theorem Iw_one_le_M1 : (Iw p 1 : Set (Matrix (Fin 2) (Fin 2) ℚ_[p])) ⊆ M1 p := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`intro g ⟨h1, h2, h3⟩`; `M1` carrier: entries `h1`; `‖g 1 0‖ ≤ p⁻¹` is `h2` (`pow_one`); `‖g 1 1‖ = 1`: mirror of `norm_apply_zero_zero_of_mem_Iw` (AtkinLehner.lean:171; `m = 1 ≠ 0`) — either prove `norm_apply_one_one_of_mem_Iw` the same way (`‖bc‖ < 1 = ‖det‖` forces `‖ad‖ = 1`, `padicNormE.add_eq_max_of_ne`) or reuse it via the transpose; `det ≠ 0` from `h3` (`norm_pos_iff`/`norm_ne_zero_iff`).

- **Mathlib/project lemmas needed**: `mem_Iw_iff`, `norm_apply_zero_zero_of_mem_Iw` (pattern), `padicNormE.add_eq_max_of_ne`, `Matrix.det_fin_two`, `norm_ne_zero_iff`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [CLEANUP-L9] Cleanup `PhD/LWX/AtkinLehnerLocal.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerLocal` and `lake exe runLinter PhD.LWX.AtkinLehnerLocal` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: tactic tails tailored per linter (no unused simp args, no dead `field_simp`/`ring`), `lake env lean` clean.

### [L28] `norm_det_fin_two_le_one` [NEW DECL]
- **Status**: done
- **File**: insert after `Iw_one_le_M1` in `PhD/LWX/AtkinLehnerLocal.lean`
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem norm_det_fin_two_le_one {g : Matrix (Fin 2) (Fin 2) ℚ_[p]} (hg : ∀ i j, ‖g i j‖ ≤ 1) :
    ‖g.det‖ ≤ 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
New helper (Part L): `theorem norm_det_fin_two_le_one {g : Matrix (Fin 2) (Fin 2) ℚ_[p]} (hg : ∀ i j, ‖g i j‖ ≤ 1) : ‖g.det‖ ≤ 1`.  `Matrix.det_fin_two`; `norm_sub_le_max` (ultrametric) / `padicNormE.nonarchimedean`; `norm_mul`, `mul_le_one'`.

- **Mathlib/project lemmas needed**: `Matrix.det_fin_two`, `padicNormE.nonarchimedean`, `norm_mul`, `mul_le_one'`.
- **Sources**: `decomposition.md` W-c.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [L29] `discImage_zero_of_norm_apply_zero_one_le`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **A matrix with `p ∣ b` fixes disc `0`** (`discImage 1 δ 0 = (b/d) mod p`). -/
theorem discImage_zero_of_norm_apply_zero_one_le (δ : M1 p)
    (hb : ‖(δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1‖ ≤ (p : ℝ)⁻¹) : discImage 1 δ 0 = 0 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `unfold discImage` (DiscModel.lean:168): `toZModPow 1 (mobiusFun (toLocalMat δ) 0)`; `mobiusFun δ 0 = (a·0 + b) * Ring.inverse (c·0 + d) = b * Ring.inverse d` (`UpMatrix.lean:65`, `mul_zero`, `zero_add`).
2. `toZModPow 1 x = 0 ↔ x ∈ ker = span {p^1}` (`PadicInt.ker_toZModPow`, `Ideal.mem_span_singleton`) `↔ ‖x‖ ≤ p⁻¹` (`PadicInt.norm_le_pow_iff_mem_span_pow` with `n = 1`, `pow_one`).
3. `‖b * inverse d‖ = ‖b‖ * ‖inverse d‖ = ‖b‖ ≤ p⁻¹` (`Ring.inverse` of a unit: `Ring.inverse_unit`, `PadicInt.norm_units`; `‖b‖ = ‖δ 0 1‖` via `M1.coe_toLocalMat_b`, `PadicInt.norm_def`, `hb`).

- **Mathlib/project lemmas needed**: `discImage`, `LocalMat.mobiusFun`, `PadicInt.ker_toZModPow`, `PadicInt.norm_le_pow_iff_mem_span_pow`, `Ring.inverse_unit`, `PadicInt.norm_units`, `M1.coe_toLocalMat_b`, `M1.coe_toLocalMat_d`.
- **Sources**: `decomposition.md` L-d.
- **Generality decision**: As stated (level `h = 1`; the `h`-general version is not needed).
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [L30] `discConjMat_eq_tMatInv_mul_mul_tMat`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The disc conjugate is `t_{a'}⁻¹ δ t_a`** — the entry-wise definition of `discConjMat`
read as a matrix product (`a' = discImage 1 δ a`). -/
theorem discConjMat_eq_tMatInv_mul_mul_tMat (δ : M1 p) (a : ZMod (p ^ 1)) :
    discConjMat 1 δ a
      = tMatInv p (((discImage 1 δ a).val : ℕ) : ℚ_[p]) * (δ : Matrix (Fin 2) (Fin 2) ℚ_[p])
          * tMat p ((a.val : ℕ) : ℚ_[p]) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`ext i j; fin_cases i <;> fin_cases j`; `simp only [discConjMat, tMat, tMatInv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, …]` (`discConjMat` entries, DiscModel.lean:172–180); `field_simp`; `ring`.  Entry check in `decomposition.md` L-d.

- **Mathlib/project lemmas needed**: `discConjMat`, `Matrix.mul_apply`, `Fin.sum_univ_two`, `field_simp`, `ring`.
- **Sources**: `decomposition.md` L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [CLEANUP-L10] Cleanup `PhD/LWX/AtkinLehnerLocal.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerLocal` and `lake exe runLinter PhD.LWX.AtkinLehnerLocal` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: tactic tails tailored per linter (no unused simp args, no dead `field_simp`/`ring`), `lake env lean` clean.

### [L31] `discConjMat_zero_of_discImage_zero`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: L30
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- At a matrix fixing disc `0`, the disc-`0` conjugate is `t₀⁻¹ δ t₀`. -/
theorem discConjMat_zero_of_discImage_zero (δ : M1 p) (hδ : discImage 1 δ 0 = 0) :
    discConjMat 1 δ 0 = tMatInv p 0 * (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) * tMat p 0 := by
  sorry
```

- **Depends on (declarations)**: `discConjMat_eq_tMatInv_mul_mul_tMat`

**Proof sketch**:
`rw [discConjMat_eq_tMatInv_mul_mul_tMat, hδ]`; `ZMod.val_zero`, `Nat.cast_zero`.

- **Mathlib/project lemmas needed**: `discConjMat_eq_tMatInv_mul_mul_tMat`, `ZMod.val_zero`.
- **Sources**: `decomposition.md` L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [L32] `conj_sQ_eq_tMat_mul_discConjMat` [NEW DECL]
- **Status**: done
- **File**: insert after `discConjMat_zero_of_discImage_zero` in `PhD/LWX/AtkinLehnerLocal.lean`
- **Depends on**: L30, L11, L12
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem conj_sQ_eq_tMat_mul_discConjMat (δ : M1 p) (a : ZMod (p ^ 1)) :
    sQ p (-(((discImage 1 δ a).val : ℕ) : ℚ_[p])) * (δ : Matrix (Fin 2) (Fin 2) ℚ_[p])
        * sQ p ((a.val : ℕ) : ℚ_[p])
      = tMat p 0 * discConjMat 1 δ a * tMatInv p 0 := by
  sorry
```

- **Depends on (declarations)**: `discConjMat_eq_tMatInv_mul_mul_tMat`, `sQ_mul_tMat`, `tMatInv_zero_mul_sQ_neg`

**Proof sketch**:
New helper (Part L, after `discConjMat_zero_of_discImage_zero`): `theorem conj_sQ_eq_tMat_mul_discConjMat (δ : M1 p) (a : ZMod (p ^ 1)) : sQ p (-(((discImage 1 δ a).val : ℕ) : ℚ_[p])) * δ * sQ p ((a.val : ℕ) : ℚ_[p]) = tMat p 0 * discConjMat 1 δ a * tMatInv p 0`.
`discConjMat_eq_tMatInv_mul_mul_tMat`; `tMat 0 * tMatInv a' = sQ (−a')` and `tMat a * tMatInv 0 = sQ a` (`Matrix.mul_fin_two`, `field_simp`, `ring`) — or `mul_assoc` + `tMat_mul_tMatInv`-style cancellations after inserting `tMatInv 0 * tMat 0 = 1`.

- **Mathlib/project lemmas needed**: `discConjMat_eq_tMatInv_mul_mul_tMat`, `tMat_mul_tMatInv`, `tMatInv_mul_tMat`, `Matrix.det_fin_two_of`, `Matrix.mul_fin_two`, `Matrix.smul_of`, `Matrix.of_apply`, `Matrix.one_fin_two`, `Matrix.ext_iff`/`Matrix.ext`, `Fin.forall_fin_two`, `field_simp`, `ring`; `(p : ℚ_[p]) ≠ 0` from `Nat.cast_ne_zero.2 hp.out.ne_zero`.
- **Sources**: `decomposition.md` W-f attack 1.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [L33] `discImage_vQ_zero`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: L29
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `vQ c` fixes disc `0`. -/
theorem discImage_vQ_zero {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) :
    discImage 1 (⟨vQ p c, vQ_mem_M1 hc⟩ : M1 p) 0 = 0 := by
  sorry
```

- **Depends on (declarations)**: `discImage_zero_of_norm_apply_zero_one_le`

**Proof sketch**:
`discImage_zero_of_norm_apply_zero_one_le`; the `(0,1)` entry of `vQ` is `0` (`norm_zero`, `inv_nonneg`).

- **Mathlib/project lemmas needed**: `discImage_zero_of_norm_apply_zero_one_le`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [CLEANUP-L11] Cleanup `PhD/LWX/AtkinLehnerLocal.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerLocal` and `lake exe runLinter PhD.LWX.AtkinLehnerLocal` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: tactic tails tailored per linter (no unused simp args, no dead `field_simp`/`ring`), `lake env lean` clean.

### [L34] `discImage_ℓQ_zero`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: L29
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `ℓQ b c` fixes disc `0` (its `b`-entry is divisible by `p`). -/
theorem discImage_ℓQ_zero {b c : ℚ_[p]} (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    discImage 1 (⟨ℓQ p b c, Iw_one_le_M1 (ℓQ_mem_Iw hb hc)⟩ : M1 p) 0 = 0 := by
  sorry
```

- **Depends on (declarations)**: `discImage_zero_of_norm_apply_zero_one_le`

**Proof sketch**:
`discImage_zero_of_norm_apply_zero_one_le`; `‖−(b²cp)‖ ≤ ‖b‖²‖c‖‖p‖ ≤ p⁻¹`.

- **Mathlib/project lemmas needed**: `discImage_zero_of_norm_apply_zero_one_le`, `Padic.norm_p`, `norm_mul`, `norm_neg`, `norm_pow`, `norm_one`, `norm_zero`, `IsUltrametricDist.norm_add_le_max`/`padicNormE.nonarchimedean`, `inv_le_one_of_one_le₀`, `mul_le_one'`, `Fin.forall_fin_two`, `Matrix.of_apply`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [L35] `discImage_ℓQinv_zero`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: L29
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `ℓQinv b c` fixes disc `0`. -/
theorem discImage_ℓQinv_zero {b c : ℚ_[p]} (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    discImage 1 (⟨ℓQinv p b c, Iw_one_le_M1 (ℓQinv_mem_Iw hb hc)⟩ : M1 p) 0 = 0 := by
  sorry
```

- **Depends on (declarations)**: `discImage_zero_of_norm_apply_zero_one_le`

**Proof sketch**:
As `discImage_ℓQ_zero` (entry `b²cp`).

- **Mathlib/project lemmas needed**: `discImage_zero_of_norm_apply_zero_one_le`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [L36] `discConj_ℓQ_zero_one_one`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The `d`-entry of the disc-`0` conjugate of `ℓQ b c` is `1 + bcp`. -/
theorem discConj_ℓQ_zero_one_one {b c : ℚ_[p]} (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    (discConj 1 (⟨ℓQ p b c, Iw_one_le_M1 (ℓQ_mem_Iw hb hc)⟩ : M1 p) 0 :
      Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 = 1 + b * c * (p : ℚ_[p]) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`coe_discConj`, `discConjMat_apply_one_one` (DiscModel.lean:200: `= δ 1 0 * a.val + δ 1 1`); `ZMod.val_zero`, `Nat.cast_zero`, `mul_zero`, `zero_add`; `ℓQ` entry `(1,1)` is `1 + bcp` (`Matrix.of_apply`).

- **Mathlib/project lemmas needed**: `coe_discConj`, `discConjMat_apply_one_one`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [CLEANUP-L12] Cleanup `PhD/LWX/AtkinLehnerLocal.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerLocal` and `lake exe runLinter PhD.LWX.AtkinLehnerLocal` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: tactic tails tailored per linter (no unused simp args, no dead `field_simp`/`ring`), `lake env lean` clean.

### [L37] `discConj_ℓQinv_zero_one_one`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The `d`-entry of the disc-`0` conjugate of `ℓQinv b c` is `1 − bcp`. -/
theorem discConj_ℓQinv_zero_one_one {b c : ℚ_[p]} (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    (discConj 1 (⟨ℓQinv p b c, Iw_one_le_M1 (ℓQinv_mem_Iw hb hc)⟩ : M1 p) 0 :
      Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 = 1 - b * c * (p : ℚ_[p]) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As `discConj_ℓQ_zero_one_one` (entry `1 − bcp`).

- **Mathlib/project lemmas needed**: `coe_discConj`, `discConjMat_apply_one_one`.
- **Sources**: [LWX] `lwx.txt:684–688` (`v_j`), `lwx.txt:606–610` (`M₁`), `lwx.txt:481–484` (`Iw`); `scratch` `upRep_mul_upAdjRep`, `obstruction_mul_lowerUni`; `decomposition.md` L-a…L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [L38] `discImage_sQ_zero`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The translation `sQ b` moves disc `0` to disc `b`, with trivial conjugate. -/
theorem discImage_sQ_zero (b : ℕ) :
    discImage 1 (⟨sQ p b, Iw_one_le_M1 (sQ_mem_Iw (by
      exact IsUltrametricDist.norm_natCast_le_one ℚ_[p] b))⟩ : M1 p) 0 = (b : ZMod (p ^ 1)) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `unfold discImage`; `mobiusFun (toLocalMat (sQ b)) 0 = (b : ℤ_p)`: `PadicInt.ext`/`Subtype.ext` after coercing to `ℚ_p`: `M1.coe_toLocalMat_a/b/c/d` give `a = 1, b = b, c = 0, d = 1`; `Ring.inverse 1 = 1` (`Ring.inverse_one`); `mul_zero`, `zero_add`, `mul_one`.
2. `toZModPow 1 (b : ℤ_p) = (b : ZMod (p^1))` (`map_natCast`).

- **Mathlib/project lemmas needed**: `discImage`, `LocalMat.mobiusFun`, `M1.coe_toLocalMat_*`, `Ring.inverse_one`, `map_natCast`, `PadicInt.ext`.
- **Sources**: `decomposition.md` L-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [L39] `discConj_sQ_zero`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: L30, L38
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem discConj_sQ_zero {b : ℕ} (hb : b < p) :
    discConj 1 (⟨sQ p b, Iw_one_le_M1 (sQ_mem_Iw (by
      exact IsUltrametricDist.norm_natCast_le_one ℚ_[p] b))⟩ : M1 p) 0 = 1 := by
  sorry
```

- **Depends on (declarations)**: `discConjMat_eq_tMatInv_mul_mul_tMat`, `discImage_sQ_zero`

**Proof sketch**:
`Subtype.ext`; `coe_discConj`; `discConjMat_eq_tMatInv_mul_mul_tMat`; `discImage_sQ_zero`; `((b : ZMod (p^1))).val = b` (`ZMod.val_natCast`, `pow_one`, `Nat.mod_eq_of_lt hb`); `ZMod.val_zero`, `Nat.cast_zero`; then `tMatInv b * sQ b * tMat 0 = 1`: `Matrix.mul_fin_two`, `Matrix.one_fin_two`, `field_simp`, `ring`.

- **Mathlib/project lemmas needed**: `discConjMat_eq_tMatInv_mul_mul_tMat`, `discImage_sQ_zero`, `ZMod.val_natCast`, `Nat.mod_eq_of_lt`, `Matrix.det_fin_two_of`, `Matrix.mul_fin_two`, `Matrix.smul_of`, `Matrix.of_apply`, `Matrix.one_fin_two`, `Matrix.ext_iff`/`Matrix.ext`, `Fin.forall_fin_two`, `field_simp`, `ring`; `(p : ℚ_[p]) ≠ 0` from `Nat.cast_ne_zero.2 hp.out.ne_zero`.
- **Sources**: `decomposition.md` L-d (the repaired statement).
- **Generality decision**: As stated (`hb : b < p` is necessary).
- **Progress**: 2026-09-10: DONE — proved as sketched; general-matrix conjugations need `simp only [Matrix.mul_apply, Fin.sum_univ_two]` *before* the literal `simp` (otherwise simp folds rows into `vecMul`).

### [CLEANUP-L13] Cleanup `PhD/LWX/AtkinLehnerLocal.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerLocal` and `lake exe runLinter PhD.LWX.AtkinLehnerLocal` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: tactic tails tailored per linter (no unused simp args, no dead `field_simp`/`ring`), `lake env lean` clean.

### [CLEANUP-L-FINAL] Final cleanup `PhD/LWX/AtkinLehnerLocal.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerLocal.lean
- **Depends on**: every proof ticket of Part L
- **Parallel**: no
- **Type**: cleanup

Whole-file `/cleanup`: sorry-free check (`grep -c sorry` = 0), `#print axioms` on the file's
headline declarations (standard axioms only), `lake exe runLinter PhD.LWX.AtkinLehnerLocal` clean, module
docstring updated to describe what is proved (drop "skeleton"/"planned" wording), relocations
named in `tickets.md` performed with one rebuild.
- **Progress**: 2026-09-10: DONE — inline cleanup: tactic tails tailored per linter (no unused simp args, no dead `field_simp`/`ring`), `lake env lean` clean.


## Part W — `PhD/LWX/AtkinLehnerMap.lean`: the data, the classical disc forms and the Atkin–Lehner map

### [W1] `pGL`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: definition

**Statement** (verbatim from the skeleton; protected):
```lean
variable (p) in
/-- The central element `p·1` as an element of `GL₂(ℚ_p)`. -/
def pGL : GL (Fin 2) ℚ_[p] :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((p : ℚ_[p]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p])) (by
    sorry)
```

- **Depends on (declarations)**: —

**Proof sketch**:
The `sorry` is `det (p • 1) ≠ 0`: `Matrix.det_smul`, `Matrix.det_one`, `Fintype.card_fin`, `mul_one`, `pow_ne_zero`, `Nat.cast_ne_zero.2 hp.out.ne_zero`.

- **Mathlib/project lemmas needed**: `Matrix.det_smul`, `Matrix.det_one`, `pow_ne_zero`.
- **Sources**: [LWX] `lwx.txt:671–682` (§2.4), `lwx.txt:1783–1785` (the twist), `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`); `decomposition.md` W-a…W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W2] `coe_wGL_inv`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
@[simp] theorem coe_wGL_inv : ((wGL p)⁻¹ : GL (Fin 2) ℚ_[p]) = (wQinv p : Matrix _ _ _) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`Matrix.coe_units_inv` then `Matrix.inv_eq_right_inv (wQ_mul_wQinv)` (or `Units.inv_eq_of_mul_eq_one_right` at the `GL` level with `Units.ext`).

- **Mathlib/project lemmas needed**: `Units.ext`, `Matrix.GeneralLinearGroup.coe_mul`/`Units.val_mul`, `Matrix.coe_units_inv`, `Matrix.inv_eq_right_inv`, `coe_vGL`/`coe_sGL`/`coe_wGL`/`coe_ℓGL` (`rfl`), `wQ_mul_wQinv`.
- **Sources**: [LWX] `lwx.txt:671–682` (§2.4), `lwx.txt:1783–1785` (the twist), `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`); `decomposition.md` W-a…W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W3] `coe_ℓGL_inv`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
@[simp] theorem coe_ℓGL_inv (b c : ℚ_[p]) :
    ((ℓGL p b c)⁻¹ : GL (Fin 2) ℚ_[p]) = (ℓQinv p b c : Matrix _ _ _) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As `coe_wGL_inv` with `ℓQ_mul_ℓQinv`.

- **Mathlib/project lemmas needed**: `Units.ext`, `Matrix.GeneralLinearGroup.coe_mul`/`Units.val_mul`, `Matrix.coe_units_inv`, `Matrix.inv_eq_right_inv`, `coe_vGL`/`coe_sGL`/`coe_wGL`/`coe_ℓGL` (`rfl`), `ℓQ_mul_ℓQinv`.
- **Sources**: [LWX] `lwx.txt:671–682` (§2.4), `lwx.txt:1783–1785` (the twist), `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`); `decomposition.md` W-a…W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [CLEANUP-W1] Cleanup `PhD/LWX/AtkinLehnerMap.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMap` and `lake exe runLinter PhD.LWX.AtkinLehnerMap` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: unused-section-variable `omit`s added per linter, dead tactics removed; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W4] `sGL_zero`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
@[simp] theorem sGL_zero : sGL p 0 = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`Units.ext`; `coe_sGL`; `sQ 0 = 1` (`Matrix.one_fin_two`, `Matrix.of` ext).

- **Mathlib/project lemmas needed**: `Units.ext`, `Matrix.GeneralLinearGroup.coe_mul`/`Units.val_mul`, `Matrix.coe_units_inv`, `Matrix.inv_eq_right_inv`, `coe_vGL`/`coe_sGL`/`coe_wGL`/`coe_ℓGL` (`rfl`)
- **Sources**: [LWX] `lwx.txt:671–682` (§2.4), `lwx.txt:1783–1785` (the twist), `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`); `decomposition.md` W-a…W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W5] `sGL_mul`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem sGL_mul (a b : ℚ_[p]) : sGL p a * sGL p b = sGL p (a + b) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`Units.ext`; `Units.val_mul`, `coe_sGL`; `sQ a * sQ b = sQ (a + b)` (`Matrix.mul_fin_two`; `ring`).

- **Mathlib/project lemmas needed**: `Units.ext`, `Matrix.GeneralLinearGroup.coe_mul`/`Units.val_mul`, `Matrix.coe_units_inv`, `Matrix.inv_eq_right_inv`, `coe_vGL`/`coe_sGL`/`coe_wGL`/`coe_ℓGL` (`rfl`)
- **Sources**: [LWX] `lwx.txt:671–682` (§2.4), `lwx.txt:1783–1785` (the twist), `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`); `decomposition.md` W-a…W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W6] `sGL_inv`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem sGL_inv (b : ℚ_[p]) : (sGL p b)⁻¹ = sGL p (-b) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`Units.ext`; `Matrix.coe_units_inv`; `Matrix.inv_eq_right_inv`: `sQ b * sQ (−b) = 1` (`Matrix.mul_fin_two`, `Matrix.one_fin_two`, `ring`).

- **Mathlib/project lemmas needed**: `Units.ext`, `Matrix.GeneralLinearGroup.coe_mul`/`Units.val_mul`, `Matrix.coe_units_inv`, `Matrix.inv_eq_right_inv`, `coe_vGL`/`coe_sGL`/`coe_wGL`/`coe_ℓGL` (`rfl`)
- **Sources**: [LWX] `lwx.txt:671–682` (§2.4), `lwx.txt:1783–1785` (the twist), `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`); `decomposition.md` W-a…W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [CLEANUP-W2] Cleanup `PhD/LWX/AtkinLehnerMap.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMap` and `lake exe runLinter PhD.LWX.AtkinLehnerMap` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: unused-section-variable `omit`s added per linter, dead tactics removed; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W7] `wGL_mul_vGL_mul_wGL_inv_mul_vGL`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: W2
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The key factorisation in `GL₂(ℚ_p)`**: `w v_b w⁻¹ v_c = ℓ_{b,c} · (p·1) · s_{−b}`
(`wQ_mul_vQ_mul_wQinv_mul_vQ`, `Units.ext`). -/
theorem wGL_mul_vGL_mul_wGL_inv_mul_vGL (b c : ℚ_[p]) :
    wGL p * vGL p b * (wGL p)⁻¹ * vGL p c = ℓGL p b c * (pGL p * sGL p (-b)) := by
  sorry
```

- **Depends on (declarations)**: `coe_wGL_inv`

**Proof sketch**:
`Units.ext`; `Units.val_mul`, `coe_wGL_inv`, `coe_*`; `wQ_mul_vQ_mul_wQinv_mul_vQ`; RHS: `(pGL p : Matrix) = p • 1` (`rfl`), `smul_mul_assoc`, `one_mul`.

- **Mathlib/project lemmas needed**: `Units.ext`, `Matrix.GeneralLinearGroup.coe_mul`/`Units.val_mul`, `Matrix.coe_units_inv`, `Matrix.inv_eq_right_inv`, `coe_vGL`/`coe_sGL`/`coe_wGL`/`coe_ℓGL` (`rfl`), `wQ_mul_vQ_mul_wQinv_mul_vQ`, `smul_mul_assoc`.
- **Sources**: [LWX] `lwx.txt:671–682` (§2.4), `lwx.txt:1783–1785` (the twist), `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`); `decomposition.md` W-a…W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W8] `atkinLehnerK_mul_atkinLehnerKinv`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem atkinLehnerK_mul_atkinLehnerKinv (ψ : ℚ_[p] →+* K) :
    atkinLehnerK ψ * atkinLehnerKinv ψ = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`unfold atkinLehnerK atkinLehnerKinv atkinLehner`; `RingHom.mapMatrix_apply`, `Matrix.map` of `!![…]` (`ext i j; fin_cases i <;> fin_cases j <;> simp`), `map_neg`, `map_pow`, `map_zero`, `map_one`; `Matrix.mul_fin_two`, `Matrix.one_fin_two`; `field_simp` (`ψ p ≠ 0`: `map_ne_zero`/`(map_eq_zero ψ).not.2 (Nat.cast_ne_zero.2 hp.out.ne_zero)`); `ring`.

- **Mathlib/project lemmas needed**: `RingHom.mapMatrix_apply`, `Matrix.map_apply`, `map_eq_zero`, `Matrix.mul_fin_two`.
- **Sources**: [LWX] `lwx.txt:671–682` (§2.4), `lwx.txt:1783–1785` (the twist), `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`); `decomposition.md` W-a…W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W9] `atkinLehnerKinv_mul_atkinLehnerK`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem atkinLehnerKinv_mul_atkinLehnerK (ψ : ℚ_[p] →+* K) :
    atkinLehnerKinv ψ * atkinLehnerK ψ = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As `atkinLehnerK_mul_atkinLehnerKinv`.

- **Mathlib/project lemmas needed**: same
- **Sources**: [LWX] `lwx.txt:671–682` (§2.4), `lwx.txt:1783–1785` (the twist), `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`); `decomposition.md` W-a…W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [CLEANUP-W3] Cleanup `PhD/LWX/AtkinLehnerMap.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMap` and `lake exe runLinter PhD.LWX.AtkinLehnerMap` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: unused-section-variable `omit`s added per linter, dead tactics removed; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W10] `theta_mem_Iw`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: L28
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `θ(u) ∈ Iw_p` for `u ∈ U`: `θ u` and `θ u⁻¹` are both in `M₁`, so `‖det θ u‖ = 1`. -/
theorem theta_mem_Iw (u : U) : θG u ∈ Iw p 1 := by
  sorry
```

- **Depends on (declarations)**: `norm_det_fin_two_le_one`

**Proof sketch**:
`mem_Iw_iff`: `hU u.2 : θG u ∈ M1` gives entries `≤ 1` and `‖c‖ ≤ p⁻¹`; for `‖det‖ = 1`: `hU u⁻¹.2` with `map_inv` gives `θG u⁻¹ = (θG u)⁻¹`… avoid matrix inverses: `θG u * θG u⁻¹ = θG (u * u⁻¹) = 1` (`← map_mul`, `mul_inv_cancel`, `map_one`), so `det (θG u) * det (θG u⁻¹) = 1` (`Matrix.det_mul`, `Matrix.det_one`); both factors have norm `≤ 1` (`norm_det_fin_two_le_one`), product of norms `= 1` (`norm_mul`, `norm_one`), hence each `= 1` (`le_antisymm`, `mul_le_one'`… : from `a b = 1`, `a ≤ 1`, `b ≤ 1` derive `a = 1` via `one_le_of_le_mul_right`-style or `nlinarith`).

- **Mathlib/project lemmas needed**: `mem_Iw_iff`, `norm_det_fin_two_le_one`, `Matrix.det_mul`, `Matrix.det_one`, `map_mul`, `map_one`, `norm_mul`, `nlinarith`.
- **Sources**: `decomposition.md` W-c.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — needed `include hU in` (the elaborated statement had silently dropped the section hypothesis, making it false); logged in `b2_log.jsonl` as a repaired-in-place entry.

### [W11] `theta_ιp_pGL`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The central element `p` (at `p`) acts trivially on the level: `θ(ιp p) = p • 1`. -/
theorem theta_ιp_pGL : θG (D.ιp (pGL p)) = (p : ℚ_[p]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`D.theta_ιp (pGL p)`; `(pGL p : Matrix) = p • 1` is `rfl`.

- **Mathlib/project lemmas needed**: `AtkinLehnerData.theta_ιp`.
- **Sources**: [LWX] `lwx.txt:671–682` (§2.4), `lwx.txt:1783–1785` (the twist), `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`); `decomposition.md` W-a…W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W12] `discShift_mem_U`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem discShift_mem_U (u : U) (a : ZMod (p ^ 1)) : discShift θG ψ U hU D u a ∈ U := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`unfold discShift`; `mul_mem (mul_mem (D.ιp_mem_U _ (sQ_mem_Iw (by rw [norm_neg]; exact IsUltrametricDist.norm_natCast_le_one _ _))) u.2) (D.ιp_mem_U _ (sQ_mem_Iw (IsUltrametricDist.norm_natCast_le_one _ _)))`.

- **Mathlib/project lemmas needed**: `AtkinLehnerData.ιp_mem_U`, `sQ_mem_Iw`, `IsUltrametricDist.norm_natCast_le_one`, `norm_neg`.
- **Sources**: [LWX] `lwx.txt:671–682` (§2.4), `lwx.txt:1783–1785` (the twist), `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`); `decomposition.md` W-a…W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [CLEANUP-W4] Cleanup `PhD/LWX/AtkinLehnerMap.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMap` and `lake exe runLinter PhD.LWX.AtkinLehnerMap` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: unused-section-variable `omit`s added per linter, dead tactics removed; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W13] `theta_discShift`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem theta_discShift (u : U) (a : ZMod (p ^ 1)) :
    θG (discShift θG ψ U hU D u a)
      = sQ p (-(((discImage 1 ⟨θG u, hU u.2⟩ a).val : ℕ) : ℚ_[p])) * θG u
        * sQ p ((a.val : ℕ) : ℚ_[p]) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`unfold discShift`; `map_mul`, `D.theta_ιp`, `coe_sGL`.

- **Mathlib/project lemmas needed**: `AtkinLehnerData.theta_ιp`, `coe_sGL`, `map_mul`.
- **Sources**: [LWX] `lwx.txt:671–682` (§2.4), `lwx.txt:1783–1785` (the twist), `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`); `decomposition.md` W-a…W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W14] `mul_ιp_sGL_eq`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: W5, W4
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `u s_a = s_{a'} u'`. -/
theorem mul_ιp_sGL_eq (u : U) (a : ZMod (p ^ 1)) :
    (u : G) * D.ιp (sGL p ((a.val : ℕ) : ℚ_[p]))
      = D.ιp (sGL p (((discImage 1 ⟨θG u, hU u.2⟩ a).val : ℕ) : ℚ_[p]))
        * discShift θG ψ U hU D u a := by
  sorry
```

- **Depends on (declarations)**: `sGL_mul`, `sGL_zero`

**Proof sketch**:
`unfold discShift`; `← mul_assoc`; `D.ιp (sGL a') * D.ιp (sGL (−a')) = D.ιp (sGL (a' + −a')) = D.ιp (sGL 0) = 1` (`← map_mul`, `sGL_mul`, `add_neg_cancel`, `sGL_zero`, `map_one`); `one_mul`.

- **Mathlib/project lemmas needed**: `sGL_mul`, `sGL_zero`, `map_mul`, `map_one`.
- **Sources**: [LWX] `lwx.txt:671–682` (§2.4), `lwx.txt:1783–1785` (the twist), `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`); `decomposition.md` W-a…W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W15] `norm_theta_discShift_zero_one_le`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: W13, L32
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem norm_theta_discShift_zero_one_le (u : U) (a : ZMod (p ^ 1)) :
    ‖(θG (discShift θG ψ U hU D u a)) 0 1‖ ≤ (p : ℝ)⁻¹ := by
  sorry
```

- **Depends on (declarations)**: `theta_discShift`, `conj_sQ_eq_tMat_mul_discConjMat`

**Proof sketch**:
`theta_discShift`; `conj_sQ_eq_tMat_mul_discConjMat`; the `(0,1)` entry of `tMat 0 * M * tMatInv 0` is `p * M 0 1` (`Matrix.mul_fin_two` with `M = !![…]` via `Matrix.eta_fin_two`, `field_simp`); `‖p * M 0 1‖ = p⁻¹ * ‖M 0 1‖ ≤ p⁻¹` since `discConjMat_mem_Mh` (DiscModel.lean, `mem_Mh_iff`: entries `≤ 1`).

- **Mathlib/project lemmas needed**: `theta_discShift`, `conj_sQ_eq_tMat_mul_discConjMat`, `discConjMat_mem_Mh`, `mem_Mh_iff`, `Matrix.eta_fin_two`, `Padic.norm_p`.
- **Sources**: `decomposition.md` W-f attack 1.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [CLEANUP-W5] Cleanup `PhD/LWX/AtkinLehnerMap.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMap` and `lake exe runLinter PhD.LWX.AtkinLehnerMap` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: unused-section-variable `omit`s added per linter, dead tactics removed; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W16] `discImage_discShift_zero`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: W15
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem discImage_discShift_zero (u : U) (a : ZMod (p ^ 1)) :
    discImage 1 (⟨θG (discShift θG ψ U hU D u a), hU (discShift_mem_U θG ψ U hU D u a)⟩ : M1 p) 0
      = 0 := by
  sorry
```

- **Depends on (declarations)**: `norm_theta_discShift_zero_one_le`

**Proof sketch**:
`discImage_zero_of_norm_apply_zero_one_le _ (norm_theta_discShift_zero_one_le …)`.

- **Mathlib/project lemmas needed**: `discImage_zero_of_norm_apply_zero_one_le`.
- **Sources**: [LWX] `lwx.txt:671–682` (§2.4), `lwx.txt:1783–1785` (the twist), `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`); `decomposition.md` W-a…W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W17] `discConjMat_discShift_zero`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: W16, W13, L32
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The disc-`0` conjugate of `u'` is the disc-`a` conjugate of `θ u`. -/
theorem discConjMat_discShift_zero (u : U) (a : ZMod (p ^ 1)) :
    discConjMat 1
        (⟨θG (discShift θG ψ U hU D u a), hU (discShift_mem_U θG ψ U hU D u a)⟩ : M1 p) 0
      = discConjMat 1 (⟨θG u, hU u.2⟩ : M1 p) a := by
  sorry
```

- **Depends on (declarations)**: `discImage_discShift_zero`, `theta_discShift`, `conj_sQ_eq_tMat_mul_discConjMat`

**Proof sketch**:
`discConjMat_zero_of_discImage_zero _ (discImage_discShift_zero …)`; `theta_discShift`; `conj_sQ_eq_tMat_mul_discConjMat`; `tMatInv 0 * (tMat 0 * M * tMatInv 0) * tMat 0 = M` (`mul_assoc`, `tMatInv_mul_tMat`, `one_mul`, `mul_one`).

- **Mathlib/project lemmas needed**: `discConjMat_zero_of_discImage_zero`, `theta_discShift`, `conj_sQ_eq_tMat_mul_discConjMat`, `tMatInv_mul_tMat`.
- **Sources**: `decomposition.md` W-f attack 1.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W18] `atkinLehnerK_eq`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `w₂ = t₀⁻¹ w t₀` in `K`. -/
theorem atkinLehnerK_eq : atkinLehnerK ψ = RingHom.mapMatrix ψ (tMatInv p 0 * wQ p * tMat p 0) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`unfold atkinLehnerK`; `← discConjMat_wQ` (Part L) — the matrix inside is `!![p⁻¹,0;0,1] * wQ * !![p,0;0,1]`, which is `tMatInv 0 * wQ * tMat 0` after `tMatInv`/`tMat` at `0` are unfolded (`neg_zero`, `zero_div`); `rfl`/`congr`.

- **Mathlib/project lemmas needed**: `discConjMat_wQ`, `tMat`, `tMatInv`.
- **Sources**: `decomposition.md` I-f.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [CLEANUP-W6] Cleanup `PhD/LWX/AtkinLehnerMap.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMap` and `lake exe runLinter PhD.LWX.AtkinLehnerMap` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: unused-section-variable `omit`s added per linter, dead tactics removed; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W19] `atkinLehnerKinv_eq`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `w₂⁻¹ = t₀⁻¹ w⁻¹ t₀` in `K`. -/
theorem atkinLehnerKinv_eq :
    atkinLehnerKinv ψ = RingHom.mapMatrix ψ (tMatInv p 0 * wQinv p * tMat p 0) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`unfold atkinLehnerKinv`; compute `tMatInv 0 * wQinv * tMat 0 = !![0, −p⁻²; 1, 0]` (`Matrix.mul_fin_two`, `field_simp`, `ring`), then `RingHom.mapMatrix_apply` + `Matrix.map` of `!![…]` (`map_neg`, `map_inv₀`, `map_pow`, `map_one`, `map_zero`).

- **Mathlib/project lemmas needed**: `Matrix.mul_fin_two`, `RingHom.mapMatrix_apply`, `map_inv₀`.
- **Sources**: `decomposition.md` I-f.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W20] `cSpace_ext_blockProj`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- Two block functions agree iff all their blocks do. -/
theorem cSpace_ext_blockProj {f g : c(ZMod (p ^ 1) × ℕ, K)}
    (h : ∀ a, cSpace.blockProj a f = cSpace.blockProj a g) : f = g := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`DFunLike.ext _ _ fun ⟨a, j⟩ => ?_`; `← cSpace.blockProj_apply a f j` (BlockOp.lean:590: `blockProj b f i = f (b, i)`) both sides; `h a ▸ rfl` / `congrArg (· j) (h a)`.

- **Mathlib/project lemmas needed**: `cSpace.blockProj_apply`, `DFunLike.ext`.
- **Sources**: `decomposition.md` W-f.
- **Generality decision**: General `σ × I` would be nicer (`Pr.lean:176` has a private one); keep the file's `ZMod (p^1) × ℕ` unless cleanup relocates it to `BlockOp.lean` as a public lemma.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W21] `nebK_one`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `nebK 1 = 1` (from the conductor hypothesis). -/
theorem nebK_one (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 → nebK (ψ x) = 1) :
    nebK (ψ 1) = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`hcond 1 (by rw [sub_self, norm_zero]; positivity)`.

- **Mathlib/project lemmas needed**: `sub_self`, `norm_zero`.
- **Sources**: [LWX] `lwx.txt:671–682` (§2.4), `lwx.txt:1783–1785` (the twist), `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`); `decomposition.md` W-a…W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [CLEANUP-W7] Cleanup `PhD/LWX/AtkinLehnerMap.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMap` and `lake exe runLinter PhD.LWX.AtkinLehnerMap` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: unused-section-variable `omit`s added per linter, dead tactics removed; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W22] `nebK_mul_nebK_eq_nebK_det`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **`nebK(a)·nebK(d) = nebK(det)`** on the disc-`0` stabiliser of `Iw_p` (`ad = det + bc` with
`p ∣ b`, `p ∣ c`, so `ad/det ≡ 1 (mod p²)`). -/
theorem nebK_mul_nebK_eq_nebK_det
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 → nebK (ψ x) = 1)
    {g : Matrix (Fin 2) (Fin 2) ℚ_[p]} (hg : g ∈ Iw p 1) (hb : ‖g 0 1‖ ≤ (p : ℝ)⁻¹) :
    nebK (ψ (g 0 0)) * nebK (ψ (g 1 1)) = nebK (ψ g.det) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `g.det = g 0 0 * g 1 1 − g 0 1 * g 1 0` (`Matrix.det_fin_two`); `hdet : g.det ≠ 0` (`‖det‖ = 1`); `g 0 0 * g 1 1 = g.det * (1 + g 0 1 * g 1 0 / g.det)` (`field_simp; ring`).
2. `‖g 0 0‖ = 1` (`norm_apply_zero_zero_of_mem_Iw one_ne_zero hg`), `‖g 1 1‖ = 1` (the `(1,1)` twin from `Iw_one_le_M1`), `‖g.det‖ = 1` (`hg.2.2`), `‖1 + g 0 1 g 1 0 / det‖ = 1` (ultrametric, `‖g 0 1 g 1 0 / det‖ ≤ p⁻² < 1`).
3. `hmul` on `g 0 0 * g 1 1`; `hmul` on `g.det * (1 + …)`; `hcond (1 + …)` with `‖(1 + x) − 1‖ = ‖x‖ ≤ p⁻¹ · p⁻¹` (`hb`, `hg.2.1` with `pow_one`, `norm_div`, `norm_mul`); `mul_one`; `congrArg nebK (map_mul …)`.

- **Mathlib/project lemmas needed**: `Matrix.det_fin_two`, `norm_apply_zero_zero_of_mem_Iw`, `Iw_one_le_M1`, `mem_Iw_iff`, `norm_div`, `norm_mul`, `field_simp`.
- **Sources**: `AtkinLehner.lean:113` (`ad = det + bc`); `decomposition.md` W-f.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W23] `nebK_one_sub_eq_inv`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `nebK(1 − x) = nebK(1 + x)⁻¹` for `‖x‖ ≤ p⁻¹` (`(1−x)(1+x) ≡ 1 (mod p²)`). -/
theorem nebK_one_sub_eq_inv
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 → nebK (ψ x) = 1)
    {x : ℚ_[p]} (hx : ‖x‖ ≤ (p : ℝ)⁻¹) :
    nebK (ψ (1 - x)) = (nebK (ψ (1 + x)))⁻¹ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`(1 − x) * (1 + x) = 1 − x^2`; `hmul (1−x) (1+x)` (norms `= 1`: ultrametric `‖1 ± x‖ = 1` from `‖x‖ < 1`, `padicNormE.add_eq_max_of_ne`); `hcond (1 − x^2)` (`‖(1 − x²) − 1‖ = ‖x‖² ≤ p⁻²`, `norm_pow`, `pow_le_pow_left`); so `nebK (ψ (1−x)) * nebK (ψ (1+x)) = 1`; `eq_inv_of_mul_eq_one_left`.

- **Mathlib/project lemmas needed**: `padicNormE.add_eq_max_of_ne`, `norm_pow`, `pow_le_pow_left₀`, `eq_inv_of_mul_eq_one_left`.
- **Sources**: `decomposition.md` I-f.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — `hne` unused (slack), renamed `_hne` per the `_hx` convention.

### [W24] `locPolyForms`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: definition

**Statement** (verbatim from the skeleton; protected):
```lean
variable (p K) in
/-- The automorphic functions whose every value is locally polynomial of degree `≤ k`. -/
def locPolyForms : Submodule K (AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)) where
  carrier := {φ | ∀ x, φ x ∈ locPolyDegSubmodule p K 1 k}
  add_mem' := by sorry
  zero_mem' := by sorry
  smul_mem' := by sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
The three closure obligations: for each `x`, `(φ + φ') x = φ x + φ' x` and `(r • φ) x = r • φ x` are `rfl` (`AutomorphicFunction` add/smul are pointwise — check the instance in `QMF/AutomorphicFunction.lean`), then `add_mem`, `zero_mem`, `smul_mem` of `locPolyDegSubmodule p K 1 k` (Theta.lean:140).

- **Mathlib/project lemmas needed**: `Submodule.add_mem`, `Submodule.zero_mem`, `Submodule.smul_mem`, `locPolyDegSubmodule`.
- **Sources**: [LWX] `lwx.txt:655–662`.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [CLEANUP-W8] Cleanup `PhD/LWX/AtkinLehnerMap.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMap` and `lake exe runLinter PhD.LWX.AtkinLehnerMap` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: unused-section-variable `omit`s added per linter, dead tactics removed; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W25] `discHeckeOperator_mem_classicalDiscForms`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `U_p` preserves the classical disc forms at a classical-shape weight
(`discSlash_mem_locPolyDegSubmodule_of_shape` at every representative). -/
theorem discHeckeOperator_mem_classicalDiscForms {u : K → K}
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    {η : G} (hη : η ∈ levelM1 (p := p) θG)
    (hfin : (((Quotient.mk'' : G → RightCosets U) '' (({η} : Set G) * (U : Set G))) :
      Set (RightCosets U)).Finite)
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ) :
    ((discHeckeOperator θG 1 ψ κ U hU hη hfin ⟨φ, hφ.1⟩ : DiscForms (Γ := Γ) θG 1 ψ κ U hU) :
        AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)) ∈ ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `refine ⟨(discHeckeOperator … ⟨φ, hφ.1⟩).2, fun x => ?_⟩`.
2. The value at `x`: `discHeckeOperator` is `heckeOperatorSlash K hU hU hη hfin` under `discLevelSlashAction` (DiscForms.lean:179); `heckeOperatorSlash_apply` (HeckeMonoid.lean; `= ∑ᶠ c, (φ ∣ₛ ⟨rep c, _⟩)` — read the exact form) with `finsum_eq_sum_of_fintype` (`hfin.fintype`), then evaluate at `x`: `_root_.sum_apply`/`AutomorphicFunction` sum-apply, `AutomorphicFunction.slash_apply` (`(φ ∣ₛ δ) x = φ (x δ⁻¹) ∣ₛ δ`), and the coefficient slash is `discSlash 1 ψ κ ⟨θ δ, _⟩` (`RightSlashAction.comap`, `levelM1ToM1`: `rfl`/`show`).
3. `Submodule.sum_mem`; each term: `discSlash_mem_locPolyDegSubmodule_of_shape 1 ψ κ δ (hA := fun a => hκ (discConjK 1 δ a ψ)) (hφ.2 _)` (Touching.lean:244; `hκ` at every `g ∈ M1Kh` specialises to every disc conjugate; its `u a` is `nebK`-free here: `u (discConjK … 1 1)`).

- **Mathlib/project lemmas needed**: `discHeckeOperator`, `heckeOperatorSlash_apply`, `finsum_eq_sum_of_fintype`, `AutomorphicFunction.slash_apply`, `RightSlashAction.comap`, `Submodule.sum_mem`, `discSlash_mem_locPolyDegSubmodule_of_shape`.
- **Sources**: [LWX] `lwx.txt:694–696`; `decomposition.md` W-c.
- **Generality decision**: As stated (any `η ∈ levelM1` with finite double coset).
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W26] `discHeckeOperatorCl`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: W25
- **Parallel**: yes (within the dependency order)
- **Type**: definition

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **`U_p` on the classical disc forms.** -/
def discHeckeOperatorCl {u : K → K}
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    {η : G} (hη : η ∈ levelM1 (p := p) θG)
    (hfin : (((Quotient.mk'' : G → RightCosets U) '' (({η} : Set G) * (U : Set G))) :
      Set (RightCosets U)).Finite) :
    ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ →ₗ[K] ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ where
  toFun φ := ⟨(discHeckeOperator θG 1 ψ κ U hU hη hfin ⟨φ.1, φ.2.1⟩ :
      DiscForms (Γ := Γ) θG 1 ψ κ U hU).1,
    discHeckeOperator_mem_classicalDiscForms θG ψ U hU k κ hκ hη hfin φ.2⟩
  map_add' := by sorry
  map_smul' := by sorry
```

- **Depends on (declarations)**: `discHeckeOperator_mem_classicalDiscForms`

**Proof sketch**:
`map_add'`, `map_smul'`: `Subtype.ext`; `show (discHeckeOperator … ⟨φ.1 + φ'.1, _⟩).1 = …`; `⟨φ.1 + φ'.1, _⟩ = ⟨φ.1, _⟩ + ⟨φ'.1, _⟩` (`rfl`/`Subtype.ext rfl`), `map_add`, `Submodule.coe_add`; same with `map_smul`, `Submodule.coe_smul`.

- **Mathlib/project lemmas needed**: `map_add`, `map_smul`, `Subtype.ext`, `Submodule.coe_add`, `Submodule.coe_smul`.
- **Sources**: [LWX] `lwx.txt:671–682` (§2.4), `lwx.txt:1783–1785` (the twist), `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`); `decomposition.md` W-a…W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W27] `apply_mul_of_theta_eq_one`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **A level element with trivial `p`-component acts trivially**: `φ(x u) = φ(x)` for `u ∈ U`,
`θ u = 1`. -/
theorem apply_mul_of_theta_eq_one {φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)}
    (hφ : φ ∈ DiscForms (Γ := Γ) θG 1 ψ κ U hU) (x : G) {u : G} (hu : u ∈ U) (hθ : θG u = 1) :
    φ (x * u) = φ x := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`(mem_discForms_iff …).1 hφ ⟨u, hu⟩ x : φ (x * u) = discSlash 1 ψ κ ⟨θG u, _⟩ (φ x)`; `have : (⟨θG u, hU hu⟩ : M1 p) = 1 := Subtype.ext hθ`; `rw [this, discSlash_one]` (DiscModel.lean:508: `= ContinuousLinearMap.id`); `ContinuousLinearMap.id_apply`.

- **Mathlib/project lemmas needed**: `mem_discForms_iff`, `discSlash_one`, `Subtype.ext`, `ContinuousLinearMap.id_apply`.
- **Sources**: `bu04.txt:633`; `decomposition.md` I-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [CLEANUP-W9] Cleanup `PhD/LWX/AtkinLehnerMap.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMap` and `lake exe runLinter PhD.LWX.AtkinLehnerMap` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: unused-section-variable `omit`s added per linter, dead tactics removed; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W28] `blockProj_zero_apply_mul_mem_U`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: S16
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **Level-equivariance on disc `0`** at a level element fixing disc `0`, for a classical form
at a classical-shape weight (`mem_discForms_iff`, `blockProj_discSlash`,
`kappaSlash_eq_smul_symAct_of_shape`). -/
theorem blockProj_zero_apply_mul_mem_U {u : K → K}
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ) (x : G) (v : U)
    (hv0 : discImage 1 (⟨θG v, hU v.2⟩ : M1 p) 0 = 0) :
    cSpace.blockProj 0 (φ (x * v))
      = u (ψ ((discConj 1 (⟨θG v, hU v.2⟩ : M1 p) 0 : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1)) •
        symAct K k (RingHom.mapMatrix ψ (discConj 1 (⟨θG v, hU v.2⟩ : M1 p) 0 :
          Matrix (Fin 2) (Fin 2) ℚ_[p])) (cSpace.blockProj 0 (φ x)) := by
  sorry
```

- **Depends on (declarations)**: `kappaSlash_eq_smul_symAct_of_shape`

**Proof sketch**:
1. `(mem_discForms_iff …).1 hφ.1 v x`; `blockProj_discSlash` (DiscModel.lean:482); `hv0` rewrites `blockProj (discImage …) ` to `blockProj 0`.
2. `kappaSlash_eq_smul_symAct_of_shape κ (discConjK 1 ⟨θG v, _⟩ 0 ψ) (hκ _) hf` with `hf : blockProj 0 (φ x) ∈ polySubmodule K k` from `hφ.2 x` (`IsLocPolyDeg`: `∀ a j, k < j → f (a, j) = 0`; `cSpace.blockProj_apply`).
3. `coe_discConjK` (`rfl`): the matrix is `ψ.mapMatrix (discConj …).1` and its `(1,1)` entry is `ψ ((discConj …) 1 1)` (`RingHom.mapMatrix_apply`, `Matrix.map_apply`).

- **Mathlib/project lemmas needed**: `mem_discForms_iff`, `blockProj_discSlash`, `kappaSlash_eq_smul_symAct_of_shape`, `coe_discConjK`, `RingHom.mapMatrix_apply`, `Matrix.map_apply`, `cSpace.blockProj_apply`.
- **Sources**: [LWX] `lwx.txt:676–680`; `decomposition.md` I-c, I-e.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W29] `shapiro_blockProj`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: L39
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **Disc `a` of `φ(x)` is disc `0` of `φ(x·s_a)`**: the translation `s_a` lies in `U`, moves
disc `0` to disc `a` and has trivial disc conjugate (`discImage_sQ_zero`, `discConj_sQ_zero`). -/
theorem shapiro_blockProj {φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)}
    (hφ : φ ∈ DiscForms (Γ := Γ) θG 1 ψ κ U hU) (x : G) (a : ZMod (p ^ 1)) :
    cSpace.blockProj a (φ x) = cSpace.blockProj 0 (φ (x * D.ιp (sGL p (a.val : ℚ_[p])))) := by
  sorry
```

- **Depends on (declarations)**: `discConj_sQ_zero`

**Proof sketch**:
1. `u := ⟨D.ιp (sGL p a.val), D.ιp_mem_U _ (sQ_mem_Iw (IsUltrametricDist.norm_natCast_le_one _ _))⟩ : U`; `(mem_discForms_iff …).1 hφ u x`; `blockProj_discSlash` at disc `0`.
2. The `M1`-element is `⟨θG (ιp (sGL a.val)), _⟩ = ⟨sQ a.val, _⟩` (`Subtype.ext (by rw [D.theta_ιp, coe_sGL])`); `discImage_sQ_zero a.val` and `ZMod.natCast_zmod_val`: `blockProj (discImage …) = blockProj a`.
3. `discConj_sQ_zero (a.val_lt' : a.val < p)` (`ZMod.val_lt` with `pow_one`): `discConjK … 1 ψ = 1` (`Subtype.ext`, `coe_discConjK`, `map_one`); `AnalyticWeight.kappaSlash_one` (Char.lean:824); `ContinuousLinearMap.id_apply`.

- **Mathlib/project lemmas needed**: `mem_discForms_iff`, `blockProj_discSlash`, `discImage_sQ_zero`, `discConj_sQ_zero`, `ZMod.natCast_zmod_val`, `ZMod.val_lt`, `AnalyticWeight.kappaSlash_one`, `AtkinLehnerData.theta_ιp`, `AtkinLehnerData.ιp_mem_U`.
- **Sources**: [LWX] `lwx.txt:841–846`; `decomposition.md` W-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W30] `atkinLehnerFun_blockProj`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem atkinLehnerFun_blockProj (φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)) (x : G)
    (a : ZMod (p ^ 1)) :
    cSpace.blockProj a (atkinLehnerFun θG ψ U k D φ x)
      = ((D.χ (x * D.ιp (sGL p (a.val : ℚ_[p]))) : Kˣ) : K)⁻¹ •
        symAct K k (atkinLehnerK ψ)
          (cSpace.blockProj 0 (φ (x * D.ιp (sGL p (a.val : ℚ_[p])) * (D.ιp (wGL p))⁻¹))) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`unfold atkinLehnerFun`; `map_sum`; `cSpace.blockProj_blockIncl` (BlockOp.lean:611: `= if b = a then f else 0`); `Finset.sum_ite_eq'` + `Finset.mem_univ`, `if_pos`.

- **Mathlib/project lemmas needed**: `cSpace.blockProj_blockIncl`, `map_sum`, `Finset.sum_ite_eq'`.
- **Sources**: [LWX] `lwx.txt:671–682` (§2.4), `lwx.txt:1783–1785` (the twist), `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`); `decomposition.md` W-a…W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [CLEANUP-W10] Cleanup `PhD/LWX/AtkinLehnerMap.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMap` and `lake exe runLinter PhD.LWX.AtkinLehnerMap` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: unused-section-variable `omit`s added per linter, dead tactics removed; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W31] `atkinLehnerFun_blockProj_zero`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: W30, W4
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- Disc `0` of `Wφ(x)`: `χ(x)⁻¹ · (disc 0 of φ(x w⁻¹)) ∣_k w₂`. -/
theorem atkinLehnerFun_blockProj_zero (φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K))
    (x : G) :
    cSpace.blockProj 0 (atkinLehnerFun θG ψ U k D φ x)
      = ((D.χ x : Kˣ) : K)⁻¹ •
        symAct K k (atkinLehnerK ψ) (cSpace.blockProj 0 (φ (x * (D.ιp (wGL p))⁻¹))) := by
  sorry
```

- **Depends on (declarations)**: `atkinLehnerFun_blockProj`, `sGL_zero`

**Proof sketch**:
`atkinLehnerFun_blockProj … 0`; `ZMod.val_zero`, `Nat.cast_zero`, `sGL_zero`, `map_one`, `mul_one`.

- **Mathlib/project lemmas needed**: `atkinLehnerFun_blockProj`, `sGL_zero`, `ZMod.val_zero`.
- **Sources**: [LWX] `lwx.txt:671–682` (§2.4), `lwx.txt:1783–1785` (the twist), `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`); `decomposition.md` W-a…W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W32] `atkinLehnerFun_left_invt`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `Wφ` is left `Γ`-invariant. -/
theorem atkinLehnerFun_left_invt (φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K))
    {γ : G} (hγ : γ ∈ Γ) (x : G) :
    atkinLehnerFun θG ψ U k D φ (γ * x) = atkinLehnerFun θG ψ U k D φ x := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`unfold atkinLehnerFun`; `Finset.sum_congr rfl fun a _ => ?_`; `mul_assoc`; `map_mul D.χ`, `D.χ_Γ γ hγ`, `one_mul`; `φ.left_invt γ hγ _` (AutomorphicFunction.lean:44).

- **Mathlib/project lemmas needed**: `AtkinLehnerData.χ_Γ`, `AutomorphicFunction.left_invt`, `map_mul`, `mul_assoc`.
- **Sources**: [LWX] `lwx.txt:671–682` (§2.4), `lwx.txt:1783–1785` (the twist), `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`); `decomposition.md` W-a…W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W33] `atkinLehnerFun_mem_locPolyDegSubmodule`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: W30, S12
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `Wφ` is locally polynomial of degree `≤ k` (`symAct_mem_polySubmodule`). -/
theorem atkinLehnerFun_mem_locPolyDegSubmodule
    (φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)) (x : G) :
    atkinLehnerFun θG ψ U k D φ x ∈ locPolyDegSubmodule p K 1 k := by
  sorry
```

- **Depends on (declarations)**: `atkinLehnerFun_blockProj`, `symAct_mem_polySubmodule`

**Proof sketch**:
`intro a j hj` (`IsLocPolyDeg`, Theta.lean:140); `← cSpace.blockProj_apply`; `atkinLehnerFun_blockProj`; `cSpace.smul_apply`; `symAct_mem_polySubmodule _ _ _ j hj`; `mul_zero`/`smul_zero`.

- **Mathlib/project lemmas needed**: `atkinLehnerFun_blockProj`, `symAct_mem_polySubmodule`, `cSpace.blockProj_apply`.
- **Sources**: [LWX] `lwx.txt:671–682` (§2.4), `lwx.txt:1783–1785` (the twist), `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`); `decomposition.md` W-a…W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [CLEANUP-W11] Cleanup `PhD/LWX/AtkinLehnerMap.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMap` and `lake exe runLinter PhD.LWX.AtkinLehnerMap` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: unused-section-variable `omit`s added per linter, dead tactics removed; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W34] `atkinLehnerFun_slash`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: W14, W12, W15, W16, W17, W28, W22, W10, L26, W18, W20, S13, W30, W33, S16
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **`W` maps `ψ`-forms to `ψ⁻¹`-forms**: for `u ∈ U`, `(Wφ)(x u) = (Wφ)(x) ∣_{κ'} u`.  Through
`shapiro_blockProj`, `u s_a = s_{a'} u'` with `u'` fixing disc `0`; `w u' w⁻¹` is again in the
level, its `d`-entry is the `a`-entry of `u'` (`atkinLehnerConj_apply_one_one`), and
`nebK(a)·nebK(d) = nebK(det)` on `Iw^{(1)}` cancels against `χ(u') = nebK(det θ u')`. -/
theorem atkinLehnerFun_slash
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh 1 ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ) (u : U) (x : G) :
    atkinLehnerFun θG ψ U k D φ (x * u)
      = discSlash 1 ψ κ' ⟨θG u, hU u.2⟩ (atkinLehnerFun θG ψ U k D φ x) := by
  sorry
```

- **Depends on (declarations)**: `mul_ιp_sGL_eq`, `discShift_mem_U`, `norm_theta_discShift_zero_one_le`, `discImage_discShift_zero`, `discConjMat_discShift_zero`, `blockProj_zero_apply_mul_mem_U`, `nebK_mul_nebK_eq_nebK_det`, `theta_mem_Iw`, `wQ_conj_mem_Iw`, `atkinLehnerK_eq`, `cSpace_ext_blockProj`, `symAct_mul`, `atkinLehnerFun_blockProj`, `atkinLehnerFun_mem_locPolyDegSubmodule`, `kappaSlash_eq_smul_symAct_of_shape`

**Proof sketch**:
Follow `decomposition.md` W-f verbatim.  `apply cSpace_ext_blockProj; intro a`.
1. LHS: `atkinLehnerFun_blockProj` at `x * u`, disc `a`; `mul_assoc`, `mul_ιp_sGL_eq u a` (`u s_a = s_{a'} u'`, `u' := discShift u a`, `a' := discImage (θu) a`); so the argument is `x * s_{a'} * u' * w⁻¹` and the `χ` is `χ (x * s_{a'} * u')`.
2. `u' * w⁻¹ = w⁻¹ * (w * u' * w⁻¹)` (`mul_inv_cancel_left`-style `group`); `hv : w u' w⁻¹ ∈ U := (D.w_conj_mem_U _ (discShift_mem_U …) (norm_theta_discShift_zero_one_le …)).1`; `θ (w u' w⁻¹) = wQ * θ u' * wQinv` (`map_mul`, `map_inv`, `theta_ιp`, `coe_wGL`, `coe_wGL_inv`); `hv0` from `(wQ_conj_mem_Iw (theta_mem_Iw u') (norm_theta_discShift_zero_one_le …)).2` + `discImage_zero_of_norm_apply_zero_one_le`.
3. `blockProj_zero_apply_mul_mem_U hκ hφ (x s_{a'} w⁻¹) ⟨w u' w⁻¹, hv⟩ hv0`: `= nebK (ψ ((discConj … 0) 1 1)) • symAct (ψ.mapMatrix (discConj … 0)) (blockProj 0 (φ (x s_{a'} w⁻¹)))`; `discConjMat_zero_of_discImage_zero`: the matrix is `t₀⁻¹ (wQ g wQinv) t₀` with `g := θ u'`, and its `(1,1)` entry is `g 0 0` (`wQ_mul_mul_wQinv`, `Matrix.mul_fin_two`, `field_simp`).
4. RHS: `blockProj_discSlash` (disc `a` of `discSlash κ' (θu) (Wφ x)` is `kappaSlash_{κ'} (discConjK (θu) a) (blockProj a' (Wφ x))`); `kappaSlash_eq_smul_symAct_of_shape κ' _ (hκ' _) (atkinLehnerFun_mem_locPolyDegSubmodule … a' …)`: `= (nebK (ψ (discConjMat (θu) a) 1 1))⁻¹ • symAct (ψ.mapMatrix (discConjMat (θu) a)) (blockProj a' (Wφ x))`; `atkinLehnerFun_blockProj` at `a'`; `discConjMat_discShift_zero` + `discConjMat_zero_of_discImage_zero`: `discConjMat (θu) a = t₀⁻¹ g t₀`, `(1,1)` entry `g 1 1`.
5. Matrices: `symAct w₂ (symAct M v) = symAct (M * w₂) v` and `symAct (t₀⁻¹ g t₀) (symAct w₂ v) = symAct (w₂ * t₀⁻¹ g t₀) v` (`symAct_mul`, `hf` by `symAct_mem_polySubmodule`/`hφ.2`); `M * w₂ = w₂ * (t₀⁻¹ g t₀)` where `M = t₀⁻¹ wQ g wQinv t₀`, `w₂ = ψ.mapMatrix (t₀⁻¹ wQ t₀)` (`atkinLehnerK_eq`): under `ψ.mapMatrix` (`map_mul`), `t₀⁻¹ wQ g wQinv t₀ t₀⁻¹ wQ t₀ = t₀⁻¹ wQ g t₀ = t₀⁻¹ wQ t₀ t₀⁻¹ g t₀` (`tMat_mul_tMatInv`, `wQinv_mul_wQ`, `mul_assoc`).
6. Scalars: `χ (x s_{a'} u') = χ (x s_{a'}) * χ u'` (`map_mul`), `χ u' = nebK (ψ (det θ u'))` (`D.χ_U _ (discShift_mem_U …)`), `det (θ u') = det g`; `nebK_mul_nebK_eq_nebK_det hmul hcond (theta_mem_Iw u') (norm_theta_discShift_zero_one_le …)`: `nebK (ψ g00) nebK (ψ g11) = nebK (ψ det)`; with `hne` (all three nonzero) `field_simp`; `smul_smul`; `ring_nf`.
Spawn sub-tickets freely for steps 3–6 (each is a self-contained equation).

- **Mathlib/project lemmas needed**: `cSpace_ext_blockProj`, `atkinLehnerFun_blockProj`, `mul_ιp_sGL_eq`, `AtkinLehnerData.w_conj_mem_U`, `AtkinLehnerData.χ_U`, `blockProj_zero_apply_mul_mem_U`, `discConjMat_zero_of_discImage_zero`, `discConjMat_discShift_zero`, `wQ_mul_mul_wQinv`, `wQ_conj_mem_Iw`, `blockProj_discSlash`, `kappaSlash_eq_smul_symAct_of_shape`, `symAct_mul`, `atkinLehnerK_eq`, `nebK_mul_nebK_eq_nebK_det`, `theta_mem_Iw`.
- **Sources**: [LWX] `lwx.txt:1783–1785`; `AtkinLehner.lean:109,113`; `decomposition.md` W-f (full derivation).
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as in `decomposition.md` W-f, split into `hLHS`/`hRHS`/`hmat`/scalar steps; needs `set_option maxHeartbeats 1000000`. Engineering: no `set` abbreviations (lemma instantiations reintroduce the unfolded terms, breaking `rw`); the `ℚ_p` matrix identity is proved for a generic `g` (`hQ`) — `congr 1` on `ψ.mapMatrix` of the concrete `θG (discShift …)` timed out in `whnf`.

### [W35] `atkinLehnerMap`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: W34, W33
- **Parallel**: yes (within the dependency order)
- **Type**: definition

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The Atkin–Lehner map** `W : S^D_{k+2}(ψ) → S^D_{k+2}(ψ⁻¹)` on classical disc forms. -/
def atkinLehnerMap
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh 1 ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1)) :
    ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ →ₗ[K] ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ' where
  toFun φ := ⟨⟨atkinLehnerFun θG ψ U k D φ.1, fun γ hγ x =>
      atkinLehnerFun_left_invt θG ψ U k D φ.1 hγ x⟩, by sorry⟩
  map_add' := by sorry
  map_smul' := by sorry
```

- **Depends on (declarations)**: `atkinLehnerFun_slash`, `atkinLehnerFun_mem_locPolyDegSubmodule`

**Proof sketch**:
Membership: `⟨(mem_discForms_iff …).2 (fun u x => atkinLehnerFun_slash … φ.2 u x), fun x => atkinLehnerFun_mem_locPolyDegSubmodule …⟩`.  `map_add'`/`map_smul'`: `Subtype.ext`, `AutomorphicFunction.ext`/`DFunLike.ext`, `unfold atkinLehnerFun`, `Finset.sum_add_distrib`, `map_add`, `smul_add`, `Finset.smul_sum`, `smul_comm`, `map_smul` (the values `φ (…)` add pointwise: `rfl`).

- **Mathlib/project lemmas needed**: `mem_discForms_iff`, `atkinLehnerFun_slash`, `atkinLehnerFun_mem_locPolyDegSubmodule`, `Finset.sum_add_distrib`, `Finset.smul_sum`, `smul_comm`.
- **Sources**: [LWX] `lwx.txt:671–682` (§2.4), `lwx.txt:1783–1785` (the twist), `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`); `decomposition.md` W-a…W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W36] `atkinLehnerFunInv_blockProj_zero`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: W4
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem atkinLehnerFunInv_blockProj_zero (φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K))
    (x : G) :
    cSpace.blockProj 0 (atkinLehnerFunInv θG ψ U k D φ x)
      = ((D.χ x : Kˣ) : K) •
        symAct K k (atkinLehnerKinv ψ) (cSpace.blockProj 0 (φ (x * D.ιp (wGL p)))) := by
  sorry
```

- **Depends on (declarations)**: `sGL_zero`

**Proof sketch**:
As `atkinLehnerFun_blockProj` + `_zero`: `map_sum`, `cSpace.blockProj_blockIncl`, `Finset.sum_ite_eq'`, `ZMod.val_zero`, `sGL_zero`, `map_one`, `mul_one`.

- **Mathlib/project lemmas needed**: `cSpace.blockProj_blockIncl`, `sGL_zero`.
- **Sources**: [LWX] `lwx.txt:671–682` (§2.4), `lwx.txt:1783–1785` (the twist), `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`); `decomposition.md` W-a…W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [CLEANUP-W12] Cleanup `PhD/LWX/AtkinLehnerMap.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMap` and `lake exe runLinter PhD.LWX.AtkinLehnerMap` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: unused-section-variable `omit`s added per linter, dead tactics removed; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W37] `atkinLehnerFunInv_left_invt`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `W'φ` is left `Γ`-invariant. -/
theorem atkinLehnerFunInv_left_invt (φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K))
    {γ : G} (hγ : γ ∈ Γ) (x : G) :
    atkinLehnerFunInv θG ψ U k D φ (γ * x) = atkinLehnerFunInv θG ψ U k D φ x := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As `atkinLehnerFun_left_invt`.

- **Mathlib/project lemmas needed**: `AtkinLehnerData.χ_Γ`, `AutomorphicFunction.left_invt`.
- **Sources**: [LWX] `lwx.txt:671–682` (§2.4), `lwx.txt:1783–1785` (the twist), `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`); `decomposition.md` W-a…W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W38] `atkinLehnerFunInv_mem_locPolyDegSubmodule`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: S12
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `W'φ` is locally polynomial of degree `≤ k`. -/
theorem atkinLehnerFunInv_mem_locPolyDegSubmodule
    (φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)) (x : G) :
    atkinLehnerFunInv θG ψ U k D φ x ∈ locPolyDegSubmodule p K 1 k := by
  sorry
```

- **Depends on (declarations)**: `symAct_mem_polySubmodule`

**Proof sketch**:
As `atkinLehnerFun_mem_locPolyDegSubmodule` (first prove the `blockProj a` formula for `atkinLehnerFunInv` inline or as a helper `atkinLehnerFunInv_blockProj`).

- **Mathlib/project lemmas needed**: `cSpace.blockProj_blockIncl`, `symAct_mem_polySubmodule`.
- **Sources**: [LWX] `lwx.txt:671–682` (§2.4), `lwx.txt:1783–1785` (the twist), `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`); `decomposition.md` W-a…W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W39] `atkinLehnerFunInv_slash`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: W34, W19, L17
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **`W'` maps `ψ⁻¹`-forms to `ψ`-forms** (the mirror of `atkinLehnerFun_slash`, with
`w⁻¹ u' w` in place of `w u' w⁻¹`). -/
theorem atkinLehnerFunInv_slash
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh 1 ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ') (u : U) (x : G) :
    atkinLehnerFunInv θG ψ U k D φ (x * u)
      = discSlash 1 ψ κ ⟨θG u, hU u.2⟩ (atkinLehnerFunInv θG ψ U k D φ x) := by
  sorry
```

- **Depends on (declarations)**: `atkinLehnerFun_slash`, `atkinLehnerKinv_eq`, `wQinv_mul_mul_wQ`

**Proof sketch**:
Mirror of `atkinLehnerFun_slash` (`decomposition.md` W-g attack 1): `u' * w = w * (w⁻¹ u' w)`, `(D.w_conj_mem_U …).2`, `θ (w⁻¹ u' w) = wQinv g wQ` (`coe_wGL_inv`), `wQinv_mul_mul_wQ` (same shape `(d, −c; −b, a)`), level-equivariance on disc `0` for `φ ∈ Cl κ'` uses `hκ'` (scalar `nebK (ψ g00)⁻¹`), the target uses `hκ` (scalar `nebK (ψ g11)`), `atkinLehnerKinv_eq`, and `nebK_mul_nebK_eq_nebK_det` gives `nebK(det) nebK(g00)⁻¹ = nebK(g11)`; matrices `(t₀⁻¹ wQinv g wQ t₀)(t₀⁻¹ wQinv t₀) = (t₀⁻¹ wQinv t₀)(t₀⁻¹ g t₀)` (`wQ_mul_wQinv`).

- **Mathlib/project lemmas needed**: as `atkinLehnerFun_slash`, plus `atkinLehnerKinv_eq`, `wQinv_mul_mul_wQ`, `coe_wGL_inv`.
- **Sources**: `decomposition.md` W-g.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — mirror of `atkinLehnerFun_slash` (same structure, `w⁻¹ u' w`, `hκ'` with `u := fun x => (nebK x)⁻¹`), `maxHeartbeats 1000000`.

### [CLEANUP-W13] Cleanup `PhD/LWX/AtkinLehnerMap.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMap` and `lake exe runLinter PhD.LWX.AtkinLehnerMap` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: unused-section-variable `omit`s added per linter, dead tactics removed; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W40] `atkinLehnerMapInv`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: W39, W38
- **Parallel**: yes (within the dependency order)
- **Type**: definition

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The inverse map on classical disc forms (the mirror of `atkinLehnerMap`, with `w⁻¹`). -/
def atkinLehnerMapInv
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh 1 ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1)) :
    ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ' →ₗ[K] ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ where
  toFun φ := ⟨⟨atkinLehnerFunInv θG ψ U k D φ.1, fun γ hγ x =>
      atkinLehnerFunInv_left_invt θG ψ U k D φ.1 hγ x⟩, by sorry⟩
  map_add' := by sorry
  map_smul' := by sorry
```

- **Depends on (declarations)**: `atkinLehnerFunInv_slash`, `atkinLehnerFunInv_mem_locPolyDegSubmodule`

**Proof sketch**:
As `atkinLehnerMap`.

- **Mathlib/project lemmas needed**: `mem_discForms_iff`, `atkinLehnerFunInv_slash`, `atkinLehnerFunInv_mem_locPolyDegSubmodule`.
- **Sources**: [LWX] `lwx.txt:671–682` (§2.4), `lwx.txt:1783–1785` (the twist), `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`); `decomposition.md` W-a…W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W41] `atkinLehnerMapInv_atkinLehnerMap`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: W29, W36, W31, S13, S14, W20
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `W' ∘ W = 1` (`χ(w) = 1`, `symAct_mul`, `symAct_one`, `shapiro_blockProj`). -/
theorem atkinLehnerMapInv_atkinLehnerMap
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh 1 ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    (φ : ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ) :
    atkinLehnerMapInv θG ψ U hU k D κ κ' hmul hne hcond hκ hκ'
        (atkinLehnerMap θG ψ U hU k D κ κ' hmul hne hcond hκ hκ' φ) = φ := by
  sorry
```

- **Depends on (declarations)**: `shapiro_blockProj`, `atkinLehnerFunInv_blockProj_zero`, `atkinLehnerFun_blockProj_zero`, `symAct_mul`, `symAct_one`, `cSpace_ext_blockProj`

**Proof sketch**:
`Subtype.ext`; `AutomorphicFunction.ext`/`DFunLike.ext x`; `cSpace_ext_blockProj a`; `shapiro_blockProj` on both sides (both are disc forms — the LHS is the value of `atkinLehnerMapInv`, so its membership is available) reduces to disc `0` at `y := x s_a`: `atkinLehnerFunInv_blockProj_zero`, `atkinLehnerFun_blockProj_zero`: `χ y • symAct w₂⁻¹ (χ (y w)⁻¹ • symAct w₂ (blockProj 0 (φ (y w w⁻¹))))`; `mul_inv_cancel_right`; `map_smul`, `smul_smul`; `symAct_mul` (`hf` from `φ.2.2`) + `atkinLehnerK_mul_atkinLehnerKinv` + `symAct_one`; `χ (y w) = χ y * χ w = χ y` (`map_mul`, `D.χ_wGL`, `mul_one`); `mul_inv_cancel₀ (Units.ne_zero _)`, `one_smul`.

- **Mathlib/project lemmas needed**: `shapiro_blockProj`, `atkinLehnerFunInv_blockProj_zero`, `atkinLehnerFun_blockProj_zero`, `symAct_mul`, `symAct_one`, `atkinLehnerK_mul_atkinLehnerKinv`, `AtkinLehnerData.χ_wGL`, `cSpace_ext_blockProj`.
- **Sources**: `decomposition.md` W-g.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W42] `atkinLehnerMap_atkinLehnerMapInv`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: W41
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `W ∘ W' = 1`. -/
theorem atkinLehnerMap_atkinLehnerMapInv
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh 1 ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    (φ : ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ') :
    atkinLehnerMap θG ψ U hU k D κ κ' hmul hne hcond hκ hκ'
        (atkinLehnerMapInv θG ψ U hU k D κ κ' hmul hne hcond hκ hκ' φ) = φ := by
  sorry
```

- **Depends on (declarations)**: `atkinLehnerMapInv_atkinLehnerMap`

**Proof sketch**:
Mirror: `χ (y w⁻¹) = χ y * (χ w)⁻¹ = χ y` (`map_inv`, `D.χ_wGL`), `atkinLehnerKinv_mul_atkinLehnerK`, `inv_mul_cancel_right`.

- **Mathlib/project lemmas needed**: as `atkinLehnerMapInv_atkinLehnerMap`, `atkinLehnerKinv_mul_atkinLehnerK`, `map_inv`.
- **Sources**: `decomposition.md` W-g.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [CLEANUP-W14] Cleanup `PhD/LWX/AtkinLehnerMap.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMap` and `lake exe runLinter PhD.LWX.AtkinLehnerMap` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: unused-section-variable `omit`s added per linter, dead tactics removed; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W43] `discEvalAtReps_mem_locPolyDegSubmoduleBlock`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- Evaluation at the representatives sends classical disc forms into the block-model classical
subspace (`discEvalAtReps_apply`). -/
theorem discEvalAtReps_mem_locPolyDegSubmoduleBlock (c : ι → G)
    (φ : ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ) :
    discEvalAtReps θG 1 ψ κ U hU c ⟨φ.1, φ.2.1⟩
      ∈ locPolyDegSubmoduleBlock p ι K 1 k := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`intro i a j hj` (`locPolyDegSubmoduleBlock` carrier, StepOne.lean:138); `discEvalAtReps_apply` (DiscForms.lean:111); `φ.2.2 (c i) a j hj`.

- **Mathlib/project lemmas needed**: `discEvalAtReps_apply`, `locPolyDegSubmoduleBlock`.
- **Sources**: [LWX] (2.11.1) `lwx.txt:848–856`.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W44] `discEvalAtRepsCl`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: W43
- **Parallel**: yes (within the dependency order)
- **Type**: definition

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The block model of the classical disc forms at a neat level**: evaluation at
representatives with trivial stabilisers is a linear isomorphism onto the block-model
classical subspace (`bijective_discEvalAtReps_of_stabilizer_eq_bot`, with the classical
condition transported both ways through the classical shape). -/
def discEvalAtRepsCl {u : K → K}
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i, AutomorphicFunction.stabilizerAtSlash Γ U (c i) = ⊥) :
    ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ ≃ₗ[K] locPolyDegSubmoduleBlock p ι K 1 k := by
  sorry
```

- **Depends on (declarations)**: `discEvalAtReps_mem_locPolyDegSubmoduleBlock`

**Proof sketch**:
Replace `by sorry` with a term.
1. `E₀ : ClassicalDiscForms … →ₗ[K] locPolyDegSubmoduleBlock … := LinearMap.codRestrict _ ((discEvalAtReps θG 1 ψ κ U hU c).comp (Submodule.inclusion inf_le_left … as a linear map into DiscForms)) (discEvalAtReps_mem_locPolyDegSubmoduleBlock …)` (`Submodule.inclusion (inf_le_left)` : `ClassicalDiscForms →ₗ DiscForms`).
2. `LinearEquiv.ofBijective E₀ ⟨inj, surj⟩`: `inj` from `(bijective_discEvalAtReps_of_stabilizer_eq_bot … c hc hstab).1` and `Submodule.inclusion_injective`; `surj`: for `f`, `obtain ⟨φ, hφ⟩ := (bijective_… ).2 f.1`; `φ ∈ locPolyForms`: for `x`, `obtain ⟨i, hi⟩ := hc.2 (Quotient.mk'' x)`, then `DoubleCoset.rel_iff.mp (Quotient.eq''.mp hi) : ∃ γ ∈ Γ, ∃ u ∈ U, x = γ * c i * u` (pattern at HeckeMatrix.lean:140), `φ.1 (γ c_i u) = φ.1 (c_i u)` (`left_invt`) `= discSlash (θu) (φ.1 (c_i))` (`mem_discForms_iff`), `φ.1 (c_i) = f|_i` (`discEvalAtReps_apply`, `hφ`) `∈ locPolyDegSubmodule` (`f.2 i`), `discSlash_mem_locPolyDegSubmodule_of_shape … (fun a => hκ _)`.
3. `refine ⟨⟨φ, φ.2, hloc⟩, Subtype.ext hφ⟩`.

- **Mathlib/project lemmas needed**: `LinearEquiv.ofBijective`, `LinearMap.codRestrict`, `Submodule.inclusion`, `bijective_discEvalAtReps_of_stabilizer_eq_bot`, `DoubleCoset.rel_iff`, `Quotient.eq''`, `discEvalAtReps_apply`, `mem_discForms_iff`, `discSlash_mem_locPolyDegSubmodule_of_shape`.
- **Sources**: [LWX] `lwx.txt:841–848` (neatness ⇒ bijection); `decomposition.md` W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [W45] `discEvalAtRepsCl_apply`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: W44
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem discEvalAtRepsCl_apply {u : K → K}
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i, AutomorphicFunction.stabilizerAtSlash Γ U (c i) = ⊥)
    (φ : ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ) :
    (discEvalAtRepsCl θG ψ U hU k κ hκ c hc hstab φ : c(ι × (ZMod (p ^ 1) × ℕ), K))
      = discEvalAtReps θG 1 ψ κ U hU c ⟨φ.1, φ.2.1⟩ := by
  sorry
```

- **Depends on (declarations)**: `discEvalAtRepsCl`

**Proof sketch**:
`rfl` / `LinearEquiv.ofBijective_apply`, `LinearMap.codRestrict_apply`, `LinearMap.comp_apply`, `Submodule.coe_inclusion`.

- **Mathlib/project lemmas needed**: `LinearEquiv.ofBijective_apply`, `LinearMap.codRestrict_apply`.
- **Sources**: [LWX] `lwx.txt:671–682` (§2.4), `lwx.txt:1783–1785` (the twist), `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`); `decomposition.md` W-a…W-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [CLEANUP-W15] Cleanup `PhD/LWX/AtkinLehnerMap.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerMap` and `lake exe runLinter PhD.LWX.AtkinLehnerMap` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: unused-section-variable `omit`s added per linter, dead tactics removed; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.

### [CLEANUP-W-FINAL] Final cleanup `PhD/LWX/AtkinLehnerMap.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerMap.lean
- **Depends on**: every proof ticket of Part W
- **Parallel**: no
- **Type**: cleanup

Whole-file `/cleanup`: sorry-free check (`grep -c sorry` = 0), `#print axioms` on the file's
headline declarations (standard axioms only), `lake exe runLinter PhD.LWX.AtkinLehnerMap` clean, module
docstring updated to describe what is proved (drop "skeleton"/"planned" wording), relocations
named in `tickets.md` performed with one rebuild.
- **Progress**: 2026-09-10: DONE — inline cleanup: unused-section-variable `omit`s added per linter, dead tactics removed; `lake env lean PhD/LWX/AtkinLehnerMap.lean` clean.


## Part I — `PhD/LWX/AtkinLehnerIdentity.lean`: the identity, H1 and the degree formula

### [I1] `vRepD_mem_levelM1`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentity.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem vRepD_mem_levelM1 (c : Fin p) : vRepD θG ψ U D c ∈ levelM1 (p := p) θG := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`levelM1 = Submonoid.comap θG (M1 p)` (IntegralModel.lean:1356): `Submonoid.mem_comap`; `D.theta_ιp`, `coe_vGL`; `vQ_mem_M1 (IsUltrametricDist.norm_natCast_le_one ℚ_[p] c)`.

- **Mathlib/project lemmas needed**: `Submonoid.mem_comap`, `AtkinLehnerData.theta_ιp`, `vQ_mem_M1`.
- **Sources**: `bu04.txt:645–649`, `lwx.txt:690–692` ((2.5.1)); `scratch` "What remains"; `decomposition.md` I-a…I-l.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched.

### [I2] `upEltD_mem_levelM1`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentity.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem upEltD_mem_levelM1 : upEltD θG ψ U D ∈ levelM1 (p := p) θG := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As `vRepD_mem_levelM1` with `c = 0` (`Nat.cast_zero`).

- **Mathlib/project lemmas needed**: `vQ_mem_M1`.
- **Sources**: `bu04.txt:645–649`, `lwx.txt:690–692` ((2.5.1)); `scratch` "What remains"; `decomposition.md` I-a…I-l.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched.

### [I3] `discHeckeOperator_apply_eq_sum`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentity.lean
- **Depends on**: I1, I2
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The naive Hecke formula**: `(U_p φ)(x) = ∑_c φ(x v_c⁻¹) ∣ v_c`
(`heckeOperatorSlash_eq_finsetSum` at the representatives, `AutomorphicFunction.slash_apply`). -/
theorem discHeckeOperator_apply_eq_sum
    (hfin : (((Quotient.mk'' : G → RightCosets U) ''
      (({upEltD θG ψ U D} : Set G) * (U : Set G))) : Set (RightCosets U)).Finite)
    (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range (vRepD θG ψ U D))
      (((Quotient.mk'' : G → RightCosets U) ''
        (({upEltD θG ψ U D} : Set G) * (U : Set G))) : Set (RightCosets U)))
    (hvinj : Function.Injective (vRepD θG ψ U D))
    (φ : DiscForms (Γ := Γ) θG 1 ψ κ U hU) (x : G) :
    ((discHeckeOperator θG 1 ψ κ U hU (upEltD_mem_levelM1 θG ψ U D) hfin φ :
        DiscForms (Γ := Γ) θG 1 ψ κ U hU) : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)) x
      = ∑ c : Fin p, discSlash 1 ψ κ ⟨θG (vRepD θG ψ U D c), vRepD_mem_levelM1 θG ψ U D c⟩
          ((φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)) (x * (vRepD θG ψ U D c)⁻¹)) := by
  sorry
```

- **Depends on (declarations)**: `vRepD_mem_levelM1`, `upEltD_mem_levelM1`

**Proof sketch**:
1. `show` the LHS as `heckeOperatorSlash K hU hU _ hfin φ` under `letI := discLevelSlashAction θG 1 ψ κ; letI := discLevelSMulSlashClass …` (copy the `letI` preamble of `discEvalAtReps_discHeckeOperator`, DiscForms.lean:202).
2. `AutomorphicFunction.heckeOperatorSlash_apply_rep (Γ := Γ) K hU (upEltD_mem_levelM1 …) hfin φ (vRepD …) (vRepD_mem_levelM1 …) hv hvinj x (fun t => x * (vRepD … t)⁻¹) (fun _ => 1) (fun _ => one_mem _) (fun _ => 1) (fun t => by simp) (fun t => by simpa using vRepD_mem_levelM1 … t)` (HeckeMatrix.lean:57).
3. `Finset.sum_congr rfl fun t _ => ?_`: the slash `∣ₛ ⟨(1 : U) * vRepD t, _⟩` on the coefficient module is `discSlash 1 ψ κ (levelM1ToM1 θG ⟨…⟩)` (`RightSlashAction.comap` — `rfl`/`show`), and `levelM1ToM1 θG ⟨1 * v, _⟩ = ⟨θG v, _⟩` (`Subtype.ext`, `one_mul`, `map_mul`, `map_one`).

- **Mathlib/project lemmas needed**: `AutomorphicFunction.heckeOperatorSlash_apply_rep`, `discLevelSlashAction`, `RightSlashAction.comap`, `levelM1ToM1`, `Subtype.ext`.
- **Sources**: `bu04.txt:645–649`, `lwx.txt:690–692` ((2.5.1)); `scratch` "What remains"; `decomposition.md` I-a…I-l. `decomposition.md` I-b.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — `heckeOperatorSlash_apply_rep` with the trivial factorisation; the `1 * v` element closed by `congr 2` + `Subtype.ext`.

### [CLEANUP-I1] Cleanup `PhD/LWX/AtkinLehnerIdentity.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentity.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerIdentity` and `lake exe runLinter PhD.LWX.AtkinLehnerIdentity` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: omits per linter, dead tactics removed; `lake env lean` clean.

### [I4] `blockProj_zero_discSlash_of_shape`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentity.lean
- **Depends on**: S16
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- Disc `0` of a classical-shape disc slash at a matrix fixing disc `0` is the nebentypus
constant times the `Sym^k`-action of the disc conjugate (`blockProj_discSlash`,
`kappaSlash_eq_smul_symAct_of_shape`). -/
theorem blockProj_zero_discSlash_of_shape {u : K → K}
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    (δ : M1 p) (hδ : discImage 1 δ 0 = 0) {f : c(ZMod (p ^ 1) × ℕ, K)}
    (hf : f ∈ locPolyDegSubmodule p K 1 k) :
    cSpace.blockProj 0 (discSlash 1 ψ κ δ f)
      = u (ψ ((discConj 1 δ 0 : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1)) •
        symAct K k (RingHom.mapMatrix ψ (discConj 1 δ 0 : Matrix (Fin 2) (Fin 2) ℚ_[p]))
          (cSpace.blockProj 0 f) := by
  sorry
```

- **Depends on (declarations)**: `kappaSlash_eq_smul_symAct_of_shape`

**Proof sketch**:
`blockProj_discSlash`; `hδ`; `kappaSlash_eq_smul_symAct_of_shape κ (discConjK 1 δ 0 ψ) (hκ _) hf'` with `hf' : blockProj 0 f ∈ polySubmodule K k` from `hf 0` (`IsLocPolyDeg`, `cSpace.blockProj_apply`); `coe_discConjK`, `RingHom.mapMatrix_apply`, `Matrix.map_apply`.

- **Mathlib/project lemmas needed**: `blockProj_discSlash`, `kappaSlash_eq_smul_symAct_of_shape`, `coe_discConjK`.
- **Sources**: `decomposition.md` I-c.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched.

### [I5] `apply_mul_ιp_pGL`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentity.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The central element acts trivially**: `φ(x · ιp(p·1)) = φ(x)` on disc forms
(`AtkinLehnerData.central`: `ιp(p·1) = γ u` with `γ ∈ Γ` central and `θ u = 1`). -/
theorem apply_mul_ιp_pGL {φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)}
    (hφ : φ ∈ DiscForms (Γ := Γ) θG 1 ψ κ U hU) (x : G) :
    φ (x * D.ιp (pGL p)) = φ x := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`obtain ⟨γ, hγ, u, hu, hp, hθu, hcomm⟩ := D.central`; `rw [hp, ← mul_assoc, ← hcomm x, mul_assoc, φ.left_invt γ hγ]`; `apply_mul_of_theta_eq_one hφ x hu hθu` (Part W).

- **Mathlib/project lemmas needed**: `AtkinLehnerData.central`, `AutomorphicFunction.left_invt`, `apply_mul_of_theta_eq_one`.
- **Sources**: `decomposition.md` I-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched.

### [I6] `apply_mul_ιp_pGL_inv`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentity.lean
- **Depends on**: I5
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
theorem apply_mul_ιp_pGL_inv {φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)}
    (hφ : φ ∈ DiscForms (Γ := Γ) θG 1 ψ κ U hU) (x : G) :
    φ (x * (D.ιp (pGL p))⁻¹) = φ x := by
  sorry
```

- **Depends on (declarations)**: `apply_mul_ιp_pGL`

**Proof sketch**:
`have := apply_mul_ιp_pGL … hφ (x * (D.ιp (pGL p))⁻¹)`; `rw [inv_mul_cancel_right] at this`; `exact this.symm`.

- **Mathlib/project lemmas needed**: `apply_mul_ιp_pGL`, `inv_mul_cancel_right`.
- **Sources**: `decomposition.md` I-d.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched.

### [CLEANUP-I2] Cleanup `PhD/LWX/AtkinLehnerIdentity.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentity.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerIdentity` and `lake exe runLinter PhD.LWX.AtkinLehnerIdentity` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: omits per linter, dead tactics removed; `lake env lean` clean.

### [I7] `blockProj_zero_apply_mul_ιp`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentity.lean
- **Depends on**: W28
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- Level-equivariance at a lift `ιp g` of an Iwahori element fixing disc `0`, read on disc `0`
(`blockProj_zero_apply_mul_mem_U` at `v = ιp g`, `ιp_mem_U`, `theta_ιp`). -/
theorem blockProj_zero_apply_mul_ιp {u : K → K}
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ) (x : G) {g : GL (Fin 2) ℚ_[p]}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) ∈ Iw p 1)
    (hg0 : discImage 1 (⟨(g : Matrix (Fin 2) (Fin 2) ℚ_[p]), Iw_one_le_M1 hg⟩ : M1 p) 0 = 0) :
    cSpace.blockProj 0 (φ (x * D.ιp g))
      = u (ψ ((discConj 1 (⟨(g : Matrix (Fin 2) (Fin 2) ℚ_[p]), Iw_one_le_M1 hg⟩ : M1 p) 0 :
            Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1)) •
        symAct K k (RingHom.mapMatrix ψ (discConj 1
          (⟨(g : Matrix (Fin 2) (Fin 2) ℚ_[p]), Iw_one_le_M1 hg⟩ : M1 p) 0 :
            Matrix (Fin 2) (Fin 2) ℚ_[p])) (cSpace.blockProj 0 (φ x)) := by
  sorry
```

- **Depends on (declarations)**: `blockProj_zero_apply_mul_mem_U`

**Proof sketch**:
`blockProj_zero_apply_mul_mem_U hκ hφ x ⟨D.ιp g, D.ιp_mem_U g hg⟩ ?_` after rewriting the `M1`-element `⟨θG (ιp g), _⟩` to `⟨g, Iw_one_le_M1 hg⟩` (`Subtype.ext (D.theta_ιp g)`; `convert … using 2` / `simp only [D.theta_ιp]`).

- **Mathlib/project lemmas needed**: `blockProj_zero_apply_mul_mem_U`, `AtkinLehnerData.theta_ιp`, `AtkinLehnerData.ιp_mem_U`.
- **Sources**: `decomposition.md` I-e.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched.

### [I8] `term_elt_eq`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentity.lean
- **Depends on**: W7, W6
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **The group element of the `(b,c)`-term**: `x v_c⁻¹ w v_b⁻¹ w⁻¹ = x s_b · (ιp p)⁻¹ · ℓ_{b,c}⁻¹`
(`wGL_mul_vGL_mul_wGL_inv_mul_vGL`, inverted). -/
theorem term_elt_eq (x : G) (b c : ℚ_[p]) :
    x * (D.ιp (vGL p c))⁻¹ * D.ιp (wGL p) * (D.ιp (vGL p b))⁻¹ * (D.ιp (wGL p))⁻¹
      = x * D.ιp (sGL p b) * (D.ιp (pGL p))⁻¹ * (D.ιp (ℓGL p b c))⁻¹ := by
  sorry
```

- **Depends on (declarations)**: `wGL_mul_vGL_mul_wGL_inv_mul_vGL`, `sGL_inv`

**Proof sketch**:
`have h := congrArg D.ιp (wGL_mul_vGL_mul_wGL_inv_mul_vGL b c)`; `map_mul`, `map_inv` at `h`; take inverses: `(w v_b w⁻¹ v_c)⁻¹ = v_c⁻¹ w v_b⁻¹ w⁻¹` (`mul_inv_rev`, `inv_inv`) and `(ℓ (P s_{−b}))⁻¹ = s_{−b}⁻¹ P⁻¹ ℓ⁻¹` with `s_{−b}⁻¹ = s_b` (`← map_inv`, `sGL_inv`, `neg_neg`); multiply by `x` on the left; `simp only [mul_assoc]`/`group`.

- **Mathlib/project lemmas needed**: `wGL_mul_vGL_mul_wGL_inv_mul_vGL`, `sGL_inv`, `mul_inv_rev`, `map_mul`, `map_inv`, `group`.
- **Sources**: `decomposition.md` I-f.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched.

### [I9] `blockProj_zero_apply_term_elt`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentity.lean
- **Depends on**: W27, I7, W29, L37, L35, W3, L31
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **Disc `0` of `φ(x s_b p⁻¹ ℓ⁻¹)`**: the central `p` acts trivially and `ℓ⁻¹` fixes disc `0`
with `d`-entry `1 − bcp`, so it is `nebK(1 − bcp) · symAct(conj ℓ⁻¹)(φ(x)|_b)`. -/
theorem blockProj_zero_apply_term_elt
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ) (x : G) (b c : Fin p) :
    cSpace.blockProj 0
        (φ (x * D.ιp (sGL p (b : ℕ)) * (D.ιp (pGL p))⁻¹ * (D.ιp (ℓGL p (b : ℕ) (c : ℕ)))⁻¹))
      = nebK (ψ (1 - (b : ℚ_[p]) * c * p)) •
        symAct K k (RingHom.mapMatrix ψ (tMatInv p 0 * ℓQinv p (b : ℕ) (c : ℕ) * tMat p 0))
          (cSpace.blockProj (b : ZMod (p ^ 1)) (φ x)) := by
  sorry
```

- **Depends on (declarations)**: `apply_mul_of_theta_eq_one`, `blockProj_zero_apply_mul_ιp`, `shapiro_blockProj`, `discConj_ℓQinv_zero_one_one`, `discImage_ℓQinv_zero`, `coe_ℓGL_inv`, `discConjMat_zero_of_discImage_zero`

**Proof sketch**:
1. `obtain ⟨γ, hγ, u, hu, hP, hθu, hcomm⟩ := D.central`; `(ιp P)⁻¹ = u⁻¹ * γ⁻¹` (`hP`, `mul_inv_rev`); move `γ⁻¹` to the far left (`hcomm` for `γ⁻¹`: from `γ x = x γ` derive `γ⁻¹ x = x γ⁻¹`, `mul_inv_eq_iff_eq_mul`), `φ.left_invt γ⁻¹ (inv_mem hγ)`.
2. `x s_b u⁻¹ ℓ⁻¹ = (x s_b ℓ⁻¹) * (ℓ u⁻¹ ℓ⁻¹)` (`group`); `hℓU : D.ιp (ℓGL b c) ∈ U := D.ιp_mem_U _ (ℓQ_mem_Iw …)`; `ℓ u⁻¹ ℓ⁻¹ ∈ U` (`mul_mem`, `inv_mem`); `θ (ℓ u⁻¹ ℓ⁻¹) = 1` (`map_mul`, `map_inv`, `hθu`, `inv_one`, `mul_one`, `mul_inv_cancel`); `apply_mul_of_theta_eq_one hφ.1`.
3. `blockProj_zero_apply_mul_ιp hκ hφ (x s_b) (g := (ℓGL b c)⁻¹) (hg : ↑ = ℓQinv ∈ Iw := by rw [coe_ℓGL_inv]; exact ℓQinv_mem_Iw …) (hg0 := discImage_ℓQinv_zero …)` (transport the `Subtype` through `coe_ℓGL_inv`).
4. Scalar: `discConj_ℓQinv_zero_one_one`; matrix: `discConjMat_zero_of_discImage_zero` (`= tMatInv 0 * ℓQinv * tMat 0`, `coe_discConj`).
5. `shapiro_blockProj hφ.1 x (b : ZMod (p^1))` reversed, with `((b : ZMod (p^1))).val = b` (`ZMod.val_natCast`, `pow_one`, `Nat.mod_eq_of_lt b.isLt`).

- **Mathlib/project lemmas needed**: `AtkinLehnerData.central`, `apply_mul_of_theta_eq_one`, `blockProj_zero_apply_mul_ιp`, `coe_ℓGL_inv`, `ℓQinv_mem_Iw`, `discImage_ℓQinv_zero`, `discConj_ℓQinv_zero_one_one`, `discConjMat_zero_of_discImage_zero`, `shapiro_blockProj`, `ZMod.val_natCast`.
- **Sources**: `decomposition.md` I-f (i).
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched.

### [CLEANUP-I3] Cleanup `PhD/LWX/AtkinLehnerIdentity.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentity.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerIdentity` and `lake exe runLinter PhD.LWX.AtkinLehnerIdentity` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: omits per linter, dead tactics removed; `lake env lean` clean.

### [I10] `atkinLehner_term_eq`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentity.lean
- **Depends on**: I8, I9, W31, W23, S13, S15, W18, W19, L31, L20, L13
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The `(b, c)`-term of the double-coset expansion, read on disc `0`: the outer `U_p`
contributes `symAct(conj v_c)`, `W'` contributes `χ(x v_c⁻¹) · symAct w₂⁻¹`, the inner
`U_p^{(ψ⁻¹)}` contributes `symAct(conj v_b)`, and `W` is evaluated at `x v_c⁻¹ w v_b⁻¹`.  With
`w v_b w⁻¹ v_c = ℓ_{b,c} · p · s_{−b}` the term is `ψ_neb(1 + bcp)⁻¹` times a vector independent
of `c`: `p^k · (disc b of φ(x)) ∣_k (1 −b/p; 0 1)`. -/
theorem atkinLehner_term_eq
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 → nebK (ψ x) = 1)
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh 1 ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    (φ : ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ) (x : G) (b c : Fin p) :
    symAct K k (RingHom.mapMatrix ψ (discConj 1 (⟨vQ p c, vQ_mem_M1 (by
        exact IsUltrametricDist.norm_natCast_le_one ℚ_[p] c)⟩ : M1 p) 0 :
          Matrix (Fin 2) (Fin 2) ℚ_[p]))
      (((D.χ (x * (vRepD θG ψ U D c)⁻¹) : Kˣ) : K) •
        symAct K k (atkinLehnerKinv ψ)
          (symAct K k (RingHom.mapMatrix ψ (discConj 1 (⟨vQ p b, vQ_mem_M1 (by
              exact IsUltrametricDist.norm_natCast_le_one ℚ_[p] b)⟩ : M1 p) 0 :
                Matrix (Fin 2) (Fin 2) ℚ_[p]))
            (cSpace.blockProj 0
              ((atkinLehnerMap θG ψ U hU k D κ κ' hmul hne hcond hκ hκ' φ :
                  AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K))
                (x * (vRepD θG ψ U D c)⁻¹ * D.ιp (wGL p) * (vRepD θG ψ U D b)⁻¹)))))
      = (nebK (ψ (1 + (b : ℚ_[p]) * c * p)))⁻¹ •
        ((ψ p) ^ k • symAct K k (RingHom.mapMatrix ψ !![1, -((b : ℚ_[p]) / p); 0, 1])
          (cSpace.blockProj (b : ZMod (p ^ 1)) (φ.1 x))) := by
  sorry
```

- **Depends on (declarations)**: `term_elt_eq`, `blockProj_zero_apply_term_elt`, `atkinLehnerFun_blockProj_zero`, `nebK_one_sub_eq_inv`, `symAct_mul`, `symAct_smul_one`, `atkinLehnerK_eq`, `atkinLehnerKinv_eq`, `discConjMat_zero_of_discImage_zero`, `ℓQinv_mul_wQ_mul_vQ_mul_wQinv_mul_vQ`, `tMatInv_zero_mul_sQ_mul_tMat_zero`

**Proof sketch**:
Follow `decomposition.md` I-f (repaired).
1. `atkinLehnerFun_blockProj_zero` at `y := x v_c⁻¹ w v_b⁻¹` (the value of `atkinLehnerMap … φ` is `atkinLehnerFun … φ.1` by `rfl`); `term_elt_eq` rewrites `y w⁻¹`; `blockProj_zero_apply_term_elt`.
2. Scalars: `χ y = χ (x v_c⁻¹) * χ w * (χ v_b)⁻¹` (`map_mul`, `map_inv`; `vRepD` unfold), `D.χ_wGL`, `D.χ_vGL`: `χ y = χ (x v_c⁻¹)`; so `χ(x v_c⁻¹) * (χ y)⁻¹ = 1` (`mul_inv_cancel₀`, `Units.ne_zero`).  `nebK (ψ (1 − bcp)) = (nebK (ψ (1 + bcp)))⁻¹` (`nebK_one_sub_eq_inv hmul hne hcond (hx : ‖b c p‖ ≤ p⁻¹)`).
3. Matrices: pull the scalars out (`map_smul`, `smul_smul`), then `symAct_mul` four times (each `hf` by `symAct_mem_polySubmodule`, base `blockProj b (φ x) ∈ polySubmodule` from `φ.2.2`): total `symAct (M₁ * M₂ * M₃ * M₄ * M₅)` with `M₁ = ψ(t₀⁻¹ ℓQinv t₀)`, `M₂ = atkinLehnerK ψ`, `M₃ = ψ(discConj (vQ b) 0)`, `M₄ = atkinLehnerKinv ψ`, `M₅ = ψ(discConj (vQ c) 0)` (outermost = rightmost).
4. `atkinLehnerK_eq`, `atkinLehnerKinv_eq`, `discConjMat_zero_of_discImage_zero` (with `discImage_vQ_zero`) write every factor as `ψ.mapMatrix (t₀⁻¹ N t₀)`; `← map_mul` (`RingHom.mapMatrix` is a ring hom); cancel `t₀ t₀⁻¹` (`tMat_mul_tMatInv`, `mul_assoc`); `ℓQinv_mul_wQ_mul_vQ_mul_wQinv_mul_vQ` (after `mul_assoc` normalisation); `tMatInv 0 * (p • sQ (−b)) * tMat 0 = p • !![1, −b/p; 0, 1]` (`smul_mul_assoc`, `mul_smul_comm`, `tMatInv_zero_mul_sQ_mul_tMat_zero`, `neg_div`).
5. `ψ.mapMatrix (p • N) = ψ p • ψ.mapMatrix N` (`Matrix.map_smul`/`RingHom.mapMatrix_apply` with `map_mul`, or write `p • N = (p • 1) * N`); `symAct ((ψ p • 1) * N') f = symAct N' (symAct (ψ p • 1) f) = symAct N' ((ψ p)^k • f)` (`symAct_mul`, `symAct_smul_one`), `map_smul`; `smul_smul`; done.
Spawn sub-tickets for steps 2–5 as needed (each is a closed equation).

- **Mathlib/project lemmas needed**: `atkinLehnerFun_blockProj_zero`, `term_elt_eq`, `blockProj_zero_apply_term_elt`, `AtkinLehnerData.χ_wGL`, `AtkinLehnerData.χ_vGL`, `nebK_one_sub_eq_inv`, `symAct_mul`, `symAct_smul_one`, `symAct_mem_polySubmodule`, `atkinLehnerK_eq`, `atkinLehnerKinv_eq`, `discConjMat_zero_of_discImage_zero`, `discImage_vQ_zero`, `ℓQinv_mul_wQ_mul_vQ_mul_wQinv_mul_vQ`, `tMatInv_zero_mul_sQ_mul_tMat_zero`, `tMat_mul_tMatInv`, `RingHom.mapMatrix`, `map_smul`.
- **Sources**: `scratch` `obstruction_mul_lowerUni`, `obstruction_zero`; `decomposition.md` I-f (repaired).
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — as in `decomposition.md` I-f (repaired). Steps: `hin` (W on disc 0, `term_elt_eq`, `blockProj_zero_apply_term_elt`), `simp only [map_smul, smul_smul]`, three `symAct_mul`, `hmat` (brute-force `ext`/`fin_cases` on literal matrices), `← symAct_mul` + `symAct_smul_one`, scalar via `nebK_one_sub_eq_inv`.

### [I11] `blockProj_zero_discHecke_atkinLehner`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentity.lean
- **Depends on**: I3, I4, W36, I10, W21, S14
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
set_option maxHeartbeats 1000000 in
/-- **`U_p ∘ W⁻¹ ∘ U_p^{(ψ⁻¹)} ∘ W = p^{k+1}` on disc `0`**: the double-coset expansion, the
key factorisation, and the character sum. -/
theorem blockProj_zero_discHecke_atkinLehner
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 → nebK (ψ x) = 1)
    (hsum : ∀ b : ℕ, ¬ p ∣ b →
      ∑ c ∈ Finset.range p, (nebK (ψ (1 + (b : ℚ_[p]) * c * p)))⁻¹ = 0)
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh 1 ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    (hfin : (((Quotient.mk'' : G → RightCosets U) ''
      (({upEltD θG ψ U D} : Set G) * (U : Set G))) : Set (RightCosets U)).Finite)
    (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range (vRepD θG ψ U D))
      (((Quotient.mk'' : G → RightCosets U) ''
        (({upEltD θG ψ U D} : Set G) * (U : Set G))) : Set (RightCosets U)))
    (hvinj : Function.Injective (vRepD θG ψ U D))
    (φ : ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ) (x : G) :
    cSpace.blockProj 0
      ((discHeckeOperatorCl θG ψ U hU k κ hκ (upEltD_mem_levelM1 θG ψ U D) hfin
        (atkinLehnerMapInv θG ψ U hU k D κ κ' hmul hne hcond hκ hκ'
          (discHeckeOperatorCl θG ψ U hU k κ' (u := fun x => (nebK x)⁻¹) hκ'
            (upEltD_mem_levelM1 θG ψ U D) hfin
            (atkinLehnerMap θG ψ U hU k D κ κ' hmul hne hcond hκ hκ' φ))) :
        AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)) x)
      = (ψ p) ^ (k + 1) • cSpace.blockProj 0 (φ.1 x) := by
  sorry
```

- **Depends on (declarations)**: `discHeckeOperator_apply_eq_sum`, `blockProj_zero_discSlash_of_shape`, `atkinLehnerFunInv_blockProj_zero`, `atkinLehner_term_eq`, `nebK_one`, `symAct_one`

**Proof sketch**:
Follow `decomposition.md` I-g.
1. Outer `U_p`: the value of `discHeckeOperatorCl … φ'` at `x` is the value of `discHeckeOperator … ⟨φ'.1, _⟩` (`rfl`); `discHeckeOperator_apply_eq_sum … hfin hv hvinj`; `map_sum` (`blockProj 0`); each term `blockProj_zero_discSlash_of_shape hκ ⟨vQ c, _⟩ (discImage_vQ_zero) hf` with scalar `nebK (ψ ((discConj (vQ c) 0) 1 1)) = nebK (ψ 1) = 1` (`discConjMat_apply_one_one`, `nebK_one hcond`), `one_smul`.
2. `atkinLehnerFunInv_blockProj_zero` (the value of `atkinLehnerMapInv … g` is `atkinLehnerFunInv … g.1`); inner `U'`: `discHeckeOperator_apply_eq_sum` for `κ'`; `map_sum` through `blockProj 0`, `symAct`, `smul`; `blockProj_zero_discSlash_of_shape hκ'` with scalar `(nebK (ψ 1))⁻¹ = 1`.
3. `Finset.smul_sum`, `map_sum`, `Finset.sum_comm`; `atkinLehner_term_eq … φ x b c` termwise (`vRepD θG ψ U D c = D.ιp (vGL p c)` by `rfl`).
4. `Finset.sum_eq_single (0 : Fin p)`: for `b ≠ 0`, `∑_c (nebK …)⁻¹ • v_b = (∑_c (nebK …)⁻¹) • v_b = 0` (`Finset.sum_smul`, `hsum b (Nat.not_dvd_of_pos_of_lt (Fin.pos_iff_ne_zero.2 hb) b.isLt)`, `Fin.sum_univ_eq_sum_range`, `zero_smul`); for `b = 0`: `(0 : Fin p) = 0` casts, `nebK (ψ 1)⁻¹ = 1` (`nebK_one`), `!![1, −0/p; 0, 1] = 1` (`neg_zero`, `zero_div`, `Matrix.one_fin_two`), `map_one`, `symAct_one` (`hf` from `φ.2.2`), `Finset.sum_const`, `Finset.card_univ`, `Fintype.card_fin`, `Nat.cast_smul_eq_nsmul`/`nsmul_eq_mul`, `map_natCast ψ p`, `pow_succ`, `smul_smul`, `Fin.val_zero`, `Nat.cast_zero`.

- **Mathlib/project lemmas needed**: `discHeckeOperator_apply_eq_sum`, `blockProj_zero_discSlash_of_shape`, `discImage_vQ_zero`, `discConjMat_apply_one_one`, `nebK_one`, `atkinLehnerFunInv_blockProj_zero`, `atkinLehner_term_eq`, `Finset.sum_comm`, `Finset.sum_eq_single`, `Finset.sum_smul`, `Fin.sum_univ_eq_sum_range`, `Nat.not_dvd_of_pos_of_lt`, `symAct_one`, `Finset.sum_const`, `map_natCast`.
- **Sources**: `scratch` "What remains, Step 2"; `decomposition.md` I-g.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — `hin` (inner `U_p^{ψ⁻¹}`), `hterm` (W' + `atkinLehner_term_eq`), `hout` (outer `U_p`), `Finset.sum_comm`, `← Finset.sum_smul`, `Finset.sum_eq_single 0`; `b ≠ 0` killed by `hsum` through `Fin.sum_univ_eq_sum_range`.

### [I12] `discHeckeCl_comp_atkinLehner`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentity.lean
- **Depends on**: I11, W29, W20
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
set_option maxHeartbeats 1000000 in
/-- **The operator identity** `U_p ∘ (W⁻¹ ∘ U_p^{(ψ⁻¹)} ∘ W) = p^{k+1}` on the classical disc
forms (`shapiro_blockProj` carries the disc-`0` identity to every disc). -/
theorem discHeckeCl_comp_atkinLehner
    (hmul : ∀ x y : ℚ_[p], ‖x‖ = 1 → ‖y‖ = 1 → nebK (ψ (x * y)) = nebK (ψ x) * nebK (ψ y))
    (hne : ∀ x : ℚ_[p], ‖x‖ = 1 → nebK (ψ x) ≠ 0)
    (hcond : ∀ x : ℚ_[p], ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ 2 → nebK (ψ x) = 1)
    (hsum : ∀ b : ℕ, ¬ p ∣ b →
      ∑ c ∈ Finset.range p, (nebK (ψ (1 + (b : ℚ_[p]) * c * p)))⁻¹ = 0)
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hκ' : ∀ g : M1Kh 1 ψ, κ'.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1))⁻¹ * linX g.1 ^ (k + 1))
    (hfin : (((Quotient.mk'' : G → RightCosets U) ''
      (({upEltD θG ψ U D} : Set G) * (U : Set G))) : Set (RightCosets U)).Finite)
    (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range (vRepD θG ψ U D))
      (((Quotient.mk'' : G → RightCosets U) ''
        (({upEltD θG ψ U D} : Set G) * (U : Set G))) : Set (RightCosets U)))
    (hvinj : Function.Injective (vRepD θG ψ U D)) :
    (discHeckeOperatorCl θG ψ U hU k κ hκ (upEltD_mem_levelM1 θG ψ U D) hfin).comp
        ((atkinLehnerMapInv θG ψ U hU k D κ κ' hmul hne hcond hκ hκ').comp
          ((discHeckeOperatorCl θG ψ U hU k κ' (u := fun x => (nebK x)⁻¹) hκ'
            (upEltD_mem_levelM1 θG ψ U D) hfin).comp
            (atkinLehnerMap θG ψ U hU k D κ κ' hmul hne hcond hκ hκ')))
      = (ψ p) ^ (k + 1) • LinearMap.id := by
  sorry
```

- **Depends on (declarations)**: `blockProj_zero_discHecke_atkinLehner`, `shapiro_blockProj`, `cSpace_ext_blockProj`

**Proof sketch**:
`LinearMap.ext fun φ => ?_`; `Subtype.ext`; `DFunLike.ext _ _ fun x => ?_`; `cSpace_ext_blockProj fun a => ?_`; `shapiro_blockProj (…).2.1 x a` on both sides (LHS: the composite's value is in `ClassicalDiscForms κ`, use its `.2.1`; RHS: `((ψ p)^(k+1) • φ).1 = (ψ p)^(k+1) • φ.1`, `Submodule.coe_smul`, `map_smul`); `blockProj_zero_discHecke_atkinLehner … φ (x * ιp (sGL a.val))`; `LinearMap.comp_apply`, `LinearMap.smul_apply`, `LinearMap.id_apply`.

- **Mathlib/project lemmas needed**: `blockProj_zero_discHecke_atkinLehner`, `shapiro_blockProj`, `cSpace_ext_blockProj`, `LinearMap.ext`, `Submodule.coe_smul`, `LinearMap.comp_apply`.
- **Sources**: `decomposition.md` I-h.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — `shapiro_blockProj` on both sides reduces to the disc-0 identity; composite abbreviated by `set Ψ`.

### [CLEANUP-I4] Cleanup `PhD/LWX/AtkinLehnerIdentity.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentity.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerIdentity` and `lake exe runLinter PhD.LWX.AtkinLehnerIdentity` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: omits per linter, dead tactics removed; `lake env lean` clean.

### [I13] `discEvalAtRepsCl_discHeckeOperatorCl`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentity.lean
- **Depends on**: W45
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- Under the block model at a neat level, the classical Hecke operator is the block operator
of the certificates restricted to the classical subspace (`discEvalAtReps_discHeckeOperator`). -/
theorem discEvalAtRepsCl_discHeckeOperatorCl {u : K → K}
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (u (g.1 1 1)) * linX g.1 ^ (k + 1))
    (hfin : (((Quotient.mk'' : G → RightCosets U) ''
      (({upEltD θG ψ U D} : Set G) * (U : Set G))) : Set (RightCosets U)).Finite)
    (c : ι → G)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
    (hstab : ∀ i, AutomorphicFunction.stabilizerAtSlash Γ U (c i) = ⊥)
    (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range (vRepD θG ψ U D))
      (((Quotient.mk'' : G → RightCosets U) ''
        (({upEltD θG ψ U D} : Set G) * (U : Set G))) : Set (RightCosets U)))
    (hvinj : Function.Injective (vRepD θG ψ U D)) (idx : ι → Fin p → ι) (uu : ι → Fin p → U)
    (d : ι → Fin p → G) (hd : ∀ i t, d i t ∈ Γ)
    (hfact : ∀ i t, c i * (vRepD θG ψ U D t)⁻¹ = d i t * c (idx i t) * (uu i t : G))
    (φ : ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ) :
    (discEvalAtRepsCl θG ψ U hU k κ hκ c hc hstab
        (discHeckeOperatorCl θG ψ U hU k κ hκ (upEltD_mem_levelM1 θG ψ U D) hfin φ) :
          c(ι × (ZMod (p ^ 1) × ℕ), K))
      = discHeckeBlockOp θG 1 ψ κ U hU (vRepD θG ψ U D) (vRepD_mem_levelM1 θG ψ U D) idx uu
          (discEvalAtRepsCl θG ψ U hU k κ hκ c hc hstab φ) := by
  sorry
```

- **Depends on (declarations)**: `discEvalAtRepsCl_apply`

**Proof sketch**:
`discEvalAtRepsCl_apply` on both sides; `discEvalAtReps_discHeckeOperator θG 1 ψ κ U hU (vRepD …) (vRepD_mem_levelM1 …) idx uu (upEltD_mem_levelM1 …) hfin c hv hvinj d hd hfact ⟨φ.1, φ.2.1⟩` (DiscForms.lean:202); the LHS form `discHeckeOperatorCl … φ` coerces to `discHeckeOperator … ⟨φ.1, φ.2.1⟩` by `rfl`.

- **Mathlib/project lemmas needed**: `discEvalAtRepsCl_apply`, `discEvalAtReps_discHeckeOperator`.
- **Sources**: `decomposition.md` I-i.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — proved as sketched.

### [I14] `atkinLehnerHypothesis_of_conj`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentity.lean
- **Depends on**: none beyond the file's imports
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **Hypothesis H1 transports along similarities**: if `A B = c • 1` with `B` conjugate to `A'`
in the abstract, the same holds after conjugating `A` and `A'` separately. -/
theorem atkinLehnerHypothesis_of_conj
    {A B A' S S' S₁ S₁' : Matrix (Fin (Fintype.card ι * ((k + 1) * p ^ 1)))
      (Fin (Fintype.card ι * ((k + 1) * p ^ 1))) K}
    (h : AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 k A B A')
    (hS : S₁ * S = 1) (hS' : S₁' * S' = 1) (hS'' : S' * S₁' = 1) :
    AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 k (S * A * S₁) (S * B * S₁)
      (S' * A' * S₁') := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`obtain ⟨hAB, P, Q, hQP, hA'⟩ := h`; `hSS₁ : S * S₁ = 1 := Matrix.mul_eq_one_comm.mp hS`; `refine ⟨?_, S' * P * S₁, S * Q * S₁', ?_, ?_⟩`; (i) `S A S₁ S B S₁ = S (A B) S₁` (`Matrix.mul_assoc`, `hS`, `Matrix.mul_one`) `= c • S S₁ = c • 1` (`hAB`, `Matrix.mul_smul`, `Matrix.smul_mul`, `hSS₁`); (ii) `Q' P' = S Q (S₁' S') P S₁ = S (Q P) S₁ = S S₁ = 1` (`hS'`, `hQP`); (iii) `S' A' S₁' = S' P B Q S₁' = (S' P S₁)(S B S₁)(S Q S₁')` inserting `S₁ S = 1` twice (`hS`).  `hS''` is slack (`_hx`).

- **Mathlib/project lemmas needed**: `Matrix.mul_eq_one_comm`, `Matrix.mul_assoc`, `Matrix.mul_smul`, `Matrix.smul_mul`, `Matrix.mul_one`, `Matrix.one_mul`.
- **Sources**: `decomposition.md` I-j.
- **Generality decision**: As stated (square matrices over a field; `hS''` slack).
- **Progress**: 2026-09-10: DONE — `hS''` unused (slack), renamed `_hS''`; uses root `mul_eq_one_comm` (no `Matrix.mul_eq_one_comm` in this Mathlib).

### [I15] `atkinLehnerHypothesis_of_atkinLehnerData`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentity.lean
- **Depends on**: I12, I13, N4, N27, N19, N20, N21, N18, I14
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **Hypothesis H1 at the classical points, from the Atkin–Lehner data.**  With `A` the matrix
of `U_p` at `(k, ψ)`, `A'` at the partner `(k, ψ⁻¹)` (nebentypus `ω⁻¹ω₀^{2k}`, point
`T_{χ_k}(ζ⁻¹)`), and `B := W⁻¹ A' W`: `A B = p^{k+1}` is `discHeckeCl_comp_atkinLehner` in
the block model, and `A' = W B W⁻¹` by construction. -/
theorem atkinLehnerHypothesis_of_atkinLehnerData [Nonempty ι]
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹)
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
    (hfact : ∀ i t, c i * (vRepD θG ψ U D t)⁻¹ = d i t * c (idx i t) * (uu i t : G)) :
    ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 k
      ((classicalData ψ ω θG U hU (vRepD θG ψ U D) (vRepD_mem_levelM1 θG ψ U D) uu hp2 hψ hζ
        hpK k).matrix idx) B
      ((classicalData ψ (partnerChar p ω k) θG U hU (vRepD θG ψ U D)
        (vRepD_mem_levelM1 θG ψ U D) uu hp2 hψ hζ.inv hpK k).matrix idx) := by
  sorry
```

- **Depends on (declarations)**: `discHeckeCl_comp_atkinLehner`, `discEvalAtRepsCl_discHeckeOperatorCl`, `autFactor_haloWeightH_classicalPoint_eq_nebCharK`, `autFactor_haloWeightH_partner_eq_inv_nebCharK`, `nebCharK_psi_mul`, `nebCharK_psi_ne_zero`, `nebCharK_psi_of_norm_sub_one_le_sq`, `sum_inv_nebCharK_eq_zero`, `atkinLehnerHypothesis_of_conj`

**Proof sketch**:
Follow `decomposition.md` I-k and Step F.
1. `set cd := classicalData ψ ω θG U hU (vRepD …) (vRepD_mem_levelM1 …) uu hp2 hψ hζ hpK k`, `cd' := classicalData ψ (partnerChar p ω k) … hζ.inv hpK k`; `κ := cd.weight`, `κ' := cd'.weight` (Touching.lean:672: `haloWeightH 1 ψ T₀ ω hp2 hψ c.h0 c.h1 c.hT`).
2. `hκ := fun g => autFactor_haloWeightH_classicalPoint_eq_nebCharK ψ ω k ζ hp2 hψ hζ cd.h0 cd.h1 cd.hT g`, `hκ' := fun g => autFactor_haloWeightH_partner_eq_inv_nebCharK … g`; `hmul hne hcond hsum` from `nebCharK_psi_mul`, `nebCharK_psi_ne_zero`, `nebCharK_psi_of_norm_sub_one_le_sq`, `sum_inv_nebCharK_eq_zero`.
3. `E := discEvalAtRepsCl θG ψ U hU k κ hκ c hc hstab`, `E' := …κ' hκ'…`; `Wb : locPolyDegSubmoduleBlock ≃ₗ[K] locPolyDegSubmoduleBlock := E.symm.trans ((atkinLehnerEquiv … hmul hne hcond hκ hκ').trans E')`.
4. `cd.matrix idx = upMatrix 1 k (discHeckeBlockOp … κ …) _ = LinearMap.toMatrix b b (restrict …)` (`ClassicalData.matrix`, `classicalMatrix`, `upMatrix` — all `rfl`/`unfold`); `hres : restrict (discHeckeBlockOp κ) = (E.toLinearMap ∘ₗ discHeckeOperatorCl κ … ∘ₗ E.symm.toLinearMap)` by `LinearMap.ext` + `discEvalAtRepsCl_discHeckeOperatorCl` at `E.symm f` (`LinearEquiv.apply_symm_apply`, `Subtype.ext`); same for `κ'`.
5. `refine ⟨LinearMap.toMatrix b b (Wb.symm.toLinearMap ∘ₗ restrict (T_{κ'}) ∘ₗ Wb.toLinearMap), ?_, LinearMap.toMatrix b b Wb.toLinearMap, LinearMap.toMatrix b b Wb.symm.toLinearMap, ?_, ?_⟩`; (i) `← LinearMap.toMatrix_comp`; the composite is `E ∘ (U_κ ∘ W⁻¹ ∘ U_κ' ∘ W) ∘ E⁻¹` (`hres`, `LinearEquiv.symm_trans_apply`, `LinearEquiv.trans_apply`, `LinearEquiv.symm_apply_apply`, `atkinLehnerEquiv` = `ofLinear`: `LinearEquiv.ofLinear_apply`, `LinearEquiv.ofLinear_symm_apply`); `discHeckeCl_comp_atkinLehner`; `LinearMap.comp_smul`, `LinearMap.smul_comp`, `LinearMap.toMatrix_smul`… (`map_smul` for `LinearMap.toMatrix`), `LinearMap.toMatrix_id`; (ii) `Q P = toMatrix (Wb.symm ∘ Wb) = toMatrix id = 1` (`LinearMap.toMatrix_comp`, `LinearEquiv.symm_comp`, `LinearMap.toMatrix_id`); (iii) `A' = P B Q` likewise (`Wb ∘ Wb.symm = id`).
`atkinLehnerHypothesis_of_conj` is available if the `finBasisOfFinrankEq` basis of `upMatrix` needs matching against a transported basis; with everything expressed as `toMatrix b b` on `locPolyDegSubmoduleBlock` it is not needed (`S = S₁ = 1`).

- **Mathlib/project lemmas needed**: `ClassicalData.matrix`, `classicalMatrix`, `upMatrix`, `discEvalAtRepsCl`, `discEvalAtRepsCl_discHeckeOperatorCl`, `atkinLehnerEquiv`, `discHeckeCl_comp_atkinLehner`, `LinearMap.toMatrix_comp`, `LinearMap.toMatrix_id`, `LinearEquiv.ofLinear_apply`, `LinearEquiv.trans_apply`, `LinearEquiv.symm_apply_apply`, `LinearMap.ext`, `autFactor_haloWeightH_classicalPoint_eq_nebCharK`, `autFactor_haloWeightH_partner_eq_inv_nebCharK`, `nebCharK_psi_*`, `sum_inv_nebCharK_eq_zero`.
- **Sources**: [LWX] Prop 3.22 `lwx.txt:1763–1789` (statement); `lwx.txt:841–866` (block model); `decomposition.md` I-k, Step F.
- **Generality decision**: As stated.
- **Progress**: 2026-09-10: DONE — needed the `κ'` radius generalisation (`{UK'} {ρ'}`, logged in `b2_log.jsonl`): the two classical-point halo weights have different `haloRhoH`. Block model: `Wb := E.symm.trans (AL.trans E')`, `B := toMatrix (Wb⁻¹ ∘ T' ∘ Wb)`; `A * B` from `hkey`; `A' = P B Q` via an explicit composition lemma (`congr 1` there timed out). `maxHeartbeats 2000000`.

### [CLEANUP-I5] Cleanup `PhD/LWX/AtkinLehnerIdentity.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentity.lean
- **Depends on**: the three preceding proof tickets of this file
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.AtkinLehnerIdentity` and `lake exe runLinter PhD.LWX.AtkinLehnerIdentity` must be clean.
- **Progress**: 2026-09-10: DONE — inline cleanup: omits per linter, dead tactics removed; `lake env lean` clean.

### [CLEANUP-ALL-1] `/cleanup-all` before the milestone
- **Status**: done
- **File**: all five files
- **Depends on**: every ticket before I15 (all Parts S, N, L, W and Part I up to the H1 assembly)
- **Parallel**: no
- **Type**: cleanup

`/cleanup-all` across the five files; full `lake build PhD`; runLinter on the five modules;
confirm `#print axioms LWX.atkinLehnerHypothesis_of_atkinLehnerData` is standard.
- **Progress**: 2026-09-10: DONE — all five modules sorry-free; `lake build PhD.LWX.AtkinLehnerIdentity` green; `lake exe runLinter` reports nothing in any of the five files (two simpNF findings fixed by dropping `@[simp]` from `coe_wGL_inv`, `coe_ℓGL_inv`).

### [I16] `degX_succ_of_atkinLehnerData` — **MILESTONE**
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentity.lean
- **Depends on**: I15
- **Parallel**: yes (within the dependency order)
- **Type**: milestone

**Statement** (verbatim from the skeleton; protected):
```lean
/-- **[LWX, Thm 1.3]'s degree formula with no hypothesis left**, granted the adelic data:
`deg X_{k+1,ω} = r_ord(ω⁻¹ω₀^{2k}) + r_ord(ωω₀^{−2k−2})`. -/
theorem degX_succ_of_atkinLehnerData [Nonempty ι] [IsAlgClosed K]
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p)
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
      (vRepD_mem_levelM1 θG ψ U D) uu i t)).IsUpShape)
    (hdet : ∀ i t, (certM1 θG U hU (vRepD θG ψ U D) (vRepD_mem_levelM1 θG ψ U D) uu i t :
      Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p) :
    degX (UpDatum.ofCerts θG U hU (vRepD θG ψ U D) (vRepD_mem_levelM1 θG ψ U D) idx uu hshape)
        ω (k + 1)
      = ordDim (UpDatum.ofCerts θG U hU (vRepD θG ψ U D) (vRepD_mem_levelM1 θG ψ U D) idx uu
          hshape) (partnerChar p ω k)
        + ordDim (UpDatum.ofCerts θG U hU (vRepD θG ψ U D) (vRepD_mem_levelM1 θG ψ U D) idx uu
          hshape) (targetChar p ω k) := by
  sorry
```

- **Depends on (declarations)**: `atkinLehnerHypothesis_of_atkinLehnerData`

**Proof sketch**:
`exact degX_succ_classicalPoint idx hp2 hψ hshape hdet hζ hζ.inv ω (partnerChar p ω k) k (atkinLehnerHypothesis_of_atkinLehnerData … ω hp2 hψ hζ (norm_natCast_p ψ hψ) D hfin hv hvinj c hc hstab idx uu d hd hfact)` (DegreeFormula.lean:56; its `hpK` is `norm_natCast_p ψ hψ`).

- **Mathlib/project lemmas needed**: `degX_succ_classicalPoint`, `atkinLehnerHypothesis_of_atkinLehnerData`, `norm_natCast_p`, `IsPrimitiveRoot.inv`.
- **Sources**: [LWX] Thm 1.3, §3.23 `lwx.txt:2028–2036`; `decomposition.md` I-l.
- **Generality decision**: As stated — **MILESTONE**.
- **Progress**: 2026-09-10: DONE — **MILESTONE**: term-mode application of `degX_succ_classicalPoint` to `atkinLehnerHypothesis_of_atkinLehnerData`. `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

### [CLEANUP-I-FINAL] Final cleanup `PhD/LWX/AtkinLehnerIdentity.lean`
- **Status**: done
- **File**: PhD/LWX/AtkinLehnerIdentity.lean
- **Depends on**: every proof ticket of Part I
- **Parallel**: no
- **Type**: cleanup

Whole-file `/cleanup`: sorry-free check (`grep -c sorry` = 0), `#print axioms` on the file's
headline declarations (standard axioms only), `lake exe runLinter PhD.LWX.AtkinLehnerIdentity` clean, module
docstring updated to describe what is proved (drop "skeleton"/"planned" wording), relocations
named in `tickets.md` performed with one rebuild.
- **Progress**: 2026-09-10: DONE — inline cleanup: omits per linter, dead tactics removed; `lake env lean` clean.

### [CLEANUP-FINAL] `/cleanup-all`, board close-out
- **Status**: done
- **File**: all five files, `plan.md`, `tickets.md`, `JL-AUDIT.md`
- **Depends on**: everything
- **Parallel**: no
- **Type**: cleanup

Final `/cleanup-all`; `lake build PhD` green with **no** sorry warnings in the five modules;
`#print axioms LWX.degX_succ_of_atkinLehnerData` = `[propext, Classical.choice, Quot.sound]`;
update `plan.md` STATUS to COMPLETE, the Summary of this file, the JL-AUDIT item 1 line
("avoided concretely"), and the memory file `lwx-h1-board.md`.
- **Progress**: 2026-09-10: DONE — docstrings updated (no skeleton wording), `PhD.lean` comment updated, axioms standard for the milestone and the headline results, plan/JL-AUDIT/memory updated; full `lake build PhD` run at close-out.
