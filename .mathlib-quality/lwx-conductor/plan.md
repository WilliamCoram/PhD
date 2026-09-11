# Development Plan — `lwx-conductor` (Step I / H1 at conductor `p^{h+1}`, and the slope reflection)

**BOARD PATH: `.mathlib-quality/lwx-conductor/`.**  The default `.mathlib-quality/` board is the
completed NewtonPolygons project — never touch it.  A parallel run owns `.mathlib-quality/qmf/`
and its `beastmode_active` sentinel — never touch that either (cat before rm; delete only
`.mathlib-quality/lwx-conductor/beastmode_active`).  Every `/beastmode` run must name this board
path explicitly.  Planned 2026-09-11.

## STATUS: EXECUTED (`/beastmode`, 2026-09-11) — every proof ticket proved, no `sorry` in the nine files; gate record (build, `#print axioms`, `runLinter`) in `tickets.md` Summary

Skeleton: nine new modules, `sorry` only, registered in `PhD.lean` (see "File structure");
`lake build` of the modules on 2026-09-11: **Build completed successfully (3829 jobs)**,
`sorry` warnings only (details in `tickets.md`, "Skeleton build record").  230 tickets
(167 proof/definition + 63 cleanup) in `tickets.md`; milestones I15 (H1 at level `h`),
R13 (the slope reflection, no hypothesis left), R17 (the arithmetic progressions of
[LWX, Thm 1.5]).  Revision (user, 2026-09-11): the unit-band hypotheses `hband`/`hband'` are
folded in through a family of Atkin–Lehner data (Part F), which also puts (4.2.5)–(4.2.6) =
(1.5.2) on the board.

## Goal

Every result of the Step I / Step III development (`lwx-theta`, `lwx-theta-h2`, `lwx-h1`) is
proved at the classical points of **conductor `p²`** (analyticity level `h = 1`).  [LWX, Thm 1.5]'s
second half ((1.5.2), the arithmetic-progression structure of the slope ratios) runs the same
argument at **conductor `p^M` for every large `M`** (`lwx.txt:2322–2366`), with `M = h + 1`.
This board generalises the level-`1` layer to every level `h ≥ 1` and proves the polygon-level
identity that (1.5.2) is assembled from:

* **H1 at level `h`** — `LWX.atkinLehnerHypothesis_of_atkinLehnerDataH`: [LWX, Prop 3.22] at
  conductor `p^{h+1}` (`lwx.txt:1763–1768`), by the same JL-free double-coset identity
  `U_p ∘ W⁻¹ ∘ U_p^{(ψ⁻¹)} ∘ W = p^{k+1}` with the Atkin–Lehner element `w_h` of level `p^{h+1}`.
* **Step I at level `h`** — `LWX.isStepOneTouching_of_atkinLehnerHypothesisH`: the touching at the
  vertex `n = (k+1)p^h t` (which is the level-`1` vertex `n_{(k+1)p^{h−1}}`; a consistency result,
  not on the critical path).
* **The unit band at every vertex and every disc, with no hypothesis left** —
  `LWX.hasUnitBand_of_atkinLehnerFamily` (row 1 of the dependency ledger in
  `.mathlib-quality/lwx-stepone/FINDINGS.md`, closed): granted the adelic data at **every**
  classical weight of conductor `p²` (`AtkinLehnerFamily`: one section `ιp`, a Hecke character
  `χ ω k` for every disc `ω` and exponent `k`), `HasUnitBand D ω n` for all `ω`, `n`; hence
  [LWX, Thm 1.5 (1.5.1)] for the genuine `U_p` unconditionally
  (`unitSlope_discHeckeCharPowerSeries_eq_slopeRatio_of_atkinLehnerFamily`).  Per-`k` version:
  `hasUnitBand_of_atkinLehnerData` (a one-line corollary of `lwx-h1`).
* **The slope reflection, with no hypothesis left** —
  `LWX.slopeRatio_add_slopeRatio_partnerChar_of_atkinLehnerFamilyH`: at conductor `p^{h+1}` in
  the slope-reading region ("the assumption on `M`"), for every disc `ω`, every `k` and
  `i < N = t(k+1)p^h`, `slopeRatio (ω⁻¹ω₀^{2k}) (N−1−i) + slopeRatio ω i = (k+1)·p^{h−1}(p−1)`
  — [LWX, §4.2]'s "`α̃_{(k+1)q^{−1}p^Mt−1−i}(ψ⁻¹|_Δ·ω₀^k) = (k+1)q^{−2}p^M − α̃_i(ψ|_Δ·ω₀^k)`"
  (`lwx.txt:2345–2350`) in the normalisation `slopeRatio = ϕ(q)·α̃`, granted the level-`h`
  family `AtkinLehnerFamilyH` over the same section.
* **[LWX, Thm 1.5, second half] at the polygon level** — (4.2.5) `slopeRatio_partnerChar_succ`;
  **(1.5.2)** = (4.2.6) `slopeRatio_mul_teichChar_sq`: `slopeRatio (ωω₀²) (j + p^h t) =
  slopeRatio ω j + p^{h−1}(p−1)` for every `ω`, `j`; and the arithmetic progressions
  `slopeRatio_add_period`: `slopeRatio ω (j + (p−1)/2·p^h t) = slopeRatio ω j + (p−1)/2·p^{h−1}(p−1)`
  ("since ω₀^{ϕ(q)} = 1", `lwx.txt:2361–2366`).  These are the ψ-varying bookkeeping that the
  first draft of this plan left to a follow-on board; with the family structure they are five
  short corollaries (user decision 2026-09-11: fold `hband`/`hband'` into this board).

**Out of scope** (each is a follow-on board or a user decision):
* Step III at level `h` (theta exactness, the degree formula): [LWX, Thm 1.5] uses only the
  complement bound `le_unitSlope_compl` (already general in `h`) plus the theta target
  (`TargetPointH.lean`), not the degree formula;
* instantiating `AtkinLehnerFamily` / `AtkinLehnerFamilyH` for `Dfx ℚ D` (class field theory
  for the characters `χ ω k`, and the local computations for `ιp`); the rigid-analytic packaging
  of Thm 1.5 (`Spc^{>λ} = ∐ Y_i`, finite flatness — excluded by the blueprint introduction);
  `p = 2` (deferred by the user, 2026-09-11: [LWX] state but do not prove the `p = 2` cases).

## The reading of the source

[LWX, §4.2] (`lwx.txt:2322–2350`), verbatim:

> "Let ψ be a character of conductor p^M. We look at weights of the form (k, ψ) for all k ≥ 0.
> First, note that v(T_{(k,ψ)}) = q/ϕ(p^M) = q/((p−1)p^{M−1}) by the assumption on M; thus
> (k,ψ) ∈ W^{>λ}_{ψ|Δ·ω₀^k}. Noting the equality q/((p−1)p^{M−1})·ϕ(q) = q²p^{−M}, it then
> follows that the U_p-slopes of S^D_{k+2}(K^p Iw_{p^M}, ψ) are
> q²p^{−M}α̃_0(ψ|Δ·ω₀^k), …, q²p^{−M}α̃_{(k+1)q^{−1}p^M t−1}(ψ|Δ·ω₀^k).
> Hence, by Atkin–Lehner theory (Proposition 3.22), in the U_p-slope sequence on
> S^D_{k+2}(K^p Iw_{p^M}; ψ^{−1}), from the (kq^{−1}p^M t+1)st to the (k+1)q^{−1}p^M t-th is
> given by k+1 − q²p^{−M}α̃_{q^{−1}p^M t−1}(ψ|Δ·ω₀^k), …, k+1 − q²p^{−M}α̃_0(ψ|Δ·ω₀^k).
> This implies the relations
> α̃_{(k+1)q^{−1}p^M t−1−i}(ψ^{−1}|Δ·ω₀^k) = q^{−2}p^M(k+1 − q²p^{−M}α̃_i(ψ|Δ·ω₀^k))
> = (k+1)q^{−2}p^M − α̃_i(ψ|Δ·ω₀^k) for 0 ≤ i ≤ q^{−1}p^M t − 1."

Three inputs are being used, and each is a leaf of this board:

1. **"by the assumption on M"** — [LWX, Thm 1.5]: "let M be a positive integer so that
   p^{−q/p^{M−1}(p−1)} > λ" with `λ = p^{−8/((p²−1)t+8)}` (`lwx.txt:181–186`).  With `q = p`,
   `M = h + 1`: `(p²−1)t + 8 < 8·p^{h−1}(p−1)` — `ConductorSlopes.lean`'s region lemma.  It
   places `T_{(k,ψ)}` in the domain of the slope reading `unitSlope_discHeckeCharPowerSeries_eq_slopeRatio`
   (`SlopesSeam.lean`, already stated at every level `h`).
2. **"it then follows that the U_p-slopes of S^D_{k+2}(K^pIw_{p^M}, ψ) are the first
   (k+1)q^{−1}p^M t ratios"** — the classical slopes are the first `N` overconvergent slopes.
   [LWX] get this from classicality (Prop 2.15, `lwx.txt:913–920`, whose proof is [Bu04, Prop 4]
   and uses Jacquet–Langlands in one direction, `JL-AUDIT.md` §2).  As in `Touching.lean`, we
   use instead: the classical slopes are `≤ k+1` (H1 and `‖U_p‖ ≤ 1`), the complement's are
   `≥ k+1` (the theta intertwining, `le_unitSlope_compl`, general in `h`), and the polygon of a
   product starts with the smaller factor (`unitSlope_newtonPolygon₀OfPowerSeries_mul_of_forall_le`,
   `PhD/NewtonPolygons/Product.lean`).
3. **"by Atkin–Lehner theory (Proposition 3.22)"** at conductor `p^M` — H1 at level `h`, whose
   source proof is Jacquet–Langlands (`lwx.txt:1770–1789`) and which `lwx-h1` replaced at level
   `1` by the double-coset identity.  The identity is the same at level `h` with the level-`p^{h+1}`
   Atkin–Lehner element; the one new ingredient is the conductor being *exactly* `p^{h+1}`
   (`nebCharH (1 + p^h)` a primitive `p`-th root of unity), which is what [LWX, §2.1] means by
   "a finite character of conductor p^m … factors through (ℤ/p^mℤ)^× but not (ℤ/p^{m−1}ℤ)^×"
   (`lwx.txt:462–464`).

Then "the relations" are the reflection of the *sorted* classical slopes, which is
[LWX, Prop 3.22]'s displayed form "α_i(ψ) = k + 1 − α_{(k+1)q^{−1}p^mt−1−i}(ψ^{−1})"
(`lwx.txt:1765`): the multiset identity `roots(A') = {p^{k+1}/x}` of `roots_charpoly_of_atkinLehnerHypothesis`
turned into an identity of ordered unit slopes by counting roots in balls
(`toReal_unitSlope_charpolyRev_reflect`, from `PhD/NewtonPolygons/RootFaces.lean`).

**The source ranges over every classical weight.**  "We look at weights of the form (k, ψ) for
all k ≥ 0" (`lwx.txt:2322`); "Replacing ψ by ψω₀⁻¹ and k by k + 1, we get
α̃_{(k+2)q^{−1}p^Mt−1−i}(ψ^{−1}|_Δ·ω₀^{k+2}) = (k+2)q^{−2}p^M − α̃_i(ψ|_Δ·ω₀^k). We thus deduce
that (4.2.5) …" (`lwx.txt:2351–2355`); "for any character ω of Δ and j ∈ Z_{≥0}, write
j = (k+1)q^{−1}p^Mt − 1 − i for some k ∈ Z_{≥0} and i ∈ [0, q^{−1}p^Mt − 1]. Choose ψ so that
ψ|_Δ·ω₀^k = ω. It then follows from (4.2.5) that (4.2.6) α̃_{j+q^{−1}p^Mt}(ωω₀²) = α̃_j(ω) +
q^{−2}p^M. In particular, since ω₀^{ϕ(q)} = 1, we have α̃_{j+(p−1)p^{M−1}t/2}(ω) = α̃_j(ω) +
ϕ(q)p^M/(2q²)" (`lwx.txt:2356–2363`).  Each use of "Atkin–Lehner theory" at a weight `(k, ψ)`
needs the adelic data (a section and a Hecke character) at that weight; the unit band that the
slope reading consumes needs it at *every* `(ω, k)` at conductor `p²`; and the `U_p`-datum must
be the same throughout.  Hence the **family** structures `AtkinLehnerFamily` (level `1`, all
`(ω, k)`, one section) and `AtkinLehnerFamilyH` (level `h`, all `(ω, k)`, over the same
section): with them the unit-band hypotheses disappear and (4.2.5)–(4.2.6) are the two
instances `(ω, k)`, `(ω, k+1)` of the reflection, subtracted, plus the character arithmetic
`partnerChar p ω (k+1) = partnerChar p ω k · ω₀²`, `partnerChar p (ω⁻¹ω₀^{2k}) k = ω`,
`ω₀^{p−1} = 1`.

**The classical points at conductor `p^{h+1}`.**  [LWX, §2.1] (`lwx.txt:466–478`):
"(when p > 2) v(T_{(k,ψ)}) ≥ 1 if m = 1, and v(T_{(k,ψ)}) = 1/p^{m−2}(p−1) if m ≥ 2".  The
`T`-coordinate `T_{(k,ψ)} = χ(exp p) − 1 = ζ·exp(pk) − 1` has **the same formula** as at level `1`
(`classicalPoint p k ζ`, `weightPoint p s ζ`), with `ζ = ψ(exp p)` now a primitive `p^h`-th root
of unity; so no new point is defined — only the root-of-unity input changes
(`‖ζ − 1‖^{p^{h−1}(p−1)} = ‖p‖` from `Φ_{p^h}(1) = p`).

## Jacquet–Langlands dependencies (standing requirement)

**The per-result audit is `.mathlib-quality/lwx-stepone/JL-AUDIT.md`; read it before working any
ticket.**  This board imports no result whose source proof uses Jacquet–Langlands:

* Prop 3.22 at conductor `p^{h+1}` is *proved* here by the double-coset expansion (Parts L/W/I at
  level `h`), exactly as `lwx-h1` did at level `1`; the classical statement is Miyake
  Thm 4.6.17 as cited at `bu04.txt:1122–1124`.
* Prop 2.15 (classicality) is **not used**: the identification of the classical slopes with the
  first `N` slopes goes through H1 + `‖U_p‖ ≤ 1` + the theta complement bound + the product
  polygon (input 2 above), the route `Touching.lean` and `StepThree.lean` already take.
* Cor 3.21 (Hida) is not needed by the reflection (it enters only the degree formula, out of scope).

On completion, `JL-AUDIT.md` gains an addendum: "Prop 3.22 at every conductor `p^{h+1}`, `h ≥ 1`,
avoided concretely" (ticket CLEANUP-FINAL).

## References

- [LWX] `.mathlib-quality/tate-riesz/references/lwx.txt`: §2.1 (`453–478`, characters of conductor
  `p^m`, `v(T_{(k,ψ)})`), §2.2 (`481–490`, `Iw_{p^m}`), Prop 2.15 (`913–920`), Cor 3.21 and
  (3.21.1) (`1743–1760`), Prop 3.22 (`1763–1790`), §3.23 Step I (`1792–1846`, incl. (3.23.1)),
  Thm 1.5 (`175–192`), Lemma 4.1 (`2196–2226`), §4.2 (`2229–2366`, esp. `2322–2366`).
- [Bu04] `.mathlib-quality/lwx-stepone/references/bu04.txt`: `633` (`(f|η)(g) = f(gη⁻¹)·η_p`),
  `1103–1128` (Prop 4).
- Level-`1` files, whose proofs the tickets transplant line by line:
  `PhD/LWX/{Touching, ClassicalPoint, TargetPoint, NebChar, AtkinLehnerLocal, AtkinLehnerMap,
  AtkinLehnerIdentity, StepThree, DegreeFormula}.lean`; every ticket names the level-`1`
  declaration and its line.
- Boards `lwx-h1` (`plan.md`, `decomposition.md` — the derivations of W-f and I-f), `lwx-theta`
  (tranche 5: why classicality is not needed), `lwx-slopes` / `lwx-seam-m` (the level-`h` slope
  reading and seam).

## Mathlib and project inventory (verified by `grep`/`#check`, 2026-09-11)

Mathlib: `Polynomial.eval_one_cyclotomic_prime_pow` (`eval 1 (cyclotomic (p^(k+1)) R) = p`),
`Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots`, `Polynomial.eval_prod`, `mem_primitiveRoots`
(`0 < k`), `IsPrimitiveRoot.card_primitiveRoots`, `IsPrimitiveRoot.pow_iff_coprime`,
`IsPrimitiveRoot.eq_pow_of_pow_eq_one` (`[NeZero k]`), `IsPrimitiveRoot.pow_of_dvd`,
`IsPrimitiveRoot.pow_of_coprime`, `IsPrimitiveRoot.inv`, `IsPrimitiveRoot.geom_sum_eq_zero`,
`IsPrimitiveRoot.pow_eq_one_iff_dvd`, `Nat.totient_prime_pow` (`0 < n`),
`Nat.exists_mul_mod_eq_one_of_coprime` (`Mathlib/Data/Int/GCD.lean:140`),
`Nat.Prime.dvd_choose_self`, `Nat.Prime.dvd_choose_pow_iff` (`Mathlib/Data/Nat/Multiplicity.lean:266`),
`PadicInt.toZModPow`, `PadicInt.ker_toZModPow`, `PadicInt.norm_le_pow_iff_mem_span_pow`,
`PadicInt.zmod_congr_of_sub_mem_span`, `PadicInt.cast_toZModPow`, `ZMod.val_natCast`,
`Matrix.GeneralLinearGroup.mkOfDetNeZero`, `mul_eq_one_comm`, `Multiset.card_filter`,
`Multiset.filter_map`, `Polynomial.natDegree_eq_card_roots` (with `IsAlgClosed.splits`).

Project (all general in `h` unless marked): `TH`, `haloExponentH`, `haloCharFunH(_psi)`,
`haloWeightH`, `autFactor_haloWeightH`, `specialize_univChar_eq_padicExp` (`‖u−1‖ ≤ p⁻¹^(h+1)`),
`levelBounds_M1Kh`, `mem_M1Kh_iff`, `mem_Mh_iff` (`HaloWeightH.lean`); `discImage`, `discConjMat`,
`discConj`, `discConjK`, `discConjMat_mem_Mh`, `discSlash`, `blockProj_discSlash` (`DiscModel.lean`);
`DiscForms`, `mem_discForms_iff`, `discHeckeOperator`, `discEvalAtReps(_apply)`,
`bijective_discEvalAtReps_of_stabilizer_eq_bot`, `discHeckeBlockOp`, `discEvalAtReps_discHeckeOperator`,
`discHeckeCharPowerSeries`, `isCompactoid_discHeckeBlockOp` (`DiscForms.lean`); `certM1`, `certConj`,
`certConj_apply_one_one`; `IsClassicalShape`, `mem_locPolyDegSubmoduleBlock_discHeckeBlockOp_of_isClassicalShape`,
`classicalMatrix`, `classicalCoordMatrix`, `charPowerSeries_eq_mul_of_stable`,
`charpolyRev_classicalCoordMatrix_eq_charpolyRev_upMatrix`, `height_le_negLogNorm_det`,
`coeff_charpolyRev_card`, `neg_log_norm_det_add_of_mul_eq_smul`, `det_ne_zero_of_mul_eq_smul'`,
`det_ne_zero_of_mul_eq_smul_conj`, `lwxLambda_mul_le_height_specCharSeries`,
`two_mul_lwxLambda_touchX` (ℕ, general `k`) (`Touching.lean`, `UpperPolygon.lean`);
`IsClassicalShape'`, `norm_le_of_eigen_compl`, `le_unitSlope_compl`,
`norm_le_one_of_isRoot_charpoly_upMatrix`, `exists_evalT_eq_zero_of_unitSlope_eq` (`StepThree.lean`);
`upMatrix`, `AtkinLehnerHypothesis`, `roots_charpoly_of_atkinLehnerHypothesis`
(`AtkinLehnerInst.lean`); `roots_charpoly_atkinLehner`, `norm_roots_charpoly_atkinLehner`,
`atkinLehner`, `Iw`, `mem_Iw_iff` (`AtkinLehner.lean`); `Matrix.roots_charpolyRev`
(`TateFredholm/CharpolyPairing.lean`); `finrank_locPolyDegSubmoduleBlock`,
`finite_locPolyDegSubmoduleBlock`, `IsStepOneTouching`, `hasUnitBand_of_isStepOneTouching`
(`StepOne.lean`); `HasUnitBand`, `hasUnitBand_zero` (`Vertices.lean`); `specCharSeries_ofCerts_eq_discHeckeCharPowerSeries`
(`SeamH.lean`); `unitSlope_discHeckeCharPowerSeries_eq_slopeRatio`, `slopeRatio`, `shapePolygon`
(`SlopesSeam.lean`, `SlopeRatios.lean`); `unitSlope_newtonPolygon₀OfPowerSeries_mul_of_forall_le`,
`height_mul_le_height_right` (`NewtonPolygons/Product.lean`, `Touching.lean`);
`faceRight_eq_card_roots_le_self`, `faceLeft_eq_card_roots_lt_self`, `unitSlope_ne_top_of_lt_natDegree`
(`NewtonPolygons/RootFaces.lean`); `unitSlope_le_of_lt_faceRight`, `lt_unitSlope_of_faceRight_le`,
`le_unitSlope_of_faceLeft_le`, `faceLeft_le_of_le_unitSlope`, `SlopesUnbounded` (`NewtonPolygons/Face.lean`);
`symAct` and its laws, `kappaSlash_eq_smul_symAct_of_shape` (`SymPow.lean`, level-free);
`vQ`, `sQ`, `vQ_mem_M1`, `sQ_mem_Iw`, `Iw_one_le_M1`, `norm_det_fin_two_le_one`
(`AtkinLehnerLocal.lean`, level-free); `vGL`, `sGL`, `pGL`, `sGL_mul`, `sGL_inv`, `theta_mem_Iw`
(`AtkinLehnerMap.lean`, level-free); `partnerChar(_apply)`, `oneAddPMul`, `coe_oneAddPMul`,
`continuous_zeta_pow_toZMod`, `oneUnitPart_oneAddPMul`, `norm_logQuot_oneAddPMul_one`
(`NebChar.lean`, the level-`1` templates); `weightPoint(_natCast)`, `targetChar(_apply)`,
`mk_choose_neg_natCast_mul_pow`, `mk_choose_natCast_mul_pow`, `coe_eq_teichRes_mul_oneUnitPart`,
`continuous_padicExp_mul_intHom`, `intHom_oneUnitPart_eq_padicExp`, `PadicExpLog.padicExp_natCast_mul`,
`padicExp_add`, `norm_padicExp_sub_one_le`, `padicLog_padicExp`, `padicExp_padicLog`, `norm_padicLog_eq`
(`TargetPoint.lean`, `ClassicalPoint.lean`, `PadicExpLog`, level-free); `specialize_univChar`
(`Specialize.lean`), `univChar_mul`, `logQuot`, `qlog`, `oneUnitPart`, `teichRes` (`IntegralModel.lean`,
`UnitsLog.lean`, `HaloWeight.lean`).

**Level-`1`-specific and therefore duplicated at level `h`** (never reused as is): `ClassicalData`,
`classicalData`, `isStepOneTouching_of_atkinLehnerHypothesis`, `two_mul_lwxLambda_touchX_mul_eq`,
`touchX_succ_eq` (`Touching.lean`); the `classicalPoint`/`weightPoint` norm and `TH`/halo-exponent
lemmas, `autFactor_haloWeightH_classicalPoint`, `isClassicalShape_haloWeightH_classicalPoint`
(`ClassicalPoint.lean`); `TargetData`, `targetData_classicalPoint`, `specialize_univChar_targetChar`,
`oneAddPow_weightPoint_mul_padicExp`, `autFactor_haloWeightH_weightPoint_neg`,
`isClassicalShape'_haloWeightH_weightPoint_neg` (`StepThree.lean`, `TargetPoint.lean`);
`nebCharK`, `nebChar` and all of `NebChar.lean` after `oneAddPMul`; `wQ`, `ℓQ`, `tMat` and the disc
bookkeeping of `AtkinLehnerLocal.lean`; `wGL`, `ℓGL`, `atkinLehnerK`, `AtkinLehnerData`, `discShift`,
`locPolyForms`, `ClassicalDiscForms`, `discHeckeOperatorCl`, `atkinLehnerFun(Inv)`, `atkinLehnerMap(Inv)`,
`atkinLehnerEquiv`, `discEvalAtRepsCl` (`AtkinLehnerMap.lean`); all of `AtkinLehnerIdentity.lean`;
`norm_pow_le_of_mem_roots_charpoly_matrix`, `unitSlope_charpolyRev_matrix_le`, the private
`specCharSeries_eq_mul_charpolyRev` (`StepThree.lean`).

## File structure

All new files; no completed file is edited (the level-`1` files stay as the `h = 1` specialisation,
bridged by `ClassicalData.toH`, `AtkinLehnerData.toH`, `wQH_one`, `ℓQH_one`, `tMatH_one`,
`wGLH_one`, `oneAddPPowMul_one`).  Import order:

| Part | File | Content | Level-`1` template |
|---|---|---|---|
| T | `PhD/LWX/TouchingH.lean` | `ClassicalDataH`, (3.23.1) at level `h`, the touching, `ClassicalData.toH` | `Touching.lean:555–786` |
| C | `PhD/LWX/ClassicalPointH.lean` | primitive `p^h`-th roots, `weightPoint`/`classicalPoint` at conductor `p^{h+1}`, the classical shape, `classicalDataH` | `ClassicalPoint.lean`, `TargetPoint.lean:133–225` |
| G | `PhD/LWX/TargetPointH.lean` | target shape, AG-ζ at level `h`, `TargetDataH`, `targetData_classicalPointH` | `TargetPoint.lean:255–526`, `StepThree.lean:350–376` |
| N | `PhD/LWX/NebCharH.lean` | `oneAddPPowMul`, `nebCharKH`, `nebCharH`, conductor exactly `p^{h+1}`, character sums, partner | `NebChar.lean` |
| L | `PhD/LWX/AtkinLehnerLocalH.lean` | `wQH`, `ℓQH`, `tMatH`, the key factorisation, membership, disc bookkeeping at level `h` | `AtkinLehnerLocal.lean` |
| W | `PhD/LWX/AtkinLehnerMapH.lean` | `wGLH`, `ℓGLH`, `atkinLehnerKH`, `AtkinLehnerDataH`, `discShiftH`, classical disc forms, `W`, `W'`, the block model | `AtkinLehnerMap.lean` |
| I | `PhD/LWX/AtkinLehnerIdentityH.lean` | `vRepDH`, the double-coset expansion, the identity, H1 at level `h` (**M1**) | `AtkinLehnerIdentity.lean` |
| F | `PhD/LWX/AtkinLehnerFamily.lean` | `AtkinLehnerFamily` (level `1`, every `(ω, k)`, one section), `toData`, `vRepF`, `upEltF`; `AtkinLehnerFamilyH` (level `h` over the same section), `toDataH`; the partner-character arithmetic (`invChar_eq_inv`, `partnerChar_succ`, `partnerChar_invChar_mul_teichChar_pow`, `teichChar_pow_sub_one`) | `AtkinLehnerMap.lean:149–168` (the structure), `NebChar.lean:394–404` |
| R | `PhD/LWX/ConductorSlopes.lean` | the region, the classical-slope bounds, the product splitting, the reflection lemma, the abstract slope identity; then, from the families: the unit band at every vertex (ledger row 1), the unconditional (1.5.1), the slope identity (**M2**), (4.2.5), (1.5.2), the arithmetic progressions (**M3**) | `StepThree.lean:415–450, 576–583`, `SlopesSeam.lean` |

`PhD.lean` imports all nine (block "Board `lwx-conductor`").

## Design decisions

1. **`h` is the analyticity level; the conductor is `p^{h+1}`; `ζ` is a primitive `p^h`-th root
   of unity; `0 < h` is an explicit hypothesis wherever `p^{h−1}` occurs.**  This matches the
   whole existing level-`h` API (`TH p h`, `haloWeightH h`, `ZMod (p^h)`, `AtkinLehnerHypothesis ψ h k`,
   `locPolyDegSubmoduleBlock … h k`).  The alternatives (index by `h+1`, or by the conductor
   exponent `m` with `m − 1` everywhere) were rejected: the first makes level `1` read as `0 + 1`,
   the second puts natural subtraction into every `ZMod`.  `h = 0` (conductor `p`, tame) is not in
   the theory (the classical points are not in the halo annulus); the `h − 1` in `hnorm` makes
   `ClassicalDataH 0` look like level `1`, harmlessly, and no statement claims anything at `h = 0`
   except the unconditional algebraic identities.
2. **New `H`-suffixed files, level `1` untouched.**  Precedent: `HaloWeightH.lean`, `SeamH.lean`,
   `QuaternionicH.lean` (board `lwx-seam-m`).  In-place generalisation would rewrite ~5000 lines of
   completed, protected code with the build red until done; here the build stays green and every
   ticket has its level-`1` proof next to it as a template.  Bridges (`toH`, `_one`) document the
   specialisation.  Retiring the level-`1` files later is the user's call.
3. **The unchanged objects are reused, not duplicated**: `classicalPoint`, `weightPoint`, `vQ`, `sQ`,
   `vGL`, `sGL`, `pGL`, `partnerChar`, `targetChar`, `symAct`, `oneAddPMul`, `Iw p 1`, `levelM1`,
   `AtkinLehnerHypothesis`, `upMatrix`, `classicalMatrix`.  Only their *hypotheses* change
   (`IsPrimitiveRoot ζ (p^h)`), so the level-`h` lemmas about them carry the suffix `_prime_pow`
   (or drop the `_one`: `TH_weightPoint`, `haloExponentH_weightPoint`); the new *definitions* and
   the lemmas about them carry `H`.
4. **`p^{2h−1}` and `b p^{h−1}` are written `p^h·p^h/p` and `b·p^h/p` in `ℚ_p`** (Parts L, W, I),
   so every algebraic identity (`ℓQH_mul_ℓQHinv`, the key factorisation, `term_elt_eqH`) holds
   for all `h` with no side condition and `ℓGLH` needs no proof of `0 < h` inside a definition;
   `0 < h` enters only the integrality statements (`ℓQH_mem_Iw`, `nebK_one_sub_eq_invH`, the disc
   bookkeeping) and the disc index `b·p^{h−1}` as a natural number.
5. **The disc-coordinate translation `(1, −b/p; 0, 1)` is the same at every level** (`t₀⁻¹ s_{−b p^{h−1}} t₀`
   with `t₀ = (p^h 0; 0 1)`), so `atkinLehner_term_eqH`'s right-hand side is the level-`1` one
   with the disc index `b` replaced by `b p^{h−1}` and `nebK(1 + bcp)` by `nebK(1 + bcp^h)`.
6. **`AtkinLehnerDataH θG ψ U h Γ nebK`**: the same data as level `1` except `χ_wGLH` and the
   normalisation on the level-`p^{h+1}` part `‖(θG u) 0 1‖ ≤ p^{−h}`.  The section `ιp`, the central
   element and `χ` do not depend on `h` — the ψ-varying board can share them across levels.
7. **Classicality is not used** (input 2 of the source reading): the slopes of the classical
   factor are bounded by H1 and `‖U_p‖ ≤ 1` from above and the theta complement from below, and
   the product polygon splits (`unitSlope_newtonPolygon₀OfPowerSeries_mul_of_forall_le`).  This is
   why `TargetPointH.lean` (the theta target at level `h`) is on the board although Step III is not.
8. **The reflection is a general Newton-polygon lemma** (`toReal_unitSlope_charpolyRev_reflect`):
   given `roots(A') = {c/x : x ∈ roots(A)}`, the sorted slopes reflect.  Proof by counting roots
   in balls (`faceRight_{A'} σ = n − faceLeft_A(v(c) − σ)`) and the face API — no new infrastructure.
9. **The adelic data is a family over `(ω, k)` with one section** (`AtkinLehnerFamily`,
   `AtkinLehnerFamilyH`; user decision 2026-09-11).  The unit band at every vertex needs Step I at
   every classical weight of conductor `p²` on every disc, hence a Hecke character `χ ω k` for
   every `(ω, k)`; the `U_p`-datum must not depend on `(ω, k)`, so the section `ιp` is shared and
   `vRepD (AtkinLehnerFamily.toData θG ψ U F ω k) = vRepF F` holds **definitionally** (`toData` is a structure literal over
   `F.ιp`).  The level-`h` characters live over the same section (`AtkinLehnerFamilyH F h ζh`), so
   the level-`h` `UpDatum` is again `vRepF F`'s.  The abstract slope identity
   (`slopeRatio_add_slopeRatio_eq_of_atkinLehnerHypothesisH`) keeps `hband`/`hband'` as
   hypotheses; every downstream statement discharges them by `hasUnitBand_of_atkinLehnerFamily`.
10. **H1 is symmetric** (`atkinLehnerHypothesis_symm`: `B' := P A Q`), which lets the classical-slope
    bounds at the partner point reuse the unprimed lemmas instead of a second family.
11. **(4.2.5)–(4.2.6) are corollaries of the reflection, not new analysis**: (4.2.5) is the
    reflection at `(ω, k)` minus the reflection at `(ω, k+1)` (same disc `ω`, partner discs
    `ω⁻¹ω₀^{2k}` and `ω⁻¹ω₀^{2k+2}`); (4.2.6) at `(ω', j)` is (4.2.5) at the disc
    `ω := ω'⁻¹ω₀^{2k}`, `k := j/(p^h t)`, `i := N_k − 1 − j`; the progressions iterate (4.2.6)
    `(p−1)/2` times and use `ω₀^{p−1} = 1`.  The character identities are pure group theory in
    `(ℤ/p)^× →* ℤ_p^×` (`invChar ω = ω⁻¹`, Fermat in `(ℤ/p)^×` through `teichRes_mul`).

## Dependency graph

Ticket IDs are those of `tickets.md`; within a part the file order **is** the dependency order.
Cross-part edges: C needs T (`ClassicalDataH`); G needs C; N needs G (only `classicalDataH`,
`targetData` are not needed — N needs C and T through G's import); L is independent; W needs N and L;
I needs W; F needs I (only the structures; its four lemmas are independent); R needs I, F, G and
`SlopesSeam`.  Parts T+C+G+N (the point layer), Part L (pure matrices) and Part F's character
lemmas are independent and can be worked in parallel; W after N and L; I after W; R last.

```
Part T (6):  T1 touchX_mul_prime_pow, T2 two_mul_lwxLambda_touchX_mul_eq_prime_pow,
             T3 ClassicalDataH.mul_neg_log_norm_eq, T4 ClassicalDataH.norm_eq, T5 ClassicalData.toH,
             T6 isStepOneTouching_of_atkinLehnerHypothesisH
Part C (19): C1 norm_eq_one_of_pow_eq_one … C6 inv_lt_norm_sub_one_of_isPrimitiveRoot_prime_pow (roots),
             C7–C13 weightPoint at conductor p^{h+1}, C14–C18 classicalPoint corollaries,
             C19 autFactor_haloWeightH_classicalPoint_prime_pow
Part G (5):  G1 autFactor_haloWeightH_weightPoint_neg_prime_pow, G2 oneAddPow_weightPoint_mul_padicExp_prime_pow,
             G3 specialize_univChar_targetChar_prime_pow, G4 targetConst_eq_classicalDataH_u,
             G5 targetData_classicalPointH
Part N (25): N1 coe_oneAddPPowMul … N25 classicalDataH_partnerChar_u
Part L (36): L1 wQH_one … L36 discConj_sQ_zero_prime_pow
Part W (40): W1 coe_wGLH_inv … W40 discEvalAtRepsClH
Part I (15): I1 vRepDH_mem_levelM1 … I15 atkinLehnerHypothesis_of_atkinLehnerDataH   [M1]
Part F (4):  F1 invChar_eq_inv, F2 partnerChar_succ, F3 partnerChar_invChar_mul_teichChar_pow, F4 teichChar_pow_sub_one
             (the structures, `toData`/`toDataH`, `vRepF`, `upEltF` and the `rfl` lemmas carry no sorry)
Part R (17): R1 inv_pow_lt_norm_pow_of_norm_pow_eq … R9 slopeRatio_add_slopeRatio_eq_of_atkinLehnerHypothesisH,
             R10 hasUnitBand_of_atkinLehnerData, R11 hasUnitBand_of_atkinLehnerFamily,
             R12 unitSlope_discHeckeCharPowerSeries_eq_slopeRatio_of_atkinLehnerFamily,
             R13 slopeRatio_add_slopeRatio_partnerChar_of_atkinLehnerFamilyH   [M2],
             R14 slopeRatio_partnerChar_succ, R15 slopeRatio_mul_teichChar_sq (1.5.2),
             R16 slopeRatio_mul_teichChar_pow, R17 slopeRatio_add_period   [M3]
```

Milestones: **M1 = I15** (preceded by CLEANUP-ALL-1), **M2 = R13** (preceded by CLEANUP-ALL-2)
and **M3 = R17** (preceded by CLEANUP-ALL-3).

## Cleanup cadence (algorithmic)

Per file, a `[CLEANUP-…]` ticket after every third proof/definition ticket and a final per-file
cleanup after the last; `CLEANUP-ALL-1` before I15, `CLEANUP-ALL-2` before R13, `CLEANUP-ALL-3`
before R17; `CLEANUP-FINAL` last (it also writes the `JL-AUDIT.md` addendum and updates
`PhD.lean`'s comment to "complete, sorry-free").  Cleanup tickets are done inline by the main agent.  `lake exe runLinter
PhD.LWX.<Module>` is part of every cleanup.  Engineering rules inherited from `lwx-h1`
(`tickets.md` Summary there): never `set` an abbreviation that lemma instantiations re-introduce
unfolded; `congr 1` on `ψ.mapMatrix (big term)` / `toMatrix` can time out — state a generic-matrix
identity instead; `simp [Matrix.mul_apply]` with a generic matrix folds into `vecMul` — run
`simp only [Matrix.mul_apply, Fin.sum_univ_two]` first; inline `(⟨x, h⟩ : ℤ_[p])` loses `Norm` —
use `let z : ℤ_[p] := ⟨x, h⟩`; `omit … in` before the docstring; `include hU in` where a section
hypothesis is used only in the proof; `omega` not `lia`; no `timeout` binary.

## Planning-pass notes

* The generalisation is **mechanical for Parts L/W/I** (replace `1 → h`, `p → p^h` at the marked
  places, `p⁻¹^2 → p⁻¹^(h+1)`, `wQ → wQH`, …): each ticket cites the level-`1` proof line range to
  transplant.  The genuinely new mathematics is in Parts C (prime-power roots of unity), N (the
  conductor is exactly `p^{h+1}`, through `toZModPow h`) and R (the reflection lemma and the slope
  identification).
* Estimated size: 167 proof/definition tickets, ~62 cleanup tickets; Parts L/W/I ≈ 2100 lines,
  the point layer ≈ 900 lines, F + R ≈ 700 lines.
* Revision 2026-09-11 (user: "fold `hband`/`hband'` into this board"): the first draft took the
  unit bands as hypotheses of the slope identity and left (4.2.5)–(4.2.6) to a follow-on board.
  The family structures (design decision 9) remove both restrictions; the whole of [LWX,
  Thm 1.5]'s second half at the polygon level is now on the board (R11–R17).
* The adversarial pass found and repaired three defects before ticketing (`decomposition.md` §2:
  L-a's `ℓGLH` needed `0 < h` inside a definition — fixed by the `p^h·p^h/p` spelling; the touching
  index is a level-`1` vertex, so the theorem is stated at `touchX p t ((k+1)p^{h−1})`, not at a new
  `touchXH`; the reflection needed the partner's slope bounds, supplied by `atkinLehnerHypothesis_symm`
  rather than a duplicated family).
