# Development Plan — `lwx-h1` (hypothesis H1: the Atkin–Lehner symmetry, both parts)

**BOARD PATH: `.mathlib-quality/lwx-h1/`.**  The default `.mathlib-quality/` board is the
completed NewtonPolygons project — never touch it.  A parallel run owns `.mathlib-quality/qmf/`
and its `beastmode_active` sentinel — never touch that either.  Every `/beastmode` run must name
this board path explicitly.  Planned 2026-09-10.

## STATUS: COMPLETE (2026-09-10, `/beastmode`)

All tickets done; the five modules are sorry-free and linter-clean.  **Milestone
`LWX.degX_succ_of_atkinLehnerData`** — [LWX, Thm 1.3]'s degree formula with no hypothesis left,
granted the adelic data — depends only on `[propext, Classical.choice, Quot.sound]`.  Two
statement repairs were logged in `b2_log.jsonl` (both strict weakenings, see `tickets.md`
Summary).  `PhD/Test/AtkinLehnerIdentity.lean` is now superseded by `AtkinLehnerLocal.lean` /
`AtkinLehnerIdentity.lean`; deleting it is the user's call.

## Goal

Hypothesis **H1** — `AtkinLehnerHypothesis ψ h k A B A'` in `PhD/LWX/AtkinLehnerInst.lean`,
[LWX, Prop 3.22] at the level of the classical matrices — is the last hypothesis of the
Step I / Step III development (`lwx-theta-h2` removed H2).  It has two clauses:

* **H1b**, the operator identity `A * B = p^{k+1} • 1`;
* **H1a**, the conjugation `A' = P * B * Q`, `Q * P = 1`, relating `U_p` at the partner
  nebentypus to `B`.

This board proves both at the classical points of `ClassicalPoint.lean`, with `B := W⁻¹ A' W`
for `W` the Atkin–Lehner map, so that H1a is the definition of `B` and H1b is the single
operator identity **`U_p ∘ W⁻¹ ∘ U_p^{(ψ⁻¹)} ∘ W = p^{k+1}`** on the classical forms of `(k, ψ)`.
Its proof is the double-coset expansion recorded in the scratch file
`PhD/Test/AtkinLehnerIdentity.lean`: the products of a `U'_p`-representative with a
`U_p`-representative factor as (Iwahori element) × (central `p`) × (translation), the central
term contributes `p · p^k`, and the non-central terms are killed by a character sum because the
nebentypus has conductor **exactly** `p²`.

**Deliverables**:
* `LWX.atkinLehnerHypothesis_of_atkinLehnerData` — H1 at the classical points, with the partner
  datum at the nebentypus `ω⁻¹ω₀^{2k}` (`partnerChar`) and the point `T_{χ_k}(ζ⁻¹)`.  This
  closes the other half of the old gap **AG-ω₀** as a by-product (`nebChar_partnerChar`).
* `LWX.degX_succ_of_atkinLehnerData` — [LWX, Thm 1.3]'s degree formula
  `deg X_{k+1,ω} = r_ord(ω⁻¹ω₀^{2k}) + r_ord(ωω₀^{−2k−2})` with **no hypothesis left**, granted
  the adelic data (`AtkinLehnerData`, neatness, and the `U_p`-certificates, exactly as every
  other statement of the development is granted them).

**Out of scope**: instantiating `AtkinLehnerData` for the finite adèles of a definite
quaternion algebra (`PhD/LWX/Quaternionic.lean`'s `Dfx ℚ D`) — the section of the
`p`-component, neatness, and the Hecke character `ψ_A ∘ ν` from class field theory; the
`p^M`-conductor version needed by [LWX, Thm 1.5]'s second half; `p = 2`.

## The reading of the source, and the honest status of the avoidance

[LWX, Prop 3.22]'s proof (`lwx.txt:1773–1789`) goes through Jacquet–Langlands plus the
classification of the local component; that route is ruled out by the standing constraint
(`.mathlib-quality/lwx-stepone/JL-AUDIT.md`, item 1: "avoidance **not yet concrete**").  The
board `lwx-atkinlehner` reduced Prop 3.22 to the operator identity and the Atkin–Lehner
conjugation; `JL-AUDIT.md` recorded that "the double-coset argument must **not** be ticketed
until a source is found or a reviewer confirms it".  Since then the scratch file
`PhD/Test/AtkinLehnerIdentity.lean` **proved every matrix identity of that argument**
(sorry-free), so what was a conjectured route is now a verified computation; what it lacked was
the seam to the forms.  This board is that seam.  The classical statement is Miyake, *Modular
forms*, Thm 4.6.17 (`|a_p|² = p^{k−1}` at nebentypus of conductor equal to the level), as cited
by Buzzard at `bu04.txt:1122–1124`; the local mechanism ("`U_p` is invertible at ramified
nebentypus") is Casselman, *On some results of Atkin and Lehner*, Math. Ann. 201 (1973).  Neither
text is to hand; the identities are proved here from scratch, and every leaf below cites either
[LWX]/[Bu04] for its *statement* or the scratch file for its *verification*.

**Where the twist comes from.**  LWX's proof twists "by a central Hecke character associated to
`ψ⁻¹`" (`lwx.txt:1783–1785`).  Without it, `φ ↦ φ ∣ w` lands in the space with nebentypus
`u ↦ ψ⁻¹(d)·ψ(det u)`, not `ψ⁻¹` (conjugation by `w` swaps `a` and `d`, and `ad ≡ det (mod p^m)`).
The twist is the Hecke character `χ = ψ_A ∘ ν` of the reduced norm, trivial on `D^×` and equal to
`ψ(det)` on the level.  In the abstract group `G` of the development it is *data*
(`AtkinLehnerData.χ`), like the certificates are; its existence for `D^×` is class field theory
(the character of `∏_l ℤ_l^×` extends uniquely to `A^×/ℚ^×`, `ℚ^× ∩ (ℝ_{>0}∏ℤ_l^×) = 1`).

**Where the central element comes from.**  The `b = 0` terms of the expansion are
`p · φ(x·p_p⁻¹) ∣_k (p·1) = p·p^k·φ(x)` **only if the central element `p_p ∈ ℚ_p^× ⊂ G` acts
trivially**, which holds when `p_p = p_global·(p^{(p)})⁻¹` with `p_global ∈ D^×` central and
`(p^{(p)})⁻¹ ∈ K^p` (the tame level contains the away-from-`p` scalars).  This is
`AtkinLehnerData.central`, again data.  It is a genuine hypothesis on the tame level (a full
level-`l` structure does not contain it unless `p ≡ 1 (mod l)`); [LWX] never state it because
their proof produces the central character from the automorphic representation.

## Jacquet–Langlands dependencies (standing requirement)

**The per-result audit is `.mathlib-quality/lwx-stepone/JL-AUDIT.md`; read it before working any
ticket.**  This board imports no result whose source proof uses Jacquet–Langlands:
Prop 3.22 is *proved* here by the double-coset expansion, the classical citations above are for
the statement only, and the two other Jacquet–Langlands uses in the audit (Buzzard Prop 4's
second half, Buzzard Thm 2) were already removed by taking H1 as the hypothesis they derive
from.  On completion, `JL-AUDIT.md` item 1 becomes "avoided concretely" and the whole
development is Jacquet–Langlands-free granted the adelic data.

## References

- [LWX] `.mathlib-quality/tate-riesz/references/lwx.txt`: §2.1 (`456–470`, classical characters),
  §2.2 (`481–490`, `Iw_{p^m}`; `520–537`, the anti-involution), §2.3 (`549–660`, the induced
  representation, (2.3.2), the monoid `M₁`, the algebraic subspace `LP^{m−1,≤k}`), §2.4–2.5
  (`671–716`, the classical space, neatness, `U_p` with `v_j = (p 0; jq 1)`), §2.11 (`841–866`),
  Prop 3.22 (`1763–1789`), §3.23 (`1792–1798`, `2028–2036`).
- [Bu04] `.mathlib-quality/lwx-stepone/references/bu04.txt`: `633` (`(f|η)(g) = f(gη⁻¹)·η_p`),
  `645–649` (Hecke operators), `1093–1100` (the Hecke relation), `1103–1128` (Prop 4).
- `PhD/Test/AtkinLehnerIdentity.lean` — the scratch file: `upRep_mul_upAdjRep`,
  `obstruction_mul_lowerUni`, `det_conjTwist`, `conjTwist_mem_Iw`, `sum_diagUnit_eq_zero`, all
  proved; its "What remains" section is this board's Part I.
- Boards `lwx-atkinlehner` (the reduction), `lwx-theta` / `lwx-theta-h2` (everything consumed).

## Mathlib and project inventory (verified by `#check`, 2026-09-10)

Project: `LWX.roots_charpoly_atkinLehner`, `atkinLehner`, `atkinLehnerConj_*`, `Iw`
(`AtkinLehner.lean`); `discSlash`, `blockProj_discSlash`, `discImage`, `discConj`, `discConjMat_*`
(`DiscModel.lean`); `DiscForms`, `mem_discForms_iff`, `discEvalAtReps(_apply)`,
`bijective_discEvalAtReps_of_stabilizer_eq_bot`, `discHeckeOperator`, `discHeckeBlockOp`,
`discEvalAtReps_discHeckeOperator` (`DiscForms.lean`); `heckeOperatorSlash_eq_finsetSum`,
`AutomorphicFunction.slash_apply`, `slash_apply_mul`, `left_invt'` (`QMF/Slash`);
`autFactor_mul_mobius_pow_of_shape`, `kappaSlash_mem_polySubmodule_of_shape`,
`discSlash_mem_locPolyDegSubmodule_of_shape`, `classicalMatrix`, `upMatrix`,
`AtkinLehnerHypothesis` (`Touching.lean`, `AtkinLehnerInst.lean`); `locPolyDegSubmodule(Block)`,
`locPolyDegBlockEquiv` (`Theta.lean`, `StepOne.lean`); `classicalPoint` and its lemmas,
`autFactor_haloWeightH_classicalPoint`, `classicalData` (`ClassicalPoint.lean`); `teichChar`,
`weightPoint`, `oneAddPow_weightPoint_mul_padicExp`, `intHom_oneUnitPart_eq_padicExp`,
`certConj_apply_one_one` (`TargetPoint.lean`); `invChar` (`ConjChar.lean`); `haloCharFunH_psi`,
`haloCharFunH_mul`, `specialize_univChar(_eq_padicExp)`, `PadicExpLog.norm_padicLog_eq`,
`padicExp_natCast_mul_padicLog`; `polySubmodule` (`QMF/Weight/Algebraic.lean`);
`kappaSlash_apply`, `linX`, `numX`, `mobius`; `cSpace.ofTendsto`, `cSpace.evalCLM`,
`cSpace.blockIncl/blockProj`; `degX_succ_classicalPoint` (`DegreeFormula.lean`).

Mathlib: `Matrix.GeneralLinearGroup.mkOfDetNeZero`, `IsPrimitiveRoot.{inv, pow_of_coprime,
geom_sum_eq_zero, pow_eq_one}`, `PowerSeries.coeff_mul`, `Finset.sum_mul`, `PadicInt.isUnit_iff`,
`PadicInt.toZMod`, `ContinuousLinearMap.smulRight`, `LinearEquiv.ofLinear`,
`LinearMap.toMatrix_comp`, `Matrix.mul_eq_one_comm`.  **Nothing new is needed from mathlib.**

## File structure

| File | Content | Part |
|---|---|---|
| `PhD/LWX/SymPow.lean` (new) | the homogeneous substitution `hsub`, the `Sym^k` action `symAct` on `c(ℕ,K)`, the right-action law, the bridge to `kappaSlash` at a classical shape | S |
| `PhD/LWX/NebChar.lean` (new) | the nebentypus `nebChar` at a classical point: multiplicative, conductor exactly `p²`, the character sum; the partner nebentypus `ω⁻¹ω₀^{2k}` (AG-ω₀) | N |
| `PhD/LWX/AtkinLehnerLocal.lean` (new) | `vQ, sQ, wQ, ℓQ`, the key factorisation, Iwahori/`M₁` memberships, disc-`0` bookkeeping | L |
| `PhD/LWX/AtkinLehnerMap.lean` (new) | `AtkinLehnerData`, `ClassicalDiscForms`, `U_p` on them, `shapiro_blockProj`, `W`, `W⁻¹`, `atkinLehnerEquiv`, the block model `discEvalAtRepsCl` | W |
| `PhD/LWX/AtkinLehnerIdentity.lean` (new) | the naive Hecke formula, the identity on disc `0` and as operators, transport to matrices, H1, the unconditional degree formula | I |

No existing file is edited except `PhD.lean` (imports, done).  `PhD/Test/AtkinLehnerIdentity.lean`
stays as the record (its identities are re-proved in `AtkinLehnerLocal.lean` in the disc-model
coordinate, `h = 1`); deleting it is a user decision.

## Design decisions

1. **Level `h = 1` (conductor `p²`) only.**  [LWX, §3.23] runs at "the classical weights `χ_k =
   (k,ψ)` of conductor `q²`"; the classical points of `ClassicalPoint.lean` are at conductor
   `p²`; and the conductor being *exactly* `p²` is what the character sum needs.  The disc model
   at `h = 1` has `p` discs; the Atkin–Lehner element of level `p²` is `wQ = (0 p; −p 0)` in the
   disc-model coordinate (`t₀⁻¹ wQ t₀ = (0 1; −p² 0)`).
2. **Everything is computed on disc `0`.**  Disc `a` of a level-`Iw_p` form at `x` is disc `0`
   at `x·s_a` (`shapiro_blockProj`), so `W` is defined disc-wise through `s_a` and the identity
   is proved on disc `0`, where the `U_p`-representatives conjugate to the level-`p²`
   representatives `(p 0; cp² 1)` and the scratch file's identities apply verbatim.
3. **`B := W⁻¹ A' W`, not a `U'_p` defined by representatives.**  The `U'_p`-representatives
   `(1 b; 0 p)` have non-unit `d`, so no slash action of a monoid containing them exists on
   `Sym^k ⊗ ψ` (the nebentypus is not multiplicative there — checked); defining `U'_p` as the
   conjugate makes H1a free and puts all the content in one identity.
4. **The abstract adelic data is a structure, not a construction.**  `AtkinLehnerData` bundles a
   section `ιp : GL₂(ℚ_p) →* G` of `θ`, `ιp(Iw_p) ⊆ U`, the central decomposition of `ιp(p·1)`,
   and the twist `χ` with its four properties.  All are theorems about `Dfx ℚ D` for another
   board; here they are hypotheses in the same way the certificates `(vRep, idx, uu)` are.
5. **`nebK` is an abstract function in Parts W and I**, with the four properties the proofs use
   (multiplicative on norm-one elements, non-vanishing, trivial within `p⁻²` of `1`, the character
   sum); Part N discharges them at the classical points.  This keeps `W` and the identity free of
   the classical-point specifics.
6. **The `Sym^k` action is a right action on `c(ℕ, K)`** (`symAct`), defined for every matrix
   by the column formula and proved multiplicative by the homogeneous-substitution lemma; at a
   classical-shape matrix it is `kappaSlash` divided by the constant.  This is the `Sym^k` route
   T-AG5 asked for.

## Dependency graph

Ticket IDs are those of `tickets.md`; within a part the file order **is** the dependency order
(each ticket's `Depends on` line names its exact prerequisites).  Cross-part edges: Part W needs
S15 (`kappaSlash_eq_smul_symAct_of_shape`), S10–S14 (`symAct` laws) and all of Part L; Part I
needs Part W and, at the H1 assembly and the milestone only, Part N (the `nebCharK_psi_*` and
`sum_inv_nebCharK_eq_zero` instances and the two partner-shape lemmas).  Parts S, N, L are
mutually independent and can be worked in parallel; Part W after S and L; Part I last.

```
Part S (16): S1 `hsub_mul`, S2 `hsub_linX`, S3 `hsub_numX`, S4 `coeff_mul_eq_zero_of_lt`
   S5 `coeff_pow_eq_zero_of_lt`, S6 `hsub_pow_of_degree_le_one`, S7 `hsub_linX_pow_mul_numX_pow`, S8 `polySeq_apply`
   S9 `coeff_linX_pow_mul_numX_pow_eq_zero`, S10 `symAct`, S11 `symAct_apply`, S12 `symAct_mem_polySubmodule`
   S13 `symAct_mul`, S14 `symAct_one`, S15 `symAct_smul_one`, S16 `kappaSlash_eq_smul_symAct_of_shape`

Part N (28): N1 `isUnit_one_add_p_mul`, N2 `nebChar_apply`, N3 `classicalData_u_eq_nebChar`, N4 `autFactor_haloWeightH_classicalPoint_eq_nebCharK`
   N5 `nebChar_mul`, N6 `nebChar_one`, N7 `nebChar_ne_zero`, N8 `nebChar_of_norm_sub_one_le_sq`
   N9 `continuous_zeta_pow_toZMod`, N10 `oneAddPow_sub_one_intHom`, N11 `oneUnitPart_oneAddPMul`, N12 `nebChar_oneAddPMul`
   N13 `norm_logQuot_oneAddPMul_one`, N14 `isPrimitiveRoot_nebChar_oneAddPMul_one`, N15 `nebChar_oneAddPMul_natCast`, N16 `sum_nebChar_oneAddPMul_mul_eq_zero`
   N17 `sum_inv_nebChar_oneAddPMul_mul_eq_zero`, N18 `sum_inv_nebCharK_eq_zero`, N19 `nebCharK_psi_mul`, N20 `nebCharK_psi_ne_zero`
   N21 `nebCharK_psi_of_norm_sub_one_le_sq`, N22 `partnerChar_apply`, N23 `oneAddPow_inv_sub_one_mul`, N24 `nebChar_eq`
   N25 `nebChar_partnerChar`, N26 `nebCharK_partnerChar`, N27 `autFactor_haloWeightH_partner_eq_inv_nebCharK`, N28 `classicalData_partnerChar_u`

Part L (39): L1 `det_vQ`, L2 `det_sQ`, L3 `det_wQ`, L4 `det_ℓQ`
   L5 `wQ_mul_wQinv`, L6 `wQinv_mul_wQ`, L7 `ℓQ_mul_ℓQinv`, L8 `ℓQinv_mul_ℓQ`
   L9 `tMat_mul_tMatInv`, L10 `tMatInv_mul_tMat`, L11 `sQ_mul_tMat`, L12 `tMatInv_zero_mul_sQ_neg`
   L13 `tMatInv_zero_mul_sQ_mul_tMat_zero`, L14 `discConjMat_wQ`, L15 `wQ_mul_vQ_mul_wQinv`, L16 `wQ_mul_mul_wQinv`
   L17 `wQinv_mul_mul_wQ`, L18 `upAdjRep_mul_vQ`, L19 `wQ_mul_vQ_mul_wQinv_mul_vQ`, L20 `ℓQinv_mul_wQ_mul_vQ_mul_wQinv_mul_vQ`
   L21 `vQ_mem_M1`, L22 `norm_vQ_zero_zero`, L23 `sQ_mem_Iw`, L24 `ℓQ_mem_Iw`
   L25 `ℓQinv_mem_Iw`, L26 `wQ_conj_mem_Iw`, L27 `Iw_one_le_M1`, L28 `norm_det_fin_two_le_one`
   L29 `discImage_zero_of_norm_apply_zero_one_le`, L30 `discConjMat_eq_tMatInv_mul_mul_tMat`, L31 `discConjMat_zero_of_discImage_zero`, L32 `conj_sQ_eq_tMat_mul_discConjMat`
   L33 `discImage_vQ_zero`, L34 `discImage_ℓQ_zero`, L35 `discImage_ℓQinv_zero`, L36 `discConj_ℓQ_zero_one_one`
   L37 `discConj_ℓQinv_zero_one_one`, L38 `discImage_sQ_zero`, L39 `discConj_sQ_zero`

Part W (45): W1 `pGL`, W2 `coe_wGL_inv`, W3 `coe_ℓGL_inv`, W4 `sGL_zero`
   W5 `sGL_mul`, W6 `sGL_inv`, W7 `wGL_mul_vGL_mul_wGL_inv_mul_vGL`, W8 `atkinLehnerK_mul_atkinLehnerKinv`
   W9 `atkinLehnerKinv_mul_atkinLehnerK`, W10 `theta_mem_Iw`, W11 `theta_ιp_pGL`, W12 `discShift_mem_U`
   W13 `theta_discShift`, W14 `mul_ιp_sGL_eq`, W15 `norm_theta_discShift_zero_one_le`, W16 `discImage_discShift_zero`
   W17 `discConjMat_discShift_zero`, W18 `atkinLehnerK_eq`, W19 `atkinLehnerKinv_eq`, W20 `cSpace_ext_blockProj`
   W21 `nebK_one`, W22 `nebK_mul_nebK_eq_nebK_det`, W23 `nebK_one_sub_eq_inv`, W24 `locPolyForms`
   W25 `discHeckeOperator_mem_classicalDiscForms`, W26 `discHeckeOperatorCl`, W27 `apply_mul_of_theta_eq_one`, W28 `blockProj_zero_apply_mul_mem_U`
   W29 `shapiro_blockProj`, W30 `atkinLehnerFun_blockProj`, W31 `atkinLehnerFun_blockProj_zero`, W32 `atkinLehnerFun_left_invt`
   W33 `atkinLehnerFun_mem_locPolyDegSubmodule`, W34 `atkinLehnerFun_slash`, W35 `atkinLehnerMap`, W36 `atkinLehnerFunInv_blockProj_zero`
   W37 `atkinLehnerFunInv_left_invt`, W38 `atkinLehnerFunInv_mem_locPolyDegSubmodule`, W39 `atkinLehnerFunInv_slash`, W40 `atkinLehnerMapInv`
   W41 `atkinLehnerMapInv_atkinLehnerMap`, W42 `atkinLehnerMap_atkinLehnerMapInv`, W43 `discEvalAtReps_mem_locPolyDegSubmoduleBlock`, W44 `discEvalAtRepsCl`
   W45 `discEvalAtRepsCl_apply`

Part I (16): I1 `vRepD_mem_levelM1`, I2 `upEltD_mem_levelM1`, I3 `discHeckeOperator_apply_eq_sum`, I4 `blockProj_zero_discSlash_of_shape`
   I5 `apply_mul_ιp_pGL`, I6 `apply_mul_ιp_pGL_inv`, I7 `blockProj_zero_apply_mul_ιp`, I8 `term_elt_eq`
   I9 `blockProj_zero_apply_term_elt`, I10 `atkinLehner_term_eq`, I11 `blockProj_zero_discHecke_atkinLehner`, I12 `discHeckeCl_comp_atkinLehner`
   I13 `discEvalAtRepsCl_discHeckeOperatorCl`, I14 `atkinLehnerHypothesis_of_conj`, I15 `atkinLehnerHypothesis_of_atkinLehnerData`, I16 `degX_succ_of_atkinLehnerData`
```

Milestone: **I16 `degX_succ_of_atkinLehnerData`** (preceded by CLEANUP-ALL-1).  9 tickets add
a new declaration to the skeleton (`[NEW DECL]`: S4, S5, N9, N11, L16, L17, L26, L28, L32 — the helper leaves the
adversarial pass identified); their statements are fixed in `tickets.md`.

## Cleanup cadence (algorithmic)

Per file, a `[CLEANUP-…]` ticket after every third proof/definition ticket and a final per-file
cleanup after the last; `CLEANUP-ALL-1` before the milestone `I15`; `CLEANUP-FINAL` last.  Cleanup
tickets are done inline by the main agent.  `lake exe runLinter PhD.LWX.<Module>` is part of every
cleanup.  Two engineering rules from `lwx-theta-h2` apply: never `rw [tsum_eq_single x (fun z hz
=> by …)]` over a compound index (state the vanishing as a `have` first), and `omit … in` goes
before the docstring.

## Planning-pass notes

- Prior-B2 consultation (`.mathlib-quality/lwx-theta/b2_log.jsonl`, `.mathlib-quality/b2_log.jsonl`,
  `.mathlib-quality/lwx-atkinlehner/b2_log.jsonl`): no leaf here re-creates a retired statement;
  in particular no `ν`-family equivariance is used and no slope statement quantifies past a degree.
- Two candidate routes were rejected during planning and are recorded so nobody re-tries them:
  (a) defining `U'_p` on `Sym^k ⊗ ψ` by its representatives (no monoid action — the nebentypus
  is not multiplicative on matrices with `p ∣ d`); (b) an adjointness/anti-involution route
  through [LWX, (2.2.2)] — no source, and the naive pairing would give `charpoly A = charpoly A'`,
  which is not Prop 3.22.
- The `pGL`-obligation in `AtkinLehnerMap.lean` (`det (p • 1) ≠ 0`) and the `i ≤ k` obligation
  inside `symAct` are the only `sorry`s inside *non-structural* definitions; both are one-liners
  (tickets W1, S10).  `locPolyForms`, `discHeckeOperatorCl`, `atkinLehnerMap(Inv)`,
  `discEvalAtRepsCl` carry their closure/membership obligations as `sorry`s (tickets W24, W26,
  W35, W40, W44).
- **Four defects found and repaired by the adversarial pass** (all before ticketing; details in
  `decomposition.md` L-d, W-b, I-f): (1) `discConj_sQ_zero` was false for `b ≥ p` — now takes
  `hb : b < p`; (2) the `(b,c)`-term lemma `atkinLehner_term_eq` omitted the inner `U_p^{ψ⁻¹}`
  slash factor `symAct (conj v_b)` — restored, and the RHS re-derived and confirmed; (3) the
  abstract hypotheses `hmul/hne/hcond` on `nebK : K → K` were stated on all norm-one `x : K`, which
  `nebCharK` does **not** satisfy for `K ⊋ ℚ_p` — restated on `ψ`-images of `p`-adic units, the
  only places they are used; (4) `AtkinLehnerData` lacked the axiom that `w` normalises the
  disc-`0` part of the level (`w_conj_mem_U`), without which `W` does not preserve the level —
  added (true for `K^p·Iw_p` by `w (a b; c d) w⁻¹ = (d, −c; −b, a)`).
- **Design note on `AtkinLehnerData`'s axioms** (what a future instantiation board must prove
  for `Dfx ℚ D`): `theta_ιp` (the `p`-component of the local embedding), `ιp_mem_U` (the level is
  `K^p·Iw_p`), `central` (`p_p = p_global·(p^{(p)})⁻¹` with `(p^{(p)})⁻¹ ∈ K^p` — a genuine
  condition on the tame level), `χ_Γ`/`χ_U`/`χ_vGL`/`χ_wGL` (the Hecke character `ψ_A ∘ ν`, class
  field theory), `w_conj_mem_U` (local).
