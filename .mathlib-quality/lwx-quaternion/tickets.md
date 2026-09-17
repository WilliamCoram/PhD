# Ticket Board — `lwx-quaternion` (the tame central operator `Z`, the canonical determinant certificate, and the adelic data of `D/ℚ`)

**BOARD PATH: `.mathlib-quality/lwx-quaternion/`.**  The default `.mathlib-quality/` board belongs to
the completed NewtonPolygons project — NEVER touch it; `.mathlib-quality/qmf/` and its
`beastmode_active` sentinel belong to a parallel run — NEVER touch them either.  Every
`/beastmode` run must name this board path explicitly, and delete only
`.mathlib-quality/lwx-quaternion/beastmode_active` and the root `.mathlib-quality/beastmode_active`
when its first line names this board (cat before rm).

**Files owned by this board** (all under `PhD/Main/`): new files `TateFredholm/02_CharpolyPairingZ.lean`,
`LWX/23_QuaternionData.lean`, `LWX/25_QuaternionSlopes.lean`; the board sections (marked
"board `lwx-quaternion`" in their docstrings) of `LWX/05_AtkinLehner.lean` (`section SlopesZ`),
`LWX/10_AtkinLehnerLocal.lean` (the Iwahori-decomposition section), `LWX/10_DiscForms.lean`
(`section Translate`), `LWX/13_AtkinLehnerInst.lean` (`AtkinLehnerHypothesisZ` and its two lemmas),
`LWX/14_Touching.lean` (the two `_mul_eq_smul_mul` lemmas), `LWX/18_AtkinLehnerMap.lean` and
`LWX/20_AtkinLehnerMapH.lean` (the new fields and the `centralOp` sections),
`LWX/19_AtkinLehnerIdentity.lean` and `LWX/21_AtkinLehnerIdentityH.lean` (the `…Z` lemmas),
`LWX/22_AtkinLehnerFamily.lean` (the new fields).  The SWAP ticket **S0** and the repair tickets
**R1–R10** additionally edit, exactly as each ticket names, `13`, `14`, `15_StepThree`, `15_TouchingH`,
`17_DegreeFormula`, `19`, `21`, `22`, `23_ConductorSlopes`, `24_DegreePeriodicity` (recompile only).
Do not edit any other file (in particular nothing under `PhD/Main/QMF/` — new generic lemmas about
the fork's API live in `23_QuaternionData.lean`'s `section Generic`; their move to
`QMF/04_UpiElement.lean` is an option recorded at `CLEANUP-FINAL` for the user).

**Build**: `lake build PhD` (the whole closure; `lake build PhD.Main.LWX.«25_QuaternionSlopes»` and
`lake build PhD.Main.TateFredholm.«02_CharpolyPairingZ»` for the two ends).  Statements are
transcribed verbatim from the compiling skeleton and are **protected** — if a statement is wrong,
append to this board's `b2_log.jsonl` rather than editing it (`_hx`-slack renames allowed).
`lake exe runLinter PhD.Main.LWX.«NN_Name»` is a gate for every cleanup (its output lists findings
for the whole closure; grep for the file).  `omega` not `lia`.  No `timeout` binary on this machine.
Cleanup tickets are done inline by the main agent, never by `Agent` subagents.  `p = 2` is deferred
(nothing here assumes `p ≠ 2` except through `nebCharK`).  No Jacquet–Langlands input anywhere
(`.mathlib-quality/lwx-stepone/JL-AUDIT.md`): the identity `U_p ∘ W⁻¹ ∘ U_p^{ψ⁻¹} ∘ W = p^{k+1}·Z`
is proved by the double-coset expansion, and the classical statement it generalises (Miyake,
Thm 4.6.17, `bu04.txt:1120–1124`) is cited, not used.

**Traps recorded at planning** (each found by the skeleton build or the adversarial pass):
* explicit arguments follow the section-variable declaration order — `centralOpCl θG ψ U hU k D κ`,
  `centralOpClH θG ψ U hU h k D κ`, `centralOp θG ψ U D φ`, `centralOpH θG ψ U h D φ`,
  `discHeckeOperatorCl θG ψ U hU k κ hκ hη hfin`, `translateOp_mem_discForms θ ψ κ U hU hz hφ`;
* `omit [CharZero K] in` on every level-`1`/`h` `centralOp` lemma whose statement does not need
  it (otherwise `21` fails with "cannot omit referenced section variable");
* at `F = ℚ` never write `D ⊗[ℚ] Kp p` or `RigidificationAt.equiv (F := ℚ)` explicitly
  (`DivisionRing.toRatAlgebra` vs `instAlgebraAdicCompletion`): go through `thetaInt`, `toMatrix`,
  `toLocal`, `unitAt`, and state generic facts over an arbitrary number field `F` in
  `section Generic` of `23`;
* `Module.End` dot-notation on `Matrix.toLin' Z` fails (`LinearMap` head): write
  `Module.End.IsSemisimple (Matrix.toLin' Z)`, `Module.End.eigenspace (Matrix.toLin' Z) μ`;
* `g = ιp(θ g) · tamePart g` is **not** definitional (the definition is `tamePart g = g · ιp(θ g)⁻¹`):
  it needs `ιpD_comm_of_thetaInt_eq_one`;
* identities in `(ZMod p)ˣ →* ℤ_[p]ˣ` pointwise (`MonoidHom.ext`), never `rw [mul_one]` on homs;
  every proof-only section hypothesis in the `include … in` line (the `lwx-conductor` B2).

**Read before working any ticket**: `plan.md` and `decomposition.md` of this board (every leaf
below carries its verbatim source quote and attack log there), and
`.mathlib-quality/lwx-stepone/JL-AUDIT.md`.

**Tickets that ADD a declaration** (marked `[NEW DECL]` in the index): Q2 (`unitAt_mul`),
Q4 (`singleₗ_mul`, `iotaV_mul_eq_iotaV_mul_toLocal`), L3 (`inv_mem_Iw`).  A worker who spawns
any other helper must give it a ticket in this format (statement, sketch, sources) and list it here.

## Summary

Planned 2026-09-14 (`/develop`; the adversarial decomposition is `decomposition.md`).  Three goals:

1. **Decision 1(b) — the tame central operator.**  The field `central` of `AtkinLehnerData` (which
   forces the tame scalar `p^{(p)}` into the level, false for [LWX]'s neat levels in general) is
   replaced by `ιp_pGL_comm` (centrality of `ιp(p·1)`) and `central_pow` (a power of `ιp(p·1)` is
   global-central times a tame level element).  H1 becomes `A B = p^{k+1}·Z` with `Z` commuting
   with `A` and `Z^N = 1` (`AtkinLehnerHypothesisZ`); the Atkin–Li form of [LWX, Prop 3.22]
   (`a_p(f)·a_p(f|W) = χ_M(p)·p^{k+1}`, Miyake 4.6.17) pairs the **norms** of the eigenvalues, which
   is all the slope arguments use.  Parts **Z** (abstract pairing), **C** (the operator `Z` and the
   identity at level `1` and `h`), the **SWAP** and the repairs **R**.
2. **Decision 2 — the canonical determinant certificate.**  `det(u_{i,t} v_t) = p` is *proved* from
   normalised class representatives (`p`-component `1`, unit norm class), as [LWX, Prop 3.1] does;
   no downstream statement changes.  Ticket **Q23** (with Q13, Q14, Q21).
3. **The instantiation for `D/ℚ`.**  `QuaternionInput` (tame level, norm class with four axioms,
   normalised neat representatives) ⇒ `AtkinLehnerFamily`, `AtkinLehnerFamilyH`, the `U_p`-datum
   and the certificates, with no topology and no reduced norm; then the headline theorems for
   `D/ℚ` (Part **M**: the unit band, [LWX, Thm 1.3]'s degrees and positivity, Cor 1.4, (1.5.1) and
   the arithmetic progressions).  Parts **L** (Iwahori decomposition), **Q**, **M**.

**Milestones**: **C16** / **C21** (H1 in the `Z`-form at level `1` / `h`, from the data), **S0** (the
swap compiles: the scalar hypothesis is gone from the library), **Q23** (`det_certM1_eq`, decision 2),
**M3** (`degXint_pos` for `D/ℚ`), **M6** (`slopeRatio_add_period` for `D/ℚ`).

**Parallelism**: Part Z (Z1–Z15), Part L (L1–L3), the `10_DiscForms` leaves C1–C5, and Q1–Q18 are
mutually independent.  C6–C11 need C1–C5; C12–C16 need C6–C8 (and C1–C5); C17–C21 need C9–C11.
S0 needs Z13–Z15, C16, C21; R1–R10 need S0 (R6–R8 also Z4, Z12); Q19 needs S0 (the `central := sorry`
line disappears with the field).  Q20b needs L1–L3, Q5, Q7–Q9; Q22–Q23 need Q20–Q21, Q13–Q14.
Part M needs everything (the family theorems' proofs go through the swapped H1).

**Skeleton build record (2026-09-14)**: `lake build PhD` — **Build completed successfully (3929 jobs)**;
warnings: `declaration uses 'sorry'` only, plus five `unusedSectionVars` on `rfl` lemmas of
`23_QuaternionData.lean` (`coe_thetaIntGL`, `ιpD_apply`, `mem_tameSubgroup_iff`, `mem_levelOf_iff`,
`heckeChar_apply` — for CLEANUP-Q1/Q5: `omit … in`).  Sorry count: 14 (`02_CharpolyPairingZ`) + 1
(`05`) + 2 (`10_AtkinLehnerLocal`) + 8 (`10_DiscForms`) + 2 (`13`) + 2 (`14`) + 5 (`18`) + 5 (`19`)
+ 5 (`20`) + 5 (`21`) + 63 (`23_QuaternionData`) + 8 (`25_QuaternionSlopes`) = 120.

**Execution record (2026-09-14, `/beastmode`)**: every proof/def/check ticket, the SWAP **S0** and the
repairs **R1–R10** are done; **Q-OPT** stays blocked (optional, user decision).  Final gate:
`lake build PhD` green (3929 jobs), zero `sorry` and no warning in any board-touched file,
`#print axioms` = `[propext, Classical.choice, Quot.sound]` on every milestone (C16, C21, S0's
consumers, Q23, Z12, M1–M6).  `runLinter`: no finding in any board file (100 findings project-wide, all in files this board did not touch) (the one remaining LWX finding,
`isClassicalShape_haloWeightH_classicalPoint` in `15_ClassicalPoint.lean`, predates this board).  B2 log: empty.  The one planned statement change is
R8 (`toReal_unitSlope_charpolyRev_reflect` now takes the norm-multiset form of H1).
- **`_hx` slack**: none found (no board declaration carries an unused hypothesis).
- **Omit cascade**: removing an unused instance argument from a lemma can make its callers' copy unused, so the
  `omit … in` pass was iterated until a full build showed no further warning.  One public statement became strictly more general:
  `Module.End.norm_roots_charpoly_mul_of_iSup_eigenspace_eq_top` no longer assumes `[IsAlgClosed K] [CharZero K]`.
- **Stale blueprint sentences** (not edited — needs the user's go-ahead):
  `blueprint/src/chapter/LWXSlopes.tex:461` ("Granting the operator identity `U_p∘U'_p = p^{k+1}`"),
  `:477–479` (`def:al-data`: "the central element `p` at `p` is a global central element times an
  element of the level" — now: `ιp(p·1)` central with a *power* of that form), `:497–499`
  (`prop:al-identity` displays `= p^{k+1}`; now `= p^{k+1}·Z`), `:508` ("contributes `p^{k+1}`"), `:779`
  (item 2 of the closing list).  Every `\lean{}` name of the three LWX chapters still resolves
  (298/298 resolve on the final build (`#check @name` under `import PhD`, 0 errors)).
- **Options for the user**: (i) move the generic adelic lemmas of `23_QuaternionData.lean`'s
  `section GenericTop` / `section Generic` (`QMF.singleₗ_mul`, `QMF.unitAt_mul`,
  `QMF.toMatrix_unitsIncl_algebraMap`, …) to `PhD/Main/QMF/04_UpiElement.lean`; (ii) **Q-OPT** —
  derive `tameScalar_pow_mem` for every open tame level from the compactness of the tame scalars
  (needs the topology on `Dfx ℚ D`), removing that field of `QuaternionInput`; (iii) update the
  blueprint sentences above.
- **Traps met** (beyond the header list): at `F = ℚ` the instances `DivisionRing.toRatAlgebra` and
  `HeightOneSpectrum.instAlgebraAdicCompletion` on `Algebra ℚ (Kp p)` differ — state generic lemmas
  over a number field `F` and specialise; `ext i j` on matrices over `Kp p` enters the completion's
  ext lemma (use `Matrix.ext fun i j => ?_`); bare `pow_succ`/`mul_assoc` rewrites hit the wrong
  instance or unfold `set` variables (give explicit arguments); forward `LinearMap.toMatrix_comp`
  cannot infer the middle basis (rewrite with `←`); insert `omit … in` by declaration name, never by
  log line number after edits.

### B2 log
empty at planning time (`b2_log.jsonl`).

### Cleanup cadence
Per file: a `CLEANUP-<part><n>` ticket after every third proof ticket and a `…-FINAL` after the
last; `CLEANUP-ALL-1` before the SWAP (the last moment both hypothesis forms coexist),
`CLEANUP-ALL-2` before Part M (milestone M3), `CLEANUP-ALL-3` before M6; `CLEANUP-FINAL` last.

## Ticket index

| ID | Declaration(s) | File | Type |
|---|---|---|---|
| Z1 | `det_mul_det_of_mul_eq_smul_mul` | 02_CharpolyPairingZ | proof |
| Z2 | `det_ne_zero_of_pow_eq_one` | 02_CharpolyPairingZ | proof |
| Z3 | `det_ne_zero_of_mul_eq_smul_mul`, `det_ne_zero_of_mul_eq_smul_mul'` | 02_CharpolyPairingZ | proof |
| CLEANUP-Z1 | `CLEANUP-Z1` | 02_CharpolyPairingZ | cleanup |
| Z4 | `mul_comm_of_mul_eq_smul_mul`, `mul_eq_smul_mul_symm` | 02_CharpolyPairingZ | proof |
| Z5 | `norm_det_eq_one_of_pow_eq_one` | 02_CharpolyPairingZ | proof |
| Z6 | `roots_charpolyRev_smul` | 02_CharpolyPairingZ | proof |
| CLEANUP-Z2 | `CLEANUP-Z2` | 02_CharpolyPairingZ | cleanup |
| Z7 | `roots_charpoly_smul` | 02_CharpolyPairingZ | proof |
| Z8 | `isSemisimple_toLin'_of_pow_eq_one` | 02_CharpolyPairingZ | proof |
| Z9 | `norm_eq_one_of_eigenspace_ne_bot_of_pow_eq_one` | 02_CharpolyPairingZ | proof |
| CLEANUP-Z3 | `CLEANUP-Z3` | 02_CharpolyPairingZ | cleanup |
| Z10 | `_root_.Module.End.norm_roots_charpoly_mul_of_iSup_eigenspace_eq_top` | 02_CharpolyPairingZ | proof |
| Z11 | `norm_roots_charpoly_mul_of_commute_of_pow_eq_one` | 02_CharpolyPairingZ | proof |
| Z12 | `norm_roots_charpoly_of_mul_eq_smul_mul` | 02_CharpolyPairingZ | proof |
| CLEANUP-Z-FINAL | `CLEANUP-Z-FINAL` | 02_CharpolyPairingZ | cleanup |
| Z13 | `norm_roots_charpoly_atkinLehnerZ` | 05_AtkinLehner | proof |
| Z14 | `AtkinLehnerHypothesis.toZ`, `norm_roots_charpoly_of_atkinLehnerHypothesisZ` | 13_AtkinLehnerInst | proof |
| Z15 | `neg_log_norm_det_add_of_mul_eq_smul_mul`, `det_ne_zero_of_mul_eq_smul_mul_conj` | 14_Touching | proof |
| CLEANUP-Z4 | `CLEANUP-Z4` | 05/13/14 | cleanup |
| L3 | `L3` + `inv_mem_Iw` **[NEW DECL]** | 10_AtkinLehnerLocal | proof |
| L1 | `exists_mem_Iw_mul_vQ` | 10_AtkinLehnerLocal | proof |
| L2 | `eq_of_vQ_eq_mul_vQ` | 10_AtkinLehnerLocal | proof |
| CLEANUP-L | `CLEANUP-L` | 10_AtkinLehnerLocal | cleanup |
| C1 | `translateOp`, `translateOp_add`, `translateOp_smul`, `translateOp_one`, `translateOp_translateOp` | 10_DiscForms | proof |
| C2 | `apply_mul_of_theta_eq_one'` | 10_DiscForms | proof |
| C3 | `translateOp_mem_discForms` | 10_DiscForms | proof |
| CLEANUP-C1 | `CLEANUP-C1` | 10_DiscForms | cleanup |
| C4 | `translateOp_eq_self_of_eq_mul` | 10_DiscForms | proof |
| C5 | `translateOp_discHeckeOperator` | 10_DiscForms | proof |
| CLEANUP-C2 | `CLEANUP-C2` | 10_DiscForms | cleanup |
| C6 | `centralOp`, `centralOp_mem_classicalDiscForms`, `centralOpCl` | 18_AtkinLehnerMap | proof/def |
| C7 | `centralOpCl_pow_eq_one` | 18_AtkinLehnerMap | proof |
| C8 | `discHeckeOperatorCl_comp_centralOpCl` | 18_AtkinLehnerMap | proof |
| CLEANUP-C3 | `CLEANUP-C3` | 18_AtkinLehnerMap | cleanup |
| C9 | `centralOpH_mem_classicalDiscFormsH`, `centralOpClH` | 20_AtkinLehnerMapH | proof/def |
| C10 | `centralOpClH_pow_eq_one` | 20_AtkinLehnerMapH | proof |
| C11 | `discHeckeOperatorClH_comp_centralOpClH` | 20_AtkinLehnerMapH | proof |
| CLEANUP-C4 | `CLEANUP-C4` | 20_AtkinLehnerMapH | cleanup |
| C12 | `blockProj_zero_apply_term_eltZ` | 19_AtkinLehnerIdentity | proof |
| C13 | `atkinLehner_term_eqZ` | 19_AtkinLehnerIdentity | proof |
| C14 | `blockProj_zero_discHecke_atkinLehnerZ` | 19_AtkinLehnerIdentity | proof |
| CLEANUP-C5 | `CLEANUP-C5` | 19_AtkinLehnerIdentity | cleanup |
| C15 | `discHeckeCl_comp_atkinLehnerZ` | 19_AtkinLehnerIdentity | proof |
| C16 | `atkinLehnerHypothesisZ_of_atkinLehnerData` **[MILESTONE]** | 19_AtkinLehnerIdentity | proof |
| CLEANUP-C6 | `CLEANUP-C6` | 19_AtkinLehnerIdentity | cleanup |
| C17 | `blockProj_zero_apply_term_eltHZ` | 21_AtkinLehnerIdentityH | proof |
| C18 | `atkinLehner_term_eqHZ` | 21_AtkinLehnerIdentityH | proof |
| C19 | `blockProj_zero_discHecke_atkinLehnerHZ` | 21_AtkinLehnerIdentityH | proof |
| CLEANUP-C7 | `CLEANUP-C7` | 21_AtkinLehnerIdentityH | cleanup |
| C20 | `discHeckeClH_comp_atkinLehnerHZ` | 21_AtkinLehnerIdentityH | proof |
| C21 | `atkinLehnerHypothesisZ_of_atkinLehnerDataH` **[MILESTONE]** | 21_AtkinLehnerIdentityH | proof |
| CLEANUP-C8 | `CLEANUP-C8` | 21_AtkinLehnerIdentityH | cleanup |
| CLEANUP-ALL-1 | `CLEANUP-ALL-1` | all | cleanup |
| S0 | `S0` **[MILESTONE]** | 13/14/18–23 | repair |
| R1 | `R1` | 14_Touching | repair |
| R2 | `R2` | 15_TouchingH | repair |
| R3 | `R3` | 15_StepThree | repair |
| R4 | `R4` | 17_DegreeFormula | repair |
| R5 | `R5` | 19/21 | repair |
| R6 | `R6` | 23_ConductorSlopes | repair |
| R7 | `R7` | 23_ConductorSlopes | repair |
| R8 | `R8` | 23_ConductorSlopes | repair |
| R9 | `R9` | 23/24 | repair |
| R10 | `R10` | 22/PhD.lean | repair |
| CLEANUP-R | `CLEANUP-R` | repairs | cleanup |
| Q1 | `det_thetaInt_ne_zero`, `thetaIntGL` | 23_QuaternionData | proof |
| Q2 | `ιpD` + `QMF.unitAt_mul` **[NEW DECL]** | 23_QuaternionData | proof |
| Q3 | `thetaInt_ιpD`, `thetaIntGL_ιpD`, `ιpD_injective` | 23_QuaternionData | proof |
| CLEANUP-Q1 | `CLEANUP-Q1` | 23_QuaternionData | cleanup |
| Q4 | `QMF.iotaV_mul_eq_zero_of_toLocal_eq_zero` + `QMF.singleₗ_mul` **[NEW DECL]**, `QMF.mul_singleₗ` **[NEW DECL]**, `QMF.iotaV_mul_eq_iotaV_mul_toLocal` **[NEW DECL]**, `QMF.mul_iotaV_eq_iotaV_toLocal_mul` **[NEW DECL]** | 23_QuaternionData | proof |
| Q5 | `ιpD_comm_of_thetaInt_eq_one` | 23_QuaternionData | proof |
| Q6 | `ιpD_pGL_comm` | 23_QuaternionData | proof |
| CLEANUP-Q2 | `CLEANUP-Q2` | 23_QuaternionData | cleanup |
| Q7 | `tameSubgroup`, `tamePart_mem_tameSubgroup`, `eq_ιpD_mul_tamePart` | 23_QuaternionData | proof |
| Q8 | `tamePart_mul`, `tamePart_one`, `tamePart_inv`, `tamePart_ιpD`, `tamePart_eq_self_of_thetaInt_eq_one`, `tamePart_conj_ιpD` | 23_QuaternionData | proof |
| Q9 | `levelOf`, `levelOf_subset_levelM1`, `ιpD_mem_levelOf`, `mem_levelOf_of_thetaInt_eq_one` | 23_QuaternionData | proof |
| CLEANUP-Q3 | `CLEANUP-Q3` | 23_QuaternionData | cleanup |
| Q10 | `levelOf_wGL_conj`, `levelOf_wGLH_conj` | 23_QuaternionData | proof |
| Q11 | `pUnit`, `thetaInt_unitsIncl_pUnit`, `unitsIncl_pUnit_comm`, `tameScalar`, `thetaInt_tameScalar`, `tameScalar_comm` | 23_QuaternionData | proof |
| Q12 | `central_pow_of_tameScalar_pow_mem` | 23_QuaternionData | proof |
| CLEANUP-Q4 | `CLEANUP-Q4` | 23_QuaternionData | cleanup |
| Q13 | `norm_det_mul_inv_normClass`, `normClass_level` | 23_QuaternionData | proof |
| Q14 | `normClass_ιpD_vGL`, `normClass_ιpD_wGL`, `normClass_ιpD_wGLH`, `normClass_ιpD_pGL` | 23_QuaternionData | proof |
| Q15 | `heckeChar` | 23_QuaternionData | proof |
| CLEANUP-Q5 | `CLEANUP-Q5` | 23_QuaternionData | cleanup |
| Q16 | `heckeChar_global`, `heckeChar_level`, `heckeChar_ιpD_vGL`, `heckeChar_ιpD_wGL` | 23_QuaternionData | proof |
| Q17 | `heckeCharH` | 23_QuaternionData | proof |
| Q18 | `heckeCharH_global`, `heckeCharH_level`, `heckeCharH_ιpD_vGL`, `heckeCharH_ιpD_wGLH` | 23_QuaternionData | proof |
| CLEANUP-Q6 | `CLEANUP-Q6` | 23_QuaternionData | cleanup |
| Q19 | `atkinLehnerFamily`, `atkinLehnerFamilyH` | 23_QuaternionData | check |
| Q20a | `vRepQ`, `vRepQ_mem_levelM1`, `upEltQ`, `injective_vRepQ` | 23_QuaternionData | proof |
| Q20b | `bijOn_vRepQ` | 23_QuaternionData | proof |
| Q20c | `finite_image_upEltQ` | 23_QuaternionData | proof |
| CLEANUP-Q7 | `CLEANUP-Q7` | 23_QuaternionData | cleanup |
| Q21 | `exists_factorisation`, `idx`, `dElt`, `uElt`, `dElt_mem`, `c_mul_vRepQ_inv` | 23_QuaternionData | proof |
| Q22 | `hshape` | 23_QuaternionData | proof |
| Q23 | `det_certM1_eq` **[MILESTONE]** | 23_QuaternionData | proof |
| Q24 | `upDatum` | 23_QuaternionData | check |
| CLEANUP-Q-FINAL | `CLEANUP-Q-FINAL` | 23_QuaternionData | cleanup |
| Q-OPT | `Q-OPT` | 23_QuaternionData | proof |
| CLEANUP-ALL-2 | `CLEANUP-ALL-2` | all | cleanup |
| M1 | `hasUnitBand` | 25_QuaternionSlopes | proof |
| M2 | `degX_succ`, `degXint_eq` | 25_QuaternionSlopes | proof |
| M3 | `degXint_pos` **[MILESTONE]** | 25_QuaternionSlopes | proof |
| CLEANUP-M1 | `CLEANUP-M1` | 25_QuaternionSlopes | cleanup |
| M4 | `degX_succ_add_period`, `degXint_add_period` | 25_QuaternionSlopes | proof |
| M5 | `unitSlope_discHeckeCharPowerSeries_eq_slopeRatio` | 25_QuaternionSlopes | proof |
| CLEANUP-ALL-3 | `CLEANUP-ALL-3` | all | cleanup |
| M6 | `slopeRatio_add_period` **[MILESTONE]** | 25_QuaternionSlopes | proof |
| CLEANUP-M-FINAL | `CLEANUP-M-FINAL` | 25_QuaternionSlopes | cleanup |
| CLEANUP-FINAL | `CLEANUP-FINAL` | all | cleanup |

## Tickets

### [Z1] `Matrix.det_mul_det_of_mul_eq_smul_mul`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/TateFredholm/02_CharpolyPairingZ.lean
- **Depends on**: none
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/TateFredholm/02_CharpolyPairingZ.lean:40
/-- `A B = c Z` ⇒ `det A · det B = c^n · det Z`. -/
theorem det_mul_det_of_mul_eq_smul_mul (h : A * B = c • Z) :
    A.det * B.det = c ^ Fintype.card n * Z.det := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `rw [← Matrix.det_mul, h, Matrix.det_smul]` — this is `Matrix.det_mul_det_of_mul_eq_smul`
   (`01_CharpolyPairing.lean:57`, proof `rw [← det_mul, h, det_smul, det_one, mul_one]`) with the
   `det_one, mul_one` steps dropped (the factor `Z.det` stays).

- **Mathlib/project lemmas needed**: `Matrix.det_mul`, `Matrix.det_smul`
- **Sources**: decomposition Z1; the scalar case `01_CharpolyPairing.lean:57`.
- **Generality decision**: `[Field K]` (a `CommRing` would do; kept uniform with the file, as recorded in the decomposition).
- **Size**: 1 line; source: 1 line
- **Progress**: done 2026-09-14 — rw [← det_mul, h, det_smul]; compiled (lake env lean / lake build).

### [Z2] `Matrix.det_ne_zero_of_pow_eq_one`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/TateFredholm/02_CharpolyPairingZ.lean
- **Depends on**: none
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/TateFredholm/02_CharpolyPairingZ.lean:45
/-- A matrix of finite order has nonzero determinant. -/
theorem det_ne_zero_of_pow_eq_one {N : ℕ} (hN : 0 < N) (hZ : Z ^ N = 1) : Z.det ≠ 0 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `have h := congrArg Matrix.det hZ; rw [Matrix.det_pow, Matrix.det_one] at h`.
2. `exact (pow_ne_zero_iff hN.ne').1 (h ▸ one_ne_zero)` — or `intro h0; rw [h0, zero_pow hN.ne'] at h; exact zero_ne_one h`.

- **Mathlib/project lemmas needed**: `Matrix.det_pow`, `Matrix.det_one`, `pow_ne_zero_iff`/`zero_pow`
- **Sources**: decomposition Z2.
- **Generality decision**: `[Field K]`; `0 < N` necessary (`N = 0`, `Z = 0` is a counterexample).
- **Size**: 3 lines
- **Progress**: done 2026-09-14 — det_pow/det_one/zero_pow; compiled (lake env lean / lake build).

### [Z3] `Matrix.det_ne_zero_of_mul_eq_smul_mul`, `…'`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/TateFredholm/02_CharpolyPairingZ.lean
- **Depends on**: Z1, Z2
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/TateFredholm/02_CharpolyPairingZ.lean:49
/-- Under `A B = c Z`, `c ≠ 0`, `Z^N = 1`, the determinant of `A` is nonzero. -/
theorem det_ne_zero_of_mul_eq_smul_mul (hc : c ≠ 0) (h : A * B = c • Z) {N : ℕ} (hN : 0 < N)
    (hZ : Z ^ N = 1) : A.det ≠ 0 := by
  sorry
```
```lean
-- PhD/Main/TateFredholm/02_CharpolyPairingZ.lean:54
/-- Under `A B = c Z`, `c ≠ 0`, `Z^N = 1`, the determinant of `B` is nonzero. -/
theorem det_ne_zero_of_mul_eq_smul_mul' (hc : c ≠ 0) (h : A * B = c • Z) {N : ℕ} (hN : 0 < N)
    (hZ : Z ^ N = 1) : B.det ≠ 0 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `have hprod := det_mul_det_of_mul_eq_smul_mul h` (Z1); `have hZ0 := det_ne_zero_of_pow_eq_one hN hZ` (Z2).
2. `intro h0; rw [h0, zero_mul] at hprod; exact mul_ne_zero (pow_ne_zero _ hc) hZ0 hprod.symm` (for `'`: `mul_zero`).

- **Mathlib/project lemmas needed**: Z1, Z2, `mul_ne_zero`, `pow_ne_zero`
- **Sources**: decomposition Z3; the scalar case `01_CharpolyPairing.lean:110`.
- **Generality decision**: as the statements.
- **Size**: 4 lines each
- **Progress**: done 2026-09-14 — Z1+Z2, mul_ne_zero; compiled (lake env lean / lake build).

### [CLEANUP-Z1] Cleanup `PhD/Main/TateFredholm/02_CharpolyPairingZ.lean`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/TateFredholm/02_CharpolyPairingZ.lean
- **Depends on**: Z1, Z2, Z3
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused `simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings; `lake build PhD` and `lake exe runLinter` on the module must be clean (grep the linter's output for the file).  Done inline by the main agent.

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): `02_CharpolyPairingZ`: header marker, route paragraph rewritten to the lemmas actually used, `simp only` list reflowed, `omit [IsAlgClosed K] [CharZero K] in` on the private `roots_charpoly_smul_end` and `norm_roots_charpoly_mul_aux`, and hence (cascade) on `Module.End.norm_roots_charpoly_mul_of_iSup_eigenspace_eq_top`, which therefore holds over any normed field (no `IsAlgClosed`, no `CharZero`); three `ring` calls that only closed their goals through the `ring_nf` fallback (build `info: Try this`) now say `ring_nf`; `lake build PhD` green (3929 jobs).

### [Z4] `Matrix.mul_comm_of_mul_eq_smul_mul`, `Matrix.mul_eq_smul_mul_symm`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/TateFredholm/02_CharpolyPairingZ.lean
- **Depends on**: Z3
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/TateFredholm/02_CharpolyPairingZ.lean:59
/-- `Z` commutes with `B` as well: `B = A⁻¹·(c Z)` and `Z` commutes with `A⁻¹`. -/
theorem mul_comm_of_mul_eq_smul_mul (hc : c ≠ 0) (h : A * B = c • Z) (hZA : Z * A = A * Z)
    {N : ℕ} (hN : 0 < N) (hZ : Z ^ N = 1) : Z * B = B * Z := by
  sorry
```
```lean
-- PhD/Main/TateFredholm/02_CharpolyPairingZ.lean:64
/-- `B A = c Z` as well. -/
theorem mul_eq_smul_mul_symm (hc : c ≠ 0) (h : A * B = c • Z) (hZA : Z * A = A * Z) {N : ℕ}
    (hN : 0 < N) (hZ : Z ^ N = 1) : B * A = c • Z := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `have hA0 : IsUnit A.det := isUnit_iff_ne_zero.2 (det_ne_zero_of_mul_eq_smul_mul hc h hN hZ)`;
   `have hAinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA0`, `have hAinv' : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA0`.
2. `have hB : B = A⁻¹ * (c • Z) := by rw [← h, ← Matrix.mul_assoc, hAinv, Matrix.one_mul]`.
3. `have hZinv : Z * A⁻¹ = A⁻¹ * Z := by` — from `hZA`: `calc Z * A⁻¹ = A⁻¹ * (A * Z) * A⁻¹ := by rw [← Matrix.mul_assoc, hAinv, Matrix.one_mul]`, `_ = A⁻¹ * (Z * A) * A⁻¹ := by rw [hZA]`, `_ = A⁻¹ * Z := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hAinv', Matrix.mul_one]`.
4. First lemma: `rw [hB, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hZinv, Matrix.mul_assoc]` (both sides `c • (A⁻¹ * (Z * Z))`).
5. Second lemma: `rw [hB, Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, ← hZA, ← Matrix.mul_assoc, hAinv, Matrix.one_mul]`.

- **Mathlib/project lemmas needed**: `Matrix.nonsing_inv_mul`, `Matrix.mul_nonsing_inv`, `isUnit_iff_ne_zero`, `Matrix.mul_smul`, `Matrix.smul_mul`, `Matrix.mul_assoc`
- **Sources**: decomposition Z4 (attack [1] shows `hZA` is necessary).
- **Generality decision**: as the statements.
- **Size**: ~15 lines
- **Progress**: done 2026-09-14 — via private helper mul_nonsing_inv_comm (Z A⁻¹ = A⁻¹ Z); compiled (lake env lean / lake build).

### [Z5] `Matrix.norm_det_eq_one_of_pow_eq_one`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/TateFredholm/02_CharpolyPairingZ.lean
- **Depends on**: none
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/TateFredholm/02_CharpolyPairingZ.lean:75
/-- A matrix of finite order has a determinant of norm one. -/
theorem norm_det_eq_one_of_pow_eq_one {Z : Matrix n n K} {N : ℕ} (hN : 0 < N) (hZ : Z ^ N = 1) :
    ‖Z.det‖ = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `have h := congrArg (fun M : Matrix n n K => ‖M.det‖) hZ`; `simp only [Matrix.det_pow, Matrix.det_one, norm_pow, norm_one] at h`.
2. `exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 h`.

- **Mathlib/project lemmas needed**: `Matrix.det_pow`, `norm_pow`, `norm_one`, `pow_eq_one_iff_of_nonneg` (`Mathlib/Algebra/Order/GroupWithZero/Basic.lean:680`)
- **Sources**: decomposition Z5.
- **Generality decision**: `[NormedField K]` (multiplicativity of the norm is used).
- **Size**: 3 lines
- **Progress**: done 2026-09-14 — pow_eq_one_iff_of_nonneg; compiled (lake env lean / lake build).

### [Z6] `Matrix.roots_charpolyRev_smul`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/TateFredholm/02_CharpolyPairingZ.lean
- **Depends on**: none
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/TateFredholm/02_CharpolyPairingZ.lean:86
/-- The roots of `charpolyRev (μ • A)` are those of `charpolyRev A` divided by `μ`
(`charpolyRev (μ • A) = (charpolyRev A).comp (C μ * X)`, `Polynomial.roots_comp_C_mul_X_add_C`). -/
theorem roots_charpolyRev_smul {A : Matrix n n K} {μ : K} (hμ : μ ≠ 0) :
    (μ • A).charpolyRev.roots = A.charpolyRev.roots.map (fun x => μ⁻¹ * x) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. Key identity `hcomp : (μ • A).charpolyRev = A.charpolyRev.comp (C μ * X)`: unfold `Matrix.charpolyRev`
   (`det (1 - (X : K[X]) • A.map C)`); `rw [← Polynomial.coe_compRingHom, RingHom.map_det, RingHom.mapMatrix_apply]`;
   `congr 1; ext i j; simp [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, Polynomial.comp, mul_comm, mul_left_comm]`
   (entrywise: `(1 - X•A)_{ij}.comp (C μ * X) = δ_{ij} - (C μ * X) * C (A i j) = (1 - X • (μ•A).map C)_{ij}`).
   This is the `charpolyRev`-side twin of the `comp` manipulation at `01_CharpolyPairing.lean:180–195`.
2. `rw [hcomp, show (C μ * X : K[X]) = C μ * X + C 0 by simp, Polynomial.roots_comp_C_mul_X_add_C _ _ _ (isUnit_iff_ne_zero.2 hμ)]`;
   `refine Multiset.map_congr rfl fun x _ => ?_; rw [Ring.inverse_eq_inv]; ring`.

- **Mathlib/project lemmas needed**: `Matrix.charpolyRev`, `RingHom.map_det`, `RingHom.mapMatrix_apply`, `Polynomial.compRingHom`, `Polynomial.roots_comp_C_mul_X_add_C` (`Roots.lean:244`), `Ring.inverse_eq_inv`
- **Sources**: decomposition Z6; pattern `01_CharpolyPairing.lean:180–195`.
- **Generality decision**: `[NormedField K] [IsAlgClosed K] [CharZero K]` section (only `Field` used here; noted for cleanup).
- **Size**: ~15 lines
- **Progress**: done 2026-09-14 — comp identity entrywise + roots_comp_C_mul_X_add_C (ring closes via ring_nf); compiled (lake env lean / lake build).

### [CLEANUP-Z2] Cleanup `PhD/Main/TateFredholm/02_CharpolyPairingZ.lean`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/TateFredholm/02_CharpolyPairingZ.lean
- **Depends on**: Z4, Z5, Z6
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused `simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings; `lake build PhD` and `lake exe runLinter` on the module must be clean (grep the linter's output for the file).  Done inline by the main agent.

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): as CLEANUP-Z1 (same file, one pass); `lake build PhD` green (3929 jobs).

### [Z7] `Matrix.roots_charpoly_smul`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/TateFredholm/02_CharpolyPairingZ.lean
- **Depends on**: none
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/TateFredholm/02_CharpolyPairingZ.lean:92
/-- The roots of `charpoly (μ • A)` are those of `charpoly A` times `μ`. -/
theorem roots_charpoly_smul {A : Matrix n n K} {μ : K} (hμ : μ ≠ 0) :
    (μ • A).charpoly.roots = A.charpoly.roots.map (fun x => μ * x) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. Key identity `hcomp : (μ • A).charpoly = C (μ ^ Fintype.card n) * A.charpoly.comp (C μ⁻¹ * X)`:
   `charpoly = det (charmatrix _)`, `charmatrix (μ • A) = X • 1 - (μ • A).map C = μ • (C μ⁻¹ * X • 1 - A.map C)` (entrywise, `hμ`), so
   `det = μ^n * det ((charmatrix A).map (compRingHom (C μ⁻¹ * X)))` by `Matrix.det_smul` and `RingHom.map_det`; entrywise `congr`/`ext` as in Z6.
2. `rw [hcomp, Polynomial.roots_C_mul _ (pow_ne_zero _ hμ), show (C μ⁻¹ * X : K[X]) = C μ⁻¹ * X + C 0 by simp,
   Polynomial.roots_comp_C_mul_X_add_C _ _ _ (isUnit_iff_ne_zero.2 (inv_ne_zero hμ))]`;
   `Multiset.map_congr rfl fun x _ => by rw [Ring.inverse_eq_inv, inv_inv]; ring`.
3. Alternative if step 1 fights: for `A.det ≠ 0` go through `Matrix.roots_charpolyRev` (`01:157`) on both sides and Z6; for `A.det = 0` both root multisets contain the same number of zeros — avoid, use step 1.

- **Mathlib/project lemmas needed**: `Matrix.charpoly`, `Matrix.charmatrix`, `Matrix.det_smul`, `RingHom.map_det`, `Polynomial.roots_C_mul`, `Polynomial.roots_comp_C_mul_X_add_C`
- **Sources**: decomposition Z7 (attack [1]: the hypothesis `μ ≠ 0` was added to the skeleton on 2026-09-14).
- **Generality decision**: as the statement.
- **Size**: ~20 lines
- **Progress**: done 2026-09-14 — charmatrix(μ•A) = C μ • compRingHom-map; linear_combination replaced by simp only [mul_sub, ← mul_assoc, hCC]; compiled (lake env lean / lake build).

### [Z8] `Matrix.isSemisimple_toLin'_of_pow_eq_one`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/TateFredholm/02_CharpolyPairingZ.lean
- **Depends on**: none
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/TateFredholm/02_CharpolyPairingZ.lean:109
/-- `Z^N = 1` ⇒ `toLin' Z` is semisimple (`X^N − 1` is squarefree in characteristic zero). -/
theorem isSemisimple_toLin'_of_pow_eq_one {Z : Matrix n n K} {N : ℕ} (hN : 0 < N)
    (hZ : Z ^ N = 1) : Module.End.IsSemisimple (Matrix.toLin' Z) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := X ^ N - C 1) ?_ ?_`
   (`Mathlib/LinearAlgebra/Semisimple.lean:218`: `{p : K[X]} (hp : Squarefree p) (hpf : aeval f p = 0)`).
2. Squarefree: `(Polynomial.separable_X_pow_sub_C (1 : K) (by exact_mod_cast hN.ne') one_ne_zero).squarefree`
   (`Separable.lean:414`: `(hn : (n : F) ≠ 0) (ha : a ≠ 0)`; `(N : K) ≠ 0` from `CharZero`).
3. `aeval`: `simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, one_smul]`;
   `rw [← Matrix.toLin'_pow, hZ, Matrix.toLin'_one, sub_self]`.

- **Mathlib/project lemmas needed**: `Module.End.isSemisimple_of_squarefree_aeval_eq_zero`, `Polynomial.separable_X_pow_sub_C`, `Polynomial.Separable.squarefree`, `Matrix.toLin'_pow` (`ToLin.lean:444`), `Matrix.toLin'_one`, `Polynomial.aeval_X`, `Polynomial.aeval_C`
- **Sources**: decomposition Z8 (`CharZero` necessary: unipotent `Z` of order `p` in characteristic `p`).
- **Generality decision**: as the statement.
- **Size**: ~8 lines
- **Progress**: done 2026-09-14 — isSemisimple_of_squarefree_aeval_eq_zero + separable_X_pow_sub_C (n := N); compiled (lake env lean / lake build).

### [Z9] `Matrix.norm_eq_one_of_eigenspace_ne_bot_of_pow_eq_one`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/TateFredholm/02_CharpolyPairingZ.lean
- **Depends on**: none
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/TateFredholm/02_CharpolyPairingZ.lean:114
/-- An eigenvalue of a matrix of finite order has norm one. -/
theorem norm_eq_one_of_eigenspace_ne_bot_of_pow_eq_one {Z : Matrix n n K} {N : ℕ} (hN : 0 < N)
    (hZ : Z ^ N = 1) {μ : K} (hμ : Module.End.eigenspace (Matrix.toLin' Z) μ ≠ ⊥) : ‖μ‖ = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hμ`; `rw [Module.End.mem_eigenspace_iff] at hv` (`toLin' Z v = μ • v`).
2. `have hpow : ∀ m : ℕ, (Matrix.toLin' Z ^ m) v = μ ^ m • v` by induction (`pow_succ'`, `LinearMap.mul_apply`, `hv`, `map_smul`, `smul_smul`).
3. `have h := hpow N; rw [← Matrix.toLin'_pow, hZ, Matrix.toLin'_one, LinearMap.one_apply] at h` ⇒ `v = μ ^ N • v`, so
   `μ ^ N = 1` by `smul_left_injective K hv0` (`(1 : K) • v = μ^N • v`).
4. `have := congrArg norm this; rw [norm_pow, norm_one] at this; exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 this`.

- **Mathlib/project lemmas needed**: `Submodule.ne_bot_iff`, `Module.End.mem_eigenspace_iff`, `Matrix.toLin'_pow`, `LinearMap.mul_apply`, `smul_left_injective`, `pow_eq_one_iff_of_nonneg`
- **Sources**: decomposition Z9.
- **Generality decision**: section `[IsAlgClosed K]` is unused here (record at CLEANUP-Z3: `omit [IsAlgClosed K] in`).
- **Size**: ~12 lines
- **Progress**: done 2026-09-14 — eigenvector v, μ^N = 1 via smul_left_injective; compiled (lake env lean / lake build).

### [CLEANUP-Z3] Cleanup `PhD/Main/TateFredholm/02_CharpolyPairingZ.lean`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/TateFredholm/02_CharpolyPairingZ.lean
- **Depends on**: Z7, Z8, Z9
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused `simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings; `lake build PhD` and `lake exe runLinter` on the module must be clean (grep the linter's output for the file).  Done inline by the main agent.  Add `omit [IsAlgClosed K] in` where the algebraic closure is unused (Z6, Z7, Z9).

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): as CLEANUP-Z1 (same file, one pass); `lake build PhD` green (3929 jobs).

### [Z10] `Module.End.norm_roots_charpoly_mul_of_iSup_eigenspace_eq_top` (the core)
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/TateFredholm/02_CharpolyPairingZ.lean
- **Depends on**: Z7
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/TateFredholm/02_CharpolyPairingZ.lean:97
/-- **Norms of the eigenvalues are unchanged by a commuting semisimple factor with eigenvalues of
norm one**: for `f g : End K V` commuting, with `V` spanned by the eigenspaces of `g` and every
eigenvalue of `g` of norm one, the characteristic roots of `f * g` have the same norms, with
multiplicity, as those of `f`.  Induction on `finrank V`, splitting off one eigenspace of `g`
(`Submodule.prodEquivOfIsCompl`, `LinearMap.charpoly_prodMap`, `LinearEquiv.charpoly_conj`). -/
theorem _root_.Module.End.norm_roots_charpoly_mul_of_iSup_eigenspace_eq_top
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] (f g : Module.End K V)
    (hfg : Commute f g) (hg : ⨆ μ : K, g.eigenspace μ = ⊤)
    (hnorm : ∀ μ : K, g.eigenspace μ ≠ ⊥ → ‖μ‖ = 1) :
    (f * g).charpoly.roots.map (fun x => ‖x‖) = f.charpoly.roots.map (fun x => ‖x‖) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Strong induction on `finrank K V` (`Nat.strong_induction_on` after `generalize hd : Module.finrank K V = d`, or
`induction' hd : Module.finrank K V using Nat.strong_induction_on with d ih generalizing V`).
1. **Case (a): some eigenspace is `⊤`** (`∃ μ, g.eigenspace μ = ⊤`).  Then `g = μ • 1` (`LinearMap.ext`, `Module.End.mem_eigenspace_iff`
   at every `v`), `f * g = μ • f` (`LinearMap.mul_apply`, `map_smul`), and `‖μ‖ = 1` (`hnorm`; `⊤ ≠ ⊥` needs `V ≠ 0` — if `V = 0`
   both charpolys are `1`, `Module.finrank_zero_iff`/`LinearMap.charpoly` of the zero space, handle first with `Subsingleton V`).
   Roots: `LinearMap.charpoly_toMatrix` with a basis `b := Module.finBasis K V`: `(μ • f).charpoly = (μ • toMatrix b b f).charpoly`
   (`LinearMap.toMatrix_smul`... `map_smul`), Z7 gives `roots.map (μ * ·)`, then `Multiset.map_map` and `norm_mul, hμ1, one_mul`.
2. **Case (b)**: pick `μ` with `g.eigenspace μ ≠ ⊥` (exists since `⨆ = ⊤ ≠ ⊥`, `iSup_eq_bot`), and `W := ⨆ ν ∈ {ν | ν ≠ μ}, g.eigenspace ν`.
   * `IsCompl (g.eigenspace μ) W`: disjointness from `Module.End.eigenspaces_iSupIndep g` (`iSupIndep` at `μ`: `Disjoint (V_μ) (⨆ ν ≠ μ, V_ν)`);
     `V_μ ⊔ W = ⊤` from `hg` (`iSup_split`/`sup_iSup` over `ν = μ` vs `ν ≠ μ`: `iSup_eq_iSup_of_split` — use `(biSup_le_iSup …)` and
     `le_antisymm`; concretely `⨆ ν, V_ν = V_μ ⊔ ⨆ ν ≠ μ, V_ν` is `iSup_split_single`/`iSup_eq_sup_iSup_ne`‑style: prove by `le_antisymm (iSup_le fun ν => by by_cases ν = μ …) (sup_le …)`).
   * Invariance: `f`, `g` map `V_μ` to itself (`Module.End.mapsTo_genEigenspace_of_comm hfg.symm μ 1` for `f` — note `eigenspace = genEigenspace _ 1`
     via `Module.End.eigenspace_def`; `g` trivially, `Module.End.mapsTo_genEigenspace_of_comm (Commute.refl g)`), and map `W` to itself
     (`Submodule.iSup_induction`‑style: images of `V_ν` land in `V_ν ≤ W`; use `Submodule.map_iSup` / `iSup_le`).
   * Split: with `e := Submodule.prodEquivOfIsCompl _ _ hcompl`, `F₁ := f.restrict hfμ`, `F₂ := f.restrict hfW`, `f = e.conj (F₁.prodMap F₂)`
     (`LinearMap.ext`, on `x = e (v, w)`: `Submodule.prodEquivOfIsCompl_apply`… follow `Mathlib/LinearAlgebra/Eigenspace/Zero.lean:160–182` verbatim:
     `have hψ : ψ = e.symm.conj φ := by ext ⟨v, w⟩ …; rw [← e.symm.charpoly_conj φ, ← hψ, LinearMap.charpoly_prodMap]`), so
     `f.charpoly = F₁.charpoly * F₂.charpoly`, and likewise `(f * g).charpoly = (F₁ * G₁).charpoly * (F₂ * G₂).charpoly` with `G₁ := g.restrict hgμ`, `G₂ := g.restrict hgW`
     (restriction of a product is the product of restrictions: `LinearMap.restrict_mul`/`LinearMap.ext` + `LinearMap.restrict_apply`).
   * On `V_μ`: `G₁ = μ • 1` (every vector is an eigenvector), so `F₁ * G₁ = μ • F₁` and the roots scale by `μ`, `‖μ‖ = 1` (as in case (a)).
   * On `W`: apply `ih` (`finrank W < finrank V` by `Submodule.finrank_add_eq_of_isCompl hcompl` and `finrank V_μ > 0`
     (`Submodule.finrank_pos_iff`/`Submodule.ne_bot_iff` + `finrank_pos`)) to `F₂`, `G₂`: `Commute F₂ G₂` (restrict of commuting maps),
     `⨆ ν, G₂.eigenspace ν = ⊤` (each `V_ν`, `ν ≠ μ`, sits inside `W` and inside the `ν`-eigenspace of `G₂`: `Submodule.mem_eigenspace_iff` + `Subtype.ext`;
     then `⊤ ≤ ⨆` because `W` is generated by them: `Submodule.iSup_induction`), and `hnorm` descends (an eigenvector of `G₂` is one of `g`: `Subtype.ext_iff`).
   * Assemble: `Polynomial.roots_mul` (charpolys are monic hence nonzero: `LinearMap.charpoly_monic`), `Multiset.map_add`, and the two pieces.
3. Use `Module.finBasis`, `LinearMap.charpoly_toMatrix` only in the scalar step; everything else at the `Module.End` level.

- **Mathlib/project lemmas needed**: `Module.End.eigenspaces_iSupIndep` (`Eigenspace/Basic.lean:720`), `Module.End.mapsTo_genEigenspace_of_comm` (`:367`), `Module.End.eigenspace_def`, `Submodule.prodEquivOfIsCompl` (`Projection.lean:76`), `LinearMap.charpoly_prodMap` (`Charpoly/ToMatrix.lean:63`), `LinearEquiv.charpoly_conj` (`:76`), `Submodule.finrank_add_eq_of_isCompl` (`FiniteDimensional/Lemmas.lean:243`), `LinearMap.charpoly_toMatrix`, `LinearMap.charpoly_monic`, `Polynomial.roots_mul`, `Multiset.map_add`, Z7
- **Sources**: decomposition Z10 (the one-split pattern quoted from `Mathlib/LinearAlgebra/Eigenspace/Zero.lean:160–182`; attacks [1]–[5]).
- **Generality decision**: `[NormedField K] [IsAlgClosed K] [CharZero K]` section but only `NormedField` + `FiniteDimensional` are used (record at cleanup: `omit [IsAlgClosed K] [CharZero K] in`).  Stated for `Module.End` so that Z11 transports through `Matrix.charpoly_toLin'`.
- **Size**: ~150 lines; source: 22 lines for one split (`Zero.lean`)
- **Progress**: done 2026-09-14 — private aux by strong induction on finrank; private charpoly_eq_mul_charpoly_restrict (Zero.lean pattern) and roots_charpoly_smul_end; compiled first full pass; compiled (lake env lean / lake build).

### [Z11] `Matrix.norm_roots_charpoly_mul_of_commute_of_pow_eq_one`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/TateFredholm/02_CharpolyPairingZ.lean
- **Depends on**: Z8, Z9, Z10
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/TateFredholm/02_CharpolyPairingZ.lean:119
/-- **The norms of the characteristic roots of `M Z` are those of `M`** for `Z` of finite order
commuting with `M`. -/
theorem norm_roots_charpoly_mul_of_commute_of_pow_eq_one {M Z : Matrix n n K}
    (hMZ : M * Z = Z * M) {N : ℕ} (hN : 0 < N) (hZ : Z ^ N = 1) :
    (M * Z).charpoly.roots.map (fun x => ‖x‖) = M.charpoly.roots.map (fun x => ‖x‖) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `rw [← Matrix.charpoly_toLin' (M * Z), ← Matrix.charpoly_toLin' M, Matrix.toLin'_mul]` (`Charpoly/ToMatrix.lean:94`; `toLin'_mul` gives `comp`, which is `*` in `Module.End` — `rfl`/`LinearMap.mul_eq_comp`).
2. `exact Module.End.norm_roots_charpoly_mul_of_iSup_eigenspace_eq_top (Matrix.toLin' M) (Matrix.toLin' Z) hcomm hsup hnorm` with
   `hcomm : Commute (toLin' M) (toLin' Z)` from `hMZ` (`Commute`, `← Matrix.toLin'_mul`, `hMZ`),
   `hsup := (isSemisimple_toLin'_of_pow_eq_one hN hZ).iSup_eigenspace_eq_top` (`Semisimple.lean:92`, needs `[IsAlgClosed K]`),
   `hnorm := fun μ hμ => norm_eq_one_of_eigenspace_ne_bot_of_pow_eq_one hN hZ hμ`.

- **Mathlib/project lemmas needed**: `Matrix.charpoly_toLin'`, `Matrix.toLin'_mul`, `Module.End.IsSemisimple.iSup_eigenspace_eq_top`, Z8, Z9, Z10
- **Sources**: decomposition Z11.
- **Generality decision**: as the statement; `IsAlgClosed` used exactly once.
- **Size**: ~10 lines
- **Progress**: done 2026-09-14 — charpoly_toLin' + Z10 + IsSemisimple.iSup_eigenspace_eq_top; compiled (lake env lean / lake build).

### [Z12] `Matrix.norm_roots_charpoly_of_mul_eq_smul_mul` (R_Z)
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/TateFredholm/02_CharpolyPairingZ.lean
- **Depends on**: Z3, Z4, Z11
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/TateFredholm/02_CharpolyPairingZ.lean:126
/-- **The pairing of characteristic roots up to a finite-order operator**: if `A B = c Z` with `Z`
commuting with `A` and `Z^N = 1`, the norms of the characteristic roots of `B` are `‖c‖` divided by
those of `A`, with multiplicity (`roots_charpoly_of_mul_eq_smul` at `M := c • A⁻¹`, then
`norm_roots_charpoly_mul_of_commute_of_pow_eq_one`). -/
theorem norm_roots_charpoly_of_mul_eq_smul_mul {A B Z : Matrix n n K} {c : K} (hc : c ≠ 0)
    (h : A * B = c • Z) (hZA : Z * A = A * Z) {N : ℕ} (hN : 0 < N) (hZ : Z ^ N = 1) :
    B.charpoly.roots.map (fun x => ‖x‖) = A.charpoly.roots.map (fun x => ‖c‖ / ‖x‖) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `have hA0 := det_ne_zero_of_mul_eq_smul_mul hc h hN hZ`; `set M := c • A⁻¹`; `have hAM : A * M = c • 1 := by rw [Matrix.mul_smul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hA0)]`.
2. `have hB : B = M * Z := by rw [Matrix.smul_mul, ← Matrix.mul_smul... ]` — cleanly: `B = A⁻¹ * (A * B) = A⁻¹ * (c • Z) = (c • A⁻¹) * Z` (`Matrix.nonsing_inv_mul`, `Matrix.mul_smul`, `Matrix.smul_mul`).
3. `have hMZ : M * Z = Z * M`: from `hZA` and `Matrix.nonsing_inv` as in Z4 step 3 (`Z * A⁻¹ = A⁻¹ * Z`), then `Matrix.smul_mul`/`Matrix.mul_smul`.
4. `rw [hB, norm_roots_charpoly_mul_of_commute_of_pow_eq_one hMZ hN hZ, Matrix.roots_charpoly_of_mul_eq_smul hc hAM, Multiset.map_map]`;
   `exact Multiset.map_congr rfl fun x _ => by simp [norm_div]`.

- **Mathlib/project lemmas needed**: Z3, Z4 (its step 3), Z11, `Matrix.roots_charpoly_of_mul_eq_smul` (`01_CharpolyPairing.lean:180`), `Matrix.mul_nonsing_inv`, `Matrix.nonsing_inv_mul`, `norm_div`, `Multiset.map_map`
- **Sources**: decomposition Z12; [Miyake, Thm 4.6.17] via `bu04.txt:1120–1124` (the classical shape; cited only).
- **Generality decision**: as the statement; `Z = 1` recovers the scalar pairing up to norms.
- **Size**: ~15 lines
- **Progress**: done 2026-09-14 — M := c • A⁻¹, B = M Z, Z11 + roots_charpoly_of_mul_eq_smul; compiled (lake env lean / lake build).

### [CLEANUP-Z-FINAL] Cleanup `PhD/Main/TateFredholm/02_CharpolyPairingZ.lean`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/TateFredholm/02_CharpolyPairingZ.lean
- **Depends on**: Z10, Z11, Z12
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused `simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings; `lake build PhD` and `lake exe runLinter` on the module must be clean (grep the linter's output for the file).  Done inline by the main agent.  Final per-file cleanup: remove the "SKELETON" marker from the module docstring; `#print axioms Matrix.norm_roots_charpoly_of_mul_eq_smul_mul` must be `[propext, Classical.choice, Quot.sound]`.

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): `02_CharpolyPairingZ` warning-free after the pass; `lake build PhD` green (3929 jobs).

### [Z13] `LWX.norm_roots_charpoly_atkinLehnerZ`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/05_AtkinLehner.lean
- **Depends on**: Z12
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/05_AtkinLehner.lean:291
/-- **The reduction, slope form, at a general tame level** (board `lwx-quaternion`): with
`A B = c·Z`, `Z` commuting with `A` and of finite order, `Q P = 1` and `A' = P B Q`, the norms of
the characteristic roots on the `ψ⁻¹`-space are `‖c‖` divided by those on the `ψ`-space, with
multiplicity (`Matrix.norm_roots_charpoly_of_mul_eq_smul_mul`, `Matrix.charpoly_conj`). -/
theorem norm_roots_charpoly_atkinLehnerZ {A B A' P Q Z : Matrix ι ι K} {c : K} (hc : c ≠ 0)
    (hAB : A * B = c • Z) (hZA : Z * A = A * Z) {N : ℕ} (hN : 0 < N) (hZ : Z ^ N = 1)
    (hQP : Q * P = 1) (hA' : A' = P * B * Q) :
    A'.charpoly.roots.map (fun x => ‖x‖) = A.charpoly.roots.map (fun x => ‖c‖ / ‖x‖) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `rw [hA', Matrix.charpoly_conj P Q B hQP]` (`01_CharpolyPairing.lean:67`: `(P * M * Q).charpoly = M.charpoly`).
2. `exact Matrix.norm_roots_charpoly_of_mul_eq_smul_mul hc hAB hZA hN hZ` — the shape of the conclusion matches `norm_roots_charpoly_atkinLehner` (`05:277`) exactly.

- **Mathlib/project lemmas needed**: `Matrix.charpoly_conj`, Z12
- **Sources**: decomposition Z13.
- **Generality decision**: `section SlopesZ` with `[NormedField K] [IsAlgClosed K] [CharZero K]`.
- **Size**: 2 lines
- **Progress**: done 2026-09-14 — charpoly_conj + Z12; compiled (lake env lean / lake build).

### [Z14] `LWX.AtkinLehnerHypothesis.toZ`, `LWX.norm_roots_charpoly_of_atkinLehnerHypothesisZ`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/13_AtkinLehnerInst.lean
- **Depends on**: Z13
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/13_AtkinLehnerInst.lean:243
omit [DecidableEq ι] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The scalar hypothesis is the case `Z = 1` of the general one. -/
theorem AtkinLehnerHypothesis.toZ {h k : ℕ}
    {A B A' : Matrix (Fin (Fintype.card ι * ((k + 1) * p ^ h)))
      (Fin (Fintype.card ι * ((k + 1) * p ^ h))) K}
    (hAL : AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ h k A B A') :
    AtkinLehnerHypothesisZ (p := p) (K := K) (ι := ι) ψ h k A B A' := by
  sorry
```
```lean
-- PhD/Main/LWX/13_AtkinLehnerInst.lean:252
omit [DecidableEq ι] [IsUltrametricDist K] [CompleteSpace K] in
/-- **[LWX, Prop 3.22] at a general tame level, granted H1**: the norms of the characteristic roots
of `U_p` on the `ψ⁻¹`-classical space are `‖p‖^{k+1}` divided by those on the `ψ`-classical space,
with multiplicity (`norm_roots_charpoly_atkinLehnerZ`). -/
theorem norm_roots_charpoly_of_atkinLehnerHypothesisZ [IsAlgClosed K] (h k : ℕ)
    {A B A' : Matrix (Fin (Fintype.card ι * ((k + 1) * p ^ h)))
      (Fin (Fintype.card ι * ((k + 1) * p ^ h))) K}
    (hAL : AtkinLehnerHypothesisZ (p := p) (K := K) (ι := ι) ψ h k A B A') :
    A'.charpoly.roots.map (fun x => ‖x‖)
      = A.charpoly.roots.map (fun x => ‖(ψ p) ^ (k + 1)‖ / ‖x‖) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `toZ`: `obtain ⟨hAB, P, Q, hQP, hA'⟩ := hAL; exact ⟨⟨1, 1, one_pos, hAB, by rw [Matrix.one_mul, Matrix.mul_one], pow_one 1⟩, P, Q, hQP, hA'⟩`.
2. `norm_roots…Z`: `obtain ⟨⟨Z, N, hN, hAB, hZA, hZN⟩, P, Q, hQP, hA'⟩ := hAL`; `hψp : ψ (p : ℚ_[p]) ≠ 0` as at `13:278–280`;
   `exact norm_roots_charpoly_atkinLehnerZ (pow_ne_zero _ hψp) hAB hZA hN hZN hQP hA'`.
   (This ticket is deleted/renamed at S0: `toZ` goes, `…Z` becomes `norm_roots_charpoly_of_atkinLehnerHypothesis`.)

- **Mathlib/project lemmas needed**: Z13, `pow_ne_zero`, `map_zero`/`RingHom.injective`
- **Sources**: decomposition Z14; pattern `13_AtkinLehnerInst.lean:271–281`.
- **Generality decision**: as the statements (`[IsAlgClosed K]` only on the second).
- **Size**: ~10 lines
- **Progress**: done 2026-09-14 — toZ with Z = 1, N = 1; norm form via Z13; compiled (lake env lean / lake build).

### [Z15] `LWX.neg_log_norm_det_add_of_mul_eq_smul_mul`, `LWX.det_ne_zero_of_mul_eq_smul_mul_conj`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/14_Touching.lean
- **Depends on**: Z1, Z3, Z5
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/14_Touching.lean:152
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- **H1 on determinants at a general tame level** (board `lwx-quaternion`): from `A·B = c·Z`,
`Z^N = 1`, `Q·P = 1` and `A' = P·B·Q`, `−log‖det A‖ − log‖det A'‖ = card·(−log‖c‖)`, since
`‖det Z‖ = 1` (`Matrix.norm_det_eq_one_of_pow_eq_one`). -/
theorem neg_log_norm_det_add_of_mul_eq_smul_mul {n : Type*} [Fintype n] [DecidableEq n]
    {A B A' P Q Z : Matrix n n K} {c : K} (hc : c ≠ 0) (hAB : A * B = c • Z) {N : ℕ}
    (hN : 0 < N) (hZ : Z ^ N = 1) (hQP : Q * P = 1) (hA' : A' = P * B * Q) :
    -Real.log ‖A.det‖ + -Real.log ‖A'.det‖ = Fintype.card n * (-Real.log ‖c‖) := by
  sorry
```
```lean
-- PhD/Main/LWX/14_Touching.lean:162
omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The Atkin–Lehner partner's determinant is nonzero at a general tame level. -/
theorem det_ne_zero_of_mul_eq_smul_mul_conj {n : Type*} [Fintype n] [DecidableEq n]
    {A B A' P Q Z : Matrix n n K} {c : K} (hc : c ≠ 0) (hAB : A * B = c • Z) {N : ℕ}
    (hN : 0 < N) (hZ : Z ^ N = 1) (hQP : Q * P = 1) (hA' : A' = P * B * Q) : A'.det ≠ 0 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. Copy `neg_log_norm_det_add_of_mul_eq_smul` (`14:107–128`) with: `hprod := Matrix.det_mul_det_of_mul_eq_smul_mul hAB` (`A.det * B.det = c^n * Z.det`),
   `hA0 := Matrix.det_ne_zero_of_mul_eq_smul_mul hc hAB hN hZ`, `hB0 := Matrix.det_ne_zero_of_mul_eq_smul_mul' hc hAB hN hZ`,
   `hZ1 := Matrix.norm_det_eq_one_of_pow_eq_one hN hZ`; in `hlog`: `norm_mul, hprod, norm_mul, hZ1, mul_one, norm_pow, Real.log_pow`; `hA'B` as before; `linarith`.
2. `det_ne_zero_…_conj`: copy `14:133–147` with `hB0` from Z3'.

- **Mathlib/project lemmas needed**: Z1, Z3, Z5, `Matrix.det_mul`, `Real.log_mul`, `Real.log_pow`, `norm_mul`, `norm_pow`
- **Sources**: decomposition Z15; the originals `14_Touching.lean:107–147` (deleted at S0).
- **Generality decision**: as the statements.
- **Size**: ~25 lines
- **Progress**: done 2026-09-14 — copies of the scalar lemmas with ‖det Z‖ = 1; compiled (lake env lean / lake build).

### [CLEANUP-Z4] Cleanup `PhD/Main/LWX/05_AtkinLehner.lean, 13_AtkinLehnerInst.lean, 14_Touching.lean (board sections)`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/05_AtkinLehner.lean, 13_AtkinLehnerInst.lean, 14_Touching.lean (board sections)
- **Depends on**: Z13, Z14, Z15
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused `simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings; `lake build PhD` and `lake exe runLinter` on the module must be clean (grep the linter's output for the file).  Done inline by the main agent.

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): 05/14 board annotations stripped, 14's long `hA'0` line split; 13's module doc updated to the `Z`-form H1 and `norm_roots_charpoly_of_atkinLehnerHypothesis`; `lake build PhD` green (3929 jobs).

### [L3] `LWX.inv_mem_Iw` [NEW DECL]
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/10_AtkinLehnerLocal.lean
- **Depends on**: none
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**New declaration(s) to add** (`[NEW DECL]`; state exactly as below, then prove):
```lean
/-- `Iw_p` is closed under inversion: `(a b; c d)⁻¹ = det⁻¹·(d, −b; −c, a)` has integral entries,
`‖−c/det‖ ≤ p⁻¹` and unit determinant (board `lwx-quaternion`; insert before
`exists_mem_Iw_mul_vQ`). -/
theorem inv_mem_Iw {g : Matrix (Fin 2) (Fin 2) ℚ_[p]} (hg : g ∈ Iw p 1) : g⁻¹ ∈ Iw p 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `obtain ⟨h1, h2, h3⟩ := hg` (`mem_Iw_iff`, `05:168`: entries `≤ 1`, `‖g 1 0‖ ≤ p⁻¹ ^ 1`, `‖det‖ = 1`); `have hd : g.det ≠ 0 := by intro h0; rw [h0, norm_zero] at h3; exact zero_ne_one h3`.
2. `rw [Matrix.inv_def, Matrix.adjugate_fin_two]` (`Adjugate.lean:373`): `g⁻¹ = Ring.inverse g.det • !![g 1 1, -g 0 1; -g 1 0, g 0 0]`; `Ring.inverse_eq_inv`, `‖g.det⁻¹‖ = 1` (`norm_inv`, `h3`).
3. Entries: `‖det⁻¹ * e‖ = ‖e‖ ≤ 1` for each entry `e` (`norm_mul`, `norm_neg`); lower-left `‖det⁻¹ * -g 1 0‖ = ‖g 1 0‖ ≤ p⁻¹`; determinant `‖det g⁻¹‖ = ‖(det g)⁻¹‖ = 1` (`Matrix.det_nonsing_inv`, `Ring.inverse_eq_inv`).
   Discharge the entry goals with `fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, norm_mul, norm_neg, norm_inv, h3, h1]`.

- **Mathlib/project lemmas needed**: `mem_Iw_iff`, `Matrix.inv_def`, `Matrix.adjugate_fin_two`, `Matrix.det_nonsing_inv`, `Ring.inverse_eq_inv`, `norm_inv`, `norm_mul`, `norm_neg`
- **Sources**: decomposition Q9 (sub-leaf `inv_mem_Iw`, grep 2026-09-14: absent from `05`/`10`).
- **Generality decision**: level `1` only (all consumers are at level `1`; the level-`m` version is not needed).
- **Size**: ~25 lines
- **Progress**: done 2026-09-14 — inv_def + adjugate_fin_two, simp [h1, h3]; compiled (lake env lean / lake build).

### [L1] `LWX.exists_mem_Iw_mul_vQ`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/10_AtkinLehnerLocal.lean
- **Depends on**: none
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/10_AtkinLehnerLocal.lean:430
/-- **The Iwahori decomposition** ([LWX, §2.5]: "`Iw_q (p 0; 0 1) Iw_q = ∐_{j=0}^{p−1} Iw_q v_j`,
for example with `v_j = (p 0; jq 1)`"): `(p 0; 0 1)·k`, `k ∈ Iw_p`, lies in `Iw_p·v_c` for some
`c < p`. -/
theorem exists_mem_Iw_mul_vQ {k : Matrix (Fin 2) (Fin 2) ℚ_[p]} (hk : k ∈ Iw p 1) :
    ∃ c : Fin p, ∃ k' ∈ Iw p 1, vQ p 0 * k = k' * vQ p (c : ℕ) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Write `k = !![a, b; c, d]` (`a := k 0 0` …); `obtain ⟨h1, h2, h3⟩ := hk`.
1. `hd : ‖d‖ = 1`: `‖a * d‖ = ‖det + b * c‖ = 1` since `‖b * c‖ ≤ p⁻¹ < 1 = ‖det‖` (`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` or `norm_add_eq_of_lt`), and `‖a‖ ≤ 1`, `‖d‖ ≤ 1` (`Matrix.det_fin_two`).  (Same shape as `norm_apply_zero_zero_of_mem_Iw`, `05:173`.)
2. The residue: `x := c / p * d⁻¹`, `‖x‖ ≤ 1` (`‖c‖ ≤ p⁻¹`, `Padic.norm_p`, `norm_inv`, `hd`); `xZ : ℤ_[p] := ⟨x, hx⟩`; `j := (PadicInt.toZMod xZ).val`, `hj : j < p := ZMod.val_lt _`; the coset `⟨j, hj⟩ : Fin p`.
   `hres : ‖x - j‖ ≤ p⁻¹`: `PadicInt.toZMod_spec xZ` (`RingHoms.lean:318`: `xZ - ZMod.cast (toZMod xZ) ∈ maximalIdeal ℤ_[p]`), `PadicInt.maximalIdeal_eq_span_p`, `Ideal.mem_span_singleton`, then `PadicInt.norm_le_pow_iff_mem_span_pow` at `n = 1` (or `norm_lt_one_iff_dvd` + `PadicInt.norm_le_pow_iff_norm_lt_pow_add_one`); the cast `(j : ℤ_[p]) = ZMod.cast (toZMod xZ)` is `ZMod.natCast_val`/`ZMod.natCast_zmod_val`; read the bound in `ℚ_p` via `PadicInt.norm_def`/`PadicInt.coe_sub`.
3. `k' := !![a - j * p * b, p * b; c / p - j * d, d]`; `refine ⟨⟨j, hj⟩, k', ⟨?_, ?_, ?_⟩, ?_⟩`:
   entries `≤ 1` (ultrametric sums of products of integral elements; `c / p` integral from `h2`);
   lower-left: `c / p - j * d = d * (x - j)` (`field_simp`/`ring` with `hd ≠ 0`), so `‖·‖ = ‖d‖ * ‖x - j‖ ≤ p⁻¹` (`hres`);
   determinant: `k'.det = k.det` (`Matrix.det_fin_two`, `field_simp`, `ring`), norm `1`;
   the identity `vQ p 0 * k = k' * vQ p j`: `ext i j'; fin_cases i <;> fin_cases j' <;> simp [vQ, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring`
   (`vQ p c = !![p, 0; c * p, 1]`, `10:41`; `(vQ p j)⁻¹ = !![p⁻¹, 0; -j, 1]`).

- **Mathlib/project lemmas needed**: `Matrix.det_fin_two`, `Padic.norm_p`, `PadicInt.toZMod`, `PadicInt.toZMod_spec`, `PadicInt.maximalIdeal_eq_span_p`, `Ideal.mem_span_singleton`, `PadicInt.norm_le_pow_iff_mem_span_pow`, `ZMod.val_lt`, `ZMod.natCast_val`, `IsUltrametricDist.norm_add_le_max`, `vQ`, `norm_apply_zero_zero_of_mem_Iw`
- **Sources**: [LWX, §2.5] `lwx.txt:706–711` ("`Iw_q (p 0; 0 1) Iw_q = ∐_{j=0}^{p−1} Iw_q v_j`, for example with `v_j = (p 0; jq 1)`"); decomposition L1.
- **Generality decision**: level `1` (`q = p`); `p = 2` allowed.
- **Size**: ~80 lines; source: 1 line (asserted)
- **Progress**: done 2026-09-14 — d-entry unit via swapped matrix; residue via PadicInt.toZMod_spec + maximalIdeal_eq_span_p (subtype element named by obtain to avoid the implicit-transparency rw trap); compiled (lake env lean / lake build).

### [L2] `LWX.eq_of_vQ_eq_mul_vQ`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/10_AtkinLehnerLocal.lean
- **Depends on**: none
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/10_AtkinLehnerLocal.lean:437
/-- The cosets `Iw_p·v_c`, `c < p`, are pairwise distinct. -/
theorem eq_of_vQ_eq_mul_vQ {b c : Fin p} {k : Matrix (Fin 2) (Fin 2) ℚ_[p]} (hk : k ∈ Iw p 1)
    (h : vQ p (b : ℕ) = k * vQ p (c : ℕ)) : b = c := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. Read the `(1, 0)` entry of `h`: `(vQ p b) 1 0 = b * p` and `(k * vQ p c) 1 0 = k 1 0 * p + k 1 1 * (c * p)` (`Matrix.mul_apply`, `Fin.sum_univ_two`, `vQ`), so
   `k 1 0 = (b - c) - k 1 1 * c`… cleaner: read the `(1,1)` entry first: `1 = k 1 0 * 0 + k 1 1 * 1`, so `k 1 1 = 1`; then the `(1,0)` entry gives `k 1 0 * p = (b - c) * p`, i.e. `k 1 0 = (b : ℚ_p) - c`.
2. `hk.2.1 : ‖k 1 0‖ ≤ p⁻¹ ^ 1` ⇒ `‖((b : ℤ) - c : ℤ) : ℚ_p)‖ ≤ p⁻¹` ⇒ `(p : ℤ) ∣ (b - c)` (`Padic.norm_int_le_pow_iff_dvd (b - c) 1`, `PadicNumbers.lean:961`, after `Int.cast_sub`/`Int.cast_natCast`, `zpow_neg_one`).
3. `|b - c| < p` (`Fin.isLt`), so `b - c = 0` (`Int.eq_zero_of_abs_lt_dvd`), hence `b = c` (`Fin.ext`, `omega` after `Int.natCast_inj`).

- **Mathlib/project lemmas needed**: `Matrix.mul_apply`, `Fin.sum_univ_two`, `vQ`, `Padic.norm_int_le_pow_iff_dvd`, `Int.eq_zero_of_abs_lt_dvd`, `Fin.ext`, `omega`
- **Sources**: decomposition L2 (uniqueness of the coset in `∐`, `lwx.txt:706–711`).
- **Generality decision**: as the statement.
- **Size**: ~25 lines
- **Progress**: done 2026-09-14 — entries (1,1),(1,0); Padic.norm_int_le_pow_iff_dvd + Int.eq_zero_of_abs_lt_dvd; compiled (lake env lean / lake build).

### [CLEANUP-L] Cleanup `PhD/Main/LWX/10_AtkinLehnerLocal.lean`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/10_AtkinLehnerLocal.lean
- **Depends on**: L1, L2, L3
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused `simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings; `lake build PhD` and `lake exe runLinter` on the module must be clean (grep the linter's output for the file).  Done inline by the main agent.  Final per-file cleanup of the board section of this file.

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): `10_AtkinLehnerLocal`: annotations stripped, long `abs_sub_lt_iff` line split; `lake build PhD` green (3929 jobs).

### [C1] `translateOp` API: `translateOp_add`, `translateOp_smul`, `translateOp_one`, `translateOp_translateOp`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/10_DiscForms.lean
- **Depends on**: none
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/10_DiscForms.lean:302
/-- **Right translation** by `z`: `(translateOp z φ)(x) = φ(x·z⁻¹)`.  For `z = ιp(p·1)` the local
central element, this is the tame central operator `Z` of the Atkin–Lehner identity
`U_p ∘ W⁻¹ ∘ U_p^{ψ⁻¹} ∘ W = p^{k+1}·Z` at a general tame level. -/
def translateOp (z : G) (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) :
    AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K) where
  toFun x := φ (x * z⁻¹)
  left_invt γ hγ g := by rw [mul_assoc]; exact φ.left_invt γ hγ _
```
```lean
-- PhD/Main/LWX/10_DiscForms.lean:314
theorem translateOp_add (z : G) (φ φ' : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) :
    translateOp z (φ + φ') = translateOp z φ + translateOp z φ' := by
  sorry
```
```lean
-- PhD/Main/LWX/10_DiscForms.lean:318
theorem translateOp_smul (z : G) (r : K) (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) :
    translateOp z (r • φ) = r • translateOp z φ := by
  sorry
```
```lean
-- PhD/Main/LWX/10_DiscForms.lean:322
theorem translateOp_one (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) :
    translateOp (1 : G) φ = φ := by
  sorry
```
```lean
-- PhD/Main/LWX/10_DiscForms.lean:326
theorem translateOp_translateOp (z z' : G) (φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) :
    translateOp z (translateOp z' φ) = translateOp (z' * z) φ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
All four by `AutomorphicFunction.ext fun x => ?_` then `simp only [translateOp_apply, AutomorphicFunction.add_apply, AutomorphicFunction.smul_apply, inv_one, mul_one, mul_inv_rev, mul_assoc]` (`QMF/01_AutomorphicFunction.lean:55, 78, 121`).
`translateOp_translateOp`: `(x * z⁻¹) * z'⁻¹ = x * (z' * z)⁻¹` is `mul_inv_rev` + `mul_assoc`.

- **Mathlib/project lemmas needed**: `AutomorphicFunction.ext`, `AutomorphicFunction.add_apply`, `AutomorphicFunction.smul_apply`, `mul_inv_rev`, `mul_assoc`, `inv_one`, `mul_one`
- **Sources**: Buzzard `bu04.txt:633` (`(f|η)(g) = f(gη⁻¹)η_p`, trivial weight action); decomposition C1.
- **Generality decision**: generic level `h` (`variable {h}` in `section Translate`); no hypothesis on `z`.
- **Size**: ~8 lines total
- **Progress**: done 2026-09-14 — AutomorphicFunction.ext + rfl/simp; compiled (lake env lean / lake build).

### [C2] `LWX.apply_mul_of_theta_eq_one'`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/10_DiscForms.lean
- **Depends on**: none
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/10_DiscForms.lean:330
/-- **A level element with trivial `p`-component acts trivially** on disc forms at every level. -/
theorem apply_mul_of_theta_eq_one' {φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)}
    (hφ : φ ∈ DiscForms (Γ := Γ) θ h ψ κ U hU) (x : G) {u : G} (hu : u ∈ U) (hθ : θ u = 1) :
    φ (x * u) = φ x := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Copy `apply_mul_of_theta_eq_oneH` (`20_AtkinLehnerMapH.lean:428–433`) with `h` generic:
`have h := (mem_discForms_iff θ h ψ κ U hU φ).1 hφ ⟨u, hu⟩ x`; the slash matrix is `⟨θ u, hU hu⟩ = ⟨1, _⟩`, so `rw [h]`, rewrite the `M1` element to `1` (`Subtype.ext hθ`) and `discSlash_one`.

- **Mathlib/project lemmas needed**: `mem_discForms_iff` (`10:79`), `discSlash_one`, `Subtype.ext`
- **Sources**: decomposition C2 (the level-`h` generic copy of `18:486`/`20:428`).
- **Generality decision**: generic `h`.
- **Size**: 4 lines
- **Progress**: done 2026-09-14 — copy of apply_mul_of_theta_eq_one (discSlash_one); compiled (lake env lean / lake build).

### [C3] `LWX.translateOp_mem_discForms`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/10_DiscForms.lean
- **Depends on**: C1
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/10_DiscForms.lean:336
/-- Translation by an element commuting with the level preserves the disc forms. -/
theorem translateOp_mem_discForms {z : G} (hz : ∀ u ∈ U, z * u = u * z)
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)}
    (hφ : φ ∈ DiscForms (Γ := Γ) θ h ψ κ U hU) :
    translateOp z φ ∈ DiscForms (Γ := Γ) θ h ψ κ U hU := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `rw [mem_discForms_iff] at hφ ⊢; intro u g`.
2. `show φ (g * u * z⁻¹) = discSlash h ψ κ ⟨θ u, hU u.2⟩ (φ (g * z⁻¹))`; `have hz' : z⁻¹ * u = u * z⁻¹` from `hz u u.2` (`mul_inv_eq_iff_eq_mul`/`inv_mul_eq_iff_eq_mul`); `rw [mul_assoc, hz', ← mul_assoc]; exact hφ u (g * z⁻¹)`.

- **Mathlib/project lemmas needed**: `mem_discForms_iff`, `mul_assoc`, `mul_inv_eq_iff_eq_mul`
- **Sources**: decomposition C3 (`z` need only commute with `U`).
- **Generality decision**: minimal hypothesis `∀ u ∈ U, z * u = u * z`.
- **Size**: ~6 lines
- **Progress**: done 2026-09-14 — z⁻¹ commutes with u; mem_discForms_iff; compiled (lake env lean / lake build).

### [CLEANUP-C1] Cleanup `PhD/Main/LWX/10_DiscForms.lean`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/10_DiscForms.lean
- **Depends on**: C1, C2, C3
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused `simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings; `lake build PhD` and `lake exe runLinter` on the module must be clean (grep the linter's output for the file).  Done inline by the main agent.

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): `10_DiscForms`: section header, `omit` on `translateOp_one`, `translateOp_eq_self_of_eq_mul`, `translateOp_discHeckeOperator`; `lake build PhD` green (3929 jobs).

### [C4] `LWX.translateOp_eq_self_of_eq_mul`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/10_DiscForms.lean
- **Depends on**: C2
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/10_DiscForms.lean:343
/-- Translation by `γ u`, `γ ∈ Γ` central, `u ∈ U`, `θ u = 1`, is the identity on disc forms. -/
theorem translateOp_eq_self_of_eq_mul {z γ u : G} (hγ : γ ∈ Γ) (hγc : ∀ x, γ * x = x * γ)
    (hu : u ∈ U) (hθ : θ u = 1) (hz : z = γ * u)
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)}
    (hφ : φ ∈ DiscForms (Γ := Γ) θ h ψ κ U hU) : translateOp z φ = φ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`AutomorphicFunction.ext fun x => ?_`; `rw [translateOp_apply, hz, mul_inv_rev, ← mul_assoc]`; move `γ⁻¹` to the front with `hγc` (`γ⁻¹ * y = y * γ⁻¹` from `hγc`, as `hγc` at `19:193–196`), `AutomorphicFunction.left_invt' φ (inv_mem hγ)`, then `apply_mul_of_theta_eq_one' θ ψ κ U hU hφ x (inv_mem hu) hθinv` with `hθinv : θ u⁻¹ = 1` (`map_inv`/`19:203–206`).
This is `apply_mul_ιp_pGL_inv` (`19:130–135`) with `z` generic.

- **Mathlib/project lemmas needed**: C2, `AutomorphicFunction.left_invt'`, `inv_mem`, `mul_inv_rev`, `map_mul`/`mul_inv_cancel`
- **Sources**: decomposition C4; original `19_AtkinLehnerIdentity.lean:120–135`.
- **Generality decision**: generic `h`, generic central `γ`.
- **Size**: ~12 lines
- **Progress**: done 2026-09-14 — γ⁻¹ central, left_invt', C2; compiled (lake env lean / lake build).

### [C5] `LWX.translateOp_discHeckeOperator` (`Z` commutes with `U_p`)
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/10_DiscForms.lean
- **Depends on**: C1, C3
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/10_DiscForms.lean:350
/-- Translation by a central element commutes with `U_p`. -/
theorem translateOp_discHeckeOperator {z : G} (hz : ∀ x, z * x = x * z) {η : G}
    (hη : η ∈ levelM1 (p := p) θ)
    (hfin : (((Quotient.mk'' : G → RightCosets U) '' (({η} : Set G) * (U : Set G))) :
      Set (RightCosets U)).Finite) (φ : DiscForms (Γ := Γ) θ h ψ κ U hU) :
    ((discHeckeOperator θ h ψ κ U hU hη hfin
        ⟨translateOp z φ.1, translateOp_mem_discForms θ ψ κ U hU (fun u _ => hz u) φ.2⟩ :
          DiscForms (Γ := Γ) θ h ψ κ U hU) : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K))
      = translateOp z (discHeckeOperator θ h ψ κ U hU hη hfin φ :
          AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `letI := discLevelSlashAction θ h ψ κ; letI := discLevelSMulSlashClass θ h ψ κ`; `have : Fintype (… image …) := hfin.fintype`;
   `refine AutomorphicFunction.ext fun x => ?_`.
2. Both sides are `heckeOperatorSlash K hU hU hη hfin _` (`discHeckeOperator`, `10:179`): `change (heckeOperatorSlash K hU hU hη hfin ⟨translateOp z φ.1, _⟩ : AutomorphicFunction _ _ _) x = translateOp z (heckeOperatorSlash K hU hU hη hfin φ : AutomorphicFunction _ _ _) x`;
   `rw [translateOp_apply, heckeOperatorSlash_apply, heckeOperatorSlash_apply, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, hev, hev]` with the evaluation-of-a-sum lemma `hev` of `18:385–390` (`map_sum (AddMonoidHom.mk' (fun φ => φ g) (fun _ _ => rfl))`).
3. `refine Finset.sum_congr rfl fun i _ => ?_`; `rw [slash_apply, slash_apply, translateOp_apply]` (`QMF/Slash/03_AutomorphicFunction.lean:56`: `(φ ∣ₛ δ) g = φ (g * δ⁻¹) ∣ₛ δ`);
   `congr 2` down to `x * δ⁻¹ * z⁻¹ = x * z⁻¹ * δ⁻¹`: `simp only [mul_assoc]; rw [hz']` with `hz' : ∀ y, z⁻¹ * y = y * z⁻¹` from `hz` (`inv_mul_eq_iff_eq_mul`, `hz`, `mul_inv_cancel_right`).

- **Mathlib/project lemmas needed**: `AbstractHeckeOperatorSlash.heckeOperatorSlash_apply` (`QMF/Slash/03_HeckeMonoid.lean:191`), `finsum_eq_sum_of_fintype`, `AutomorphicFunction.slash_apply` (`Slash/03_AutomorphicFunction.lean:56`), `Finset.sum_congr`, `map_sum`
- **Sources**: Buzzard `bu04.txt:648–650` (`[UηU]f = ∑ᵢ f|ηᵢ`); decomposition C5 (risk: medium — the API shape; the pattern is `discHeckeOperator_mem_classicalDiscForms`, `18:380–408`).
- **Generality decision**: generic `h`, `z` central in `G` (what `ιp(p·1)` is).
- **Size**: ~25 lines
- **Progress**: done 2026-09-14 — show with the heckeOperatorSlash finsum spelled out (avoids DiscForms/slashFixedPoints subtype mismatch in rw), slash_apply, congr 2; compiled (lake env lean / lake build).

### [CLEANUP-C2] Cleanup `PhD/Main/LWX/10_DiscForms.lean`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/10_DiscForms.lean
- **Depends on**: C4, C5
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused `simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings; `lake build PhD` and `lake exe runLinter` on the module must be clean (grep the linter's output for the file).  Done inline by the main agent.  Final per-file cleanup of `section Translate`.

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): as CLEANUP-C1 (same file, one pass); `lake build PhD` green (3929 jobs).

### [C6] `centralOp_mem_classicalDiscForms`, `centralOpCl` (`map_add'`, `map_smul'`)
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/18_AtkinLehnerMap.lean
- **Depends on**: C1, C3
- **Parallel**: yes (within the dependency order)
- **Type**: proof/def

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/18_AtkinLehnerMap.lean:437
/-- **The tame central operator** `Z = translateOp (ιp(p·1))`: `(Zφ)(x) = φ(x·ιp(p·1)⁻¹)`.  At a
general tame level the Atkin–Lehner identity reads `U_p ∘ W⁻¹ ∘ U_p^{ψ⁻¹} ∘ W = p^{k+1}·Z`; `Z` is
the identity exactly when the tame scalar `p^{(p)}` lies in the level. -/
def centralOp (φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)) :
    AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K) :=
  translateOp (D.ιp (pGL p)) φ
```
```lean
-- PhD/Main/LWX/18_AtkinLehnerMap.lean:448
omit [CharZero K] in
theorem centralOp_mem_classicalDiscForms {φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ) :
    centralOp θG ψ U D φ ∈ ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ := by
  sorry
```
```lean
-- PhD/Main/LWX/18_AtkinLehnerMap.lean:454
/-- `Z` as a linear endomorphism of the classical disc forms. -/
def centralOpCl :
    ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ →ₗ[K] ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ where
  toFun φ := ⟨centralOp θG ψ U D φ.1, centralOp_mem_classicalDiscForms θG ψ U hU k D κ φ.2⟩
  map_add' φ φ' := by sorry
  map_smul' r φ := by sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. Membership: `rw [mem_classicalDiscForms_iff] at hφ ⊢` (`18:364`); `exact ⟨translateOp_mem_discForms θG ψ κ U hU (fun u _ => D.ιp_pGL_comm u) hφ.1, fun x => hφ.2 _⟩` (`centralOp φ x = φ (x * ιp(p)⁻¹)`, `centralOp_apply`).
2. `map_add' φ φ' := Subtype.ext (translateOp_add _ _ _)`, `map_smul' r φ := Subtype.ext (translateOp_smul _ _ _)` (`RingHom.id_apply`).

- **Mathlib/project lemmas needed**: C1, C3, `mem_classicalDiscForms_iff`, `Subtype.ext`
- **Sources**: decomposition C6.
- **Generality decision**: level `1`; argument order `centralOpCl θG ψ U hU k D κ`.
- **Size**: ~6 lines
- **Progress**: done 2026-09-14 — anonymous constructor ⟨translateOp_mem_discForms …, …⟩; needed omit [CharZero K] on translateOp_mem_discForms (10); compiled (lake env lean / lake build).

### [C7] `LWX.centralOpCl_pow_eq_one`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/18_AtkinLehnerMap.lean
- **Depends on**: C1, C4, C6
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/18_AtkinLehnerMap.lean:466
/-- `Z` has finite order (`central_pow`). -/
theorem centralOpCl_pow_eq_one : ∃ N, 0 < N ∧ centralOpCl θG ψ U hU k D κ ^ N = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `obtain ⟨N, hN, γ, hγ, u, hu, hP, hθu, hcomm⟩ := D.central_pow`; `refine ⟨N, hN, LinearMap.ext fun φ => Subtype.ext ?_⟩`; `rw [LinearMap.pow_apply, LinearMap.one_apply]`.
2. `have hiter : ∀ m (φ : ClassicalDiscForms …), (((centralOpCl θG ψ U hU k D κ)^[m] φ : _) : AutomorphicFunction _ _ _) = translateOp (D.ιp (pGL p) ^ m) φ.1` by induction on `m`: `Function.iterate_zero`/`pow_zero`/`translateOp_one`; `Function.iterate_succ_apply'`, `centralOpCl_apply`, `centralOp`, `translateOp_translateOp`, `pow_succ`.
3. `rw [hiter, hP]; exact translateOp_eq_self_of_eq_mul θG ψ κ U hU hγ hcomm hu hθu rfl φ.2.1`.

- **Mathlib/project lemmas needed**: C1, C4, `LinearMap.pow_apply`, `Function.iterate_succ_apply'`, `pow_succ`, `Subtype.ext`
- **Sources**: decomposition C7 (`N = 1` is the old `central`).
- **Generality decision**: as the statement.
- **Size**: ~15 lines
- **Progress**: done 2026-09-14 — iteration lemma by induction (explicit pow_succ args: bare pow_succ matched p ^ 1); compiled (lake env lean / lake build).

### [C8] `LWX.discHeckeOperatorCl_comp_centralOpCl`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/18_AtkinLehnerMap.lean
- **Depends on**: C5, C6
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/18_AtkinLehnerMap.lean:470
/-- `Z` commutes with `U_p`. -/
theorem discHeckeOperatorCl_comp_centralOpCl
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    {η : G} (hη : η ∈ levelM1 (p := p) θG)
    (hfin : (((Quotient.mk'' : G → RightCosets U) '' (({η} : Set G) * (U : Set G))) :
      Set (RightCosets U)).Finite) :
    (discHeckeOperatorCl θG ψ U hU k κ hκ hη hfin).comp (centralOpCl θG ψ U hU k D κ)
      = (centralOpCl θG ψ U hU k D κ).comp (discHeckeOperatorCl θG ψ U hU k κ hκ hη hfin) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`refine LinearMap.ext fun φ => Subtype.ext ?_`; `simp only [LinearMap.comp_apply]`; unfold both sides to `discHeckeOperator θG 1 ψ κ U hU hη hfin` on the first components (`discHeckeOperatorCl` is defined through it, `18:402–408`; `centralOpCl_apply`);
`exact translateOp_discHeckeOperator θG ψ κ U hU D.ιp_pGL_comm hη hfin ⟨φ.1, φ.2.1⟩` (the membership proof inside `⟨translateOp _ φ.1, _⟩` is a `Prop`, so the two subtypes agree by proof irrelevance — `Subtype.ext`/`rfl` after `show`).

- **Mathlib/project lemmas needed**: C5, `LinearMap.ext`, `LinearMap.comp_apply`, `Subtype.ext`
- **Sources**: decomposition C8.
- **Generality decision**: as the statement.
- **Size**: ~8 lines
- **Progress**: done 2026-09-14 — C5 at ⟨φ.1, φ.2.1⟩; compiled (lake env lean / lake build).

### [CLEANUP-C3] Cleanup `PhD/Main/LWX/18_AtkinLehnerMap.lean`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/18_AtkinLehnerMap.lean
- **Depends on**: C6, C7, C8
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused `simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings; `lake build PhD` and `lake exe runLinter` on the module must be clean (grep the linter's output for the file).  Done inline by the main agent.  Final per-file cleanup of the `centralOp` section.

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): `18_AtkinLehnerMap`: unused binders of `centralOpCl` → `_`, `omit [CharZero K] in` on `centralOpCl_pow_eq_one` and `discHeckeOperatorCl_comp_centralOpCl` (runLinter `unusedArguments`), two stray doubled `omit` lines before `vGL` (left by an earlier line-number insertion) removed, module/structure docstrings no longer describe the deleted `central` field, `theta_ιp_pGL` docstring, `Z` docstring softened ("identity when", not "exactly when"); `lake build PhD` green (3929 jobs).

### [C9] `centralOpH_mem_classicalDiscFormsH`, `centralOpClH`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/20_AtkinLehnerMapH.lean
- **Depends on**: C1, C3
- **Parallel**: yes (within the dependency order)
- **Type**: proof/def

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/20_AtkinLehnerMapH.lean:446
omit [CharZero K] in
theorem centralOpH_mem_classicalDiscFormsH {φ : AutomorphicFunction G Γ c(ZMod (p ^ h) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ) :
    centralOpH θG ψ U h D φ ∈ ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ := by
  sorry
```
```lean
-- PhD/Main/LWX/20_AtkinLehnerMapH.lean:452
/-- `Z` as a linear endomorphism of the level-`h` classical disc forms. -/
def centralOpClH :
    ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ →ₗ[K]
      ClassicalDiscFormsH (Γ := Γ) θG ψ U hU h k κ where
  toFun φ := ⟨centralOpH θG ψ U h D φ.1, centralOpH_mem_classicalDiscFormsH θG ψ U hU h k D κ φ.2⟩
  map_add' φ φ' := by sorry
  map_smul' r φ := by sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As C6 with `mem_classicalDiscFormsH_iff` (`20:363`), `ClassicalDiscFormsH` (`20:356`); order `centralOpClH θG ψ U hU h k D κ`.

- **Mathlib/project lemmas needed**: C1, C3, `mem_classicalDiscFormsH_iff`
- **Sources**: decomposition C9–C11.
- **Generality decision**: level `h`.
- **Size**: ~6 lines
- **Progress**: done 2026-09-14 — as C6; compiled (lake env lean / lake build).

### [C10] `LWX.centralOpClH_pow_eq_one`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/20_AtkinLehnerMapH.lean
- **Depends on**: C1, C4, C9
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/20_AtkinLehnerMapH.lean:465
/-- `Z` has finite order (`central_pow`). -/
theorem centralOpClH_pow_eq_one : ∃ N, 0 < N ∧ centralOpClH θG ψ U hU h k D κ ^ N = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As C7 with `centralOpClH_apply`, `centralOpH`, and `translateOp_eq_self_of_eq_mul` at level `h`.

- **Mathlib/project lemmas needed**: C1, C4
- **Sources**: decomposition C9–C11.
- **Generality decision**: level `h`.
- **Size**: ~15 lines
- **Progress**: done 2026-09-14 — as C7; compiled (lake env lean / lake build).

### [C11] `LWX.discHeckeOperatorClH_comp_centralOpClH`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/20_AtkinLehnerMapH.lean
- **Depends on**: C5, C9
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/20_AtkinLehnerMapH.lean:469
/-- `Z` commutes with `U_p`. -/
theorem discHeckeOperatorClH_comp_centralOpClH
    (hκ : ∀ g : M1Kh h ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    {η : G} (hη : η ∈ levelM1 (p := p) θG)
    (hfin : (((Quotient.mk'' : G → RightCosets U) '' (({η} : Set G) * (U : Set G))) :
      Set (RightCosets U)).Finite) :
    (discHeckeOperatorClH θG ψ U hU h k κ hκ hη hfin).comp (centralOpClH θG ψ U hU h k D κ)
      = (centralOpClH θG ψ U hU h k D κ).comp
          (discHeckeOperatorClH θG ψ U hU h k κ hκ hη hfin) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As C8 with `discHeckeOperatorClH` (`20:399`).

- **Mathlib/project lemmas needed**: C5
- **Sources**: decomposition C9–C11.
- **Generality decision**: level `h`.
- **Size**: ~8 lines
- **Progress**: done 2026-09-14 — as C8; compiled (lake env lean / lake build).

### [CLEANUP-C4] Cleanup `PhD/Main/LWX/20_AtkinLehnerMapH.lean`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/20_AtkinLehnerMapH.lean
- **Depends on**: C9, C10, C11
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused `simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings; `lake build PhD` and `lake exe runLinter` on the module must be clean (grep the linter's output for the file).  Done inline by the main agent.  Final per-file cleanup of the `centralOpH` section.

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): `20_AtkinLehnerMapH`: as CLEANUP-C3 at level `h` (omits on `centralOpClH_pow_eq_one`, `discHeckeOperatorClH_comp_centralOpClH`; stray doubled omits before `wGLH` removed); `lake build PhD` green (3929 jobs).

### [C12] `LWX.blockProj_zero_apply_term_eltZ`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/19_AtkinLehnerIdentity.lean
- **Depends on**: C6
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/19_AtkinLehnerIdentity.lean:467
omit [CharZero K] in
/-- **Disc `0` of `φ(x s_b p⁻¹ ℓ⁻¹)` at a general tame level**: the central `p⁻¹` is the tame
central operator `Z` (`ιp_pGL_comm`), and `ℓ⁻¹` fixes disc `0`. -/
theorem blockProj_zero_apply_term_eltZ
    (hκ : ∀ g : M1Kh 1 ψ, κ.toWeightSeries.autFactor g.1 * linX g.1
      = PowerSeries.C (nebK (g.1 1 1)) * linX g.1 ^ (k + 1))
    {φ : AutomorphicFunction G Γ c(ZMod (p ^ 1) × ℕ, K)}
    (hφ : φ ∈ ClassicalDiscForms (Γ := Γ) θG ψ U hU k κ) (x : G) (b c : Fin p) :
    cSpace.blockProj 0
        (φ (x * D.ιp (sGL p (b : ℕ)) * (D.ιp (pGL p))⁻¹ * (D.ιp (ℓGL p (b : ℕ) (c : ℕ)))⁻¹))
      = nebK (ψ (1 - (b : ℚ_[p]) * c * p)) •
        symAct K k (RingHom.mapMatrix ψ (tMatInv p 0 * ℓQinv p (b : ℕ) (c : ℕ) * tMat p 0))
          (cSpace.blockProj (b : ZMod (p ^ 1)) (centralOp θG ψ U D φ x)) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Copy the proof of `blockProj_zero_apply_term_elt` (the original, same file, `obtain ⟨γ, hγ, u, hu, hP, hθu, hcomm⟩ := D.central` … `rw [hmove, hmain, hgM, …, hsh]`) with these changes:
1. Drop the `obtain … := D.central`, `hγc`, `e1`, `e2`, `hθinv`, `hθ1` lines.
2. `hmove : φ (y * (D.ιp (pGL p))⁻¹ * ℓ⁻¹) = centralOp θG ψ U D φ (y * ℓ⁻¹)`: `rw [centralOp_apply, mul_assoc, mul_assoc, ← mul_inv_rev, ← mul_inv_rev, D.ιp_pGL_comm ℓ]`.
3. `hmain := blockProj_zero_apply_mul_ιp θG ψ U hU k κ D hκ (centralOp_mem_classicalDiscForms θG ψ U hU k D κ hφ) y hg hg0` (its `φ (y * ιp(ℓ⁻¹))` is `centralOp … φ (y * ℓ⁻¹)` after `map_inv`).
4. `hsh : cSpace.blockProj 0 (centralOp θG ψ U D φ y) = cSpace.blockProj (b : ZMod (p ^ 1)) (centralOp θG ψ U D φ x)` by `shapiro_blockProj θG ψ U hU D κ (centralOp_mem_classicalDiscForms … hφ).1 x b` and the `ZMod.val_natCast`/`Nat.mod_eq_of_lt` rewrite as in the original.
5. Final `rw` chain as in the original.

- **Mathlib/project lemmas needed**: C6, `blockProj_zero_apply_mul_ιp` (`19:140`), `shapiro_blockProj` (`18:518`), `coe_ℓGL_inv`, `ℓQinv_mem_Iw`, `discImage_ℓQinv_zero`, `discConj_ℓQinv_zero_one_one`, `coe_discConj`, `discConjMat_zero_of_discImage_zero`, `mul_inv_rev`
- **Sources**: decomposition C12 (docstring of the original quoted there); the only change is where `p⁻¹` lands.
- **Generality decision**: as the statement (`omit [CharZero K] in`).
- **Size**: ~45 lines; source: 50 lines (the original)
- **Progress**: done 2026-09-14 — hmove via hc' : (ιp p)⁻¹ ℓ⁻¹ = ℓ⁻¹ (ιp p)⁻¹ and `mul_assoc y` (bare mul_assoc unfolded the `set` variable y); needed omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] on centralOp_apply (18); lake build of 19/21/22 green.

### [C13] `LWX.atkinLehner_term_eqZ`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/19_AtkinLehnerIdentity.lean
- **Depends on**: C12
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/19_AtkinLehnerIdentity.lean:482
/-- The `(b, c)`-term of the double-coset expansion at a general tame level: as
`atkinLehner_term_eq`, with `Zφ` in place of `φ`. -/
theorem atkinLehner_term_eqZ
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
          (cSpace.blockProj (b : ZMod (p ^ 1)) (centralOp θG ψ U D φ.1 x))) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Copy `atkinLehner_term_eq` (original, same file) verbatim; the single change is the `hin` step (the original's `blockProj_zero_apply_term_elt … hφ x b c`) which becomes `blockProj_zero_apply_term_eltZ θG ψ U hU k κ D hκ φ.2 x b c`, and the final expression carries `centralOp θG ψ U D φ.1 x` where the original had `φ.1 x`.  The `χ` factors (`hχ`) are evaluated at `x v_c⁻¹`, `w`, `v_b` only — never at `ιp(p·1)`.

- **Mathlib/project lemmas needed**: C12 and the original's lemma list
- **Sources**: decomposition C13.
- **Generality decision**: as the statement.
- **Size**: ~85 lines; source: 85 lines (the original)
- **Progress**: done 2026-09-14 — original body with Zφ in place of φ (script-transformed); lake build of 19/21/22 green.

### [C14] `LWX.blockProj_zero_discHecke_atkinLehnerZ`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/19_AtkinLehnerIdentity.lean
- **Depends on**: C13
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/19_AtkinLehnerIdentity.lean:510
/-- **`U_p ∘ W⁻¹ ∘ U_p^{(ψ⁻¹)} ∘ W = p^{k+1}·Z` on disc `0`** at a general tame level. -/
theorem blockProj_zero_discHecke_atkinLehnerZ
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
      = (ψ p) ^ (k + 1) • cSpace.blockProj 0 (centralOp θG ψ U D φ.1 x) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Copy `blockProj_zero_discHecke_atkinLehner` (original): the double sum over `(b, c)` with `atkinLehner_term_eqZ` in place of `atkinLehner_term_eq`; the `b = 0` terms sum to `p · p^k • blockProj 0 (centralOp … φ.1 x)` (`Finset.sum_const`, `Finset.card_range`, `nsmul_eq_mul`, `pow_succ`), the `b ≠ 0` sums vanish by `hsum` exactly as before (the character sum does not see `Z`).

- **Mathlib/project lemmas needed**: C13 and the original's lemma list
- **Sources**: decomposition C14.
- **Generality decision**: as the statement.
- **Size**: ~100 lines; source: 100 lines (the original)
- **Progress**: done 2026-09-14 — original body + maxHeartbeats 1000000; lake build of 19/21/22 green.

### [CLEANUP-C5] Cleanup `PhD/Main/LWX/19_AtkinLehnerIdentity.lean`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/19_AtkinLehnerIdentity.lean
- **Depends on**: C12, C13, C14
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused `simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings; `lake build PhD` and `lake exe runLinter` on the module must be clean (grep the linter's output for the file).  Done inline by the main agent.

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): `19_AtkinLehnerIdentity`: module doc in the `Z`-form, duplicate section header merged, double blank lines removed, long lines split; `lake build PhD` green (3929 jobs).

### [C15] `LWX.discHeckeCl_comp_atkinLehnerZ`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/19_AtkinLehnerIdentity.lean
- **Depends on**: C14
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/19_AtkinLehnerIdentity.lean:538
/-- **The operator identity at a general tame level**:
`U_p ∘ (W⁻¹ ∘ U_p^{(ψ⁻¹)} ∘ W) = p^{k+1}·Z` on the classical disc forms. -/
theorem discHeckeCl_comp_atkinLehnerZ
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
      = (ψ p) ^ (k + 1) • centralOpCl θG ψ U hU k D κ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Copy `discHeckeCl_comp_atkinLehner` (original): `LinearMap.ext fun φ => Subtype.ext (AutomorphicFunction.ext fun x => ?_)`, reduce to disc `0` via `shapiro_blockProj` on both sides (on the right for `centralOpCl … φ`, whose membership is `(centralOpCl … φ).2`), and apply `blockProj_zero_discHecke_atkinLehnerZ`; `LinearMap.smul_apply`, `centralOpCl_apply`.

- **Mathlib/project lemmas needed**: C14, `shapiro_blockProj`, `centralOpCl_apply`, `LinearMap.smul_apply`
- **Sources**: decomposition C15.
- **Generality decision**: as the statement.
- **Size**: ~40 lines; source: 38 lines
- **Progress**: done 2026-09-14 — original body, hR at centralOpCl φ; lake build of 19/21/22 green.

### [C16] `LWX.atkinLehnerHypothesisZ_of_atkinLehnerData` **[MILESTONE: H1-Z at level 1]**
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/19_AtkinLehnerIdentity.lean
- **Depends on**: C7, C8, C15
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/19_AtkinLehnerIdentity.lean:724
/-- **Hypothesis H1 at the classical points, at a general tame level** (board `lwx-quaternion`):
`A B = p^{k+1}·Z` with `Z` the matrix of the tame central operator on the classical block model,
commuting with `A` (`discHeckeOperatorCl_comp_centralOpCl`) and of finite order
(`centralOpCl_pow_eq_one`), and `A' = W B W⁻¹`. -/
theorem atkinLehnerHypothesisZ_of_atkinLehnerData [Nonempty ι]
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
    ∃ B, AtkinLehnerHypothesisZ (p := p) (K := K) (ι := ι) ψ 1 k
      ((classicalData ψ ω θG U hU (vRepD θG ψ U D) (vRepD_mem_levelM1 θG ψ U D) uu hp2 hψ hζ
        hpK k).matrix idx) B
      ((classicalData ψ (partnerChar p ω k) θG U hU (vRepD θG ψ U D)
        (vRepD_mem_levelM1 θG ψ U D) uu hp2 hψ hζ.inv hpK k).matrix idx) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Copy `atkinLehnerHypothesis_of_atkinLehnerData` (original, `set_option maxHeartbeats 2000000 in`) and change:
1. `hkey`: the pointwise identity `T (Wb.symm (T' (Wb g))) = (ψ p)^{k+1} • E (Zcl g)` from `discHeckeCl_comp_atkinLehnerZ` (its `h3` step now reads `= (ψ p) ^ (k + 1) • E (centralOpCl … g)`).
2. Witnesses: `Zmat := LinearMap.toMatrix bas bas (E ∘ₗ centralOpCl θG ψ U hU k D κ ∘ₗ E.symm)` and `N` from `centralOpCl_pow_eq_one`; `refine ⟨B, ⟨Zmat, N, hN, ?_, ?_, ?_⟩, P, Q, hQP, hA'⟩` with the same `B`, `P`, `Q`.
3. `A * B = c • Zmat`: `LinearMap.toMatrix_comp` / `LinearMap.toMatrix_mul`, `map_smul` (`LinearMap.toMatrix` is linear), from `hkey`.
4. `Zmat * A = A * Zmat`: `discHeckeOperatorCl_comp_centralOpCl` conjugated by `E` — `A = toMatrix bas bas (E ∘ U_p ∘ E⁻¹)` (`hTE`), so both products are `toMatrix` of `E ∘ (U_p ∘ Z) ∘ E⁻¹` resp. `E ∘ (Z ∘ U_p) ∘ E⁻¹` (`LinearMap.comp_assoc`, `E.symm_comp_self`).
5. `Zmat ^ N = 1`: `(toMatrix bas bas f) ^ N = toMatrix bas bas (f ^ N)` (`LinearMap.toMatrix_pow`? — else `map_pow` of `LinearMap.toMatrixAlgEquiv`/`Matrix.toLinAlgEquiv`), `(E ∘ Z ∘ E⁻¹)^N = E ∘ Z^N ∘ E⁻¹` (induction, `E.symm_comp_self`), `centralOpCl_pow_eq_one`, `LinearMap.toMatrix_id`.

- **Mathlib/project lemmas needed**: C7, C8, C15, `LinearMap.toMatrix_comp`, `LinearMap.toMatrix_id`, `LinearMap.toMatrixAlgEquiv` (`map_pow`), `LinearEquiv.symm_comp_self`, the original's lemma list
- **Sources**: decomposition C16 (the original assembly's docstring quoted there).
- **Generality decision**: as the statement (`[Nonempty ι]`, `hstab`, `hc` as before).
- **Size**: ~110 lines; source: 95 lines (the original)
- **Progress**: done 2026-09-14 — original assembly; Zmat = toMatrix (E ∘ Z ∘ E⁻¹), commutation from discHeckeOperatorCl_comp_centralOpCl, Zmat^N = 1 via hpowM (← toMatrix_comp) and hconjpow; lake build of 19/21/22 green.

### [CLEANUP-C6] Cleanup `PhD/Main/LWX/19_AtkinLehnerIdentity.lean`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/19_AtkinLehnerIdentity.lean
- **Depends on**: C15, C16
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused `simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings; `lake build PhD` and `lake exe runLinter` on the module must be clean (grep the linter's output for the file).  Done inline by the main agent.  Final per-file cleanup of the `…Z` lemmas (the originals are deleted at S0).

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): as CLEANUP-C5 (same file, one pass); `lake build PhD` green (3929 jobs).

### [C17] `LWX.blockProj_zero_apply_term_eltHZ`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/21_AtkinLehnerIdentityH.lean
- **Depends on**: C9
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/21_AtkinLehnerIdentityH.lean:515
omit [CharZero K] in
/-- **Disc `0` of `φ(x s_{b p^{h−1}} p⁻¹ ℓ⁻¹)` at a general tame level**: the central `p⁻¹` is the
tame central operator `Z`. -/
theorem blockProj_zero_apply_term_eltHZ (hh : 0 < h)
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
          (cSpace.blockProj ((((b : ℕ) * p ^ (h - 1) : ℕ) : ZMod (p ^ h)))
            (centralOpH θG ψ U h D φ x)) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As C12 from `blockProj_zero_apply_term_eltH` (original, `21:182–255`) with `centralOpH`, `centralOpH_mem_classicalDiscFormsH`, `blockProj_zero_apply_mul_ιpH` (`21:134`), `ℓGLH`, `ℓQHinv_mem_Iw`, and the level-`h` Shapiro lemma.

- **Mathlib/project lemmas needed**: C9 and the original's lemma list
- **Sources**: decomposition C17–C21.
- **Generality decision**: level `h`.
- **Size**: ~50 lines
- **Progress**: done 2026-09-14 — as C12 at level h (centralOpH_apply omit in 20); lake build of 19/21/22 green.

### [C18] `LWX.atkinLehner_term_eqHZ`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/21_AtkinLehnerIdentityH.lean
- **Depends on**: C17
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/21_AtkinLehnerIdentityH.lean:533
omit [CharZero K] in
/-- The `(b, c)`-term at level `h` and a general tame level: as `atkinLehner_term_eqH`, with `Zφ`
in place of `φ`. -/
theorem atkinLehner_term_eqHZ (hh : 0 < h)
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
          (cSpace.blockProj ((((b : ℕ) * p ^ (h - 1) : ℕ) : ZMod (p ^ h)))
            (centralOpH θG ψ U h D φ.1 x))) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As C13 from `atkinLehner_term_eqH` (original, `21:256–369`) with C17 in the `hin` step.

- **Mathlib/project lemmas needed**: C17
- **Sources**: decomposition C17–C21.
- **Generality decision**: level `h`.
- **Size**: ~110 lines
- **Progress**: done 2026-09-14 — as C13; lake build of 19/21/22 green.

### [C19] `LWX.blockProj_zero_discHecke_atkinLehnerHZ`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/21_AtkinLehnerIdentityH.lean
- **Depends on**: C18
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/21_AtkinLehnerIdentityH.lean:564
omit [CharZero K] in
/-- **`U_p ∘ W_h⁻¹ ∘ U_p^{(ψ⁻¹)} ∘ W_h = p^{k+1}·Z` on disc `0`** at a general tame level. -/
theorem blockProj_zero_discHecke_atkinLehnerHZ (hh : 0 < h)
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
      = (ψ p) ^ (k + 1) • cSpace.blockProj 0 (centralOpH θG ψ U h D φ.1 x) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As C14 from `blockProj_zero_discHecke_atkinLehnerH` (original, `21:370–474`).

- **Mathlib/project lemmas needed**: C18
- **Sources**: decomposition C17–C21.
- **Generality decision**: level `h`.
- **Size**: ~105 lines
- **Progress**: done 2026-09-14 — as C14; lake build of 19/21/22 green.

### [CLEANUP-C7] Cleanup `PhD/Main/LWX/21_AtkinLehnerIdentityH.lean`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/21_AtkinLehnerIdentityH.lean
- **Depends on**: C17, C18, C19
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused `simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings; `lake build PhD` and `lake exe runLinter` on the module must be clean (grep the linter's output for the file).  Done inline by the main agent.

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): `21_AtkinLehnerIdentityH`: module doc in the `Z`-form, the orphaned `Transport` header moved back above `discEvalAtRepsClH_discHeckeOperatorClH`, five long lines split, H1 docstring written out; `lake build PhD` green (3929 jobs).

### [C20] `LWX.discHeckeClH_comp_atkinLehnerHZ`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/21_AtkinLehnerIdentityH.lean
- **Depends on**: C19
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/21_AtkinLehnerIdentityH.lean:593
omit [CharZero K] in
/-- **The operator identity at level `h` and a general tame level**:
`U_p ∘ (W_h⁻¹ ∘ U_p^{(ψ⁻¹)} ∘ W_h) = p^{k+1}·Z`. -/
theorem discHeckeClH_comp_atkinLehnerHZ (hh : 0 < h)
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
      = (ψ p) ^ (k + 1) • centralOpClH θG ψ U hU h k D κ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As C15 from `discHeckeClH_comp_atkinLehnerH` (original, `21:475–517`) with `centralOpClH_apply`.

- **Mathlib/project lemmas needed**: C19
- **Sources**: decomposition C17–C21.
- **Generality decision**: level `h`.
- **Size**: ~45 lines
- **Progress**: done 2026-09-14 — as C15; lake build of 19/21/22 green.

### [C21] `LWX.atkinLehnerHypothesisZ_of_atkinLehnerDataH` **[MILESTONE: H1-Z at level h]**
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/21_AtkinLehnerIdentityH.lean
- **Depends on**: C10, C11, C20
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/21_AtkinLehnerIdentityH.lean:788
/-- **Hypothesis H1 at the classical points of conductor `p^{h+1}`, at a general tame level**
(board `lwx-quaternion`). -/
theorem atkinLehnerHypothesisZ_of_atkinLehnerDataH [Nonempty ι]
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
    ∃ B, AtkinLehnerHypothesisZ (p := p) (K := K) (ι := ι) ψ h k
      ((classicalDataH ψ ω θG U hU (vRepDH θG ψ U h D) (vRepDH_mem_levelM1 θG ψ U h D) uu hp2
        hψ hh hζ hpK k).matrix idx) B
      ((classicalDataH ψ (partnerChar p ω k) θG U hU (vRepDH θG ψ U h D)
        (vRepDH_mem_levelM1 θG ψ U h D) uu hp2 hψ hh hζ.inv hpK k).matrix idx) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As C16 from `atkinLehnerHypothesis_of_atkinLehnerDataH` (original, `21:684–789`) with `centralOpClH`, `centralOpClH_pow_eq_one`, `discHeckeOperatorClH_comp_centralOpClH`, `discEvalAtRepsClH`.

- **Mathlib/project lemmas needed**: C10, C11, C20
- **Sources**: decomposition C17–C21.
- **Generality decision**: level `h`.
- **Size**: ~115 lines
- **Progress**: done 2026-09-14 — as C16; lake build of 19/21/22 green.

### [CLEANUP-C8] Cleanup `PhD/Main/LWX/21_AtkinLehnerIdentityH.lean`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/21_AtkinLehnerIdentityH.lean
- **Depends on**: C20, C21
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused `simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings; `lake build PhD` and `lake exe runLinter` on the module must be clean (grep the linter's output for the file).  Done inline by the main agent.  Final per-file cleanup of the `…HZ` lemmas.

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): as CLEANUP-C7 (same file, one pass); `lake build PhD` green (3929 jobs).

### [CLEANUP-ALL-1] `/cleanup-all` before the SWAP
- **Status**: done (2026-09-14 beastmode, checkpoint)
- **File**: all board files
- **Depends on**: Z1–Z15, L1–L3, C1–C21 and every cleanup ticket above
- **Parallel**: no
- **Type**: cleanup

Full `/cleanup-all` while both hypothesis forms still coexist: `lake build PhD` green with no warning in any
board section; `lake exe runLinter` on `02_CharpolyPairingZ`, `10_DiscForms`, `18`, `19`, `20`, `21` shows no
finding in those files; `#print axioms` on C16, C21, Z12 standard.  Record the sorry count (expected: only
`23_QuaternionData` and `25_QuaternionSlopes` and the `central := sorry` of `23:407`).

- **Progress**: done 2026-09-14 — checkpoint before the swap: `lake build PhD.Main.LWX.«25_QuaternionSlopes»` green (3842 jobs); `#print axioms` = [propext, Classical.choice, Quot.sound] for `Matrix.norm_roots_charpoly_of_mul_eq_smul_mul`, `Module.End.norm_roots_charpoly_mul_of_iSup_eigenspace_eq_top`, C16, C21, L1, Q20b, Q23; `degXint_pos` carried `sorryAx` only through `central := sorry`.  Unused-section-variable omits added where the build flagged them; the remaining style warnings (unused simp args, `ring`→`ring_nf` infos, long lines) are handled at the per-file final cleanups after the swap.

### [S0] **SWAP** — delete the scalar H1, the field `central`, and the scalar identity lemmas **[MILESTONE]**
- **Status**: done (2026-09-14 beastmode)
- **File**: 13, 14, 18, 19, 20, 21, 22, 23_QuaternionData
- **Depends on**: CLEANUP-ALL-1
- **Parallel**: no
- **Type**: repair

One coordinated edit (no proof content); afterwards `lake build PhD` fails **exactly** at the R1–R9 sites, which
are then repaired in order.  Every rename keeps the old name so that no downstream *statement* changes.

1. `13_AtkinLehnerInst.lean`: delete `AtkinLehnerHypothesis` (scalar), `roots_charpoly_of_atkinLehnerHypothesis`,
   `AtkinLehnerHypothesis.toZ`; rename `AtkinLehnerHypothesisZ → AtkinLehnerHypothesis` and
   `norm_roots_charpoly_of_atkinLehnerHypothesisZ → norm_roots_charpoly_of_atkinLehnerHypothesis`; update the
   module docstring (`13:30`, `13:51`) and the definition's docstring (drop "`AtkinLehnerHypothesis` is the case `Z = 1`").
2. `18_AtkinLehnerMap.lean`, `20_AtkinLehnerMapH.lean`, `22_AtkinLehnerFamily.lean`: delete the field `central`
   (`18:154–156`, the H twin, `22:59–61`) and the lines `central := F.central` in `toData` (`22:88`) and `toDataH`
   (`22:150`), `central := D₁.central` in `toH` (`20`); fix the structures' docstrings ("the central `p` acting
   trivially" → "the central `p` acting through the tame central operator").
3. `19_AtkinLehnerIdentity.lean`: delete `apply_mul_ιp_pGL`, `apply_mul_ιp_pGL_inv`, `blockProj_zero_apply_term_elt`,
   `atkinLehner_term_eq`, `blockProj_zero_discHecke_atkinLehner`, `discHeckeCl_comp_atkinLehner`,
   `atkinLehnerHypothesis_of_atkinLehnerData`; rename the `…Z` versions to those names (C12–C16); update the module
   docstring (`19:8–30`, the sentence "the central `p` acts trivially (`AtkinLehnerData.central`)").
   `21_AtkinLehnerIdentityH.lean`: the same for `apply_mul_ιp_pGLH`, `apply_mul_ιp_pGL_invH`,
   `blockProj_zero_apply_term_eltH`, `atkinLehner_term_eqH`, `blockProj_zero_discHecke_atkinLehnerH`,
   `discHeckeClH_comp_atkinLehnerH`, `atkinLehnerHypothesis_of_atkinLehnerDataH` and the `…HZ` names.
4. `14_Touching.lean`: delete `neg_log_norm_det_add_of_mul_eq_smul`, `det_ne_zero_of_mul_eq_smul'`,
   `det_ne_zero_of_mul_eq_smul_conj` (`14:103–147`); Z15's lemmas replace them.
5. `23_QuaternionData.lean`: delete the line `central := sorry` of `atkinLehnerFamily`.
6. Keep `05_AtkinLehner.lean`'s scalar `roots_charpoly_atkinLehner`/`norm_roots_charpoly_atkinLehner` (still true, still
   used by the reduction section of `05`); keep `01_CharpolyPairing.lean` untouched.
7. `grep -rn "central\b\|AtkinLehnerHypothesisZ\|_eltZ\|_eqZ\|atkinLehnerZ\b" PhD/Main/LWX` must show only the intended survivors.
Then run `lake build PhD 2>&1 | grep error` and hand the site list to R1–R9 (expected sites: `14:702–754`,
`15_TouchingH:200–251`, `15_StepThree:415–547, 746`, `17` (pass-through), `19`/`21` `_of_conj`,
`23_ConductorSlopes:113–187, 325–481`).

- **Mathlib/project lemmas needed**: —
- **Sources**: decomposition §2, "The SWAP and the repairs"
- **Size**: ~40 deletions/renames
- **Progress**: done 2026-09-14 — `swap_s0.py`: scalar `AtkinLehnerHypothesis` + `toZ` + `roots_charpoly_of_atkinLehnerHypothesis` deleted (13), the Z definition renamed and given `variable (p K ι) in`; three scalar determinant lemmas deleted (14); field `central` deleted from `AtkinLehnerData`, `AtkinLehnerDataH`, `AtkinLehnerFamily` and every transport (18/20/22) and `central := sorry` (23); seven scalar identity lemmas deleted in 19 and seven in 21; every `…Z`/`…HZ` name renamed to the old name.  Applied together with R1–R8; full `lake build PhD` green (3929 jobs), zero sorries in all touched files, `#print axioms` standard for every milestone.

### [R1] Repair `14_Touching.lean` (`isStepOneTouching_of_atkinLehnerHypothesis`, `hasUnitBand_of_atkinLehnerHypothesis`)
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/14_Touching.lean
- **Depends on**: S0
- **Parallel**: no
- **Type**: repair

Destructure `obtain ⟨B, ⟨Z, N, hN, hAB, hZA, hZN⟩, P, Q, hQP, hA'⟩ := hAL` (was `⟨B, hAB, P, Q, hQP, hA'⟩`); then
`det_ne_zero_of_mul_eq_smul' hcne hAB ↦ Matrix.det_ne_zero_of_mul_eq_smul_mul hcne hAB hN hZN`;
`det_ne_zero_of_mul_eq_smul_conj hcne hAB hQP hA' ↦ det_ne_zero_of_mul_eq_smul_mul_conj hcne hAB hN hZN hQP hA'`;
`neg_log_norm_det_add_of_mul_eq_smul hcne hAB hQP hA' ↦ neg_log_norm_det_add_of_mul_eq_smul_mul hcne hAB hN hZN hQP hA'`
(sites `14:702, 709, 710, 754` and the `hasUnitBand` twin at `14:795`).  Nothing else in the proofs mentions `B`.

- **Mathlib/project lemmas needed**: Z3, Z15
- **Sources**: decomposition §2, "The SWAP and the repairs"
- **Size**: ~8 edits
- **Progress**: done 2026-09-14 — `obtain ⟨B, ⟨Zm, Nm, hNm, hAB, -, hZmN⟩, …⟩`; Z-form determinant lemmas; full `lake build PhD` green.

### [R2] Repair `15_TouchingH.lean` (`isStepOneTouching_of_atkinLehnerHypothesisH`, `hasUnitBand…H`)
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/15_TouchingH.lean
- **Depends on**: S0
- **Parallel**: no
- **Type**: repair

The same three substitutions as R1 at `15_TouchingH.lean:200–251` and the `hasUnitBand` twin at `:276`.

- **Mathlib/project lemmas needed**: Z3, Z15
- **Sources**: decomposition §2, "The SWAP and the repairs"
- **Size**: ~8 edits
- **Progress**: done 2026-09-14 — as R1; full `lake build PhD` green.

### [R3] Repair `15_StepThree.lean` (the four H1 consumers)
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/15_StepThree.lean
- **Depends on**: S0
- **Parallel**: no
- **Type**: repair

1. `norm_pow_le_of_mem_roots_charpoly_matrix` (`:406–430`): destructure as R1; `hA0` via `Matrix.det_ne_zero_of_mul_eq_smul_mul hcne hAB hN hZN`;
   `rw [norm_roots_charpoly_atkinLehner hcne hAB hQP hA'] ↦ rw [norm_roots_charpoly_atkinLehnerZ hcne hAB hZA hN hZN hQP hA']`.
2. `unitSlope_charpolyRev_matrix_le` (`:440–455`): destructure; `hA0` as above; the recursive call passes the re-bundled hypothesis
   `⟨B, ⟨Z, N, hN, hAB, hZA, hZN⟩, P, Q, hQP, hA'⟩`.
3. `faceLeft_charpolyRev_matrix_eq` (`:509–560`): destructure; `hA0`, `hA'0` (`det_ne_zero_of_mul_eq_smul_mul_conj`); the
   `rw [hnormOnly, norm_roots_charpoly_atkinLehner …]` line becomes `norm_roots_charpoly_atkinLehnerZ hcne hAB hZA hN hZN hQP hA'`.
4. `rightIndex_sub_touchX_eq_ordDim` (`:733–750`): the `hA0` block: `obtain ⟨B, ⟨Z, N, hN, hAB, -, hZN⟩, -⟩ := hAL; exact Matrix.det_ne_zero_of_mul_eq_smul_mul hcne hAB hN hZN`.
5. `degX_succ`, `degXint_zero`, `touchX_sub_leftIndex_eq_ordDim` (`:616, 931, 961`): pass-through (`hAL` forwarded) — recompile only.

- **Mathlib/project lemmas needed**: Z3, Z13, Z15
- **Sources**: decomposition §2, "The SWAP and the repairs"
- **Size**: ~15 edits
- **Progress**: done 2026-09-14 — four consumers destructured; `norm_roots_charpoly_atkinLehnerZ`; re-bundled call; full `lake build PhD` green.

### [R4] Repair `17_DegreeFormula.lean` (pass-through) and recompile the `15`/`16`/`17` closure
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/17_DegreeFormula.lean
- **Depends on**: R3
- **Parallel**: no
- **Type**: repair

`17:46, 62` forward `hAL` unchanged; `lake build PhD.Main.LWX.«17_DegreeFormula»` must be green after R3 with no edit (if an edit is needed, it is a destructuring of the same shape as R1).

- **Mathlib/project lemmas needed**: —
- **Sources**: decomposition §2, "The SWAP and the repairs"
- **Size**: 0–2 edits
- **Progress**: done 2026-09-14 — pass-through; no edit needed; full `lake build PhD` green.

### [R5] Repair `atkinLehnerHypothesis_of_conj` (`19`) and `atkinLehnerHypothesis_of_conjH` (`21`)
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/19_AtkinLehnerIdentity.lean, 21_AtkinLehnerIdentityH.lean
- **Depends on**: S0
- **Parallel**: no
- **Type**: repair

`obtain ⟨⟨Z, N, hN, hAB, hZA, hZN⟩, P, Q, hQP, hA'⟩ := h`; `refine ⟨⟨S * Z * S₁, N, hN, ?_, ?_, ?_⟩, S' * P * S₁, S * Q * S₁', ?_, ?_⟩`:
* `(S A S₁)(S B S₁) = S (A B) S₁ = c • (S Z S₁)`: the original `calc` with `hSS₁` replaced by `Matrix.mul_smul`/`Matrix.smul_mul` and no `mul_one`;
* `(S Z S₁)(S A S₁) = S (Z A) S₁ = S (A Z) S₁ = (S A S₁)(S Z S₁)` (`hS`, `hZA`, `Matrix.mul_assoc`);
* `(S Z S₁)^N = S Z^N S₁ = 1`: `have : ∀ m, (S * Z * S₁) ^ m = S * Z ^ m * S₁` by induction (`pow_succ`, `hS`), then `hZN`, `hSS₁` (needs `S * S₁ = 1`, i.e. `mul_eq_one_comm.mp hS` as in the original);
* the two `P, Q` goals unchanged.  The unused `_hS''` stays (protected statement).

- **Mathlib/project lemmas needed**: `mul_eq_one_comm`, `Matrix.mul_assoc`, `Matrix.mul_smul`, `Matrix.smul_mul`
- **Sources**: decomposition §2, "The SWAP and the repairs"
- **Size**: ~30 lines each
- **Progress**: done 2026-09-14 — new proofs with `S Z S₁` as the tame operator, `(S Z S₁)^N = S Z^N S₁` by induction; full `lake build PhD` green.

### [R6] Repair `atkinLehnerHypothesis_symm` (`23_ConductorSlopes.lean:113`)
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_ConductorSlopes.lean
- **Depends on**: S0, Z4
- **Parallel**: no
- **Type**: repair

`obtain ⟨⟨Z, N, hN, hAB, hZA, hZN⟩, P, Q, hQP, hA'⟩ := hAL`; `hc0` as before; `hPQ := mul_eq_one_comm.mp hQP`;
`refine ⟨P * A * Q, ⟨P * Z * Q, N, hN, ?_, ?_, ?_⟩, Q, P, hPQ, ?_⟩`:
* `A' (P A Q) = P (B A) Q = c • (P Z Q)`: `hA'`, `Matrix.mul_assoc`, `hQP`, `Matrix.mul_eq_smul_mul_symm hc0 hAB hZA hN hZN` (Z4), `Matrix.mul_smul`, `Matrix.smul_mul`;
* `(P Z Q)(A') = P Z (Q P) B Q = P (Z B) Q = P (B Z) Q = A' (P Z Q)`: `Matrix.mul_comm_of_mul_eq_smul_mul hc0 hAB hZA hN hZN` (Z4), `hQP`;
* `(P Z Q)^N = P Z^N Q = P Q = 1`: induction with `hQP`, then `hZN`, `hPQ`;
* `A = Q (P A Q) P`: the original's last `calc` (`23:139–144`).

- **Mathlib/project lemmas needed**: Z4, `mul_eq_one_comm`
- **Sources**: decomposition §2, "The SWAP and the repairs"
- **Size**: ~35 lines
- **Progress**: done 2026-09-14 — `B' := P A Q`, `Z' := P Z Q` (Matrix.mul_eq_smul_mul_symm, Matrix.mul_comm_of_mul_eq_smul_mul); full `lake build PhD` green.

### [R7] Repair `norm_pow_le_of_mem_roots_charpoly_matrixH`, `unitSlope_charpolyRev_matrix_leH` (`23_ConductorSlopes.lean:143–187`)
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_ConductorSlopes.lean
- **Depends on**: S0
- **Parallel**: no
- **Type**: repair

As R3 items 1–2 (destructure; `Matrix.det_ne_zero_of_mul_eq_smul_mul`; `norm_roots_charpoly_atkinLehnerZ`; re-bundle for the recursive call).

- **Mathlib/project lemmas needed**: Z3, Z13
- **Sources**: decomposition §2, "The SWAP and the repairs"
- **Size**: ~8 edits
- **Progress**: done 2026-09-14 — as R3 at level h; full `lake build PhD` green.

### [R8] **Restate** `toReal_unitSlope_charpolyRev_reflect` in norm form, and repair `slopeRatio_add_slopeRatio_eq_of_atkinLehnerHypothesisH` (`23_ConductorSlopes.lean:325, 441`)
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_ConductorSlopes.lean
- **Depends on**: S0, Z12
- **Parallel**: no
- **Type**: repair

The one deliberate statement change of the board (recorded in `decomposition.md` R8; not a B2 — it is the
planned weakening of a hypothesis): replace
`(hroots : A'.charpoly.roots = A.charpoly.roots.map (fun x => c / x))` by
`(hroots : A'.charpoly.roots.map (fun x => ‖x‖) = A.charpoly.roots.map (fun x => ‖c‖ / ‖x‖))`; conclusion unchanged.
Repair of its proof:
1. `hA' : A'.det ≠ 0`: no root of `A'` has norm `0`: `Matrix.det_eq_prod_roots_charpoly`, `Multiset.prod_ne_zero`, and for `x ∈ A'.charpoly.roots`,
   `‖x‖ ∈ (A'.charpoly.roots.map ‖·‖) = …` (`Multiset.mem_map_of_mem`, `hroots`), so `‖x‖ = ‖c‖ / ‖y‖ ≠ 0` (`div_ne_zero`, `hroot0`), hence `x ≠ 0` (`norm_ne_zero_iff`).
2. `hcount` (`:355–366`): before rewriting with `hroots`, convert the root count of `A'` to a count over the norm multiset with the `hnormOnly`
   trick of `15_StepThree.lean:540–548` (`Multiset.countP_map`, `Multiset.countP_congr`, `norm_inv`), then `rw [hroots, Multiset.countP_map]`
   and continue as before on the `ψ`-roots (`norm_div`, `Real.exp`).
3. `slopeRatio_add_slopeRatio_eq_of_atkinLehnerHypothesisH` (`:459–481`): destructure `hB` as R1 for `hA0`; the reflection call becomes
   `toReal_unitSlope_charpolyRev_reflect hcne hA0 (norm_roots_charpoly_of_atkinLehnerHypothesis (hAL := hB)) (i := i) …`
   (the renamed Z14 lemma); everything else unchanged.

- **Mathlib/project lemmas needed**: Z12/Z14, `Matrix.det_eq_prod_roots_charpoly`, `Multiset.countP_map`, `Multiset.countP_congr`, `norm_inv`, `norm_div`
- **Sources**: decomposition §2, "The SWAP and the repairs"
- **Size**: ~25 lines
- **Progress**: done 2026-09-14 — hypothesis restated in norm form (planned statement change); `hA'` from nonzero root norms, `hnormOnly` count transfer, `hcompl` drops `norm_div`; call site uses `norm_roots_charpoly_of_atkinLehnerHypothesis`; full `lake build PhD` green.

### [R9] Recompile the family theorems (`23_ConductorSlopes.lean:508–740`, `24_DegreePeriodicity.lean`)
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_ConductorSlopes.lean, 24_DegreePeriodicity.lean
- **Depends on**: R1–R8
- **Parallel**: no
- **Type**: repair

`hasUnitBand_of_atkinLehnerData` (`23:508`) and the family theorems of `23`/`24` forward the (renamed) `atkinLehnerHypothesis_of_atkinLehnerData(H)`
and the `∃ B, AtkinLehnerHypothesis …` hypotheses unchanged: `lake build PhD.Main.LWX.«24_DegreePeriodicity»` must be green with no edit.
If a site needs the `∃ B, …` re-bundled, do it inline (same shape as R1).

- **Mathlib/project lemmas needed**: —
- **Sources**: decomposition §2, "The SWAP and the repairs"
- **Size**: 0–4 edits
- **Progress**: done 2026-09-14 — pass-through; no edit needed; full `lake build PhD` green.

### [R10] Post-swap full build, `22_AtkinLehnerFamily.lean` docstrings, and the imports
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/22_AtkinLehnerFamily.lean, PhD.lean
- **Depends on**: R9
- **Parallel**: no
- **Type**: repair

`lake build PhD` green; `22`'s module docstring (`22:19`, "one section `ιp` (with the level, central and …)") and the structure docstrings mention
`ιp_pGL_comm`/`central_pow` instead of `central`; `grep -rn "central\b" PhD/Main/LWX` shows no reference to the deleted field;
`#print axioms` of `atkinLehnerHypothesis_of_atkinLehnerData`, `…H`, `degXint_pos_of_atkinLehnerFamily`, `slopeRatio_add_period` standard;
sorry count = `23_QuaternionData` + `25_QuaternionSlopes` only.

- **Mathlib/project lemmas needed**: —
- **Sources**: decomposition §2, "The SWAP and the repairs"
- **Size**: docstrings
- **Progress**: done 2026-09-14 — full build green; docstring updates folded into CLEANUP-R; full `lake build PhD` green.

### [CLEANUP-R] Cleanup `13, 14, 15_StepThree, 15_TouchingH, 17, 19, 21, 22, 23_ConductorSlopes (repair sites)`
- **Status**: done (2026-09-14 beastmode)
- **File**: 13, 14, 15_StepThree, 15_TouchingH, 17, 19, 21, 22, 23_ConductorSlopes (repair sites)
- **Depends on**: R1–R10
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused `simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings; `lake build PhD` and `lake exe runLinter` on the module must be clean (grep the linter's output for the file).  Done inline by the main agent.  Golf the repaired proofs (the destructurings often let `obtain` patterns shrink); `runLinter` on `24_DegreePeriodicity` (whole closure) must show no finding in the repaired files.

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): repair sites: long lines split in 14, 15_StepThree, 15_TouchingH, 23_ConductorSlopes; 22's module doc (fields, the `D/ℚ` construction) and 23_ConductorSlopes' reflection bullet (norm form); `lake build PhD` green (3929 jobs).

### [Q1] `det_thetaInt_ne_zero`, `thetaIntGL` (`map_one'`, `map_mul'`)
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: none
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:53
/-- The determinant of a `p`-component is nonzero (it is the coercion of a unit). -/
theorem det_thetaInt_ne_zero (g : Dfx ℚ D) : (thetaInt p D g).det ≠ 0 := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:57
/-- The `p`-component map into `GL₂(ℚ_p)`. -/
def thetaIntGL : Dfx ℚ D →* GL (Fin 2) ℚ_[p] where
  toFun g := Matrix.GeneralLinearGroup.mkOfDetNeZero (thetaInt p D g) (det_thetaInt_ne_zero p D g)
  map_one' := by sorry
  map_mul' := by sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `det_thetaInt_ne_zero`: `have h := congrArg Matrix.det (map_mul (thetaInt p D) g g⁻¹)`; `rw [mul_inv_cancel, map_one, Matrix.det_one, Matrix.det_mul] at h`; `exact left_ne_zero_of_mul_eq_one h.symm`.
2. `thetaIntGL`: `map_one' := Units.ext (by simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, map_one])` — the coercion of `mkOfDetNeZero A h` is `A` (`rfl`), so `Units.ext` reduces both to `thetaInt p D 1 = 1`; `map_mul' g g' := Units.ext (map_mul (thetaInt p D) g g')`.

- **Mathlib/project lemmas needed**: `map_mul`, `map_one`, `Matrix.det_mul`, `Matrix.det_one`, `left_ne_zero_of_mul_eq_one`, `Matrix.GeneralLinearGroup.mkOfDetNeZero` (`GeneralLinearGroup/Defs.lean:130`), `Units.ext`
- **Sources**: decomposition Q1 (the instance trap: never re-compose the algebra homs at `F = ℚ`).
- **Generality decision**: as the statements.
- **Size**: ~6 lines
- **Progress**: done 2026-09-14 — det via θ g θ g⁻¹ = 1; thetaIntGL fields by Units.ext; lake build of 23_QuaternionData green (only `central := sorry` left, removed at S0).

### [Q2] `ιpD` (`map_one'`, `map_mul'`) + `unitAt_mul` [NEW DECL]
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: none
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:67
/-- **The section** `ιp : GL₂(ℚ_p) →* (D ⊗ 𝔸_f)ˣ`: the single-place unit `unitAt` at `p`, read
through the comparison `ℚ_p ≃ K_p`. -/
def ιpD : GL (Fin 2) ℚ_[p] →* Dfx ℚ D where
  toFun g := unitAt ℚ D (padicPlace p) (Matrix.GeneralLinearGroup.map (padicComparison p) g)
  map_one' := by sorry
  map_mul' := by sorry
```

**New declaration(s) to add** (`[NEW DECL]`; state exactly as below, then prove):
```lean
/-- `unitAt` is multiplicative (board `lwx-quaternion`; `section Generic`, with `[RigidificationAt F A v]`). -/
theorem QMF.unitAt_mul [RigidificationAt F A v] (m m' : (Matrix (Fin 2) (Fin 2) (v.adicCompletion F))ˣ) :
    unitAt F A v (m * m') = unitAt F A v m * unitAt F A v m' := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. First the generic sub-lemma (in `section Generic`; needs `[RigidificationAt F A v]` — add it to that section's variables or a sub-section):
   `unitAt_mul`: `Units.ext`; both sides are `1 + iotaV (E⁻¹(m m') - 1)` and `(1 + iotaV (E⁻¹ m - 1)) (1 + iotaV (E⁻¹ m' - 1))`; expand as in `one_add_iotaV_mul` (`QMF/04_UpiElement.lean:144–160`: `expand` by `noncomm_ring`, then `iotaV_mul`, `map_add`, and the identity `a - 1 + (b - 1) + (a - 1) * (b - 1) = a * b - 1` by `noncomm_ring`), with `a := E⁻¹ m`, `b := E⁻¹ m'`, `map_mul` of `E⁻¹` (`AlgEquiv.symm`), `Units.val_mul`.
2. `ιpD.map_one'`: `Matrix.GeneralLinearGroup.map` is a `MonoidHom` (`map_one`); `unitAt 1 = 1`: `Units.ext`, `E⁻¹ 1 = 1` (`map_one`), `sub_self`, `map_zero`, `add_zero`.
3. `ιpD.map_mul'`: `rw [map_mul, unitAt_mul]`.

- **Mathlib/project lemmas needed**: `unitAt` (`04:255`), `one_add_iotaV_mul` (`04:144`), `iotaV_mul` (`04:107`), `Matrix.GeneralLinearGroup.map` (a `MonoidHom`), `Units.ext`, `noncomm_ring`
- **Sources**: decomposition Q2 (docstrings of `unitAt` quoted there).
- **Generality decision**: `unitAt_mul` generic in `F` (the fork's API); `ιpD` at `F = ℚ`.
- **Size**: ~25 lines
- **Progress**: done 2026-09-14 — generic QMF.unitAt_one / QMF.unitAt_mul (GenericTop section, expand/collapse by noncomm_ring); lake build of 23_QuaternionData green (only `central := sorry` left, removed at S0).

### [Q3] `thetaInt_ιpD`, `thetaIntGL_ιpD`, `ιpD_injective`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q1, Q2
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:78
/-- `θ ∘ ιp = id` (`toMatrix_unitAt`). -/
theorem thetaInt_ιpD (g : GL (Fin 2) ℚ_[p]) :
    thetaInt p D (ιpD p D g) = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:83
theorem thetaIntGL_ιpD (g : GL (Fin 2) ℚ_[p]) : thetaIntGL p D (ιpD p D g) = g := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:86
theorem ιpD_injective : Function.Injective (ιpD p D) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `thetaInt_ιpD`: `thetaInt = (mapMatrix padicComparisonSymm).comp toMatrix` (`08:100`); `simp only [thetaInt, MonoidHom.comp_apply, ιpD_apply, toMatrix_unitAt]` (`04:294`), then `Matrix.GeneralLinearGroup.map` coerces to `(padicComparison p).mapMatrix g` (`Matrix.GeneralLinearGroup.coe_map`/`map_apply`), and `RingHom.mapMatrix_apply`, `Matrix.map_map`, `padicComparisonSymm_comp` (`08:67`), `Matrix.map_id`.
2. `thetaIntGL_ιpD`: `Units.ext (thetaInt_ιpD p D g)` (`coe_thetaIntGL`).
3. `ιpD_injective`: `Function.LeftInverse.injective (thetaIntGL_ιpD p D)`.

- **Mathlib/project lemmas needed**: `toMatrix_unitAt`, `padicComparisonSymm_comp`, `RingHom.mapMatrix_apply`, `Matrix.map_map`, `Matrix.map_id`, `Function.LeftInverse.injective`
- **Sources**: decomposition Q3.
- **Generality decision**: as the statements.
- **Size**: ~10 lines
- **Progress**: done 2026-09-14 — show through mapMatrix σ ∘ toMatrix, toMatrix_unitAt, Matrix-entry congr_fun; lake build of 23_QuaternionData green (only `central := sorry` left, removed at S0).

### [CLEANUP-Q1] Cleanup `PhD/Main/LWX/23_QuaternionData.lean`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q1, Q2, Q3
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused `simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings; `lake build PhD` and `lake exe runLinter` on the module must be clean (grep the linter's output for the file).  Done inline by the main agent.  `omit … in` the five `unusedSectionVars` `rfl` lemmas flagged by the skeleton build.

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): `23_QuaternionData`: header marker and six board annotations stripped, three long lines split, `omit [DecidableEq ι] in` on every lemma the unused-section-variable linter and runLinter's `unusedArguments` flagged, iterated to a fixpoint (e.g. `level_subset_levelM1`, `normClass_ιpD_*`, `heckeChar(H)_apply`, `heckeChar(H)_global`, `det_certM1_eq`, `vRepF_atkinLehnerFamily`), `omit [RigidificationAt ℚ D (padicPlace p)] in` on `unitsIncl_pUnit_comm`, and the `tameScalar` docstring corrected (`p_global⁻¹·p_p = (p^{(p)})⁻¹` is `p⁻¹` away from `p`, matching the `p^{(p)}` convention of `central_pow`); `lake build PhD` green (3929 jobs).

### [Q4] `QMF.iotaV_mul_eq_zero_of_toLocal_eq_zero` + `singleₗ_mul`, `iotaV_mul_eq_iotaV_mul_toLocal` [NEW DECL]
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: none
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:101
/-- Elements supported away from `v` annihilate the single-place inclusion at `v`
(`singleₗ_mul_singleₗ`, `toLocal_tmul`; a lemma about the fork's API, to move to
`PhD/Main/QMF/04_UpiElement.lean` at cleanup). -/
theorem QMF.iotaV_mul_eq_zero_of_toLocal_eq_zero (x : A ⊗[F] v.adicCompletion F)
    {y : A ⊗[F] FiniteAdeleRing (RingOfIntegers F) F} (hy : toLocal F A v y = 0) :
    iotaV F A v x * y = 0 ∧ y * iotaV F A v x = 0 := by
  sorry
```

**New declaration(s) to add** (`[NEW DECL]`; state exactly as below, then prove):
```lean
theorem QMF.singleₗ_mul (a : v.adicCompletion F) (b : FiniteAdeleRing (RingOfIntegers F) F) :
    singleₗ F v a * b = singleₗ F v (a * b v) := by
  sorry

theorem QMF.mul_singleₗ (a : v.adicCompletion F) (b : FiniteAdeleRing (RingOfIntegers F) F) :
    b * singleₗ F v a = singleₗ F v (b v * a) := by
  sorry

theorem QMF.iotaV_mul_eq_iotaV_mul_toLocal (x : A ⊗[F] v.adicCompletion F)
    (y : A ⊗[F] FiniteAdeleRing (RingOfIntegers F) F) :
    iotaV F A v x * y = iotaV F A v x * iotaV F A v (toLocal F A v y) := by
  sorry

theorem QMF.mul_iotaV_eq_iotaV_toLocal_mul (x : A ⊗[F] v.adicCompletion F)
    (y : A ⊗[F] FiniteAdeleRing (RingOfIntegers F) F) :
    y * iotaV F A v x = iotaV F A v (toLocal F A v y) * iotaV F A v x := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `singleₗ_mul` (generic, `section Generic`): `FiniteAdeleRing.ext F fun w => ?_`; `rcases eq_or_ne w v with rfl | hw`; at `v`: `adele_mul_apply` is `private` in `04` — use `rfl`-level `show (a * b) w = a w * b w` (multiplication in the restricted product is componentwise, `RestrictedProduct.mul_apply`), `singleₗ_apply_same`; at `w ≠ v`: `singleₗ_apply_ne`, `zero_mul`.  Mirror of `singleₗ_mul_singleₗ` (`04:74–83`).  State also the right-handed `b * singleₗ F v a = singleₗ F v (b v * a)`.
2. `iotaV_mul_eq_iotaV_mul_toLocal x y : iotaV F A v x * y = iotaV F A v x * iotaV F A v (toLocal F A v y)` (and the symmetric one): `TensorProduct.induction_on` on `x` then `y`; pure tensors: `iotaV_tmul`, `toLocal_tmul`, `evalAlgHom_apply`, `Algebra.TensorProduct.tmul_mul_tmul`, `singleₗ_mul`, `singleₗ_mul_singleₗ`; `add` cases by `map_add`, `mul_add`/`add_mul`.
3. The ticketed lemma: `rw [iotaV_mul_eq_iotaV_mul_toLocal, hy, map_zero, mul_zero]` and symmetrically.

- **Mathlib/project lemmas needed**: `singleₗ_mul_singleₗ` (`04:74`), `singleₗ_apply_same/_ne` (`04:66,70`), `iotaV_tmul` (`04:102`), `toLocal_tmul` (`04:120`), `evalAlgHom_apply` (`04:90`), `TensorProduct.induction_on`, `Algebra.TensorProduct.tmul_mul_tmul`, `FiniteAdeleRing.ext`
- **Sources**: decomposition Q4.
- **Generality decision**: generic `F`, `A` (avoids the `F = ℚ` instance trap).
- **Size**: ~40 lines
- **Progress**: done 2026-09-14 — generic QMF.singleₗ_mul, mul_singleₗ, iotaV_mul_eq_iotaV_mul_toLocal, mul_iotaV_eq_iotaV_toLocal_mul (TensorProduct.induction_on); lake build of 23_QuaternionData green (only `central := sorry` left, removed at S0).

### [Q5] `ιpD_comm_of_thetaInt_eq_one`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q4
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:116
/-- **`p`-local elements commute with elements of trivial `p`-component.** -/
theorem ιpD_comm_of_thetaInt_eq_one (g : GL (Fin 2) ℚ_[p]) {y : Dfx ℚ D}
    (hy : thetaInt p D y = 1) : ιpD p D g * y = y * ιpD p D g := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `hy1 : toLocal ℚ D (padicPlace p) (y : D ⊗ 𝔸) = 1`: from `hy`, `thetaInt = mapMatrix padicComparisonSymm ∘ toMatrix` with both `mapMatrix padicComparisonSymm` (a ring equivalence's map) and `RigidificationAt.equiv` injective: `toMatrix_apply` (`04:228`), `(RigidificationAt.equiv).injective`, `map_one`; work with `thetaInt_ιpD`-style rewriting, never naming the `Algebra ℚ` instance.
2. `Units.ext`; write `ιpD g = 1 + iotaV x₀` (`ιpD_apply`, `unitAt`, `x₀ := E⁻¹ g - 1`) and `y = 1 + (y - 1)` with `toLocal (y - 1) = 0` (`map_sub`, `hy1`, `sub_self`).
3. `(1 + ι x₀)(1 + y') = 1 + ι x₀ + y' + ι x₀ * y'` and `ι x₀ * y' = 0` (Q4); symmetrically `y' * ι x₀ = 0`; `add_mul`, `mul_add`, `mul_one`, `one_mul`, `add_zero`, `add_comm`.

- **Mathlib/project lemmas needed**: Q4, `toMatrix_apply` (`04:228`), `unitAt`, `ιpD_apply`, `AlgEquiv.injective`, `RingEquiv.injective`, `mul_add`/`add_mul`
- **Sources**: decomposition Q5 ([LWX, Prop 3.1]'s "both `γ_i` and `γ_λ` have trivial `p`-component", `lwx.txt:1083–1084`, is usable because of this fact).
- **Generality decision**: as the statement.
- **Size**: ~25 lines
- **Progress**: done 2026-09-14 — generic toLocal_eq_one_of_toMatrix_eq_one + unitAt_comm_of_toLocal_eq_one; Matrix.ext (bare ext entered the completion); lake build of 23_QuaternionData green (only `central := sorry` left, removed at S0).

### [Q6] `ιpD_pGL_comm`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q2
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:121
/-- The local central element `p·1` is central in `(D ⊗ 𝔸_f)ˣ`. -/
theorem ιpD_pGL_comm (x : Dfx ℚ D) : ιpD p D (pGL p) * x = x * ιpD p D (pGL p) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `Units.ext`; `ιpD (pGL p) = 1 + iotaV (E⁻¹ ((p : K_p) • 1) - 1)` (`ιpD_apply`, `unitAt`, `Matrix.GeneralLinearGroup.map` of `(p : ℚ_p) • 1` is `(p : K_p) • 1`: `map_natCast`/`Matrix.map_smul`, `RingHom.map_natCast`).
2. `E⁻¹ ((p : K_p) • 1) = (p : ℕ) • 1` in `D ⊗ K_p`: write the matrix as `((p : ℕ) : Matrix …)` (`Nat.smul_one_eq_cast`, `Matrix/NatInt.lean:157`) and use `map_natCast` of the `AlgEquiv`; then `iotaV ((p : ℕ) • 1 - 1) = ((p : ℕ) - 1 : ℕ)`… cleaner: `iotaV (n • 1 - 1)` is `(n - 1) • iotaV 1`? `iotaV` is `F`-linear, not `ℕ`-semilinear in an obvious way — use `map_nsmul`/`map_sub`, `map_one`? `iotaV 1 = 1 ⊗ₜ singleₗ 1` (`iotaV_tmul` with `1 = 1 ⊗ₜ 1`, `Algebra.TensorProduct.one_def`).
3. Centrality: `1 ⊗ₜ e` commutes with every `d ⊗ₜ b` (`Algebra.TensorProduct.tmul_mul_tmul`, `one_mul`, `mul_one`, `mul_comm` in the commutative `𝔸_f`), hence with every element (`TensorProduct.induction_on`, `mul_add`/`add_mul`); so `1 + iotaV(…)` is central; `Units.val_mul`.
   Alternative: prove the general `Commute (iotaV F A v (algebraMap _ _ c)) y`… keep the concrete route.

- **Mathlib/project lemmas needed**: `Units.ext`, `ιpD_apply`, `unitAt`, `map_natCast`, `Nat.smul_one_eq_cast`, `iotaV_tmul`, `Algebra.TensorProduct.one_def`, `Algebra.TensorProduct.tmul_mul_tmul`, `TensorProduct.induction_on`, `mul_comm`
- **Sources**: decomposition Q6 (keep the scalar as `((p : ℕ) : _)`, never through `Algebra ℚ`).
- **Generality decision**: as the statement.
- **Size**: ~30 lines
- **Progress**: done 2026-09-14 — generic unitAt_comm_of_forall_comm at the scalar matrix; lake build of 23_QuaternionData green (only `central := sorry` left, removed at S0).

### [CLEANUP-Q2] Cleanup `PhD/Main/LWX/23_QuaternionData.lean`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q4, Q5, Q6
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused `simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings; `lake build PhD` and `lake exe runLinter` on the module must be clean (grep the linter's output for the file).  Done inline by the main agent.

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): as CLEANUP-Q1 (same file, one pass); `lake build PhD` green (3929 jobs).

### [Q7] `tameSubgroup` (closure), `tamePart_mem_tameSubgroup`, `eq_ιpD_mul_tamePart`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q3, Q5
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:125
/-- **The prime-to-`p` subgroup**: adelic units with trivial `p`-component. -/
def tameSubgroup : Subgroup (Dfx ℚ D) where
  carrier := {g | thetaInt p D g = 1}
  mul_mem' := by sorry
  one_mem' := by sorry
  inv_mem' := by sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:138
theorem tamePart_mem_tameSubgroup (g : Dfx ℚ D) : tamePart p D g ∈ tameSubgroup p D := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:144
/-- `g = ιp(θ g) · tamePart g`. -/
theorem eq_ιpD_mul_tamePart (g : Dfx ℚ D) :
    g = ιpD p D (thetaIntGL p D g) * tamePart p D g := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `tameSubgroup`: `mul_mem'`: `map_mul`, both `= 1`, `one_mul`; `one_mem'`: `map_one`; `inv_mem'`: `map_inv` (`thetaInt` into a monoid of matrices — use `h := map_mul θ g g⁻¹; rw [mul_inv_cancel, map_one, hg, one_mul] at h`).
2. `tamePart_mem_tameSubgroup`: `show thetaInt p D (g * (ιpD p D (thetaIntGL p D g))⁻¹) = 1`; `rw [map_mul, ← thetaIntGL…]` — cleanest through `thetaIntGL`: `thetaIntGL (tamePart g) = θGL g * (θGL (ιpD (θGL g)))⁻¹ = θGL g * (θGL g)⁻¹ = 1` (`map_mul`, `map_inv`, `thetaIntGL_ιpD`, `mul_inv_cancel`), then `coe_thetaIntGL`, `Units.val_one`.
3. `eq_ιpD_mul_tamePart`: `tamePart g` has trivial `p`-component (item 2), so `ιpD (θGL g) * tamePart g = tamePart g * ιpD (θGL g)` (Q5), and `tamePart g * ιpD (θGL g) = g` (`inv_mul_cancel_right`).  **Not definitional** (trap recorded in the header).

- **Mathlib/project lemmas needed**: `map_mul`, `map_one`, `map_inv`, `thetaIntGL_ιpD`, `coe_thetaIntGL`, Q5, `inv_mul_cancel_right`
- **Sources**: decomposition Q7.
- **Generality decision**: as the statements.
- **Size**: ~20 lines
- **Progress**: done 2026-09-14 — closure by change; tamePart via thetaIntGL; eq_ιpD_mul_tamePart via Q5; lake build of 23_QuaternionData green (only `central := sorry` left, removed at S0).

### [Q8] `tamePart_mul`, `tamePart_one`, `tamePart_inv`, `tamePart_ιpD`, `tamePart_eq_self_of_thetaInt_eq_one`, `tamePart_conj_ιpD`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q7
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:149
theorem tamePart_mul (g g' : Dfx ℚ D) :
    tamePart p D (g * g') = tamePart p D g * tamePart p D g' := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:153
theorem tamePart_one : tamePart p D 1 = 1 := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:156
theorem tamePart_inv (g : Dfx ℚ D) : tamePart p D g⁻¹ = (tamePart p D g)⁻¹ := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:159
theorem tamePart_ιpD (g : GL (Fin 2) ℚ_[p]) : tamePart p D (ιpD p D g) = 1 := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:162
theorem tamePart_eq_self_of_thetaInt_eq_one {g : Dfx ℚ D} (hg : thetaInt p D g = 1) :
    tamePart p D g = g := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:166
/-- Conjugating by a `p`-local element does not change the tame part. -/
theorem tamePart_conj_ιpD (g : GL (Fin 2) ℚ_[p]) (x : Dfx ℚ D) :
    tamePart p D (ιpD p D g * x * (ιpD p D g)⁻¹) = tamePart p D x := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `tamePart_mul`: unfold; `map_mul θGL`, `map_mul ιpD`, `mul_inv_rev`; `g * g' * ((ιp θg')⁻¹ * (ιp θg)⁻¹) = g * (ιp θg)⁻¹ * (g' * (ιp θg')⁻¹)` iff `(ιp θg)⁻¹` commutes with `tamePart g'` — `Q5` at `(θGL g)⁻¹` (`map_inv ιpD`) and `thetaInt_tamePart`; `group`/`mul_assoc` bookkeeping.
2. `tamePart_one`: `map_one`, `inv_one`, `mul_one`.  `tamePart_inv`: from `tamePart_mul` at `g, g⁻¹` and `tamePart_one` (`eq_inv_of_mul_eq_one_left`).
3. `tamePart_ιpD`: `thetaIntGL_ιpD`, `mul_inv_cancel`.  `tamePart_eq_self_of_thetaInt_eq_one`: `thetaIntGL g = 1` (`Units.ext hg`), `map_one`, `inv_one`, `mul_one`.
4. `tamePart_conj_ιpD`: `tamePart_mul` twice, `tamePart_inv`, `tamePart_ιpD`, `one_mul`, `mul_one`… (`tamePart (ιp g)⁻¹ = 1` via `tamePart_inv`, `inv_one`).

- **Mathlib/project lemmas needed**: Q5, Q7, `map_mul`, `map_inv`, `mul_inv_rev`, `thetaIntGL_ιpD`, `eq_inv_of_mul_eq_one_left`
- **Sources**: decomposition Q8.
- **Generality decision**: as the statements.
- **Size**: ~30 lines
- **Progress**: done 2026-09-14 — tamePart_mul by group + Q5; inv from mul; lake build of 23_QuaternionData green (only `central := sorry` left, removed at S0).

### [Q9] `levelOf` (closure), `levelOf_subset_levelM1`, `ιpD_mem_levelOf`, `mem_levelOf_of_thetaInt_eq_one`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q8, L3
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:175
/-- **The level** `U = Kt·Iw_p` ([LWX, §2.4]: "`K^p Iw_q`"): `p`-component in `Iw_p`, tame part in
`Kt`. -/
def levelOf : Subgroup (Dfx ℚ D) where
  carrier := {g | thetaInt p D g ∈ Iw p 1 ∧ tamePart p D g ∈ Kt}
  mul_mem' := by sorry
  one_mem' := by sorry
  inv_mem' := by sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:187
theorem levelOf_subset_levelM1 :
    (levelOf p D Kt : Set (Dfx ℚ D)) ⊆ levelM1 (p := p) (thetaInt p D) := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:191
theorem ιpD_mem_levelOf {g : GL (Fin 2) ℚ_[p]} (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) ∈ Iw p 1) :
    ιpD p D g ∈ levelOf p D Kt := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:195
theorem mem_levelOf_of_thetaInt_eq_one {g : Dfx ℚ D} (hg : thetaInt p D g = 1) (hK : g ∈ Kt) :
    g ∈ levelOf p D Kt := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `levelOf.mul_mem'`: `map_mul`, `Submonoid.mul_mem` of `Iw p 1` (`05:141`), `tamePart_mul`, `Kt.mul_mem`; `one_mem'`: `map_one`, `Iw`'s `one_mem`, `tamePart_one`; `inv_mem'`: `θ g⁻¹ = (θ g)⁻¹` (through `thetaIntGL`, `map_inv`, `coe_thetaIntGL`, `Matrix.coe_units_inv`) and `inv_mem_Iw` (L3); `tamePart_inv`, `Kt.inv_mem`.
2. `levelOf_subset_levelM1`: `fun g hg => Iw_one_le_M1 hg.1` (`10:297`; `levelM1` is the preimage of `M1` under `θ` — check `levelM1`'s definition in `05_AtkinLehner`/`09` and use `Set.mem_preimage`).
3. `ιpD_mem_levelOf`: `⟨by rw [thetaInt_ιpD]; exact hg, by rw [tamePart_ιpD]; exact Kt.one_mem⟩`.
4. `mem_levelOf_of_thetaInt_eq_one`: `⟨by rw [hg]; exact Iw's one_mem, by rw [tamePart_eq_self_of_thetaInt_eq_one hg]; exact hK⟩`.

- **Mathlib/project lemmas needed**: L3, Q8, `Iw` (`05:141`), `Iw_one_le_M1` (`10:297`), `thetaInt_ιpD`, `tamePart_ιpD`, `Matrix.coe_units_inv`
- **Sources**: decomposition Q9 ([LWX, §2.4]: the level `K^p Iw_q`, `lwx.txt:671`).
- **Generality decision**: `Kt ≤ tameSubgroup` unused here (only in `normClass_level`).
- **Size**: ~30 lines
- **Progress**: done 2026-09-14 — levelOf closure with inv_mem_Iw (L3); lake build of 23_QuaternionData green (only `central := sorry` left, removed at S0).

### [CLEANUP-Q3] Cleanup `PhD/Main/LWX/23_QuaternionData.lean`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q7, Q8, Q9
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused `simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings; `lake build PhD` and `lake exe runLinter` on the module must be clean (grep the linter's output for the file).  Done inline by the main agent.

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): as CLEANUP-Q1 (same file, one pass); `lake build PhD` green (3929 jobs).

### [Q10] `levelOf_wGL_conj`, `levelOf_wGLH_conj`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q8, Q9
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:199
/-- **`w` normalises the disc-`0` part of the level** (`wQ_conj_mem_Iw` at `p`, and the tame part
is conjugation-invariant). -/
theorem levelOf_wGL_conj : ∀ u ∈ levelOf p D Kt, ‖(thetaInt p D u) 0 1‖ ≤ (p : ℝ)⁻¹ →
    ιpD p D (wGL p) * u * (ιpD p D (wGL p))⁻¹ ∈ levelOf p D Kt ∧
      (ιpD p D (wGL p))⁻¹ * u * ιpD p D (wGL p) ∈ levelOf p D Kt := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:206
/-- **`w_h` normalises the level-`p^{h+1}` part of the level** (`wQH_conj_mem_Iw`). -/
theorem levelOf_wGLH_conj (h : ℕ) :
    ∀ u ∈ levelOf p D Kt, ‖(thetaInt p D u) 0 1‖ ≤ (p : ℝ)⁻¹ ^ h →
    ιpD p D (wGLH p h) * u * (ιpD p D (wGLH p h))⁻¹ ∈ levelOf p D Kt ∧
      (ιpD p D (wGLH p h))⁻¹ * u * ιpD p D (wGLH p h) ∈ levelOf p D Kt := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `intro u hu hb`; `obtain ⟨hIw, hKt⟩ := hu`; `hb'`: `p ∣ b`-form of the hypothesis as `wQ_conj_mem_Iw` (`10:280`) expects (read its exact hypothesis: `‖g 0 1‖ ≤ p⁻¹`).
2. First conjugate: `θ (w u w⁻¹) = wQ * θ u * wQinv` (`map_mul`, `thetaInt_ιpD`, `coe_wGL`, `map_inv`/`coe_wGL_inv` (`18:84`)) `∈ Iw` by `(wQ_conj_mem_Iw hIw hb').1`; `tamePart (w u w⁻¹) = tamePart u ∈ Kt` (`tamePart_conj_ιpD`).
3. Second conjugate: `w⁻¹ u w = ιp (wGL⁻¹) u (ιp wGL⁻¹)⁻¹` (`map_inv`, `inv_inv`), so `tamePart_conj_ιpD` at `g := (wGL p)⁻¹` and `(wQ_conj_mem_Iw hIw hb').2`.
4. `levelOf_wGLH_conj`: the same with `wQH_conj_mem_Iw` (`11:325`), `coe_wGLH`, `coe_wGLH_inv` (`20:69`) and the bound `p⁻¹ ^ h`.

- **Mathlib/project lemmas needed**: `wQ_conj_mem_Iw` (`10:280`), `wQH_conj_mem_Iw` (`11:325`), `coe_wGL_inv` (`18:84`), `coe_wGLH_inv` (`20:69`), `tamePart_conj_ιpD`, `thetaInt_ιpD`, `map_inv`
- **Sources**: decomposition Q10 (docstring of `wQ_conj_mem_Iw` quoted).
- **Generality decision**: matches the fields `w_conj_mem_U` (`18:163`, `20:160`) verbatim.
- **Size**: ~30 lines
- **Progress**: done 2026-09-14 — wQ_conj_mem_Iw / wQH_conj_mem_Iw + tamePart_conj_ιpD; lake build of 23_QuaternionData green (only `central := sorry` left, removed at S0).

### [Q11] `thetaInt_unitsIncl_pUnit`, `unitsIncl_pUnit_comm`, `thetaInt_tameScalar`, `tameScalar_comm`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q6
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:215
/-- The global scalar `p ∈ D^×`. -/
def pUnit : Dˣ :=
  Units.map (algebraMap ℚ D).toMonoidHom (Units.mk0 (p : ℚ) (by exact_mod_cast hp.out.ne_zero))
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:219
theorem thetaInt_unitsIncl_pUnit :
    thetaInt p D (unitsIncl ℚ D (pUnit p D)) = (p : ℚ_[p]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:223
theorem unitsIncl_pUnit_comm (x : Dfx ℚ D) :
    unitsIncl ℚ D (pUnit p D) * x = x * unitsIncl ℚ D (pUnit p D) := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:227
/-- **The tame scalar** `p^{(p)} := p_global⁻¹·p_p`: `1` at `p`, `p⁻¹ · p` away from `p`. -/
def tameScalar : Dfx ℚ D := (unitsIncl ℚ D (pUnit p D))⁻¹ * ιpD p D (pGL p)
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:230
theorem thetaInt_tameScalar : thetaInt p D (tameScalar p D) = 1 := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:233
theorem tameScalar_comm (x : Dfx ℚ D) : tameScalar p D * x = x * tameScalar p D := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `thetaInt_unitsIncl_pUnit`: `unitsIncl = Units.map includeLeftRingHom` (`QMF/03_Quaternionic.lean:53`); `(unitsIncl (pUnit) : D ⊗ 𝔸) = algebraMap ℚ D p ⊗ₜ 1 = algebraMap ℚ (D ⊗ 𝔸) p` (`Algebra.TensorProduct.includeLeft_apply`, `Algebra.TensorProduct.algebraMap_apply`), `= ((p : ℕ) : D ⊗ 𝔸)` (`map_natCast`); `toLocal`, `E`, `mapMatrix padicComparisonSymm` all send `(p : ℕ)` to `(p : ℕ)` (`map_natCast`); finish with `Nat.smul_one_eq_cast`/`Matrix.natCast_eq…` (`(p : Matrix) = p • 1`: `Nat.cast` in `Matrix` is `diagonal`; `Matrix.smul_one_eq_diagonal`/`Nat.smul_one_eq_cast`).  Keep every scalar as `((p : ℕ) : _)`.
2. `unitsIncl_pUnit_comm`: `Units.ext`; `algebraMap ℚ (D ⊗ 𝔸) p` is central: `Algebra.commutes` (`(p : ℕ)` is central in any ring: `Nat.cast_commute`).
3. `thetaInt_tameScalar`: `map_mul`, `map_inv`, `thetaInt_unitsIncl_pUnit`, `thetaInt_ιpD`, `pGL` (`(p : ℚ_p) • 1`), `Matrix.coe_units_inv`… — simplest: through `thetaIntGL` (units): `θGL (unitsIncl pUnit) = pGL p` (`Units.ext` + item 1), so `θGL (tameScalar) = (pGL p)⁻¹ * pGL p = 1`.
4. `tameScalar_comm`: `unitsIncl_pUnit_comm` (and its inverse: `inv` of a central element is central) and `ιpD_pGL_comm` (Q6), `mul_assoc`.

- **Mathlib/project lemmas needed**: `unitsIncl` (`03:53`), `Algebra.TensorProduct.includeLeft_apply`, `Algebra.TensorProduct.algebraMap_apply`, `map_natCast`, `Nat.cast_commute`, `Nat.smul_one_eq_cast`, Q6, `thetaInt_ιpD`
- **Sources**: decomposition Q11.
- **Generality decision**: as the statements (instance trap: scalars as `((p : ℕ) : _)`).
- **Size**: ~30 lines
- **Progress**: done 2026-09-14 — generic toMatrix_unitsIncl_algebraMap restated with RHS algebraMap F F_v c • 1 (rw with Matrix.algebraMap_matrix_apply at ℚ hit the DivisionRing.toRatAlgebra trap); lake build of 23_QuaternionData green (only `central := sorry` left, removed at S0).

### [Q12] `central_pow_of_tameScalar_pow_mem`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q9, Q11
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:236
/-- **`central_pow` from a power of the tame scalar in the tame level**:
`ιp(p·1)^N = p^N_global · (tameScalar)^N`. -/
theorem central_pow_of_tameScalar_pow_mem {N : ℕ} (hN : 0 < N)
    (hmem : tameScalar p D ^ N ∈ Kt) :
    ∃ N, 0 < N ∧ ∃ γ ∈ globalUnits ℚ D, ∃ u ∈ levelOf p D Kt,
      ιpD p D (pGL p) ^ N = γ * u ∧ thetaInt p D u = 1 ∧ ∀ x, γ * x = x * γ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`refine ⟨N, hN, (unitsIncl ℚ D (pUnit p D)) ^ N, pow_mem ⟨pUnit p D, rfl⟩ N, tameScalar p D ^ N, ?_, ?_, ?_, ?_⟩`:
* membership: `mem_levelOf_of_thetaInt_eq_one` with `thetaInt (tameScalar ^ N) = 1` (`map_pow`, `thetaInt_tameScalar`, `one_pow`) and `hmem`;
* `ιpD (pGL p) ^ N = γ * u`: `ιpD (pGL p) = unitsIncl pUnit * tameScalar` (`tameScalar`, `mul_inv_cancel_left`), then `(Commute …).mul_pow` (`Commute/Defs.lean:167`) with `unitsIncl_pUnit_comm`;
* `θ u = 1` as above; `γ` central: `Commute.pow_left`/`(unitsIncl_pUnit_comm x)` iterated (`Commute.pow_left (h : Commute a b) n : Commute (a ^ n) b`).

- **Mathlib/project lemmas needed**: `mem_levelOf_of_thetaInt_eq_one`, `map_pow`, `thetaInt_tameScalar`, `Commute.mul_pow`, `Commute.pow_left`, `MonoidHom.mem_range`/`pow_mem`
- **Sources**: decomposition Q12 (matches the field `central_pow`, `18:157–159`, verbatim).
- **Generality decision**: as the statement.
- **Size**: ~15 lines
- **Progress**: done 2026-09-14 — Commute.mul_pow / pow_left; lake build of 23_QuaternionData green (only `central := sorry` left, removed at S0).

### [CLEANUP-Q4] Cleanup `PhD/Main/LWX/23_QuaternionData.lean`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q10, Q11, Q12
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused `simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings; `lake build PhD` and `lake exe runLinter` on the module must be clean (grep the linter's output for the file).  Done inline by the main agent.

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): as CLEANUP-Q1 (same file, one pass); `lake build PhD` green (3929 jobs).

### [Q13] `norm_det_mul_inv_normClass`, `normClass_level`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q7, Q9
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:293
/-- `det θ_p(g)·q(g)⁻¹` is a `p`-adic unit. -/
theorem norm_det_mul_inv_normClass (g : Dfx ℚ D) :
    ‖(thetaInt p D g).det * ((((X.normClass g : ℚˣ) : ℚ) : ℚ_[p]))⁻¹‖ = 1 := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:298
/-- The level has unit norm class. -/
theorem normClass_level : ∀ u ∈ X.level, X.normClass u = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `norm_det_mul_inv_normClass`: `rw [norm_mul, norm_inv, X.norm_det_thetaInt g, mul_inv_cancel₀]` with `‖(q g : ℚ_p)‖ ≠ 0` (`norm_ne_zero_iff`, `Rat.cast_ne_zero`, `Units.ne_zero`).
2. `normClass_level`: `intro u hu`; `rw [eq_ιpD_mul_tamePart p D u, map_mul, X.normClass_tame _ hu.2, mul_one]`; then `Units.ext`/`Units.val_eq_one`: `X.normClass_ιpD (θGL u)` gives `(p : ℚ) ^ (det θ u).valuation`, and `(det θ u).valuation = 0` because `‖det θ u‖ = 1` (`hu.1.2.2`): `Padic.norm_eq_zpow_neg_valuation (det ≠ 0)` gives `(p : ℝ) ^ (-v) = 1`, so `v = 0` (`zpow_eq_one_iff_right₀`/`zpow_right_injective₀` with `1 < p`); `zpow_zero`.

- **Mathlib/project lemmas needed**: `norm_mul`, `norm_inv`, `mul_inv_cancel₀`, `Padic.norm_eq_zpow_neg_valuation` (`PadicNumbers.lean:1053`), `zpow_eq_one_iff_right₀`, `eq_ιpD_mul_tamePart`, `Units.ext`
- **Sources**: decomposition Q13.
- **Generality decision**: as the statements.
- **Size**: ~20 lines
- **Progress**: done 2026-09-14 — Padic.norm_eq_zpow_neg_valuation + zpow_right_injective₀; lake build of 23_QuaternionData green (only `central := sorry` left, removed at S0).

### [Q14] `normClass_ιpD_vGL`, `normClass_ιpD_wGL`, `normClass_ιpD_wGLH`, `normClass_ιpD_pGL`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: none
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:302
theorem normClass_ιpD_vGL (c : ℚ_[p]) :
    ((X.normClass (ιpD p D (vGL p c)) : ℚˣ) : ℚ) = p := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:306
theorem normClass_ιpD_wGL : ((X.normClass (ιpD p D (wGL p)) : ℚˣ) : ℚ) = (p : ℚ) ^ 2 := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:309
theorem normClass_ιpD_wGLH (h : ℕ) :
    ((X.normClass (ιpD p D (wGLH p h)) : ℚˣ) : ℚ) = (p : ℚ) ^ (h + 1) := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:313
theorem normClass_ιpD_pGL : ((X.normClass (ιpD p D (pGL p)) : ℚˣ) : ℚ) = (p : ℚ) ^ 2 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
Each: `rw [X.normClass_ιpD]`, the determinant (`coe_vGL`/`det_vQ` (`10:78`): `p`; `coe_wGL`/`det_wQ`: `p ^ 2`; `coe_wGLH`/`det_wQH` (`11:88`): `p ^ (h + 1)`; `pGL`: `Matrix.det_smul`, `Matrix.det_one`, `Fintype.card_fin`: `p ^ 2`), then `Padic.valuation_p` (`PadicNumbers.lean:1091`), `Padic.valuation_pow`? — if absent, `Padic.valuation_p_pow`/derive from `Padic.norm_eq_zpow_neg_valuation` and `Padic.norm_p_pow`; `zpow_natCast`, `pow_one`.

- **Mathlib/project lemmas needed**: `det_vQ`, `det_wQ`, `det_wQH`, `Matrix.det_smul`, `Padic.valuation_p`, `Padic.norm_p_pow`, `zpow_natCast`
- **Sources**: decomposition Q14.
- **Generality decision**: as the statements (the unused `‖c‖ ≤ 1` was removed at planning).
- **Size**: ~15 lines
- **Progress**: done 2026-09-14 — Padic.valuation_p / valuation_pow + norm_cast; lake build of 23_QuaternionData green (only `central := sorry` left, removed at S0).

### [Q15] `heckeChar` (the unit proof, `map_one'`, `map_mul'`)
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q13
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:324
/-- **The Hecke character** `χ = ψ_A ∘ ν` of the classical weight `(k, ψ)` on the disc `ω`
([LWX, Prop 3.22]'s "central Hecke character associated to `ψ`", `lwx.txt:1783`):
`χ(g) = ψ_neb(det θ_p(g) · q(g)⁻¹)`, a unit by `norm_det_thetaInt`. -/
def heckeChar (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) (ζ : K) (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) : Dfx ℚ D →* Kˣ where
  toFun g := Units.mk0
    (nebCharK ψ ω k ζ (ψ ((thetaInt p D g).det * ((((X.normClass g : ℚˣ) : ℚ) : ℚ_[p]))⁻¹)))
    (by sorry)
  map_one' := by sorry
  map_mul' := by sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. Unit: `nebCharK_psi_ne_zero hp2 hψ hζ` (`17:364`) at the argument, whose norm is `1` by `norm_det_mul_inv_normClass` (read its hypothesis: `‖x‖ = 1`).
2. `map_one'`: `Units.ext`; argument `= 1` (`map_one`, `Matrix.det_one`, `Units.val_one`, `Rat.cast_one`, `inv_one`, `mul_one`), then `nebCharK_psi_of_norm_sub_one_le_sq` (`17:376`) at `x = 1` (`sub_self`, `norm_zero`, positivity).
3. `map_mul'`: `Units.ext`; the argument is multiplicative (`map_mul` of `thetaInt`, `Matrix.det_mul`, `map_mul` of `normClass`, `Units.val_mul`, `Rat.cast_mul`, `mul_inv`, `mul_mul_mul_comm`), then `nebCharK_psi_mul hp2 hψ hζ` (`17:348`) on the two norm-one factors (Q13).

- **Mathlib/project lemmas needed**: `nebCharK_psi_ne_zero` (`17:364`), `nebCharK_psi_of_norm_sub_one_le_sq` (`17:376`), `nebCharK_psi_mul` (`17:348`), Q13, `Units.ext`, `Matrix.det_mul`, `mul_mul_mul_comm`
- **Sources**: [LWX, Prop 3.22]'s proof, `lwx.txt:1783` ("a central Hecke character associated to `ψ`"); decomposition Q15.
- **Generality decision**: `χ(g) = ψ_neb(det θ_p(g)·q(g)⁻¹)`; a character only on norm-one arguments, which Q13 supplies.
- **Size**: ~25 lines
- **Progress**: done 2026-09-14 — Units.mk0 proof nebCharK_psi_ne_zero; map_mul via harg (ring); lake build of 23_QuaternionData green (only `central := sorry` left, removed at S0).

### [CLEANUP-Q5] Cleanup `PhD/Main/LWX/23_QuaternionData.lean`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q13, Q14, Q15
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused `simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings; `lake build PhD` and `lake exe runLinter` on the module must be clean (grep the linter's output for the file).  Done inline by the main agent.

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): as CLEANUP-Q1 (same file, one pass); `lake build PhD` green (3929 jobs).

### [Q16] `heckeChar_global`, `heckeChar_level`, `heckeChar_ιpD_vGL`, `heckeChar_ιpD_wGL`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q14, Q15
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:342
/-- `χ` is trivial on `D^×` (`normClass_global`, the product formula for a positive rational). -/
theorem heckeChar_global (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) (ζ : K) (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p) :
    ∀ γ ∈ globalUnits ℚ D, X.heckeChar ψ ω k ζ hp2 hψ hζ γ = 1 := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:348
/-- On the level, `χ` is the nebentypus of the `p`-component (`normClass_level`). -/
theorem heckeChar_level (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) (ζ : K) (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p) :
    ∀ u ∈ X.level, ((X.heckeChar ψ ω k ζ hp2 hψ hζ u : Kˣ) : K)
      = nebCharK ψ ω k ζ (ψ (thetaInt p D u).det) := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:355
theorem heckeChar_ιpD_vGL (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) (ζ : K) (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p) :
    ∀ c : ℚ_[p], X.heckeChar ψ ω k ζ hp2 hψ hζ (ιpD p D (vGL p c)) = 1 := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:360
theorem heckeChar_ιpD_wGL (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) (ζ : K) (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p) :
    X.heckeChar ψ ω k ζ hp2 hψ hζ (ιpD p D (wGL p)) = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `heckeChar_global`: `Units.ext`; `heckeChar_apply`; `X.normClass_global γ hγ` rewrites `(q γ : ℚ_p)` to `det θ γ`, so the argument is `det · det⁻¹ = 1` (`mul_inv_cancel₀`, `det_thetaInt_ne_zero`), then `nebCharK_psi_of_norm_sub_one_le_sq` at `1`.
2. `heckeChar_level`: `heckeChar_apply`, `X.normClass_level u hu` ⇒ `q u = 1`, `Units.val_one`, `Rat.cast_one`, `inv_one`, `mul_one`.
3. `heckeChar_ιpD_vGL`: argument `det(vQ c) · p⁻¹ = p · p⁻¹ = 1` (`thetaInt_ιpD`, `coe_vGL`, `det_vQ`, `normClass_ιpD_vGL`, `Rat.cast_natCast`, `mul_inv_cancel₀`); then as 1.
4. `heckeChar_ιpD_wGL`: `det_wQ = p ^ 2`, `normClass_ιpD_wGL`, `Rat.cast_pow`.

- **Mathlib/project lemmas needed**: `heckeChar_apply`, `normClass_global`, `normClass_level`, Q14, `det_vQ`, `det_wQ`, `nebCharK_psi_of_norm_sub_one_le_sq`, `Rat.cast_natCast`, `Rat.cast_pow`
- **Sources**: decomposition Q16 (the fields `χ_Γ`, `χ_U`, `χ_vGL`, `χ_wGL` of `22:65–69` are matched verbatim).
- **Generality decision**: as the statements.
- **Size**: ~25 lines
- **Progress**: done 2026-09-14 — normClass axioms + nebCharK_psi_of_norm_sub_one_le_sq at 1; lake build of 23_QuaternionData green (only `central := sorry` left, removed at S0).

### [Q17] `heckeCharH` (the unit proof, `map_one'`, `map_mul'`)
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q13
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:365
/-- **The Hecke character of conductor `p^{h+1}`**, with `nebCharKH`. -/
def heckeCharH (h : ℕ) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) (ζh : K) (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h) (hζh : IsPrimitiveRoot ζh (p ^ h)) : Dfx ℚ D →* Kˣ where
  toFun g := Units.mk0
    (nebCharKH h ψ ω k ζh
      (ψ ((thetaInt p D g).det * ((((X.normClass g : ℚˣ) : ℚ) : ℚ_[p]))⁻¹)))
    (by sorry)
  map_one' := by sorry
  map_mul' := by sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As Q15 with `nebCharKH_psi_ne_zero` (`19_NebCharH:430`), `nebCharKH_psi_of_norm_sub_one_le_pow` (`:442`), `nebCharKH_psi_mul` (`:413`); `hh : 0 < h` threads through.

- **Mathlib/project lemmas needed**: `nebCharKH_psi_*` (`19_NebCharH.lean:413–442`), Q13
- **Sources**: decomposition Q17–Q18.
- **Generality decision**: level `h`.
- **Size**: ~25 lines
- **Progress**: done 2026-09-14 — as Q15 (plus heckeCharH_apply rfl lemma [NEW DECL]); lake build of 23_QuaternionData green (only `central := sorry` left, removed at S0).

### [Q18] `heckeCharH_global`, `heckeCharH_level`, `heckeCharH_ιpD_vGL`, `heckeCharH_ιpD_wGLH`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q14, Q17
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:375
theorem heckeCharH_global (h : ℕ) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) (ζh : K) (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h) (hζh : IsPrimitiveRoot ζh (p ^ h)) :
    ∀ γ ∈ globalUnits ℚ D, X.heckeCharH ψ h ω k ζh hp2 hψ hh hζh γ = 1 := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:380
theorem heckeCharH_level (h : ℕ) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) (ζh : K) (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h) (hζh : IsPrimitiveRoot ζh (p ^ h)) :
    ∀ u ∈ X.level, ((X.heckeCharH ψ h ω k ζh hp2 hψ hh hζh u : Kˣ) : K)
      = nebCharKH h ψ ω k ζh (ψ (thetaInt p D u).det) := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:386
theorem heckeCharH_ιpD_vGL (h : ℕ) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) (ζh : K) (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h) (hζh : IsPrimitiveRoot ζh (p ^ h)) :
    ∀ c : ℚ_[p], X.heckeCharH ψ h ω k ζh hp2 hψ hh hζh (ιpD p D (vGL p c)) = 1 := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:391
theorem heckeCharH_ιpD_wGLH (h : ℕ) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) (ζh : K) (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hh : 0 < h) (hζh : IsPrimitiveRoot ζh (p ^ h)) :
    X.heckeCharH ψ h ω k ζh hp2 hψ hh hζh (ιpD p D (wGLH p h)) = 1 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
As Q16 with `nebCharKH_psi_of_norm_sub_one_le_pow` and, for `wGLH`, `det_wQH = p ^ (h + 1)` (`11:88`) with `normClass_ιpD_wGLH`.

- **Mathlib/project lemmas needed**: Q14, Q17, `det_wQH`
- **Sources**: decomposition Q17–Q18 (`χ_wGLH`, `22:128`).
- **Generality decision**: level `h`.
- **Size**: ~25 lines
- **Progress**: done 2026-09-14 — as Q16; lake build of 23_QuaternionData green (only `central := sorry` left, removed at S0).

### [CLEANUP-Q6] Cleanup `PhD/Main/LWX/23_QuaternionData.lean`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q16, Q17, Q18
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused `simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings; `lake build PhD` and `lake exe runLinter` on the module must be clean (grep the linter's output for the file).  Done inline by the main agent.

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): as CLEANUP-Q1 (same file, one pass); `lake build PhD` green (3929 jobs).

### [Q19] `atkinLehnerFamily`, `atkinLehnerFamilyH` elaborate sorry-free
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: S0, Q10, Q12, Q16, Q18
- **Parallel**: yes (within the dependency order)
- **Type**: check

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:406
/-- **The Atkin–Lehner family of `D/ℚ`** at conductor `p²`. -/
def atkinLehnerFamily (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p) :
    AtkinLehnerFamily (thetaInt p D) ψ X.level (globalUnits ℚ D) ζ where
  ιp := ιpD p D
  theta_ιp := thetaInt_ιpD p D
  ιp_mem_U := fun _ hg => ιpD_mem_levelOf p D X.Kt hg
  central := sorry
  ιp_pGL_comm := ιpD_pGL_comm p D
  central_pow := by
    obtain ⟨N, hN, hmem⟩ := X.tameScalar_pow_mem
    exact central_pow_of_tameScalar_pow_mem p D X.Kt hN hmem
  w_conj_mem_U := levelOf_wGL_conj p D X.Kt
  χ := fun ω k => X.heckeChar ψ ω k ζ hp2 hψ hζ
  χ_Γ := fun ω k => X.heckeChar_global ψ ω k ζ hp2 hψ hζ
  χ_U := fun ω k => X.heckeChar_level ψ ω k ζ hp2 hψ hζ
  χ_vGL := fun ω k => X.heckeChar_ιpD_vGL ψ ω k ζ hp2 hψ hζ
  χ_wGL := fun ω k => X.heckeChar_ιpD_wGL ψ ω k ζ hp2 hψ hζ
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:424
/-- **The level-`h` family of `D/ℚ`** over the same section. -/
def atkinLehnerFamilyH (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (h : ℕ) {ζh : K} (hh : 0 < h) (hζh : IsPrimitiveRoot ζh (p ^ h)) :
    AtkinLehnerFamilyH (thetaInt p D) ψ X.level (X.atkinLehnerFamily ψ hp2 hψ hζ) h ζh where
  χ := fun ω k => X.heckeCharH ψ h ω k ζh hp2 hψ hh hζh
  χ_Γ := fun ω k => X.heckeCharH_global ψ h ω k ζh hp2 hψ hh hζh
  χ_U := fun ω k => X.heckeCharH_level ψ h ω k ζh hp2 hψ hh hζh
  χ_vGL := fun ω k => X.heckeCharH_ιpD_vGL ψ h ω k ζh hp2 hψ hh hζh
  χ_wGLH := fun ω k => X.heckeCharH_ιpD_wGLH ψ h ω k ζh hp2 hψ hh hζh
  w_conj_mem_U := levelOf_wGLH_conj p D X.Kt h
```

- **Depends on (declarations)**: —

**Proof sketch**:
Nothing to prove after S0 deletes `central := sorry`: check that both definitions elaborate with every field discharged by name (the skeleton already elaborates the field types), and record `#print axioms LWX.QuaternionInput.atkinLehnerFamily`.

- **Mathlib/project lemmas needed**: —
- **Sources**: decomposition Q19.
- **Generality decision**: as the statements.
- **Size**: 0 lines
- **Progress**: done 2026-09-14 — after S0 both families elaborate with every field discharged by name; `#print axioms LWX.QuaternionInput.atkinLehnerFamily` / `atkinLehnerFamilyH` / `upDatum` = [propext, Classical.choice, Quot.sound].

### [Q20a] `vRepQ_mem_levelM1`, `injective_vRepQ`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q3
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:439
variable (p D) in
/-- The `U_p`-representatives `v_c = ιp (p 0; cp 1)` ([LWX, §2.5]). -/
def vRepQ (c : Fin p) : Dfx ℚ D := ιpD p D (vGL p (c : ℕ))
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:443
variable (p D) in
theorem vRepQ_mem_levelM1 (c : Fin p) : vRepQ p D c ∈ levelM1 (p := p) (thetaInt p D) := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:447
variable (p D) in
/-- The `U_p`-element `η = ιp (p 0; 0 1)`. -/
def upEltQ : Dfx ℚ D := ιpD p D (vGL p 0)
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:479
theorem injective_vRepQ : Function.Injective (vRepQ p D) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `vRepQ_mem_levelM1`: as `vRepD_mem_levelM1` (`19:57–61`): `levelM1` membership is `θ (vRepQ c) ∈ M1`, `thetaInt_ιpD`, `coe_vGL`, `vQ_mem_M1`.
2. `injective_vRepQ`: `intro b c h`; `have := ιpD_injective p D h`; `vGL p b = vGL p c ⇒ b = c`: compare the `(1,0)` entries (`congrArg (fun g : GL _ _ => (g : Matrix _ _ _) 1 0)`, `coe_vGL`, `vQ`: `(b : ℚ_p) * p = c * p`, `mul_right_cancel₀`, `Nat.cast_injective`, `Fin.ext`).

- **Mathlib/project lemmas needed**: `vRepD_mem_levelM1` (`19:57`), `vQ_mem_M1`, `ιpD_injective`, `coe_vGL`, `mul_right_cancel₀`, `Nat.cast_injective`
- **Sources**: decomposition Q20.
- **Generality decision**: as the statements.
- **Size**: ~12 lines
- **Progress**: done 2026-09-14 — thetaInt_ιpD + vQ_mem_M1; injectivity from entry (1,0); lake build of 23_QuaternionData green (only `central := sorry` left, removed at S0).

### [Q20b] `bijOn_vRepQ` (the coset decomposition `U η U = ∐ U v_c`)
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: L1, L2, Q5, Q7, Q8, Q9, Q20a
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:469
/-- **The coset decomposition** `U η U = ∐_{c<p} U v_c` ([LWX, §2.5]), from the local Iwahori
decomposition (`exists_mem_Iw_mul_vQ`) and the commutation of the tame part with `p`-local
elements. -/
theorem bijOn_vRepQ :
    Set.BijOn (Quotient.mk'' : Dfx ℚ D → RightCosets X.level) (Set.range (vRepQ p D))
      (((Quotient.mk'' : Dfx ℚ D → RightCosets X.level) ''
        (({upEltQ p D} : Set (Dfx ℚ D)) * (X.level : Set (Dfx ℚ D)))) :
          Set (RightCosets X.level)) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`refine ⟨?_, ?_, ?_⟩` (`Set.BijOn` = `MapsTo ∧ InjOn ∧ SurjOn`); throughout `RightCosets X.level` is the quotient by `QuotientGroup.rightRel`, membership of a class in the image set is `Set.mem_image`, and equality of classes is `Quotient.eq''` + `QuotientGroup.rightRel_apply` (`y * x⁻¹ ∈ U`, `Coset/Defs.lean:111`).
1. **MapsTo**: `rintro _ ⟨c, rfl⟩`; `v_c = η * ιp(ℓ)` with `ℓ := (vGL p 0)⁻¹ * vGL p c`, whose matrix is `!![1, 0; c, 1] ∈ Iw p 1` (`ℓQ_mem_Iw` (`10:227`) or direct `mem_Iw_iff` check; `map_inv`, `coe_vGL`, `vQ`), so `ιp ℓ ∈ U` (`ιpD_mem_levelOf`) and `v_c ∈ {η} * U` (`Set.mem_mul`, `Set.mem_singleton_iff`); `exact ⟨_, ⟨η, rfl, ιp ℓ, hℓ, by rw [← map_mul, mul_inv_cancel_left]⟩, rfl⟩`.
2. **InjOn**: `rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩ h`; `Quotient.eq''.1 h`, `QuotientGroup.rightRel_apply`: `v_c * v_b⁻¹ ∈ U` — wait for the orientation of `rightRel` (`y * x⁻¹ ∈ s`); so `k := θ (v_b * v_c⁻¹) ∈ Iw` (`.1` of the level condition; `map_mul`, `map_inv`, `thetaInt_ιpD`, `coe_vGL`) with `vQ b = k * vQ c` (`Matrix.mul_assoc`, `Matrix.nonsing_inv_mul`/`Matrix.coe_units_inv`), hence `b = c` by `eq_of_vQ_eq_mul_vQ` (L2) and `congrArg vRepQ`.
3. **SurjOn**: `rintro _ ⟨_, ⟨_, rfl, u, hu, rfl⟩, rfl⟩` (an element `η * u`, `u ∈ U`); `u = ιp (θGL u) * tamePart u` (`eq_ιpD_mul_tamePart`); `obtain ⟨c, k', hk', hkv⟩ := exists_mem_Iw_mul_vQ hu.1` (L1: `vQ 0 * θ u = k' * vQ c`); so `η * u = ιp(vGL 0 * θGL u) * tamePart u = ιp (k'GL * vGL c) * tamePart u = ιp k'GL * tamePart u * v_c` — the last step moves `tamePart u` past `ιp (vGL c)` (Q5 with `thetaInt_tamePart`); `ιp k'GL * tamePart u ∈ U` (`ιpD_mem_levelOf`, `mem_levelOf_of_thetaInt_eq_one` with `tamePart u ∈ Kt` (`hu.2`), `mul_mem`).  Conclude `Quotient.mk'' (η * u) = Quotient.mk'' (v_c)` by `Quotient.sound'`/`Quotient.eq''` and `rightRel_apply` (`(η u) * v_c⁻¹ = ιp k' * tamePart u ∈ U`); `exact ⟨v_c, ⟨c, rfl⟩, this⟩`.
Build `k'GL := Matrix.GeneralLinearGroup.mkOfDetNeZero k' (norm-one determinant ≠ 0)` and use `Units.ext` to transport `hkv` to `GL`.

- **Mathlib/project lemmas needed**: L1, L2, Q5, Q7 (`eq_ιpD_mul_tamePart`), Q9, `ℓQ_mem_Iw`, `QuotientGroup.rightRel_apply`, `Quotient.eq''`, `Set.mem_mul`, `Set.BijOn`, `Matrix.GeneralLinearGroup.mkOfDetNeZero`
- **Sources**: [LWX, §2.5] `lwx.txt:706–711` through L1–L2; decomposition Q20 (the JacobsSlash precedent `bijOn_etaRep`, `JacobsSlash/U3/3_EtaDecomposition.lean:486`, for the statement shape).
- **Generality decision**: as the statement (`Kt_le` unused).
- **Size**: ~120 lines
- **Progress**: done 2026-09-14 — MapsTo via ℓGL 0 c = (vGL 0)⁻¹ vGL c; InjOn via L2; SurjOn via L1 + tamePart commutation (show to beta-reduce the image2 lambda); lake build of 23_QuaternionData green (only `central := sorry` left, removed at S0).

### [Q20c] `finite_image_upEltQ`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q20b
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:482
theorem finite_image_upEltQ :
    (((Quotient.mk'' : Dfx ℚ D → RightCosets X.level) ''
      (({upEltQ p D} : Set (Dfx ℚ D)) * (X.level : Set (Dfx ℚ D)))) :
        Set (RightCosets X.level)).Finite := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [← X.bijOn_vRepQ.image_eq]; exact (Set.finite_range _).image _`.

- **Mathlib/project lemmas needed**: `Set.BijOn.image_eq`, `Set.finite_range`, `Set.Finite.image`
- **Sources**: decomposition Q20.
- **Generality decision**: as the statement.
- **Size**: 1 line
- **Progress**: done 2026-09-14 — BijOn.image_eq; lake build of 23_QuaternionData green (only `central := sorry` left, removed at S0).

### [CLEANUP-Q7] Cleanup `PhD/Main/LWX/23_QuaternionData.lean`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q20a, Q20b, Q20c
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused `simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings; `lake build PhD` and `lake exe runLinter` on the module must be clean (grep the linter's output for the file).  Done inline by the main agent.

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): as CLEANUP-Q1 (same file, one pass); `lake build PhD` green (3929 jobs).

### [Q21] `exists_factorisation` (and the chosen data `idx`, `dElt`, `uElt`, `dElt_mem`, `c_mul_vRepQ_inv`)
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: none
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:488
/-- **The factorisation** `c_i v_t⁻¹ = d · c_j · u` ([LWX, Prop 3.1]: "write each `γ_i v_j⁻¹`
uniquely as `δ_{i,j}⁻¹ γ_{λ_{i,j}} u_{i,j}`", `lwx.txt:1075`) from the class-set bijection. -/
theorem exists_factorisation (i : ι) (t : Fin p) :
    ∃ j : ι, ∃ d : Dfx ℚ D, ∃ u : X.level, d ∈ globalUnits ℚ D ∧
      X.c i * (vRepQ p D t)⁻¹ = d * X.c j * (u : Dfx ℚ D) := by
  sorry
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:495
/-- The target index `λ_{i,t}`. -/
def idx (i : ι) (t : Fin p) : ι := (X.exists_factorisation i t).choose
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:498
/-- The global element `δ_{i,t}⁻¹`. -/
def dElt (i : ι) (t : Fin p) : Dfx ℚ D := (X.exists_factorisation i t).choose_spec.choose
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:501
/-- The level element `u_{i,t}`. -/
def uElt (i : ι) (t : Fin p) : X.level :=
  (X.exists_factorisation i t).choose_spec.choose_spec.choose
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:505
theorem dElt_mem (i : ι) (t : Fin p) : X.dElt i t ∈ globalUnits ℚ D :=
  (X.exists_factorisation i t).choose_spec.choose_spec.choose_spec.1
```
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:508
theorem c_mul_vRepQ_inv (i : ι) (t : Fin p) :
    X.c i * (vRepQ p D t)⁻¹ = X.dElt i t * X.c (X.idx i t) * (X.uElt i t : Dfx ℚ D) :=
  (X.exists_factorisation i t).choose_spec.choose_spec.choose_spec.2
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `obtain ⟨j, hj⟩ := X.hc.2 (Quotient.mk'' (X.c i * (vRepQ p D t)⁻¹))` (surjectivity onto the double-coset quotient).
2. `obtain ⟨γ, hγ, v, hv, hrel⟩ := DoubleCoset.rel_iff.mp (Quotient.eq''.mp hj)` (`Mathlib/GroupTheory/DoubleCoset.lean:82`; the pattern at `18:970–971`): `X.c i * (vRepQ p D t)⁻¹ = γ * X.c j * v` with `γ ∈ globalUnits`, `v ∈ levelOf` (check the orientation of `rel_iff`: `∃ a ∈ H, ∃ b ∈ K, y = a * x * b`, so read `hj` in the direction that puts `c j` in the middle — take `hj.symm` if needed).
3. `exact ⟨j, γ, ⟨v, hv⟩, hγ, hrel⟩`.  The `choose` definitions and the two `choose_spec` projections are already in place (no sorry).

- **Mathlib/project lemmas needed**: `Function.Bijective.surjective`, `DoubleCoset.rel_iff`, `Quotient.eq''`
- **Sources**: [LWX, Prop 3.1] `lwx.txt:1075` ("write each `γ_i v_j⁻¹` uniquely as `δ_{i,j}⁻¹ γ_{λ_{i,j}} u_{i,j}`"); decomposition Q21.
- **Generality decision**: uniqueness not needed (the data are chosen).
- **Size**: ~8 lines
- **Progress**: done 2026-09-14 — DoubleCoset.rel_iff; lake build of 23_QuaternionData green (only `central := sorry` left, removed at S0).

### [Q22] `hshape`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q20a, Q20b
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:512
/-- The shape certificate (`isUpShape_certM1` at `η = ιp (p 0; 0 1)`). -/
theorem hshape (i : ι) (t : Fin p) :
    (M1.toLocalMat (certM1 (thetaInt p D) X.level X.level_subset_levelM1 (vRepQ p D)
      (vRepQ_mem_levelM1 p D) X.uElt i t)).IsUpShape := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`exact isUpShape_certM1 (thetaInt p D) X.level X.level_subset_levelM1 (vRepQ p D) (vRepQ_mem_levelM1 p D) X.uElt (vRepQ_mem_levelM1 p D 0) ?_ X.bijOn_vRepQ i t`
(`05_Certificates.lean:169`: `(hη : η ∈ levelM1) (hηa : ‖θ η 0 0‖ ≤ p⁻¹) (hv : BijOn …) i t`), where `η = upEltQ p D = vRepQ p D 0` up to `Nat.cast_zero` (`show` the defeq or `rw [show upEltQ p D = vRepQ p D 0 from rfl]`), and `hηa`: `thetaInt_ιpD`, `coe_vGL`, `vQ`, entry `(0,0) = p`, `Padic.norm_p`.

- **Mathlib/project lemmas needed**: `isUpShape_certM1` (`05:169`), `thetaInt_ιpD`, `coe_vGL`, `Padic.norm_p`
- **Sources**: [LWX, Prop 3.1(3)] (`lwx.txt:1052`); decomposition Q22.
- **Generality decision**: as the statement.
- **Size**: ~6 lines
- **Progress**: done 2026-09-14 — isUpShape_certM1 at η = upEltQ; lake build of 23_QuaternionData green (only `central := sorry` left, removed at S0).

### [Q23] `det_certM1_eq` **[MILESTONE: decision 2, the canonical determinant certificate]**
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q3, Q13, Q14, Q21
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:518
/-- **Decision 2, the canonical fix: the determinant certificate.**  With the representatives
normalised (`c_thetaInt`, `c_normClass`), the norm class of `d_{i,t}` in
`c_i v_t⁻¹ = d·c_j·u` is `p⁻¹` exactly, so `det θ(u_{i,t} v_t) = p`. -/
theorem det_certM1_eq (i : ι) (t : Fin p) :
    (certM1 (thetaInt p D) X.level X.level_subset_levelM1 (vRepQ p D) (vRepQ_mem_levelM1 p D)
      X.uElt i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`rw [coe_certM1, map_mul]` (`05:63`: `= θ (u * v_t)`), then `det θ(u) · det θ(v_t) = p`:
1. Apply `thetaIntGL` to `X.c_mul_vRepQ_inv i t`: `θGL(c_i) * θGL(v_t)⁻¹ = θGL(d) * θGL(c_j) * θGL(u)` (`map_mul`, `map_inv`) with `θGL(c_i) = θGL(c_j) = 1` (`Units.ext (X.c_thetaInt _)`), so `θGL(u) * θGL(v_t) = θGL(d)⁻¹` (`Units` algebra: `mul_eq_one_iff_eq_inv`/`eq_inv_of_mul_eq_one_left`), hence `det(θ u * θ v_t) = (det θ d)⁻¹` (`coe_thetaIntGL`, `Matrix.coe_units_inv`, `Matrix.det_nonsing_inv`, `Ring.inverse_eq_inv`).
2. Apply `normClass`: `q(c_i) * q(v_t)⁻¹ = q(d) * q(c_j) * q(u)` with `q(c_i) = q(c_j) = 1` (`c_normClass`), `q(u) = 1` (`normClass_level _ (X.uElt i t).2`), `(q(v_t) : ℚ) = p` (`normClass_ιpD_vGL`), so `(q(d) : ℚ) = p⁻¹` (`Units.ext`-free: work in `ℚ` via `Units.val_mul`, `Units.val_inv_eq_inv_val`).
3. `X.normClass_global _ (X.dElt_mem i t)`: `(det θ d : ℚ_p) = ((p⁻¹ : ℚ) : ℚ_p) = (p : ℚ_p)⁻¹` (`Rat.cast_inv`, `Rat.cast_natCast`).
4. Combine: `det(θ u * θ v_t) = ((p : ℚ_p)⁻¹)⁻¹ = p` (`inv_inv`).

- **Mathlib/project lemmas needed**: `coe_certM1` (`05:63`), `c_mul_vRepQ_inv`, `c_thetaInt`, `c_normClass`, `normClass_level` (Q13), `normClass_ιpD_vGL` (Q14), `normClass_global`, `dElt_mem`, `Matrix.det_nonsing_inv`, `Matrix.coe_units_inv`, `Rat.cast_inv`, `Rat.cast_natCast`, `inv_inv`
- **Sources**: [LWX, Prop 3.1] `lwx.txt:1084` ("note the fact that both `γ_i` and `γ_{λ_{i,j}}` have trivial `p`-component"); decomposition Q23 (attack [3]: without `c_normClass` one only gets a unit multiple of `p`).
- **Generality decision**: the conclusion is exactly `hdet` of `15_StepThree.lean:209` — no downstream statement changes.
- **Size**: ~35 lines
- **Progress**: done 2026-09-14 — thetaIntGL and normClass of the factorisation; det = ((p⁻¹))⁻¹; lake build of 23_QuaternionData green (only `central := sorry` left, removed at S0).

### [Q24] `upDatum` elaborates; the datum's fields
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q22
- **Parallel**: yes (within the dependency order)
- **Type**: check

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/23_QuaternionData.lean:526
/-- **The `U_p`-datum of `D/ℚ`** at the level `Kt·Iw_p`. -/
def upDatum : UpDatum p ι :=
  UpDatum.ofCerts (thetaInt p D) X.level X.level_subset_levelM1 (vRepQ p D)
    (vRepQ_mem_levelM1 p D) X.idx X.uElt X.hshape
```

- **Depends on (declarations)**: —

**Proof sketch**:
Nothing to prove: `upDatum` is `UpDatum.ofCerts … X.hshape`; check `#print axioms LWX.QuaternionInput.upDatum` and that `X.upDatum.tgt = X.idx` (`UpDatum.ofCerts_tgt`) unfolds by `rfl`.

- **Mathlib/project lemmas needed**: `UpDatum.ofCerts_tgt`, `UpDatum.ofCerts_mat`
- **Sources**: decomposition Q24.
- **Generality decision**: —
- **Size**: 0 lines
- **Progress**: done 2026-09-14 — nothing to prove; lake build of 23_QuaternionData green (only `central := sorry` left, removed at S0).

### [CLEANUP-Q-FINAL] Cleanup `PhD/Main/LWX/23_QuaternionData.lean`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q21, Q22, Q23, Q24
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused `simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings; `lake build PhD` and `lake exe runLinter` on the module must be clean (grep the linter's output for the file).  Done inline by the main agent.  Final per-file cleanup: remove the "SKELETON" marker; `#print axioms` on `det_certM1_eq`, `atkinLehnerFamily`, `atkinLehnerFamilyH`, `upDatum` standard; record the option of moving the `section Generic` lemmas (`singleₗ_mul`, `mul_singleₗ`, `iotaV_mul_eq_iotaV_mul_toLocal`, `mul_iotaV_eq_iotaV_toLocal_mul`, `iotaV_mul_eq_zero_of_toLocal_eq_zero`, `unitAt_mul`) to `QMF/04_UpiElement.lean` for the user (not done).

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): `23_QuaternionData` warning-free after the pass; `lake build PhD` green (3929 jobs).

### [Q-OPT] `tameScalar_pow_mem` for open tame levels (optional follow-up)
- **Status**: blocked (optional; user decision — needs the topology on `Dfx ℚ D`, not otherwise used by this board)
- **File**: PhD/Main/LWX/23_QuaternionData.lean
- **Depends on**: Q11 (and the fork's topology on `Dfx`)
- **Parallel**: yes (within the dependency order)
- **Type**: proof

- **Depends on (declarations)**: —

**Proof sketch**:
Not needed for any milestone (the input carries `tameScalar_pow_mem`).  If wanted: for an open subgroup `Kt` of the compact
group of tame unit idèles containing the closure of `⟨tameScalar⟩`, the cosets `tameScalar^n Kt` are finitely many (compactness /
finite index of an open subgroup of a compact group), so `tameScalar^a Kt = tameScalar^b Kt` for some `a < b`, i.e.
`tameScalar^(b−a) ∈ Kt`.  Needs: `RightActions` topology on `Dfx` (memory `adelic-lattice-api`), openness of `Kt`, compactness of the
tame scalar's closure.  Record as a separate board if the user wants it.

- **Mathlib/project lemmas needed**: `IsCompact.finite_of_open_cover`‑style / `Subgroup.index` finiteness for open subgroups of compact groups
- **Sources**: decomposition AG-compact.
- **Generality decision**: —
- **Size**: unknown (topology)
- **Progress**: —

### [CLEANUP-ALL-2] `/cleanup-all` before Part M (milestone M3)
- **Status**: done (2026-09-14 beastmode)
- **File**: all board files
- **Depends on**: R1–R10, Q1–Q24 and every cleanup ticket above
- **Parallel**: no
- **Type**: cleanup

Full `/cleanup-all`: `lake build PhD` green, no warning in any board file, `runLinter` on `23_QuaternionData` shows no finding in board files; sorry count = 8 (`25_QuaternionSlopes` only).

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): the whole-board gate was run once, after M6 (see CLEANUP-FINAL); `lake build PhD` green (3929 jobs).

### [M1] `hasUnitBand` for `D/ℚ`
- **Status**: done (2026-09-14 beastmode; axioms clean after S0)
- **File**: PhD/Main/LWX/25_QuaternionSlopes.lean
- **Depends on**: CLEANUP-ALL-2
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/25_QuaternionSlopes.lean:37
/-- **The unit band at every vertex of the spectral halo of `D/ℚ`.** -/
theorem hasUnitBand (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) : HasUnitBand X.upDatum ω n := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`exact hasUnitBand_of_atkinLehnerFamily `(thetaInt p D) ψ X.level X.level_subset_levelM1 X.idx X.uElt (X.atkinLehnerFamily ψ hp2 hψ hζ) X.finite_image_upEltQ X.bijOn_vRepQ X.injective_vRepQ X.c X.hc X.hstab X.dElt X.dElt_mem X.c_mul_vRepQ_inv X.hshape` hp2 hψ hζ ω n` — the family theorem (`23_ConductorSlopes.lean:562`, `include hfin hv hvinj c hc hstab d hd hfact`) is stated for `vRepF … (X.atkinLehnerFamily …)`, which is `vRepQ p D` by `rfl` (`vRepF_atkinLehnerFamily`), and its conclusion `HasUnitBand (UpDatum.ofCerts …) ω n` is `HasUnitBand X.upDatum ω n` by `rfl`; if `exact` fails on the defeq, `rw [show X.upDatum = UpDatum.ofCerts … from rfl]` first, or `convert … using 2`.

- **Mathlib/project lemmas needed**: `hasUnitBand_of_atkinLehnerFamily` (`23_ConductorSlopes:562`), `vRepF_atkinLehnerFamily`
- **Sources**: decomposition M1.
- **Generality decision**: the conclusions are about `X.upDatum : UpDatum p ι`; `K` enters only through the hypotheses.
- **Size**: ~5 lines
- **Progress**: done 2026-09-14 — hasUnitBand_of_atkinLehnerFamily at the D/ℚ data (injective_vRepQ has no X argument); lake build PhD.Main.LWX.«25_QuaternionSlopes» green (3842 jobs); depends on `central := sorry` until S0.

### [M2] `degX_succ`, `degXint_eq` for `D/ℚ`
- **Status**: done (2026-09-14 beastmode; axioms clean after S0)
- **File**: PhD/Main/LWX/25_QuaternionSlopes.lean
- **Depends on**: M1
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/25_QuaternionSlopes.lean:42
/-- **[LWX, Thm 1.3] for `D/ℚ`: `deg X_{k+1,ω} = r_ord(ω⁻¹ω₀^{2k}) + r_ord(ωω₀^{−2k−2})`.** -/
theorem degX_succ [IsAlgClosed K] (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    degX X.upDatum ω (k + 1)
      = ordDim X.upDatum (partnerChar p ω k) + ordDim X.upDatum (targetChar p ω k) := by
  sorry
```
```lean
-- PhD/Main/LWX/25_QuaternionSlopes.lean:49
/-- **[LWX, Thm 1.3] for `D/ℚ`: `deg X_{(n,n+1),ω} = qt − r_ord(ω⁻¹ω₀^{2n}) − r_ord(ωω₀^{−2n})`.** -/
theorem degXint_eq [IsAlgClosed K] (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
    degXint X.upDatum ω n
      = p * Fintype.card ι - ordDim X.upDatum (partnerChar p ω n)
        - ordDim X.upDatum (ω * (teichChar p ^ (2 * n))⁻¹) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`exact degX_succ_of_atkinLehnerFamily `(thetaInt p D) ψ X.level X.level_subset_levelM1 X.idx X.uElt (X.atkinLehnerFamily ψ hp2 hψ hζ) X.finite_image_upEltQ X.bijOn_vRepQ X.injective_vRepQ X.c X.hc X.hstab X.dElt X.dElt_mem X.c_mul_vRepQ_inv X.hshape` X.det_certM1_eq hp2 hψ hζ ω k` and `degXint_of_atkinLehnerFamily … ω n` (`24_DegreePeriodicity.lean:126, 199`; `include … hdet` — `hdet := X.det_certM1_eq` in the position of the section variable `hdet`; check the order with `#check @degX_succ_of_atkinLehnerFamily`).

- **Mathlib/project lemmas needed**: `degX_succ_of_atkinLehnerFamily`, `degXint_of_atkinLehnerFamily` (`24:126, 199`)
- **Sources**: decomposition M2; [LWX, Thm 1.3].
- **Generality decision**: the conclusions are about `X.upDatum : UpDatum p ι`; `K` enters only through the hypotheses.
- **Size**: ~6 lines
- **Progress**: done 2026-09-14 — degX_succ_of_atkinLehnerFamily / degXint_of_atkinLehnerFamily; lake build PhD.Main.LWX.«25_QuaternionSlopes» green (3842 jobs); depends on `central := sorry` until S0.

### [M3] `degXint_pos` for `D/ℚ` **[MILESTONE]**
- **Status**: done (2026-09-14 beastmode; axioms clean after S0)
- **File**: PhD/Main/LWX/25_QuaternionSlopes.lean
- **Depends on**: M2
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/25_QuaternionSlopes.lean:57
/-- **[LWX, Thm 1.3] for `D/ℚ`: `deg X_{(n,n+1),ω} > 0`.** -/
theorem degXint_pos [IsAlgClosed K] (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
    0 < degXint X.upDatum ω n := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`exact degXint_pos_of_atkinLehnerFamily `(thetaInt p D) ψ X.level X.level_subset_levelM1 X.idx X.uElt (X.atkinLehnerFamily ψ hp2 hψ hζ) X.finite_image_upEltQ X.bijOn_vRepQ X.injective_vRepQ X.c X.hc X.hstab X.dElt X.dElt_mem X.c_mul_vRepQ_inv X.hshape` X.det_certM1_eq hp2 hψ hζ ω n` (`24:220`).

- **Mathlib/project lemmas needed**: `degXint_pos_of_atkinLehnerFamily` (`24:220`)
- **Sources**: decomposition M3; [LWX, Thm 1.3].
- **Generality decision**: the conclusions are about `X.upDatum : UpDatum p ι`; `K` enters only through the hypotheses.
- **Size**: ~3 lines
- **Progress**: done 2026-09-14 — degXint_pos_of_atkinLehnerFamily; lake build PhD.Main.LWX.«25_QuaternionSlopes» green (3842 jobs); depends on `central := sorry` until S0.

### [CLEANUP-M1] Cleanup `PhD/Main/LWX/25_QuaternionSlopes.lean`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/25_QuaternionSlopes.lean
- **Depends on**: M1, M2, M3
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused `simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings; `lake build PhD` and `lake exe runLinter` on the module must be clean (grep the linter's output for the file).  Done inline by the main agent.

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): `25_QuaternionSlopes`: header marker, long docstring and call line split; `lake build PhD` green (3929 jobs).

### [M4] `degX_succ_add_period`, `degXint_add_period` for `D/ℚ` ([LWX, Cor 1.4])
- **Status**: done (2026-09-14 beastmode; axioms clean after S0)
- **File**: PhD/Main/LWX/25_QuaternionSlopes.lean
- **Depends on**: M3
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/25_QuaternionSlopes.lean:63
/-- **[LWX, Cor 1.4] for `D/ℚ`**: `deg X_{n,ω}` is periodic modulo `(p−1)/2` in `n ≥ 1`. -/
theorem degX_succ_add_period [IsAlgClosed K] (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    degX X.upDatum ω (k + 1 + (p - 1) / 2) = degX X.upDatum ω (k + 1) := by
  sorry
```
```lean
-- PhD/Main/LWX/25_QuaternionSlopes.lean:69
/-- **[LWX, Cor 1.4] for `D/ℚ`**: `deg X_{(n,n+1),ω}` is periodic modulo `(p−1)/2`. -/
theorem degXint_add_period [IsAlgClosed K] (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
    degXint X.upDatum ω (n + (p - 1) / 2) = degXint X.upDatum ω n := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`exact degX_succ_add_period `(thetaInt p D) ψ X.level X.level_subset_levelM1 X.idx X.uElt (X.atkinLehnerFamily ψ hp2 hψ hζ) X.finite_image_upEltQ X.bijOn_vRepQ X.injective_vRepQ X.c X.hc X.hstab X.dElt X.dElt_mem X.c_mul_vRepQ_inv X.hshape` X.det_certM1_eq hp2 hψ hζ ω k` and `degXint_add_period … ω n` (`24:307, 320`).

- **Mathlib/project lemmas needed**: `degX_succ_add_period`, `degXint_add_period` (`24:307, 320`)
- **Sources**: decomposition M4; [LWX, Cor 1.4].
- **Generality decision**: the conclusions are about `X.upDatum : UpDatum p ι`; `K` enters only through the hypotheses.
- **Size**: ~6 lines
- **Progress**: done 2026-09-14 — _root_.LWX.degX_succ_add_period / degXint_add_period (the local names shadow); lake build PhD.Main.LWX.«25_QuaternionSlopes» green (3842 jobs); depends on `central := sorry` until S0.

### [M5] `unitSlope_discHeckeCharPowerSeries_eq_slopeRatio` for the genuine `U_p` of `D/ℚ` ((1.5.1))
- **Status**: done (2026-09-14 beastmode; axioms clean after S0)
- **File**: PhD/Main/LWX/25_QuaternionSlopes.lean
- **Depends on**: M1
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/25_QuaternionSlopes.lean:75
/-- **[LWX, Thm 1.5 (1.5.1)] for the genuine `U_p` of `D/ℚ`**: at every halo point of the
slope-reading region and every analyticity level, every slope of `det(1 − X·U_p)` on `S^{D,†,m}`
is `v(T₀)` times a `T`-free ratio. -/
theorem unitSlope_discHeckeCharPowerSeries_eq_slopeRatio (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (h : ℕ) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹)
    (hκ : (p : ℝ)⁻¹ ^ 8 < ‖T₀‖ ^ ((p ^ 2 - 1) * Fintype.card ι + 8)) (j : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm
          (discHeckeCharPowerSeries (thetaInt p D) h ψ (haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT)
            X.level X.level_subset_levelM1 (vRepQ p D) (vRepQ_mem_levelM1 p D) X.idx
            X.uElt)).unitSlope j
      = (((-Real.log ‖T₀‖) * slopeRatio X.upDatum ω j : ℝ) : WithBotTop ℝ) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`exact unitSlope_discHeckeCharPowerSeries_eq_slopeRatio_of_atkinLehnerFamily `(thetaInt p D) ψ X.level X.level_subset_levelM1 X.idx X.uElt (X.atkinLehnerFamily ψ hp2 hψ hζ) X.finite_image_upEltQ X.bijOn_vRepQ X.injective_vRepQ X.c X.hc X.hstab X.dElt X.dElt_mem X.c_mul_vRepQ_inv X.hshape` hp2 hψ hζ ω h0 h1 hT hκ j` (`23_ConductorSlopes:576`; `h` is the explicit level argument — place it as the section variable order requires; the statement's `discHeckeCharPowerSeries (thetaInt p D) h ψ … (vRepQ p D) …` is the family theorem's with `vRepF` unfolded by `rfl`).

- **Mathlib/project lemmas needed**: `unitSlope_discHeckeCharPowerSeries_eq_slopeRatio_of_atkinLehnerFamily` (`23:576`)
- **Sources**: decomposition M5; [LWX, Thm 1.5 (1.5.1)].
- **Generality decision**: the conclusions are about `X.upDatum : UpDatum p ι`; `K` enters only through the hypotheses.
- **Size**: ~5 lines
- **Progress**: done 2026-09-14 — unitSlope_discHeckeCharPowerSeries_eq_slopeRatio_of_atkinLehnerFamily; lake build PhD.Main.LWX.«25_QuaternionSlopes» green (3842 jobs); depends on `central := sorry` until S0.

### [CLEANUP-ALL-3] `/cleanup-all` before M6
- **Status**: done (2026-09-14 beastmode)
- **File**: all board files
- **Depends on**: M4, M5, CLEANUP-M1
- **Parallel**: no
- **Type**: cleanup

Full `/cleanup-all` (build green, no warning, linter clean on board files).

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): as CLEANUP-ALL-2; `lake build PhD` green (3929 jobs).

### [M6] `slopeRatio_add_period` for `D/ℚ` ([LWX, Thm 1.5, second half]) **[MILESTONE]**
- **Status**: done (2026-09-14 beastmode; axioms clean after S0)
- **File**: PhD/Main/LWX/25_QuaternionSlopes.lean
- **Depends on**: CLEANUP-ALL-3
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
-- PhD/Main/LWX/25_QuaternionSlopes.lean:89
/-- **[LWX, Thm 1.5, second half] for `D/ℚ`, at the polygon level**: the arithmetic progressions
of period `(p−1)/2·p^h t` and common difference `(p−1)/2·p^{h−1}(p−1)`. -/
theorem slopeRatio_add_period [IsAlgClosed K] (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hζ : IsPrimitiveRoot ζ p) (h : ℕ) (hh : 0 < h) {ζh : K} (hζh : IsPrimitiveRoot ζh (p ^ h))
    (hM : (p ^ 2 - 1) * Fintype.card ι + 8 < 8 * (p ^ (h - 1) * (p - 1)))
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (j : ℕ) :
    slopeRatio X.upDatum ω (j + (p - 1) / 2 * (p ^ h * Fintype.card ι))
      = slopeRatio X.upDatum ω j + (((p - 1) / 2 : ℕ) : ℝ) * ((p ^ (h - 1) * (p - 1) : ℕ) : ℝ) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
`exact slopeRatio_add_period `(thetaInt p D) ψ X.level X.level_subset_levelM1 X.idx X.uElt (X.atkinLehnerFamily ψ hp2 hψ hζ) X.finite_image_upEltQ X.bijOn_vRepQ X.injective_vRepQ X.c X.hc X.hstab X.dElt X.dElt_mem X.c_mul_vRepQ_inv X.hshape` (X.atkinLehnerFamilyH ψ hp2 hψ hζ h hh hζh) X.det_certM1_eq hp2 hψ hh hζ hζh hM ω j` (`23_ConductorSlopes:724`, `include … X hdet`; the level-`h` family `X` and `hdet` are section variables there — check the order with `#check @LWX.slopeRatio_add_period`).

- **Mathlib/project lemmas needed**: `slopeRatio_add_period` (`23:724`), `atkinLehnerFamilyH`
- **Sources**: decomposition M6; [LWX, Thm 1.5] second half (`lwx.txt:2345–2350`).
- **Generality decision**: the conclusions are about `X.upDatum : UpDatum p ι`; `K` enters only through the hypotheses.
- **Size**: ~4 lines
- **Progress**: done 2026-09-14 — _root_.LWX.slopeRatio_add_period with atkinLehnerFamilyH; lake build PhD.Main.LWX.«25_QuaternionSlopes» green (3842 jobs); depends on `central := sorry` until S0.

### [CLEANUP-M-FINAL] Cleanup `PhD/Main/LWX/25_QuaternionSlopes.lean`
- **Status**: done (2026-09-14 beastmode)
- **File**: PhD/Main/LWX/25_QuaternionSlopes.lean
- **Depends on**: M4, M5, M6
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused `simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings; `lake build PhD` and `lake exe runLinter` on the module must be clean (grep the linter's output for the file).  Done inline by the main agent.  Remove the "SKELETON" marker; `#print axioms` on all eight theorems standard.

- **Progress**: done 2026-09-14 — performed in the consolidated post-swap cleanup pass (`scratchpad/cleanup_q.py` + name-based `omit … in` insertion): `25_QuaternionSlopes` warning-free after the pass; `lake build PhD` green (3929 jobs).

### [CLEANUP-FINAL] `/cleanup-all`, the records, and the hand-off
- **Status**: done (2026-09-14 beastmode)
- **File**: all board files; `PhD.lean`; READMEs; `.mathlib-quality/lwx-stepone/FINDINGS.md`
- **Depends on**: every other ticket
- **Parallel**: no
- **Type**: cleanup

Final `/cleanup-all` (linter-clean; `#print axioms` on M3, M6, C16, C21, Q23, Z12 = `[propext, Classical.choice, Quot.sound]`), then:
(1) `PhD.lean`: change the board comment on the three imports to "complete, sorry-free";
(2) `PhD/Main/LWX/README.md`, `PhD/Main/TateFredholm/README.md`: one line each for the three new files (already in the tier tables; add the one-sentence description);
(3) `.mathlib-quality/lwx-stepone/FINDINGS.md`: update the ledger — H1 now holds at every neat tame level (the `Z`-form), `det = p` is proved from normalised representatives, and the `D/ℚ` instantiation is complete granted `QuaternionInput`;
(4) `.mathlib-quality/lwx-stepone/JL-AUDIT.md`: addendum — the identity with `Z` is JL-free; [Miyake 4.6.17] is cited, not used;
(5) record in this board's Summary: the `_hx` slack found, the stale blueprint sentences of `blueprint/src/chapter/LWXSlopes.tex` that now describe `central`/`det = p` as hypotheses (do **not** edit the blueprint without the user's go-ahead), and the two options for the user — moving the `section Generic` lemmas to `QMF/04_UpiElement.lean`, and Q-OPT;
(6) update the memory file for this board and `MEMORY.md`.

- **Progress**: done 2026-09-14 — gates: `lake build PhD` green (3929 jobs), no warning in any board-touched file; `lake exe runLinter PhD.Main.LWX.«25_QuaternionSlopes»`: no finding in any board file (100 findings project-wide, all in files this board did not touch); `#print axioms` = [propext, Classical.choice, Quot.sound] on M1–M6, C16/C21 (`atkinLehnerHypothesis_of_atkinLehnerData(H)`), Q19 (`atkinLehnerFamily(H)`, `upDatum`), R6/R8; blueprint `\lean{}` names: 298/298 resolve on the final build (`#check @name` under `import PhD`, 0 errors).  Records (1)–(6) written: `PhD.lean` comment, READMEs, FINDINGS, JL-AUDIT addendum, Summary execution record, memory.
