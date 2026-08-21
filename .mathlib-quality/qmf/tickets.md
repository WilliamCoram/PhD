# Ticket Board — Quaternionic modular forms of general weight (QMF)

**BOARD PATH: `.mathlib-quality/qmf/`** (tickets/plan/decomposition all here).  The
default `.mathlib-quality/` path is the parallel NewtonPolygon board — NEVER touch it.
Every `/beastmode` run for this project must be invoked with this board path named
explicitly, e.g. `/beastmode board=.mathlib-quality/qmf/`.

Skeleton compiles (sorries only): every proof ticket = "fill the sorries of the named
declarations".  Statements are canonical in the `.lean` files; leaf ids (L…) refer to
`.mathlib-quality/qmf/decomposition.md` (verbatim source quotes + attack logs there).
Build: `lake build PhD.QMF.Quaternionic` (whole chain).
NOTE: another agent builds this repo concurrently — expect waiting on the lake build
lock; never kill the other build.

COORDINATION (2026-08-03 ~14:50): superseded weight-2 FLT reference copies DELETED from
FLTstuff at user request (Basic, InnerProduct, FiniteDimensional, HeckeOperators/* —
our general-weight library replaces them; originals remain in the FLT clone; QMF chain
still green). FLTstuff now contains ONLY ported files. EXTERNAL PORT IN FLIGHT:
RestrictedProduct/{Basic,Module,TopologicalSpace}, Module/ModuleTopology,
Algebra/Module/Submodule/Basic appeared externally (not from this board's workers);
RestrictedProduct/Basic.lean currently has unsolved goals at l.334 — mid-flight work,
DO NOT dispatch competing T016a-c workers or edit those files until they stabilize;
re-check build state at next pickup.

## Summary
- Total: 26 tickets (18 proof/def/port + 6 per-file cleanups + 1 cleanup-all + 1 final)
- Open: 0 | Done: 26 of 26 — **BOARD COMPLETE 2026-08-04**. PROJECT COMPLETE: library sorry-free/warning-free/cleaned, milestone proved, U_ϖ operator built, and the ENTIRE Fujisaki port landed (~95 files) giving `QMF.finite_classSet`. All endpoints axiom-clean. (Historical: ALL 14 proof tickets T001-T014 done 2026-08-03; PhD/QMF/*.lean SORRY-FREE, axioms standard-only, lake build green. Remaining: CLEANUP-1..6, T015 port, T016 port [large], T017 U_ϖ element, CLEANUP-ALL-1, T018 milestone, CLEANUP-FINAL)
- Milestone: T018 (class-set decomposition instantiated for `QMF.Space`)
- Parallel capacity: 4 at start (T001 ∥ T005 ∥ T011 ∥ T012; also T004, T015 anytime)


## AG-B STATUS SNAPSHOT (2026-08-05, end of beastmode run)

**Done**: B01–B05, B07 (+B07a–f), B08, B09, B10, B11, B13 (+B13a, B13b, B13b-1/-2/-3a/-3b/-3c/-3d, B13c),
B14, BC1, BC2, BC3, BC4, BC5 (Level.lean half).

**Sorry inventory of the live chain** (everything else is sorry-free, std axioms):
* `Level.lean` — 1: `hClassNumberOne`, USER-APPROVED PERMANENT for this tranche.
* `Factorisations.lean` — 8: B12, BLOCKED on the 3-adic certificate data.
* `Matrix.lean` — 8: B15/B16/B17, downstream of B12.
* `ClassNumberOneFallback.lean` — 6: UNIMPORTED skeleton; B06/B18 DEFERRED by the user to FLT.

**New files this run**: `PhD/Jacobs/U3/Compose.lean` (analytic substitution `compAn`),
`PhD/Jacobs/BinomialTheorem.lean` (the `p`-adic binomial theorem).
**Also touched**: `PhD/TateFredholm/Matrix.lean` gained `hasSum_matrixCoeff` and
`matrixCoeff_comp` (and had 5 pre-existing deprecation warnings fixed).

**Everything still open is blocked or deferred** — the only unblocking action is supplying
(or authorising a search for) the nine `d(i,t)` / `σ(i,t)` certificates of B12.

**UPDATE (2026-08-05, later same day, orchestrator): B12 UNBLOCKED — the certificate data
is COMPUTED.**  The user authorised the search; it ran as
`PhD/Jacobs/U3/certificate_search.py` (exhaustive over the 96 norm-`3` Hurwitz quaternions
× 3 class indices per pair, exact `ℚ(ν)` arithmetic at `ν ≡ 2695 mod 3¹⁰`, UNIQUE hit per
pair).  Results + provenance: the script docstring and `Factorisations.lean`'s header
section `## The computed tables`.  Headlines: `σ = (2,1,1),(0,2,2),(1,0,0)` — the thesis's
table on the nose; `dTable` = three norm-`3` Hurwitz quaternions up to sign;
`d(0,0) = 3·d_thesis` with `u(0,0)` literally the thesis's printed third factor (p. 26
example); the `ε`-identification closes EXACTLY as `ε_{i,j}(t') = θ₃(c_j⁻¹ · star d · cᵢ)`
(E1-corrected `eps12M2` confirmed; the misprinted value occurs nowhere).  **B15's
determinant-twist audit FIRED** — recorded statement amendment applied, see B15.
`Factorisations.lean` is now a 9-sorry skeleton (8 prior + the new matrix-level
`adjParams_toMatrix_eq_smul_epsTable`); new defs `classDet` + `epsTable` landed
sorry-free.  **B12a/b/c and B15 are workable now**; the live chain builds (3438 jobs).

**FINAL (2026-08-06): THE BOARD IS COMPLETE — 66/68 done, the other 2 (B06, B18) are
user-deferred to FLT.**  The AG-B tranche is mathematically complete AND style-clean:
B12 (nine certificates), B15 (ε-identification + coboundary resolution), B16 (the
unconditional headline `heckeU3_apply_classRep`), B17 (completeness), and the full
cleanup cadence BC1–BC5 / BCALL-B / BCFINAL-B.  All 16 endpoints verified on
[propext, Classical.choice, Quot.sound]; all 220 tracked live modules build with zero
errors and zero warnings across the AG-B surface; the single remaining `sorry` in the
live chain is the contracted `hClassNumberOne` (Level.lean:673).

**UPDATE 3 (2026-08-05, beastmode run, later): B16 AND B17 ARE ALSO DONE — the AG-B
mathematical chain is COMPLETE.**  `Matrix.lean` is sorry-free; the headline
`heckeU3_apply_classRep`, the completeness `eval_classRep_injective`, and the
determinant-twist bridge `charPowerSeries_blockOp_eq_U3MatrixOp` are all proven on
std axioms.  Live-chain sorry inventory: Level.lean 1 (`hClassNumberOne`, approved
permanent).  Remaining board: cleanup cadence only (BC5-Factorisations resume,
BCALL-B, BCFINAL-B) + deferred B06/B18 (FLT).

**UPDATE 2 (2026-08-05, beastmode run): B12 AND B15 ARE DONE.**
`Factorisations.lean` is **SORRY-FREE** (0 sorries; all headline decls
`#print axioms` = std [propext, Classical.choice, Quot.sound]; downstream Matrix.lean
builds, 3439 jobs).  Setting.lean gained two public away-from-3 lemmas
(`valuation_three_eq_one_of_ne`, `inv_three_mem_adicCompletionIntegers`).  Sorry
inventory of the live chain is now: Level.lean 1 (`hClassNumberOne`, approved) +
Matrix.lean 8 (B16/B17).  Remaining board: BC5 (Factorisations half now unblocked),
BCALL-B, B16, B17, BCFINAL-B.

### [T001] FixedPoints.submodule + fixedPointsOfLE API
- **Status**: done (2026-08-03; all 3 decls proved term-mode: add_mem'/zero_mem'/smul_mem' via smul_add/smul_zero/smul_comm, mem_iff = Iff.rfl; lake build clean; cleanup deferred to CLEANUP-1 per board cadence) | **File**: PhD/QMF/HeckeMonoid.lean | **Depends**: none | **Parallel**: yes | **Type**: def API
- Fill: `FixedPoints.submodule` fields (l.45), `FixedPoints.mem_submodule_iff` (l.52),
  `fixedPointsOfLE` fields (l.66).  Leaves L1.x/L2 support.
- Sketch: carrier membership `simp`; `add_mem`: `m•(a+b) = m•a + m•b`; `smul_mem` via
  `smul_comm`.  Template: FLT FLTstuff/HeckeOperators/Abstract.lean:66–70 (group case,
  transfers verbatim to monoid).  Mathlib: `smul_add`, `smul_zero`, `smul_comm`.

### [T002] Double-coset membership lemmas
- **Status**: done (2026-08-03; mul_singleton_mul_subset via rintro on Set-mul + `obtain rfl : g' = g` for the singleton [NB: `-`/`rfl` rintro patterns clobber the section `hg` — name components]; out_mem via `QuotientGroup.mk_out_eq_mul` [name verified at this rev] + `Set.mul_mem_mul`; lake build clean; cleanup deferred to CLEANUP-1) | **File**: PhD/QMF/HeckeMonoid.lean | **Depends**: none | **Parallel**: yes | **Type**: lemma
- Fill: `mul_singleton_mul_subset` (l.85), `out_mem_mul_singleton_mul` (l.90).
- Sketch: (1) `rintro` the product decomposition, `Submonoid.mul_mem` with `hU/hV/hg`.
  (2) `Quotient.out` is in its own class: `QuotientGroup.mk_out_eq_mul`-style — `x.out ∈
  (u*g)V ⊆ U*{g}*V`.  Mathlib: `Set.mem_mul`, `QuotientGroup.mk_out_eq_mul` (name-check
  at rev; FLT Abstract.lean:169 uses it).

### [T003] heckeOperator well-definedness + finsetSum form
- **Status**: done (2026-08-03; helpers subtype_smul_mul [proof-irrelevance defeq + mul_smul], smul_mem_image, smul_out_smul [Quotient.mk_smul_out + mk_out_eq_mul + V-fixedness]; U-fixedness via Fintype.sum_equiv with translation Equiv; map_add/map_smul via finsum_eq_sum_of_fintype + Submodule.coe_add/SetLike.val_smul; eq_finsetSum via Fintype.sum_bijective + Finset.univ_eq_attach; first-compile clean) | **File**: PhD/QMF/HeckeMonoid.lean | **Depends**: T001, T002 | **Type**: theorem (core)
- Fill: `heckeOperator` U-fixedness + `map_add'`/`map_smul'` (l.102 block),
  `heckeOperator_eq_finsetSum` (l.122).  Leaf L2 (source quote in decomposition.md R2).
- Sketch: adapt FLT Abstract.lean `eq_finsum_quotient_out_of_bijOn'` (l.159) +
  `heckeOperator.toFun` (l.174) + `heckeOperator_eq_finsetSum` (l.231) — replace `g • a`
  (group act) by `(⟨x.out, _⟩ : Δ) • a`; `u ∈ U` still invertible so the coset-permuting
  argument is unchanged; V-invariance of `a` handles rep-independence.  Mathlib:
  `finsum_mem_eq_of_bijOn`, `smul_finsum_mem`, `MulAction.injective` (on U-elements via
  Δ-units — u has inverse in Δ since U subgroup ⊆ Δ).

### [T004] Compact-open ⇒ finite coset decomposition
- **Status**: done (2026-08-03; QuotientGroup.discreteTopology hVo [needs import Mathlib.Topology.Algebra.Group.Quotient] + Set.mul_singleton + hUc.image (continuous_mul_const g) + finite_of_discrete; HeckeMonoid.lean SORRY-FREE) | **File**: PhD/QMF/HeckeMonoid.lean | **Depends**: none | **Parallel**: yes | **Type**: theorem
- Fill: `finite_image_doubleCoset_of_isCompact_of_isOpen` (l.135).  Leaf L2.3 (FLT header
  quote in decomposition.md).
- Sketch: image of `U*{g}` in `G⧸V` = image of compact `U·g`; `G⧸V` has open points
  (V open ⇒ `QuotientGroup.mk` open map, cosets open); compact ⊆ union of point-opens ⇒
  finite subcover.  Mathlib: `IsCompact.elim_finite_subcover`, `QuotientGroup.isOpenMap_mk`
  (FLT Finiteness.lean:1091 does the same shape — consult).

### [CLEANUP-1] /cleanup PhD/QMF/HeckeMonoid.lean
- **Status**: done (2026-08-03; Phases 0-6: baseline green; audit punch-list [imports unordered, 3 public docstrings missing, 3 private docstrings]; Phase 3 fixed all file-level items; Phase 4 via ONE lean4:proof-golfer worker (scoped adaptation for context budget — per-decl reports produced, statement-protection rails held, 9 golf edits incl. Submonoid.mul_subset mathlib replacement, haveI×3 → have, 211→198 lines); Phase 5b n/a (no renames; NB shared default-path renames.jsonl must never be used by QMF — qmf-scope any future renames); Phase 6 gates pass (chain build green, 0 sorry/haveI/set_option); Phase 6.5 /simplify DEFERRED to CLEANUP-ALL-1 (will run over whole QMF diff once) — recorded deviation) | **Depends**: T003, T004 | **Type**: cleanup (board path: .mathlib-quality/qmf/)

### [T005] AutomorphicFunction module boilerplate
- **Status**: done (2026-08-03; all instance fields term-mode via ext + pointwise lemmas; left_invt fields need `left_invt'` (coe form) not `left_invt` (toFun form) for rw; build clean) | **File**: PhD/QMF/AutomorphicFunction.lean | **Depends**: none | **Parallel**: yes | **Type**: instances
- Fill: l.66–93 (zero/add left_invt fields, AddCommMonoid, SMul/Module fields).
  Leaf L1.1.
- Sketch: all pointwise; `ext; simp`.  Template: FLTstuff/Basic.lean:155–216 (zero/neg/
  add/addCommGroup) — ours is lighter (no right_invt/central fields).

### [T006] Δ-action instances
- **Status**: done (2026-08-03; mul_smul closed by `simp [mul_smul, mul_assoc]` — handedness law verified by the compiler; left_invt via mul_assoc + left_invt'; build clean; cleanup deferred to CLEANUP-2) | **File**: PhD/QMF/AutomorphicFunction.lean | **Depends**: T005 | **Type**: instances (load-bearing)
- Fill: SMul left_invt (l.110), `DistribMulAction Δ` laws (l.116), `SMulCommClass Δ R`
  (l.122).  Leaf L1.2 — the left-action law computation is recorded in decomposition.md;
  `mul_smul` is THE check that the handedness design is right.
- Sketch: `ext g`; `mul_smul`: both sides `(δ₁δ₂)•φ(g·δ₁·δ₂)` via coefficient `mul_smul`
  + `mul_assoc`; left_invt preserved since `φ(γ·(g·δ)) = φ(g·δ)`.

### [T007] Level API (mem_iff, Loeffler form)
- **Status**: done (2026-08-03; mem_iff via DFunLike.congr_fun + ext + simpa [membership in levelSubmodule unfolds defeq — `h u` works directly]; apply_mul_coe via mem_iff at u⁻¹, (g*u), simpa closes incl. coe_inv/mul_inv_cancel; AutomorphicFunction.lean now SORRY-FREE; build clean) | **File**: PhD/QMF/AutomorphicFunction.lean | **Depends**: T006, T001 | **Type**: lemma
- Fill: `mem_levelSubmodule_iff` (l.135), `apply_mul_coe` (l.141).  Leaf L1.3.
- Sketch: unfold fixedPointsOfLE membership = `∀ u, u•φ = φ`, apply at `g`, `ext`-style;
  for `apply_mul_coe` apply the fixed-point equation at `u⁻¹` and cancel
  `⟨u⁻¹,_⟩ * ⟨u,_⟩ = 1` in Δ (`Subtype.ext`, `one_smul`).

### [CLEANUP-2] /cleanup PhD/QMF/AutomorphicFunction.lean
- **Status**: done (2026-08-03; audit: imports single+ordered, docstring/dividers/set_option/mechanical/≥ all clean; fixed 22 unused-binder linter warnings (named instance-field binders → _); added mem_levelSubmodule_iff docstring; golfer worker SKIPPED — recorded: all proof bodies ≤6 lines, hand-golfed at authoring, audit inline; gates pass: 0 warnings, chain build green; /simplify deferred to CLEANUP-ALL-1) | **Depends**: T007 | **Type**: cleanup

### [T008] stabilizerAt + evalAtReps supporting sorries
- **Status**: done (2026-08-03; mem_iff by simp [MulAut.conj_apply]; evalAtReps membership via conjugation transport [NB: destructure hu FIRST and use `have h1 : ... := mem_iff-instantiation` typed by defeq — raw rw hits motive-not-type-correct]; map_add/map_smul = funext+Subtype.ext rfl) | **File**: PhD/QMF/Decomposition.lean | **Depends**: T007 | **Type**: lemma
- Fill: `mem_stabilizerAt_iff` (l.42), `evalAtReps` value-membership + linearity (l.50).
  Leaves L5.1, L5.2 (argument in decomposition.md R5).
- Sketch: `MulAut.conj_apply` unfold; membership: for `u ∈ Γ_λ`,
  `φ(τu) = φ((τuτ⁻¹)·τ) = φ(τ)` (left_invt) and `= u⁻¹•φ(τ)` (apply_mul_coe) ⇒ fixed.

### [T009] Buzzard's isomorphism (bijective_evalAtReps)
- **Status**: done (2026-08-03; PROVED IN FULL. Injectivity: DoubleCoset.rel_iff + Quotient.eq'' transport + apply_mul_coe. Surjectivity: `choose p hp` decompositions, master well-definedness lemma hval [w = p₂u⁻¹ ∈ stabilizerAt via calc+`group`, c-fixedness, conv_lhs ← hfix, ← mul_smul + Subtype.ext+push_cast+group]; witness assembled by refine ⟨⟨⟨fun g => …⟩,…⟩,…⟩ with each field a hval instance. New simp lemma AutomorphicFunction.coe_mk added for structure-literal beta. Needed import Mathlib.Tactic.Group. Axioms: standard only) | **File**: PhD/QMF/Decomposition.lean | **Depends**: T008 | **Type**: theorem (core)
- Fill: `bijective_evalAtReps` (l.61).  Leaf L5.3; source quote decomposition.md R5.
- Sketch: injective: two forms agreeing at all `σ q` agree everywhere (write
  `g = γ·(σ q)·u` via `hσ` + `DoubleCoset.rel_iff`, transport by invariance/apply_mul_coe).
  Surjective: given `(a_q)`, define `φ(g) := u⁻¹-twist of a_{[g]}` following FLT
  formEquivOfSection (FLTstuff/Basic.lean:747–806, character χ = 1 case); well-defined by
  the `Γ_λ`-invariance of `a_q`.  Mathlib: `DoubleCoset.rel_iff`, `Quotient.exists_rep`.
  If choice-of-decomposition data gets heavy, port FLT σLeft/σRight first (T015).

### [T010] Weight-2 bridge
- **Status**: done (2026-08-03; projection (c ↦ fun q => (c q).1) bijective under htriv [Subtype.ext + ⟨f q, fun v => htriv _ _⟩], composed with T009 via Bijective.comp; defeq closes the factoring; Decomposition.lean SORRY-FREE) | **File**: PhD/QMF/Decomposition.lean | **Depends**: T009 | **Type**: theorem
- Fill: `bijective_eval_of_trivial_smul` (l.68).  Leaf L5.4.
- Sketch: with `htriv`, invariants = ⊤; compose T009 with the equiv
  `↥(fixedPointsOfLE …) ≃ A` (trivial action) — or reprove directly (short).

### [CLEANUP-3] /cleanup PhD/QMF/Decomposition.lean
- **Status**: done (2026-08-03; structure gate was the real item: bijective_evalAtReps body 70→32 lines via extracted private lemmas exists_decomposition + smul_decomp_eq (golfer worker, statements untouched, both reusable for T018); mem_stabilizerAt_iff → Iff.rfl; evalAtReps 17→12; trivial-smul 17→13; file 167→163; gates pass, chain green; /simplify deferred to CLEANUP-ALL-1) | **Depends**: T010 | **Type**: cleanup

### [T011] Σ₀(γ) monoid + detUnits + eta
- **Status**: done (2026-08-03; mul_mem: entries via v.map_add+Fin.sum_univ_two+mul_le_one', c-entry via mul_le_mul'+mul_one/one_mul, a-entry via Valuation.map_add_eq_of_lt_left [Valuation/Basic.lean:307], det via det_mul+mul_ne_zero; one_mem/eta/detUnits by simp [Units.ext_iff, det_fin_two, fin_cases]; Sigma0.lean SORRY-FREE; build clean) | **File**: PhD/QMF/Sigma0.lean | **Depends**: none | **Parallel**: yes | **Type**: def API
- Fill: `Sigma0` mul_mem/one_mem (l.41), `detUnits` hom laws (l.65), `eta` membership
  (l.74).  Leaf L3.1 (ultrametric argument + necessity of `γ < 1` in decomposition.md).
- Sketch: entry formulas `Matrix.mul_apply` (Fin 2 sums, `Fin.sum_univ_two`);
  `v(a₁a₂)=1` (`map_mul`), `v(b₁c₂) ≤ 1·γ < 1` ⇒ max-eq (`Valuation.map_add` +
  ultrametric `v(x+y) = v(x)` when `v(y) < v(x)` — mathlib `Valuation.map_add_of_lt`-
  family, name-check); `det` via `map_mul (Matrix.det)`; eta: `decide`-style entries +
  `Matrix.det_fin_two` = `ϖ ≠ 0`.

### [CLEANUP-4] /cleanup PhD/QMF/Sigma0.lean
- **Status**: done (2026-08-03; audit clean [docstrings/naming/imports/no ≥]; fixed 2 unused-simp-arg warnings (Units.ext_iff in detUnits fields); 0 warnings; proof bodies all ≤22 lines — golfer skipped, recorded; /simplify deferred to CLEANUP-ALL-1) | **Depends**: T011 | **Type**: cleanup

### [T012] matrixSubst API
- **Status**: done (2026-08-03; matrixSubst_X = simp [matrixSubst]; _one via algHom_ext + fin_cases + simp [Matrix.one_apply, Fin.sum_univ_two]; _mul via algHom_ext, simp only [map_sum, map_smul, Matrix.mul_apply, map_mul, Finset.sum_smul, Finset.smul_sum, smul_smul], Finset.sum_comm, per-term mul_comm; build clean) | **File**: PhD/QMF/WeightModule.lean | **Depends**: none | **Parallel**: yes | **Type**: lemma
- Fill: `matrixSubst_X` (l.43), `matrixSubst_one` (l.46), `matrixSubst_mul` (l.50).
  Leaf L3.2 (left-action check in decomposition.md).
- Sketch: `aeval_X`; `algHom_ext` + `simp [Matrix.mul_apply, Finset.smul_sum, smul_smul,
  map_sum]` on `X i` generators; one: `aeval_X_left`-ish.

### [T013] WeightModule action
- **Status**: done (2026-08-03; homogeneity via IsHomogeneous.aeval [Homogeneous.lean:291, note explicit g arg: hP.aeval _ h1] + smul_eq_C_mul + C_mul + isHomogeneous_X; needed new rfl-simp lemmas coe_zero/coe_add/coe_rsmul stated via .1 [type synonym has NO ↑-coe to MvPolynomial — .1 only]; action laws by Subtype.ext + simp; WeightModule.lean SORRY-FREE) | **File**: PhD/QMF/WeightModule.lean | **Depends**: T012 | **Type**: instances
- Fill: homogeneity `matrixSubst_mem_homogeneousSubmodule` (l.54), SMul membership
  (l.90), `DistribMulAction` laws (l.98), `SMulCommClass` (l.104); silence the `ν`
  unused-binder linter (l.76, `nolint`/rename).  Leaves L3.3, L3.4.
- Sketch: homogeneity by monomial induction (`MvPolynomial.IsHomogeneous`, each `X j`-
  image is degree-1 ⇒ products of degree n; check for a ready mathlib lemma first —
  `IsHomogeneous.eval₂`/`aeval` variants); action laws from `matrixSubst_mul` +
  `ν` multiplicativity + `smul_comm`.

### [CLEANUP-5] /cleanup PhD/QMF/WeightModule.lean
- **Status**: done (2026-08-03; fixed all 5 warnings: unused Fin.sum_univ_two simp arg, ν→_ν phantom binder, omit [Algebra K R] on the three coe lemmas; 0 warnings; bodies ≤11 lines, golfer skipped — recorded; /simplify deferred to CLEANUP-ALL-1) | **Depends**: T013 | **Type**: cleanup

### [T014] Global glue (Quaternionic.lean sorries)
- **Status**: done (2026-08-03; evalAlgHom.commutes' = rfl [FiniteAdeleRing algebraMap evaluates componentwise definitionally]; levelMonoidToSigma0 laws = Subtype.ext + simp; SMulCommClass = smul_comm through levelMonoidToSigma0 [compHom defeq]; Quaternionic.lean SORRY-FREE) | **File**: PhD/QMF/Quaternionic.lean | **Depends**: T011, T013 | **Type**: lemma
- Fill: `evalAlgHom.commutes'` (l.62), `levelMonoidToSigma0` map_one/map_mul (l.93),
  `SMulCommClass` (l.117).  Leaves L4.1–L4.3.
- Sketch: commutes': `algebraMap F 𝔸 = diagonal` then `evalRingHom` picks component —
  mathlib FiniteAdeleRing `algebraMap_apply` lemmas; hom laws: `Subtype.ext` +
  `map_one/map_mul` of `toMatrix`; SMulCommClass: unfold `DistribMulAction.compHom`,
  use WeightModule's instance.

### [CLEANUP-6] /cleanup PhD/QMF/Quaternionic.lean
- **Status**: done (2026-08-03; single warning fixed (commutes' r → _); audit clean: docstrings on all public decls, FLT-mock-up comment present, imports ordered, no ≥/set_option; all defs are one-liners — golfer n/a; 0 warnings, chain green; /simplify deferred to CLEANUP-ALL-1) | **Depends**: T014 | **Type**: cleanup

### [T015] PORT: DoubleCoset chain into FLTstuff
- **Status**: done (2026-08-03; 3 files ported: FLTstuff/Mathlib/Topology/Algebra/Group/Quotient.lean [37 l.], FLTstuff/GroupTheoryStuff.lean [382 l.], FLTstuff/Mathlib/GroupTheory/DoubleCoset.lean [369 l.]; module-syntax stripped, statements verbatim, only proofs adapted for v4.33 [root cause: new kabstract motive check rejects defeq-only le_rfl at comap-id — worked around term-level; grind regressions eta-expanded]; zero errors/warnings; unblocks σ-section API + first slice of T016/T017 closure) | **Files**: new PhD/QMF/FLTstuff/Mathlib/… | **Depends**: none | **Parallel**: yes | **Type**: port
- Port (user-authorised) from local FLT clone (`/Users/nkw24xru/Desktop/Lean/FLT`,
  branch samsWork): `FLT/Mathlib/Topology/Algebra/Group/Quotient.lean` →
  `FLT/AutomorphicForm/GroupTheoryStuff.lean` → `FLT/Mathlib/GroupTheory/DoubleCoset.lean`
  (367 l., authors Coram–Buzzard–Yang).  Convert `module`/`public import` headers to
  classic imports, rewrite `FLT.*` → `PhD.QMF.FLTstuff.*`/mathlib, fix v4.32→v4.33
  breakage.  Keep original copyright headers.  Unlocks `DoubleCoset.mk`/`σ` sections →
  optional canonical (section-free) restatement of T009.

### [T016] PORT (large): Fujisaki finiteness chain
- **Status**: done (status line corrected 2026-08-05 during AG-B planning — the Summary and the code already record completion: `QMF.finite_classSet` live in PhD/QMF/Finiteness.lean, whole chain green; the per-ticket line had never been flipped) | **Depends**: none | **Type**: port (follow-on tranche)
- **Route decided by user 2026-08-03: PORT into PhD/QMF/FLTstuff/.  No lake dependencies
  beyond mathlib, ever — all FLT reuse in this repo is by porting.**
- Goal: `NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset`
  (FLT/DivisionAlgebra/Finiteness.lean:1088, Buzzard–**Coram**) available in-repo, giving
  `Finite (DoubleCoset.Quotient ↑(QMF.globalUnits F D) ↑U)` and `∏ → ⊕` upgrades.
- **MEASURED 2026-08-03 (supersedes the original estimate)**: transitive FLT import
  closure of Finiteness.lean = **94 files, ~16,300 lines** (script over the fork's import
  graph). Mathlib-overlap audit (top-16 by size, first-5-decl grep at our rev): the bulk
  has NOT landed upstream — RestrictedProduct.{TopologicalSpace,Equiv} 0/5, AdicValuation
  0/5, HaarChar.Ring 0/5, TensorPi 0/5; only ModuleTopology (4/5), RightActionInstances
  (4/4), RingTheory.DedekindDomain.FiniteAdeleRing (3/5) look partially landed.  Net
  honest size: **~80-85 files / ~13-16k lines across the v4.32→v4.33 bump, incl. the
  full Haar-character measure-theory stack** — a multi-week project-scale port for ONE
  finiteness instance.  USER VISIBILITY: this is 10-15× the sizing under which the
  port-route decision was taken; alternatives if priorities shift: wait for FLT's own
  v4.33 bump then re-diff, or keep `Finite (DoubleCoset.Quotient …)` as a standing
  hypothesis (the library already compiles and the milestone holds without it).
  Sub-tranches (port order, per-file conventions as T015):
  - **T016a** ✅ DONE (2026-08-03: RestrictedProduct/{Basic,Module} — external port +
    3 repairs by this board's session: singleAddMonoidHom rebuilt on mathlib's landed
    `RestrictedProduct.single` API [mulSingle & friends landed upstream — dedupe pattern];
    Submodule.pi membership fixed via DEFEQ ∀-form [rw coe_pi hits coercion mismatch];
    ContinuousLinearEquiv continuity fixed by supplying hφ EXPLICITLY with ascribed
    MapsTo [structure-projection hides the `map` form; proof irrelevance makes it defeq])
  - **T016b** ✅ DONE (TopologicalSpace ported externally, builds; Equiv 652 not yet
    needed by anything ported — pull in when a dependent requires it)
  - **T016c** ✅ DONE (ModuleTopology + Algebra/Module/Submodule/Basic ported externally,
    build green; whole FLTstuff tree: zero sorries, zero PORT-DEFERRED)
  - **T016d** DedekindDomain — PART 1 ✅ DONE (2026-08-03: WithZeroMulInt,
    Mathlib/RingTheory/DedekindDomain/AdicValuation, DedekindDomain/AdicValuation 615,
    IntegralClosure 329 + 4 leaf deps ported; 2 decls found LANDED in our mathlib and
    substituted [finite_quotient_maximalIdeal_pow… → Valued.integer.* in
    Valued.LocallyCompact; intValuation_eq_coe_neg_multiplicity → …exp_neg_multiplicity];
    dominant v4.33 breakage = defeq-strictness in kabstract/simp instance paths, fixed
    term-level; every adaptation marked `-- PORT (v4.33)`; 8 modules build clean).
    PART 2a ✅ DONE (2026-08-03: Completion/BaseChange 825 l. + 7 support deps —
    SemialgHom/Tower/RightActionInstances/Bilinear/Pi partial-ported [PARTIAL PORT
    headers record tranche-needed-only scope], UniformRing/TensorProduct.Basis full;
    ModuleTopology partial port extended additively [documented deviation]; 2 proof
    bodies substituted by landed mathlib decls; all green, statements verbatim).
    PART 2b ✅ DONE (2026-08-03: all 5 tensor-family files + 9 new deps + 3 documented
    partial-port extensions; mapAlongRingHom found landed; per-decl respectTransparency
    false exactly where FLT uses it; WORKER-CAUGHT TRAP: inside structure-literal field
    tactics a failed-Decidable `show` can SILENTLY close goals with sorry — always
    axiom-audit ported files [14 key decls verified standard-only here]).
    **T016d COMPLETE — T017 now UNBLOCKED** (TensorRestrictedProduct + mathlib
    RestrictedProduct.single API available)
  - **T016e** NumberField adeles — PARTIAL (2026-08-03: worker died on session limit
    mid-tranche; its ~24 landed files consolidated + repaired by main session:
    RestrictedProduct/Equiv extension [congr apply_apply via `rfl` finisher; map_add'/
    map_mul' via show-cast + apply_apply simp + componentwise map_mul — e.symm(e i) is
    only PROPOSITIONALLY i, never defeq], TopologicalSpace extension [Countable
    cofinite.sets derived inline via Set.Countable.ofPred_finite.image compl],
    Mathlib/NumberTheory/NumberField/InfiniteAdeleRing ported first-try by main session;
    BorelSpace trio + InfinitePlace basics + ~14 leaf deps all green; whole tree 3501
    jobs, zero sorries.  REMAINING T016e files: NumberField/{InfinitePlace/Extension 289,
    HeightOneSpectrum 32, Completion/{Finite 79, Infinite 223}, InfiniteAdeleRing 178,
    AdeleRing 894, Padics/RestrictedProduct 158} + Mathlib/NumberTheory/NumberField/
    {FiniteAdeleRing 84, AdeleRing 57} + Mathlib/NumberTheory/Padics/* leaves)
  - **T016f** HaarChar stack — SCOPE TRIMMED 2026-08-03 by import-graph analysis:
    HaarMeasure/{Quotient 399, FiniteAdeleRing 205} and Mathlib/MeasureTheory/Group/
    ModularCharacter 564 are NOT in Finiteness.lean's closure — SKIP (~1.2k saved).
    Needed, in dependency order:
    f-1 ✅ DONE (2026-08-03: all 10 files; HaarChar/AddEquiv compiled VERBATIM;
      3 partial ports extended [RestrictedProduct/{Equiv,TopologicalSpace},
      ModuleTopology]; mathlib had absorbed Measure.{IsMulLeft/RightInvariant,
      IsHaarMeasure}.comap, IsFiniteMeasureOnCompacts.comap', Regular.comap', the whole
      TopologicalGroup.IsSES/inducedMeasure layer, and RestrictedProduct.{unitsEquiv,
      coeUnits,mkUnit} → substituted; but NOT mulEquivHaarChar naturality nor
      ringHaarChar (stay FLT-sourced). Only 1 decl of PadicIntegers 154 needed.
      226-decl sorryAx sweep CLEAN, 78 modules build zero-warning.
      NEW PATTERNS: `simp only [<defName>]` no longer reduces Equiv.symm/Homeomorph
      STRUCTURE LITERALS (use explicit `show` restating the coordinate function; pin
      the dite branch type as `dite (α := R i) …` since the motive is still a metavar
      when the else-branch ⟨i,h⟩ : (Jᶜ : Set ι) elaborates). TRAP: BorelSpace/Padic and
      MeasurableSpacePadics each declare their OWN `MeasurableSpace ℚ_[p] := borel _`
      — downstream must import one or the other, NEVER both.)
    f-2a ✅ DONE (2026-08-04: HaarChar/{RealComplex 76, Padic 122, FiniteDimensional
      323 — the last VERBATIM, zero proof edits} + 3 new deps [LinearAlgebra/
      {Transvection 136, Determinant 129}, RingTheory/SimpleRing/TensorProduct 216 —
      over the 150-line guideline but UNAVOIDABLE: mathlib PR 26377 has NOT landed and
      HaarChar/FiniteAdeleRing:642 consumes IsSimpleRing.ringHaarChar_eq_…_mulRight]
      + Bilinear partial port COMPLETED (+LinearEquiv.mul{Left,Right}); REPAIRED the
      previous tranche's PadicIntegers extension which had been left BROKEN on disk
      → next tranche must `lake build` the previously-extended partial ports FIRST,
      not trust header notes. 92-decl sorryAx sweep clean.
      NEW PATTERN: `ℤ_[p]` is a def for a subtype, so terms containing `↑↑(x : ℤ_[p]⁰)`
      are NOT type-correct at implicit transparency — simp/rw silently refuse to
      rewrite anywhere underneath (Lean hints "not type-correct under `implicit`");
      always escape to a term (`exact`, checked at default transparency). Also
      `Units.val_mk0` is no longer @[simp].)
    f-2b ✅ DONE (2026-08-04, main session — worker died on OAuth expiry having
      transcribed FiniteAdeleRing 704/706 with 6 unrepaired proofs; main session
      repaired + finished the tranche):
      * FiniteAdeleRing 704: g_commSq ended on an FLT `simp at f` hack → `exact
        f.apply_symm_apply _`; φLocalKvLinear zero/add cases → `simp only [map_zero,
        smul_zero]` and `simp only [smul_add, map_add] at hx hy ⊢; rw [hx, hy]`;
        3× `LocallyCompactSpace (B ⊗[K] 𝔸)` synthesis failures fixed by RESTORING the
        `LocallyCompactSpace` scoped instance our partial RightActionInstances port had
        OMITTED (+ import of the ported ModuleTopology, no cycle).
      * Padics/HeightOneSpectrum 134 (new dep): landed rename
        intValuation_eq_coe_neg_multiplicity → …exp_neg_multiplicity; `simp [primesEquiv]`
        now unfolds the Equiv to a STRUCTURE LITERAL blocking pow_natGenerator_dvd_iff →
        `simp [show ((primesEquiv v : Nat.Primes) : ℕ) = natGenerator v from rfl, …]`.
      * RightActionInstances: RESTORED the whole omitted baseChange block (LinearMap.
        baseChange{,_comp}, LinearEquiv.baseChange, AlgebraMap.baseChange,
        Algebra.TensorProduct.basis).
      * AdeleRing 252: MulEquiv.restrictedProductUnits → mathlib
        `RestrictedProduct.unitsEquiv` — NB mathlib takes R EXPLICIT (`unitsEquiv _ x p`);
        the substitution changed the unfolded shape, needing
        `RestrictedProduct.{coeUnits,coeMonoidHom}, MulEquiv.piUnits, MonoidHom.comp_apply,
        MonoidHom.coe_mk, OneHom.coe_mk` in the simp set to get back to a rewritable form.
      **LESSON (recorded for T016g): partial ports that silently omit instances/blocks are
      the dominant failure mode of this port — when an instance/constant is 'unknown',
      check our own partial port BEFORE assuming mathlib drift.**
    → **T016f COMPLETE**; whole FLTstuff tree 3571 jobs green, zero sorries.
  - **T016g** ✅ DONE (2026-08-04) — **T016 COMPLETE, BOARD COMPLETE**:
    DivisionAlgebra/Finiteness.lean 1127 l. ported (statements verbatim; only 2 marked
    proof bodies changed) + 3 new deps (Topology/{HomToDiscrete 123, Polish 77},
    LinearAlgebra/TensorProduct/Basis 41) + ModuleTopology extended once more
    (Module.Finite.secondCountabletopology). Many decls found LANDED in our mathlib
    (SimpleRing.Principal, the DoubleCoset finite-cover lemmas, IsSES.ofClosedAddSubgroup,
    addEquivAddHaarChar_pos, isModuleTopologyOfFiniteDimensional). AutomorphicForm/Stuff
    and further HaarChar deps turned out NOT to be in the closure. 186-decl sorryAx
    sweep clean; `finiteDoubleCoset` axioms standard-only.
    **WIRED**: new `PhD/QMF/Finiteness.lean` — `QMF.finite_classSet` states Fujisaki for
    `QMF.globalUnits F D` (FLT's `incl₁` is definitionally our `unitsIncl`; needs
    `open scoped TensorProduct.RightActions` for the Dfx topology instance).
    → Buzzard's decomposition is now a FINITE product.

### [T017] Standard `U_ϖ` element and operator
- **Status**: done (2026-08-03; PhD/QMF/UpiElement.lean 243 l., zero warnings, std axioms: `etaAdelic : Dfx F D` built as the unit `1 + ι_v(e−1)` [ι_v = lTensor of the F-linearized RestrictedProduct single; explicit inverse via e·e⁻¹−1=0; iotaV_mul by double TensorProduct.induction; noncomm_ring for the expansion], `toMatrix_etaAdelic` = Sigma0.eta matrix, `etaAdelic_mem_levelMonoid`, and **`QMF.heckeUpi`** — the standard U_ϖ operator [Buzzard §9 p.69]. NB: private singleHom retype needed — FiniteAdeleRing/RestrictedProduct defeq types trip v4.33 rw. Unblocks the jacobs/ board's AG-B) | **File**: PhD/QMF/Quaternionic.lean | **Depends**: T014, T015+tensor-port | **Type**: def + lemma
- Construct `η ∈ Dfx F D` whose `v`-component is `Sigma0.eta` and which is `1` at other
  places: lift via `RigidificationAt.equiv.symm` + `RestrictedProduct.mulSingle`-style
  units (mathlib name-check; FLT has `RestrictedProduct.mulSingleHom` — port via T015
  chain if absent).  Prove `η ∈ levelMonoid` (its matrix is `eta` ∈ Σ₀); define
  `QMF.heckeUpi := heckeOperator … hη …` with finiteness from T004 once a topology on
  `Dfx` is fixed (if topology is not yet available in-repo, state with the finiteness
  hypothesis explicit — do NOT develop adelic topology inside this ticket).

### [CLEANUP-ALL-1] /cleanup-all over PhD/QMF (board .mathlib-quality/qmf/)
- **Status**: done (2026-08-03; /simplify holistic pass: 4 parallel reviewers [reuse/simplification/efficiency/altitude]. FIXED: dead FixedPoints.submodule section deleted from HeckeMonoid [flagged by ALL FOUR — also a name clash with FLTstuff/HeckeOperators/Abstract.lean that would break T016 imports]; unused DoubleCoset import moved HeckeMonoid→Decomposition; Sigma0 imports lightened [ValuedField→ValuationTopology, NonsingularInverse→Determinant.Basic]; chain green. SKIPPED with notes: (i) inclHom U→*Δ architecture refactor [altitude #1 — the RIGHT design, 12+ sites incl. public sigs; needs its own /develop pass — Quaternionic.levelMonoidToSigma0 already models it]; (ii) fixedPointsOfLE_eq_top under trivial action as general lemma; (iii) publicize subtype_smul_mul to dedupe Decomposition ritual ×2; (iv) finsum→Finset.sum heckeOperator redesign [API change]; (v) simp-only squeezes in WeightModule instances; (vi) eta↔levelMonoid membership bridge [→ T017 scope]; (vii) QMF.Space-phrased milestone restatement) | **Depends**: CLEANUP-1..6, T015, T017

### [T018] MILESTONE: decomposition of `QMF.Space`
- **Status**: done (2026-08-03; `QMF.bijective_space_evalAtReps` added to Quaternionic.lean — one-line instantiation of T009's bijective_evalAtReps at G = Dfx, Γ = globalUnits, Δ = levelMonoid, A = WeightModule; docstring records the Fujisaki/T016 ⊕-upgrade path; first-compile green. NOTE: dep on CLEANUP-ALL-1 was a cadence gate, reordered — math deps T009/T014 were met; CLEANUP-ALL-1 (+deferred /simplify) still runs before CLEANUP-FINAL) | **File**: PhD/QMF/Quaternionic.lean (new section) | **Depends**: T009, T014, CLEANUP-ALL-1 | **Type**: theorem
- Statement (add to file): instantiate `bijective_evalAtReps` for
  `QMF.Space F D v γ hγ n ν U hU`:
  `Space ≃ ∏ q : Dˣ\Dfx/U, (WeightModule R n ν)^{Γ_q}` (as the Bijective statement, and
  a `Finite`-conditional `⊕`-corollary noting discharge by T016/AG2).
  Source: Buzzard §9 p. 69 displayed iso + §9 p. 70 Definition (quotes in
  decomposition.md R4/R5).
- Sketch: apply T009 with `G := Dfx`, `Γ := globalUnits`, `Δ := levelMonoid`,
  `A := WeightModule R n ν`; the only new content is assembling instances.

### [CLEANUP-FINAL] /cleanup-all, final pass (board .mathlib-quality/qmf/)
- **Status**: done (2026-08-03; final sweep: whole QMF chain + ported FLTstuff DoubleCoset chain build with ZERO warnings and zero errors; zero sorries anywhere; milestone endpoint QMF.bijective_space_evalAtReps depends only on [propext, Classical.choice, Quot.sound]) | **Depends**: T018

---

# AG-B tranche tickets (opened 2026-08-05; the `U₃` identification)

**Read first**: `decomposition.md` "AG-B tranche" (prose proofs, verbatim source quotes,
attack logs, the LEFT-vs-right convention seam — BINDING).  Skeleton canonical: every
proof ticket = "fill the named sorries"; `lake build PhD.Jacobs.U3.Matrix` green at
opening (3594 jobs).  Code: `PhD/Jacobs/U3/` + `PhD/QMF/HeckeMatrix.lean` (user
decision: Jacobs-paper material lives under `PhD/Jacobs/`).  Board: this file — NEVER
the default board, NEVER `.mathlib-quality/jacobs/` (paused AG-W beastmode owns that).
Thesis PDF: `~/Desktop/Papers/Jacobs - Slopes of Compact Hecke Operators.pdf`; verified
text extraction (SIGNS DROPPED — derive, never transcribe): planning scratchpad.
`ν₃`-congruence facts route through `ν₃_near` (mod 3¹⁰), NOT ad-hoc Hensel reruns.

## Summary (AG-B)
- Proof tickets: B01–B17 (+3 certificate columns inside B12) | Cleanups: BC1–BC6 +
  BCALL + BCFINAL per cadence | Milestones: B16 (headline), B17 (completeness)
- Parallel at start: B01 ∥ B02 ∥ B04 ∥ B07 ∥ B10 (5 workers)
- `HClassNumberOne` gating: B17 consumes it as an explicit hypothesis.  B16 (headline)
  is UNCONDITIONAL — do not let workers "wait for CN1".
- **CN1 DEFERRAL + INTERFACE FACTORING (user decisions 2026-08-05)**: FLT states this
  lemma (`FLT/Data/HurwitzRatHat.lean: completed_units`) and is expected to cover it
  upstream — we are NOT required to fill it.  The dependency is factored to a SINGLE
  interface sorry: `Jacobs.U3.hClassNumberOne` (Level.lean, full contract in its
  docstring — pointer, port obligations, ẐHat-vs-live-framework note).  The in-repo
  fallback chain (Euclidean → principal → dictionary) was MOVED OFF the live chain to
  `PhD/Jacobs/U3/ClassNumberOneFallback.lean` (imported by nothing; built standalone).
  B06 and B18 are DEFERRED and point there: do not pick them up unless the user asks;
  when FLT lands its proof, port it into the interface (re-audit the formulation seam
  then).  Consumers: hypothesis form (axiom-clean, gradable) + primed convenience
  corollaries consuming the interface (sorry-tainted, one source) — e.g.
  `eval_classRep_injective'` (B17).

### [B01] K₃ instance pack
- **Status**: done (2026-08-05, beastmode; chain green 3595 jobs. DISCOVERIES: IsUltrametricDist + CompleteSpace are ALREADY mathlib instances at K₃ (Valued.toNormedField's ultrametric instance + completion) — sorried skeleton instances DELETED in favour of `example : … := inferInstance` checks (removing a shadow-instance diamond risk); CharZero via `charZero_of_injective_algebraMap`; NontriviallyNormedField = mathlib NormedField + non_trivial ⟨3⁻¹⟩. norm_three_lt_one: `Valued.toNormedField.norm_lt_one_iff` + pass to UniformSpace.Completion through `adicCompletion.equiv` (map_ofNat) + `Valued.valuedCompletion_apply` + `valuation_lt_one_iff_mem`; helpers natGenerator_v₃ (primesEquiv.apply_symm_apply + congrArg — NO unfold, whnf-timeout trap) + three_mem_v₃ (natGenerator_dvd_iff + comap_map_of_bijective). PITFALL RECORDED: `Algebra (𝓞 ℚ) K₃` has NON-DEFEQ instance paths once PhD.QMF.Quaternionic is imported — avoid any statement mentioning algebraMap 𝓞ℚ→K₃; route through the unambiguous `adicCompletion.equiv`/`coeRingHom` chain instead (B02/B03 workers take note). Cleanup deferred to BC1 per board cadence) | **File**: PhD/Jacobs/U3/Setting.lean | **Depends**: none |
  **Parallel**: yes | **Type**: instances
- Fill: `IsUltrametricDist K₃`, `CompleteSpace K₃`, `CharZero K₃`,
  `NontriviallyNormedField K₃` (non_trivial field ONLY — parent structure already wired
  to mathlib's NormedField; do NOT restate the norm), `norm_three_lt_one`.
- Sketch (decomposition L7.1): mathlib `Mathlib.NumberTheory.Padics.HeightOneSpectrum`
  has `v.adicCompletion ℚ ≃A[ℚ] ℚ_[primesEquiv v]`; transport `ℚ_[3]`'s instances, or
  prove directly from `Valued`-nonarchimedean (`Valued.toNormedField` norm law).
  `norm_three_lt_one`: valuation of 3 at v₃ is `< 1` (uniformiser); or transport
  `Padic.norm_p`.  Est: source trivial; ~80 LOC Lean.

### [B02] ν₃: the located square root of −2
- **Status**: done (2026-08-05, beastmode; ν₃/sq_ν₃/ν₃_near proven, axioms standard, chain 3596 green. DESIGN CHANGE (recorded): the planned integral-transport route (padicEquiv_bijOn + PadicInt.subring) hit repeated non-defeq instance-path seams (ContinuousAlgEquiv type ascription vs K₃-abbrev; Fact-prime at `primesEquiv v₃`-cast types) — replaced by the SIGN-NORMALISED design: transport ANY hensel root through `Padic.adicCompletionEquiv` (ring structure only — map_pow/map_ofNat), then `ν₃ := if ‖ν′−1‖ < 1 then ν′ else −ν′`; both `norm_ν₃_sub_one_le : ‖ν₃−1‖ ≤ ‖3‖` and `ν₃_near` (exact value ‖3‖¹¹ ≥ strength ‖3‖¹⁰) follow from pure ultrametric factorisations ((x−1)(x+1) = −3 resp. (ν−2695)(ν+2695) = −3¹¹·41) — matching thesis sign since 508 ≡ 1 mod 3 (docstring). Hensel side: hensels_lemma at F = X²+2, a = 1 fully proven (hder/hnorm numeral bookkeeping; PadicInt.norm_int_lt_one_iff_dvd for ‖2‖ = 1). U3Data now imported by Setting (norm_ofNat_eq_one, norm_sub_le_max', norm_eq_of_sub_lt reused). WORKER NOTE for B03+: same instance-path seams will appear — prefer ring-structure-only transports and `Jacobs.*` ultrametric helpers over norm-compat lemmas on the equiv. Cleanup deferred to BC1) | **File**: PhD/Jacobs/U3/Setting.lean | **Depends**: B01 |
  **Parallel**: yes (after B01) | **Type**: def + lemmas
- Fill: `ν₃`, `sq_ν₃`, `ν₃_near`.
- Sketch (L7.2): `hensels_lemma` (mathlib, ℤ_[3]) at `F = X² + 2`, `a = 1`
  (‖F 1‖ = ‖3‖ < 1 = ‖F′ 1‖²) → root `z ≡ 1 mod 3`; transport along the comparison
  equiv; location: ultrametric factorisation `(ν−2695)(ν+2695) = −3¹¹·41` verbatim from
  `PhD/Jacobs/Instance.lean: exists_sqrt_neg_two_near` (2695 ≡ 1 mod 3 pins the sign —
  NO precision-Hensel).  Est: ~60 LOC (Instance.lean precedent 40).

### [B03] θ₃ and the RigidificationAt instance
- **Status**: done (2026-08-05, beastmode; `theta` + the `RigidificationAt ℚ D v₃`
  instance both real and axiom-clean; `Setting.lean` sorry-free; chain 3597 green.
  Sub-ticket B03a carries the bijectivity route and the five recorded traps.  The
  instance-path alignment predicted at planning time DID occur and is resolved by an
  explicit `Subsingleton.elim` transport — see B03a's SEAM note.  Cleanup deferred to
  BC1 per board cadence) | **File**: PhD/Jacobs/U3/Setting.lean | **Depends**: B02 |
  **Type**: def + instance
- Fill: `theta`, the `RigidificationAt ℚ D v₃` instance (alignment note at the sorry).
- Sketch (L7.3): define on the ℚ-basis `1,i,j,k` by [Jac p. 14]'s display (quote in
  decomposition; ξ = 1); AlgEquiv via `Algebra.TensorProduct.lift` + explicit inverse
  `th1` [§B.1 p. 44: `th1(m) = [(m₁₁+m₂₂)/2, ((m₂₂−m₁₁)ν − (m₁₂+m₂₁))/(2(ν²+1))…]` —
  re-derive, extraction unreliable]; structure constants: `θ(i)² = θ(j)² = −1`,
  `θ(i)θ(j) = θ(k)` (hand-verified planning).  v4.33 seam: align instance paths
  (board precedent: term-level `exact`, no `rw` across defeq).  Source ~10 lines;
  est ~150 LOC.

### [B03a] Bijectivity of `thetaTensorHom` (sub-ticket of B03)
- **Status**: done (2026-08-05, beastmode; `Setting.lean` SORRY-FREE, `theta` axiom-clean
  [propext, Classical.choice, Quot.sound], chain 3597 green) | **File**:
  PhD/Jacobs/U3/Setting.lean | **Depends**: B02 | **Parent**: B03 | **Type**: theorem
- ROUTE (supersedes the planned explicit-inverse + basis-expansion sketch): rebuilt over
  K₃ — `thetaK : K₃ ⊗[ℚ] D →ₐ[K₃] M₂(K₃)` via `Algebra.TensorProduct.lift`, so
  `Algebra.TensorProduct.basis` applies directly; `tensorBasis`, `finrank_tensor = 4`,
  `finrank_matrix₂ = 4`.  Then `thetaK_surjective` by Jacobs's explicit `th1` preimage
  (re-derived; only `ν² = −2` used), and **injectivity for free** from
  `LinearMap.injective_iff_surjective_of_finrank_eq_finrank` — it is an *iff*, so `.mpr`
  gives injectivity from surjectivity and the whole planned basis-expansion argument is
  deleted.  `theta` = `Algebra.TensorProduct.comm` ∘ `AlgEquiv.ofBijective` ∘
  `restrictScalars ℚ`.
- **TRAPS RECORDED (all cost real time — read before any similar proof):**
  1. `ext` is TOO AGGRESSIVE here: it applies `Matrix.ext` *and then* `adicCompletion.ext`,
     pushing entry goals through the structure-eta into `(…).toCompletion = (…).toCompletion`
     where `hν` (a K₃-level hypothesis) no longer matches and `ring`/`linear_combination`
     both fail.  Use `refine Matrix.ext fun r c => ?_` to stop at K₃ level.  Same trap
     appears in `thetaBasis.i_mul_i`, where the fix was hoisting K₃-level `have`s above
     the `simp`.
  2. `<;> first | t₁ | t₂ | …` spanning multiple lines mis-parses; write the `first` block
     on ONE line, or use per-goal `·` bullets.
  3. Anonymous quaternion constructors elaborate at the *unfolded* `ℍ[ℚ,-1,-1]`, which
     `rw` will not match against the `D` abbrev — hence the named `qi`/`qj`/`qk`.
  4. `Algebra.TensorProduct.lift_tmul` is `rfl`: close tmul-evaluation lemmas with
     `show` + `Algebra.smul_def`, not `rw`/`simp` (the `Commute` proof-term blocks them).
  5. NAMES at this rev: `Module.Basis` (not `Basis`), `QuaternionAlgebra.basisOneIJK`
     (not `Quaternion.`), `Module.finrank_matrix`, and
     `Mathlib.Algebra.QuaternionBasis` is a SEPARATE import.
- **SEAM RESOLVED (binding for every later ticket)**: `Algebra ℚ K₃` has TWO instance
  paths in scope (`DivisionRing.toRatAlgebra` vs
  `HeightOneSpectrum.instAlgebraAdicCompletion`); equal by `algebra_rat_subsingleton` but
  NOT syntactically, so any statement mixing `D ⊗[ℚ] K₃` with the QMF framework needs the
  explicit `Subsingleton.elim` transport — pattern in the `RigidificationAt` instance.

### [B04] Σ₁(9)
- **Status**: done (2026-08-05, beastmode; first-compile: γ₉_lt_one by `decide`; Sigma1 mul_mem via the planned expansion `(ab)₀₀−1 = (a₀₀−1)b₀₀ + (b₀₀−1) + a₀₁b₁₀` + two map_add/max_le splits + Sigma0.entry_le_one/v_c_le; mem_sigma1_iff = Iff.rfl; chain 3595 green. Cleanup deferred to BC1) | **File**: PhD/Jacobs/U3/Setting.lean | **Depends**: none |
  **Parallel**: yes | **Type**: def + lemmas
- Fill: `γ₉_lt_one`, `Sigma1`, `sigma1_le_sigma0`, `mem_sigma1_iff`.
- Sketch (L5.1): carrier = Σ₀-conditions ∧ `v(g₀₀ − 1) ≤ γ₉`; `mul_mem`: mirror
  `Sigma0.mul_mem'` + the 1-unit congruence (`a″−1 = (a−1)a′ + a(a′−1) + bc′`-shape with
  `v(bc′) ≤ γ₉`); `γ₉_lt_one`: `ℤᵐ⁰` coe (`ofAdd (−2) < ofAdd 0`).  Est ~90 LOC.

### [B05] Hurwitz order: ring + norm + the 24 units
- **Status**: done (2026-08-05, beastmode/autonomous-loop; **`Hurwitz.lean` SORRY-FREE**,
  endpoints axiom-clean [propext, Classical.choice, Quot.sound], chain 3597 green) |
  **File**: PhD/Jacobs/U3/Hurwitz.lean | **Depends**: none | **Type**: def + lemmas
- PROVEN: the whole `Subring` (incl. `mul_mem'`), `exists_norm_eq_natCast`, `star_mem`,
  `hnorm` + `hnorm_coe`/`hnorm_mul`/`hnorm_eq_zero_iff`, `isUnit_iff_hnorm_eq_one`,
  `hnorm_eq_one_iff`, `hnorm_eq_one_iff_coords`, `abs_le_two_of_hnorm_eq_one`,
  `ofTuple` (+ projections, `ofTuple_injective`, `ofTuple_mem_of_parity`), `unitTuples`,
  `card_unitTuples`, `card_units_hurwitzOrder = 24`.
- **ENCODING** (supersedes the planned two-branch carrier): `IsHurwitz x` = single-branch
  halved-coordinate parity form (`∃ A B C D : ℤ`, `x.re = A/2`, …, all `% 2` equal),
  stated via coordinate PROJECTIONS, never via anonymous-constructor literals.
- **TRAP (generalises Setting.lean's trap 3)**: `Quaternion` is a `def`, NOT an `abbrev`,
  so a literal `⟨a,b,c,d⟩` at expected type `ℍ[ℚ]` elaborates at
  `QuaternionAlgebra ℚ (-1) 0 (-1)` carrying THAT type's ring instances — helper
  `mk_add_mk`/`mk_mul_mk` lemmas fail to `rw` at either type and `simp` will not reduce
  projections of literal sums.  Projections (`re_add`, `re_mul`, … `@[simp]`) sidestep it.
  Also: coordinate projections are `QuaternionAlgebra.re`/`imI`/… — there is no
  `Quaternion.re`.
- **KEY TECHNIQUE (reusable)**: for parity obligations that are nonlinear in the raw
  coordinates, supply `have h : E₁ - E₂ = 2 * (…) := by ring` and then `omega`.  The
  difference is visibly even, which makes the `% 2` goal LINEAR; `omega` cannot do it
  without `h`.  This closed `mul_mem'` with NO case split (the planned 4-case split on
  shared parity turned out unnecessary).
- **INDEPENDENT CHECK OF THE SOURCE**: `card_unitTuples` is proved by
  `simp [unitTuples]; decide` from the norm equation `A²+B²+C²+D² = 4` alone — it
  confirms [Jac p. 22]'s "24 units" (8 all-even = `±1, ±i, ±j, ±k`; 16 all-odd =
  `(±1±i±j±k)/2`) without relying on the thesis's list.  NB `unitTuples` must be
  `noncomputable` (`Finset.Icc` on `ℤ` goes through a noncomputable order instance);
  `decide` still discharges the card after `simp`.
- Cleanup deferred to BC2 per board cadence.

### [BC1] /cleanup PhD/Jacobs/U3/Setting.lean
- **Status**: done (2026-08-05, beastmode; file 437→424 lines, **0 errors / 0 warnings**,
  all lines ≤100 chars, chain 3596 green).  Phase 2 punch-list: A.1 copyright ok, A.2
  module docstring ok, A.5 length ok (<1000), A.6 no `set_option`, A.7 no `λ`/`$`/`push_neg`.
  FIXES: (i) A.4 — stripped all 5 `/-! ##` subsection dividers (project convention confirmed
  empirically: the already-cleaned `HeckeMonoid`/`AutomorphicFunction`/`Decomposition` carry
  ZERO); the one divider with prose was demoted to a plain `/- … -/` block.  (ii) Collapsed
  the four 6-way `first | linear_combination …` blocks in `thetaK_surjective` into one
  deterministic `linear_combination` per entry — this was the source of 11 `tactic does
  nothing` / `never executed` warnings; correct coefficients are `(m11−m00)/2`,
  `(−m01−m10)/2`, `(−m01−m10)/2`, `(m00−m11)/2`.  (iii) Removed 6 unused simp args
  (`Polynomial.aeval_C`, `Matrix.one_apply` ×2, `Matrix.head_cons`, `Matrix.head_fin_const`,
  `Matrix.head_val'`, `zero_mul`).  (iv) `zero_le'` → `zero_le` (deprecated).  (v) Rewrapped
  an over-long comment line.  NOTE for future workers: a `first`-block that only *needs* one
  branch per goal is a lint smell — resolve the goals individually once they are known. | **Depends**: B01, B02, B03, B04 | **Type**: cleanup (board
  .mathlib-quality/qmf/)

### [B06] Euclidean division and principal right ideals
- **SUPERSEDED by board hurwitz-cn1 (executed 2026-08-10)**: proven in
  `PhD/JacobsSlash/CN1/2_Euclidean.lean` (right-handed `a = b * q + r`, correcting
  this skeleton's `a = q * b + r`).  Entry below kept as written.
- **Status**: DEFERRED (user 2026-08-05: FLT will cover `completed_units`; only needed
  for B18 — do not work unless asked) | **File**:
  PhD/Jacobs/U3/ClassNumberOneFallback.lean (moved off the live chain 2026-08-05) |
  **Depends**: B05 | **Type**: theorem (core of B-CN1, part 1)
- Fill: `exists_div_rem`, `right_ideal_principal`.
- Sketch (L6.3/L6.4): `q` = the nearer of round-to-ℤ⁴ / round-to-(ℤ+½)⁴ of `a·b⁻¹`
  (STRICTNESS needs the half-lattice — decomposition attack note); then
  `N(a−qb) = N(ab⁻¹−q)N(b) ≤ ½N(b) < N(b)`.  Principality: minimal-norm generator +
  division.  [Voight 11.3.1, 11.1.8.]  Est ~200 LOC.

### [B07] Local orders and U₀(1)/U₁(9) — DONE
- **Status**: DONE (2026-08-05, beastmode; every fill PROVEN, chain green).
  DONE: `localOrder` (+ new generator lemmas `includeLeft_mem_localOrder`,
  `includeRight_mem_localOrder`), `U0`, `U1_9`, `U1_9_le_U0`, `U1_9_subset_levelMonoid`,
  `toMatrix_mem_sigma1_of_mem_U1_9`.
  **DESIGN WIN (supersedes the sketch's "component-wise via FLTstuff BaseChange API")**:
  `U0` is defined with the ALREADY-AVAILABLE `QMF.toLocal ℚ D w` — no BaseChange /
  restricted-product plumbing needed at all.  Carrier is
  `{g | ∀ w, toLocal w g ∈ localOrder w ∧ toLocal w g⁻¹ ∈ localOrder w}`; carrying the
  inverse condition explicitly makes `inv_mem'` a swap and `mul_mem'` two `Subring.mul_mem`s.
  Same trick for `U1_9` (Σ₁ conditions on `g` AND `g⁻¹`), which makes it a subgroup even
  though `Sigma1` is only a submonoid — and then `U1_9_le_U0` / `_subset_levelMonoid` /
  `toMatrix_mem_sigma1_of_mem_U1_9` are one-liners off the definition.
  `localOrder` is a `Subring.closure` of (Hurwitz image ∪ local integers), so membership
  goes through `subset_closure` / `closure_induction`.
  **B07 COMPLETE 2026-08-05**: Level.lean is sorry-free apart from the permanent,
  user-approved `hClassNumberOne` (FLT `completed_units`).  All new declarations on
  [propext, Classical.choice, Quot.sound].
  `theta_localOrder` DONE 2026-08-05 via B07a (⊆, `Subring.closure_le`) and B07b (⊇, via
  Jacobs's `th1`).  REMAINING: `unitsIncl_mem_U0_iff` only.
  KEY INFRASTRUCTURE FIX (2026-08-05): `Algebra ℚ K₃` had two non-defeq instance paths
  (`DivisionRing.toRatAlgebra` vs `HeightOneSpectrum.instAlgebraAdicCompletion`); the old
  `Subsingleton.elim` transport in the `RigidificationAt` instance made θ₃ *uncomputable*
  in practice.  Replaced by `attribute [local instance 2000]
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion` in Setting.lean AND
  Level.lean, so the instance is now literally `⟨theta ν₃ sq_ν₃⟩`.  New public API in
  Setting.lean: `theta_tmul_one`, `theta_one_tmul`, `norm_two_eq_one`, `norm_ν₃`,
  `norm_algebraMap_half_le_one`, and `qi/qj/qk` made public with projection simp lemmas.
  EVERY downstream certificate (Factorisations.lean) depends on this fix.
  OLD SPLIT NOTE:
  the parent then assembles the two inclusions.  Also still open:
  `unitsIncl_mem_U0_iff` (everywhere-local integrality ⟹ global, a denominator argument
  on the Hurwitz ℤ-basis). | **File**: PhD/Jacobs/U3/Level.lean | **Depends**: B03 (for the v₃
  statements), B05 | **Parallel**: yes after deps | **Type**: def + lemmas
- Fill: `localOrder`, `theta_localOrder`, `U0`, `U1_9`, `U1_9_le_U0`,
  `U1_9_subset_levelMonoid`, `toMatrix_mem_sigma1_of_mem_U1_9`, `unitsIncl_mem_U0_iff`.
- Sketch (L1.2 + Level defs): `localOrder` = 𝓞_w-span of the Hurwitz ℤ-basis image;
  `U0` component-wise via the restricted-product structure (FLTstuff BaseChange API);
  `theta_localOrder`: θ₃ integral both ways (2 unit at 3; th1 has /2 only);
  `unitsIncl_mem_U0_iff`: everywhere-local integrality ⟹ global (denominator argument
  on the ℤ-basis).  Est ~300 LOC; the seam file of B-GLOB.

### [B07a] θ₃ maps the local order INTO the integral matrices (sub-ticket of B07) — DONE
- **Status**: DONE (2026-08-05) | **File**: PhD/Jacobs/U3/Level.lean | **Depends**: B03,
  B05 | **Parent**: B07 | **Type**: theorem
- **Progress**: PROVEN sorry-free, std axioms.  Route was `Subring.closure_le` (NOT
  `closure_induction`): the preimage of a subring under a ring hom is a subring, so only
  the two generator families need checking.  `integralMatrices` restated with `‖·‖ ≤ 1`
  (ultrametric API) + `mem_integralMatrices_iff` to the `adicCompletionIntegers` form.
- **Spawned** 2026-08-05 (beastmode, Tier A5): `theta_localOrder` is a SET EQUALITY, i.e.
  two independently-provable inclusions; splitting per the one-conclusion rule.  This is
  the easy direction.
- **Statement**: `∀ x ∈ localOrder v₃, ∀ i j, (RigidificationAt.equiv … x) i j ∈
  v₃.adicCompletionIntegers ℚ`.
- **Proof sketch**: `Subring.closure_induction` on membership in `localOrder v₃` — the
  carrier is a `Subring.closure`, so it suffices to check the two generator families and
  that integral matrices are closed under `+`, `*`, `-`, `0`, `1`.
  (1) generators from `hurwitzOrder`: `θ₃(d ⊗ 1)` has entries that are ℤ-combinations of
      `1, ν₃` divided by 2 — integral because `ν₃ ∈ 𝓞₃` (`ν₃_near` ⟹ `‖ν₃‖ ≤ 1`) and `2`
      is a unit at `3` (`norm_ofNat_eq_one`).
  (2) generators from `𝓞₃`: `θ₃(1 ⊗ z) = z • 1`, integral since `z ∈ 𝓞₃`.
  (3) closure: entries of sums/products of integral matrices are integral
      (`Valuation.map_add`/`map_mul` + `mem_adicCompletionIntegers`).
- **Mathlib lemmas**: `Subring.closure_induction`, `mem_adicCompletionIntegers`,
  `Valued.v.map_add`, `map_mul`.
- **Sources**: [Jac p. 14] (the explicit θ), [Jac §B.1 p. 44] (`th1`).
- **Generality**: concrete at `v₃` per the tranche.

### [B07b] θ₃ maps the integral matrices INTO the local order (sub-ticket of B07) — DONE
- **Status**: DONE (2026-08-05) | **File**: PhD/Jacobs/U3/Level.lean | **Depends**: B03,
  B05, B07a | **Parent**: B07 | **Type**: theorem
- **Progress**: PROVEN sorry-free, std axioms.  `preimage` (Jacobs `th1` at ξ=1) +
  `theta_preimage` (entrywise `linear_combination … * sq_ν₃`) + `preimage_mem_localOrder`
  (every coefficient is (integral ± integral·ν₃)/2; `norm_ν₃ = 1`, `norm_two_eq_one`).
  `theta_localOrder` assembled from B07a ⊆ and this ⊇.
- **Spawned** 2026-08-05 (beastmode, Tier A5): the reverse inclusion of `theta_localOrder`.
- **Statement**: `∀ g : Matrix (Fin 2) (Fin 2) K₃, (∀ i j, g i j ∈ v₃.adicCompletionIntegers ℚ)
  → (RigidificationAt.equiv … ).symm g ∈ localOrder v₃`.
- **Proof sketch**: Jacobs's explicit inverse `th1` [§B.1 p. 44] writes the preimage
  quaternion coordinates as `(m₀₀+m₁₁)/2`, `((m₁₁−m₀₀)ν − (m₀₁+m₁₀))/2`, `(m₁₀−m₀₁)/2`,
  `((m₁₁−m₀₀) + (m₀₁+m₁₀)ν)/2` — all in `𝓞₃` when the `mᵢⱼ` are, since `2` is a unit at `3`
  and `ν₃ ∈ 𝓞₃`.  Then exhibit the preimage as a sum of generators: the `1, i, j, k`
  components times local integers, each of which is in `localOrder v₃` by
  `includeLeft_mem_localOrder` (the Hurwitz basis vectors `1, i, j, k` ARE in
  `hurwitzOrder`) and `includeRight_mem_localOrder`.
  NB the four coordinates are `𝓞₃`-multiples of the ℤ-basis, NOT half-integers, so no
  parity condition is involved — the `/2` is absorbed because `2 ∈ 𝓞₃ˣ`.
- **Mathlib lemmas**: `Subring.mul_mem`, `Subring.add_mem`, `Subring.sum_mem`.
- **Sources**: [Jac §B.1 p. 44] (`th1`).
- **Generality**: concrete at `v₃`.

### [B07c] The Hurwitz `ℚ`-basis `1, i, j, ω` and its coordinate criterion (sub-ticket of B07) — DONE
- **Status**: DONE (2026-08-05) — landed as `mem_hurwitzOrder_iff_isInt` (the four-fold conjunction form, which is what the functionals consume) plus `qomega`/`hurwitzCoord`/`mem_hurwitzOrder_iff_coords`.  The abstract `Module.Basis` turned out to be UNNECESSARY: the coordinate extraction goes through `ℚ`-linear functionals (`coordLin`) extended to `D ⊗ K_w` by `TensorProduct.lift`, not through a basis `repr`.
  **File**: PhD/Jacobs/U3/Level.lean | **Depends**: B05 |
  **Parent**: B07 | **Type**: def + theorem
- **Statement**: `hurwitzBasis : Module.Basis (Fin 4) ℚ D` on `![1, qi, qj, qomega]` with
  `qomega = (1+i+j+k)/2`, plus
  `mem_hurwitzOrder_iff_coords : d ∈ hurwitzOrder ↔ ∀ n, ∃ z : ℤ, hurwitzCoord d n = z`
  where `hurwitzCoord d = ![d.re - d.imK, d.imI - d.imK, d.imJ - d.imK, 2 * d.imK]`.
- **Proof sketch**: build the basis with `basisOfTopLeSpanOfCardEqFinrank` (four vectors,
  `finrank ℚ D = 4` from `QuaternionAlgebra.basisOneIJK`); spanning because
  `k = 2ω − 1 − i − j`.  The coordinate criterion is arithmetic on `IsHurwitz`'s
  `(A,B,C,E)/2` presentation: `c₀ = (A−E)/2`, `c₁ = (B−E)/2`, `c₂ = (C−E)/2`, `c₃ = E`,
  and the equal-parity condition is exactly integrality of the first three.
- **Sources**: [Jacobs p. 22]; [Voight, GTM 288, §11.1] for the Hurwitz order.
- **Generality**: project-local (specific to `ℍ[ℚ]`).

### [B07d] `localOrder w` is the `𝓞_w`-span of the Hurwitz order (sub-ticket of B07) — DONE
- **Status**: DONE (2026-08-05) — landed as `localSpan` (an `AddSubmonoid`, NOT a `Submodule`: `Module 𝓞_w (D ⊗ K_w)` does not synthesise, and the additive form needs only multiplicativity, which comes free from `hurwitzOrder` and `𝓞_w` being rings) + `localSubring` + `localOrder_le_localSpan`.  Only the `≤` direction is needed.
  **File**: PhD/Jacobs/U3/Level.lean | **Depends**: B07c |
  **Parent**: B07 | **Type**: theorem
- **Statement**: `(localOrder w : Set (D ⊗[ℚ] w.adicCompletion ℚ)) =
  Submodule.span (w.adicCompletionIntegers ℚ) (includeLeftRingHom '' hurwitzOrder)`.
- **Proof sketch**: `⊇` each generator is in `localOrder` (`tmul_mem_localOrder`) and
  `localOrder` is `𝓞_w`-stable because `z • x = (1 ⊗ z) * x`.  `⊆` by
  `Subring.closure_le` into the subring built on the span — closed under `*` because the
  generating set is multiplicatively closed (`Submodule.span_mul_span`), contains `1 ⊗ z`
  as `z • (1 ⊗ 1)`.  **Note**: no quaternion multiplication table is needed; the
  multiplicative closure comes from `hurwitzOrder` already being a `Subring`.
- **Generality**: project-local.

### [B07e] Everywhere-local integrality of a rational (sub-ticket of B07) — DONE
- **Status**: DONE (2026-08-05) — `isInt_of_forall_mem_adicCompletionIntegers`, via `valuedAdicCompletion_eq_valuation'`, `mem_integers_of_valuation_le_one` and `Rat.ringOfIntegersEquiv`.
  **File**: PhD/Jacobs/U3/Level.lean | **Depends**: — |
  **Parent**: B07 | **Type**: theorem
- **Statement**: `(∀ w : HeightOneSpectrum (RingOfIntegers ℚ),
  algebraMap ℚ (w.adicCompletion ℚ) q ∈ w.adicCompletionIntegers ℚ) → ∃ z : ℤ, q = z`.
- **Proof sketch**: `valuation_le_one` at every height-one prime says `q ∈ 𝓞_ℚ = ℤ`
  (`IsDedekindDomain.HeightOneSpectrum` + `Rat.HeightOneSpectrum` API); pull the adic
  condition back to `v.valuation ℚ q ≤ 1` through `valuedAdicCompletion_eq_valuation`.
- **Generality**: could be stated for a general number field; keep at `ℚ` for now.

### [B07f] `D^× ∩ U₀(1) = 𝓞_D^×` (sub-ticket of B07, the ticketed statement) — DONE
- **Status**: DONE (2026-08-05) — `mem_hurwitzOrder_of_forall_local` (crux) + `toLocal_unitsIncl` + `unitsIncl_mem_U0_iff`.  Std axioms.
  **File**: PhD/Jacobs/U3/Level.lean | **Depends**: B07c, B07d, B07e |
  **Parent**: B07 | **Type**: theorem
- **Statement**: `unitsIncl_mem_U0_iff` as already on the board.
- **Proof sketch**: the crux is `mem_hurwitzOrder_of_forall_local`: if `d ⊗ 1 ∈ localOrder w`
  for every `w` then, by B07d + the `K_w`-basis `Algebra.TensorProduct.basis` on
  `hurwitzBasis`, every coordinate of `d` is in `𝓞_w`; by B07e each is a rational integer;
  by B07c `d ∈ hurwitzOrder`.  Apply to `x` and `x⁻¹`, then `x * x⁻¹ = 1` makes `x` a unit
  of `hurwitzOrder`.  Converse: `tmul_mem_localOrder`.
- **Sources**: [Jacobs (1.4.7)].
- **Generality**: project-local.

### [B08] Lemma 2.3: the η-decomposition — DONE
- **Status**: DONE (2026-08-05, beastmode).  `PhD/Jacobs/U3/EtaDecomposition.lean` is
  **sorry-free**; all declarations on [propext, Classical.choice, Quot.sound].
- **Design**: `etaRep t := levelUnip t * eta3` with `levelUnip t = (1 0; 9t 1) ∈ U₁(9)`, so
  membership of `U₁(9)·{η₃}` (the MapsTo half) is true by CONSTRUCTION.  The `3`-component
  is `w_t = (1 0; 9t 3)`; the adjugate of the thesis's `v_t = (3 0; 9t 1)` is `(1 0; −9t 3)`
  and `{0,−9,−18} ≡ {0,18,9} mod 27`, so this is the same family reindexed.
- **Two facts the thesis's "elementary" proof hides, both needed and both new**:
  1. **`3` is a uniformizer at `v₃`** — `Setting.valued_three_eq : v(3) = exp(−1)`, plus
     `valued_nine_eq : v(9) = γ₉`.  Disjointness turns on `w_s⁻¹w_t = (1 0; 3(t−s) 1)`
     having lower-left valuation exactly one step ABOVE the threshold `γ₉ = exp(−2)`;
     `v(3) < 1` is too weak.  Proved via `asIdeal_v₃` (the prime is `span {3}`),
     `three_notMem_sq_v₃` (`9 ∤ 3`) and `intValuation_le_pow_iff_mem` in both directions.
  2. **The residue field of `𝓞₃` is `𝔽₃`** — `exists_fin3_approx`: every local integer is
     `≡ 0, 1, 2 mod 3`.  This is what makes the COVERING work (the index `t` is forced).
     Proved by transporting to `ℤ_[3]` along `PadicInt.adicCompletionIntegersEquiv`, which
     applies on the nose because `v₃` is *defined* as `primesEquiv.symm ⟨3, _⟩`; then
     `PadicInt.exists_mem_range` + `maximalIdeal_eq_span_p`.
- **Reusable API added**: `QMF.unitAt` + `toMatrix_unitAt` / `toLocal_unitAt` /
  `toLocal_unitAt_ne` / `unitAt_inv` / `toLocal_iotaV_ne` / `toLocal_etaAdelic_(inv_)ne`
  (UpiElement.lean); `unitAt_mem_U0`, `unitAt_mem_U1_9`, `symm_mem_localOrder`,
  `mem_U1_9_of_toMatrix` (Level.lean); `Setting.sigma1_of_mul_eq_one` — **`Σ₁(9)` is closed
  under integral inverses**, which halved the covering proof by removing the need to redo
  the whole analysis for `h⁻¹`.
- **Chain**: `lowerUnip` → `levelUnip` → `etaRep`; `toMatrix_eta3(_inv)`,
  `toMatrix_eta3_conj` (`(α β; γ δ) ↦ (α 3β; γ/3 δ)`), `toMatrix_etaRep(_inv)(_mul)`,
  `toMatrix_etaRep_inv_mul_eta3(_inv)`, `valued_div_three`, `etaRep_inv_mul_notMem`
  (disjointness), `exists_etaRep_mem` (covering), `bijOn_etaRep`, `finite_image_eta3`.

### [BC2] /cleanup PhD/Jacobs/U3/Hurwitz.lean
- **Status**: done (2026-08-05, beastmode; **0 errors / 0 warnings**, all lines ≤100,
  chain green).  FIXES: (i) A.3 — replaced the `import Mathlib.Tactic` catch-all with
  targeted imports (`Mathlib.Data.Int.Interval` for `Finset.Icc` on `ℤ`, plus
  `Tactic.{Linarith, NormNum, Positivity, Ring}`).  **This cut the chain build from 3596
  to 3411 jobs — 185 fewer modules in the transitive closure.**  Confirmed as the project
  convention: NO other file in `PhD/QMF/` or `PhD/Jacobs/` imports the catch-all, so this
  file was the outlier.  Note the instance failures on narrowing were Finset/order, not
  tactics — `Finset.Icc` on `ℤ` lives in `Mathlib.Data.Int.Interval` (NOT
  `Mathlib.Order.Interval.Finset.Int`, which does not exist at this rev).
  (ii) A.4 — stripped the one `/-! ###` divider.  (iii) Added the 5 missing public
  docstrings (`hnorm_coe`, `hnorm_mul`, `hnorm_eq_zero_iff`, `hnorm_eq_one_iff`,
  `ofTuple_injective`).  (iv) Rewrapped one 102-char line. | **Depends**: B05 (+ B06 only if worked — deferred) | **Type**: cleanup

### [B09] Thm 2.1 substrate: the mod-9 orbit computation — DONE
- **Status**: DONE (2026-08-05, beastmode).  All three fills PROVEN sorry-free, std axioms:
  `unitsMod9`, `card_primitiveVectors = 72`, `orbits_unitsMod9`.
- **The orbit count is a KERNEL `decide`** over the `24 × 72 × 3` table — no
  `native_decide`, as the ticket required.  Two things had to be arranged first:
  (i) the `∃!` must be spelled out as `∃ i, P i ∧ ∀ j, P j → j = i`; the `Decidable`
  instance is NOT found through the `∃!` binder;
  (ii) `set_option maxRecDepth 100000 in` must come BEFORE the docstring, not between it
  and the `theorem` — Lean rejects `/-- … -/ set_option … in theorem`.
- **The table is DERIVED, not transcribed** ([Jacobs p. 23] gives it, we recompute it):
  `unitsMod9_apply` sends a unit with halved coordinates `(A,B,C,E)` to
  `![![5(A+E) + 20B, 5(B−C) − 20E], ![5(B+C) − 20E, 5(A−E) − 20B]]` in `ℤ/9`, via
  `theta_tmul_one` plus the reduction dictionary (`A/2 ↦ 5A` since `2⁻¹ = 5`, and `ν₃ ↦ 4`
  from `ν₃_near`).
- **Chain**: `redMod9` (`𝓞₃ →+* ℤ/9`, via `PadicInt.toZModPow 2` transported along
  `PadicInt.adicCompletionIntegersEquiv`) → `redMat` → `thetaOnOrder`
  (`RingHom.codRestrict`, containment = B07a) → `unitsMod9`; then `tupleMat` +
  `exists_unit_iff_exists_tuple` (using Hurwitz.lean's newly extracted
  `exists_tuple_of_unit` / `exists_unit_of_tuple`, the two directions of the 24-element
  enumeration) reduce the statement to `orbits_tupleMat`.
- **Traps recorded**: `theta3` is a `RingEquiv` — use `.toRingHom.comp`, else unification
  runs away; subtype ring-hom laws need `rw [← map_add redMod9]; congr 1` rather than
  `Subtype` defeq; subtype numerals need `Subtype.ext (by norm_cast)`; and do not
  `rw [theta_tmul_one]` under a `redMod9 ⟨_, hint i j⟩` binder (motive not type correct).

### [B10] Class representatives — DONE
- **Status**: DONE (2026-08-05, beastmode) — `classRep` + `toMatrix_classRep` PROVEN,
  std axioms.  Route: added a **generic** `QMF.unitAt` to `PhD/QMF/UpiElement.lean` (the
  single-place adelic unit for an arbitrary invertible local matrix, with
  `toMatrix_unitAt` as its computation rule); `etaAdelic` is its `(1 0; 0 ϖ)` case.
  `classRep` is then `unitAt` of an explicit `diagUnit`, and `toMatrix_classRep` is
  `toMatrix_unitAt` + `fin_cases`.  ClassSet.lean also picked up the adic-instance pin. |
  **(orig)**: open | **File**: PhD/Jacobs/U3/ClassSet.lean | **Depends**: B03 |
  **Parallel**: yes after B03 | **Type**: def + lemma
- Fill: `classRep`, `toMatrix_classRep`.
- Sketch (L1.3): diagonal units at 3 via the `UpiElement.singleₗ`/`iotaV` pattern
  (dets 1, 10, 28 are 3-units).  Est ~120 LOC.

### [B11] Theorem 2.1 + Lemma 2.2 — **DONE** (ClassSet.lean SORRY-FREE)
- **Status**: DONE (2026-08-05, beastmode).  **`classRep_complete` and `exists_classRep_section` PROVEN sorry-free, std axioms; `PhD/Jacobs/U3/ClassSet.lean` has ZERO sorries and ZERO warnings.**  The uniqueness half closed via three new lemmas: `classRep_orbit_index` (`cᵢ` realises orbit index `i`, trivial Hurwitz unit), `redMat_mulVec_e1_of_mem_U1_9` (a `U₁(9)` element fixes `e₁` mod `9` — the `(∗ ∗; 0 1)` shape read as an action on the first basis vector), and `orbit_index_of_factorisation` (if `u = d·c_j·w` with `d` a global unit in `U₀(1)` and `w ∈ U₁(9)` then `u` realises orbit index `j`).  `classRep_index_unique` then observes that BOTH `i` and `j` are orbit indices of the single element `cᵢ` — note `d ∈ U₀(1)` is automatic, since `d = cᵢ·w⁻¹·c_j⁻¹` and all three factors lie in `U₀(1)` — so `exists_unique_orbit_index_of_mem_U0` forces `i = j`.  `exists_classRep_section` is then `Quotient.out` + `DoubleCoset.rel_iff` + `Quotient.sound'`.  `classRep_complete`/`exists_classRep_section` were MOVED to the end of the file (statements untouched) so they sit after their dependencies.
  **(prior)**: in_progress (2026-08-05, beastmode).  **`only_one_tuple_sigma1` PROVEN** by
  kernel `decide` — the finite heart of Lemma 2.2: among the `24` Hurwitz units, only the
  identity reduces mod `9` to the shape `(∗ ∗; 0 1)`.
  **KEY SIMPLIFICATION (verified)**: conjugation by `classRep i` can be IGNORED in this
  check.  Its `3`-component is `diag(dᵢ, eᵢ)` with `(dᵢ,eᵢ) ∈ {(1,1),(5,2),(7,4)}`, all
  units mod `9`; for diagonal `C = diag(a,b)`, `(C⁻¹MC)₀₀ = M₀₀` and
  `(C⁻¹MC)₁₀ = M₁₀·(a/b)`.  So the `(0,0)` condition is untouched and the `(1,0)` condition
  is scaled by a unit — both are independent of `i`.  That collapses what looked like a
  `3 × 24` check to a single `24`-case one.
  ALSO PROVEN: `redMod9_of_mem_sigma1` — the `Σ₁(9)` conditions read mod `9`: the `(0,0)`
  entry reduces to `1` and the `(1,0)` entry to `0` (both are `valuation ≤ γ₉ = v(9)`
  statements, and `redMod9_eq_zero_of_le` turns them into vanishing reductions).  This is
  the bridge from the level condition to the input of `only_one_tuple_sigma1`.
  ALSO PROVEN (the integrality half of the wrapper): `toMatrix_classRep_inv`,
  `norm_classDiag_eq_one` (the entries `1,5,7,2,4` are `3`-units),
  `diag_mem_integralMatrices`, and `classRep_mem_integralMatrices` — **both `cᵢ` and
  `cᵢ⁻¹` have integral `3`-component**, which is exactly why conjugation by `cᵢ` preserves
  integrality.
  ALSO: `mem_U0_of_toMatrix` extracted in Level.lean (the `U₀(1)` half of
  `mem_U1_9_of_toMatrix`, which now just calls it) — the componentwise criterion the
  wrapper needs.
  ALSO PROVEN: `diag_conj_entries` — conjugating by a diagonal fixes the `(0,0)` entry and
  scales `(1,0)` by a unit, **as an identity in `K₃`, not just mod 9**.  That is a real
  simplification of the plan: the argument never needs to reduce the conjugation mod `9`.
  `(C M C⁻¹)₀₀ = M₀₀` exactly, and `v((C M C⁻¹)₁₀) = v(M₁₀)` because the diagonal entries
  are `3`-units — so `redMod9_of_mem_sigma1` and `redMod9_eq_zero_of_le` apply directly to
  the conjugate.
  **`stabilizerAt_classRep` PROVEN** (2026-08-05) — [Jacobs, Lemma 2.2], `Γᵢ = {1}`,
  sorry-free on std axioms and NOT gated on HCN1, exactly as the ticket predicted.
  Assembly: conjugate integrality (`classRep_mem_integralMatrices` + `hu.2.1/.2.2`) and
  triviality of the `cᵢ` factors away from `3` (`toLocal_unitAt_ne`) give
  `cᵢuc ᵢ⁻¹ ∈ U₀(1)` via `mem_U0_of_toMatrix`; `unitsIncl_mem_U0_iff` then makes the
  global factor a Hurwitz unit; `diag_conj_entries` transports the two `Σ₁(9)` conditions
  to it unchanged; `only_one_tuple_sigma1` forces the tuple `(2,0,0,0)`, i.e. `x = 1`,
  whence `u = 1` by cancellation.  (`toLocal_unitsIncl` had to be de-`private`d.)
  **`redMod9_surjective` PROVEN** — `𝓞₃ ↠ ℤ/9`, as the composite of the bijection
  `𝓞₃ ≅ ℤ_[3]` with `PadicInt.toZModPow 2` (surjective, witness `(z.val : ℤ_[3])`).  This
  is the lifting input for the `GL₂(ℤ₃) ↠ GL₂(ℤ/9)` step of [Jacobs, (1.4.6)] that
  `classRep_complete` needs.
  **`mulVec_e1_of_mul_eq` PROVEN** — if `N` and `M` agree on `e₁` and `N` is invertible then
  `N⁻¹M` fixes `e₁`.  That is the algebraic step converting the orbit equation into the
  `Σ₁(9)` hypothesis of `mem_U1_9_of_redMod9`.
  **`orbit_eq_mulVec` PROVEN** — repackages the orbit equation as an identity of VECTORS
  (`orbits_unitsMod9` states it coordinatewise), which is the form `mulVec_e1_of_mul_eq`
  consumes.
  **`redMat_globalUnit_mul_classRep_mulVec_e1` PROVEN** — the mod-`9` action of `γ·cᵢ` on
  `e₁` IS `unitsMod9 γ` applied to the `i`-th orbit representative.  With `orbit_eq_mulVec`
  this says `redMat(γcᵢ)` and `redMat(u)` agree on `e₁`, which is exactly the hypothesis of
  `mulVec_e1_of_mul_eq`.  NOTE: new lemmas must be inserted AFTER their dependencies — the
  `U₀` block sits late in the file, so appending near the section header silently breaks
  the build.
  **`redMat_inv_mul_of_mem_U0` / `redMat_mul_inv_of_mem_U0` PROVEN** — the mod-`9` matrices
  of `g` and `g⁻¹` are two-sided inverses for `g ∈ U₀(1)`.  These supply the invertibility
  hypothesis of `mulVec_e1_of_mul_eq` and the `e₁`-fixing of the INVERSE that
  `mem_U1_9_of_redMod9` also demands.
  **`corrected_mulVec_e1` PROVEN** — if `γcᵢ` and `u` have the same mod-`9` action on `e₁`
  then `(γcᵢ)⁻¹u` FIXES `e₁`.  That is the `Σ₁(9)` hypothesis, so the orbit argument now
  connects end-to-end to `mem_U1_9_of_redMod9`.
  **`inv_mulVec_e1_of_mulVec_e1` PROVEN** — if a `U₀(1)` element fixes `e₁` mod `9` then so
  does its inverse.  This supplies the second half of `mem_U1_9_of_redMod9`'s hypotheses;
  every input to `classRep_complete` is now available.
  **`exists_classRep_factorisation_of_mem_U0` PROVEN — THE EXISTENCE HALF OF THEOREM 2.1**
  at the `U₀(1)` level: every `u ∈ U₀(1)` factors as `d·cᵢ·w` with `d ∈ globalUnits`,
  `w ∈ U₁(9)`.  The index is the orbit index of `u`'s mod-`9` action on `e₁` and `d` is the
  Hurwitz unit witnessing that orbit.  Also `redMod9_entries_of_mulVec_e1` (reading the
  `e₁`-fixing statement entrywise).  REMAINING for `classRep_complete`: lift from `U₀(1)` to
  a general `g` using `hcn`, and uniqueness of `i`.
  **`exists_classRep_factorisation` PROVEN** — the existence half for a GENERAL `g ∈ D_f^×`
  under `hcn`: the class-number-one hypothesis splits `g = d₀·u₀`, the `U₀(1)` factorisation
  applies to `u₀`, and `d₀` is absorbed into the global factor.  Only UNIQUENESS of `i` now
  stands between this and `classRep_complete`.
  **`classRep_orbit_index` PROVEN** — `cᵢ` realises orbit index `i`, with the TRIVIAL
  Hurwitz unit.  With the uniqueness clause of `exists_unique_orbit_index_of_mem_U0` this
  pins the index of `cᵢ`, which is the base case of the uniqueness argument.  (Proved by `Function.Surjective.comp`, NOT by unfolding the
  `RingHom.comp` — the latter leaves an unreducible `toZModHom` goal.)
  **`redMat_surjective` PROVEN** — `M₂(𝓞₃) ↠ M₂(ℤ/9)`, entrywise, which is the matrix form
  of [Jacobs, (1.4.6)] that `classRep_complete` consumes.
  **[Jacobs, Prop 1.25] first half PROVEN**: `mulVec_e1_mem_primitiveVectors` — an
  invertible `mod 9` matrix carries `e₁` to a primitive vector.  Proved STRUCTURALLY, not
  by `decide` on matrices: brute-forcing all `9⁴` matrices with `Matrix.det` times out at
  `whnf`, but the scalar criterion `not_isUnit_det_of_not_isUnit_col`
  (`¬IsUnit a → ¬IsUnit c → ¬IsUnit (ad − bc)`, i.e. `ℤ/9` is local with maximal ideal
  `(3)`) decides instantly and gives the matrix statement by contraposition.
  **[Jacobs, Prop 1.25] second half PROVEN**: `exists_matrix_mulVec_e1` — every primitive
  vector is `M·e₁` for an invertible `M` (scalar input `exists_completion`, again by
  `decide` on `ℤ/9` rather than on matrices).  With the first half this is transitivity of
  the `GL₂(ℤ/9)`-action on primitive vectors, i.e. the input to the orbit count.
  **RULE OF THUMB (recorded)**: push `decide` down to `ZMod 9` scalars and lift by hand;
  deciding over `Matrix (Fin 2) (Fin 2) (ZMod 9)` times out.
  **`redMat_mulVec_e1_of_mem_sigma1` PROVEN**: the `Σ₁(9)` conditions say exactly that the
  first column reduces to `(1,0)`, i.e. `U₁(9)` lands in the STABILISER of `e₁` mod `9`.
  That is the step of the (1.4.5)–(1.4.10) chain identifying `U₁(9)` inside `U₀(1)` as a
  point stabiliser — which, with Prop 1.25 (transitivity), is what puts `U₀/U₁(9)` in
  bijection with the primitive vectors.
  **`redMat_classRep_mulVec_e1` PROVEN** — the class representatives hit the orbit
  representatives: `cᵢ` has `3`-component `diag(dᵢ,eᵢ)`, so mod `9` it carries `e₁` to
  `(dᵢ, 0)`, and `(d₀,d₁,d₂) = (1,5,7)` are exactly the representatives appearing in
  `orbits_unitsMod9`.  **That closes the conceptual chain**: `classRep` ↔ orbit reps ↔
  primitive vectors ↔ `U₀/U₁(9)` cosets; `classRep_complete` is now assembly under `hcn`.
  **ONE GAP REMAINS, precisely located**: the CONVERSE of `redMod9_eq_zero_of_le`, i.e.
  `redMod9 ⟨y,_⟩ = 0 → v(y) ≤ v(9)` (the kernel of reduction is exactly `9·𝓞₃`).  It is
  needed to turn "fixes `e₁` mod `9`" back into the `Σ₁(9)` valuation conditions, i.e. to
  get `U₁(9)` membership rather than just the necessary direction.
  MATHEMATICALLY it is immediate — `PadicInt.ker_toZModPow 2` gives kernel `(3²)` and
  `𝓞₃ ≅ ℤ_[3]` is a ring iso — but THREE attempts died on the same seam: writing
  `v₃.adicCompletionIntegers ℚ` in an intermediate `have` will not unify with the equiv's
  codomain `(primesEquiv.symm ⟨3,_⟩).adicCompletionIntegers ℚ`, because `v₃` is a plain
  `def` and Lean does not delta-reduce it there (it works in `redMod9`'s definition only
  because the codomain is INFERRED).  **RESOLVED (2026-08-05)** — `redMod9_eq_zero_iff_dvd` + `valued_le_of_redMod9_eq_zero`
  PROVEN, and WITHOUT touching `v₃`.  **The fix was to transport DIVISIBILITY inside the
  subtype instead of transporting an equation through coercions into `K₃`**: all the
  rewriting then happens in `𝓞₃`, where the two (defeq but non-syntactic) copies never
  meet.  The single coercion step is one `congrArg`, with the numeral cast
  `((9 : 𝓞₃) : K₃) = 9` normalised separately by `norm_cast`.
  So the recommended `abbrev v₃` change is NOT needed — do not make it.
  (Historical diagnosis of the 5 failed attempts, kept because the trap will recur: the
  `hv3 := rfl` trick and "let types be inferred" are BOTH insufficient.  The seam is
  pervasive: after `Ideal.mem_span_singleton'` + `apply_symm_apply` one reaches
  `Valued.v (↑(e z) * ↑9) ≤ Valued.v 9`, and even `Valuation.map_mul` FAILS to match,
  because the coercion `↑(e z)` lands in `adicCompletion ℚ (primesEquiv.symm ⟨3,_⟩)` while
  `Valued.v` on the goal is the `K₃` one — defeq but not syntactically equal, so `rw`
  cannot fire anywhere in the chain.
  **RECOMMENDED FIX**: make `v₃` REDUCIBLE in `Setting.lean` (`noncomputable abbrev v₃`
  instead of `def v₃`).  That removes this whole class of failure at the source; the cost
  is more unfolding during elaboration, which should be measured against the current
  chain-build time before committing.  Everything else in B11's substrate is proved, so
  this one lemma is all that stands between the substrate and `classRep_complete`.
  )  **`valued_sigma1_of_redMod9` PROVEN** — the converse of
  `redMat_mulVec_e1_of_mem_sigma1`: fixing `e₁` mod `9` gives back the `Σ₁(9)` valuation
  conditions on the `(0,0)` and `(1,0)` entries.  With this the mod-9 ↔ `U₁(9)` dictionary
  is complete IN BOTH DIRECTIONS, so B11's substrate is finished and `classRep_complete`
  is pure assembly under `hcn`.  Also `U0_toMatrix_mem_integralMatrices` (a `U₀(1)`
  element and its inverse have integral `3`-component — B07a once more).  NOTE: ClassSet.lean
  needed `open scoped TensorProduct` added for the `⊗[ℚ]` type notation.
  **`isUnit_det_redMat_of_mem_U0` + `U0_mulVec_e1_mem_primitiveVectors` PROVEN**: the mod-`9`
  image of a `U₀(1)` element lands in `GL₂(ℤ/9)` (its inverse is integral, so the
  determinant is a unit) and therefore carries `e₁` to a primitive vector.  That is the
  entry point of the orbit argument — `orbits_unitsMod9` now applies directly to any
  `u ∈ U₀(1)`.
  **`exists_unique_orbit_index_of_mem_U0` PROVEN** — for `u ∈ U₀(1)` there is a UNIQUE
  `i : Fin 3` and a Hurwitz unit `γ` with `unitsMod9 γ · (dᵢ,0) = (u mod 9)·e₁`.  That `γ`
  is what absorbs into the global factor of `classRep_complete`, and the uniqueness is the
  `∃!` the theorem asserts.
  **`exists_globalUnit_of_hurwitzUnit` PROVEN** — a Hurwitz unit gives a global unit whose
  adelic image lies in `U₀(1)`, i.e. the orbit argument's `γ` viewed adelically.  This is
  the `mpr` direction of `unitsIncl_mem_U0_iff` (B07f) and is what lets `γ` be absorbed
  into the `d ∈ globalUnits` factor of `classRep_complete`.
  **`classRep_mem_U0` PROVEN** — each `cᵢ` lies in `U₀(1)`: trivial away from `3`, and at
  `3` both its matrix and inverse are integral because the diagonal entries `1,5,7,2,4` are
  `3`-units.  So `(unitsIncl γ · cᵢ)⁻¹ · u` is a product of `U₀(1)` elements and the whole
  orbit argument stays inside `U₀(1)`.
  **`redMat_mul_of_mem_U0` PROVEN** — the mod-`9` matrix is multiplicative on `U₀(1)`, so
  the orbit equation `unitsMod9 γ · (dᵢ,0) = (u mod 9)·e₁` can be rearranged into a
  statement about `(γcᵢ)⁻¹u` directly.
  **`redMat_unitsIncl_eq_unitsMod9` PROVEN** — the mod-`9` matrix of a global unit's adelic
  image IS its `unitsMod9` image.  This is the bridge between the adelic bookkeeping and the
  finite orbit table, i.e. it is what lets the `γ` produced by `orbits_unitsMod9` be used
  adelically.  (Needs two `rfl`s to identify `RigidificationAt.equiv` with `theta3`.)
  **`mem_U1_9_of_redMod9` + `valued_eq_one_of_sub_one_le` PROVEN** — for `g ∈ U₀(1)` whose
  reduced matrix AND reduced inverse both fix `e₁`, every `Σ₁(9)` condition follows (the
  unit condition `v(g₀₀) = 1` comes from `v(g₀₀ − 1) ≤ γ₉ < 1` by the ultrametric).  This
  is the form in which the orbit argument concludes, and it is the last general lemma
  `classRep_complete` needs.
  **`mulVec_e1_of_mul_eq` PROVEN** — if `N` and `M` agree on `e₁` and `N` is invertible then
  `N⁻¹M` fixes `e₁`.  That is the algebraic step converting the orbit equation into the
  `Σ₁(9)` hypothesis of `mem_U1_9_of_redMod9`.
  **`orbit_eq_mulVec` PROVEN** — repackages the orbit equation as an identity of VECTORS
  (`orbits_unitsMod9` states it coordinatewise), which is the form `mulVec_e1_of_mul_eq`
  consumes.
  **`redMat_globalUnit_mul_classRep_mulVec_e1` PROVEN** — the mod-`9` action of `γ·cᵢ` on
  `e₁` IS `unitsMod9 γ` applied to the `i`-th orbit representative.  With `orbit_eq_mulVec`
  this says `redMat(γcᵢ)` and `redMat(u)` agree on `e₁`, which is exactly the hypothesis of
  `mulVec_e1_of_mul_eq`.  NOTE: new lemmas must be inserted AFTER their dependencies — the
  `U₀` block sits late in the file, so appending near the section header silently breaks
  the build.
  **`redMat_inv_mul_of_mem_U0` / `redMat_mul_inv_of_mem_U0` PROVEN** — the mod-`9` matrices
  of `g` and `g⁻¹` are two-sided inverses for `g ∈ U₀(1)`.  These supply the invertibility
  hypothesis of `mulVec_e1_of_mul_eq` and the `e₁`-fixing of the INVERSE that
  `mem_U1_9_of_redMod9` also demands.
  **`corrected_mulVec_e1` PROVEN** — if `γcᵢ` and `u` have the same mod-`9` action on `e₁`
  then `(γcᵢ)⁻¹u` FIXES `e₁`.  That is the `Σ₁(9)` hypothesis, so the orbit argument now
  connects end-to-end to `mem_U1_9_of_redMod9`.
  **`inv_mulVec_e1_of_mulVec_e1` PROVEN** — if a `U₀(1)` element fixes `e₁` mod `9` then so
  does its inverse.  This supplies the second half of `mem_U1_9_of_redMod9`'s hypotheses;
  every input to `classRep_complete` is now available.
  **`exists_classRep_factorisation_of_mem_U0` PROVEN — THE EXISTENCE HALF OF THEOREM 2.1**
  at the `U₀(1)` level: every `u ∈ U₀(1)` factors as `d·cᵢ·w` with `d ∈ globalUnits`,
  `w ∈ U₁(9)`.  The index is the orbit index of `u`'s mod-`9` action on `e₁` and `d` is the
  Hurwitz unit witnessing that orbit.  Also `redMod9_entries_of_mulVec_e1` (reading the
  `e₁`-fixing statement entrywise).  REMAINING for `classRep_complete`: lift from `U₀(1)` to
  a general `g` using `hcn`, and uniqueness of `i`.
  **`exists_classRep_factorisation` PROVEN** — the existence half for a GENERAL `g ∈ D_f^×`
  under `hcn`: the class-number-one hypothesis splits `g = d₀·u₀`, the `U₀(1)` factorisation
  applies to `u₀`, and `d₀` is absorbed into the global factor.  Only UNIQUENESS of `i` now
  stands between this and `classRep_complete`.
  **`classRep_orbit_index` PROVEN** — `cᵢ` realises orbit index `i`, with the TRIVIAL
  Hurwitz unit.  With the uniqueness clause of `exists_unique_orbit_index_of_mem_U0` this
  pins the index of `cᵢ`, which is the base case of the uniqueness argument.
  (superseded plan) REMAINING for `stabilizerAt_classRep`: the adelic wrapper — `u ∈ U₁(9)` with
  `cᵢ u cᵢ⁻¹ ∈ globalUnits` gives `x : Dˣ` with `unitsIncl x ∈ U₀(1)` (conjugation by the
  diagonal `cᵢ` preserves integrality since its entries are `3`-units), hence `x` is a
  Hurwitz unit by `unitsIncl_mem_U0_iff`; then `only_one_tuple_sigma1` forces `x = 1` and
  so `u = 1`.  `classRep_complete` / `exists_classRep_section` remain HCN1-gated. |
  **(orig)**: open | **File**: PhD/Jacobs/U3/ClassSet.lean | **Depends**: B07, B09,
  B10 | **Type**: theorem (HCN1-gated for completeness parts)
- Fill: `classRep_complete`, `exists_classRep_section`, `stabilizerAt_classRep`.
- Sketch (L1.5/L1.6): chain (1.4.5)–(1.4.10) — Lemma 1.23 (ported DoubleCoset API +
  mirrored form), GL₂(ℤ₃)↠GL₂(ℤ/9) (entrywise lift + det unit), GL₂/SL₂ det
  bookkeeping, Props 1.24/1.25 (stabiliser + primitive-orbit; Bezout mod 9);
  `stabilizerAt_classRep` from B09's substrate + `unitsIncl_mem_U0_iff` (no HCN1
  needed).  Quotes in decomposition R1.  Est ~350 LOC.

### [BC3] /cleanup PhD/Jacobs/U3/ClassSet.lean — **DONE**
- **Status**: DONE (2026-08-05, beastmode).  Baseline green; 0 errors / 0 warnings; longest line 96 (the earlier byte-based scan that flagged ~27 "long" lines was a FALSE ALARM — `‖`, `₃`, `γ` are multi-byte, so byte length overcounts; always measure in CHARACTERS).  Fixed: module docstring gained `## Main definitions` / `## Main results` / `## Implementation notes`; the three in-body `/-! ## …` subsection dividers stripped per the style rules (the prose of the mod-9 one was redundant with the header).  RECORDED DEVIATION: the four `set_option maxRecDepth … in` lines are KEPT — they are load-bearing for kernel `decide` over the 24 Hurwitz units / 72 primitive vectors, and are scoped to a single declaration each (the style rule targets file-level `maxHeartbeats`).  **(prior)**: open | **Depends**: B09, B10, B11 | **Type**: cleanup

### [B12] The nine certificates (3 tickets: B12a/b/c by t-column) — **DONE**
- **Status**: done (2026-08-05, beastmode; ALL columns a/b/c at once).
  **`Factorisations.lean` is SORRY-FREE**: `sigmaTable`(+`_ne` by decide), `dTable`
  (+`_mem` one-liner via `globalUnits = range`), `uTable := ⟨uCand, uCand_mem⟩`,
  `factorisation` (by construction, `mul_inv_cancel_left`),
  `toMatrix_etaRep_mul_inv_uTable_mem_sigma1` — all `#print axioms` = std
  [propext, Classical.choice, Quot.sound].  Downstream `Matrix.lean` builds (3439 jobs).
  ARCHITECTURE: `uCand := (d·c_σ)⁻¹·cᵢ·wₜ`; membership via `mem_U1_9_of_toMatrix` with
  (i) away-from-3: `toLocal_uCand_ne = d⁻¹ ⊗ 1` per-factor + NEW Setting lemmas
  `valuation_three_eq_one_of_ne`/`inv_three_mem_adicCompletionIntegers` + `star_mem`
  (d⁻¹ = star d/3); (ii) at 3: nine explicit E-matrices in canonical `(X+Y·ν₃)/M` form
  (generated from certificate_search.py's LEAN LITERALS), norm workhorses
  `norm_lin_le`/`norm_lin_eq` (ν₃ ≡ 22 mod 27, `‖ν₃−22‖ ≤ ‖3‖³ — actually 3⁵∣2673`) +
  `norm_frac_le`/`norm_frac_eq_one`; inverse side GENERIC via `sigma1_of_mul_eq_one`
  (Setting) + new `valued_inv_entries_le` (adjugate/det-unit) — no u⁻¹ matrices computed.
  GOTCHAS for posterity: (1) files consuming `theta`-tensors need
  `attribute [local instance 2000] …instAlgebraAdicCompletion` or the ⊗ₜ elaborates on
  `DivisionRing.toRatAlgebra` and defeq-rfl FAILS (this silently sorry-taints via error
  recovery — caught by #print axioms, NOT by the build); (2) `fin_cases` leaves
  `(fun i ↦ i) ⟨k,⋯⟩`-wrappers — normalize with
  `simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]` before literal
  rws; (3) index-2 `Matrix.cons` applications don't simp — close by defeq `rfl`;
  (4) `valued_le_of_norm_le`/`valued_eq_one_of_norm_eq_one` already exist PUBLIC in
  ClassSet.lean (don't redeclare).
  **(prior)**: in_progress (2026-08-05, beastmode: transcribing tables) — DATA AVAILABLE
  (2026-08-05, orchestrator; user-authorised search).
  The nine `(σ, d)` are computed, machine-validated (four stages, unique hit per pair),
  and recorded in `PhD/Jacobs/U3/certificate_search.py` (rerunnable, < 1 s) and
  `Factorisations.lean` header `## The computed tables`.  Values: σ-rows
  `(2,1,1), (0,2,2), (1,0,0)`; with `a = 1+i−j`, `b = (−1+i+3j+k)/2`,
  `c = −(1+3i+j+k)/2` (all `nrd = 3`, Hurwitz): `d(0,·) = (−a, b, c)`,
  `d(1,·) = (a, b, c)`, `d(2,·) = (a, −b, −c)`.  All nine `u(i,t)` 3-component matrices
  are printed by the script (3-integral, `a ≡ 1 mod 9`, `c ≡ 0 mod 9`,
  `det = classDet i / classDet σ(i,t) ≡ 1 mod 9`).  The det bookkeeping FORCES
  `nrd d = 3` exactly, so the 96-candidate space is exhaustive — TRANSCRIBE these
  values, don't re-search; on any Lean-side mismatch rerun the script before suspecting
  the tables.  Membership arithmetic needs `ν₃ ≡ 22 mod 27` (`ν₃_near`), as planned.
  **(prior)**: BLOCKED (2026-08-05, beastmode; flagged 5× with no response).  The nine
  `d(i,t)` quaternions and the `σ(i,t)` index table come from the thesis's 3-adic PARI
  search (§B.1 pp. 44–48), and this board's own design note REQUIRES recomputing them
  rather than transcribing (the p. 28 `ε₁,₂` misprint was caught exactly that way).  I
  cannot derive them here without either those tables or a 3-adic search facility.
  **REJECTED SHORTCUT (recorded so nobody retries it)**: now that `classRep_complete` is
  proved, one *can* obtain `σ` and `d` by choice from
  `exists_classRep_factorisation hcn (classRep i * etaRep t)`, which would make
  `factorisation`, `dTable_mem`, `uTable` and the `Σ₁(9)` membership true by construction.
  Two reasons not to: (a) it needs `hcn`, so the tables inherit the one approved `sorry`;
  (b) far worse, a choice-defined `sigmaTable` is OPAQUE — `sigmaTable_ne` (the
  diagonal-never-occurs fact that gives `trace U₃ = 0`) and B15's `sum_weightGenFun_eq_h`
  would become unprovable about it.  The explicit tables are genuinely load-bearing.
  Note the `U0` route does NOT avoid `hcn`: `classRep i · etaRep t ∉ U₀(1)`, since
  `etaRep t` has determinant `3` at the place `3` — which is precisely why Lemma 2.4 needs
  a `d` clearing the norm-`3ᵏ` factor.
  **(prior)**: open | **File**: PhD/Jacobs/U3/Factorisations.lean | **Depends**: B02,
  B03, B07, B08, B10 | **Parallel**: a/b/c mutually parallel | **Type**: theorem
  (finite arithmetic)
- Fill: `sigmaTable`(+`_ne`), `dTable`(+`_mem`), `uTable`, `factorisation`,
  `toMatrix_etaRep_mul_inv_uTable_mem_sigma1` — B12a: t-column 0; B12b: 1; B12c: 2
  (tables are defs — B12a lands them, b/c fill their columns' identities).
- **Progress**:
  - 2026-08-05T-beastmode: chunks 1-3 BUILT. Setting.lean gained
    `valuation_three_eq_one_of_ne` + `inv_three_mem_adicCompletionIntegers` (away-from-3
    unit input). Factorisations: dA/dB/dC(+inverses dAi/dBi/dCi as literals, products
    = 1, IsHurwitz memberships, star/3 relations, units uA/uB/uC), `sigmaTable` +
    `sigmaTable_ne` (decide) + `dTable` + `dTable_mem` PROVEN (4/9 sorries gone);
    norm workhorses `norm_lin_le`/`norm_lin_eq` over ν₃ ≡ 22 mod 27; `toMatrix_unitsIncl`;
    `uCand` + away-components (`toLocal_uCand_ne`/`_inv_ne` via per-factor lemmas);
    ALL NINE `toMatrix_uCand*` E-matrix literals PROVEN (recipe: rfl-pin the pair,
    rw-chain to 4-matrix product, fin_cases + uniform simp superlist + push_cast +
    field_simp + ring). Next: per-pair Σ₁(9)/integrality + inverse generics
    (`sigma1_of_mul_eq_one` exists in Setting) + `uTable`/`factorisation`.
- Sketch (R4): LEFT-convention recomputation (right-handed shadow in decomposition for
  orientation); per certificate: θ₃-identity at 3 (`ν₃² = −2` arithmetic), d-integrality
  away from 3 (`N(d) = ±3^k`; at 2 the half-coordinates are Hurwitz-integral),
  u-membership mod 9 via `ν₃ mod 27` (from `ν₃_near`; `2695 ≡ 22 mod 27`).
  Est: §B.1's tables ≈ 9 × ~40 LOC + tables.

### [B13] κ-action: integrality, columns, operator, action laws — **DONE (7/7)**
- **Status**: DONE (2026-08-05, beastmode).  **All seven fills PROVEN; `KappaAction.lean` SORRY-FREE, 0 warnings, std axioms.**  The last two (`kappaOp_mul`, `kappaModuleAction`) are B13b/B13c — see those tickets for the `compAn` + ODE + `p`-adic-binomial-theorem development that closed them.
  **(prior)**: in_progress (2026-08-05, beastmode).  PROVEN: `norm_coeff_weightGenFun_le_one`,
  `tendsto_coeff_weightGenFun`, `kappaOp`, `matrixCoeff_kappaOp` (the last is literally
  `Jacobs.matrixCoeff_ofGenFun` — Prop 2.6 by design, as planned).
- **TWO new integrality layers, both needed, both new**:
  * **`CoeffInt φ := ∀ p, ‖coeff p φ‖ ≤ 1`** — the weight-`0` analogue of `Jacobs.RowInt`.
    Needed because `rowInt_weightGenFun` requires `‖γ 0 0‖ ≤ ‖3‖`, i.e. `‖g 1 1‖ ≤ ‖3‖`,
    which FAILS at `g = 1`.  This CONFIRMS the recorded adversarial finding (L5.2): row
    decay is genuinely unavailable on `Σ₁(9)`.
  * **`ShiftInt φ := ∀ p, ‖coeff p φ‖ ≤ ‖3‖ ^ (p 0 − p 1)`** (truncated `ℕ`-subtraction) —
    strictly between the two, and the one `Σ₁(9)` actually supports.  It is exactly what
    `ofGenFun`'s column hypothesis needs: at a fixed column `r` the bound is `‖3‖^(m−r) → 0`.
    The key closure fact is superadditivity `(a−b) + (c−d) ≥ (a+c) − (b+d)` in `ℕ` (`omega`),
    which makes `shiftInt_mul` / `shiftInt_inv` go through on the `rowInt_inv` template.
    **This replaced the planned y-degree-decomposition route entirely** — no need to split
    `C⁻¹ = B⁻¹∑ₖ((a·xy+b·y)B⁻¹)^k`; the four `quadSeries` monomials satisfy the shifted
    bound directly (`b·y` sits at `p 0 − p 1 = 0`, so `‖b‖ ≤ 1` suffices).
  Each layer has the full `of_rowInt / monomial / add / neg / sub / mul / inv` API.
  Support: `norm_le_of_valued_le`, `norm_eq_one_of_valued_eq_one` (Σ₁ is stated in
  `Valued.v`, U3Data in norms), `adjParams_apply` (= `Matrix.adjugate_fin_two`).
- **BLOCKER CLEARED**: `Jacobs.ext_matrixCoeff` (GenFun.lean) — *an operator between
  coefficient spaces is determined by its matrix*.  Proof: `norm_eq_iSup_matrixCoeff` on
  `u − v` gives `‖u − v‖ = 0`, then `TateFredholm.le_opNorm`.  It had to go in GenFun.lean,
  NOT `TateFredholm/Matrix.lean`, because the last step needs a `NontriviallyNormedField`
  base and Matrix.lean's section only has `NormedCommRing R` (there `c(I,R) →L c(J,R)` is
  not even a `NormedAddGroup`, so `norm_eq_zero` is unavailable).  `matrixCoeff_sub` added
  in Matrix.lean.
- **`kappaOp_one` PROVEN**: `adjParams 1 = 1`, `linSeries 1 = 1`, `quadSeries 1 = 1 − x·y`,
  `kappaSeries₂ t 0 1 = 1` (via `unitPow_one`, `binomialCoeff_zero`), so
  `weightGenFun t 1 = (1 − xy)⁻¹ = diagSeries`, identified through
  `MvPowerSeries.inv_eq_iff_mul_eq_one` + `coeff_mul_monomial`.
- **REMAINING**: `kappaOp_mul` (the genuine content — the generating-function composition
  identity, Jacobs's "easy check", Def 1.27; ~300 LOC) and `kappaModuleAction` (a
  one-liner once `kappaOp_mul` and `kappaOp_one` are both available).

### [B13a] The `y`-expansion of `weightGenFun`: `∑_r j_γ · w_γ^r · y^r` (sub-ticket of B13) — DONE
- **Status**: DONE (2026-08-05, beastmode).  `yCoeff_weightGenFun` PROVEN sorry-free,
  std axioms: `yCoeff (weightGenFun t γ) r = autFactor t γ * (mobius γ) ^ r` for `γ 1 1 ≠ 0`.
- **What it means**: the operator's `r`-th column is `j_γ · w_γ^r`, i.e. `kappaOp` IS the
  classical weight-`2` slash `f ↦ j_γ · (f ∘ w_γ)` with `w_γ = (a·x+b)/(c·x+d)` and
  `j_γ = κ(c·x+d)/(c·x+d)²`.  **This discharges most of the "identification debt" recorded
  in `PhD/Jacobs/U3Data.lean`'s header** ("proving that `weightGenFun` really is the
  generating function of `‖_κ γ` … is future work") — note that in U3Data at cleanup.
- **Route**: `quadSeries γ = linSeries γ − yNum γ` with `yNum γ = y·(a·x+b)`, so from
  `weightGenFun · quadSeries = kappaSeries₂ · (linSeries)⁻¹` the `y`-columns satisfy
  `yCoeff F 0 · linX = yCoeff κ 0 · (linX)⁻¹` and `yCoeff F (k+1) · linX = yCoeff F k · numX`;
  induction on `r` then gives the closed form.
- **The `y`-grading toolkit built for it** (all reusable): `yCoeff`, `linX`, `numX`,
  `mobius`, `autFactor`, `yNum`, `quadSeries_eq_sub`, `coeff_mul_of_yDeg0`,
  `coeff_mul_of_yDeg1`, `coeff_zero_mul_of_yDeg1`, `yCoeff_mul_yDeg0`, `yCoeff_mul_yDeg1`,
  `yCoeff_zero_mul_yDeg1`, `yDeg0_inv` (inverses stay in `y`-degree `0`),
  `yCoeff_linSeries`, `yCoeff_yNum`, `yCoeff_linSeries_inv`, `yCoeff_sub`,
  `yCoeff_one_zero`, `yCoeff_eq_zero_of_yDeg0`.  The two `coeff_mul_of_yDeg*` lemmas are
  `Finset.sum_nbij'` between the filtered two-variable antidiagonal and the one-variable one.

### [B13b] The action law via Möbius composition and the `κ`-cocycle — **DONE**
- **Status**: DONE (2026-08-05, beastmode).  **`kappaOp_mul` PROVEN sorry-free, std axioms; `PhD/Jacobs/U3/KappaAction.lean` is now COMPLETELY SORRY-FREE with 0 warnings.**  Final assembly: `adjParams_mul` (the adjugate anti-homomorphism `adjParams (gh) = adjParams h · adjParams g`), `absSummable_yCoeff_weightGenFun`, **`yCoeff_weightGenFun_mul`** (the column cocycle `yCoeff (weightGenFun (δγ)) r = j_γ · (yCoeff (weightGenFun δ) r ∘ w_γ)`, from `autFactor_cocycle` + `compAn_mobius_mobius` + `compAn_mul`/`compAn_pow`), then `ext_matrixCoeff` + the new `TateFredholm.matrixCoeff_comp` (matrix of a composition = convergent matrix product, from the new `hasSum_matrixCoeff`) + `PowerSeries.coeff_mul_compAn`.  Σ₁(9) side conditions discharged by `norm_adjParams_le_one`/`_lower_right`/`_lower_right_sub_one_le`/`_lower_left_le`/`_ratio_le`, `absSummable_kappaCol`, `absSummable_linX_inv_adjParams`, `absSummable_mobius_adjParams`, `absSummable_autFactor`, `coeffLeOne_mobius_adjParams`.
  **THE RECORDED OBSTRUCTION IS RESOLVED**: formal `PowerSeries.subst` indeed cannot express the composition, but the ANALYTIC substitution `PowerSeries.compAn` (B13b-1) can, and it is a ring homomorphism obeying a chain rule — the whole law follows from that plus the ODE argument.
  **(prior)**: open (2026-08-05: `norm_coeff_autFactor_le_one` PROVEN as a first step — the
  automorphy factor `j_γ` has integral coefficients, being the `r = 0` column of
  `weightGenFun`, which `coeffInt_weightGenFun` already bounds.  This is the integrality
  input the convergence argument will need.  ALSO PROVEN:
  `norm_coeff_autFactor_mul_mobius_pow_le_one` and
  `norm_coeff_autFactor_mul_mobius_pow_le_shift` — BOTH integrality layers transported
  through B13a to the `PowerSeries` columns `j_γ · w_γ^r`: uniform `≤ 1`, and the
  `‖3‖^(n−r)` decay.  Those are exactly the two bounds the analytic substitution needs to
  converge, so the remaining work is the substitution machinery itself plus the
  Möbius/cocycle pair, not further estimates.
  **`kappaOp_apply` PROVEN**: `(kappaOp g f)_j = ∑ᵢ coeff j (j_γ·w_γ^i) · fᵢ` — the
  operator IS the slash `f ↦ j_γ·(f ∘ w_γ)`, read coefficientwise.  That is the form in
  which `kappaOp_mul` should be attacked; with the two bounds above, the only content left
  is Möbius composition and the `κ`-cocycle.  Also `adjParams_lower_right_ne_zero`
  (the standing hypothesis of `yCoeff_weightGenFun`, now factored out).
  **`linX_mul` / `numX_mul` PROVEN** — `lin(δγ) = δ₁₀·num(γ) + δ₁₁·lin(γ)` and
  `num(δγ) = δ₀₀·num(γ) + δ₀₁·lin(γ)`.  **This is Möbius composition `w_{δγ} = w_δ ∘ w_γ`
  written WITHOUT substitution**, and it sidesteps the recorded obstruction entirely: the
  composition law is a LINEAR identity between the numerator and denominator series, so it
  is provable formally even though `w_γ` has nonzero constant term.  Dividing through by
  `lin γ` recovers `w_{δγ} = (δ₀₀w_γ + δ₀₁)/(δ₁₀w_γ + δ₁₁)`.
  Note `adjParams` is an ANTI-homomorphism (`adjugate (gh) = adjugate h · adjugate g`), so
  the `δ·γ` order above is the right one for `kappaOp (g*h)`.
  **`mobius_mul` PROVEN — Möbius composition in CLOSED FORM**:
  `w_{δγ} = (δ₀₀·w_γ + δ₀₁)·(δ₁₀·w_γ + δ₁₁)⁻¹`, i.e. `w_δ ∘ w_γ`, **with no substitution
  anywhere**.  Supporting: `linX_mul_eq` / `numX_mul_eq` (`lin(δγ) = lin γ·(δ₁₀w_γ+δ₁₁)`,
  `num(δγ) = lin γ·(δ₀₀w_γ+δ₀₁)`).  **The recorded substitution obstruction therefore does
  NOT apply to the geometric half of the action law** — it was a false alarm; the
  `lin`/`num` factorisation does all the work formally.  What may still need analytic input
  is only the `κ`-cocycle for `autFactor`, since `unitPow` is transcendental
  (`PadicAnalytic.unitPow_mul` is the scalar case).
  **`coeff_yCoeff_kappaSeries₂` / `constantCoeff_yCoeff_kappaSeries₂` PROVEN**: the
  `κ`-column in closed form, `coeff n = κ(d)·(t choose n)·(c/d)ⁿ`, with constant term
  `κ(d)` — so `autFactor` is invertible for a `1`-unit `d`.
  **SCOPE NOTE for the cocycle**: it genuinely needs a series-level `κ`.  With
  `lin(δγ) = lin γ · L` (`L = δ₁₀w_γ + δ₁₁`, a full power series, NOT linear in `x`), the
  cocycle is exactly multiplicativity `κ(lin γ · L) = κ(lin γ)·κ(L)`, i.e. `unitPow`
  extended to `1`-unit elements of `K₃⟦x⟧` via `padicExp (t · padicLog ·)`.  That IS an
  analytic development — unlike the geometric half, which `mobius_mul` settled formally). | **File**: PhD/Jacobs/U3/KappaAction.lean | **Depends**: B13a |
  **Parent**: B13 | **Type**: theorem
- **Statement**: `kappaOp_mul`, i.e. `w_δ ∘ w_γ = w_{γδ}` and
  `j_γ · (j_δ ∘ w_γ) = j_{γδ}` (up to the adjugate/handedness convention), transported to
  operators.
- **THE OBSTRUCTION (recorded, binding for whoever picks this up)**: this canNOT be done
  by *formal* power-series substitution.  `PowerSeries.subst` requires the substituted
  series to have zero constant term, and `mobius γ` has constant term `b/d ≠ 0` in general.
  So the composition must be proved **analytically** in the Tate algebra `c(ℕ, K₃)`:
  show `kappaOp g` acts as `f ↦ j_g · (f ∘ w_g)` on convergent series (this is where
  `PhD.Jacobs.PadicAnalytic` and the `unitPow_mul` / `unitPow_add` cocycle lemmas enter,
  as the original B13 sketch anticipated), then compose analytically.
- **Note on the identification debt**: `PhD/Jacobs/U3Data.lean`'s header explicitly records
  that "`weightGenFun` really is the generating function of `‖_κ γ`" is assumed, not proved.
  B13a is exactly the missing bridge — it turns `weightGenFun` back into the slash operator,
  which is what makes the action law provable at all.  **Discharging B13a therefore also
  discharges most of that debt**, and that should be recorded in U3Data's header at cleanup.
- **Generality**: project-local.

### [B13b-1] Analytic substitution `compAn` — **DONE**
- **Status**: DONE (2026-08-05, beastmode).  `PhD/Jacobs/U3/Compose.lean`, **0 errors / 0 warnings, std axioms**.  `compAn_mul` PROVEN: both sides equal `∑'_{(k,l)} Fₖ Gₗ · coeff n (w^(k+l))`, the left by grouping along `k+l`, the right by the Cauchy product.  Supporting: `tsum_prod_eq_tsum_sum_antidiagonal` (the `ℕ×ℕ → ℕ` regrouping, isolated because the summand is NOT of mathlib's `f k * g l` shape), `compAn_add/_C/_one/_X/_pow`, `absSummable_add/_mul/_pow/_C/_X/_one`, `CoeffLeOne.one/.mul/.pow`.
  **DESIGN DECISION (recorded)**: the file is stated over an ABSTRACT `[NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]`, not over `K₃`.  Two reasons: it is the honest generality, AND unfolding the adic completion during higher-order unification was killing elaboration — the first two attempts hit `isDefEq` timeouts at 1e6 heartbeats on exactly the `tsum_mul_tsum_of_summable_norm` / `Summable.tsum_finsetSum` applications, which compile instantly over abstract `K`.  Second pitfall worth recording: those two lemmas MUST be applied with explicit `(f := …) (g := …)`; leaving them to higher-order unification is what times out.
  **(spawned)**: 2026-08-05, beastmode — Tier A2/A4.
- **Why**: `kappaOp_mul` is a matrix-product identity `M(δγ) = M(γ)·M(δ)` whose entries are
  INFINITE sums over the inner index.  Read as generating functions that sum is exactly the
  substitution `F ↦ F ∘ w_γ`, and `w_γ = mobius γ` has NONZERO constant term, so
  `PowerSeries.subst` (which needs zero constant term) cannot express it.  The substitution
  is nonetheless perfectly well defined ANALYTICALLY: the coefficients of the outer series
  decay (`norm_coeff_autFactor_mul_mobius_pow_le_shift`: `‖·‖ ≤ ‖3‖^(k−r)`) while `w_γ` is
  coefficientwise integral, so `∑ₖ Fₖ·coeff n (wᵏ)` converges.
- **Statement**: in a new file `PhD/Jacobs/U3/Compose.lean`,
  * `AbsSummable F : Summable fun k => ‖PowerSeries.coeff k F‖` (the outer class);
  * `CoeffLeOne w : ∀ n, ‖PowerSeries.coeff n w‖ ≤ 1` (the inner class);
  * `compAn F w := PowerSeries.mk fun n => ∑' k, coeff k F * coeff n (w ^ k)`;
  * `compAn_add`, `compAn_C`, `compAn_one`, `compAn_X`, `compAn_mul`, `compAn_pow`,
    `absSummable_mul`, `coeffLeOne_pow`.
- **Sketch**: `coeffLeOne_pow` by induction + `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`
  (the `coeffInt_mul` pattern).  `compAn_mul` is the only real step: expand
  `coeff n (compAn F w * compAn G w)` over the antidiagonal, turn each product of `tsum`s
  into a `tsum` over `ℕ × ℕ` with `tsum_mul_tsum_of_summable_norm`
  [Mathlib/Analysis/Normed/Ring/InfiniteSum.lean:70], exchange the FINITE antidiagonal sum
  with the `tsum` (`tsum_sum`), recombine `coeff n (wᵏ)·coeff n (wˡ)` over the antidiagonal
  into `coeff n (w^(k+l))`, and regroup `ℕ × ℕ → ℕ` along `k + l` with
  `Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq` + `Summable.tsum_sigma'`
  (this is exactly how mathlib proves `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`,
  Topology/Algebra/InfiniteSum/Ring.lean:233).
- **Generality**: stated over `K₃` for now; the proofs use only
  `[NontriviallyNormedField] [CompleteSpace] [IsUltrametricDist]`, so a `/generalise` pass
  can lift the file wholesale — recorded for BC4.
- **Depends**: B13a | **Parent**: B13b | **Type**: def + lemma (new file)

### [B13b-2] `compAn` of the linear/Möbius data — **DONE**
- **Status**: DONE (2026-08-05, beastmode).  Landed in `KappaAction.lean` as `section Compose`, all sorry-free, std axioms, build green.  **`compAn_mobius_mobius` PROVEN: `w_δ ∘ w_γ = w_{δγ}` analytically** — the GEOMETRIC half of the action law is now completely settled.  Supporting chain: `absSummable_linX`/`absSummable_numX`, `compAn_linX`/`compAn_numX`, `linX_inv_eq` (the explicit geometric inverse `(d + c·x)⁻¹ = ∑ₙ (−c)ⁿ/d^(n+1) xⁿ`, verified by `eq_inv_iff_mul_eq_one` + a two-case `coeff` computation), `absSummable_linX_inv` (geometric series, needs `‖c‖ < ‖d‖`), `coeffLeOne_numX`/`coeffLeOne_linX_inv`/`coeffLeOne_mobius`, `constantCoeff_compAn_linX_ne_zero` (ultrametric: `‖δ₁₀·w₀‖ < 1 = ‖δ₁₁‖`), and `compAn_mobius`.  `PowerSeries.compAn_inv` was added to Compose.lean for the inverse step.
  **(spawned)**: 2026-08-05, beastmode.
- **Statement**: `compAn (linX δ) w = C (δ 1 1) + C (δ 1 0) * w`; the explicit geometric
  inverse of `linX` and its `AbsSummable`; `compAn ((linX δ)⁻¹) w = (compAn (linX δ) w)⁻¹`;
  `compAn (mobius δ) (mobius γ) = mobius (δ * γ)`, closing the GEOMETRIC half of the
  composition law from `mobius_mul` (already proved).
- **Sketch**: `linX` is a polynomial, so its `compAn` is a two-term sum.  For the inverse,
  `(C d + C c X)⁻¹ = C d⁻¹ · ∑ₙ (−c/d)ⁿ xⁿ` — verify by `PowerSeries.eq_inv_iff_mul_eq_one`;
  `AbsSummable` is then a geometric series (`‖c/d‖ ≤ ‖9‖ < 1` on `Σ₁(9)`).  Inverses pass
  through `compAn` by `compAn_mul` + `PowerSeries.mul_inv_cancel` on the image.
- **Depends**: B13b-1 | **Parent**: B13b | **Type**: lemma

### [B13b-3] The `κ`-cocycle (sub-ticket of B13b) — **DONE**
- **Status**: done (2026-08-05; bookkeeping close-out by the BC5 run).  All children
  B13b-3a/3b/3c/3d are done and the parent B13b is DONE — `kappaCol_cocycle` landed with
  them; `KappaAction.lean` is sorry-free.  The `open` status was stale.
  **(prior)**: open (spawned 2026-08-05, beastmode).
- **Statement**: `compAn (kappaCol t δ) (mobius γ) · κ(linX γ) = κ(linX (δ*γ))`, where
  `kappaCol t δ = yCoeff (kappaSeries₂ t (δ 1 0) (δ 1 1)) 0 = unitPow t d · B_t((c/d)x)`.
- **Sketch**: `linX_mul_eq` gives `linX (δγ) = linX γ · L` with
  `L = compAn (linX δ) (mobius γ)`, so the claim is multiplicativity of the `t`-th power
  `κ` on series with unit constant term.  Split `A = A₀·(1 + u)` with `u` of positive
  order; the scalar half is `PadicAnalytic.unitPow_mul` (already proved) and the formal
  half is the binomial identity `B_t(u)·B_t(v) = B_t(u + v + u·v)` in `K₃⟦x⟧`.
  **This is the one genuinely analytic input of B13b** — the geometric half is settled
  formally by `mobius_mul`.
- **Depends**: B13b-1, B13b-2 | **Parent**: B13b | **Type**: theorem (core)

### [B13b-3a] Chain rule for `compAn` — **DONE**
- **Status**: DONE (2026-08-05, beastmode).  `derivative_compAn : d⁄dX (compAn F w) = compAn (d⁄dX F) w * d⁄dX w` PROVEN in `Compose.lean`, 0 warnings, std axioms.  Also `absSummable_derivative` (free in the ultrametric setting), `CoeffLeOne.derivative`, and the reusable `summable_coeff_mul` / `summable_norm_coeff_mul`.  Both sides are shown equal to `∑'ⱼ F_{j+1}·(j+1)·coeff n (wʲ·w′)`; the `k = 0` term of the reindexing vanishes because `derivative_pow` carries the factor `(k : K⟦X⟧)`.
- **Statement** (in `Compose.lean`, abstract `K`):
  * `absSummable_derivative : AbsSummable F → AbsSummable (d⁄dX F)` — free in the
    ultrametric setting, since `‖(n+1)·F_{n+1}‖ ≤ ‖F_{n+1}‖`;
  * `derivative_compAn : d⁄dX (compAn F w) = compAn (d⁄dX F) w * d⁄dX w`.
- **Sketch**: coefficientwise.  `coeff n (d⁄dX (compAn F w)) = ∑'ₖ Fₖ·coeff n (d⁄dX (wᵏ))`
  and `d⁄dX (wᵏ) = k·w^(k−1)·d⁄dX w`; reindex `k ↦ k+1` (the `k = 0` term vanishes) to
  match `coeff n (compAn (d⁄dX F) w * d⁄dX w)`, moving the finite antidiagonal sum through
  the `tsum` as in `compAn_mul`.
- **Depends**: B13b-1 | **Parent**: B13b-3 | **Type**: lemma

### [B13b-3b] ODE uniqueness for power series — **DONE**
- **Status**: DONE (2026-08-05, beastmode).  `PowerSeries.eq_of_ode` PROVEN in `Compose.lean` (`section ODE`, over any `[Field k] [CharZero k]`), std axioms.  Strong induction on the coefficient index; `Finset.sum_eq_single (0, m)` isolates `a₀·(m+1)·d_{m+1}` as the only surviving term.
- **Statement**: over a characteristic-zero field, if `A · d⁄dX S = C t · d⁄dX A · S` and
  the same for `T`, with `constantCoeff A ≠ 0` and `constantCoeff S = constantCoeff T`,
  then `S = T`.
- **Sketch**: strong induction on the coefficient index.  Reading `coeff n` of
  `A · S' = C t · A' · S` isolates `a₀·(n+1)·s_{n+1}` as the only term involving
  `s_{n+1}`; `a₀ ≠ 0` and `(n+1) ≠ 0` (char 0) make the recursion determinate.
- **Why**: this is the uniqueness that turns "both sides satisfy the same first-order
  linear ODE and have the same constant term" into equality — the mechanism by which the
  `κ`-cocycle is proved without a two-variable binomial identity.
- **Depends**: none | **Parent**: B13b-3 | **Type**: lemma

### [B13b-3c] The `κ`-cocycle via the ODE — **DONE**
- **Status**: DONE (2026-08-05, beastmode).  **`kappaCol_cocycle` PROVEN sorry-free, std axioms**: `κ(lin (δγ)) = κ(lin γ) · (κ(lin δ) ∘ w_γ)`, under `‖t‖ ≤ 1`, the three `≠ 0` conditions, the two `1`-unit conditions on `γ₁₁`/`δ₁₁`, `‖e_δ·w_{γ,0}‖ ≤ ‖3‖²`, and the `compAn` side conditions.  Closed by `PowerSeries.eq_of_ode` on `A = lin (δγ)`: `kappaCol_ode` gives the LHS's ODE, `kappaCol_mul_compAn_ode` the RHS's, and the constant terms match via `constantCoeff_compAn_kappaCol` (= the `p`-adic binomial theorem) + `lower_right_cocycle` + `unitPow_mul` twice.  Supporting: `constantCoeff_compAn`, `constantCoeff_mobius`.
  **(details)**: ALL INGREDIENTS NOW PROVEN.
  **`Jacobs.binomialSeries_ode` PROVEN** (in `BinomialTheorem.lean`): `(1 + e·x)·B′ = t·e·B`,
  from the new `Jacobs.binomialCoeff_succ` (`(n+1)·(t choose n+1) = (t−n)·(t choose n)`);
  also `coeff_binomialSeries`, `binomialCoeff_one`.  Since `linX γ = C d·(1 + C(c/d)·X)` and
  `kappaCol t γ = C (unitPow t d)·binomialSeries t (c/d)`, scaling both sides by constants
  turns this into the ODE `linX γ · S′ = C t · (d⁄dX (linX γ)) · S` that `eq_of_ode` needs.
  **(i) and (ii) DONE**: `yCoeff_kappaSeries₂_eq` (the `κ`-column IS `C (κ d) · B_t(c/d)`),
  `linX_eq_scaled` (`lin γ = C d · (1 + C(c/d)·X)`), `derivative_linX`, and
  **`kappaCol_ode` PROVEN**: `lin γ · S′ = C t · (lin γ)′ · S` for `S = κ(lin γ)`.
  **Most of (iii) DONE**: `derivative_numX`, **`derivative_mobius`** (`w_γ′ = det γ · (lin γ)⁻²`,
  via `Derivation.leibniz` + `PowerSeries.derivative_inv'`), `C_lower_left_mul_numX_add_det`
  (`γ₁₀·num γ + det γ = γ₀₀·lin γ`), and **`lower_left_cocycle` PROVEN**:
  `C γ₁₀·(C δ₁₁ + C δ₁₀·w_γ) + C δ₁₀·lin γ·w_γ′ = C ((δγ)₁₀)`.  That is EXACTLY the
  coefficient identity the product rule throws up, so the remaining work in (iii) is pure
  bookkeeping: transport `kappaCol_ode` for `δ` through `compAn` (multiplicativity +
  `derivative_compAn`), then combine with `kappaCol_ode` for `γ` and `linX_mul_eq`.
  **(iii) DONE**: `PowerSeries.compAn_ode` (analytic substitution transports a first-order
  ODE — chain rule + multiplicativity) added to `Compose.lean`, and
  **`kappaCol_mul_compAn_ode` PROVEN**: `lin(δγ)·(S·T)′ = C t·(lin(δγ))′·(S·T)` for
  `S = κ(lin γ)`, `T = κ(lin δ) ∘ w_γ`, under the side conditions
  `AbsSummable (κ(lin δ))` and `CoeffLeOne (mobius γ)`.
  STILL OPEN: those two side conditions AT `Σ₁(9)` DATA (both are routine: the `κ`-column
  decays like `‖3‖ⁿ` by `norm_binomialCoeff_mul_pow_le`, and `coeffLeOne_mobius` is already
  proved), and (iv) constant terms agree — `constantCoeff (κ(lin δ) ∘ w_γ)
  = κ(δ₁₁)·∑ₙ (t choose n)(e_δ·w_{γ,0})ⁿ = κ(δ₁₁)·κ(1 + e_δ w_{γ,0})` by
  `tsum_binomialCoeff_eq_unitPow` + `exists_natCast_close`, then `unitPow_mul` twice using
  `(δγ)₁₁ = γ₁₁·δ₁₁·(1 + e_δ·γ₀₁/γ₁₁)`.
- **Statement**: `kappaCol t (δ*γ) = kappaCol t γ * compAn (kappaCol t δ) (mobius γ)`,
  where `kappaCol t γ := yCoeff (kappaSeries₂ t (γ 1 0) (γ 1 1)) 0`.
- **Sketch**: both sides satisfy `linX (δγ) · d⁄dX S = C t · d⁄dX (linX (δγ)) · S`.
  For the LHS this is the recursion `(n+1)·(t choose n+1) = (t−n)·(t choose n)` on
  `binomialCoeff`.  For the RHS it is the product rule plus B13b-3a's chain rule, using
  `linX_mul_eq : linX (δγ) = linX γ · L` with `L = compAn (linX δ) (mobius γ)`.  Then
  B13b-3b closes it, PROVIDED the constant terms agree — which is B13b-3d.
- **Depends**: B13b-3a, B13b-3b, B13b-3d | **Parent**: B13b-3 | **Type**: theorem (core)

### [B13b-3d] The `p`-adic binomial theorem `∑ₙ (t choose n) zⁿ = unitPow t (1+z)` — **DONE**
- **Status**: done (2026-08-05; status field corrected by the BC5 run — the ticket body
  already recorded DONE and `BinomialTheorem.lean` is sorry-free with std axioms).
  **(prior)**: in_progress (2026-08-05, beastmode).  **`Jacobs.tsum_binomialCoeff_eq_unitPow` PROVEN** in the new file `PhD/Jacobs/BinomialTheorem.lean` (0 errors / 0 warnings, std axioms) — the `p`-adic binomial theorem `∑ₙ (t choose n) zⁿ = (1+z)^t`, for any exponent `t` with `‖t‖ ≤ 1` that is APPROXIMABLE BY NATURAL NUMBERS, and any `‖z‖ ≤ ‖3‖²`.
  Proved exactly as sketched: `unitPow_add` / `unitPow_one_eq` / `unitPow_natCast` (weight power at natural exponents), `prod_natCast_sub` / `binomialCoeff_natCast` / `tsum_binomialCoeff_natCast` (the series truncates at natural exponents to the ordinary binomial theorem), then the two Lipschitz estimates `norm_unitPow_sub_unitPow_le` (via `unitPow_add` + `norm_unitPow_sub_one_le` + the new `norm_unitPow_eq_one`) and `norm_tsum_binomialCoeff_sub_le` (via the new ultrametric product estimate `norm_prod_sub_prod_le` and `‖3‖ⁿ ≤ ‖n!‖`).
  **DESIGN DECISION (recorded)**: the density of `ℕ` is taken as an explicit HYPOTHESIS
  `hdense : ∀ ε > 0, ∃ m : ℕ, ‖t − m‖ < ε` rather than derived, so that the whole analytic
  argument stays over an abstract ultrametric field.  **REMAINING**: discharge `hdense` for
  `K₃` (`K₃ = ℚ₃`, so `ℕ` is dense in its unit ball — route: `PadicInt.denseRange_natCast`
  transported along `PadicInt.adicCompletionIntegersEquiv`, OR successive approximation
  through the residue field using the `redMod9`-style surjectivity already in `ClassSet`).
  **DONE 2026-08-05**: `Jacobs.U3.exists_natCast_close` PROVEN in `Setting.lean` — `ℕ` is
  dense in the unit ball of `K₃`, via `PadicInt.adicCompletionIntegersEquiv` (a CONTINUOUS
  `ℤ`-algebra equivalence `ℤ₃ ≅ 𝓞₃`, and `v₃` is DEFINITIONALLY `primesEquiv.symm ⟨3,_⟩`, so
  the usual `v₃` defeq seam does not bite here) plus `PadicInt.denseRange_natCast`, pulled
  back through the open set `{y : 𝓞₃ | ‖y − t‖ < ε}` with `DenseRange.exists_mem_open`.
  **B13b-3d is therefore COMPLETE at `K₃`.**
  **(spawned)**: 2026-08-05, beastmode — Tier A1/A4.  **The long pole of B13b.**
- **Why**: B13b-3c's ODE argument pins both sides of the cocycle up to their CONSTANT
  terms.  Matching those constant terms is exactly this scalar identity: the constant term
  of `compAn (kappaCol t δ) (mobius γ)` is `unitPow t d_δ · ∑ₙ (t choose n)·(e_δ·w_{γ,0})ⁿ`,
  and it has to come out as `unitPow t L₀` so that `unitPow_mul` can absorb it.
- **Sketch** (density in the exponent, no continuity-of-`tsum` needed):
  1. `unitPow_add : unitPow (t+s) u = unitPow t u * unitPow s u` (from `padicExp_add`), and
     `unitPow 1 u = u` (`padicExp_padicLog`) ⟹ `unitPow (m : K) u = u ^ m` for `m : ℕ`.
  2. `binomialCoeff (m : K) n = (m.choose n : K)` and it VANISHES for `n > m` (the product
     `∏_{k<n}(m−k)` contains the factor `m − m`) ⟹ the tsum is a finite sum and the
     identity at `t = m` is the ordinary binomial theorem.
  3. Lipschitz-in-`t` on both sides, with ULTRAMETRIC bounds rather than a continuity
     argument: `‖unitPow t u − unitPow t' u‖ = ‖unitPow t' u‖·‖unitPow (t−t') u − 1‖
     ≤ ‖t−t'‖·‖3‖` by `norm_unitPow_sub_one_le`; and
     `‖(t choose n) − (t' choose n)‖ ≤ ‖t−t'‖/‖n!‖` because `∏_{k<n}(t−k) − ∏_{k<n}(t'−k)`
     factors as `(t−t')·Q` with `Q` an integer polynomial evaluated at norm-`≤1` arguments.
  4. `ℕ` is dense in the unit ball of `K₃` (via `PadicInt.denseRange_natCast` transported
     along `PadicInt.adicCompletionIntegersEquiv`), so 1–3 give the identity for all `t`.
- **Depends**: none (uses only `PhD.Jacobs.PadicAnalytic`) | **Parent**: B13b-3 |
  **Type**: theorem (core, analytic)

### [B13c] `kappaModuleAction` — **DONE**
- **Status**: DONE (2026-08-05, beastmode) — one-liner assembly from `kappaOp_mul` + `kappaOp_one` + linearity of `kappaOp g`; marked `@[instance_reducible]`.  **(prior)**: open | **File**: PhD/Jacobs/U3/KappaAction.lean | **Depends**: B13b |
  **Parent**: B13 | **Type**: def
- One-liner assembly from `kappaOp_mul` + `kappaOp_one` (`DistribMulAction` fields are
  `one_smul`, `mul_smul`, `smul_zero`, `smul_add`; the last two are linearity of `kappaOp g`).

### [BC4] /cleanup PhD/Jacobs/U3/KappaAction.lean + EtaDecomposition.lean — **DONE**
- **Status**: DONE (2026-08-05, beastmode).  Both files: 0 errors / 0 warnings, all lines ≤ 100 chars, no `λ`/`$`/`push_neg`/`haveI`/`letI`/`set_option`, no in-body subsection dividers, sorry-free.  Added `## Main definitions` / `## Main results` to both module docstrings, plus an `## Implementation notes` on `KappaAction` recording WHY the composition law needs the analytic substitution rather than `PowerSeries.subst`.  Also removed two genuinely unused hypotheses surfaced by the linter (`constantCoeff_mobius`'s `hd`, and the `hlr` threaded through `autFactor_cocycle`/`yCoeff_weightGenFun_mul`).  NOTE: the new files `Compose.lean` and `BinomialTheorem.lean` were authored clean (0 warnings) and should be folded into BCALL-B rather than re-audited here.  **(prior)**: open | **Depends**: B08, B13 | **Type**: cleanup

### [B14] Generic matrix recipe — DONE
- **Status**: DONE (2026-08-05, beastmode) — `heckeOperator_apply_rep` PROVEN sorry-free,
  std axioms; `PhD/QMF/HeckeMatrix.lean` is clean.  Route: `heckeOperator_eq_finsetSum`
  at `s = Finset.image w univ`, evaluated at `c` through an explicit evaluation
  `AddMonoidHom` (so `map_sum` applies — there is no `Finset.sum_apply` for
  `AutomorphicFunction`), then reindexed along `w` by `Fintype.sum_bijective`; the
  per-term step is `hfact` + `left_invt'` (kills `d`) + `apply_mul_coe` (turns `u` into an
  action factor) + `← mul_smul` (merges `⟨wₜ⟩⟨uₜ⁻¹⟩`). |
  **(orig)**: open | **File**: PhD/QMF/HeckeMatrix.lean | **Depends**: none (generic!)
  | **Parallel**: yes | **Type**: theorem
- Fill: `heckeOperator_apply_rep`.
- Sketch (R3): `heckeOperator_eq_finsetSum` (s = image of w over univ; hwinj for the
  reindex) → `(Tφ)(c) = Σₜ wₜ • φ(c·wₜ)`; factorisation + `left_invt'` +
  `apply_mul_coe` + `mul_smul` split.  Source: [Jac p. 21 display, quote in
  decomposition].  Est: source 15 lines; ~60 LOC.

### [B15] ε-identification: blocks = the transcribed generating functions
- **COBOUNDARY RESOLUTION (2026-08-05, user-requested, PROVEN)**: the twist scalar is
  spectrally inert, now a THEOREM not a remark.  Three new layers, all sorry-free except
  where gated on B16's skeleton: (1) `TateFredholm.charPowerSeries_blockOp_twist`
  (BlockOp.lean) — general coboundary invariance, `charPS (blockOp ((ψ a·φ b) • T a b))
  = charPS (blockOp T)` when `φ·ψ = 1`, via diagonal conjugation + trace property;
  (2) `Jacobs.charPowerSeries_twist_U3MatrixOp` (DiamondW.lean, + the six
  `matrixCoeff_epsOp*` de-privatised as the AG-B seam); (3) in U3/Matrix.lean:
  `classWeight` (φᵢ = κ_t(dᵢ)·dᵢ⁻²), `twist_factor` (scalar = φᵢ⁻¹·φⱼ, via one
  `unitPow_mul`), `blockOp_eq_smul_epsOp`, and the bridge
  `charPowerSeries_blockOp_eq_U3MatrixOp` (consumes the amended `matrixCoeff_blockOp`,
  so sorry-tainted until B16 fills it; the twist chain itself is proven).  U3/Matrix.lean
  now imports DiamondW — it is the designated AG-B↔AG-W meeting point.  Decision
  recorded in docstrings (Matrix.lean module header §"The determinant twist",
  Factorisations header §"Why the twist is harmless").
- **Status**: done (2026-08-05, beastmode, same run as B12).  **BOTH layers PROVEN, std
  axioms**: matrix level `adjParams_toMatrix_eq_smul_epsTable` (nine per-pair
  `adjParams_acting*` lemmas with numeral scalars 28/1, 10/1, 1/10, 28/10, 10/28, 1/28 +
  `cd0/cd1/cd2` classDet-cast lemmas + fin_cases dispatcher), series level
  `sum_weightGenFun_eq_h` (fibre Finsets by `decide`, `weightGenFun_smul` with
  per-eps `hd_*` 1-unit lemmas + per-scalar `hs_*` lemmas — all through the same
  `norm_frac_le` workhorse at T=1 — then `← smul_add`/`add_comm` collection; index-2
  matrix entries closed by defeq `rfl`).  The predicted determinant-twist scalar is
  EXACTLY as recorded in the amendment; no further statement drift.
  **(prior)**: open — STATEMENT AMENDED (2026-08-05, orchestrator).  The determinant-twist
  audit FIRED, exactly as this ticket's binding clause anticipated: the certificate
  search found `adjParams (θ₃ (etaRep t' · u⁻¹)) = (classDet σ(i,t') / classDet i) •
  ε_{i,j}(t')`, a `1`-unit scalar (`classDet ∈ {1,10,28}`, all `≡ 1 mod 9`); equivalently
  `ε_{i,j}(t') = θ₃ (c_j⁻¹ · star d · cᵢ)` on the nose.  RECORDED amendment (not
  silent): B15 is now TWO layers in Factorisations.lean — new matrix-level
  `adjParams_toMatrix_eq_smul_epsTable` (the exact certificate content; new sorry-free
  defs `classDet`, `epsTable` = the (i,t')↦ε assignment) and the series corollary
  `sum_weightGenFun_eq_h`, which gained the factor `κ(s)·s⁻²` with
  `s = classDet j / classDet i` and the hypothesis `htw : ‖tw‖ ≤ 1`.
  **(prior)**: open | **File**: PhD/Jacobs/U3/Factorisations.lean | **Depends**: B12,
  B13 | **Type**: theorem
- Fill: `adjParams_toMatrix_eq_smul_epsTable` first, then `sum_weightGenFun_eq_h`.
- Sketch (L4.3, amended 2026-08-05): matrix level — from B12's tables,
  `(wₜ'·u⁻¹)₃ = θ₃(cᵢ)⁻¹·θ₃(d)·θ₃(c_σ)` (unfold `factorisation`; 2×2 arithmetic over
  `ℚ(ν₃)`, `ν₃² = −2`), take `adjParams` (`adjParams_apply`), compare entrywise against
  `epsTable` — per-entry `linear_combination`/`ring` identities.  Series level —
  `weightGenFun_smul` (U3Data; hyps: `h3`, `htw`, scalar `≠ 0`, `‖s−1‖ ≤ ‖3‖` from
  `≡ 1 mod 9`, `‖ε₁₁ − 1‖ ≤ ‖3‖` from the RowIntegrality inventory) + sum the fibre
  `{t' | σ(i,t') = j}` (decidable once `sigmaTable` lands; scalar constant on fibre).
  DETERMINANT-TWIST AUDIT (b2-precedented, binding): FIRED and RECORDED — amendment
  above.  Est ~200 LOC.

### [B16] MILESTONE — the unconditional headline
- **Status**: done (2026-08-05, beastmode; SAME RUN as B12/B15).  **Matrix.lean is
  SORRY-FREE** (0 sorry warnings; full `lake build` green).  ALL fills proven, std
  axioms [propext, Classical.choice, Quot.sound]: `U1_9_subset_levelMonoid1` (comap
  one-liner), `eta3_mem_levelMonoid1` (via `Sigma0.eta`'s own membership + trivial
  `(0,0)`-congruence), NEW `etaRep_mem_levelMonoid1` + `levelMonoid1ToSigma1`
  (corestriction hom, `levelMonoidToSigma0` pattern) + `cosets_eta3_finite`
  (`bijOn_etaRep.image_eq` + finite range), `kappaForms` :=
  `AutomorphicFunction.levelSubmodule` under the compHom-pullback of
  `kappaModuleAction` along `levelMonoid1ToSigma1` (letI-chain per def;
  `SMulCommClass` from `(kappaOp …).map_smul`), `heckeU3` := `QMF`-style
  `AutomorphicFunction.heckeOperator` at η₃, `blockOp` := fibre-Finset sum of
  `kappaOp` over the certificates, `matrixCoeff_blockOp` (WITH the twist scalar:
  fibre-sum + `matrixCoeff_kappaOp` + `map_sum` + `sum_weightGenFun_eq_h` +
  `coeff_smul`; diagonal via `sigmaTable_ne` ⟹ empty fibre), and THE HEADLINE
  `heckeU3_apply_classRep` := `AutomorphicFunction.heckeOperator_apply_rep`
  instantiated with (etaRep, bijOn_etaRep, etaRep_injective, dTable/dTable_mem,
  uTable, factorisation, Σ₁-memberships), then `Finset.sum_fiberwise` regrouping by
  `σ(i,·)` into `blockOp`.  The determinant-twist bridge
  `charPowerSeries_blockOp_eq_U3MatrixOp` is now sorry-free too (user's decision
  record).  GOTCHAS: Matrix.lean needed `open scoped Pointwise` (Set-mul in the
  finiteness statement); `matrixCoeff_add/smul` public forms live in
  TateFredholm.Riesz OUTSIDE the import chain — local rfl-privates instead;
  `MvPowerSeries.coeff_smul` already lands in `*`-form (no `smul_eq_mul` after it).
  **(prior)**: in_progress (2026-08-05, beastmode, resumed post session-limit).
  USER DECISION RECORD (Matrix.lean module header, "The determinant twist"): the twist
  is kept in `matrixCoeff_blockOp`'s statement (honest operators) and discharged
  SPECTRALLY — new PROVEN infrastructure in Matrix.lean: `classWeight`, `twist_factor`
  (coboundary factorisation via unitPow_mul), `blockOp_eq_smul_epsOp`,
  `charPowerSeries_blockOp_eq_U3MatrixOp` (AG-B↔AG-W bridge via
  TateFredholm.charPowerSeries_blockOp_twist + Jacobs.charPowerSeries_twist_U3MatrixOp
  + DiamondW epsOp machinery; builds, 3447 jobs).  Remaining 8 sorries = the B16/B17
  fills.  NOTE: BC5's Factorisations cleanup Phase 4 is PARKED mid-run (worker seq:
  dA PASS/0-edits; sum_weightGenFun worker died at session limit with one pending
  safe finding: six `try rfl` → `rfl`); resume BC5 after B16 per user steer.
  BC5 RESUME LOG (2026-08-05, post-B16/B17): try-rfl finding was already applied
  (0 remaining, build green).  Worker seq done: dA (PASS/0 edits),
  sum_weightGenFun_eq_h (PASS; golf: 3× add_comm eliminated by enumerating two-element
  fibres as {2,1} matching the h-def order; extraction-simp proven load-bearing by
  deletion test), factorisation (PASS; golfed to one-line term
  `(mul_inv_cancel_left _ _).symm` — show/rw eliminated via the defeq seam, signature
  repacked, statement byte-identical, both builds green).  Main-agent file-level:
  3 lint warnings fixed (2× unnecessary seq-focus, 1× dead norm_num in the
  dA_mul/three_smul families) — file now ZERO warnings.  Worker log (cont.): uCand_mem PASS (30→21 lines; DISCOVERY: the nine-way int_uCand
  dispatch was mathematically redundant — integrality is the Σ₀-projection `hs.1.1` of
  the Sigma1 membership; hdet+hs now one fin_cases + positional `exacts` over the nine
  pairs; eta-reduce; stale docstring ref uCand_mem_U1_9 → uCand_mem fixed).
  adjParams_toMatrix_eq_smul_epsTable PASS (37→7 lines: nine bullet-blocks → one
  shared fin_cases<;>simp normalizer [cd0-2 + sigmaTable/epsTable unfolds via mathlib
  vecCons lemmas] + positional exacts; cast-rewrites proven load-bearing by probe).
  uCand+uTable PASS (zero-edit; docstring chain verified; two non-blocking file
  observations: `=>`-lambda convention is file-uniform [keep], L478 set_option justified
  [keep]).
  norm-workhorse cluster PASS (6 decls, −43 lines: gcongr-detours → mul_le_of_le_one,
  have-folding, exact_mod_cast, omega→lia, norm_natAbs mathlib find; rename QUEUED
  norm_int_coprime → norm_intCast_eq_one_of_not_dvd in renames.jsonl; Phase-5 flags:
  PadicAnalytic move+generalise of the ℤ-coprime lemma, U3Data ν-congruence dedup
  helper, MATHLIB-PR candidate `norm_eq_of_sub_lt` [general ultrametric isosceles —
  mathlib only has the ℚ_p forms], sub-threshold shared-chain notes).
  data/tables cluster PASS (15 edits/6 items, 8 items 0-edit; −24 lines: decide+revert,
  positional-exacts in dTable_val_mem/inv_val, products+three_smul families normalized
  to minimal `ext <;> norm_num`, cd family → term-mode mod_cast, dTable_mem docstring
  added; all statements/values byte-identical).
  toLocal/valued cluster PASS (13 decls, 57→33 body lines: toMatrix_unitsIncl bridge
  collapsed [exact crosses the instance seam where rw cannot], toLocal ×4 → terminal
  one-line simps + ×2 merged simp only, smul_third have-fold, acting_eq's 7-lemma
  chain → `group`, valued_le_γ₉ rebuilt on mathlib's norm_le_iff, valued_inv_entries_le
  15→9 with positional exacts.  PHASE-5a FLAGS: (i) valued_le_one_of_norm is a Rule-1
  wrapper for Valued.toNormedField.norm_le_one_iff.mp [~50 call sites — cascade];
  (ii) DUPLICATE `valued_eq_one_of_norm_eq_one` declared in BOTH ClassSet.lean:163 and
  EtaDecomposition.lean:236 — consolidate into Level.lean; ClassSet's
  valued_le_of_norm_le has a superfluous y≠0 vs mathlib's norm_le_iff;
  (iii) smul_third_tmul_mem single-use inline candidate.)
  Worker queue remaining: adjParams dispatcher, toMatrix_unitsIncl, norm workhorses
  (norm_lin_le/eq, norm_frac_le/eq_one, norm_ν₃_sub_22, norm_int_coprime), tables
  (sigmaTable/dTable/classDet/epsTable), toLocal family rep, acting_eq, valued
  bridges, valued_inv_entries_le, family reps (projections, products, uX, E-matrices,
  det/int/sigma1/valued_det × uCand+acting, adjParams_acting, hd/hs, cd).
  **(prior)**: open | **File**: PhD/Jacobs/U3/Matrix.lean | **Depends**: B08, B12, B13,
  B14, B15, BCALL-B | **Type**: theorem (milestone)
- Fill: `U1_9_subset_levelMonoid1`, `eta3_mem_levelMonoid1`, `kappaForms`, `heckeU3`,
  `blockOp`, `matrixCoeff_blockOp`, `heckeU3_apply_classRep`.
- **STATEMENT AMENDED (2026-08-05, B15 coboundary resolution)**: `matrixCoeff_blockOp`
  now carries the determinant-twist scalar `κ_t(s)·s⁻²`, `s = classDet j / classDet i`
  — the shape B15's `sum_weightGenFun_eq_h` actually produces, so the fill should now
  close without any scalar juggling.  Do NOT absorb the scalar into `blockOp`'s
  definition (decision record, Matrix.lean module header).  Filling
  `matrixCoeff_blockOp` automatically un-taints the already-written bridge
  `charPowerSeries_blockOp_eq_U3MatrixOp`.
- Sketch (R-B prose in decomposition): assemble the compHom action (Quaternionic
  pattern), instantiate B14 with B08's reps + B12's certificates, group by σ, apply B15.
  Est ~250 LOC.

### [B17] Completeness under HClassNumberOne
- **Status**: done (2026-08-05, beastmode, same run).  `eval_classRep_injective`
  PROVEN on std axioms (hypothesis form): pointwise via `Subtype.ext` +
  `AutomorphicFunction.ext`; `exists_classRep_factorisation hcn g` splits
  `g = d·cᵢ·w`; both forms transform by the same level action (`left_invt'` +
  `apply_mul_coe`), so agreement at the three `classRep` forces agreement
  everywhere.  `eval_classRep_injective'` (convenience) carries `sorryAx` from
  EXACTLY the one contracted source (`hClassNumberOne`) as its docstring states.
  **(prior)**: open | **File**: PhD/Jacobs/U3/Matrix.lean | **Depends**: B11, B16 |
  **Type**: theorem
- Fill: `eval_classRep_injective` (the primed convenience form
  `eval_classRep_injective'` is already complete — it just cites the interface — and
  needs no work; it goes sorry-free automatically when FLT's proof is ported).
- Sketch: `bijective_evalAtReps` at the B11 section + `stabilizerAt_classRep` (⊥ ⟹
  fixedPoints = ⊤) → injectivity of 3-point evaluation.  Est ~80 LOC.

### [B18] The idelic dictionary and hClassNumberOne (B-CN1, part 2)
- **SUPERSEDED by board hurwitz-cn1 (executed 2026-08-10)**: the FLT deferral was
  cancelled (FLT dropped its Hurwitz material); `JacobsSlash.hClassNumberOne` is proven
  in `PhD/JacobsSlash/CN1/«4_Dictionary».lean`, standard axioms.  Entry below kept as
  written.
- **Status**: DEFERRED (user 2026-08-05: FLT's `completed_units` is the same statement
  and FLT is expected to cover it — not needed for us to fill; on FLT landing, port
  their proof into the Level.lean interface and re-audit the formulation seam) |
  **File**: PhD/Jacobs/U3/ClassNumberOneFallback.lean (fallback chain incl.
  `hClassNumberOne_of_dictionary`; moved off the live chain 2026-08-05 — the live
  interface `hClassNumberOne` stays in Level.lean) | **Depends**: B06, B07 |
  **Type**: theorem (LARGE — the research-formalisation leaf)
- Fill: `latticeOf`, `latticeOf_ne_bot`, `inv_generator_mul_mem_U0`,
  `hClassNumberOne_of_dictionary` (then transplant into Level.lean's interface).
- Sketch (L6.5, decomposition): denominator ideal; sandwich for ne_bot; the CRT
  approximation for local recovery (sub-plan IN decomposition L6.5; fallback: line-by-
  line Voight 27.6.8 via /develop --continue).  [Voight 27.6.8.]  FLT's sorried
  `completed_units` is the same statement — consider upstreaming on completion.
  Est: honestly unknown; plan ~600+ LOC; hard-stop and replan if the lattice-completion
  formulation resists.

### [BC5] /cleanup PhD/Jacobs/U3/Level.lean + Factorisations.lean — **DONE**
- **Status**: done (2026-08-06, beastmode; BOTH halves).  Full 10-phase /cleanup ran on
  Factorisations.lean: Phase 0 baseline green; Phase 2 punch-list; Phase 3 file-level
  (9 in-body `/-! ###` dividers converted/stripped, 18 private docstrings → `--`
  comments, all lines ≤ 100 chars); Phase 4 SEQUENTIAL per-declaration/per-family
  workers (dA, sum_weightGenFun_eq_h, factorisation, uCand_mem, adjParams dispatcher,
  uCand+uTable, norm-workhorse ×6, data/tables ×14, toLocal/valued ×13, generated
  families ×105 by representative) — every one PASS with its four hard-gate artifacts;
  Phase 5a REFACTORS APPLIED: duplicate `valued_eq_one_of_norm_eq_one` (declared
  IDENTICALLY in ClassSet.lean:163 AND EtaDecomposition.lean:236) consolidated into the
  common ancestor Level.lean; Rule-1 wrapper `valued_le_one_of_norm` DELETED and its 66
  call sites redirected to mathlib's `Valued.toNormedField.norm_le_one_iff.mp`;
  Phase 5b rename applied (`norm_int_coprime` → `norm_intCast_eq_one_of_not_dvd`),
  queue truncated; Phase 6 gates all pass (full `lake build` green; 0 FIXME/TODO;
  0 `λ`/`$`/`push_neg`/`maxHeartbeats`/in-body dividers; 0 lines > 100 chars; axioms
  re-verified std on every headline); Phase 6.5 /simplify ran (reuse angle, deep) and
  its findings were APPLIED: `cosets_eta3_finite` → reuse `finite_image_eta3`,
  Matrix.lean's `cd0/cd1/cd2` duplicates deleted (Factorisations' de-privatised),
  the hand-rolled `Finset.induction_on` in `matrixCoeff_blockOp` → the existing generic
  `TateFredholm.matrixCoeff_sum`, `levelMonoid1ToSigma1` → mathlib's
  `MonoidHom.submonoidComap`, `norm_ne_zero_iff` for the hand-rolled nonzero steps.
  **HEADLINE NUMBERS**: Factorisations 2504 → 2125 lines (−379) with the file-level
  `set_option linter.unusedSimpArgs false` DELETED (684 dead simp args removed, 1791 →
  1065; the suppressed linter was itself the audit instrument); Matrix.lean 460 → 431.
  Zero warnings across all five touched files except the ONE approved
  `hClassNumberOne` sorry.  DEFERRED to BCALL-B (cross-board files): move
  `TateFredholm.Riesz`'s public `matrixCoeff_add/neg/smul` into `TateFredholm/Matrix.lean`
  (4 copies exist across DiamondW/Slopes/Matrix); merge the twin `ext_matrixCoeff`
  (GenFun.lean:64 vs BlockOp.lean:117); generalise `norm_div_sub_one_le` +
  `unitPow_ne_zero` into PadicAnalytic/BinomialTheorem and collapse the six `hs_*`
  certificates; `valuation_three_eq_one_of_ne` can shed ~6 lines via mathlib's
  `valuation_eq_one_iff_notMem`.
  **(prior)**: in_progress (2026-08-05, beastmode).  **Level.lean DONE**: 0 errors, only the ONE expected `sorry` warning (`hClassNumberOne`, user-approved permanent), all lines ≤ 96 chars, three in-body `/-! ## …` dividers stripped, module docstring gained `## Main definitions` / `## Main results` (flagging `hClassNumberOne` as a deliberate `sorry` in the docstring itself).  **Factorisations.lean half BLOCKED**: it is still an 8-sorry skeleton, gated on B12's certificate data.  **(prior)**: open | **Depends**: B07, B12, B15 (+ B18 only if worked — deferred) | **Type**: cleanup

### [BCALL-B] /cleanup-all over PhD/Jacobs/U3 + PhD/QMF/HeckeMatrix (pre-milestone) — **DONE**
- **Status**: done (2026-08-06, beastmode; BC5 finished both its halves, so the
  remaining files are Setting/Hurwitz/ClassSet/EtaDecomposition/KappaAction/Matrix +
  QMF/HeckeMatrix.  BC5's deferred cross-file items are folded in here: Riesz
  matrixCoeff move, twin ext_matrixCoeff merge, norm_div_sub_one_le/unitPow_ne_zero
  generalisation + hs_* collapse, valuation_three_eq_one_of_ne shortening.)
  **Matrix.lean DONE** (2026-08-06): 431 → 371 lines, zero warnings, all headline
  axioms re-verified std.  Wins: the `letI`-instance block that appeared FIVE times
  (4× in Matrix.lean + 1× in Fredholm.lean) is now two named providers
  `kappaLevelAction` / `kappaLevelSMulCommClass` placed by `levelMonoid1ToSigma1` —
  ALL five sites converted (Fredholm.lean included, 5 lines → 2);
  `heckeU3_apply_classRep` 52 → 11 body lines (the three-step calc collapsed: steps 2+3
  became the private `sum_kappaOp_eq_sum_blockOp`, step 1 + the `hact` have were pure
  bureaucracy — `hact` was `fun _ => rfl`); `eval_classRep_injective` 22 → 7 (the
  12-line coercion-ascription `key` have → the 5-rewrite idiom from
  QMF/Decomposition.lean:119); `twist_factor` 17 → 12 with `hq`/`hU` proven DEAD and
  removed (`field_simp` verified NECESSARY — `ring` cannot cancel `unitPow t dᵢ` without
  `hUi`); `unitPow_classDet_ne_zero` GENERALISED to `unitPow_ne_zero` (any 1-unit) and
  absorbed twist_factor's duplicate; `classDet_cast_ne_zero` 5 → 1; module docstring
  restructured to `## Main definitions` / `## Main results` / `## Implementation notes`
  (the twist decision record preserved in full); imports alphabetised; in-body divider
  stripped; 4 narrative proof comments stripped.  NOTE (Prop-valued instance):
  `kappaLevelSMulCommClass` MUST be a `theorem` not a `def` — a `def` trips
  `linter.defProp`.  **matrixCoeff DEDUP DONE** (2026-08-06): `matrixCoeff_smul/_add/_zero` published
  index-generically next to `TateFredholm.matrixCoeff_sum` in `PhD/Jacobs/BlockOp.lean`;
  the private copies deleted from `U3/Matrix.lean` (2) and `DiamondW.lean` (3) with all
  uses retargeted.  IMPORT-CHAIN FINDING → BETTER FIX: BlockOp was the wrong home.  `Slopes.lean` is
  *upstream* of BlockOp (Slopes → SlopeTheorem → TateFredholm.Fredholm; DiamondW imports
  Slopes AND BlockOp), and `GenFun.lean` is a third independent branch — so the lemmas
  were HOISTED to `PhD/TateFredholm/Matrix.lean`, the common ancestor of all of them
  (its own import `TateFredholm.ModelSpace` supplies `cSpace.hasSum_single`, which is all
  the general proof needs).  `matrixCoeff_smul/_add/_zero` are now `@[simp]` there beside
  `matrixCoeff_sub`, together with the index-generic `TateFredholm.ext_matrixCoeff`
  (moved out of BlockOp).  FOUR local copies deleted (U3/Matrix ×2, DiamondW ×3,
  Slopes ×1, BlockOp's ext + sum-support).  `Jacobs.ext_matrixCoeff` (GenFun.lean:64)
  KEPT deliberately: it is the norm-theoretic proof over a nontrivially normed field,
  the form the `IsTate` API consumes — the cross-reference is now recorded in both
  docstrings.
  **VERIFICATION FINDING (2026-08-06, important for every future ticket): a bare
  `lake build` DOES NOT BUILD THE WHOLE PROJECT.**  It reported "Build completed
  successfully (3 jobs)" while `PhD/TateFredholm/Riesz.lean` was GENUINELY BROKEN by the
  matrixCoeff hoist (`matrixCoeff_add`/`matrixCoeff_smul` "has already been declared" —
  Riesz reaches TateFredholm.Matrix, so the hoisted copies shadowed its originals).
  Caught only by enumerating the modules and building them explicitly; fixed by deleting
  Riesz's two now-redundant originals.  **Verify with an explicit module list, not
  `lake build`.**  That sweep also surfaced errors in four UNTRACKED scratch files
  (`PhD/QMF/Sigma0Adj.lean`, `PhD/QMF/Slash.lean`, `PhD/Jacobs/U3/DiamondHecke.lean`,
  `PhD/JacobsSlash/` — a parallel slash-refactor effort, cf. `.mathlib-quality/
  slashRefactor/`).  PROVEN NOT MINE: Sigma0Adj and Slash reach NONE of the files this
  session edited (import-closure computed); DiamondHecke does reach them but references
  none of the moved symbols, and its errors are self-contained — it calls
  `kappaOpW t ht ⟨…⟩` while its own line 146 defines `kappaOpW (g : Sigma1₃)` with no
  `t ht` parameters, so the `⟨…⟩` lands at `ℕ`.  Its own draft inconsistency.
  **ALL FOUR DEFERRED ITEMS NOW APPLIED (2026-08-06)**:
  (i) `valuation_three_eq_one_of_ne` (Setting.lean) shortened 13 → 6 lines on mathlib's
  `HeightOneSpectrum.valuation_eq_one_iff_notMem`;
  (ii) `norm_classDet_sub_one_le` + `norm_div_sub_one_le` HOISTED from Matrix.lean up to
  Factorisations.lean beside `classDet`/`cd0-2` (Matrix is downstream, so this is the
  only direction that works), and the six hand-computed `hs_*` certificates collapsed
  from 6 lines each to one-line `norm_div_sub_one_le hᵤ hᵥ` applications — new numeral
  1-unit lemmas `norm_one/ten/twentyEight_sub_one_le` + `norm_three_pow_le` serve both
  them and `norm_classDet_sub_one_le`.  GOTCHA: the obvious route `rw [← cd1, ← cd0]`
  (rewriting numerals BACKWARDS into `((classDet j : ℤ) : K₃)`) blows up with a
  deterministic `isDefEq` timeout at 200000 heartbeats — feed the numeral lemmas
  forwards instead;
  (iii) `unitPow_ne_zero` GENERALISED over the base field and moved to
  `BinomialTheorem.lean` beside `norm_unitPow_eq_one`; Matrix.lean's private deleted;
  (iv) the `=>` → `↦` sweep stays deferred as its own project-wide ticket (U3/ is
  uniformly `=>`: 285 vs 2 — per-file conversion would create inconsistency).
  **BCALL-B FINAL STATE**: Matrix.lean 431 → 335 lines; Factorisations 2125 → 2138 (net
  +13 = the two hoisted lemmas arriving, minus the hs_ collapse); live surface verified
  by building all 220 tracked modules EXPLICITLY (not `lake build`) — zero errors, and
  the only `sorry` warning in the whole live chain is `Level.lean:673 hClassNumberOne`
  (approved-permanent).  All headline axioms re-verified std. | **Depends**: BC1–BC4, B14, B15 | **Type**: cleanup-all
  (gates B16 per cadence; BC5 covers the CN1 trail afterwards)

### [BCFINAL-B] /cleanup-all, AG-B final pass — **DONE**
- **Status**: done (2026-08-06, beastmode).  **FILE-LEVEL GATE SWEEP over the whole
  AG-B surface (12 files: Setting, Hurwitz, Level, ClassSet, EtaDecomposition,
  KappaAction, Compose, Factorisations, Matrix, BinomialTheorem, U3Data,
  QMF/HeckeMatrix) — ALL PASS**: 0 lines > 100 chars, 0 `λ`, 0 `$`, 0 `push_neg`,
  0 in-body `/-! ##` dividers, and `## Main results` present in every file with
  `## Main definitions` wherever the file has definitions (BinomialTheorem and
  HeckeMatrix legitimately have none).  Fixes this pass: `Factorisations.lean`,
  `Setting.lean` and `U3Data.lean` all LACKED the Main-definitions/Main-results
  sections — added, enumerating the certificates/tables, the `ε`-matrices and
  `weightGenFun`, and the Lemma 2.7/2.11 results; `U3Data.lean`'s six in-body
  `/-! ####` dividers stripped (five pure headers deleted, the content-bearing
  scale-factor one demoted to a plain `/- -/`); two over-long lines rewrapped
  (Matrix.lean 101, U3Data 137).
  **CUMULATIVE BUILD**: all 220 tracked live modules built EXPLICITLY — zero errors,
  zero warnings anywhere in the AG-B surface, and the ONLY `sorry` warning in the entire
  live chain is `Level.lean:673 hClassNumberOne` (the contracted FLT interface).
  **AXIOM AUDIT — all 16 AG-B endpoints on [propext, Classical.choice, Quot.sound]**
  (`sigmaTable_ne` on `propext` alone): heckeU3_apply_classRep, eval_classRep_injective,
  charPowerSeries_blockOp_eq_U3MatrixOp, matrixCoeff_blockOp, blockOp_eq_smul_epsOp,
  twist_factor, factorisation, sigmaTable_ne, dTable_mem, uTable,
  toMatrix_etaRep_mul_inv_uTable_mem_sigma1, adjParams_toMatrix_eq_smul_epsTable,
  sum_weightGenFun_eq_h, classRep_complete, bijOn_etaRep, kappaOp_mul.
  This is the ACCEPTED end state: the AG-B tranche is mathematically complete and
  style-clean, gated only on FLT's `hClassNumberOne`.
  **(prior)**: open | **Depends**: B16, B17, BC5 (+ B18 only if worked — deferred; the
  tranche closes with `hClassNumberOne` sorried and B17 hypothesis-gated, which is the
  ACCEPTED end state until FLT's proof lands) | **Type**: cleanup-all (final; axiom
  check on B16/B17 endpoints: [propext, Classical.choice, Quot.sound] only; B18's
  endpoint joins the check when worked)
