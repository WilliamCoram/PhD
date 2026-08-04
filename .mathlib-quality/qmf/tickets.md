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
- **Status**: DEFERRED (user 2026-08-05: FLT will cover `completed_units`; only needed
  for B18 — do not work unless asked) | **File**:
  PhD/Jacobs/U3/ClassNumberOneFallback.lean (moved off the live chain 2026-08-05) |
  **Depends**: B05 | **Type**: theorem (core of B-CN1, part 1)
- Fill: `exists_div_rem`, `right_ideal_principal`.
- Sketch (L6.3/L6.4): `q` = the nearer of round-to-ℤ⁴ / round-to-(ℤ+½)⁴ of `a·b⁻¹`
  (STRICTNESS needs the half-lattice — decomposition attack note); then
  `N(a−qb) = N(ab⁻¹−q)N(b) ≤ ½N(b) < N(b)`.  Principality: minimal-norm generator +
  division.  [Voight 11.3.1, 11.1.8.]  Est ~200 LOC.

### [B07] Local orders and U₀(1)/U₁(9)
- **Status**: in_progress (2026-08-05, beastmode; **6 of 8 fills PROVEN**, chain green).
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
  REMAINING: `theta_localOrder` — SPLIT per Tier A5 into sub-tickets **B07a** (⊆, the
  easy direction via `Subring.closure_induction`) and **B07b** (⊇, via Jacobs's `th1`);
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

### [B07a] θ₃ maps the local order INTO the integral matrices (sub-ticket of B07)
- **Status**: open | **File**: PhD/Jacobs/U3/Level.lean | **Depends**: B03, B05 |
  **Parent**: B07 | **Type**: theorem
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

### [B07b] θ₃ maps the integral matrices INTO the local order (sub-ticket of B07)
- **Status**: open | **File**: PhD/Jacobs/U3/Level.lean | **Depends**: B03, B05, B07a |
  **Parent**: B07 | **Type**: theorem
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

### [B08] Lemma 2.3: the η-decomposition
- **Status**: open | **File**: PhD/Jacobs/U3/EtaDecomposition.lean | **Depends**: B07 |
  **Type**: theorem
- Fill: `valued_pi3_le_one`, `pi3_ne_zero`, `eta3_mem_levelMonoid`, `etaRep`,
  `etaRep_mem_levelMonoid`, `toMatrix_etaRep_mem_sigma1`, `bijOn_etaRep`,
  `etaRep_injective`, `finite_image_eta3`.
- Sketch (R2, decomposition — the thesis omits the proof; OUR expansion is recorded
  there verbatim): local identity by 2×2 arithmetic (membership/disjointness/covering),
  adelic transport via `etaAdelic`/`iotaV` API (T017 precedent).  LEFT-convention: reps
  are `η·(local unit)` forms — recompute, do not copy `(3 0; 9t 1)`.
  Est: source 0 lines (omitted) + our 1-page expansion; ~250 LOC.

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

### [B09] Thm 2.1 substrate: the mod-9 orbit computation
- **Status**: open | **File**: PhD/Jacobs/U3/ClassSet.lean | **Depends**: B03, B05 |
  **Type**: theorem (finite computation)
- Fill: `unitsMod9`, `card_primitiveVectors`, `orbits_unitsMod9`.
- Sketch (L1.4): reduction 𝓞ˣ → GL₂(ℤ/9) through θ₃ + `toZModPow`-analogue
  (`ν₃ ≡ 4 mod 9` from `ν₃_near`); orbit partition over the 72-element Finset by
  `decide`-guarded enumeration — NO native_decide; if kernel-`decide` stalls, three
  explicit orbit Finsets + closure/covering lemmas.  |G·x| = 81 − 9 = 72 ✓.
  Est: "unilluminating calculation" ~ ~300 LOC.

### [B10] Class representatives
- **Status**: open | **File**: PhD/Jacobs/U3/ClassSet.lean | **Depends**: B03 |
  **Parallel**: yes after B03 | **Type**: def + lemma
- Fill: `classRep`, `toMatrix_classRep`.
- Sketch (L1.3): diagonal units at 3 via the `UpiElement.singleₗ`/`iotaV` pattern
  (dets 1, 10, 28 are 3-units).  Est ~120 LOC.

### [B11] Theorem 2.1 + Lemma 2.2
- **Status**: open | **File**: PhD/Jacobs/U3/ClassSet.lean | **Depends**: B07, B09,
  B10 | **Type**: theorem (HCN1-gated for completeness parts)
- Fill: `classRep_complete`, `exists_classRep_section`, `stabilizerAt_classRep`.
- Sketch (L1.5/L1.6): chain (1.4.5)–(1.4.10) — Lemma 1.23 (ported DoubleCoset API +
  mirrored form), GL₂(ℤ₃)↠GL₂(ℤ/9) (entrywise lift + det unit), GL₂/SL₂ det
  bookkeeping, Props 1.24/1.25 (stabiliser + primitive-orbit; Bezout mod 9);
  `stabilizerAt_classRep` from B09's substrate + `unitsIncl_mem_U0_iff` (no HCN1
  needed).  Quotes in decomposition R1.  Est ~350 LOC.

### [BC3] /cleanup PhD/Jacobs/U3/ClassSet.lean
- **Status**: open | **Depends**: B09, B10, B11 | **Type**: cleanup

### [B12] The nine certificates (3 tickets: B12a/b/c by t-column)
- **Status**: open | **File**: PhD/Jacobs/U3/Factorisations.lean | **Depends**: B02,
  B03, B07, B08, B10 | **Parallel**: a/b/c mutually parallel | **Type**: theorem
  (finite arithmetic)
- Fill: `sigmaTable`(+`_ne`), `dTable`(+`_mem`), `uTable`, `factorisation`,
  `toMatrix_etaRep_mul_inv_uTable_mem_sigma1` — B12a: t-column 0; B12b: 1; B12c: 2
  (tables are defs — B12a lands them, b/c fill their columns' identities).
- Sketch (R4): LEFT-convention recomputation (right-handed shadow in decomposition for
  orientation); per certificate: θ₃-identity at 3 (`ν₃² = −2` arithmetic), d-integrality
  away from 3 (`N(d) = ±3^k`; at 2 the half-coordinates are Hurwitz-integral),
  u-membership mod 9 via `ν₃ mod 27` (from `ν₃_near`; `2695 ≡ 22 mod 27`).
  Est: §B.1's tables ≈ 9 × ~40 LOC + tables.

### [B13] κ-action: integrality, columns, operator, action laws
- **Status**: open | **File**: PhD/Jacobs/U3/KappaAction.lean | **Depends**: B01, B04 |
  **Parallel**: yes after deps | **Type**: theorem (core of B-LOC)
- Fill: `norm_coeff_weightGenFun_le_one`, `tendsto_coeff_weightGenFun`, `kappaOp`,
  `matrixCoeff_kappaOp`, `kappaOp_mul`, `kappaOp_one`, `kappaModuleAction`.
- Sketch (L5.2/L5.3/L5.4, decomposition — incl. the recorded FALSE-row-decay catch: the
  bound is `≤ 1`, NOT `‖3‖^m`): integrality via `kappaSeries₂`/geometric-inverse
  machinery (U3Data RowInt section, weakened to Σ₁-hypotheses); `kappaOp := ofGenFun`;
  `kappaOp_mul` per-column: continuity + basis-column substitution chain rule
  (`unitPow_mul/_add`, PadicAnalytic).  The heaviest single proof of B-LOC ("easy
  check", Def 1.27 — expect ~400 LOC).

### [BC4] /cleanup PhD/Jacobs/U3/KappaAction.lean + EtaDecomposition.lean
- **Status**: open | **Depends**: B08, B13 | **Type**: cleanup

### [B14] Generic matrix recipe
- **Status**: open | **File**: PhD/QMF/HeckeMatrix.lean | **Depends**: none (generic!)
  | **Parallel**: yes | **Type**: theorem
- Fill: `heckeOperator_apply_rep`.
- Sketch (R3): `heckeOperator_eq_finsetSum` (s = image of w over univ; hwinj for the
  reindex) → `(Tφ)(c) = Σₜ wₜ • φ(c·wₜ)`; factorisation + `left_invt'` +
  `apply_mul_coe` + `mul_smul` split.  Source: [Jac p. 21 display, quote in
  decomposition].  Est: source 15 lines; ~60 LOC.

### [B15] ε-identification: blocks = the transcribed generating functions
- **Status**: open | **File**: PhD/Jacobs/U3/Factorisations.lean | **Depends**: B12,
  B13 | **Type**: theorem
- Fill: `sum_weightGenFun_eq_h`.
- Sketch (L4.3): 2×2 products `(wₜ·u⁻¹)₃`, adjugate parameters, sum per block; compare
  against `Jacobs.h01…h21` coefficientwise (they are sums of `weightGenFun` of the
  U3Data ε-matrices — reduce to matrix-parameter equality).  DETERMINANT-TWIST AUDIT
  (b2-precedented, binding): any κ(det)-scalar mismatch is a RECORDED statement
  amendment, never a silent patch.  Est ~200 LOC.

### [B16] MILESTONE — the unconditional headline
- **Status**: open | **File**: PhD/Jacobs/U3/Matrix.lean | **Depends**: B08, B12, B13,
  B14, B15, BCALL-B | **Type**: theorem (milestone)
- Fill: `U1_9_subset_levelMonoid1`, `eta3_mem_levelMonoid1`, `kappaForms`, `heckeU3`,
  `blockOp`, `matrixCoeff_blockOp`, `heckeU3_apply_classRep`.
- Sketch (R-B prose in decomposition): assemble the compHom action (Quaternionic
  pattern), instantiate B14 with B08's reps + B12's certificates, group by σ, apply B15.
  Est ~250 LOC.

### [B17] Completeness under HClassNumberOne
- **Status**: open | **File**: PhD/Jacobs/U3/Matrix.lean | **Depends**: B11, B16 |
  **Type**: theorem
- Fill: `eval_classRep_injective` (the primed convenience form
  `eval_classRep_injective'` is already complete — it just cites the interface — and
  needs no work; it goes sorry-free automatically when FLT's proof is ported).
- Sketch: `bijective_evalAtReps` at the B11 section + `stabilizerAt_classRep` (⊥ ⟹
  fixedPoints = ⊤) → injectivity of 3-point evaluation.  Est ~80 LOC.

### [B18] The idelic dictionary and hClassNumberOne (B-CN1, part 2)
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

### [BC5] /cleanup PhD/Jacobs/U3/Level.lean + Factorisations.lean
- **Status**: open | **Depends**: B07, B12, B15 (+ B18 only if worked — deferred) | **Type**: cleanup

### [BCALL-B] /cleanup-all over PhD/Jacobs/U3 + PhD/QMF/HeckeMatrix (pre-milestone)
- **Status**: open | **Depends**: BC1–BC4, B14, B15 | **Type**: cleanup-all
  (gates B16 per cadence; BC5 covers the CN1 trail afterwards)

### [BCFINAL-B] /cleanup-all, AG-B final pass
- **Status**: open | **Depends**: B16, B17, BC5 (+ B18 only if worked — deferred; the
  tranche closes with `hClassNumberOne` sorried and B17 hypothesis-gated, which is the
  ACCEPTED end state until FLT's proof lands) | **Type**: cleanup-all (final; axiom
  check on B16/B17 endpoints: [propext, Classical.choice, Quot.sound] only; B18's
  endpoint joins the check when worked)
