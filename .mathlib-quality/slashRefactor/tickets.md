# Ticket Board — slashRefactor (REVISION 2: QMF slash layer + self-enclosed JacobsSlash fork)

**BOARD PATH: `.mathlib-quality/slashRefactor/`** — tell every `/beastmode` worker this
path explicitly.  Required reading per ticket: `plan.md` rev 2 (port map +
statement-form rules 1–6) and `decomposition.md` (Q-leaves + Result P port specs).

**Standing constraints (binding for every worker):**
- `PhD/JacobsSlash/**` must NEVER `import PhD.Jacobs.*`.  Allowed: Mathlib,
  `PhD.TateFredholm.*`, `PhD.QMF.*`, `PhD.NewtonPolygons.*`, earlier
  `PhD.JacobsSlash.«…»` files.  **Reading** `PhD/Jacobs/` sources is required (the
  port mirrors them); importing them is the defect.
- ZERO edits to existing files anywhere (`PhD/Jacobs/**`, existing `PhD/QMF/*` are
  read-only; new-QMF-file escape hatch: `PhD/QMFSlash/` — via `/develop --continue`).
- No builds before GATE-1's precondition (BCALL-B sentinel gone).
- Guillemet imports for digit-prefixed modules; prefix rule:
  `prefix(f) = 1 + max(prefix of imported JacobsSlash files)` — re-number if imports
  change, and record here.
- Statement-form rules (plan.md 1–6) override convenience: thesis convention only,
  no adjugate in JacobsSlash statements, orientation audits on data files, verbatim
  ports change header/imports/namespace ONLY, `hClassNumberOne'` mirrors the
  contract, errata decisions carry over.
- Namespace: `JacobsSlash` (flat; avoids the `Jacobs.U3` shadowing trap).

## Summary
- S-tranche (QMF layer): S-SKEL + S01–S11 proof tickets + 6 cleanups
- P-tranche (fork): P01–P22 port tickets + per-file cleanups + CLEANUP-ALL + MILESTONE
- GATE-1 blocks all proof/port work; S-SKEL precedes GATE-1.
- Open: all | Done: 0

## Dependency graph (condensed)
```
S-SKEL → GATE-1 → { S01→S02, S03, S04, S07 } …→ S05→S06, S08→S09 → S10 → S11
GATE-1 → P01,P02,P03 (VERBATIM, parallel) → P04,P05 → P06 → P07 → P08 → P09
P03,P06 → P10 ; P-analytic tail → P11
S02,GATE-1 → P12 → P13 → P14 → {P15,P16} ; P04 → P17 ; P12,P17,S03 → P18
P15,P16,P18 → P19 ; S10,S11,P18,P19 → P20 → P21 → P22 (MILESTONE)
per-file cleanups after each Pn; CLEANUP-ALL-1 → P22 → CLEANUP-FINAL
```

---

### [S-SKEL] Write the three remaining QMF skeletons
- **Status**: done (2026-08-06, beastmode: Slash/{HeckeMonoid,HeckeMatrix,Quaternionic}.lean
  written, all `:= by sorry`.  Design notes: `slashFixedPointsOfLE` introduced abstractly in
  Slash/HeckeMonoid (unification with `levelSubmoduleSlash` deferred to the cleanup wave);
  variance flip `L(U) → L(V)` documented; right cosets via `Quotient (QuotientGroup.rightRel U)`
  with `Quotient.mk''`; `heckeOperatorSlash_apply_rep` states the [Jac p. 21] display verbatim
  (`c·vₜ⁻¹ = d·c'·u`, acting element `uₜ·vₜ`); `etaAdelic'` body deferred to GATE-1/S12
  (`:= by sorry` def — needs the mirrored `etaTensor'` family); `spaceSlash_eq_space` is the
  FLT-facing agreement corollary with explicit `hcompat`.)
- **Depends**: user approval of rev 2 | **Type**: skeleton
- **Files**: NEW `PhD/QMF/Slash/HeckeMonoid.lean`, `PhD/QMF/Slash/HeckeMatrix.lean`,
  `PhD/QMF/Slash/Quaternionic.lean` (mirror `Quaternionic.lean` + the `etaAdelic`
  part of `UpiElement.lean`: `levelMonoid'`, `levelMonoidToSigma0'`, `etaAdelic'`
  with component `(ϖ 0; 0 1)`, `WeightModule`-slash plumbing, classical-weight
  quaternionic forms `L(U, L_{n,ν})` via `levelSubmoduleSlash`)
- **Do**: side-by-side mirror of `HeckeMonoid.lean` (177 lines) and
  `HeckeMatrix.lean`/`Decomposition.lean` statement surfaces: right-coset quotient
  (`QuotientGroup.rightRel`), `heckeOperatorSlash : L_slash(V) →ₗ[R] L_slash(U)`
  summing `a ∣ₛ xᵢ` over the image of `U·g` in the right-coset space
  ([Buz07 §9 quote at `HeckeMonoid.lean:30-32`]: `UηU = ∐ᵢ Uxᵢ`, `f|[UηU] := Σᵢ f|xᵢ`),
  `heckeOperatorSlash_eq_finsetSum`, right `heckeOperator_apply_rep` (factorisations
  `cᵢ·x = d·c_σ·u` in thesis orientation), right `evalAtReps` + `bijective_evalAtReps`.
  All `:= by sorry`; statement-form spec per decomposition Q10/Q11.  No builds.

### [GATE-1] Skeleton compile + digit-prefix verification
- **Status**: done (2026-08-06, beastmode.  All 7 QMF/Slash modules build, sorries only.
  Signature fixes applied: `adj_adj` statements qualified (`Sigma0'.adj (adj g) = g` —
  dot-notation on Subtype-coerced submonoid elements doesn't resolve); `adjEquiv`
  inverse fields sorried; seam theorem RHS needs `levelSubmodule (Γ := Γ) (A := A)`;
  added the missing `SMulSlashClass R Δ' (AutomorphicFunction G Γ A)` instance to
  Slash/AutomorphicFunction (mirror of the library's SMulCommClass instance);
  `bijective_evalAtRepsSlash` pins `A` via type ascription (named `(A := A)` arg not
  available on the section-variable binder).  DIGIT-PREFIX VERDICT: works end-to-end —
  `lake build PhD.JacobsSlash.«1_PadicAnalytic»` ✓ (1855 jobs), `lake exe runLinter`
  on the guillemet module ✓ (runs, produces real lints — same lints as the ORIGINAL
  PadicAnalytic, i.e. inherited not port-introduced; recorded for cleanup-wave
  decision).  No fallback rename needed.  Whole-lib `lake build PhD` ✓.
  P01 executed inside this gate per its ticket note.)
- **Depends**: S-SKEL + BCALL-B beastmode finished | **Type**: gate
- **Do**: `lake build` the 7 QMF skeleton modules; fix signature-level breakage only
  (sorries stay; statement deltas recorded here).  Known risks: `Matrix.adjugate_smul`
  exact name; `adjugate_adjugate` n=2 form; right-quotient API names
  (`QuotientGroup.rightRel` machinery).  Then create
  `PhD/JacobsSlash/1_PadicAnalytic.lean` as a smoke test of the digit-prefix pipeline
  (VERBATIM port P01 may be done here directly) and run
  `lake exe runLinter PhD.JacobsSlash.«1_PadicAnalytic»`.  FALLBACK on tool rejection:
  `S1_`-style letter prefixes, recorded.  Whole-lib `lake build PhD` must stay green.

---

## S-tranche proof tickets (QMF layer)

S01–S09 are UNCHANGED from revision 1 of this board (statements in the 4 written
skeleton files; leaves Q1–Q9 in decomposition.md carry sources, sketches, and attack
logs).  Summary lines only; the decomposition entries are the full specs:

### [S01] `Sigma0'` monoid — Slash/Sigma0.lean — dep GATE-1 — leaf Q1
- **Status**: done (2026-08-06, beastmode; mirrored `Sigma0.mul_mem'` compiles first-try —
  level entry proof IDENTICAL to original (c-entry is (1,0) in both conventions), unit
  entry via `Valued.v.map_add_eq_of_lt_right` (sum order small+big, mirror of original's
  `_of_lt_left`); `eta` membership mirrored.)
### [S02] adjugate dictionary — Slash/Sigma0.lean — dep S01 — leaf Q2
- **Status**: done (2026-08-06, beastmode; file now SORRY-FREE, axioms
  [propext, Classical.choice, Quot.sound] on adj_mul/adj_adj ×2.  Notes: memberships via
  `adjugate_fin_two` + `fin_cases <;> simp [Valuation.map_neg]`; `det_adjugate` needs
  `simpa using hdet` (simp normalises `det^(2−1)` before `pow_ne_zero` can apply);
  `adjugate_adjugate _ (by simp : Fintype.card (Fin 2) ≠ 1)` for involutivity;
  `adj_eta` by entrywise `ext` + `adjugate_fin_two`.)
### [S03] `RightSlashAction` class + `ofAntiHom` — Slash/Basic.lean — dep GATE-1 — leaf Q3
- **Status**: done (2026-08-06, beastmode; 4 one-liners, file sorry-free.)
### [S04] `matrixSubstR` calculus — Slash/WeightModule.lean — dep GATE-1 — leaf Q4
- **Status**: done (2026-08-06, beastmode; mirrors compile first-try;
  `matrixSubstR_mul` closes with `Finset.sum_comm` — no `mul_comm` needed, the
  right-handed index order aligns.)
### [S05] Buzzard slash on `WeightModule` — dep S02,S03,S04 — leaf Q5
- **Status**: done (2026-08-06, beastmode; `add_slash` needs explicit
  `simp only [coe_add, map_add, smul_add]; rfl` — plain simp stalls on the mk-sum coe.)
### [S06] `jTwist` + bridge — dep S05 — leaf Q6 (amendment path Q6-A)
- **Status**: done (2026-08-06, beastmode; **`slash_eq_adj_smul` PROVED**, axioms
  standard — the planning-time sign convention (`J = !![0,1;-1,0]`, inverse
  `!![0,-1;1,0]`) is correct, Q6-A amendment NOT needed.  Infrastructure:
  `substRLinear` + comp/one lemmas; `jTwist` via `LinearEquiv.ofLinear`;
  key matrix identity `J⁻¹ · adjᵀ · J = δ` by `eta_fin_two`/`mul_fin_two` +
  entrywise `ring`.  `Matrix.transpose` spelled out — `ᵀ` notation not open.)
### [S07] automorphic slash instance — Slash/AutomorphicFunction.lean — dep S03 — leaf Q7
- **Status**: done (2026-08-06, beastmode; instance + SMulSlashClass instance, simp-level.)
### [S08] `levelSubmoduleSlash` + membership forms — dep S07 — leaf Q8
- **Status**: done (2026-08-06, beastmode; `iff'` via `DFunLike.congr_fun` at `g·u` /
  `g·u⁻¹` + `inv_mul_cancel_right`.)
### [S09] seam theorem (`hcompat` ⇒ equality) — dep S08 — leaf Q9
- **Status**: done (2026-08-06, beastmode; **file sorry-free; seam theorem on
  [propext, Quot.sound]** — no Classical.choice.  Proof exactly the planned
  stay-inside-the-monoid route: both directions are `hcompat` + `← mul_smul` +
  inline `show ⟨u⟩*⟨u⁻¹⟩ = 1` (`convert` produced un-simpable congruence goals;
  the `rw [show … from Subtype.ext (by simp)]` form works).)

### [S10] Right-coset abstract Hecke — Slash/HeckeMonoid.lean
- **Status**: done (2026-08-06, beastmode; FILE SORRY-FREE.  `slashFixedPointsOfLE`,
  `rightTranslate` (+ `_mk` simp), `out_mem_mul_singleton_mul`, `subtype_slash_mul`,
  `slash_out_slash`, `heckeOperatorSlash` (+ `_apply`, `_eq_finsetSum`), and the
  topological finiteness helper — the last proved by TRANSPORT: inversion
  `Quotient.map' (·⁻¹)` maps `RightCosets U` injectively to `G ⧸ U`, image of `{g}·V`
  ↦ image of `V·{g⁻¹}`, then the LEFT lemma applies (needed
  `import PhD.QMF.HeckeMonoid`).  Key idioms: `simp only [hu]` before
  `subtype_slash_mul` with only hy/hz given (third membership unifies — rw-motive
  trap otherwise); `slashAddHom` added to Slash/Basic to push `∣ₛ` through sums;
  `subst` on singleton-membership eliminates the OUTER `g` (use `g'` after).
  Cleanup-wave note: `ofAntiHom` wants `@[instance_reducible]` or the
  warn-disable option.)
- **Depends**: S08, GATE-1 | **Type**: def + theorems | **Leaves**: Q10
- **Sketch**: mirror `HeckeMonoid.lean:61-176` over the right quotient; the
  representative-independence lemma uses the slash-fixedness of `a` on the OTHER side
  (`smul_out_smul`'s mirror); `heckeOperatorSlash_eq_finsetSum` mirrors `:149-163`.
  Prefer direct mirror over `Mᵐᵒᵖ`-transport (no `MulOpposite` in statements — project
  rule).  Finiteness helper mirrors `finite_image_doubleCoset_of_isCompact_of_isOpen`.
- **Sources**: [Buz07 §9 p. 69] quote at `HeckeMonoid.lean:30-32`; the left file
  itself (proof substrate).

### [S11] Right Hecke matrix recipe + evaluation — Slash/HeckeMatrix.lean
- **Status**: done (2026-08-06, beastmode; FILE SORRY-FREE.  `slash_apply_mul`
  (right transformation law), **`heckeOperatorSlash_apply_rep`** — the [Jac p. 21]
  display verbatim (`c·vₜ⁻¹ = d·c'·u`, acting `uₜ·vₜ`) — `stabilizerAtSlash`,
  `evalAtRepsSlash`, `slash_decomp_eq`, **`bijective_evalAtRepsSlash`** (the (2.1.1)
  iso, slash form).  All on [propext, Classical.choice, Quot.sound].  Proof notes:
  inverse-map value is `c ⟦g⟧ ∣ₛ ⟨(p g).2⟩` (slash by `u` itself, not `u⁻¹` — the
  pleasant mirror); `simp only [hsplit]` before `subtype_slash_mul` (rw-motive trap);
  backward `← subtype_slash_mul` leaves the `hyz` membership as a side bullet —
  closed by `Δ'.mul_mem (hU (SetLike.coe_mem _)) (hU u₀.2)`.)
- **Depends**: S10 | **Type**: theorems | **Leaves**: Q11
- **Sketch**: mirror `heckeOperator_apply_rep` (`HeckeMatrix.lean:49`) with the
  thesis-orientation factorisation hypotheses (`cᵢ·x = d·c_σ·u`, `d ∈ Γ`, `u ∈ U`);
  mirror `evalAtReps`/`bijective_evalAtReps` (`Decomposition.lean:52,111`) for
  `|`-transforming functions.
- **Sources**: [Jac p. 21] display (recorded qmf decomposition.md:260-261); the left
  files (substrate).

### [S12] Quaternionic specialisation seam — Slash/Quaternionic.lean
- **Status**: done (2026-08-06, beastmode; FILE SORRY-FREE.  `levelMonoid'`,
  `levelMonoid'ToSigma0'`, WeightModule slash instance through the corestriction
  (fields need `show`-reduction to the Sigma0'-instance before `exact` — instance
  synthesis stalls otherwise), `etaTensor'`/`etaTensorInv'`/`etaAdelic'` (component
  `(ϖ 0; 0 1)`) + `toMatrix_etaAdelic'`, `SpaceSlash` (classical right-slash
  quaternionic modular forms), `heckeOperatorQSlash`, and **`spaceSlash_eq_space`**
  (the FLT-facing agreement corollary — one-line application of the S09 seam
  theorem).  Axioms standard.
  **S-TRANCHE COMPLETE: all 7 QMF/Slash files sorry-free, 2672 jobs green.**)
- **Depends**: S02, S05, S08, GATE-1 | **Type**: def + API + instance
- **Sketch**: mirror `Quaternionic.lean`: `levelMonoid' := Sigma0'.comap
  (toMatrix F D v)` (`toMatrix` itself reused — it is convention-neutral),
  `levelMonoidToSigma0' := (toMatrix …).submonoidComap _`; `etaAdelic'` mirrors
  `UpiElement.lean:205` with component `(ϖ 0; 0 1)` (thesis form); pull the
  `WeightModule` slash back along `levelMonoidToSigma0'` (RightSlashAction via
  compHom-style def, mirroring `Quaternionic.lean:110`'s SMulCommClass pattern with
  `SMulSlashClass`); define classical-weight quaternionic modular forms
  `L(U, L_{n,ν})` as `levelSubmoduleSlash` at these coefficients — the classical
  right-slash forms space, self-standing deliverable.
- **Also (the FLT-facing agreement corollary, user-requested 2026-08-06)**:
  instantiate the abstract seam theorem (S09) at the quaternionic coefficients —
  under the `detNorm`-dictionary on the level group, the right-slash forms space
  equals the left-action `levelSubmodule` (the FLT-convention space).  This is the
  kernel-checked "both conventions agree" statement at the quaternionic level, and
  the docking point for a future FLT discharge of class-number-one (FLT speaks
  left; the corollary carries its output to the slash side).  The left
  `Quaternionic.lean` is NOT deprecated: it remains the FLT interface and the
  mirror substrate.
- **Sources**: `Quaternionic.lean:84-147`, `UpiElement.lean:205` (mirrors);
  [Buz07 §9] quotes as for S05/S08.
- **Note**: the fork's adelic layer (P12, P14, P16, P20) instantiates THIS file at
  `F = ℚ, D = ℍ[ℚ], v = v₃` instead of building the comap plumbing locally.

### Cleanups (S): [CLEANUP-S1] Slash/Sigma0 after S02 · [CLEANUP-S2] Slash/Basic after S03 ·
[CLEANUP-S3] Slash/WeightModule after S06 · [CLEANUP-S4] Slash/AutomorphicFunction after S09 ·
[CLEANUP-S5] Slash/HeckeMonoid after S10 · [CLEANUP-S6] Slash/HeckeMatrix after S11 ·
[CLEANUP-S7] Slash/Quaternionic after S12

---

## P-tranche port tickets (the fork; one file per ticket)

Common contract for every Pn: create the JacobsSlash file per plan.md's port map
(mode + prefix), port ALL declarations of the original (public surface + private
helpers its proofs need), obeying statement-form rules 1–6.  VERBATIM mode: diff
against the original modulo header/imports/namespace — any other delta is a defect.
MIRROR mode: the ticket's statement-form spec (decomposition Result P) is binding;
proof bodies mirror the original's side-by-side.  Every ticket ends with
`lake build` of the new module + the orientation/diff audit recorded in the status
line.  Each Pn is followed by its per-file [CLEANUP-Pn].

### [P01] `1_PadicAnalytic` ← PadicAnalytic.lean — VERBATIM — dep GATE-1 (may run inside it)
- **Status**: done (2026-08-06, executed inside GATE-1: sed-port `namespace Jacobs →
  JacobsSlash` + docstring qualifiers; diff-audit CLEAN (verbatim modulo namespace);
  builds ✓; runLinter lints identical to the original — inherited, recorded.)
### [P02] `1_GenFun` ← GenFun.lean — VERBATIM — dep GATE-1
- **Status**: done (2026-08-06, beastmode; P01-style sed port, diff-audit CLEAN,
  builds sorry-free, 2160 jobs.)
### [P03] `1_BlockOp` ← BlockOp.lean — VERBATIM — dep GATE-1
- **Status**: done (2026-08-06, beastmode; NOTE the original's namespace is
  `TateFredholm`, not `Jacobs` — ported as `namespace JacobsSlash` + full
  `open TateFredholm` (the original's `open scoped` alone leaves unqualified
  references unresolved).  Builds sorry-free, 2292 jobs.  Statement content
  verbatim.)
### [P04] `3_BinomialTheorem` ← BinomialTheorem.lean — VERBATIM — dep P06
- **Status**: done (2026-08-06; source imports U3Data (not just PadicAnalytic as
  planned) — renumbered 3_ per the prefix rule; builds sorry-free.)
### [P05] `1_SlopeTheorem` ← SlopeTheorem.lean — VERBATIM — dep GATE-1
- **Status**: done (2026-08-06; source imports only TateFredholm — renumbered 1_ per
  the prefix rule; builds sorry-free.)
### [P06] `2_U3Data` ← U3Data.lean — NEAR-VERBATIM (P-D orientation audit) — dep P01, P02
- **Status**: done (2026-08-06, beastmode; ported as `2_U3Data` per the prefix rule
  (imports two level-1 files); guillemet import rewiring; builds sorry-free, 2195
  jobs — the single grep-`sorry` hit is the hClassNumberOne docstring note, present
  identically in the original.)
- **TRANSCRIPTION DECISION (user-raised, settled 2026-08-06)**: the ε/h data STAYS a
  transcription (byte-identical to the left library's — one shared data-entry with
  one provenance/errata trail), NOT derived via the left↔right transport (would
  violate self-enclosure and merely launder the same hand-entry).  The "deduce from
  our computations" content is instead the ACCEPTANCE CRITERION for the
  `U3/Factorisations` + `U3/6_Matrix` ports: prove the transcribed data IS the
  matrix of the genuine `U₃` — twist-free if the thesis orientation permits (P-D
  expectation), recorded scalar otherwise.  The closed forms must exist as terms
  anyway (the whole slopes layer does norm estimates on them), so transcription is
  irreducible; the identification theorem is what makes it trustworthy.
### [P07] `3_Slopes` ← Slopes.lean — VERBATIM — dep P05, P06
- **Status**: done (2026-08-06; builds sorry-free.)
### [P08] `4_SlopeReading` ← SlopeReading.lean — VERBATIM — dep P07 (+ NewtonPolygons)
- **Status**: done (2026-08-06; builds sorry-free.)
### [P09] `5_Instance` ← Instance.lean — VERBATIM — dep P08
- **Status**: done (2026-08-06; builds sorry-free.)
### [P10] `4_DiamondW` ← DiamondW.lean — NEAR-VERBATIM — dep P03, P07
- **Status**: done (2026-08-06; builds sorry-free — all references to the ported
  BlockOp resolved through the fork namespace (no stale `TateFredholm.`-qualified
  refs); Lemma 2.9 residue docstring kept; W-identification stays out (AG-W-ID).
  **ANALYTIC LAYER COMPLETE: 11 fork files, 2644 jobs green, includes
  `charPowerSeries_U3MatrixOp` + both slope readings.**)
### [P11] `3_BaseChange` ← BaseChange.lean — VERBATIM — dep P06
- **Status**: done (2026-08-06; renumbered 3_ (imports 2_U3Data + TateFredholm);
  builds sorry-free.)
### [P12] `U3/1_Setting` ← U3/Setting.lean — MIRROR — dep S02, S12, GATE-1
- `K₃/v₃/ν₃/θ₃/norm_three_lt_one` verbatim; `Σ₁(9)'` native (`d ≡ 1`; mirror of
  `Setting.lean:580-606`); imports `PhD.QMF.Slash.Sigma0` for `Σ₀'`.  No left monoids.
- **Status**: done (2026-08-06, beastmode; sorry-free, native d-form `Sigma1` +
  `sigma1_of_mul_eq_one` + `mem_sigma1_iff`; in every downstream green build).
### [P13] `U3/2_Hurwitz` ← U3/Hurwitz.lean — VERBATIM — dep P12
- **Status**: done (2026-08-06; RENUMBERED `1_Hurwitz` — imports no JacobsSlash
  files, so prefix 1 per the rule; verbatim port, sorry-free.)
### [P14] `U3/3_Level` ← U3/Level.lean — MIRROR — dep P12, P13
- `U₁(9)` with the THESIS congruence (`toMatrix g ∈ Σ₁(9)'` both for `g`, `g⁻¹`);
  `hClassNumberOne'` permanent-sorry contract mirrored (docstring copied + adapted;
  axiom-audit note).
- **Status**: done (2026-08-06, beastmode; RENUMBERED `2_Level` (max import prefix
  1).  `U1_9` d-form + `toMatrix_mem_sigma1_of_mem_U1_9` / `mem_U1_9_of_toMatrix`;
  `HClassNumberOne` + the contracted `hClassNumberOne` sorry at `2_Level:673` —
  the fork's ONLY sorry.)
### [P15] `U3/3_ClassSet` ← U3/ClassSet.lean — MIRROR — dep P14
- **Status**: done (2026-08-06, beastmode; FILE SORRY-FREE, 3413 jobs.  The recorded
  mirror spec below EXECUTED AS DERIVED: row-invariant `(0,1)·red(u⁻¹)`, reps
  `(0,1),(0,5),(0,7)` (= `eᵢ⁻¹`), both `decide` tables (row-orbit 24×72×3 and
  d-form only-one-tuple) confirmed by the kernel; correction `W = u⁻¹·d⁻¹·cᵢ`;
  Thm 2.1 keeps the thesis shape `u = d·cᵢ·w`; Lemma 2.2 stated on
  `stabilizerAtSlash`.  Proof-engineering notes: proof-irrelevant subtype-pair
  conversions via `congr 1` haves (`hpe`-pattern) — needed wherever two membership
  routes give the same `integralMatrices` element; `congrArg redMat (Subtype.ext
  (congrArg toMatrix hui))` for value-level rewrites under `redMat` (raw `rw` hits
  motive errors); triple-`vecMul` collapse must re-associate FIRST
  (`vecMul_vecMul ×2, ← mul_assoc`) before the mul-inv identity; `simp only [hv]`
  (not `rw`) to entry-normalise vecMul hypotheses — `fin_cases` leaves Fin-mk
  wrappers that block `rw`; `maxHeartbeats 1000000` on the two big assembly
  theorems.).
- **Mirror spec (derived + recorded before writing):**
  1. NEUTRAL (verbatim): diagUnit/classDiag/classRep, redMod9/redMat machinery,
     hurwitzToLocal, unitsMod9, tupleMat + exists_unit_iff_exists_tuple,
     primitiveVectors, exists_completion (reusable with roles renamed), ν₃/half
     lemmas, U0-integrality block, redMat mul/inv lemmas, classRep_mem_U0.
  2. VECTOR STORY: the fork's Σ₁ (c≡0, d≡1) reads on the BOTTOM ROW; the class-set
     invariant is `(0,1) · red(u⁻¹)` (bottom row of the reduced INVERSE), invariant
     under u ↦ u·w (w ∈ U₁-fork) and transforming by RIGHT `unitsMod9`-multiplication
     under u ↦ γ⁻¹u.  KEY COMPUTATION: `(0,1)·red(cᵢ⁻¹) = (0, eᵢ⁻¹)` and
     `eᵢ⁻¹ mod 9 = (1, 5, 7)` for e = (1,2,4) — the orbit representatives are rows
     `(0,1),(0,5),(0,7)`, the SAME values as the left story's columns (2·5≡1, 4·7≡1
     mod 9).  Orbit decide-table mirror: ∀ x ∈ primitiveVectors, ∃! i, ∃ t ∈
     unitTuples, `Matrix.vecMul ![0, (![1,5,7] i)] (tupleMat t) = ![x.1, x.2]`.
  3. CORRECTION: from `(0,1)red(u⁻¹) = (0, ẽᵢ)·red(γ')`, set `W := u⁻¹·γ'⁻¹·cᵢ`;
     then `(0,1)·red(W) = (0,1)`, the inverse condition follows by the one-line
     invertibility trick, `W ∈ U₁` via the mem_U1_9_of_redMod9 mirror
     (conditions: (1,0)-entry ↦ 0 — SAME slot as left — and (1,1)-entry ↦ 1), and
     `u = γ'⁻¹ · cᵢ · W⁻¹ = d·cᵢ·w` — **the thesis's Thm 2.1 shape verbatim**.
  4. Row-primitivity: `not_isUnit_det_of_not_isUnit_row` (bottom-row version, decide);
     completion on the top row via the SAME `exists_completion` with arguments
     reordered.
  5. Lemma 2.2 (trivial stabilisers): `only_one_tuple_sigma1` mirror reads
     `(tupleMat t) 1 0 = 0 → (tupleMat t) 1 1 = 1 → t = (2,0,0,0)` (decide);
     diag-conjugation invariance: `(C M C⁻¹)₁₀ = (b/a)·M₁₀` and `(C M C⁻¹)₁₁ = M₁₁`
     — both Σ₁-fork conditions invariant, mirror of `diag_conj_entries`.
  6. FALSE-PATH RECORDED (do not retry): "fork-U₁ = left-U₁ as sets via g ↔ g⁻¹
     mod-9 conditions" is REFUTED by g = diag(4,1) (fork-member, not left-member);
     the det ≡ a (not ≡ d) when d≡1.  The two U₁'s are genuinely different subgroups.
### [P16] `U3/3_EtaDecomposition` ← U3/EtaDecomposition.lean — MIRROR — dep P14
- **Status**: done (2026-08-06, beastmode; FILE SORRY-FREE, 3413 jobs.  `eta3 :=
  etaAdelic'` (component `(3 0; 0 1)`); `etaRep t := eta3 * levelUnip t` — component
  `(3 0; 9t 1)`, THE THESIS'S MATRICES VERBATIM; right cosets via `RightCosets U1_9`
  + `Quotient.mk''`; disjointness via `etaRep t * (etaRep s)⁻¹ = (1 0; 3(t−s) 1)`;
  covering via the d-unit approximation `c/(9d)` (mirror of the left's `c/(9a)`) —
  first-compile; `bijOn_etaRep` in the exact image shape `{η₃}·U₁(9)` that
  `heckeOperatorSlash` consumes.  Slash/Quaternionic gained
  `etaAdelic'_mem_levelMonoid'` + two `toLocal_etaAdelic'_*_ne` lemmas.
  Pleasant find: the fork's `η₃`-conjugation formula `(α β; γ δ) ↦ (α 3β; γ/3 δ)` is
  literally the same map as the left library's — the conjugation lemmas mirror
  verbatim.)
### [P17] `U3/2_Compose` ← U3/Compose.lean — VERBATIM — dep P04
- **Status**: done (2026-08-06; RENUMBERED `1_Compose` — imports no JacobsSlash
  files, prefix 1; verbatim port, sorry-free, consumed by `4_KappaSlash`.)
### [P18] `U3/4_KappaSlash` ← U3/KappaAction.lean — MIRROR — dep P12, P17, S03
- **Status**: done (2026-08-06, beastmode; FILE SORRY-FREE, 3438 jobs, axioms
  standard.  `kappaSlash δ := ofGenFun (weightGenFun t δ.1)` — NO adjParams anywhere
  (def + all API deleted); [Jac Prop 2.6] definitional at δ's own parameters;
  **`kappaSlash_mul : kappaSlash (g·h) = (kappaSlash h).comp (kappaSlash g)`** — the
  right law via the SAME column cocycle instantiated at (δ,γ) := (g.1, h.1), no
  anti-flip, `hadj` collapses to `rfl` — the fork's proof is SIMPLER than the left's;
  `kappaSlashAction : RightSlashAction Sigma1 c(ℕ,K₃)`.  Port notes: the fork
  Σ₀'-tuple positions make the destructuring names (`ha`,`ha1`) bind the mirrored
  (1,1)-facts automatically; the `hγ`-translation layers deleted wholesale; the
  `*_adjParams` wrapper lemma names KEPT (bodies now direct — rename them in
  CLEANUP-P18: they no longer mention adjParams); quadSeries bullet entry-swap
  (param₀₀ ↦ g₀₀); `open TateFredholm JacobsSlash` (bare `Jacobs` survives sed —
  watch in later ports).  CoeffInt (L5.2 correction) carried.)
### [P19] `U3/5_Factorisations` ← U3/Factorisations.lean — MIRROR — dep P15, P16, P18
- **Oracle record** (2026-08-06; **ORACLE COMPLETE AND STORED** at
  `PhD/JacobsSlash/U3/certificate_search.py`, re-verified in place; final Status
  line below).
- **ORACLE RESULTS (binding data for the port)**:
  * Factorisation shape: `classRep i · (etaRep t)⁻¹ = d(i,t) · classRep σ(i,t) · u(i,t)`
    with `u ∈ fork-U₁(9)` — the thesis §B.1 problem, the exact `hfact` shape S11's
    `heckeOperatorSlash_apply_rep` consumes.  UNIQUE hit per pair (9/9).
  * σ-table `(2,1,1),(0,2,2),(1,0,0)` — the thesis's, same as the left library's.
  * d-table: `d = h/3`, h Hurwitz norm-3 — THE THESIS'S OWN GLOBAL FACTORS
    (left library's d's are `3×` these): rows d(0,·) = (−a,b,c)/3-family with
    a = 1+i−j, b = (−1+i+3j+k)/2, c = −(1+3i+j+k)/2 sign-permuted per the table
    in the oracle header; nrd(d) = 1/3 (det bookkeeping: det(cᵢvₜ⁻¹) = CDᵢ/3).
  * **TWIST-FREE IDENTIFICATION (P06 acceptance criterion PASSED at oracle level)**:
    `G' := C_σ⁻¹·θ(d)⁻¹·C_i` (= the θ-params of `(u(i,t)·etaRep t)₃`, NO adjParams)
    equals the transcribed ε-matrices EXACTLY, all nine summands — the left
    library's B15 classWeight coboundary `κ(s)s⁻²` VANISHES in thesis orientation.
    Hence the fork's `sum_weightGenFun_eq_h` carries NO scalar and [Jac p. 28]
    "A = (ε_{i,j})" will hold on the nose.
  * u-components recorded in the oracle output (dets `CDᵢ/(3·CD_σ)·3 = CDᵢ/CD_σ`-family).
- **Status: DONE** (2026-08-06, beastmode; FILE SORRY-FREE, 3443 jobs, all endpoints
  on [propext, Classical.choice, Quot.sound]).  Delivered: fork units `d = ±h/3` with
  `star h`-inverses (`ext <;> norm_num` throughout); oracle-corrected `dTable`
  (t-columns C/B-SWAPPED vs the left's rows — `v_t⁻¹ ~ w_{−t}`); `uCand` +
  `factorisation` (thesis shape, true by construction); nine `toMatrix_uCand`
  literal blocks + nine certificate bundles (36 stamped theorems, all first-compile
  on the derived `linear_combination` coefficients and valuation exponents);
  `uCand_mem` (all nine in `U₁(9)`); **`toMatrix_eq_epsTable` — the TWIST-FREE
  matrix-level identification** (fork ε-assignment is IN-ORDER: t=1↦M1, t=2↦M2);
  **`sum_weightGenFun_eq_h` — the series level with NO scalar and NO weight
  hypothesis** (strictly stronger than the left's B15 form; the whole
  `weightGenFun_smul`/`hd_eps`/`hs_ratio` scalar layer of the left library is
  DELETED).  classDet/cd0-2 kept for P20's convenience.  Port hazards logged: python
  double-escaped replace can silently no-op (verify insertions by grep!);
  `!![...]` takes ONE closing bracket; vector-extraction goals after `fin_cases`
  close by `rfl` after the h-rewrites.
### [P20] `U3/6_Matrix` ← U3/Matrix.lean — MIRROR — dep S10, S11, P18, P19 — **DONE 2026-08-06**
- `kappaForms := levelSubmoduleSlash` (Buzzard verbatim); `heckeU3 :=
  heckeOperatorSlash` at `η₃`; `heckeU3_apply_classRep` in the [Jac p. 21] display
  shape via S11's recipe; `blockOp` from thesis-orientation certificates; coboundary
  scalar (if any survives in thesis orientation — decomposition P-D expects
  simplification) recorded as B15 was.
- **DONE notes** (built green FIRST attempt, 6.8s; axioms: all unconditional
  endpoints [propext, Classical.choice, Quot.sound]; sorryAx ONLY in
  `eval_classRep_injective'` via hClassNumberOne ✓; runLinter: ZERO findings on new
  decls, closure findings pre-existing):
  - **NAME CLASH RESOLVED**: fork 1_BlockOp owns `JacobsSlash.blockOp`, so the
    per-entry operator is `blockEntry` (NOT the left's `blockOp` name):
    `blockEntry t ht i j := ∑ t' ∈ {t' | sigmaTable i t' = j}, kappaSlash t ht
    ⟨toMatrix ((uTable i t')·etaRep t'), …⟩`.
  - `levelMonoid1 := Sigma1.comap (toMatrix ℚ D v₃)`; eta3/etaRep memberships;
    `levelMonoid1ToSigma1 := (toMatrix …).submonoidComap Sigma1`.
  - `kappaLevelSlashAction` (@[instance_reducible], letI-style — IDE linter demanded
    the attribute, it exists and works) = pullback of kappaSlashAction; SMulSlash
    via `map_smul (kappaSlash …)` directly (NO Sigma1-level SMulSlashClass needed).
  - `kappaForms := slashFixedPointsOfLE K₃ (AutomorphicFunction …) U1_9_subset_levelMonoid1`;
    `heckeU3 := heckeOperatorSlash K₃ hU hU eta3_mem finite_image_eta3`.
  - **TWIST-FREE CONFIRMED AT ENDPOINT**: `matrixCoeff_blockEntry` = coeff of the
    h-matrix directly (diagonal via sigmaTable_ne + empty filter);
    `blockEntry_eq_epsOp` EXACT (funext + ext_matrixCoeff + fin_cases + simp with
    the six matrixCoeff_epsOp lemmas); `charPowerSeries_blockEntry_eq_U3MatrixOp`
    proof = `rw [blockEntry_eq_epsOp]; rfl` (U3MatrixOp is definitionally blockOp
    of the eps-matrix — the left's twist-conjugation bridge DELETED, nothing
    replaces it because nothing is needed).
  - `heckeU3_apply_classRep` via S11 apply_rep at (etaRep, bijOn_etaRep,
    etaRep_injective, dTable_mem, uTable, hfact := uTable_coe▸factorisation) +
    private `sum_kappaSlash_eq_sum_blockEntry` (Finset.sum_fiberwise regroup;
    `key.trans` closes by defeq through the letI instances — no `show` massage
    needed).  `eval_classRep_injective` via Subtype.ext + AutomorphicFunction.ext +
    exists_classRep_factorisation + calc through slash_apply_mul (calc avoids the
    rw-vs-subtype-coe matching trap).  Deprecation: use bare `sum_apply`, not
    `ContinuousLinearMap.sum_apply`.
### [P21] `U3/7_Fredholm` ← U3/Fredholm.lean — MIRROR — dep P20 — **DONE 2026-08-06**
- `evalU3` via right `evalAtReps`; `charPowerSeriesU3` = `det(1 − T·U₃)`;
  compactoid + model-equiv under `hcn'`.
- **DONE notes** (green FIRST attempt, 7.2s; ZERO warnings in-file; axioms: all
  seven endpoints [propext, Classical.choice, Quot.sound] — hcn is a hypothesis,
  so NO sorryAx anywhere in this file; runLinter: zero new findings):
  - `instance : IsTate K₃` declared here (fork had none; mirrors left).
  - `evalU3`/`blockProj_evalU3`/`kappaFormsModelEquiv` verbatim-mirror;
    `bijective_evalU3` surjectivity via S11 `bijective_evalAtRepsSlash` +
    `exists_classRep_section` + `stabilizerAt_classRep = ⊥` (the ∀-p subtype-mk
    rewrite trick ports unchanged, `one_smul` → `slash_one`).
  - `evalU3_heckeU3` = P20's `heckeU3_apply_classRep` + `blockOp_blockIncl` +
    `Finset.sum_comm` — statement `blockOp (blockEntry t ht)` (JacobsSlash.blockOp).
  - **TWIST-FREE PAYOFF**: left's private `isCompactoid_smul` DELETED (nothing
    replaces it — no scalars to close under); `isCompactoid_blockOpU3` is
    `blockEntry_eq_epsOp` + `isCompactoid_blockOp` + the six
    `isCompactoid_epsOpXY` + `isCompactoid_zero_clm` directly.
  - `charPowerSeriesU3_eq_U3MatrixOp := charPowerSeries_blockEntry_eq_U3MatrixOp`.
  - 2_U3Data's stale doc cross-refs fixed (`JacobsSlash.U3.*` → flat
    `JacobsSlash.*`, module names → «7_Fredholm»/«8_HeckeSlopes»).
### [P22] MILESTONE `U3/8_HeckeSlopes` ← U3/HeckeSlopes.lean — MIRROR — dep P21, P11, CLEANUP-ALL-1 — **DONE 2026-08-06**
- Factorisation over admissible `(L, f, ω)` + the `L₃` witness; end state: [Jac
  Cor 2.16] about the fork's `U₃`, sorry-free except `hClassNumberOne'` in
  `'`-forms.
- **DONE notes** (green FIRST attempt, 7.1s, 3504 jobs; zero in-file warnings;
  runLinter zero findings; axioms: `map_charPowerSeriesU3`,
  `charPowerSeriesU3_factorisation`, `charPowerSeriesU3_factorisation_L₃`,
  `ω₃_sq_add_ω₃_add_one`, `norm_ι₃` ALL exactly
  [propext, Classical.choice, Quot.sound] — the whole factorisation chain is
  UNCONDITIONAL, no hcn, no sorryAx):
  - Near-verbatim mirror of left U3/HeckeSlopes.lean with `Jacobs.`-prefixes
    dropped (fork names bare in namespace JacobsSlash) and `_root_.TateFredholm.
    matrixCoeff_blockOp` → bare `matrixCoeff_blockOp` (1_BlockOp owns it).
  - Abstract layer over any complete ultrametric (L, f isometric, ω): transport
    lemmas + `map_charPowerSeriesU3` (via P21 bridge + TateFredholm.
    charPowerSeries_map + 3_BaseChange map_h layer) +
    `charPowerSeriesU3_factorisation` (+ 4_DiamondW charPowerSeries_U3MatrixOp).
  - Concrete `L₃ := CyclotomicField 3 K₃` wrapper + spectral-norm instances +
    `ι₃`/`ω₃` + the L₃-witnessed factorisation — [Jacobs, Cor 2.16] about the
    fork's genuine `U₃`.  **FORK ENDGAME COMPLETE.**

### Cleanups (P): per-file [CLEANUP-P01]…[CLEANUP-P21] after each port ticket
(VERBATIM ports: light pass — header/name hygiene only, the content was already
cleaned on the jacobs boards).  [CLEANUP-ALL-1] after all of P01–P21 + S-chain,
blocks P22 — **DONE 2026-08-06**: (a) warning sweep — Slash/Basic `ofAntiHom`
@[instance_reducible] added; Slash/WeightModule dead `<;> ring` dropped; 1_Setting
`_h2` binder; 5_Factorisations 24 unused simp args removed (line-targeted sed —
24 sites share the pattern text, only 18+6 flagged/legit, blanket replace unsafe);
(b) 4_KappaSlash `*_adjParams` wrapper renames → `*_sigma1*`
(norm_sigma1_entry_le_one, norm_sigma1_lower_right(_sub_one_le),
norm_sigma1_lower_left_le, norm_sigma1_ratio_le, sigma1_lower_right_ne_zero,
coeffLeOne_mobius_sigma1, absSummable_{linX_inv,mobius,kappaCol}_sigma1) + five
docstring rewords; `adjParams`/`adjParams_apply`/`adjParams_mul` KEPT (load-bearing
in the cocycle proof); (c) runLinter zero-residual pass on all MIRROR/new files:
docstrings added (qj, qk, theta, classRep), redundant @[simp] dropped
(coeff_yCoeff_kappaSeries₂; ten of twelve dX_star_* — dA_star_imI + dB_star_imJ
keep theirs, linter-verified); (d) VERBATIM-port lints (1_BlockOp, 2_U3Data,
3_Slopes unused-args etc.) inherited from originals, RECORDED NOT FIXED per the
verbatim parity contract; TateFredholm/ForMathlib findings out of scope (other
boards' property).  Full rebuild green (3488 jobs), only 2_Level:673 contracted
sorry remains in fork warnings.  [CLEANUP-FINAL] after P22: `/cleanup-all` + axiom audit
(`#print axioms` on the fork's `heckeU3_apply_classRep` and
`charPowerSeriesU3_factorisation_L₃`-analogue: exactly
`[propext, Classical.choice, Quot.sound]` + `hClassNumberOne'`-sorry only in
`'`-forms) + write `PhD/JacobsSlash/PROGRESS.md` (the fork's own map).
**CLEANUP-FINAL DONE 2026-08-06**: cleanup substance discharged by the ALL-1
zero-residual pass (nothing new to sweep — 6/7/8 ports produced zero warnings);
full-fork final build GREEN (both leaves `U3.«8_HeckeSlopes»` + `«5_Instance»` =
all 22 modules, 3525 jobs, single warning = the contracted `2_Level:673` sorry);
consolidated axiom audit PASSES THE CONTRACT EXACTLY —
`heckeU3_apply_classRep` and `charPowerSeriesU3_factorisation_L₃` (and the whole
factorisation chain, `matrixCoeff_blockEntry`, `blockEntry_eq_epsOp`,
`evalU3_heckeU3`, `isCompactoid_blockOpU3`, `map_charPowerSeriesU3`,
`bijective_evalU3`, `kappaFormsModelEquiv`) on exactly
[propext, Classical.choice, Quot.sound]; sorryAx ONLY in
`eval_classRep_injective'` via `hClassNumberOne` (its sole term-level consumer);
`PhD/JacobsSlash/PROGRESS.md` WRITTEN (fork map + conventions + axiom contract +
file table).  **BOARD COMPLETE — all tickets S-SKEL…S12, GATE-1, P01–P22,
CLEANUP-ALL-1, CLEANUP-FINAL are DONE.**

---

# PHASE 2 ticket board (2026-08-06): Wave W (AG-W-ID) + Wave E (eigenvalue endgame)

Phase 1 (S + P tranches) COMPLETE above.  Common contract: fork constraints hold
(self-enclosed; never import PhD.Jacobs; read left files for mirroring only).  Every
Lean ticket ends with `lake build` of its module + axiom spot-check; runLinter gate on
new files.  Oracle verdicts (W01) are BINDING on downstream statements — the P19
pattern: the ticket records the verdict before the Lean statement is committed.

### [W01] Fork W-oracle: right-coset certificates + twist verdict
- **Status**: done (2026-08-06, beastmode; **ORACLE COMPLETE AND STORED** at
  `PhD/JacobsSlash/U3/certificate_search_w.py`, all validations pass, unique hit
  per class over 312 deduped candidates.  **BINDING RESULTS**: trap confirmed
  (diag(1,4) ∉ fork-U₁(9), diag(4,1) ∈ — the handedness flip); **σ_W = (1,2,0)**
  (same cycle as left — the acting product cancels μ, so the cycle survives the
  μ→μ⁻¹ flip); **d_W = (−1,−1,+1)** central signs; **u(i) at 3 =
  diag(−1/5,−1/8), diag(−5/7,−1/8), diag(7,1)** (rational diagonal, ν-free, det
  3-units 1/40, 5/56, 7); acting θ(u(i)·μ) = diag(−1/5,−1/2), diag(−5/7,−1/2),
  diag(7,4) = the thesis δ01/δ12/δ20 pairs EXACTLY.  **TWIST VERDICT:
  TWIST-FREE** — W06 takes the scalar-free branch (`kappaSlashWide(acting i) =
  deltaOf i` exact; no fork classWeight def needed).  Dedup note: the norm-9/3
  candidate set contains 3·(unit)/3 overlaps; the left oracle shares this
  benign duplication.)
- **File**: PhD/JacobsSlash/U3/certificate_search_w.py (new; fork mirror of the left oracle)
- **Depends on**: none
- **Parallel**: yes
- **Type**: oracle (no Lean)

#### Task
Port `PhD/Jacobs/U3/certificate_search_w.py` (validated left run 2026-08-06) to the
fork conventions of `PhD/JacobsSlash/U3/certificate_search.py` (same θ/classRep/U19
code, d-form congruence).  Compute, for each `i : Fin 3`, the RIGHT-coset
factorisation demanded by S11's `heckeOperatorSlash_apply_rep`:

    classRep i · μ⁻¹ = d · classRep σ(i) · u,   u ∈ U₁(9)  (d-form: u₃ ≡ (∗ ∗; 0 mod 9, 1 mod 9))

with **μ = diag(1,4) at 3** — the THESIS'S OWN element.  Handedness pin (mirror of
the jacobs-endgame adversarial finding, decomposition.md:339-345): in the fork's
d-form `U₁(9)` the trap element is `diag(4,1)` (d-entry 1 ⇒ lies in U₁(9) ⇒ trivial
coset); verify `diag(1,4) ∉ U₁(9)` and `diag(4,1) ∈ U₁(9)` explicitly in the
validation block.
Outputs (stored as the results header, board-noted):
1. `σ_W : Fin 3 → Fin 3` (expected: the inverse 3-cycle of the left's (1,2,0),
   because the factorisation is at μ⁻¹ — DO NOT assume; compute),
2. `d_W` (central signs) with nrd bookkeeping (det μ = 4 is a 3-unit — no clearing),
3. the three `u(i)` (expected rational diagonal, ν-free) + their d-form Σ₁(9) checks,
4. acting matrices `θ₃(u(i)·μ)` — RIGHT-handed, NO adjParams — as diag(a,d) literals,
5. **TWIST VERDICT**: compare each acting diag against the transcribed δ-arguments
   (`D ∈ {2/5, 10/7, 7/4}`, thesis (a,d)-data `(−1/5,−1/2), (−5/7,−1/2), (7,4)` up to
   the σ-relabelling) — is the fork acting matrix the thesis data ON THE NOSE
   (twist-free, the AG-B outcome) or off by the `classDet σ(i)/classDet i` coboundary
   (the left outcome)?  Record `TWIST-FREE: yes/no` + the per-i scalars if any.
6. uniqueness: exactly one hit per class over the 312 candidates.

#### Sources
- Left oracle `PhD/Jacobs/U3/certificate_search_w.py` (docstring quoted in full in
  this session's log); jacobs-endgame `decomposition.md:329-420` (§AG-W-ID: computed
  data, validation list); fork oracle `PhD/JacobsSlash/U3/certificate_search.py`
  (conventions + Lean-literal emitter to reuse).

### [W02] `Binvop_comp_Wop_comp_Bop`: B diagonalises the transcribed diamond operator
- **Status**: done (2026-08-06, beastmode parallel worker; ω-assignment FLIPPED per the WI6
  protocol — entry (1,1) computes to `ω`, statement fixed to `diag(1, ω·1, ω²·1)`;
  E03/E04 inherit the flip: block 1 = ω-eigenblock, block 2 = ω²-eigenblock of this `B`)
- **Progress**: appended after `lemma210` (4_DiamondW.lean:1243, docstring records the
  statement-fix).  Proof mirrors lemma210's route with an operator-level collapse: unfold
  `Binvop/Bop/Wop/δ`'s + `ContinuousLinearMap.smul_comp` + `blockOp_comp`, then a local
  `hcore` (`D(7/4)∘(D(2/5)∘D(10/7)) = 1` via `diagOp_comp`/`diagOp_eq_id`) together with
  `diagOp_710_comp_107`/`diagOp_74_comp_47` turns every surviving entry term into
  `scalar • id`; `ext_matrixCoeff` + `fin_cases` + 9 `linear_combination` certificates over
  hA (`κ(4)κ(1/4)=1`), hB (`κ(−2)κ(−1/2)=1`), hC (`κ(−1/2)²κ(4)=1`), hω, hω3.
  **Flip evidence (goal-level probe, protocol step)**: entry (1,1) LHS scalar sum =
  `ω⁴·κ(−1/2)²κ(4) + ω·κ(−2)κ(−1/2) + ω·κ(4)κ(1/4)` = 3ω, not 3ω²; conceptually
  `κ(−1/2)² = κ(1/4)` makes column `r` of the transcribed `B` a genuine `ω^r`-eigenvector
  of `W`.  `lake build PhD.JacobsSlash.«4_DiamondW»` green (2319 jobs, no new warnings);
  `#print axioms JacobsSlash.Binvop_comp_Wop_comp_Bop` = [propext, Classical.choice,
  Quot.sound].
- **File**: PhD/JacobsSlash/4_DiamondW.lean (append, Diagonalisation section)
- **Depends on**: none
- **Parallel**: yes
- **Type**: lemma (generic K — transcription level, no certificates)

#### Statement
```lean
/-- **`B` diagonalises the diamond operator** [Jacobs, Lemma 2.9 reading]:
`B⁻¹·W·B = diag(1, ω²·1, ω·1)` — block `1` (the `M₂,₂` slot) is the `ω²`-eigenblock,
block `2` the `ω`-eigenblock.  With `lemma210` this makes "`M₂,₂` is the restriction
of the `U₃`-matrix to the `ω²`-eigenblock of the diamond operator" a theorem about
the transcribed matrices. -/
theorem Binvop_comp_Wop_comp_Bop :
    (Binvop ω h3 ht hω).comp ((Wop h3 ht).comp (Bop ω h3 ht hω))
      = blockOp
          ![![1, 0, 0],
            ![0, ω ^ 2 • (1 : c(ℕ, K) →L[K] c(ℕ, K)), 0],
            ![0, 0, ω • (1 : c(ℕ, K) →L[K] c(ℕ, K))]] := by sorry
```
(Section variables of the Diagonalisation section: `ω h3 ht hω` — same pack as
`lemma210` minus `hνc`; `Wop` takes `(h3 ht)`.)

#### Proof sketch
Mirror `lemma210`'s route (4_DiamondW:1203-1211): `simp only [Binvop, Bop, Wop,
ContinuousLinearMap.smul_comp, blockOp_comp]`, then `ext_matrixCoeff`, then
`fin_cases` on the two block indices.  Per entry the cancellation is the
ω-DFT computation: columns of `B` are `(1, ω^r, ω^{2r})`-vectors, `Wop`'s blocks are
the δ-operators at the cyclic layout, and the geometric identities `1 + ω + ω² = 0`
(from `hω`, via `linear_combination`/`ring_nf` as in `lemma210`'s entry bullets)
collapse each off-diagonal entry and produce the scalars `(1, ω², ω)` on the
diagonal.  **ω-assignment pin** (jacobs-endgame WI6): the scalar order `(1, ω², ω)`
is the DFT-orientation matching U3Data's "ω²-eigenblock" naming for block 1 = M₂,₂;
the worker hand-checks entry `(1,1)` FIRST — if the computed scalar is `ω` not `ω²`,
the fix is swapping the two scalars in the STATEMENT (a recorded statement-fix, not
a proof bug); re-check E03's Wop-clause then uses the matching power.

#### Mathlib/project lemmas needed
`ext_matrixCoeff`, `matrixCoeff_blockOp` (1_BlockOp:649, @[simp]), `blockOp_comp`
(used by lemma210's simp — verified in its proof text), the δ/B `matrixCoeff`
computation lemmas already consumed by `lemma210` (same file), `hω`-identities.

#### Sources
- Left skeleton `PhD/Jacobs/U3/DiamondHecke.lean:233-245` (statement, verbatim
  shape); jacobs-endgame decomposition WI6 (ω-assignment + flip protocol);
  [Jac Lemma 2.9, p. 32].
- Source line-count anchor: `lemma210` (same computation class) is ~92 lines; expect
  the same order.

#### Generality decision
Generic `K` (the file's section: NontriviallyNormedField, IsUltrametricDist,
CompleteSpace, CharZero) — transcription level, no K₃ content.

### [W03] `U3/7_DiamondHecke.lean` part 1: the wide monoid `Σ₁(3)` and the wide κ-slash
- **Status**: done (2026-08-06, beastmode parallel worker; all W03 skeleton statements landed verbatim — Σ₁(3) + wide κ-slash + cocycle in U3/7_DiamondHecke.lean, build green, endpoints axiom-clean)
- **Progress**: file created (449 lines, module `PhD.JacobsSlash.U3.«7_DiamondHecke»`, sole import `U3.«6_Matrix»`).  Pack landed as THREE hypotheses (`∀ i j, ‖γ i j‖ ≤ 1`, `‖γ 1 1 − 1‖ ≤ ‖3‖`, `‖γ 1 0 / γ 1 1‖ ≤ ‖3‖²`) on `coeffInt_weightGenFun'` / `shiftInt_weightGenFun'` / `tendsto_coeff_weightGenFun'` — the skeleton's 4th member `g₁₁ ≠ 0` is derivable (`‖g₁₁‖ = 1` via `norm_eq_one_of_norm_sub_one_lt_one`) and never consumed by the 4_KappaSlash proofs, so dropped.  No statement adjustments (one proof-term substitution: `Submonoid.comap_mono` absent in this mathlib → explicit `mem_comap` route for `levelMonoid1_le_levelMonoid1₃`).  Extras: `γ₉_le_γ₃`, `mem_sigma1₃_iff`, and the `_sigma1₃` extraction family (`coeffLeOne_mobius_sigma1₃`, `absSummable_{linX_inv,mobius,kappaCol,autFactor,yCoeff_weightGenFun}_sigma1₃`, `autFactor_cocycle_sigma1₃`, `yCoeff_weightGenFun_mul_sigma1₃`) mirroring 4_KappaSlash's `_sigma1` layer — the generic cocycle underliers (`kappaCol_cocycle`, `compAn_mobius_mobius`, `yCoeff_weightGenFun`) needed no changes, confirming the Σ₁-width analysis.  Gates: `lake build PhD.JacobsSlash.U3.«7_DiamondHecke»` green (3454 jobs); `#print axioms` on `kappaSlashWide_mul` / `kappaSlashWide_restrict` → `[propext, Classical.choice, Quot.sound]`.  W04 unblocked.
- **File**: PhD/JacobsSlash/U3/7_DiamondHecke.lean (NEW; imports U3.«6_Matrix»)
- **Depends on**: none (file creation; W01 not needed)
- **Parallel**: yes (with W01, W02)
- **Type**: def + API

#### Statement (skeleton — d-form mirrors of the left DiamondHecke.lean:49-71 + the wide κ)
```lean
/-- The tame threshold `v(3)`. -/
def γ₃ : WithZero (Multiplicative ℤ) := (Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ)

theorem γ₃_lt_one : γ₃ < 1 := by sorry
theorem valued_three_eq_γ₃ : Valued.v (3 : K₃) = γ₃ := by sorry

/-- The wide acting monoid `Σ₁(3)`: `Σ₀'`-integrality at level `9`, but the `1`-unit
condition on the `(1,1)`-entry only mod `3` — the honest domain of the κ-analytics. -/
def Sigma1₃ : Submonoid (Matrix (Fin 2) (Fin 2) K₃) where
  carrier := {g | g ∈ Sigma0' K₃ γ₉ γ₉_lt_one ∧ Valued.v (g 1 1 - 1) ≤ γ₃}
  one_mem' := by sorry
  mul_mem' := by sorry

theorem sigma1_le_sigma1₃ : Sigma1 ≤ Sigma1₃ := by sorry
noncomputable def levelMonoid1₃ : Submonoid (Dfx ℚ D) := Sigma1₃.comap (toMatrix ℚ D v₃)
theorem levelMonoid1_le_levelMonoid1₃ : levelMonoid1 ≤ levelMonoid1₃ := by sorry
theorem U1_9_subset_levelMonoid1₃ : (U1_9 : Set (Dfx ℚ D)) ⊆ levelMonoid1₃ := by sorry

-- the five norm workhorses at the wide threshold (statements as the `*_sigma1*`
-- family of 4_KappaSlash:1275-1325, with `Sigma1₃` and NO γ₉→γ₃ weakening step):
theorem sigma1₃_lower_right_ne_zero (g : Sigma1₃) : g.1 1 1 ≠ 0 := by sorry
theorem norm_sigma1₃_entry_le_one (g : Sigma1₃) : ∀ i j : Fin 2, ‖g.1 i j‖ ≤ 1 := by sorry
theorem norm_sigma1₃_lower_right_sub_one_le (g : Sigma1₃) :
    ‖g.1 1 1 - 1‖ ≤ ‖(3 : K₃)‖ := by sorry
theorem norm_sigma1₃_lower_right (g : Sigma1₃) : ‖g.1 1 1‖ = 1 := by sorry
theorem norm_sigma1₃_lower_left_le (g : Sigma1₃) : ‖g.1 1 0‖ ≤ ‖(3 : K₃)‖ ^ 2 := by sorry
theorem norm_sigma1₃_ratio_le (g : Sigma1₃) :
    ‖g.1 1 0 / g.1 1 1‖ ≤ ‖(3 : K₃)‖ ^ 2 := by sorry

/-- The weight-`κ` operator of a wide element — the SAME `ofGenFun` formula as
`kappaSlash` (the fork's advantage: no def-hole, cf. the left plan's WI3). -/
noncomputable def kappaSlashWide (t : K₃) (ht : ‖t‖ < 1) (g : Sigma1₃) :
    c(ℕ, K₃) →L[K₃] c(ℕ, K₃) := sorry  -- ofGenFun (weightGenFun t g.1) ⟨1, …⟩ (tendsto …)

theorem matrixCoeff_kappaSlashWide (t ht) (g : Sigma1₃) (j i : ℕ) :
    matrixCoeff (kappaSlashWide t ht g) j i
      = MvPowerSeries.coeff (idx j i) (weightGenFun t g.1) := by sorry

/-- Restriction compatibility — proof-irrelevance-trivial in the fork. -/
theorem kappaSlashWide_restrict (t ht) (g : Sigma1) :
    kappaSlashWide t ht ⟨g.1, sigma1_le_sigma1₃ g.2⟩ = kappaSlash t ht g := by sorry

theorem kappaSlashWide_mul (t ht) (g h : Sigma1₃) :
    kappaSlashWide t ht (g * h)
      = (kappaSlashWide t ht h).comp (kappaSlashWide t ht g) := by sorry
```

#### Proof sketch
1. `γ₃` facts: `decide`-free order computation in `WithZero (Multiplicative ℤ)`
   (mirror `γ₉_lt_one`'s proof in 1_Setting); `valued_three_eq_γ₃` from the fork's
   `Valued.v (3 : K₃)` computation (1_Setting:556 pattern).
2. `Sigma1₃` monoid: mirror `Sigma1`'s `one_mem'`/`mul_mem'` (1_Setting:592-625)
   with γ₉→γ₃ in the last conjunct; the multiplicativity step for the (1,1)-entry
   is the same `map_add_eq_of_lt_right` computation (`d₁d₂ − 1 = d₁(d₂−1) + (d₁−1)`
   with both summands ≤ γ₃).
3. Inclusions: `γ₉ ≤ γ₃` (`v(9) ≤ v(3)`) + `Iff.rfl`-membership.
4. The five workhorses: copy the `*_sigma1*` proofs of 4_KappaSlash:1275-1325
   REMOVING the `hγ9le3` weakening (the wide hypothesis is already at `v(3)`).
5. `kappaSlashWide := ofGenFun (weightGenFun t g.1) …` — the two `ofGenFun` inputs
   are wide restatements of `norm_coeff_weightGenFun_le_one` and
   `tendsto_coeff_weightGenFun` (4_KappaSlash, consumed at :396-399).  ROUTE
   (binding): state primed generic versions in THIS file over the explicit
   hypothesis pack (entries ≤ 1, `‖d−1‖ ≤ ‖3‖`, `‖c/d‖ ≤ ‖3‖²`, `d ≠ 0`) by
   copying the two proofs from 4_KappaSlash with the `*_sigma1*` calls replaced by
   pack hypotheses; instantiate at `Sigma1₃` via items 4.  Do NOT edit 4_KappaSlash.
6. `matrixCoeff_kappaSlashWide := matrixCoeff_ofGenFun _ _ _ j i` (the
   4_KappaSlash:404-407 pattern verbatim).
7. `kappaSlashWide_restrict`: both sides are `ofGenFun (weightGenFun t g.1) _ _`;
   `ext_matrixCoeff` + both `matrixCoeff_ofGenFun`s (proof-irrelevance of the
   bundled hypotheses).
8. `kappaSlashWide_mul`: mirror `kappaSlash_mul` (4_KappaSlash — the column-cocycle
   consumption) with the wide workhorses; per the P18 notes the proof consumes the
   cocycle directly (`hadj = rfl` fork pattern).

#### Mathlib/project lemmas needed
`ofGenFun`/`matrixCoeff_ofGenFun` (1_GenFun), `weightGenFun`, the 4_KappaSlash
cocycle layer (compAn/mobius interface — all named in its `kappaSlash_mul` proof),
`map_add_eq_of_lt_right` (1_Setting's Sigma1 route), `Submonoid.mem_comap`.

#### Sources
- Left skeleton DiamondHecke.lean:47-71 + :142-165 (statement shapes); jacobs-endgame
  §AG-W-ID "The one API gap (Σ₁-width)" (quoted in plan.md Phase 2); fork
  4_KappaSlash:294/345/1286 (the three `hγ9le3` sites — the evidence the analytics
  need only mod 3); 4_KappaSlash:1275-1325 (the five workhorses to widen).
- LOC anchor: the five workhorses are ~50 lines in 4_KappaSlash; the two ofGenFun
  inputs and the cocycle consumption are the bulk — expect ~250-450 LOC mirror.

#### Generality decision
`K₃`-level (the wide monoid is a `K₃`-object); the primed `weightGenFun` bound
lemmas stated over the explicit hypothesis pack (maximal within this file's scope).

### [W04] μ₃ = diag(1,4): the adelic element, normalisation, single right coset
- **Status**: done (2026-08-06, beastmode orchestrator after the W-chain worker died
  on credits; in 7_DiamondHecke.lean, green, zero warnings.  **ROUTE IMPROVEMENT over
  the ticket sketch**: `mu3 := unitAt ℚ D v₃ (diagUnit 1 4 …)` — the same machinery
  `classRep` uses (QMF/UpiElement:258 + 3_ClassSet:66) — instead of the ticket's
  `central-4 × etaAdelic'(4⁻¹)`; that makes `toMatrix_mu3`/`toMatrix_mu3_inv` one-line
  (`toMatrix_unitAt` + `diagUnit_val/_inv`) and away-from-3 triviality literally
  `toLocal_unitAt_ne`.  Also landed: `norm_four_eq_one`, `valued_four_eq_one`,
  `valued_inv_four_eq_one`, `conj_mu3_entries` ((a b; c d) ↦ (a b/4; 4c d)),
  `toMatrix_conj_mu3`, `mu3_mul_mem_U1_9` (via `mem_U1_9_of_toMatrix`; away-from-3 by
  toLocal triviality, at 3 by the entry table — note `integralMatrices` is NORM-valued
  so the Σ₁ Valued.v facts convert through `Valued.toNormedField.norm_le_one_iff`),
  `bijOn_muRep` + `finite_image_mu3` (Fin 1 family), `mu3_mem_levelMonoid1₃` (with the
  recorded NON-membership in the narrow monoid: v(4−1) = v(3) = γ₃ > γ₉).
  Traps: `four_ne_zero` needs a `NeZero 4` instance — use `(by norm_num)`;
  `Matrix.dotProduct` is root-level `dotProduct`; `RightCosets` needs
  `open AbstractHeckeOperatorSlash`.)
- **File**: PhD/JacobsSlash/U3/7_DiamondHecke.lean
- **Depends on**: W03
- **Parallel**: after W03, parallel with W02/W01
- **Type**: def + lemmas

#### Statement (skeleton)
```lean
/-- `4` as a central unit of `D`. -/
noncomputable def fourUnit : Dˣ :=
  Units.map (algebraMap ℚ D).toMonoidHom (Units.mk0 4 (by norm_num))

theorem invFour_ne_zero : ((4 : K₃)⁻¹) ≠ 0 := by sorry

/-- The adelic diamond element: the THESIS'S `μ = diag(1,4)` at `3` (no adjugate
transport in the fork), `1` elsewhere — central `4` times `etaAdelic'` at `4⁻¹`. -/
noncomputable def mu3 : Dfx ℚ D :=
  unitsIncl ℚ D fourUnit * etaAdelic' ℚ D v₃ ((4 : K₃)⁻¹) invFour_ne_zero

theorem toMatrix_mu3 : toMatrix ℚ D v₃ mu3 = Matrix.of ![![1, 0], ![0, 4]] := by sorry
theorem mu3_mem_levelMonoid1₃ : mu3 ∈ levelMonoid1₃ := by sorry

/-- `μ` normalises `U₁(9)` (right-coset orientation): conjugation scales the
off-diagonals by the `3`-unit `4^{±1}` and fixes both congruences. -/
theorem mu3_mul_mem_U1_9 {u : Dfx ℚ D} (hu : u ∈ U1_9) : mu3 * u * mu3⁻¹ ∈ U1_9 := by
  sorry

theorem finite_image_mu3 :
    (((Quotient.mk'' : Dfx ℚ D → RightCosets U1_9) ''
      (({mu3} : Set (Dfx ℚ D)) * (U1_9 : Set (Dfx ℚ D)))) :
      Set (RightCosets U1_9)).Finite := by sorry

/-- `U₁(9)·μ·U₁(9)` is the single right coset `U₁(9)·μ`: the `Fin 1` family `_ ↦ μ`
is a bijective system of representatives. -/
theorem bijOn_muRep :
    Set.BijOn (Quotient.mk'' : Dfx ℚ D → RightCosets U1_9)
      (Set.range (fun _ : Fin 1 => mu3))
      (((Quotient.mk'' : Dfx ℚ D → RightCosets U1_9) ''
        (({mu3} : Set (Dfx ℚ D)) * (U1_9 : Set (Dfx ℚ D)))) :
        Set (RightCosets U1_9)) := by sorry
```

#### Proof sketch
1. `toMatrix_mu3`: `map_mul` + `toMatrix_unitsIncl` (5_Factorisations has the
   pattern) + `toMatrix_etaAdelic'` (Slash/Quaternionic) + the central-scalar
   collapse `4 • diag(4⁻¹, 1) = diag(1, 4)` (`Matrix` `smul`/`of` simp).
2. `mu3_mem_levelMonoid1₃`: `mem_comap` + `toMatrix_mu3`; `diag(1,4)` checks:
   entries integral, `v(c)=0 ≤ γ₉` ✓, `v(d)=v(4)=1` ✓, `det = 4 ≠ 0` ✓, and the
   WIDE congruence `v(1 − 1) = 0 ≤ γ₃` ✓ — mirror `eta3_mem_levelMonoid1`'s bullet
   list (6_Matrix:70-82).  NOTE the narrow monoid REJECTS μ (`v(4−1) = v(3) = γ₃ >
   γ₉`) — that rejection is the whole reason `Σ₁(3)` exists; record it as a
   comment, not a lemma.
3. `mu3_mul_mem_U1_9`: away from 3, `mu3` is the central 4 times a unit trivial at
   `w ≠ v₃` (`toLocal_etaAdelic'_ne`, Slash/Quaternionic — the 3_EtaDecomposition
   :283-318 pattern) so conjugation is identity there; at 3,
   `diag(1,4)·(a b; c d)·diag(1,4⁻¹) = (a, b/4; 4c, d)` — `c ≡ 0 mod 9` is
   preserved by the 3-unit `4`, `d ≡ 1` untouched, integrality of `b/4` by
   `v(4)=1`; close by `mem_U1_9_of_toMatrix` (2_Level:639).
4. `bijOn_muRep`: surjectivity — for `mu3·u` in the image,
   `mk'' (mu3·u) = mk'' mu3` since `(mu3·u)·mu3⁻¹ = mu3·u·mu3⁻¹ ∈ U₁(9)` by item 3
   (`QuotientGroup.rightRel_apply`); injectivity on a `Fin 1`-range is trivial
   (`Set.injOn_singleton`-style); mapsTo direct.  `finite_image_mu3` from
   `bijOn_muRep.image_eq ▸ (Set.finite_range _).image _` (the
   3_EtaDecomposition:511-516 pattern verbatim).

#### Mathlib/project lemmas needed (locations pre-verified 2026-08-06)
`toMatrix_unitsIncl` (5_Factorisations:271), `etaAdelic'` (Slash/Quaternionic:117,
args `(F D v) ϖ hϖ0`-shape as in 3_EtaDecomposition:60), `toMatrix_etaAdelic'`
(Slash/Quaternionic:125, full-args call shape at :140),
`etaAdelic'_mem_levelMonoid'` (:137), `toLocal_etaAdelic'_ne`/`_inv_ne`
(:144/:152, @[simp]), `unitsIncl` (QMF/Quaternionic:53), `mem_U1_9_of_toMatrix`
(2_Level:639), `QuotientGroup.rightRel_apply`, `Set.finite_range`.

#### Sources
- Left skeleton DiamondHecke.lean:75-106 (shapes); jacobs-endgame §AG-W-ID
  "Single coset" bullet; fork 3_EtaDecomposition:283-318, :486-516 (the proved
  eta-analogues these mirror); [Jac Lemma 2.9 coset content, p. 32].

#### Generality decision
`K₃`/`D`-level (adelic content).  Right-coset orientation THROUGHOUT (the S11
recipe's shape) — the left skeleton's left-coset statements are transposed, not
copied.

### [W05] The three W-certificates (oracle-bound)
- **Status**: done (2026-08-06, beastmode orchestrator; green, ZERO warnings.
  `sigmaTableW = ![1,2,0]`, `dTableW = ![-1,-1,1]` (central signs — so
  `toMatrix (unitsIncl (dTableW i)⁻¹) = ±1 • 1`, no ν anywhere), `uCandW`,
  `factorisationW` (by `group`), `uTableW` + `uTableW_coe`, `toMatrix_uCandW`
  (= diag(−1/5,−1/8), diag(−5/7,−1/8), diag(7,1) — MATCHES THE ORACLE),
  `toMatrix_uCandW_inv` (uniqueness-of-inverse trick, as `toMatrix_eta3_inv`),
  `uCandW_mem`, `toMatrix_uTableW_mul_mu3` (= diag(−1/5,−1/2), diag(−5/7,−1/2),
  diag(7,4) — the thesis δ-data), `toMatrix_uTableW_mul_mu3_mem_sigma1₃`.
  ENGINEERING: reusable `mem_sigma1_diag` / `mem_integralMatrices_diag` helpers
  cover all six membership checks; away-from-3 via `toLocal_unitAt_ne`
  (classRep and mu3 are both `unitAt`!) + `toLocal_unitsIncl` +
  `tmul_mem_localOrder` at ±1 ∈ hurwitzOrder.  Traps: 5_Factorisations'
  `toLocal_classRep_*_ne` are PRIVATE (re-derived locally);
  `valued_eq_one_of_norm_eq_one` already exists in 2_Level;
  `fin_cases` + `![…] i` needs `show` to reduce (used for the d ≡ 1 mod 9 checks);
  a multi-line `by show …; tac` inside parens must be single-line.)
- **File**: PhD/JacobsSlash/U3/7_DiamondHecke.lean
- **Depends on**: W01, W04
- **Parallel**: after both
- **Type**: def + certificate lemmas

#### Statement (skeleton — oracle slots FILLED from W01's results, 2026-08-06, BINDING)
```lean
def sigmaTableW : Fin 3 → Fin 3 := ![1, 2, 0]
noncomputable def dTableW : Fin 3 → Dˣ := ![-1, -1, 1]
theorem dTableW_mem (i : Fin 3) : unitsIncl ℚ D (dTableW i) ∈ globalUnits ℚ D := sorry

noncomputable def uCandW (i : Fin 3) : Dfx ℚ D :=
  (unitsIncl ℚ D (dTableW i) * classRep (sigmaTableW i))⁻¹ * (classRep i * mu3⁻¹)

theorem uCandW_mem (i : Fin 3) : uCandW i ∈ U1_9 := by sorry
noncomputable def uTableW : Fin 3 → U1_9 := fun i => ⟨uCandW i, uCandW_mem i⟩
@[simp] theorem uTableW_coe (i) : ((uTableW i : U1_9) : Dfx ℚ D) = uCandW i := rfl

theorem factorisationW (i : Fin 3) :
    classRep i * mu3⁻¹
      = unitsIncl ℚ D (dTableW i) * classRep (sigmaTableW i) * uCandW i := by
  rw [uCandW]; group

-- Oracle literals (W01): u(i) at 3 = diag(−1/5,−1/8), diag(−5/7,−1/8), diag(7,1);
-- acting u(i)·μ = diag(−1/5,−1/2), diag(−5/7,−1/2), diag(7,4).
theorem toMatrix_uTableW_mul_mu3 (i : Fin 3) :
    toMatrix ℚ D v₃ ((uTableW i : Dfx ℚ D) * mu3)
      = Matrix.of ![![![(-1/5 : K₃), (-5/7 : K₃), (7 : K₃)] i, 0],
                    ![0, ![(-1/2 : K₃), (-1/2 : K₃), (4 : K₃)] i]] := by sorry

theorem toMatrix_uTableW_mul_mu3_mem_sigma1₃ (i : Fin 3) :
    toMatrix ℚ D v₃ ((uTableW i : Dfx ℚ D) * mu3) ∈ Sigma1₃ := by sorry
```

#### Proof sketch
Mirror 5_Factorisations' certificate engine, SIMPLIFIED (all matrices diagonal,
ν-free): (1) `uCandW_mem` — away from 3 the product collapses to global-unit
inverses (the `uCand_away` route, easier: no η-conjugation because `mu3⁻¹`'s away
components are `4⁻¹`-central); at 3 the entries are explicit rationals — d-form
checks are numeral valuations via `valued_le_γ₉_of_norm` + the 5_Factorisations
numeral workhorses.  (2) `toMatrix_uTableW_mul_mu3`: `map_mul` + the classRep/mu3
literals + `Matrix.mul_fin_two` numerals.  (3) Σ₁(3)-membership from the literal:
entries integral, `v(d−1) ≤ γ₃` (the acting d's are `≡ 1 mod 3` only — the width
gap made concrete).  Per-i `fin_cases`-free: three separate literal blocks as in
5_Factorisations (the P19 layout).

#### Sources
- W01's results header (BINDING data); left skeleton DiamondHecke.lean:108-136
  (shapes; note the fork factorisation is at `μ⁻¹`, right-coset form);
  5_Factorisations (the proved certificate engine being mirrored); jacobs-endgame
  §AG-W-ID "Certificates" bullet (left tables for cross-checking magnitude).
- LOC anchor: 5_Factorisations' nine certificates ≈ 700 LOC; three diagonal
  certificates ≈ 150-250 LOC.

#### Generality decision
Concrete `K₃`/`D` data (certificates are literals by design).

### [W06] `coeff_weightGenFun_diagonal` + the δ-identification
- **Status**: done (2026-08-06, beastmode orchestrator; green, zero warnings.
  **THE TWIST-FREE δ-IDENTIFICATION IS PROVED**: `kappaSlashWide_acting_eq_delta` —
  each certificate acting operator IS `delta01/delta12/delta20` exactly, no scalar
  (the W-side counterpart of `blockEntry_eq_epsOp`).  `coeff_weightGenFun_diagonal`
  proved from the definitions: at `diag(a,d)`, `linX = C d` (so `(linX)⁻¹ = C d⁻¹` by
  `PowerSeries.C_inv`), `numX = C a * X`, hence `mobius = C (a/d) * X` and
  `autFactor = C (κ(d)·d⁻²)` (the κ-column collapses at `c = 0` — only `n = 0`
  survives `coeff_yCoeff_kappaSeries₂`), so
  `yCoeff (weightGenFun) r = C (κ(d)·d⁻²·(a/d)^r) · X^r` and the coefficient is the
  advertised `if m = r then … else 0`.  Numerals then match the transcribed δ's
  scalars `4κ(−1/2), 4κ(−1/2), κ(4)/16` and arguments `2/5, 10/7, 7/4` by `ring_nf`
  alone.)
- **File**: PhD/JacobsSlash/U3/7_DiamondHecke.lean
- **Depends on**: W01, W03, W05
- **Parallel**: no
- **Type**: lemma

#### Statement (skeleton)
```lean
/-- `weightGenFun` of a diagonal matrix: the coefficient at `(m, r)` is
`κ(d)·d⁻²·(a/d)^m` on the diagonal `m = r`, else `0`. -/
theorem coeff_weightGenFun_diagonal {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [CharZero K] (t a d : K) (hd : d ≠ 0)
    (m r : ℕ) :
    MvPowerSeries.coeff (idx m r)
        (weightGenFun t (Matrix.of ![![a, 0], ![0, d]]))
      = if m = r then unitPow t d * d⁻¹ * d⁻¹ * (a / d) ^ m else 0 := by sorry

-- W01 VERDICT (2026-08-06): TWIST-FREE — this scalar-free branch is BINDING;
-- the coboundary branch below is dead, no fork classWeight def is introduced:
theorem kappaSlashWide_acting_eq_delta (t ht) (i : Fin 3) :
    kappaSlashWide t ht ⟨toMatrix ℚ D v₃ ((uTableW i : Dfx ℚ D) * mu3),
        toMatrix_uTableW_mul_mu3_mem_sigma1₃ i⟩
      = ![delta01 norm_three_lt_one ht, delta12 norm_three_lt_one ht,
          delta20 norm_three_lt_one ht] i := by sorry
-- COBOUNDARY branch (if W01 says no): same LHS, RHS `(scalar i) • ![…] i` with the
-- W01-recorded scalars; a fork `classWeight` def is then introduced here.
```
(The `![δ…] i` indexing is by SOURCE class `i`; the target class is `sigmaTableW i` —
the assignment of which δ sits at which `i` follows W01's σ_W and the transcribed
δ-layout of `Wop`; pin it in the oracle results before stating.)

#### Proof sketch
`coeff_weightGenFun_diagonal`: unfold `weightGenFun` at a diagonal matrix — the
mobius numerator degenerates (`b = c = 0`), the column series collapses to the
geometric diagonal; compute via the `yCoeff_weightGenFun` layer (4_KappaSlash) at
`c = 0` — the left skeleton records exactly this route (DiamondHecke.lean:201-209).
Identification: `ext_matrixCoeff` + `matrixCoeff_kappaSlashWide` +
`coeff_weightGenFun_diagonal` at the W05 literals vs the transcribed δ-generating
functions (`delta01`-defs in 4_DiamondW:668-677 read off their `D`-arguments);
`fin_cases i` + numeral arithmetic (`unitPow` at the literal `d`'s).

#### Mathlib/project lemmas needed
`yCoeff_weightGenFun` (4_KappaSlash), `unitPow` (the κ-power — 3_BinomialTheorem
layer; verify exact name at execution start, it is the function `lemma210`'s file
calls `unitPow`), `matrixCoeff_ofGenFun`, δ-defs 4_DiamondW:668-677.

#### Sources
- Left skeleton DiamondHecke.lean:199-229 (both statements' shapes);
  jacobs-endgame §AG-W-ID "Acting matrices" bullet (left scalars
  `4κ(−1/2), 4κ(−1/2), κ(4)/16` — the coboundary that W01 tests in fork
  orientation); [Jac p. 32 δ-display, erratum records on the jacobs board].

#### Generality decision
`coeff_weightGenFun_diagonal` generic-K (maximal); the identification concrete.

### [W07] `heckeW` + the W-HEADLINE: `Wop` is the genuine `[U₁(9)·μ·U₁(9)]`
- **Status**: **DONE (2026-08-06, beastmode orchestrator — THE W-WAVE IS COMPLETE)**.
  Green, zero warnings; endpoints (`heckeW_apply_classRep`,
  `heckeW_apply_classRep_eq_delta`, `kappaSlashWide_acting_eq_delta`,
  `mu3_mul_mem_U1_9`, `uCandW_mem`) all on exactly
  [propext, Classical.choice, Quot.sound] — unconditional.  Landed:
  `kappaSlashWide_one` + `kappaSlashWideAction` (the Σ₁(3) RightSlashAction — W03 had
  only the operator and its laws), `levelMonoid1₃ToSigma1₃`,
  `kappaWideLevelSlashAction` + `kappaWideLevelSMulSlashClass` + `kappaFormsWide`
  (verbatim 6_Matrix pullback pattern at the wide monoid), `heckeW`,
  **`heckeW_apply_classRep`** (S11 recipe at the Fin 1 family — `hvinj` by
  `Subsingleton.elim`, sum collapses via `Finset.univ_unique`+`sum_singleton`), and
  **`heckeW_apply_classRep_eq_delta`**: `(Wφ)(cᵢ) = δᵢ(φ(c_{σ(i)}))` with the
  transcribed δ — i.e. **`Wop` IS the matrix of the genuine `W = [U₁(9)·μ·U₁(9)]`,
  twist-free**.  Needs `open RightSlashAction` for the structure fields.  One
  decorative block-sum restatement was dropped (a `Finset.sum_eq_single` metavariable
  stall on the operator-valued `if`; the content is already in
  `_eq_delta` — recorded, not a gap).
- **File**: PhD/JacobsSlash/U3/7_DiamondHecke.lean
- **Depends on**: W03, W04, W05, W06, CLEANUP-W1
- **Parallel**: no
- **Type**: theorem (wave headline)

#### Statement (skeleton)
```lean
noncomputable def kappaWideLevelSlashAction (t : K₃) (ht : ‖t‖ < 1) :
    RightSlashAction levelMonoid1₃ c(ℕ, K₃) := sorry  -- 6_Matrix pullback pattern
theorem kappaWideLevelSMulSlashClass (t ht) :
    letI := kappaWideLevelSlashAction t ht
    SMulSlashClass K₃ levelMonoid1₃ c(ℕ, K₃) := sorry
noncomputable def kappaFormsWide (t ht) :
    Submodule K₃ (AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) := sorry

/-- The wide presentation is the same space (membership quantifies only over
`U₁(9) ⊆` both monoids; the actions agree there by `kappaSlashWide_restrict`). -/
theorem kappaFormsWide_eq_kappaForms (t ht) :
    kappaFormsWide t ht = kappaForms t ht := by sorry

/-- **The genuine diamond operator** `W = [U₁(9)·μ·U₁(9)]`. -/
noncomputable def heckeW (t ht) : kappaFormsWide t ht →ₗ[K₃] kappaFormsWide t ht :=
  sorry  -- heckeOperatorSlash K₃ hU hU mu3_mem_levelMonoid1₃ finite_image_mu3

/-- **AG-W-ID headline (unconditional)**: `(Wφ)(cᵢ) = φ(c_{σ(i)}) ∣κ (u(i)·μ)` —
the `Fin 1`-coset instance of the S11 recipe. -/
theorem heckeW_apply_classRep (t ht) (φ : kappaFormsWide t ht) (i : Fin 3) :
    (heckeW t ht φ : AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃))
        (classRep i)
      = kappaSlashWide t ht
          ⟨toMatrix ℚ D v₃ ((uTableW i : Dfx ℚ D) * mu3),
            toMatrix_uTableW_mul_mu3_mem_sigma1₃ i⟩
          ((φ : AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃))
            (classRep (sigmaTableW i))) := by sorry

/-- **`Wop` is the matrix of the genuine `W`** (assembled block form, mirror of
6_Matrix's `blockEntry_eq_epsOp` endpoint). -/
theorem blockEntryW_eq_Wop (t ht) : sorry := by sorry
-- shape: the (i,j)-blocks read from heckeW_apply_classRep (δ at j = σ i, else 0)
-- assemble to `Wop norm_three_lt_one ht` — via W06's identification;
-- statement-form fixed after W06 lands (twist-free vs coboundary).
```

#### Proof sketch
`kappaWideLevelSlashAction`/`SMulSlash`/`kappaFormsWide`: verbatim the 6_Matrix
pullback pattern at the wide monoid (kappaLevelSlashAction:88-118 with
`levelMonoid1₃`/`kappaSlashWide` substituted — including the `@[instance_reducible]`
attribute).  `kappaFormsWide_eq_kappaForms`: `Submodule` ext; membership in
`slashFixedPointsOfLE` is `∀ u : U₁(9), φ ∣ₛ ⟨u, hU u.2⟩ = φ` on BOTH sides; the
two subtype slashes agree by `kappaSlashWide_restrict` (value-level) — a `show` +
`congr`-transport per the 6_Matrix seam idioms.  `heckeW_apply_classRep`: S11
`AutomorphicFunction.heckeOperatorSlash_apply_rep` at `T := Fin 1`,
`vRep := fun _ => mu3`, `hv := bijOn_muRep`, `hvinj` (constant on `Fin 1`:
`Function.injective` via `Subsingleton.elim`), `hfact := fun _ => uTableW_coe ▸
factorisationW i`, `hd := dTableW_mem`, `hact := mem_comap ∘
toMatrix_uTableW_mul_mu3_mem_sigma1₃`; the `Fin 1` sum collapses via
`Finset.sum_const`/`Fintype.sum_subsingleton`.  `blockEntryW_eq_Wop`: mirror
6_Matrix's `blockEntry`/`blockEntry_eq_epsOp` layout with W06's per-block
identification; the diagonal-vs-cyclic layout bookkeeping is `sigmaTableW`-driven
`fin_cases`.

#### Mathlib/project lemmas needed
S11 `heckeOperatorSlash_apply_rep` (Slash/HeckeMatrix:57 — signature verified in
P20), `heckeOperatorSlash` (Slash/HeckeMonoid:144), 6_Matrix's instance patterns,
`Fintype.sum_subsingleton`, W06's lemmas, `Wop` (4_DiamondW:684).

#### Sources
- Left skeleton DiamondHecke.lean:169-197 (shapes); the P20 board notes (the
  worked S11-instantiation this mirrors); jacobs-endgame WI4.

#### Generality decision
`K₃`-level; statements right-slash native; `kappaFormsWide` kept as a def (not
inlined) because `heckeW`'s type needs the wide monoid even though the SPACE equals
`kappaForms` — the eq-lemma is the API.

### [CLEANUP-W1] /cleanup on 7_DiamondHecke.lean (cadence: after 3rd proof ticket)
- **Status**: done (2026-08-06, run inline after W05: the 12 unused-simp-arg warnings
  from the generated boilerplate lists were stripped; file at zero warnings before W06
  started)
### [CLEANUP-W2] /cleanup on 7_DiamondHecke.lean (final per-file)
- **Status**: done (2026-08-06: file ends at ZERO errors + ZERO warnings, 1100 lines;
  runLinter reports zero findings in the file)
### [CLEANUP-W3] /cleanup on 4_DiamondW.lean (final per-file, post-W02 edit)
- **Status**: done (2026-08-06: Mode-A verification of the single new decl —
  zero warnings, zero in-file runLinter findings; W02 worker's code already clean)
  — **Depends on**: W02

### [E00] `ιC : K₃ →+* ℂ_[3]`, isometric
- **Status**: done (2026-08-06, beastmode parallel worker; primary route: `Padic.adicCompletionEquiv`.symm ∘ `algebraMap ℚ_[3] ℂ_[3]`, isometry by valuation squeeze — no density needed; 182 LOC; `lake build` green (3430 jobs); axioms = [propext, Classical.choice, Quot.sound])
- **File**: PhD/JacobsSlash/U3/2_PadicEmbedding.lean (NEW; imports U3.«1_Setting»)
- **Depends on**: none
- **Parallel**: yes
- **Type**: def + lemmas
- **Progress**: File complete, sorry-free. Public API: `JacobsSlash.norm_three_eq` (`‖(3:K₃)‖ = 3⁻¹`), `JacobsSlash.norm_adicCompletionEquiv` (mathlib's `ℚ_[3] ≃A[ℚ] K₃` is isometric), `JacobsSlash.ιC`, `JacobsSlash.norm_ιC`. Key mathlib names: `Padic.adicCompletionEquiv` (E₃; kept UNascribed — ascribing `≃A[ℚ] K₃` clashes `instAlgebraAdicCompletion` vs `DivisionRing.toRatAlgebra`), `PadicInt.coe_adicCompletionIntegersEquiv_apply` (unit-ball transport → `HeightOneSpectrum.mem_adicCompletionIntegers`), `Valued.toNormedField.norm_le_one_iff`, `FinitePlace.norm_def` + `valued_three_eq` (1_Setting) + `Ideal.absNorm_span_singleton`/`Algebra.norm_algebraMap`/`RingOfIntegers.rank` (→ `absNorm v₃.asIdeal = 3`), `WithZeroMulInt.toNNReal_neg_apply`, `Padic.norm_eq_zpow_neg_valuation`/`Padic.norm_p` (y = u·3ⁿ squeeze), `PadicComplex.norm_extends'`. Seam idiom: statements ascribed at `K₃`, seam-crossing steps in exact mode (congrArg/trans), never rw across the `v₃`-vs-`primesEquiv.symm ⟨3,_⟩` spelling (v₃ is non-reducible). `ιC := (algebraMap ℚ_[3] ℂ_[3]).comp E₃.symm.toAlgEquiv.toAlgHom.toRingHom` (the `→+*` coercion doesn't fire across the seam). Note: lean-lsp MCP tools were unavailable this session; iterated with `lake env lean` on the file (no build-dir contention).

#### Statement (skeleton)
```lean
/-- The isometric embedding of the fork's completed field into `ℂ₃`. -/
noncomputable def ιC : K₃ →+* ℂ_[3] := sorry

theorem norm_ιC (x : K₃) : ‖ιC x‖ = ‖x‖ := by sorry
```

#### Proof sketch
Primary route: mathlib's `Padic.adicCompletionEquiv` /
`adicCompletion.padicEquiv` (Mathlib/NumberTheory/Padics/HeightOneSpectrum.lean:217
— continuous ℚ-algebra iso `v.adicCompletion ℚ ≃ ℚ_[p]`); identify the fork's `v₃`
with the mathlib-side height-one prime of `3` (the same seam 1_Setting's density
proof crossed via `PadicInt.adicCompletionIntegersEquiv` — reuse its
identification bookkeeping), compose with `algebraMap ℚ_[3] ℂ_[3]`.  Isometry:
`PadicComplex.norm_extends'` for the second leg; for the equiv leg both norms
restrict to the `3`-adic norm on the dense image of `ℚ`
(`UniformSpace.Completion.denseRange_coe`), and a continuous map agreeing on a
dense set with a continuous target determines `‖·‖ ∘ ιC = ‖·‖`
(`Continuous.ext_on` / `DenseRange.equalizer`).  FALLBACK (if the v₃-vs-prime
identification fights): build `ιC` directly as
`UniformSpace.Completion.extensionHom` of `algebraMap ℚ ℂ_[3]` (uniformly
continuous for the v₃-adic uniformity since `‖q‖_{ℂ₃}` is the 3-adic absolute
value on `ℚ` — `PadicComplex.norm_extends'` + `Padic.norm_rat`-layer), with the
same density-isometry ending.  Record which route landed.

#### Mathlib lemmas needed (verified to exist)
`Padic.adicCompletionEquiv` / `adicCompletion.padicEquiv`
(HeightOneSpectrum.lean:217-220), `PadicComplex.norm_extends'` (used by
5_Instance:117), `UniformSpace.Completion.denseRange_coe`,
`UniformSpace.Completion.extensionHom` (fallback), `DenseRange.equalizer`.

#### Sources
- 1_Setting:680-684 (the fork's existing crossing of the same seam);
  Mathlib.NumberTheory.Padics.HeightOneSpectrum (module docstring quoted:
  "Isomorphisms between `adicCompletion ℚ` and `ℚ_[p]`").

#### Generality decision
Concrete (K₃, ℂ₃) — the general statement is mathlib's; this is the instantiation.

### [E01] The general bridge: Newton-polygon slopes are valuations of reciprocal eigenvalues
- **Status**: done (2026-08-06, beastmode parallel worker; both theorems proved verbatim,
  sorry-free, std axioms, file + module built clean, runLinter clean on the new file)
- **File**: PhD/JacobsSlash/5_EigenSlopes.lean (NEW; imports «4_SlopeReading»,
  «4_DiamondW», PhD.TateFredholm.Riesz, PhD.NewtonPolygons.PowerSeriesZeros,
  PhD.NewtonPolygons.PolynomialRoots)
- **Depends on**: none
- **Parallel**: yes
- **Type**: theorem (generic bridge — the Riesz × NewtonPolygons composition point)
- **GENERALITY (user-directed, 2026-08-06, BINDING)**: both theorems of this ticket
  are stated in FULL generality — arbitrary complete algebraically closed
  ultrametric `K`, arbitrary index type `{I} [DecidableEq I]`, arbitrary compactoid
  operator; NO Jacobs/M22op/ϖ₃ content anywhere in their statements or proofs.
  They live in this folder FOR NOW (file docstring marks them as public-API
  candidates for the `TateFredholm` × `NewtonPolygons` seam, to be upstreamed once
  folder ownership with the tatefredholm-eigen board is settled), but nothing in
  them may depend on the fork.

#### Statement
```lean
/-- **Slopes are zeros** (Riesz–Newton bridge): over a complete algebraically closed
ultrametric field, an entire series with constant term `1` has, at every finite
Newton-polygon slope `m`, a zero of norm `exp m` (in the `evalT` sense of
`TateFredholm`). -/
theorem exists_evalT_zero_of_slope {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K]
    (f : PowerSeries K) (hf0 : PowerSeries.coeff 0 f = 1)
    (hent : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f)
    {k j₀ : ℕ} {m : ℝ}
    (hm : (newtonPolygon₀OfPowerSeries negLogNorm f).slopes k = (m : WithBotTop ℝ))
    (hj : (newtonPolygon₀OfPowerSeries negLogNorm f).vertexX (k + 1)
        = ((j₀ : ℤ) : WithTop ℤ)) :
    ∃ x : K, PowerSeries.evalT x f = 0 ∧ ‖x‖ = Real.exp m := by sorry

/-- **Newton-polygon slopes are valuations of reciprocal eigenvalues** (the
headline of the bridge, fully general): over a complete algebraically closed
ultrametric field, every finite slope `m` of the Newton polygon of the Fredholm
determinant `det(1 − T·u)` of a compactoid operator is realised by an eigenvector
`u x = a • x` with `‖a‖ = exp (−m)` — the zero of the determinant at `a⁻¹` being
the reciprocal of the eigenvalue [Serre1962, §7 Props 11–12 + blueprint §5.11–5.14].
Public-API candidate for the `TateFredholm`/`NewtonPolygons` seam; kept here for
now, Jacobs-free by construction. -/
theorem exists_eigenvector_of_slope_charPowerSeries {K : Type*}
    [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsAlgClosed K] {I : Type*} [DecidableEq I]
    (u : c(I, K) →L[K] c(I, K)) (hu : IsCompactoid u)
    {k j₀ : ℕ} {m : ℝ}
    (hm : (newtonPolygon₀OfPowerSeries negLogNorm
        (charPowerSeries u)).slopes k = (m : WithBotTop ℝ))
    (hj : (newtonPolygon₀OfPowerSeries negLogNorm
        (charPowerSeries u)).vertexX (k + 1) = ((j₀ : ℤ) : WithTop ℤ)) :
    ∃ (a : K) (x : c(I, K)), a ≠ 0 ∧ x ≠ 0 ∧ u x = a • x ∧
      ‖a‖ = Real.exp (-m) := by sorry
```

#### Proof sketch
1. `hconv := hent (Real.exp m) (Real.exp_pos m)`.
2. **5.13**: `exists_weierstrass_factorisation f hf0 hm hj hconv` →
   `⟨g, h, hfeq, hdeg, hg0, _, hhconv, hh1, hpoly⟩` (PowerSeriesZeros:571; the
   polygon-agreement clause `hpoly : ∀ a ≤ k, slopes/lengths of g = those of f`).
3. **Positive length**: extract `(newtonPolygon₀OfPowerSeries negLogNorm
   (g : PowerSeries K)).lengths k ≥ 1`-content from `hm`/`hj` + `hpoly` (a
   finite slope whose segment ends at `vertexX (k+1) = j₀` has positive length;
   the Height/Spec API lemma names are located at execution — the same extraction
   4_SlopeReading's engine performs).
4. **5.11**: `card_roots_slope g hg0 …` (PolynomialRoots:955) at segment `k` of
   `g`'s polygon (= `f`'s data by `hpoly`): the number of roots of `g` of norm
   `exp m`, counted in `g.roots`, equals the segment length ≥ 1.  If the theorem
   carries a splitting hypothesis, discharge with `IsAlgClosed.splits_codomain`;
   `[IsAlgClosed K]` enters ONLY here.  `Multiset.card_pos.mp` + `mem_filter` →
   `⟨x, hxroot, hxnorm⟩` with `‖x‖ = Real.exp m`.
5. **5.14**: `hasSum_zero_iff_aeval_eq_zero` (PowerSeriesZeros:818) at `L := K`,
   `Algebra.id K` (`hL := fun a => by simp`), `hx : ‖x‖ ≤ exp m` (from `hxnorm`):
   the `.mpr` of `Polynomial.aeval x g = 0` (from `hxroot` via
   `Polynomial.aeval_eq_zero_of_mem_roots`-layer) gives
   `HasSum (fun t => algebraMap K K (coeff t f) * x ^ t) 0`.
6. **evalT bridge**: `simp only [Algebra.id.map_eq_id, RingHom.id_apply]` in the
   HasSum, then `PowerSeries.evalT x f = 0` by `HasSum.tsum_eq` (evalT is the tsum,
   Riesz.lean:111).
7. **Operator headline** (`exists_eigenvector_of_slope_charPowerSeries`): apply
   the series-level theorem to `f := charPowerSeries u` (`hf0` by `simp`
   [charCoeff 0 = 1, the Riesz:2212 discharge]; `hent := charPowerSeries_isEntire
   u hu`) → zero `x₀`, `‖x₀‖ = exp m`; then
   `exists_eigenvector_of_evalT_charPowerSeries_eq_zero u hu` (Riesz:2208) →
   `x₀ ≠ 0` and eigenvector `x` with `u x = x₀⁻¹ • x`.  Set `a := x₀⁻¹`:
   `a ≠ 0` (`inv_ne_zero`), `‖a‖ = ‖x₀‖⁻¹ = (exp m)⁻¹ = exp (−m)`
   (`norm_inv`, `Real.exp_neg`).

#### Mathlib/project lemmas needed (existence verified this session)
`exists_weierstrass_factorisation` (PowerSeriesZeros:571), `card_roots_slope`
(PolynomialRoots:955), `hasSum_zero_iff_aeval_eq_zero` (PowerSeriesZeros:818),
`PowerSeries.evalT` (Riesz:111), `HasSum.tsum_eq`, `IsAlgClosed.splits_codomain`,
`Polynomial.mem_roots`.

#### Sources
- Blueprint 5.13/5.14/5.11 as formalised (locators above; docstrings quoted in
  plan.md Phase 2 inventory).  This is a COMPOSITION of proved results — no new
  mathematics; the risk surface is API-shape only (step 3/4 extraction).

#### Generality decision
Maximal: any complete alg-closed ultrametric `K`; `IsAlgClosed` used only in the
5.11 step and stated as the theorem's only extra hypothesis.

#### Progress
- DONE 2026-08-06 (beastmode parallel worker).  `PhD/JacobsSlash/5_EigenSlopes.lean`
  created; both binding statements proved **verbatim — no forced signature changes**.
- **Route as executed**: `exists_weierstrass_factorisation` (5.13, obtain pattern
  `⟨g, h, hfeq, hdeg, hg0, -, hhconv, hh1, hpoly⟩` exactly as sketched) → private
  `exists_pos_length_of_segment_data` (step 3; the PolynomialRoots bridge lemmas are
  private, so re-derived from the PUBLIC construction API:
  `NewtonPolygon₀.vertexX_succ` rules out the rays, `.slopes`/`.lengths` are defeq to
  `slopes' (newtonPolygon (coeffVal f) k)` / `newtonPolygon_lengths (coeffVal f) k`,
  and `nextStep_nextVertex` + `nextVertex_l_eq` + `nextVertex_lt` give `1 ≤ l`) →
  transfer to `g` by `(hpoly k le_rfl).1/.2.trans` → `card_roots_slope` (5.11) inside
  private `exists_aeval_zero_norm_eq_of_slope` → `hasSum_zero_iff_aeval_eq_zero`
  (5.14 at `L := K`, `hL := fun a => by rw [Algebra.algebraMap_self, RingHom.id_apply]`)
  → `HasSum.tsum_eq` (evalT defeq the tsum) → Riesz
  `exists_eigenvector_of_evalT_charPowerSeries_eq_zero` + `charPowerSeries_isEntire`,
  `a := x₀⁻¹`, `norm_inv`/`Real.exp_neg`.
- **`card_roots_slope` exact shape found** (differs from the sketch's guess): NO
  `Splits` hypothesis.  It takes `(w : Valuation (AlgebraicClosure K) NNReal)`
  `(hw : ∀ a, w (algebraMap K (AlgebraicClosure K) a) = ‖a‖₊)` plus `hm` (slopes) and
  `hl : lengths k = (l : WithTop ℕ)` — hence step 3's length extraction is genuinely
  needed — and counts `(Multiset.filter (fun x => (w x : ℝ) = Real.exp m)
  ((g.map (algebraMap K (AlgebraicClosure K))).roots)).card = l`.  So `[IsAlgClosed K]`
  enters NOT via `IsAlgClosed.splits_codomain` but via
  `IsAlgClosed.algebraMap_bijective_of_isIntegral`: `w` is mathlib's
  `NormedField.valuation` (`Mathlib.Topology.Algebra.Valued.NormedValued`, new import)
  comapped along `(RingEquiv.ofBijective (algebraMap K (AlgebraicClosure K)) hbij).symm`,
  and the root is pulled back to `K` by the same iso
  (`Polynomial.eval_map`/`eval₂_at_apply`/`map_eq_zero_iff`, `coe_aeval_eq_eval`).
- Sketch deltas: step 4's `Multiset.card_pos.mp` became
  `Multiset.card_pos_iff_exists_mem.mp (hl1.trans_eq hcard.symm)`; step 6's
  `Algebra.id.map_eq_id` is `Algebra.algebraMap_self` at this mathlib.
- Gates: `lake build PhD.JacobsSlash.«5_EigenSlopes»` ✓ (2652 jobs);
  `#print axioms` on BOTH theorems = `[propext, Classical.choice, Quot.sound]` ✓;
  `lake exe runLinter` — zero findings in the new file (108 pre-existing findings in
  transitively imported modules, untouched per rules).

### [E02] The `M₂,₂` factor at `negLogNorm` + eigenvectors of `M22op`
- **Status**: done (2026-08-06, beastmode orchestrator; FILE SORRY-FREE, 2652 jobs,
  all four endpoints [propext, Classical.choice, Quot.sound].  KEY ENGINEERING: the
  slopes/vertexX structure fields of the constructed polygon came NOT from the
  Height-API sandwich but from a **forced-walk computation**: for strictly monotone
  partial-sum data every step of the SpecConstruction walk is
  `nextVertex (k+1) _ 1 (s k)` (`nextStep_eq_of_strict` — IsLeast of the slope set
  at the immediate successor + `achievingSet = {k+1}` via sum_eq_zero_iff_of_nonneg;
  `split` + `Finset.max'_mem` + `Set.ext_iff.mp` avoid every choose/motive trap;
  the walk recursion then gives `newtonPolygon_eq_of_strict` by induction).
  val↔negLogNorm rescale via `PseudoUniformizer.val_def` + `coe_ϖ₃` (scale
  `L = −log‖3‖`, `inv_mul_cancel₀`).  `exists_eigenvector_M22op` is the pure
  E01-instantiation; the ‖a‖² = ‖3‖^(2j+1) conversion via a targeted
  exp_nat_mul/exp_log chain (NO global ‖3‖-rewrite — that traps the log-argument).)
- **File**: PhD/JacobsSlash/5_EigenSlopes.lean
- **Depends on**: E01
- **Parallel**: no
- **Type**: theorem

#### Statement (skeleton; `L₃norm := -Real.log ‖(3 : K)‖`)
```lean
theorem slopes_negLogNorm_charPowerSeries_M22op (hω : ω ^ 2 + ω + 1 = 0)
    (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1) (hν2 : ν ^ 2 = -2)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) (k : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm
        (charPowerSeries (M22op ω hω h3 ht hνc))).slopes k
      = ((((k : ℝ) + 1 / 2) * (-Real.log ‖(3 : K)‖) : ℝ) : WithBotTop ℝ) := by sorry

theorem vertexX_negLogNorm_charPowerSeries_M22op (…same pack…) (k : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm
        (charPowerSeries (M22op ω hω h3 ht hνc))).vertexX (k + 1)
      = (((k + 1 : ℕ) : ℤ) : WithTop ℤ) := by sorry

/-- Eigenvectors of the middle block at every half-integral valuation. -/
theorem exists_eigenvector_M22op [IsAlgClosed K] (…same pack…) (j : ℕ) :
    ∃ (a : K) (x : c(ℕ, K)), a ≠ 0 ∧ x ≠ 0 ∧
      M22op ω hω h3 ht hνc x = a • x ∧
      ‖a‖ ^ 2 = ‖(3 : K)‖ ^ (2 * j + 1) := by sorry
```

#### Proof sketch
1. Polygon data: re-run 4_SlopeReading's engine (:358-425 — `IsNewtonPolygonOf`
   from an explicit coefficient sequence, then `slopes`/`unitSlope`/`vertexX`
   extraction) at `negLogNorm` in place of `(ϖ₃ h3).val`.  The coefficient input
   is the SAME proved computation `val_charCoeff_M22op … m = Σ_{i<m} (i + 1/2)`;
   convert values by the `PseudoUniformizer` val↔norm dictionary
   (`‖x‖ = ‖ϖ₃‖^(val x)`-layer, Tate.lean/1_SlopeTheorem — so
   `negLogNorm (charCoeff m) = (Σ_{i<m}(i+1/2)) · (−log ‖3‖)`, using
   `‖ϖ₃‖ = ‖3‖`).  Slopes scale by the positive constant, vertexX is unchanged
   (unit lengths: the slopes `k + 1/2` are strictly increasing).
2. `exists_eigenvector_M22op`: PURE INSTANTIATION of E01's general
   `exists_eigenvector_of_slope_charPowerSeries` at `u := M22op ω hω h3 ht hνc`
   (`hu := isCompactoid_M22op ω hω h3 ht hνc` — 2_U3Data:1078, public),
   `m := (j + 1/2)·(−log‖3‖)`, `j₀ := j + 1` (item 1's polygon data) →
   `a, x` with `M22op x = a • x`, `‖a‖ = exp(−(j+1/2)·(−log‖3‖))`.  Norm
   conversion to the milestone form: `‖3‖ = Real.exp (Real.log ‖3‖)` (norm pos:
   `three_ne_zero` + `norm_pos_iff`), so
   `‖a‖² = exp((2j+1)·log‖3‖) = ‖3‖^(2j+1)` — `Real.exp_log`,
   `Real.exp_nat_mul` bookkeeping.  No Riesz call here: the composition already
   happened generically in E01.

#### Mathlib/project lemmas needed
`val_charCoeff_M22op` (4_SlopeReading — consumed at :425), the 4_SlopeReading
polygon engine (locate the `IsNewtonPolygonOf`-to-`slopes` lemmas it uses),
`charPowerSeries_isEntire` (Riesz-verified), `isCompactoid_M22op` (2_U3Data:1078),
`exists_eigenvector_of_evalT_charPowerSeries_eq_zero` (Riesz:2208),
`Real.exp_log`, `Real.exp_nat_mul`.

#### Sources
- 4_SlopeReading:415-425 (the ϖ₃-normalised original whose computation is being
  rescaled — [Jac, Cor 2.16 slope data]); E01.

#### Generality decision
Generic `K` throughout; `[IsAlgClosed K]` only on the eigen-statement (inherited
from E01).  Norm-side statements, no `rpow` (squared ℕ-power form).

### [E03] Block transport: `M₂,₂`-eigenvectors are `U₃`-matrix eigenvectors in the `ω²`-eigenspace
- **Status**: done (2026-08-06, beastmode orchestrator; in 5_EigenSlopes.lean, FILE
  SORRY-FREE, build green 2652 jobs, axioms [propext, Classical.choice, Quot.sound].
  W02-FLIP APPLIED: the clause is `Wop h3 ht y = ω • y` (block 1 = ω-eigenblock).
  Proof exactly per sketch: `y := Bop (blockIncl 1 x)`; two private diag-collapse
  lemmas (`U3diag_blockIncl_one`, `Wdiag_blockIncl_one` via blockOp_blockIncl +
  Fin.sum_univ_three + simp); `lemma210` and `Binvop_comp_Wop_comp_Bop` applied
  pointwise via DFunLike.congr_fun + comp_apply; nonvanishing via
  blockProj_blockIncl (pin the block index `(1 : Fin 3)` explicitly — bare `1`
  elaborates σ := ℕ and demands `Fintype ℕ`).)
- **File**: PhD/JacobsSlash/5_EigenSlopes.lean
- **Depends on**: E02, W02
- **Parallel**: no
- **Type**: theorem (generic K)

#### Statement
```lean
/-- Transport along `B`: an eigenvector of the middle block embeds as an
eigenvector of the assembled `U₃`-matrix lying in the `ω²`-eigenspace of the
transcribed diamond operator. -/
theorem exists_eigenvector_U3MatrixOp_of_M22 (hω : ω ^ 2 + ω + 1 = 0)
    (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1) (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10)
    {a : K} {x : c(ℕ, K)} (hx0 : x ≠ 0)
    (hx : M22op ω hω h3 ht hνc x = a • x) :
    ∃ y : c(Fin 3 × ℕ, K), y ≠ 0 ∧
      U3MatrixOp h3 ht hνc y = a • y ∧
      Wop h3 ht y = ω • y := by sorry
```
**W02 FLIP APPLIED (2026-08-06, binding)**: W02's computation landed
`Binvop∘Wop∘Bop = diag(1, ω•1, ω²•1)` — block 1 (the M₂,₂ slot) is the
**ω-eigenblock** of the transcribed `B`-conjugation, so the clause here is
`Wop y = ω • y` (was ω² in the draft).  The thesis's "ω²-eigenblock" wording
[Jac p. 34] is the same statement under the relabeling ω ↦ ω² (both are
primitive; `ωC` is `∃`-chosen, so the labeling is conventional) — record this
in E05's docstring.

#### Proof sketch
Set `y := Bop ω h3 ht hω (cSpace.blockIncl 1 x)`.
1. `y ≠ 0`: `Binvop_comp_Bop` (4_DiamondW:957) pointwise gives
   `Binvop y = blockIncl 1 x ≠ 0` (`blockIncl` injective: evaluate with
   `cSpace.blockProj_blockIncl`, 1_BlockOp:615); a CLM of `0` is `0`.
2. `U₃`-clause: apply `congrFun`-of-`lemma210` (4_DiamondW:1203) at
   `blockIncl 1 x`: `Binvop (U3MatrixOp (Bop (blockIncl 1 x))) = blockOp
   diag(M11,M22,M33) (blockIncl 1 x)`; the RHS collapses by `blockOp_blockIncl`
   (1_BlockOp:631) + `fin_cases`/`simp` (column-1 blocks vanish off the diagonal)
   to `blockIncl 1 (M22op … x) = a • blockIncl 1 x` (by `hx`, `map_smul`).
   Post-compose `Bop` and cancel `Bop ∘ Binvop = id` (`Bop_comp_Binvop`,
   4_DiamondW:1001): `U3MatrixOp y = Bop (a • blockIncl 1 x) = a • y`.
3. `W`-clause: same computation with W02's `Binvop_comp_Wop_comp_Bop` in place of
   `lemma210`; the diagonal scalar block at index 1 is `ω ^ 2 • 1`, giving
   `Wop y = Bop (ω ^ 2 • blockIncl 1 x) = ω ^ 2 • y`.
   (If W02's hand-check swapped the scalars, this clause follows the recorded
   statement-fix — the eigenvector clause becomes the matching power; E04/E05
   statements inherit the same power.)

#### Mathlib/project lemmas needed
`lemma210` (4_DiamondW:1203), `Binvop_comp_Bop` (:957), `Bop_comp_Binvop` (:1001),
`blockOp_blockIncl` (1_BlockOp:631), `cSpace.blockProj_blockIncl` (:615), W02.

#### Sources
- 4_DiamondW's own diagonalisation route (:1244-1300 — the charPowerSeries-level
  version of the same conjugation, whose inline steps this ticket re-runs
  vector-level); [Jac Lemma 2.10 + p. 34 eigenspace reading].

#### Generality decision
Generic `K`; no compactoidness needed (pure algebra).  `hν2` not needed (M22op
does not take it).

### [CLEANUP-E1] /cleanup on 2_PadicEmbedding.lean (final) — **Depends on**: E00 —
**done** (2026-08-06: baseline green, diagnostics clean, runLinter zero in-file
findings.  Audit: A-items clean (house conventions: project-first imports +
docstrings-on-privates preserved deliberately); 3-item punch list worked
main-agent-inline (file was fresh from a disciplined worker — per-decl audit
recorded in-phase, workers not spawned for 1-3-line decls): (c) `norm_E₃_eq_one`
nlinarith+hcancel → `le_antisymm h1 ((inv_le_one₀ h0).mp h3)` (−2 lines); (a)
`; exact rfl` at the calc step verified LOAD-BEARING (defeq-not-syntactic after
rw — kept); (b) `valued_E₃_le_one` judged clear as written.  Rebuild green 3430
jobs.  Note: `natGenerator_v₃`/`asIdeal_v₃`/`absNorm_asIdeal_v₃` duplicate
1_Setting privates — deduplication would need publicising them there; recorded
as a future-polish note, out of cleanup scope.)
### [CLEANUP-E2] /cleanup on 5_EigenSlopes.lean (cadence after 3rd + final) — **Depends on**: E03 —
**done** (2026-08-06: diagnostics + warnings ZERO across the whole 600-line file
(the E01 worker + orchestrator kept it clean as written — omit-clauses and binder
hygiene already in place); runLinter zero in-file findings at E01-time; audit
punch list: one item — the module docstring predated E02/E03, EXTENDED with the
strict-transport / M22 / block-transport sections; rebuild green.)

### [CLEANUP-ALL-2] /cleanup-all sweep before the milestone
- **Status**: done (2026-08-06: full E04-closure build green — 8_HeckeSlopes +
  2_PadicEmbedding + 5_EigenSlopes + 5_Instance, 3575 jobs; warning census over
  PhD/JacobsSlash + PhD/QMF: zero besides the contracted 2_Level:673 sorry;
  CLEANUP-W3 verified 4_DiamondW post-W02 at zero warnings/zero in-file linter
  findings.)
- **Depends on**: E00, E01, E02, E03, W02, CLEANUP-E1, CLEANUP-E2, CLEANUP-W3
- (W03–W07 NOT required: E04 does not depend on the certificate wave.)

### [E04] MILESTONE — **the crux**: `U₃` has eigenvalues of valuation `j + ½`
- **Status**: **DONE (2026-08-06, beastmode orchestrator — THE CRUX IS PROVEN)**.
  `PhD/JacobsSlash/U3/9_EigenvaluesU3.lean` created; `exists_eigenvalue_U3_halfIntegral`
  ELABORATED CLEAN ON THE FIRST ATTEMPT; build green (3576 jobs); axioms EXACTLY
  [propext, Classical.choice, Quot.sound] — fully unconditional (no hcn, no sorryAx).
  Statement as ticketed with the W02 flip (`Wop … y = ωC • y`).  Proof: 6 lines —
  E02 (exists_eigenvector_M22op at the ιC-transported parameters, with
  `map_sq_ν₃ ιC` supplying hν2) → E03 (block transport) → det-zero via
  map_charPowerSeriesU3-rewrite + evalT_charPowerSeries_eq_zero_iff.mpr with the
  eigenvector itself as the certificate (inv_inv at a⁻¹) — no evalT-multiplicativity,
  no NP-of-product, exactly as designed.  `ωC := Classical.choose Instance.exists_omega`.
- **File**: PhD/JacobsSlash/U3/9_EigenvaluesU3.lean (NEW; imports U3.«8_HeckeSlopes»,
  U3.«2_PadicEmbedding», «5_EigenSlopes», «5_Instance»)
- **Depends on**: E03, E00, CLEANUP-ALL-2
- **Parallel**: no
- **Type**: theorem (MILESTONE)

#### Statement (skeleton)
```lean
/-- A fixed primitive cube root of unity in `ℂ₃`. -/
noncomputable def ωC : ℂ_[3] := Classical.choose Instance.exists_omega
theorem ωC_spec : ωC ^ 2 + ωC + 1 = 0 := Classical.choose_spec Instance.exists_omega

/-- **THE CRUX** ([Jacobs, Cor 2.16] as an eigenvalue statement about the genuine
`U₃`): over `ℂ₃`, for every `j : ℕ` the base-changed matrix of
`U₃ = [U₁(9)·η₃·U₁(9)]` has an eigenvalue `a` of `3`-adic valuation `j + ½`
(`‖a‖² = ‖3‖^{2j+1}`), whose reciprocal is a zero of the base-changed Fredholm
determinant `det(1 − T·U₃)` of the genuine operator, and whose eigenvector lies in
the `ω²`-eigenspace of the transcribed diamond operator. -/
theorem exists_eigenvalue_U3_halfIntegral (t : K₃) (ht : ‖t‖ < 1) (j : ℕ) :
    ∃ (a : ℂ_[3]) (y : c(Fin 3 × ℕ, ℂ_[3])), a ≠ 0 ∧ y ≠ 0 ∧
      U3MatrixOp (norm_three_lt_one_of_isometry ιC norm_ιC)
          (norm_map_weight_lt_one ιC norm_ιC ht) (map_ν₃_near ιC norm_ιC) y
        = a • y ∧
      ‖a‖ ^ 2 = ‖(3 : ℂ_[3])‖ ^ (2 * j + 1) ∧
      PowerSeries.evalT a⁻¹
        (PowerSeries.map ιC (charPowerSeriesU3 t ht)) = 0 ∧
      Wop (norm_three_lt_one_of_isometry ιC norm_ιC)
          (norm_map_weight_lt_one ιC norm_ιC ht) y = ωC • y := by sorry
```
(W02 flip inherited: the eigenvector lies in the **ω-eigenblock** of the
transcribed diamond operator — `ωC • y`, not `ωC ^ 2 • y`; the thesis's
"ω²" wording is the ω ↦ ω² relabeling, see E03's flip note.)

#### Proof sketch
Work over `K := ℂ_[3]` (instances: 5_Instance's four `example`s + `IsAlgClosed`;
parameters `ω := ωC`, `hω := ωC_spec`, and the genuine images
`ιC t`, `ιC ν₃` with hypotheses from 8_HeckeSlopes' transport layer —
`norm_three_lt_one_of_isometry ιC norm_ιC`, `norm_map_weight_lt_one`,
`map_sq_ν₃ ιC` (for `hν2`!), `map_ν₃_near`).
1. E02 (`exists_eigenvector_M22op` at these parameters) → `a, x` with
   `M22op … x = a • x`, `‖a‖² = ‖3‖^{2j+1}`, `a ≠ 0`, `x ≠ 0`.
2. E03 → `y` with the `U₃`-matrix and `Wop`/`ωC²` clauses.
3. Det-zero clause: rewrite `map_charPowerSeriesU3 ιC norm_ιC t ht`
   (8_HeckeSlopes) to replace the base-changed genuine determinant by
   `charPowerSeries (U3MatrixOp …)`; then
   `evalT_charPowerSeries_eq_zero_iff _ (isCompactoid_U3MatrixOp …) (a⁻¹ ≠ 0)`
   `.mpr ⟨y, hy0, by rw [inv_inv]; exact hyU3⟩` — the eigenvector itself certifies
   the zero (no evalT-multiplicativity, no NP-of-product).
4. Assemble the tuple.

#### Mathlib/project lemmas needed
E02, E03, `map_charPowerSeriesU3` + transports incl. `map_sq_ν₃` (8_HeckeSlopes —
all proved), `evalT_charPowerSeries_eq_zero_iff` (Riesz:2221),
`isCompactoid_U3MatrixOp` (4_DiamondW:407), `Instance.exists_omega`
(5_Instance:126), `IsAlgClosed ℂ_[3]` instance (mathlib PadicComplex).

#### Sources
- [Jac Cor 2.16] (slope statement — 4_SlopeReading:415 docstring); Serre 1962 §7
  Props 11-12 via Riesz.lean's own citations; the composition is this
  development's own.

#### Generality decision
Stated at `ℂ₃` with the GENUINE parameter images (the whole point); the generic
content lives in E01–E03.  Norm-squared valuation form (no `rpow`).

### [E05] FINAL MILESTONE — the culmination: eigenvalues of `U₃` in the `ω`-eigenspace of the genuine diamond operator `W`
- **Status**: **DONE (2026-08-06 — THE CULMINATION IS PROVEN)**.
  `exists_eigenvalue_U3_in_W_eigenspace` in `U3/9_EigenvaluesU3.lean`: E04's tuple plus
  the clause that the genuine `heckeW` acts on every class representative by the
  transcribed `δ` (W07).  Axioms exactly [propext, Classical.choice, Quot.sound].
  **No `map_delta` base-change layer was needed** — because the W-identification is
  twist-free AND stated at the `K₃`-level operator, the `Wop`-clause over `ℂ₃` and the
  `heckeW`-identification compose directly; the ticket's contingency (a δ-analogue of
  3_BaseChange's `map_h`) is recorded as unnecessary.
- **File**: PhD/JacobsSlash/U3/9_EigenvaluesU3.lean
- **Depends on**: E04, W07
- **Parallel**: no
- **Type**: theorem (MILESTONE — assembly + the W-upgrade)

#### Statement (skeleton)
```lean
/-- **The culmination** (Riesz + Newton polygons + the fork): for every `j`, the
genuine `U₃` has an eigenvalue of valuation `j + ½` with eigenvector in the
`ω²`-eigenspace of the genuine diamond operator `W = [U₁(9)·μ·U₁(9)]` — `Wop`
being the matrix of `W` by `blockEntryW_eq_Wop` (W07), so the `Wop`-clause of E04
IS the statement about `W`.  Statement shape: E04's tuple, with the `Wop`-clause
re-expressed through the base change of the W-identification. -/
theorem exists_eigenvalue_U3_in_W_eigenspace (t : K₃) (ht : ‖t‖ < 1) (j : ℕ) :
    -- E04's conclusion, PLUS the clause that the base-changed matrix of the
    -- genuine `heckeW` (via W07's identification + a `map_delta` base-change
    -- layer mirroring 3_BaseChange's `map_h`) acts on `y` by `ωC ^ 2`.
    sorry := by sorry
```
(The exact final form is fixed when W07 lands: the W-identification IS twist-free
(W01 verdict), so the clause is `(base-changed Wop) y = ωC • y` — W02's flip:
block 1 is the ω-eigenblock; the thesis's "ω²-eigenspace of ⟨w⟩" wording is the
ω ↦ ω² relabeling of the same statement (record in the docstring).
Sub-item: `map_delta01/12/20` base-change lemmas if 3_BaseChange's `map_h` layer
does not already cover the δ-generating functions — check first, mirror second.)

#### Proof sketch
Assembly: E04's tuple + W07's `blockEntryW_eq_Wop` read through `PowerSeries.map
ιC`-level coefficient transport (the `map_h` pattern of 3_BaseChange:238-266
applied to the δ-data).  One-line core, plus the (small) `map_delta` layer.

#### Sources
- E04, W07, 3_BaseChange:238-266 (`map_h01`…`map_h21` — the pattern);
  [Jac p. 34: "M₂,₂ is the restriction of U₃ to the ω²-eigenspace of ⟨w⟩"].

### [CLEANUP-E3] /cleanup on 9_EigenvaluesU3.lean (final per-file) — **Depends on**: E05 —
**done** (2026-08-06: zero errors, zero warnings, zero runLinter findings; both
milestones documented with source citations and the ω-relabeling note)
### [CLEANUP-FINAL-2] /cleanup-all + fork PROGRESS.md update (Phase 2 map + axiom audit:
E04/E05 endpoints on exactly [propext, Classical.choice, Quot.sound]; W07 likewise;
sorryAx still ONLY via hClassNumberOne in '-forms) — **Depends on**: CLEANUP-E3, CLEANUP-W2

---

# PHASE 3 ticket board (2026-08-07): close the two audit gaps BY REPLACEMENT

Binding contract for every Phase-3 ticket (user-directed): **this is a replacement
refactor.** A ticket that leaves the object it supersedes alive has failed, even if it
builds. Each ticket names its DELETIONS explicitly; the `/beastmode` worker must perform
them and must not re-add an "old name = new name" compatibility shim. Standing fork rules
still apply (never import `PhD.Jacobs`; no new axioms; `hClassNumberOne` untouched).

Net-LOC expectation: Phase 3 should REMOVE more lines than it adds (~275 duplicated κ-layer
lines + ~40 of narrow plumbing out; ~120 of `map_delta`/`map_Wop`/E05 in).

### [U1] Move the `Σ₁(3)` layer into `U3/1_Setting`
- **Status**: done (2026-08-07; full chain green, 3577 jobs, zero warnings in both files).
  **SPLIT ADJUSTED vs the ticket (recorded)**: only the *pure monoid* layer moved to
  `1_Setting` — `γ₃`, `γ₃_lt_one`, `valued_three_eq_γ₃`, `γ₉_le_γ₃`, `Sigma1₃`,
  `mem_sigma1₃_iff`, `sigma1_le_sigma1₃` (7 decls) — under a new
  "The tame acting monoid Σ₁(3)" section header explaining why Σ₁(3) is the honest
  domain.  The six `norm_sigma1₃_*` workhorses CANNOT live there: they use
  `norm_le_of_valued_le`, which is defined in `«4_KappaSlash»:88` (above `1_Setting` in
  the import order).  They stay put and move with the κ-layer in U2 — which is where they
  belong anyway (κ-support, next to their only consumers).  `levelMonoid1₃` +
  `levelMonoid1_le_levelMonoid1₃` + `U1_9_subset_levelMonoid1₃` also stayed: they need
  `U1_9`/`levelMonoid1` from `«2_Level»`; they move to `«6_Matrix»` in U3 as planned.
  Trap for later tickets: `lake env lean` on a downstream file reads STALE oleans after
  editing an upstream one — always `lake build` first, then re-check.
- **File**: PhD/JacobsSlash/U3/1_Setting.lean (add), PhD/JacobsSlash/U3/7_DiamondHecke.lean (delete)
- **Depends on**: none
- **Parallel**: yes (with M1)
- **Type**: def + lemmas (MOVE — no new mathematics)

#### Statement
Move verbatim from `«7_DiamondHecke»` (lines ~55–172) to `U3/1_Setting.lean`, placed
immediately after `Sigma1`/`mem_sigma1_iff`, deleting the originals:
```lean
def γ₃ : WithZero (Multiplicative ℤ)
theorem γ₃_lt_one : γ₃ < 1
theorem valued_three_eq_γ₃ : Valued.v (3 : K₃) = γ₃
theorem γ₉_le_γ₃ : γ₉ ≤ γ₃
def Sigma1₃ : Submonoid (Matrix (Fin 2) (Fin 2) K₃)
theorem mem_sigma1₃_iff {g : Matrix (Fin 2) (Fin 2) K₃} :
    g ∈ Sigma1₃ ↔ g ∈ Sigma0' K₃ γ₉ γ₉_lt_one ∧ Valued.v (g 1 1 - 1) ≤ γ₃
theorem sigma1_le_sigma1₃ : Sigma1 ≤ Sigma1₃
theorem sigma1₃_lower_right_ne_zero (g : Sigma1₃) : g.1 1 1 ≠ 0
theorem norm_sigma1₃_entry_le_one (g : Sigma1₃) : ∀ i j : Fin 2, ‖g.1 i j‖ ≤ 1
theorem norm_sigma1₃_lower_right_sub_one_le (g : Sigma1₃) : ‖g.1 1 1 - 1‖ ≤ ‖(3 : K₃)‖
theorem norm_sigma1₃_lower_right (g : Sigma1₃) : ‖g.1 1 1‖ = 1
theorem norm_sigma1₃_lower_left_le (g : Sigma1₃) : ‖g.1 1 0‖ ≤ ‖(3 : K₃)‖ ^ 2
theorem norm_sigma1₃_ratio_le (g : Sigma1₃) : ‖g.1 1 0 / g.1 1 1‖ ≤ ‖(3 : K₃)‖ ^ 2
```

#### Proof sketch
1. Cut the block from `«7_DiamondHecke»` and paste after `1_Setting`'s `mem_sigma1_iff`.
   Proof bodies transfer verbatim: every ingredient they use (`Sigma0'`, `γ₉`,
   `γ₉_lt_one`, the `Valued.v (3 : K₃)` computation, `norm_ofNat_eq_one` from the imported
   `«2_U3Data»`) is already in `1_Setting`'s scope — verified 2026-08-07.
2. `lake build PhD.JacobsSlash.U3.«1_Setting»`, then `«7_DiamondHecke»` (which now sees
   them through its import chain — no import edit needed).
3. **DELETIONS (required)**: the moved declarations must not remain in `«7_DiamondHecke»`.

#### Mathlib/project lemmas needed
None new; the bodies are unchanged.

#### Sources
Board tickets W03 (which authored these) and the Phase-3 plan section "Gap 1"; the
mathematical justification for Σ₁(3) being the honest domain is the `hγ9le3` observation
recorded in `.mathlib-quality/jacobs-endgame/decomposition.md` §AG-W-ID.

#### Generality decision
`K₃`-level, unchanged from the originals — these are setting-level facts and belong beside
`Sigma1` in the setting file.

### [U2] Migrate the κ-layer to `Σ₁(3)` inside `«4_KappaSlash»`, deleting the narrow one
- **Status**: done (2026-08-07; 4_KappaSlash green, 3438 jobs, zero warnings).
  **ROUTE IMPROVEMENT — no cut-paste was needed.**  The six workhorses have *norm-side*
  conclusions (`‖g.1 1 1 − 1‖ ≤ ‖3‖`, …) that never mention γ₉ or γ₃, so retyping the
  κ-layer's arguments from `Sigma1` to `Sigma1₃` **in place** changes only three proof
  bodies and nothing downstream: total diff ≈ 12 lines instead of a 275-line move.
  Done: `(g : Sigma1) → (g : Sigma1₃)` etc. throughout the layer; the three
  `hγ9le3`-weakening bodies (`coeffInt_weightGenFun`, `shiftInt_weightGenFun`,
  `norm_sigma1_lower_right_sub_one_le`) replaced by the direct
  `le_of_eq valued_three_eq_γ₃.symm` form; `(1 : Sigma1)`/`((g*h) : Sigma1)` ascriptions
  in `kappaSlash_one`/`kappaSlash_mul` retyped.  Names kept plain (`kappaSlash`,
  `norm_sigma1_*`, `kappaSlashAction`) — with one layer there is no `Wide` to
  disambiguate.  DELETIONS in `«7_DiamondHecke»`: the whole `WideKappa` section (~13.1k
  chars), the six `norm_sigma1₃_*` workhorses (~1.8k), and the duplicate
  `kappaSlash_one`/`kappaSlashAction` (~1.2k).  `kappaSlashWide_restrict` deleted, not
  restated — with a single operator it has no content.
- **File**: PhD/JacobsSlash/U3/4_KappaSlash.lean (replace), PhD/JacobsSlash/U3/7_DiamondHecke.lean (delete)
- **Depends on**: U1
- **Parallel**: no
- **Type**: def + lemmas (MIGRATION — the largest ticket; no new mathematics)

#### Statement
Move `«7_DiamondHecke»`'s `WideKappa` section (lines ~173–447) into `«4_KappaSlash»`,
**deleting the corresponding Σ₁(9) declarations there**, and drop the `Wide` suffix
throughout (the surviving operator is *the* κ-slash):
```lean
-- pack-based (kept, they are the general form):
theorem coeffInt_weightGenFun' (ht : ‖t‖ < 1) {γ : Matrix (Fin 2) (Fin 2) K₃} …
theorem shiftInt_weightGenFun' (ht : ‖t‖ < 1) {γ : Matrix (Fin 2) (Fin 2) K₃} …
theorem tendsto_coeff_weightGenFun' (ht : ‖t‖ < 1) {γ : Matrix (Fin 2) (Fin 2) K₃} …
-- Σ₁(3) instantiations (renamed from *_sigma1₃ to the plain names the narrow ones had):
theorem norm_coeff_weightGenFun_le_one (ht : ‖t‖ < 1) (g : Sigma1₃) (m r : ℕ) : …
theorem tendsto_coeff_weightGenFun (ht : ‖t‖ < 1) (g : Sigma1₃) (r : ℕ) : …
noncomputable def kappaSlash (ht : ‖t‖ < 1) (g : Sigma1₃) : c(ℕ, K₃) →L[K₃] c(ℕ, K₃)
theorem matrixCoeff_kappaSlash (ht : ‖t‖ < 1) (g : Sigma1₃) (j i : ℕ) : …
theorem kappaSlash_one (t : K₃) (ht : ‖t‖ < 1) : kappaSlash t ht 1 = ContinuousLinearMap.id K₃ c(ℕ, K₃)
theorem kappaSlash_mul (ht : ‖t‖ < 1) (g h : Sigma1₃) :
    kappaSlash t ht (g * h) = (kappaSlash t ht h).comp (kappaSlash t ht g)
noncomputable def kappaSlashAction (t : K₃) (ht : ‖t‖ < 1) : RightSlashAction Sigma1₃ c(ℕ, K₃)
-- plus the cocycle-support family, Σ₁(3)-indexed, keeping the plain names:
--   coeffLeOne_mobius, absSummable_linX_inv, absSummable_mobius, absSummable_kappaCol,
--   absSummable_autFactor, autFactor_cocycle, absSummable_yCoeff_weightGenFun,
--   yCoeff_weightGenFun_mul
```

#### Proof sketch
1. In `«4_KappaSlash»`, DELETE the Σ₁(9) κ-layer: the six `norm_sigma1_*` /
   `sigma1_lower_right_ne_zero` workhorses (~lines 1275–1330), the `coeffLeOne_mobius_sigma1`
   … `yCoeff_weightGenFun_mul_sigma1` family, `kappaSlash`+`matrixCoeff_kappaSlash`
   (~lines 394–410), `kappaSlash_one`, `kappaSlash_mul`, `kappaSlashAction` (~1340–1570).
   Verified 2026-08-07: **no declaration outside this file uses any of them** except
   `kappaSlashAction`, whose four `letI` users die in U3/U4.
2. Paste `«7_DiamondHecke»`'s `WideKappa` bodies in their place, in the same order.  They
   were authored by copying these very proofs with the `hγ9le3` weakening step removed, so
   they compile against the same ambient API.
3. Rename in the pasted block: `kappaSlashWide` → `kappaSlash`, `*_sigma1₃` → the plain
   names listed above (mathlib style: the Σ₁(3) instantiation is *the* statement now).
   Keep the primed pack lemmas primed.
4. `lake env lean` then `lake build PhD.JacobsSlash.U3.«4_KappaSlash»`; expect only the
   downstream files to break (fixed in U3/U4/U5).
5. **DELETIONS (required)**: `kappaSlashWide_restrict` is deleted, not restated — with a
   single κ-operator it has no content.

#### Mathlib/project lemmas needed
None new. Internal API used by the pasted bodies (`ofGenFun`, `matrixCoeff_ofGenFun`,
`weightGenFun`, `yCoeff_weightGenFun`, `compAn_mobius_mobius`, `kappaCol_cocycle`) is all
in `«4_KappaSlash»` above the migrated block and is untouched.

#### Sources
Phase-3 plan "Gap 1"; the W03 board notes recording that the pack is
(entries ≤ 1, ‖g₁₁−1‖ ≤ ‖3‖, ‖g₁₀/g₁₁‖ ≤ ‖3‖²) and that `g₁₁ ≠ 0` is derivable.

#### Generality decision
The primed lemmas stay stated over the explicit hypothesis pack (maximal generality within
the file); the Σ₁(3) instantiations are the user-facing API.  `Sigma1` is *not* removed — it
remains the level congruence of `U₁(9)`; only its role as an acting monoid ends.

### [CLEANUP-U1] /cleanup on PhD/JacobsSlash/U3/4_KappaSlash.lean
- **Status**: done (2026-08-07: module header retitled to `Σ₁(3)`, the `kappaSlash`/`kappaModuleAction` bullets now state why Σ₁(3) is the honest domain and that it is the single acting monoid; zero warnings, zero linter findings) — **Depends on**: U2 — **Type**: cleanup
- Post-migration hygiene on the largest edited file: dead `open`s, docstrings that still
  say "Σ₁(9)" where the domain is now Σ₁(3), stale module-header bullets.

### [U3] Single acting monoid and single form space in `«6_Matrix»`
- **Status**: done (2026-08-07; green, 3453 jobs).  `levelMonoid1` → `levelMonoid1₃`
  (`Sigma1₃.comap`), `levelMonoid1ToSigma1` → `levelMonoid1₃ToSigma1₃` (`submonoidComap
  Sigma1₃`), and every membership fact composed with `sigma1_le_sigma1₃` exactly as
  planned — `U1_9_subset_levelMonoid1₃`, `etaRep_mem_levelMonoid1₃`,
  `toMatrix_uTable_mul_etaRep_mem_sigma1₃`; `eta3_mem_levelMonoid1₃` kept its direct
  entry-by-entry proof (the `(1,1)`-entry is `1`, so the γ₃ conjunct is `simp`).
  **All statements of `matrixCoeff_blockEntry` / `blockEntry_eq_epsOp` /
  `charPowerSeries_blockEntry_eq_U3MatrixOp` / `heckeU3_apply_classRep` /
  `eval_classRep_injective` are byte-identical** — only the plumbing moved.  Docstring
  now records that `Δ₁(3)` is the single acting monoid shared with `heckeW`.
- **File**: PhD/JacobsSlash/U3/6_Matrix.lean
- **Depends on**: U2
- **Parallel**: yes (with U5, after U2)
- **Type**: def + lemmas (REPLACEMENT)

#### Statement
```lean
-- REPLACES `levelMonoid1` (deleted): the single acting monoid.
noncomputable def levelMonoid1₃ : Submonoid (Dfx ℚ D) := Sigma1₃.comap (toMatrix ℚ D v₃)
theorem U1_9_subset_levelMonoid1₃ : (U1_9 : Set (Dfx ℚ D)) ⊆ levelMonoid1₃
theorem eta3_mem_levelMonoid1₃ : eta3 ∈ levelMonoid1₃
theorem etaRep_mem_levelMonoid1₃ (t' : Fin 3) : etaRep t' ∈ levelMonoid1₃
noncomputable def levelMonoid1₃ToSigma1₃ : levelMonoid1₃ →* Sigma1₃
@[instance_reducible] noncomputable def kappaLevelSlashAction (t : K₃) (ht : ‖t‖ < 1) :
    RightSlashAction levelMonoid1₃ c(ℕ, K₃)
theorem kappaLevelSMulSlashClass (t : K₃) (ht : ‖t‖ < 1) :
    letI := kappaLevelSlashAction t ht; SMulSlashClass K₃ levelMonoid1₃ c(ℕ, K₃)
noncomputable def kappaForms (t : K₃) (ht : ‖t‖ < 1) :
    Submodule K₃ (AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃))   -- now at Δ₁(3)
noncomputable def heckeU3 (t : K₃) (ht : ‖t‖ < 1) : kappaForms t ht →ₗ[K₃] kappaForms t ht
theorem toMatrix_uTable_mul_etaRep_mem_sigma1₃ (i t' : Fin 3) :
    toMatrix ℚ D v₃ ((uTable i t' : Dfx ℚ D) * etaRep t') ∈ Sigma1₃
noncomputable def blockEntry (t : K₃) (ht : ‖t‖ < 1) (i j : Fin 3) : c(ℕ, K₃) →L[K₃] c(ℕ, K₃)
-- statements of matrixCoeff_blockEntry / blockEntry_eq_epsOp /
-- charPowerSeries_blockEntry_eq_U3MatrixOp / heckeU3_apply_classRep /
-- eval_classRep_injective(') are UNCHANGED.
```

#### Proof sketch
1. Rename `levelMonoid1` → `levelMonoid1₃` and repoint its definition at `Sigma1₃`.  The
   membership proofs get *shorter*, not longer: `eta3_mem_levelMonoid1₃` and
   `etaRep_mem_levelMonoid1₃` are the existing Σ₁(9) proofs post-composed with
   `sigma1_le_sigma1₃` (`Submonoid.mem_comap.mpr (sigma1_le_sigma1₃ …)`); likewise
   `toMatrix_uTable_mul_etaRep_mem_sigma1₃`.  Keep the Σ₁(9) versions only if still used —
   they are not; delete them.
2. `levelMonoid1₃ToSigma1₃ := (toMatrix ℚ D v₃).submonoidComap Sigma1₃`; the
   `kappaLevelSlashAction` / `kappaLevelSMulSlashClass` bodies are unchanged apart from the
   monoid names (they only use `map_one`/`map_mul`/`slash_*`).
3. `blockEntry`'s subtype membership argument changes from the Σ₁(9) proof to the Σ₁(3) one;
   `matrixCoeff_blockEntry`'s proof is unchanged (`matrixCoeff_kappaSlash` now takes a
   `Sigma1₃` argument but has the same conclusion — the coefficient of `weightGenFun` at the
   same matrix).
4. `heckeU3_apply_classRep`: the S11 call's `hact` argument becomes
   `Submonoid.mem_comap.mpr (toMatrix_uTable_mul_etaRep_mem_sigma1₃ i t')`; everything else
   is unchanged.  `eval_classRep_injective` needs only the renamed `hU`.
5. `lake build PhD.JacobsSlash.U3.«6_Matrix»`; `#print axioms` on
   `heckeU3_apply_classRep` and `blockEntry_eq_epsOp` — must stay
   `[propext, Classical.choice, Quot.sound]`.
6. **DELETIONS (required)**: `levelMonoid1`, `levelMonoid1ToSigma1`, and any Σ₁(9)-valued
   membership lemma left unused.

#### Mathlib/project lemmas needed
`sigma1_le_sigma1₃` (U1), `Submonoid.mem_comap`, `MonoidHom.submonoidComap`,
`AutomorphicFunction.heckeOperatorSlash_apply_rep` (`PhD/QMF/Slash/HeckeMatrix.lean:57`,
unchanged), `AbstractHeckeOperatorSlash.heckeOperatorSlash` (`HeckeMonoid.lean:144`).

#### Sources
Phase-3 plan "Gap 1"; the existing `«6_Matrix»` (this ticket is a re-basing of it, not a
re-derivation).

#### Generality decision
Unchanged from the current file: `K₃`/`D`-level, right-slash native.  The single behavioural
change is the acting monoid, which *weakens* the ambient hypothesis (Σ₁(9) ⊆ Σ₁(3)) and so
strengthens every consumer.

### [U4] Re-base `«7_Fredholm»` onto the single space (proof-level only)
- **Status**: done (2026-08-07; green.  Exactly the three sites the ticket predicted —
  `U1_9_subset_levelMonoid1₃` in the `bijective_evalAtRepsSlash` call and the two
  `levelMonoid1₃` occurrences in the `∀ p, ⟨v, p⟩ = 1` rewrite.  Every statement in the
  file is unchanged.  `«9_EigenvaluesU3»`'s stale `kappaFormsWide` reference was
  repointed to `kappaForms` in passing; M3 replaces that clause outright.)
- **U-TRANCHE VERIFICATION**: full chain green (3577 jobs) and ZERO errors/warnings in
  all six touched files (`1_Setting`, `4_KappaSlash`, `6_Matrix`, `7_Fredholm`,
  `7_DiamondHecke`, `9_EigenvaluesU3`).
- **File**: PhD/JacobsSlash/U3/7_Fredholm.lean
- **Depends on**: U3
- **Parallel**: yes (with U5)
- **Type**: lemma (REBASE — statements unchanged)

#### Statement
All statements (`evalU3`, `blockProj_evalU3`, `bijective_evalU3`, `kappaFormsModelEquiv`,
`evalU3_heckeU3`, `isCompactoid_blockOpU3`, `charPowerSeriesU3`,
`charPowerSeriesU3_eq_U3MatrixOp`) are **unchanged**; only the instance plumbing inside the
proofs moves to the single monoid.

#### Proof sketch
1. Replace the `letI := kappaSlashAction t ht` / `letI := kappaLevelSlashAction t ht` /
   `haveI := kappaLevelSMulSlashClass t ht` triples with the new (identically-named)
   Σ₁(3)-based ones — the names are unchanged, so in most proofs the edit is nil once
   `«6_Matrix»` is re-based.
2. `bijective_evalU3`'s surjectivity uses `U1_9_subset_levelMonoid1` in the
   `bijective_evalAtRepsSlash` call and in the `∀ p, ⟨v, p⟩ = 1` rewrite — repoint both to
   `U1_9_subset_levelMonoid1₃` and `levelMonoid1₃`.
3. `lake build`; `#print axioms bijective_evalU3` (must stay standard — it takes `hcn` as a
   hypothesis, so no `sorryAx`).

#### Mathlib/project lemmas needed
`AutomorphicFunction.bijective_evalAtRepsSlash` (`HeckeMatrix.lean:181`),
`stabilizerAt_classRep` (`3_ClassSet`), `exists_classRep_section` — all unchanged.

#### Sources
Phase-3 plan "Gap 1"; the existing `«7_Fredholm»`.

#### Generality decision
Unchanged.

### [U5] `heckeW` on the single space; delete the wide duplicates in `«7_DiamondHecke»`
- **Status**: done (2026-08-07; green, 3454 jobs, zero warnings; file 1057 → 616 lines).
  **GAP 1 IS CLOSED BY CONSTRUCTION** — no `kappaFormsWide_eq_kappaForms` lemma exists
  or is needed.  Deleted: the duplicate `levelMonoid1₃` block, the entire wide plumbing
  (`levelMonoid1₃ToSigma1₃`, `kappaWideLevelSlashAction`, `kappaWideLevelSMulSlashClass`,
  `kappaFormsWide`), and the orphaned section headers.  `heckeW` is now the same
  `heckeOperatorSlash` construction as `heckeU3` over `levelMonoid1₃`, at `μ` instead of
  `η₃`, so its type is literally `kappaForms t ht →ₗ[K₃] kappaForms t ht`.
  **ACCEPTANCE TEST PASSED** (scratch file): `(heckeU3 t ht).comp (heckeW t ht)`
  elaborates, and a single `φ : kappaForms t ht` feeds `heckeU3_apply_classRep`,
  `heckeW_apply_classRep_eq_delta`, and `heckeU3_apply_classRep _ _ (heckeW t ht φ) i`
  in one proof context.  Axioms of `heckeW_apply_classRep_eq_delta` unchanged:
  [propext, Classical.choice, Quot.sound].
- **File**: PhD/JacobsSlash/U3/7_DiamondHecke.lean
- **Depends on**: U2, M1
- **Parallel**: yes (with U3/U4 once U2 lands, but must follow M1)
- **Type**: def + lemmas (REPLACEMENT)

#### Statement
```lean
theorem mu3_mem_levelMonoid1₃ : mu3 ∈ levelMonoid1₃              -- unchanged statement
theorem uTableW_mul_mu3_mem_levelMonoid1₃ (i : Fin 3) : ((uTableW i : Dfx ℚ D) * mu3) ∈ levelMonoid1₃
noncomputable def heckeW (t : K₃) (ht : ‖t‖ < 1) :
    kappaForms t ht →ₗ[K₃] kappaForms t ht                        -- was kappaFormsWide
theorem heckeW_apply_classRep (t : K₃) (ht : ‖t‖ < 1) (φ : kappaForms t ht) (i : Fin 3) :
    (heckeW t ht φ : AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) (classRep i)
      = kappaSlash t ht ⟨toMatrix ℚ D v₃ ((uTableW i : Dfx ℚ D) * mu3), …⟩
          ((φ : AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) (classRep (sigmaW i)))
theorem kappaSlash_acting_eq_delta (ht : ‖t‖ < 1) (i : Fin 3) :
    kappaSlash t ht ⟨toMatrix ℚ D v₃ ((uTableW i : Dfx ℚ D) * mu3), …⟩ = deltaOf ht i
theorem heckeW_apply_classRep_eq_delta (t : K₃) (ht : ‖t‖ < 1) (φ : kappaForms t ht) (i : Fin 3) :
    (heckeW t ht φ : AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) (classRep i)
      = deltaOf ht i ((φ : AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃))
          (classRep (sigmaW i)))
```

#### Proof sketch
1. Delete the `WideKappa` section (moved by U2) and the `Σ₁(3)` block (moved by U1).
2. Delete `levelMonoid1₃ToSigma1₃`, `kappaWideLevelSlashAction`,
   `kappaWideLevelSMulSlashClass`, `kappaFormsWide` — `«6_Matrix»` now provides the single
   corestriction, action and space under those roles.
3. Delete `sigmaTableW` and `deltaOf` (moved to `«4_DiamondW»` by M1); repoint every
   certificate declaration (`dTableW`, `uCandW`, `factorisationW`, `toMatrix_uCandW`, …) to
   `sigmaW`.  This is a pure rename — the tables are numerically identical, `![1,2,0]`.
4. `heckeW := heckeOperatorSlash K₃ U1_9_subset_levelMonoid1₃ U1_9_subset_levelMonoid1₃
   mu3_mem_levelMonoid1₃ finite_image_mu3` — the *same* `heckeOperatorSlash` call as
   `heckeU3` but at `μ`, so it lands on `kappaForms` by construction.  **This is where
   Gap 1 closes**: no `kappaFormsWide_eq_kappaForms` lemma is written, because there is no
   second space to identify.
5. `heckeW_apply_classRep` and `heckeW_apply_classRep_eq_delta` keep their proofs verbatim
   modulo the renames (`kappaSlashWide` → `kappaSlash`, `sigmaTableW` → `sigmaW`).
6. `lake build`; `#print axioms heckeW_apply_classRep_eq_delta` must stay standard.
7. **Acceptance check (the point of the ticket)**: `heckeU3 t ht` and `heckeW t ht` must
   have *literally the same* type `kappaForms t ht →ₗ[K₃] kappaForms t ht`.  Record a
   `example : (heckeU3 t ht).comp (heckeW t ht) = (heckeU3 t ht).comp (heckeW t ht) := rfl`-style
   type-agreement check in the ticket notes (it type-checks only if the spaces coincide).

#### Mathlib/project lemmas needed
`heckeOperatorSlash`, `AutomorphicFunction.heckeOperatorSlash_apply_rep`,
`Subsingleton.elim` (the `Fin 1` injectivity), `Finset.univ_unique`, `Finset.sum_singleton`
— all as used today.

#### Sources
Phase-3 plan "Gap 1"; W07's existing proofs.

#### Generality decision
Unchanged; `heckeW`'s type is *narrowed* to the canonical space, which is the deliverable.

### [CLEANUP-U2] /cleanup on PhD/JacobsSlash/U3/7_DiamondHecke.lean
- **Status**: done (2026-08-07: module header rewritten for what remains (the file lost ~440 lines and its whole wide-κ section): now documents μ, the single coset, the certificates and the twist-free δ-identification, and records that Σ₁(3) moved to its proper depth; zero warnings) — **Depends on**: U5 — **Type**: cleanup
- The file loses ~400 lines; check the module docstring still describes what remains, and
  that no `open`/import survives only for deleted material.

### [CLEANUP-U3] /cleanup on PhD/JacobsSlash/U3/6_Matrix.lean — **Depends on**: U3
### [CLEANUP-U4] /cleanup on PhD/JacobsSlash/U3/7_Fredholm.lean — **Depends on**: U4
### [CLEANUP-U5] /cleanup on PhD/JacobsSlash/U3/1_Setting.lean — **Depends on**: U1

### [M1] `sigmaW`, `deltaOf`, and `Wop = blockOp (δ at σ_W)` in `«4_DiamondW»`
- **Status**: done (2026-08-07; FIRST-ATTEMPT green).  `sigmaW`, `sigmaW_ne`
  (`decide +revert`), `deltaOf`, and `Wop_eq_blockOp_deltaOf` (`congrArg blockOp` +
  `funext` + `fin_cases`² + `simp [sigmaW, deltaOf]`) — placed inside `section W` so the
  `h3 ht` section variables apply.  **The certificate permutation is now definitionally
  `Wop`'s block layout**: `«7_DiamondHecke»`'s `sigmaTableW`/`deltaOf` were DELETED and
  every certificate declaration re-indexed off these (generic-`K`, shared).
- **File**: PhD/JacobsSlash/4_DiamondW.lean
- **Depends on**: none
- **Parallel**: yes (with U1/U2)
- **Type**: def + lemma

#### Statement
```lean
/-- The block-layout permutation of `Wop`: the 3-cycle `0 ↦ 1 ↦ 2 ↦ 0`. -/
def sigmaW : Fin 3 → Fin 3 := ![1, 2, 0]

theorem sigmaW_ne (i : Fin 3) : sigmaW i ≠ i

/-- The transcribed `δ`-operators indexed by the source class. -/
noncomputable def deltaOf (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1) (i : Fin 3) :
    c(ℕ, K) →L[K] c(ℕ, K) :=
  ![delta01 h3 ht, delta12 h3 ht, delta20 h3 ht] i

/-- `Wop`'s transcribed block layout IS the `σ_W`-indexed `δ`-matrix. -/
theorem Wop_eq_blockOp_deltaOf :
    Wop h3 ht = blockOp (fun i j => if j = sigmaW i then deltaOf h3 ht i else 0)
```

#### Proof sketch
1. `sigmaW_ne`: `decide +revert`.
2. `Wop_eq_blockOp_deltaOf`: `congrArg blockOp` on the matrix argument, then
   `funext i j` + `fin_cases i <;> fin_cases j` + `simp [sigmaW, deltaOf]` — nine numeric
   checks, each `rfl`-shaped: row 0 hits `δ₀,₁` at `j = 1 = σ_W 0`, row 1 hits `δ₁,₂` at
   `j = 2 = σ_W 1`, row 2 hits `δ₂,₀` at `j = 0 = σ_W 2`, and the six others are `0`.
   (Read `Wop`'s definition at `4_DiamondW:684-688` — the layout matches by inspection;
   this ticket is what turns that inspection into a theorem.)
3. Place next to `Wop` (inside `section W`, whose variables `h3 ht` are already in scope).

#### Mathlib/project lemmas needed
`blockOp` (`«1_BlockOp»:628`), `Matrix.cons_val_*` simp set, `decide`.

#### Sources
Phase-3 plan, "A third duplication removed"; [Jacobs, (2.1.10) and p. 32] — the display
whose block-cyclic layout `Wop` transcribes; the fork W-oracle
`U3/certificate_search_w.py` (σ_W = (1,2,0), the same cycle).

#### Generality decision
Generic `K` (the file's section context: `NontriviallyNormedField`, `IsUltrametricDist`,
`CompleteSpace`, `CharZero`) — this is transcription-level, no quaternionic content, which
is precisely why it can live below the U3 layer and be shared.

### [M2] `map_delta01/12/20` and `map_Wop`: the δ-side base change
- **Status**: done (2026-08-07; green, zero warnings).  `«4_DiamondW»` gained
  `import PhD.JacobsSlash.«3_BaseChange»` (prefix stays 4, no cycle) and a
  `BaseChangeW` section: generic transport lemmas `norm_three_lt_one_of_isometry'` /
  `norm_map_lt_one'`, a shared private `matrixCoeff_delta_scaled`
  (`matrixCoeff_smul` + `matrixCoeff_diagOp`), the three `map_delta*`, and `map_Wop`
  (`matrixCoeff_blockOp` + `fin_cases`² → three `map_delta*` and six `map_zero`), exactly
  mirroring `map_charPowerSeriesU3`.  Traps: `map_inv₀` is ambiguous with
  `MvPowerSeries.map_inv₀` (use `_root_.map_inv₀`); the numeral pushes want a single
  `simp only [map_mul, map_pow, map_div₀, map_ofNat, …, map_unitPow f hf]` rather than a
  hand-ordered `rw` chain (`f 7` was left unreduced by the latter).
- **File**: PhD/JacobsSlash/4_DiamondW.lean (+ one new import)
- **Depends on**: M1
- **Parallel**: no
- **Type**: lemma

#### Statement
```lean
-- new import at the top of 4_DiamondW: import PhD.JacobsSlash.«3_BaseChange»
theorem map_delta01 (f : K →+* L) (hf : ∀ x, ‖f x‖ = ‖x‖) (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1)
    (m r : ℕ) :
    matrixCoeff (delta01 (norm_three_lt_one_of_isometry' f hf h3) (norm_map_lt_one' f hf ht)) m r
      = f (matrixCoeff (delta01 h3 ht) m r)
-- likewise map_delta12, map_delta20
theorem map_Wop (f : K →+* L) (hf : ∀ x, ‖f x‖ = ‖x‖) (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1)
    (x z : Fin 3 × ℕ) :
    matrixCoeff (Wop (norm_three_lt_one_of_isometry' f hf h3) (norm_map_lt_one' f hf ht)) x z
      = f (matrixCoeff (Wop h3 ht) x z)
```
(The transport hypotheses are the generic-`K` analogues of `«8_HeckeSlopes»`'s
`norm_three_lt_one_of_isometry` / `norm_map_weight_lt_one`, which are stated there only for
`K₃`; state the two generic versions in this file — one line each — rather than importing
`«8_HeckeSlopes»`, which sits above this file.)

#### Proof sketch
1. Each `delta` is `scalar • diagOp (fun n => D ^ n)`.  `matrixCoeff` of that is
   `matrixCoeff_smul` + `matrixCoeff_diagOp` (`«1_GenFun»:345`) =
   `scalar * (if m = r then D ^ m else 0)`.
2. Push `f` through: `map_mul`, `map_ite`/`apply_ite f`, `map_pow`, `map_div₀`, `map_ofNat`,
   and — the only non-formal step — `map_unitPow f hf` (`«3_BaseChange»:139`) for the
   `κ(d)` factor, exactly as `map_h01` uses `map_weightGenFun`.  The three scalars are
   `4·κ(−1/2)`, `4·κ(−1/2)`, `κ(4)/16`; the three ratios `2/5, 10/7, 7/4` are numerals, so
   `map_div₀`/`map_ofNat` close them.
3. `map_Wop`: `obtain ⟨a, j⟩ := x; obtain ⟨b, i⟩ := z`, `matrixCoeff_blockOp`, then
   `fin_cases a <;> fin_cases b` — three cases are the `map_delta*` above and six are
   `(map_zero f).symm`.  This mirrors `map_charPowerSeriesU3`'s proof
   (`«8_HeckeSlopes»`) line for line.
4. `lake build PhD.JacobsSlash.«4_DiamondW»`, then the whole fork (this file is deep in the
   tree).

#### Mathlib/project lemmas needed
`map_unitPow` (`«3_BaseChange»:139`, verified to exist), `map_binomialCoeff` (:133),
`matrixCoeff_diagOp` (`«1_GenFun»:345`), `matrixCoeff_smul`, `matrixCoeff_blockOp`
(`«1_BlockOp»:649`), `matrixCoeff_zero`, `apply_ite`, `map_div₀`, `map_ofNat`, `map_pow`.

#### Sources
Phase-3 plan "Gap 2"; the ε-side template `map_h01 … map_h21` (`«3_BaseChange»:238-266`)
and its consumer `map_charPowerSeriesU3` (`«8_HeckeSlopes»`).

#### Generality decision
Generic `K → L` along any isometric ring hom, matching `map_h*`'s generality exactly — not
specialised to `ιC`, so the same lemmas serve any future base change.

### [CLEANUP-M1] /cleanup on PhD/JacobsSlash/4_DiamondW.lean — **Depends on**: M2
- Two proof tickets on this file (M1, M2) plus W02's earlier addition; final per-file pass.

### [CLEANUP-ALL-3] /cleanup-all across the Phase-3 diff — **Depends on**: CLEANUP-U1..U5, CLEANUP-M1
- **Status**: done (2026-08-07).  Full-fork build GREEN (3577 jobs); the ONLY warning in
  `PhD/JacobsSlash` is the contracted `2_Level:673` sorry; runLinter reports ZERO findings
  in all seven Phase-3 files; per-file error+warning census is 0 across
  `1_Setting`, `4_KappaSlash`, `6_Matrix`, `7_Fredholm`, `7_DiamondHecke`,
  `9_EigenvaluesU3`, `4_DiamondW`.  Axiom sweep: `exists_eigenvalue_U3_in_W_eigenspace`,
  `exists_eigenvalue_U3_halfIntegral`, `map_Wop`, `Wop_eq_blockOp_deltaOf`,
  `heckeW_apply_classRep_eq_delta`, `heckeU3_apply_classRep` — all exactly
  [propext, Classical.choice, Quot.sound].  Net LOC: the fork is 16 933 lines after
  removing ~16 k characters of duplicated κ-layer and plumbing and adding ~150 lines of
  base-change; the replacement contract held (deletions exceed additions).

### [M3] MILESTONE — E05 as ONE composed statement
- **Status**: **DONE (2026-08-07 — GAP 2 CLOSED)**.  `exists_eigenvalue_U3_in_W_eigenspace`
  now ends in the single clause
  `∀ W', (∀ x z, matrixCoeff W' x z = ιC (matrixCoeff (Wop norm_three_lt_one ht) x z)) →
  W' y = ωC • y` — "y is an ω-eigenvector of the base change of the matrix of the genuine
  W".  Proof: E04's tuple, then `ext_matrixCoeff` + `map_Wop` identify any such `W'` with
  `Wop` over ℂ₃ and E04's clause closes it.  **DELETION performed**: the old
  `∀ (φ : kappaFormsWide …) …` conjunct is gone — its content is
  `heckeW_apply_classRep_eq_delta`, cited from the docstring together with
  `Wop_eq_blockOp_deltaOf` as the justification of the hypothesis.  Axioms:
  [propext, Classical.choice, Quot.sound].
- **File**: PhD/JacobsSlash/U3/9_EigenvaluesU3.lean
- **Depends on**: M2, U5, CLEANUP-ALL-3
- **Parallel**: no
- **Type**: theorem (MILESTONE, REPLACEMENT)

#### Statement
```lean
/-- **THE CULMINATION** … `y` is an `ω`-eigenvector of the base change of the K₃-matrix of
the genuine diamond operator `W = [U₁(9)·μ·U₁(9)]` (that matrix being `Wop`, by
`heckeW_apply_classRep_eq_delta` + `Wop_eq_blockOp_deltaOf`). -/
theorem exists_eigenvalue_U3_in_W_eigenspace (t : K₃) (ht : ‖t‖ < 1) (j : ℕ) :
    ∃ (a : ℂ_[3]) (y : c(Fin 3 × ℕ, ℂ_[3])), a ≠ 0 ∧ y ≠ 0 ∧
      U3MatrixOp (norm_three_lt_one_of_isometry ιC norm_ιC)
          (norm_map_weight_lt_one ιC norm_ιC ht) (map_ν₃_near ιC norm_ιC) y = a • y ∧
      ‖a‖ ^ 2 = ‖(3 : ℂ_[3])‖ ^ (2 * j + 1) ∧
      PowerSeries.evalT a⁻¹ (PowerSeries.map ιC (charPowerSeriesU3 t ht)) = 0 ∧
      ∀ W' : c(Fin 3 × ℕ, ℂ_[3]) →L[ℂ_[3]] c(Fin 3 × ℕ, ℂ_[3]),
        (∀ x z, matrixCoeff W' x z = ιC (matrixCoeff (Wop norm_three_lt_one ht) x z)) →
        W' y = ωC • y
```

#### Proof sketch
1. `obtain` E04's tuple (`exists_eigenvalue_U3_halfIntegral`) — unchanged.
2. New final clause: `intro W' hW'`.  By `map_Wop ιC norm_ιC norm_three_lt_one ht`, the
   operator `Wop (ιC-transported params)` satisfies the same coefficient description, so
   `W' = Wop (transported)` by `TateFredholm.ext_matrixCoeff` (`Matrix.lean:66`) —
   `hW'` and `map_Wop` give `matrixCoeff W' = matrixCoeff (Wop transported)` pointwise.
3. Rewrite and close with E04's `Wop … y = ωC • y` clause.
4. **DELETION (required)**: the old `∀ (φ : kappaFormsWide …) (i : Fin 3), heckeW … = deltaOf …`
   conjunct is removed — it was the *justification* of the new clause's hypothesis, not a
   second conclusion.  Its content now lives where it belongs, as
   `heckeW_apply_classRep_eq_delta` in `«7_DiamondHecke»`, cited from this docstring.
5. `#print axioms exists_eigenvalue_U3_in_W_eigenspace` — must be exactly
   `[propext, Classical.choice, Quot.sound]`.

#### Mathlib/project lemmas needed
`map_Wop` (M2), `TateFredholm.ext_matrixCoeff` (`PhD/TateFredholm/Matrix.lean:66`),
`exists_eigenvalue_U3_halfIntegral` (E04, unchanged), `norm_ιC` (`«2_PadicEmbedding»`).

#### Sources
Phase-3 plan "Gap 2"; [Jacobs, Cor 2.16] + [Jacobs, Lemma 2.9/2.10] eigenspace reading;
the 2026-08-07 audit finding that recorded the parallel-clause defect.

#### Generality decision
Stated at `ℂ₃` with the genuine parameter images (unchanged from E04/E05); the `∀ W'`
form is deliberately *hypothesis-driven* rather than naming `Wop`-over-ℂ₃ directly, so the
statement reads as a fact about the base change of the genuine operator's matrix and does
not depend on which transcribed representative is used to compute it.

### [CLEANUP-FINAL-3] /cleanup-all + PROGRESS.md + final audit — **Depends on**: M3 —
**DONE 2026-08-07.  BOTH AUDIT GAPS CLOSED; PHASE 3 COMPLETE.**
Re-audit result: (1) `kappaFormsWide` no longer exists — `heckeU3` and `heckeW` share
`kappaForms` by construction, acceptance test passed; (2) the culmination is ONE composed
statement about the base change of the genuine `W`'s matrix, with `map_Wop` supplying the
bridge.  Unchanged: the single contracted `sorry` (`hClassNumberOne`, `2_Level:673`), no
`axiom`, no `native_decide`, self-enclosure (no `import PhD.Jacobs`).  PROGRESS.md carries
the Phase-3 section and the corrected conventions (Σ₁(9) = level congruence; Σ₁(3) = the
single acting monoid).
- Update `PhD/JacobsSlash/PROGRESS.md`: single acting monoid Σ₁(3), single space
  `kappaForms` carrying both `heckeU3` and `heckeW`, the composed culmination, and the
  axiom contract (unchanged: the only `sorry` is `hClassNumberOne`).
- Re-run the two-gap audit and confirm both are closed; record the net-LOC delta.
