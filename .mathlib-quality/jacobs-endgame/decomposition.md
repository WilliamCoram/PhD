# Decomposition — Jacobs endgame: the `U₃`-refactor of the downstream slope files

**BOARD PATH: `.mathlib-quality/jacobs-endgame/`** (NOT the default board = NewtonPolygons,
NOT `jacobs/`, NOT `qmf/`, NOT `tatefredholm-eigen/`).  Tell every `/beastmode` this path.

## What this board is

A **refactor/assembly board**: the mathematical content of [Jac] Ch. 2 is already proved
across three completed tranches (Tranche A + AG-NP + AG-W on `jacobs/`; AG-B on `qmf/`).
This board (i) turns the meeting-point bridges of `PhD/Jacobs/U3/Matrix.lean` into the
final headline statements **about the genuine Hecke operator `U₃`**, and (ii) replaces the
"Assumed input (identification debt)" notices in the downstream files with pointers to the
proofs.  The "sources" for most leaves are therefore our own proved declarations (cited
file:decl, verified to exist and compile — baseline `lake build PhD.Jacobs.U3.Matrix
PhD.Jacobs.Instance` green, 3481 jobs, 2026-08-05 this session); thesis quotes are reused
from the recorded quote inventories of the two completed boards (the thesis PDF is not in
the repo; those boards recorded verbatim quotes precisely for this reuse).

## Sources

- [Jac] Jacobs, *Slopes of Compact Hecke Operators*, Imperial College PhD thesis, 2003.
  Quotes below are reproduced from `.mathlib-quality/jacobs/decomposition.md`,
  `.mathlib-quality/qmf/decomposition.md` and `PhD/Jacobs/PROGRESS.md` (recorded verbatim
  there at planning time with page references).
- [Buz07] Buzzard, *Eigenvarieties* §9 p. 69 (quoted in qmf R5, reproduced below) — the
  evaluation isomorphism `L(U,A) ≅ ⊕ A^{Γ_λ}`.
- Project: `PhD/Jacobs/U3/Matrix.lean` (meeting point — read in full this session),
  `PhD/Jacobs/Instance.lean` (ℂ₃ witness layer — read in full this session),
  `PhD/QMF/` (`bijective_evalAtReps`, `heckeOperator_apply_rep`),
  `PhD/Jacobs/{BlockOp,DiamondW,Slopes,SlopeReading,U3Data,PadicAnalytic}.lean`,
  `PhD/TateFredholm/{Fredholm,Matrix,Tate}.lean`.

## Setting

`K₃` = the `v₃`-adic completion of `ℚ` (`PhD/Jacobs/U3/Setting.lean`), with instances
`NontriviallyNormedField, IsUltrametricDist, CompleteSpace, CharZero` (qmf B01) and
parameters `ν₃` (`sq_ν₃ : ν₃ ^ 2 = -2`, `ν₃_near : ‖ν₃ - 2695‖ ≤ ‖3‖ ^ 10` — one power
stronger than needed, recorded), `norm_three_lt_one : ‖(3 : K₃)‖ < 1`.  Weight `t : K₃`,
`ht : ‖t‖ < 1`.

**The `ω` obstruction (why E-C exists).**  `K₃ = ℚ₃` contains no primitive cube root of
unity: `x² + x + 1 ≡ (x + 2)² mod 3`, the discriminant `−3` has odd valuation, and
`μ(ℚ₃) = {±1}` (Teichmüller `μ₂` × torsion-free `1 + 3ℤ₃`).  The U3Data module header
records the same fact from the thesis side: "`hω` forces `K ⊇ ℚ₃(ζ₃)`", a *ramified
quadratic* extension whose ramification is load-bearing (`v₃(Kˣ) = ½ℤ` is what makes the
slopes `n − ½` expressible).  So every statement mentioning the `M`-eigenblocks lives over
an extension field `L`; the E-C primary statements are abstract over
`(L, f : K₃ →+* L, hf : ∀ x, ‖f x‖ = ‖x‖, ω : L, hω)`, with `L = ℂ_[3]`
(mathlib `Mathlib.NumberTheory.Padics.Complex`; all four instances + `IsAlgClosed`, per
`PhD/Jacobs/Instance.lean`) as the concrete witness.

## Prior-B2 log consultation (Step 4.6 — all three logs read this session)

- Root log (2 entries, NewtonPolygon representation defects): no name/shape match; the
  polygon-touching leaves here only *instantiate* the completed SlopeReading theorems,
  never touch `.slopes`/structure fields.  Addressed by design.
- `jacobs/b2_log.jsonl` (4 entries).  Binding inheritances:
  1. **ω-hypothesis family** (`norm_coeff_M22genFun_le`, `M22half`, J020): any statement
     or def mentioning `ω` MUST carry `hω : ω ^ 2 + ω + 1 = 0` explicitly.  Every E-C
     leaf mentioning `ω` below does.
  2. **`[IsTate R]` on block-compactoid lemmas** (`isCompactoid_restrictOp/blockOp`):
     rowNorm's real-`iSup` junk is `0` on unbounded rows, so compactoid transport lemmas
     are false without `IsTate`.  E-B's compactoid leaf carries/derives `IsTate K₃`.
  3. **Scalar honesty** (`charCoeff_M22op_eq` RHS-scalar omission): operator restatements
     keep their scalars explicit — matches the Matrix.lean determinant-twist decision
     record (twist stays in `matrixCoeff_blockOp`'s statement).
- `qmf/b2_log.jsonl`: empty.
No planned leaf name (`charPowerSeriesU3`, `kappaFormsEquiv`, `charPowerSeries_map`,
`map_padicExp`, …) matches any logged entry.

## Adversarial findings recorded up front (planning-time)

1. **AG-B did NOT identify `W`.**  The qmf tranche certified `U₃ = [U₁(9)η₃U₁(9)]` only.
   The diamond operator `W = [UμU]` (`μ = diag(1,4)`; [Jac Lemma 2.9, §B.2]) remains
   *transcription-status*: no certificate ties the `δ`-blocks to the `[UμU]`-action.
   Consequence for this board: **no final statement may mention `W`-as-Hecke-operator**.
   This costs nothing — `W` is proof-scaffolding inside AG-W (`lemma210` is a pure matrix
   computation; `charPowerSeries_U3MatrixOp`'s statement never mentions `W`), so the
   factorisation and `M₂,₂`-slope finals are unaffected.  The E-A notice for
   `DiamondW.lean` must keep Lemma 2.9's debt-notice for the `δ`/`B` data while
   discharging the `ε`/`U₃` half.  Recorded as deferred **AG-W-ID** (no tickets).
2. **`hClassNumberOne` stays a hypothesis.**  The one contracted `sorry`
   (`U3/Level.lean`, FLT interface).  Everything `hcn`-dependent on this board takes
   `hcn : HClassNumberOne` as an explicit argument (the `eval_classRep_injective`
   pattern); `hcn`-free layers (everything about the certificate block operator and
   `U3MatrixOp`) must NOT acquire it.  Axiom gate: the board's milestone endpoints must
   show exactly `[propext, Classical.choice, Quot.sound]`, except the explicitly-marked
   `'`-convenience forms citing `hClassNumberOne`.
3. **Out-of-scope guard (quote-or-delete applied at planning).**  A "Newton polygon of a
   product = merged slopes" theorem has NO source in [Jac] (the thesis stops at Cor 2.16,
   the `M₂,₂` factor) — any leaf in that direction is an invented artifact and was
   deleted at planning time.  The board's finals mirror the thesis: factorisation of
   `det(1 − T·U₃)` + per-factor slope statements.

## Key verbatim quotes (reused from the recorded inventories)

- [Buz07 §9 p. 69] (qmf R5; the E-B iso):
  > "Say D×_f = ∐_{λ=1}^{μ} D×τ_λU.  Then the groups Γ_λ := τ_λ⁻¹D×τ_λ ∩ U …
  > Note that f ∈ L(U,A) is determined by f(τ_λ) for 1 ≤ λ ≤ μ, and one checks easily
  > that the map f ↦ (f(τ_λ))_{1≤λ≤μ} induces an isomorphism L(U,A) → ⊕_{λ=1}^{μ} A^{Γ_λ}."
- [Jac p. 28] (U3/Matrix.lean module header, reproduced from the thesis):
  > "Thus, the matrix of U₃ will have the form A = (ε_{i,j}) = (0 ε₀,₁ ε₀,₂; ε₁,₀ 0 ε₁,₂;
  > ε₂,₀ ε₂,₁ 0) … Our next aim is to calculate the generating functions of the non-zero
  > ε_{i,j}."
- [Jac Lemma 1.15 = Ser62 Lemme 2] (jacobs AG-W section):
  > "Let I = I′ ∪ I″ be a partition of I. … Then u′ and u″ are compact and
  > det(1 − tu) = det(1 − tu′) det(1 − tu″)."
- [Jac Cor 2.16 p. 39] (jacobs J021): "The n-th slope of M₂,₂ is n − 1/2 for n ∈ ℕ.
  Proof. Apply Theorem 2.14 with M = M′₂,₂."
- [Jac p. 34–35 "hence" step] (jacobs AG-NP): the points-to-slopes reading, formalised as
  `SlopeReading.unitSlope_newtonPolygon₀OfPowerSeries_M22op` (proved).
- `PhD/Jacobs/U3Data.lean` §"Assumed input" (read this session — the debt being
  discharged): "Nothing in this file (or this tranche) proves that these definitions are
  the matrix of the Hecke operator `U₃ = [Uη₃U]` on `L(U₁(9), A₃)`; … The identification
  is tracked as **AG-B** … and must be discharged before any 'slopes of `U₃`' claim is
  final."
- `PhD/Jacobs/PROGRESS.md` (2026-08-05 milestone): "`heckeU3_apply_classRep` (the
  unconditional headline `(U₃φ)(cᵢ) = ∑ⱼ blockOpᵢⱼ φ(cⱼ)`), `eval_classRep_injective`
  (completeness under `HClassNumberOne`), and the determinant-twist bridge
  `charPowerSeries_blockOp_eq_U3MatrixOp` … are all proven on standard axioms."

---

## Skeleton location (verified green 2026-08-05, this session)

- `PhD/Jacobs/BaseChange.lean` (176 lines, 17 sorries) — `lake build PhD.Jacobs.BaseChange` ✓
- `PhD/Jacobs/U3/Fredholm.lean` (~130 lines, 5 sorries) — `lake build PhD.Jacobs.U3.Fredholm` ✓
- `PhD/Jacobs/U3/HeckeSlopes.lean` (~190 lines, 8 sorries) — `lake build PhD.Jacobs.U3.HeckeSlopes` ✓ (3498 jobs)

Already REAL (no sorry) in the skeleton — the dependency shape is machine-checked:
`instance : IsTate K₃`, `kappaFormsModelEquiv` (via `LinearEquiv.ofBijective`),
`charPowerSeriesU3` (def), `charPowerSeriesU3_eq_U3MatrixOp` (**proved**, one-line from
the AG-B bridge), the entire `L₃` spectral-norm instance chain (9 instances), `ι₃`, `ω₃`
(defs), and `charPowerSeriesU3_factorisation_L₃` (**real body** — instantiation of the
abstract theorem; goes sorry-free automatically when E9–E12 land).

## Tranche E-B leaves (`PhD/Jacobs/U3/Fredholm.lean`)

- **EB.1** `evalU3` linearity fields (`map_add'`/`map_smul'`, :49) + `blockProj_evalU3`
  (:57).  Source: construction-level; [Buz07 §9] quote above ("f is determined by
  f(τ_λ)").  Lean ↔ source: `evalU3 φ = Σᵢ blockIncl i (φ (classRep i))` IS the
  displayed evaluation map, landed in the block model.  Discharge: Submodule coe
  add/smul + `map_sum`-linearity of `cSpace.blockIncl` (BlockOp:568) +
  `cSpace.blockProj_blockIncl` orthogonality (BlockOp:626) + `Finset.sum_eq_single`.
  Attacks: [1-edge] φ = 0 ✓ sums of zeros; [2-convention] output block `i` = value at
  `cᵢ` — matches `heckeU3_apply_classRep`'s row convention (verified against
  Matrix.lean:350-354 this session) ✓; [3-discharge] `blockProj_blockIncl` verified at
  BlockOp:626 with exactly the `if b = a` shape needed ✓.  Verdict: SURVIVED.
- **EB.2** `bijective_evalU3` (:68, `hcn` explicit).  Source: [Buz07 §9 p. 69] quote
  above — the displayed isomorphism.  Lean ↔ source: injectivity = "f is determined by
  f(τ_λ)" (= proved `eval_classRep_injective`, Matrix.lean:411); surjectivity = "induces
  an isomorphism onto ⊕ A^{Γ_λ}" with `Γ_λ = 1` here, so onto the full block model.
  Discharge: `AutomorphicFunction.bijective_evalAtReps` (QMF/Decomposition.lean:111,
  **proved**) at the section from `exists_classRep_section` (ClassSet.lean:1215, proved,
  hcn) + `stabilizerAt_classRep i = ⊥` (ClassSet.lean:996, unconditional) trivialising
  the invariants + `DoubleCoset.Quotient ≃ Fin 3` enumeration plumbing +
  `blockProj`-ext.  Attacks: [1-hyp] hcn genuinely needed both halves (without
  completeness of the reps a form vanishing at three points need not vanish; the section
  needs hcn to exist) ✓ carried; [2-edge] the invariant-strip: membership in
  `fixedPointsOfLE` at `⊥` is `∀ u ∈ ⊥, u • x = x` — trivially all of `A` ✓ no
  hidden condition; [3-prior-B2] no name/shape match; [4-discharge] all four cited
  decls fetched verbatim this session (signatures in the seam inventory) ✓.
  Verdict: SURVIVED.  Sizing: B17's `eval_classRep_injective` was ~80 LOC; the
  surjectivity transport is comparable — est. ~120 LOC.
- **EB.3** `evalU3_heckeU3` (:82, **unconditional**).  Source: `heckeU3_apply_classRep`
  (Matrix.lean:350, proved — PROGRESS.md quote above).  Lean ↔ source: apply the proved
  headline at each `i`, then collapse `TateFredholm.blockOp (blockOp t ht)` on
  `Σⱼ blockIncl j (φ cⱼ)` via the orthogonality sum (`blockOp` def BlockOp:638:
  `Σ_{a,b} blockIncl a ∘ T a b ∘ blockProj b`).  Attacks: [1-convention] blockOp's
  "(a,b) block acts from b-component to a-component" (BlockOp:639 docstring) matches the
  headline's `Σⱼ blockOp i j (φ(cⱼ))` exactly — no transpose ✓ (checked both docstrings
  this session); [2-edge] diagonal blocks are 0 (`sigmaTable_ne`) — sum still correct ✓;
  [3-discharge] `blockProj_blockIncl` + `Finset` algebra only ✓.  Verdict: SURVIVED.
- **EB.4** `isCompactoid_blockOpU3` (:91).  Source: structural ([Ser62]-side closure
  facts, all proved).  Discharge: `blockOp_eq_smul_epsOp` (Matrix.lean:299, proved) +
  `TateFredholm.isCompactoid_blockOp [IsTate]` (BlockOp:690) + `IsCompactoid.smul`
  (Riesz.lean:645) + the six `isCompactoid_epsOp*` (DiamondW:342–367) + a zero-block
  case (`isCompactoid_zero_clm`, DiamondW:292).  **Recorded skeleton-adjacent
  amendment (authorised at planning)**: the six `isCompactoid_epsOp*` and
  `isCompactoid_zero_clm` are `private` in DiamondW — de-privatise them as the E-B seam
  (exact precedent: the six `matrixCoeff_epsOp*` were de-privatised for B15, recorded on
  the qmf board).  Attacks: [1-IsTate] the b2-logged `[IsTate]` necessity is satisfied:
  `instance : IsTate K₃` is REAL in the skeleton (compiled) ✓; [2-edge] scalar weights
  `classWeight` need not be nonzero for compactoidness — no extra hypothesis smuggled ✓;
  [3-discharge] `IsCompactoid.smul` signature fetched verbatim (needs `[IsTate R]`) ✓.
  Verdict: SURVIVED.
- **EB.5** `charPowerSeriesU3` + `charPowerSeriesU3_eq_U3MatrixOp` — **already real and
  proved in the skeleton** (compiled against `charPowerSeries_blockOp_eq_U3MatrixOp`).
  No ticket needed; listed for the tree's completeness.

## Tranche E-C leaves — base change (`PhD/Jacobs/BaseChange.lean`)

- **EC.1** `TateFredholm.charCoeff_map` (:48) + `charPowerSeries_map` (:57).  Source:
  structural (the definition `charCoeff u n = (−1)ⁿ Σ'_{|S|=n} minor` — Fredholm.lean:147,
  fetched verbatim).  Lean ↔ statement: minors are finite dets, `f` maps dets
  (`RingHom.map_det`-family — verify exact mathlib name at pickup) and maps the tsum
  (continuity from isometry via `AddMonoidHomClass.isometry_of_norm`; summability of the
  source family = `summable_minor` [IsTate R] + `IsCompactoid u`; `HasSum.map`).
  Attacks: [1-edge] n = 0: both sides 1 ✓; I finite/empty: finite sums ✓;
  [2-hyp-strength] `Continuous f` would suffice here (recorded generalisation note —
  the isometric form is kept for uniformity with the analytic layer, where isometry is
  genuinely needed for the junk-region argument); [3-discharge] `summable_minor`
  (Fredholm.lean:143, `[IsTate R]`) verified ✓.  Verdict: SURVIVED.  PR-shaped.
- **EC.2** `MvPowerSeries.map_inv₀` (:70) + analytic layer `map_padicLog` (:86),
  `map_padicExp` (:92), `map_binomialCoeff` (:99), `map_unitPow` (:105).
  Source: definitions in `PadicAnalytic.lean` (tsums of field expressions) and
  mathlib's junk conventions.  Attacks: [1-junk-edge] non-summable region: both tsums
  are `0` (`tsum_eq_zero_of_not_summable`) and `f 0 = 0` ✓; `map_inv₀` at zero constant
  coefficient: both sides junk `0`, `f` injective (field hom) preserves the split ✓;
  [2-hyp] isometry (not mere continuity) is load-bearing exactly here — summability must
  transport in BOTH directions (ultrametric: summable ↔ terms → 0, norms preserved) ✓;
  [3-edge] `u = 1`, `w = 0`, `n = 0` all check ✓; [4-discharge]
  `MvPowerSeries.inv_eq_iff_mul_eq_one` (mathlib Inverse.lean:252, verified present),
  `map_div₀`/`map_natCast`/`map_prod`, `tsum_eq_zero_of_not_summable`, `HasSum.map`,
  ultrametric summability criterion (TateFredholm.Tate / mathlib nonarchimedean) ✓.
  Verdict: SURVIVED.  (`map_inv₀` recorded as a mathlib-PR candidate.)
- **EC.3** series layer: `map_kappaSeries₂` (:116), `map_linSeries` (:121),
  `map_quadSeries` (:126), `map_weightGenFun` (:134).  Source: `weightGenFun` def
  (U3Data:187, fetched verbatim: `kappaSeries₂ t (γ 1 0) (γ 1 1) * (linSeries γ)⁻¹ *
  (quadSeries γ)⁻¹`).  Lean ↔ source: coefficientwise `MvPowerSeries.ext` + `coeff_map`
  (`@[simp]`, mathlib) + EC.2; `map_weightGenFun` = `map_mul` ×2 + `map_inv₀` ×2 + the
  three (≤ 3-lemma composition over EC.2/EC.3 ✓).  Attacks: [1-edge] `d = 0` division
  junk maps through `map_div₀` ✓; `γ.map f` entry access `Matrix.map_apply` ✓;
  [2-drift] the thesis's own working object from p. 30 on is this formula-as-definition
  (Tranche-A record) — no drift possible, the map lemma is about our definition ✓.
  Verdict: SURVIVED.
- **EC.4** the six `map_h**` (:145–:170).  Source: `h01` def (U3Data:193, verbatim:
  `weightGenFun t (eps01M1 ν) + weightGenFun t (eps01M2 ν)`) and the eps-matrix defs
  (U3Data:113–146, entries in `ℚ(ν)`).  Discharge: `map_weightGenFun` + `map_add` +
  per-matrix `(eps**M* ν).map f = eps**M* (f ν)` (entrywise `map_div₀`/`map_ofNat`/
  `map_neg`/`map_mul` — private helpers at execution).  Attacks: [1-edge] entries with
  denominators 10, 4, 7, 14, 5 — all field divisions, `map_div₀` total ✓; [2-drift] the
  E1-erratum-corrected `eps12M2` maps like any other (the correction is in the data, not
  the map) ✓.  Verdict: SURVIVED.

## Tranche E-C leaves — finals (`PhD/Jacobs/U3/HeckeSlopes.lean`)

- **EC.5** hypothesis transports: `norm_three_lt_one_of_isometry` (:56),
  `norm_map_weight_lt_one` (:61), `map_ν₃_near` (:66), `map_sq_ν₃` (:71).  Discharge:
  `map_ofNat` + hf + `norm_three_lt_one`/`ν₃_near`/`sq_ν₃` (Setting.lean:105/252/195,
  all proved, signatures fetched).  Attacks: [1] `(3 : L) = f (3 : K₃)` and
  `(2695 : L) = f (2695 : K₃)` are `map_ofNat` — no numeral drift ✓; [2-edge]
  `map_sq_ν₃` needs no isometry (pure ring hom) — stated without `hf` ✓ minimal
  hypotheses.  Verdict: SURVIVED.
- **EC.6** `map_charPowerSeriesU3` (:80).  Chain (each link proved or a leaf above):
  `charPowerSeriesU3_eq_U3MatrixOp` (proved) → `charPowerSeries_map` (EC.1) at
  `u := U3MatrixOp` over `K₃` (`isCompactoid_U3MatrixOp`, DiamondW:383, public, proved;
  `IsTate K₃` real) → `hmatch` from `TateFredholm.matrixCoeff_blockOp` (BlockOp, proved)
  + the six public `matrixCoeff_epsOp*` (DiamondW:423–443) + `coeff_map` + EC.4 +
  zero-block map.  Attacks: [1-pinning] `U3MatrixOp` over `L`'s implicit `{t ν}` are
  pinned to `(f t, f ν₃)` by the hypothesis-term types — machine-verified: the skeleton
  statement elaborated ✓; [2-convention] both sides' matrixCoeff go through the same
  `blockOp`/`epsOp` spellings — no index flip possible ✓.  Verdict: SURVIVED.
- **EC.7 (MILESTONE)** `charPowerSeriesU3_factorisation` (:97).  Source: [Jac Lemma 1.15]
  + (2.1.14) chain (quotes above), formalised as `charPowerSeries_U3MatrixOp`
  (DiamondW:1240, proved, AG-W milestone — signature fetched verbatim, takes `ω hω h3 ht
  hνc`, **no hν2**).  Discharge: EC.6 + that theorem at `L` — 2-lemma composition ✓.
  Attacks: [1-hω] `ω` carried with explicit `hω` (b2-inheritance) ✓; [2-scope] no
  polygon-merge claim — the statement stops at the product, per the out-of-scope guard;
  the `M₂,₂`-factor slope reading is the ALREADY-PROVED
  `unitSlope_newtonPolygon₀OfPowerSeries_M22op` at `L` (SlopeReading:412, signature
  fetched; its `hν2` supplied by `map_sq_ν₃`) — cited in the docstring, not restated ✓;
  [3-edge] `L = ℂ₃`-sized fields also satisfy the pack — abstract statement covers both
  the minimal and the closed cases ✓.  Verdict: SURVIVED.
- **EC.8** cyclotomic witness fills: `norm_ι₃` (:150), `ω₃_sq_add_ω₃_add_one` (:157).
  (The 9-instance chain, `L₃`, `ι₃`, `ω₃`, and `charPowerSeriesU3_factorisation_L₃` are
  already REAL — the chain compiled this session, which retires the feasibility gate of
  plan.md.)  Discharge: `spectralNorm_extends` (SpectralNorm.lean:573) or
  `norm_algebraMap'` (Normed/Module/Basic.lean:293); `IsCyclotomicExtension.zeta_spec`
  + `IsPrimitiveRoot.isRoot_cyclotomic (by decide)` + `Polynomial.cyclotomic_three`
  (`@[simp]`) — the verbatim FLT-Three idiom (`Mathlib/NumberTheory/NumberField/
  Cyclotomic/Three.lean:92-95`, fetched).  Attacks: [1-normalisation] the spectral norm
  restricted to `K₃` IS `‖·‖_{K₃}` (`spectralNorm_extends`) — `‖3‖` unchanged, no `e = 2`
  rescaling anywhere (this is WHY the cyclotomic-over-`K₃` route was chosen over
  adic-completion-of-`ℚ(ζ₃)`, whose standard normalisation differs by the ramification
  index) ✓; [2-degenerate] if `x²+x+1` had a root in `K₃` the extension would be trivial
  and every statement still holds (nothing assumes degree 2) — but it does not (setting
  section) ✓.  Verdict: SURVIVED.

## Tranche E-A (notices — documentation only, no Lean leaves)

Rewrite targets (exact current texts read this session): `U3Data.lean` §"Assumed input
(identification debt — deliberately skipped)" (lines 76–93) and the in-body transcription
note (:106–108); `Slopes.lean` §"Assumed input" (read via seam inventory);
`SlopeTheorem.lean` / `SlopeReading.lean` AG-NP-era notes where they call the
identification open; `DiamondW.lean` §"Assumed input" (lines 25–30) — **the DiamondW
rewrite must keep Lemma 2.9's `δ`/`B` transcription-debt notice** (adversarial finding 1:
AG-B never certified `W`; only the `ε`/`U₃` half is discharged).  Each rewritten notice
points at: `heckeU3_apply_classRep`, `eval_classRep_injective`,
`charPowerSeries_blockOp_eq_U3MatrixOp` (U3/Matrix.lean), `charPowerSeriesU3` +
`charPowerSeriesU3_eq_U3MatrixOp` (U3/Fredholm.lean), `charPowerSeriesU3_factorisation`
(U3/HeckeSlopes.lean), and the `hClassNumberOne` contract.  Statement text: unchanged —
zero statement edits, docstrings/module headers only.

## API gaps / deferred (recorded, NO tickets)

- **AG-W-ID** — certify the `δ`-blocks/`B` as the matrix of `W = [UμU]` ([Jac Lemma 2.9,
  §B.2]) by the qmf certificate machinery.  Optional (no final statement needs it);
  would upgrade DiamondW's remaining notice.
- **AG-EIGEN** — eigenvalues of `U₃` from `det(1 − T·U₃)` over `L₃`/`ℂ₃` via the
  `tatefredholm-eigen` board's Riesz theory (coordinate with that board; `Instance.lean`'s
  header records why `ℂ₃` is the natural home for eigenvalue statements).
- **AG-EXT** — `M₃,₃` slopes, `λ ∈ {1,2}` (jacobs board, unchanged).
- `hClassNumberOne` — permanent contracted `sorry` (FLT interface), unchanged.

## Confidence-gate summary

1. Every leaf discharged from mathlib (names verified by the mathlib sweep this
   session, file:line cited) or from proved project code (signatures fetched verbatim
   this session); the single absent-mathlib item (`map_inv` for power series) became
   leaf EC.2 with a verified derivation route.  2. Skeleton compiles — three modules
   green, 30 sorries, 0 errors; five further planned decls are already REAL including
   the proved `K₃`-headline.  3. Verbatim quotes per leaf: project decls quoted from
   this session's fetches; thesis/[Buz07] quotes reused from the recorded inventories
   (thesis PDF not in repo — recorded-quote reuse is this board's documented
   convention).  4. Attack logs above, ≥ 3 categories per leaf, all SURVIVED; one
   planning-time artifact (polygon-merge) was killed by quote-or-delete.  5. Prior-B2
   consulted (3 logs); the three inheritances are applied in the skeleton (explicit
   `hω`, real `IsTate K₃`, explicit twist scalars).  6. The tree mirrors its sources:
   E-B mirrors [Buz07 §9]'s displayed isomorphism + the meeting-point architecture; E-C
   mirrors the thesis's own two-step (identification p. 28, then (2.1.14)+Lemma 1.15
   product), stopping exactly where the thesis stops.  LOC estimates anchored to
   comparable proved decls (B17 ≈ 80 LOC for the injectivity half; W003 ≈ reindex-scale
   for EC.1).  7. All leaves single-conclusion (the factorisation is one equation; no
   `∧` anywhere in the skeleton).

---

# AG-W-ID tranche (opened 2026-08-06, user-directed): `Wop` is the genuine `[U₁(9)·μ·U₁(9)]`

## Skeleton
`PhD/Jacobs/U3/DiamondHecke.lean` (27 sorries incl. 2 def-holes; `lake build` green —
verify against the parallel session's rebuild races).  Imports `PhD.Jacobs.U3.Fredholm`.

## Goal + sources
Upgrade the recorded DiamondW residue ("the δ-blocks and `B` are transcription-status")
to a theorem: the transcribed diamond operator `Jacobs.Wop` is the matrix of the genuine
Hecke operator `W = [U₁(9)·μ·U₁(9)]`, and `M₂,₂` is the `ω²`-eigenblock of the diamond
action.  Sources: the recorded verbatim quotes on the jacobs board ([Jac p. 32] δ-display
+ erratum 6/7 records; DiamondW header "μ = (1 0; 0 4) at 3"); the §B.2 tables are NOT
available (no thesis PDF in repo) — per the AG-B provenance rule the certificates are
RECOMPUTED, not transcribed (`PhD/Jacobs/U3/certificate_search_w.py`, this session).

## Computed data (search run 2026-08-06; validation all-pass)
- **Handedness**: the thesis's `μ = diag(1,4)` is right-handed; left-handed = adjugate =
  `diag(4,1)`.  ADVERSARIAL FINDING (caught by the search): `diag(1,4)` ∈ U₁(9) — with
  it, `[UμU]` would be the identity (σ = id, d = 1).  With `diag(4,1)`: σ = (1,2,0), the
  exact 3-cycle of `Wop`'s block layout.  The class action lives on the FIRST column
  ((ℤ/9)ˣ-cosets {1,8},{2,7},{4,5} of ±1).
- **Single coset**: `μ` normalises `U₁(9)` (diagonal conjugation scales off-diagonals by
  the 3-unit `4^{±1}`) ⇒ `UμU = μU`; the coset family is `Fin 1`.
- **Certificates** (unique hit per class over 312 candidates = 24 Hurwitz units + 288
  norm-9/3; det bookkeeping forces `nrd d = 1`):
  `σ_W = (1, 2, 0)`; `d_W = (−1, −1, +1)` (central signs);
  `u(0) = diag(−4/5, −1/2)`, `u(1) = diag(−20/7, −1/2)`, `u(2) = diag(28, 4)` at 3 —
  all rational diagonal (ν-free!), Σ₁(9)-checks are numeral valuations.
- **Acting matrices** `adjParams(θ₃(μ·u(i)⁻¹))`: DIAGONAL with
  `(a,d) = (−2,−5), (−2,−7/5), (1/4,1/7)`; ratios `a/d = 2/5, 10/7, 7/4` = EXACTLY the
  `D`-arguments of `δ₀,₁, δ₁,₂, δ₂,₀` ✓; the values are
  `(classDet σ(i)/classDet i)`-multiples of the thesis's `(a,d)`-data
  ((−1/5,−1/2), (−5/7,−1/2), (7,4)) — THE SAME classWeight COBOUNDARY as B15, and
  `κ(d)·d⁻²` at the thesis values reproduces the transcribed δ-scalars
  `4κ(−1/2), 4κ(−1/2), (1/16)κ(4)` on the nose.

## The one API gap (Σ₁-width) — the tranche's real content
`Sigma1` requires `v(a−1) ≤ γ₉` (≡ 1 mod 9); the μ-acting elements are ≡ 1 only mod 3
(e.g. a-entry −5).  BUT all three γ₉-uses in `KappaAction.lean` (lines 294/349/1312) are
`hγ9le3 : γ₉ ≤ v(3)` — the κ-analytics genuinely need only the mod-3 threshold.  Leaves:
`Sigma1₃` (Σ₀ at level 9 + `v(a−1) ≤ γ₃`), `kappaOpW` by re-running `kappaOp`'s
construction with the three lemmas stated at `v(3)` (their proofs already establish it),
compatibility `kappaOpW_restrict`, action law, `matrixCoeff_kappaOpW`, and the
`levelSubmodule`-transport `kappaFormsW = kappaForms` (membership only quantifies over
`U₁(9) ⊆` both; actions agree by restrict).

## Leaves → tickets WI1–WI7 (per-leaf detail on the ticket board)
WI1 wide monoid; WI2 μ + single coset; WI3 kappaOpW (the γ₃-generalisation); WI4
kappaFormsW + heckeW + HEADLINE `heckeW_apply_classRep`; WI5 δ-identification
(`coeff_weightGenFun_diagonal` + `actingW_eq_smul_delta`); WI6 `Binvop∘Wop∘Bop =
blockOp diag(1, ω²•1, ω•1)` (eigen-diagonalisation; scalar assignment (1, ω², ω) pinned
by the DFT-orientation + U3Data's "ω²-eigenblock" naming for block 1 = M₂,₂ — the
ticket hand-checks and treats a flip as a recorded statement-fix); WI7 docstring
upgrades (DiamondW/Slopes/SlopeReading: remove the "not formalisable" caveats).

## Attacks (recorded)
[handedness] the identity-coset trap above — caught and fixed by the search; [Σ₁-width]
the acting elements fail Sigma1 — caught at planning (this is the API gap, not a
surprise-at-execution); [uniqueness] one hit per class ⇒ no certificate ambiguity;
[δ-scalars] κ(d)d⁻² reproduces all three transcribed scalars exactly ⇒ the
identification statement shape (coboundary smul) is forced, same as B15; [ω-assignment]
WI6's (1, ω², ω) cross-checked against W011's M33-as-ω-block reading.
