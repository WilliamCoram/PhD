# Development Plan: slashRefactor — the QMF right-slash layer + the self-enclosed JacobsSlash fork

**BOARD PATH: `.mathlib-quality/slashRefactor/`** — all artifacts here.  Parallel boards
(`.mathlib-quality/` = NewtonPolygons, `qmf/`, `jacobs/`, `jacobs-endgame/`,
`tatefredholm-eigen/`) are other instances' property.  Every `/beastmode` invocation for
this project must be told this path explicitly.

**REVISION 2 (user-directed, 2026-08-06, supersedes the "statement dialect" plan):**
`PhD/JacobsSlash/` is a **self-enclosed fork of the thesis formalisation**, not a façade:

- **No `import PhD.Jacobs` anywhere in `PhD/JacobsSlash/`.**  The relevant Jacobs files
  are *ported* — copied, renamed with tree-position prefixes, converted to be natively
  right-handed.  Allowed imports: Mathlib, `PhD.TateFredholm`, `PhD.QMF`,
  `PhD.NewtonPolygons` (all outside the Jacobs folder), and earlier JacobsSlash files.
- **Statements mimic the thesis.**  Every convention-carrying statement takes the
  thesis's own right-handed form; the thesis's own tables and displays are the data —
  **nothing is transcribed into the left convention anywhere in the fork** (the reason
  the left library had to recompute every table — qmf board decomposition.md:240 — 
  evaporates in the right-handed development).
- **The transports do the convention work once, abstractly.**  The QMF slash layer
  (new files under `PhD/QMF/Slash/`, mirror-named after their left counterparts — project convention: general slash facts live in
  `PhD/QMF/`) supplies the right-handed abstract theory — right monoids + adjugate
  dictionary, right slash actions, slash level spaces, right-coset Hecke operators,
  right evaluation/decomposition — with statements right-handed and proofs obtained by
  transport from the existing left-handed QMF machinery.  JacobsSlash then just
  *instantiates* the right-handed abstract layer at the thesis's data.
- `PhD/Jacobs/` and every existing `PhD/QMF/` file stay untouched (no breakage
  mid-refactor; BCALL-B owns edits to existing files).  If an *existing* QMF
  declaration ever needs changing, the escape hatch is a mirror in `PhD/QMFSlash/` —
  additive new QMF files are fine and are the default.

## Goal

A reader opens `PhD/JacobsSlash/` and finds the complete Ch. 1–2 §2.1 story of
[Jacobs, *Slopes of Compact Hecke Operators*] in the thesis's own conventions and
order — `Σ₁(9)` with `c ≡ 0, d ≡ 1 mod 9`; `η₃ = (3 0; 0 1)`; `U₁(9)η₃U₁(9) = ⊔ₜ U₁(9)vₜ`;
`(f|u)(g) = f(gu⁻¹)|κ u₃`; `L(U,A)` as `|`-fixed points; the p. 21 and p. 28 displays
verbatim; `det(1 − T·U₃)` and [Cor 2.16] — sorry-free on the standard axioms except
the mirrored `hClassNumberOne` contract, with no reference to the left-handed library.

## Binding constraints (unchanged from revision 1)

- Zero edits to existing files (new files only, everywhere).
- No `lake build`/`lake exe` until the BCALL-B session's sentinel is gone; GATE-1 is
  the build gate.  No beastmode sentinel is created by planning.
- Digit-prefix file naming: module `PhD.JacobsSlash.«1_Foo»`, imports in guillemets
  (lake `stringToLegalOrSimpleName`, verified; GATE-1 re-checks linter tooling, with
  the letter-digit `S1_Foo` fallback).  **Prefix rule: `prefix(f) = 1 + max(prefix of
  JacobsSlash files f imports)` (external imports don't count).**  The `U3/` subfolder
  is mirrored as `PhD/JacobsSlash/U3/` with the same global numbering, so file names
  encode depth across the whole tree.

## Architecture

### Tranche S — the QMF right-slash abstract layer (`PhD/QMF/Slash/`, mirror names, additive)

Written as skeletons already (4 files) + 3 more from this revision:

| File | Contents | Status |
|---|---|---|
| `QMF/Slash/Sigma0.lean` | `Σ₀'` (Buzzard's `Mₜ`, d-unit), adjugate dictionary, `eta` | skeleton ✓ |
| `QMF/Slash/Basic.lean` | `RightSlashAction` class (mathlib `SlashAction` axioms, weight-free), `ofAntiHom`, `SMulSlashClass`, `∣ₛ` | skeleton ✓ |
| `QMF/Slash/WeightModule.lean` | Buzzard's right action on `L_{n,ν}` by his formula; `jTwist` bridge (`(adj δ)ᵀ = JδJ⁻¹` seam) | skeleton ✓ |
| `QMF/Slash/AutomorphicFunction.lean` | `(φ ∣ₛ δ)(g) = φ(gδ⁻¹) ∣ₛ δ`; `levelSubmoduleSlash` = Buzzard's `L(U,A)`; seam theorem (`hcompat` ⇒ equality with `levelSubmodule`) | skeleton ✓ |
| `QMF/Slash/HeckeMonoid.lean` | right-coset abstract Hecke: `[UgV]` on slash level spaces via `UgV = ⊔ᵢ Uxᵢ` (Buzzard §9 verbatim shape); `heckeOperatorSlash_eq_finsetSum`; mirror of `HeckeMonoid.lean` over `QuotientGroup.rightRel` | NEW — skeleton pending |
| `QMF/Slash/HeckeMatrix.lean` | right versions of `heckeOperator_apply_rep` + `evalAtReps`/`bijective_evalAtReps` (the (2.1.1) machinery for right-transforming functions) | NEW — skeleton pending |
| `QMF/Slash/Quaternionic.lean` | the quaternionic specialisation seam, right-handed: `levelMonoid' := Sigma0'.comap toMatrix`, `levelMonoidToSigma0'`, `etaAdelic'` (component `(ϖ 0; 0 1)`), the `WeightModule`-slash `SMulSlashClass` plumbing, and the classical-weight quaternionic modular forms space `L(U, L_{n,ν})` with the classical right slash (user-requested 2026-08-06) | NEW — skeleton pending |

Proof discipline for S: statements right-handed; proofs EITHER by transport along the
adjugate/inversion dictionaries from the left-handed originals (preferred where the
dictionary is available at the needed generality) OR by mirrored copies of the
left-handed proofs (both files are in view; the mirror is mechanical).  Recorded
per-leaf in decomposition.md.

### Tranche P — the JacobsSlash port (self-enclosed fork)

Port map (provisional prefixes; final numbers fixed by the import-depth rule at
skeleton time).  Convention classification decides the port mode:

| JacobsSlash file | ports Jacobs file | mode |
|---|---|---|
| `1_PadicAnalytic` | `PadicAnalytic.lean` | VERBATIM (convention-neutral) |
| `1_GenFun` | `GenFun.lean` | VERBATIM |
| `1_BlockOp` | `BlockOp.lean` | VERBATIM (TateFredholm generality) |
| `2_BinomialTheorem` | `BinomialTheorem.lean` | VERBATIM |
| `2_SlopeTheorem` | `SlopeTheorem.lean` | VERBATIM |
| `U3/1_Setting` | `U3/Setting.lean` | MIRROR: `K₃, v₃, ν₃, θ₃, Hurwitz-θ` verbatim; `Σ₁(9)'` native (`c ≡ 0, d ≡ 1`), no left `Σ₀/Σ₁` |
| `U3/2_Hurwitz` | `U3/Hurwitz.lean` | VERBATIM |
| `U3/3_Level` | `U3/Level.lean` | MIRROR: `U₁(9)` with the THESIS congruence `≡ (∗ ∗; 0 1) mod 9`; `hClassNumberOne` contract mirrored (permanent `sorry`, same discipline) |
| `U3/4_ClassSet` | `U3/ClassSet.lean` | MIRROR: Thm 2.1/Lemma 2.2 for the thesis-form `U₁(9)` |
| `U3/4_EtaDecomposition` | `U3/EtaDecomposition.lean` | MIRROR: `η₃ = (3 0; 0 1)` native; `Uη₃U = ⊔ₜ Uvₜ` (right cosets, thesis display) |
| `U3/2_Compose` | `U3/Compose.lean` | VERBATIM (analytic substitution) |
| `U3/3_KappaSlash` | `U3/KappaAction.lean` | MIRROR: `kappaSlash δ := ofGenFun (weightGenFun t δ.1)` — **no `adjParams`**; Prop 2.6 by design with δ's own parameters; right-action law via `RightSlashAction` |
| `3_U3Data` | `U3Data.lean` | NEAR-VERBATIM: the ε/h data ARE thesis displays; re-examine index orientation (see statement-form rules below) |
| `U3/5_Factorisations` | `U3/Factorisations.lean` | MIRROR: certificates in THESIS orientation (`cᵢvₜ = d·c_{σ}·u`-form as the thesis writes them) — tables from the thesis/§B.1 directly; `certificate_search.py` re-run un-mirrored as validation |
| `4_Slopes`, `5_SlopeReading`, `5_Instance` | same names | VERBATIM (consume U3Data + NewtonPolygons) |
| `4_DiamondW` | `DiamondW.lean` | NEAR-VERBATIM (operator layer; W-identification stays out — AG-W-ID board) |
| `5_BaseChange` | `BaseChange.lean` | VERBATIM |
| `U3/6_Matrix` | `U3/Matrix.lean` | MIRROR: `kappaForms := levelSubmoduleSlash` (Buzzard verbatim); `heckeU3 := heckeOperatorSlash` at `η₃`; p. 21/p. 28 displays in thesis form |
| `U3/7_Fredholm` | `U3/Fredholm.lean` | MIRROR: `evalU3` via right `evalAtReps`; `det(1 − T·U₃)` |
| `U3/8_HeckeSlopes` | `U3/HeckeSlopes.lean` | MIRROR: factorisation + `L₃` witness |

Excluded from the fork: `U3/DiamondHecke.lean` (in-flight on jacobs-endgame, AG-W-ID),
`U3/ClassNumberOneFallback.lean` (unimported skeleton), `PROGRESS.md` (the fork gets
its own).

### Statement-form rules (the "care and thought" — binding for every port ticket)

1. **The thesis's convention is the default; the left library's is forbidden in
   statements.**  Level monoids: `d`-unit / `d ≡ 1`.  Hecke element: `η₃ = (3 0; 0 1)`.
   Cosets: right (`Uvₜ`), quotients: `QuotientGroup.rightRel`.  Transformation law:
   `φ(gu) = φ(g) ∣κ u₃`.  Action on coefficients: `RightSlashAction`/`∣ₛ`.
2. **No adjugate in JacobsSlash statements.**  The dictionary lives in QMF; the fork
   is natively right-handed.  (`adjParams` disappears: `kappaSlash` consumes `δ`
   directly — this is the fork's single biggest simplification, and why no table is
   transcribed.)
3. **Index orientation audit per data file.**  The generating-function matrix
   convention (`matrixCoeff u j i`, thesis `(n_{ji})`) is convention-neutral
   machinery, but which of `h_{i,j}`/`h_{j,i}` labels a block flips with the coset
   side.  Each port ticket for a data-carrying file (U3Data, Factorisations, Matrix)
   records an explicit orientation decision, checked against the thesis display it
   claims to be — with the p. 28 "A = (ε_{i,j})" display as the anchor.  The B15/L4.3
   coboundary history is the cautionary precedent: any residual scalar is a recorded
   statement amendment, never a silent patch.
4. **Verbatim ports change only**: module header path, imports, namespace
   (`JacobsSlash`, avoiding the `Jacobs.U3` shadowing trap), and docstring pointers.
   A verbatim port with ANY statement change is a defect.
5. **The fork's `hClassNumberOne'` mirrors the contract**: permanent `sorry`,
   consumers hypothesis-parametrised, axiom audits expect it only in `'`-forms.
6. **Erratum decisions (E1–E6) carry over verbatim** — the fork adopts the same
   corrected data, with the same docstring records, in thesis orientation.

## References

- [Jac] thesis Ch. 1–2 (displays quoted through the jacobs/qmf board decompositions
  and the Jacobs file docstrings — the fork's leaves cite those recorded quotes).
- [Buz07] §9 pp. 68–70 (quotes in `AutomorphicFunction.lean:11-16`,
  `WeightModule.lean:12-18`, `HeckeMonoid.lean:30-32`).
- The left-handed originals `PhD/Jacobs/**`, `PhD/QMF/*` — the *proof* substrate for
  mirroring (read-only; never imported by the fork).
- Mathlib `SlashActions.lean` (axiom shape), `Adjugate.lean` (dictionary),
  `QuotientGroup.rightRel` (right cosets).

## Status

- 2026-08-06 (rev 2): QMF tranche skeletons S01–S09 stand (4 files); the 6 dialect
  drafts in JacobsSlash were deleted (they imported `PhD.Jacobs`, contradicting rev 2).
  T-CRIT resolution (`adjugate (u₃/det) = u₃⁻¹`, detNorm needs `v(det)=1`) recorded in
  decomposition.md — it remains the engine of the S-tranche seam theorem and of the
  right-Hecke transport proofs.  NEXT: skeletons for `Slash/HeckeMonoid` /
  `Slash/HeckeMatrix` + the port skeletons, then the P-ticket board.  AWAITING USER
  APPROVAL of the revised architecture before skeleton mass-production.

---

# Phase 2 (opened 2026-08-06, user-directed): the W-identification and the eigenvalue endgame

Phase 1 (S-chain + P01–P22) is COMPLETE — see tickets.md.  Phase 2 adds two waves.

## Wave W — AG-W-ID in the fork: `Wop` is the genuine `[U₁(9)·μ·U₁(9)]`

Certify the transcribed diamond operator (`Wop`, the block-cyclic δ-operator of
`4_DiamondW`) as the matrix of the genuine Hecke operator `W = [U₁(9)·μ·U₁(9)]`, in
the fork's right-slash convention, self-enclosed.

**Source** (binding): the jacobs-endgame board's §AG-W-ID decomposition
(`.mathlib-quality/jacobs-endgame/decomposition.md:329-420` — computed oracle data,
the Σ₁-width API gap, leaves WI1–WI7) and its executed left skeleton
`PhD/Jacobs/U3/DiamondHecke.lean` (27 sorries — the exact statement shapes, to be
mirrored, NEVER imported) + `PhD/Jacobs/U3/certificate_search_w.py` (left oracle,
validated run 2026-08-06).  Thesis: [Jac Lemma 2.9, 2.10, p. 32 δ-display].

**The fork handedness flip (pinned)**: the left convention forced `μ = diag(4,1)`
(adjugate transport) because thesis-`μ = diag(1,4)` lies in the left (a-form)
`U₁(9)`.  In the fork the congruence is on the d-entry, so `diag(4,1) ∈ U₁(9)` is
now the trap and **the thesis's own `μ = diag(1,4)` is the correct element**.  The
fork oracle (W01) recomputes all tables in right-coset orientation
(`cᵢ·μ⁻¹ = d·c_σ·u`) and settles whether the δ-identification is twist-free (the
left form carries the B15-style `κ(d)d⁻²` coboundary; the fork's AG-B coboundary
vanished identically — W01's verdict is BINDING on W06's statement, the P19
pattern).

**The Σ₁-width gap** (the wave's real content, mirrored from the left plan): the
μ-acting elements are 1-units only mod 3; the fork's three `γ₉`-uses
(`4_KappaSlash:294/345/1286`, all `hγ9le3`-weakenings) show the κ-analytics need
only the mod-3 threshold.  Fork advantage: `kappaSlash` is `ofGenFun`-based, so the
wide action is the SAME formula and `kappaSlashWide_restrict` is
proof-irrelevance-trivial (the left plan's def-hole WI3 disappears).

New file: `PhD/JacobsSlash/U3/7_DiamondHecke.lean` (prefix 7: imports `6_Matrix`);
one new lemma in `4_DiamondW.lean` (`Binvop_comp_Wop_comp_Bop` — transcription
level, generic K).

## Wave E — the eigenvalue endgame: `U₃` has eigenvalues of valuation `n + ½`

**The culmination of Riesz + NewtonPolygons + the fork**: for every `j : ℕ`, the
(base-changed) genuine `U₃` has an eigenvalue `a` with `v₃(a) = j + ½`
(`‖a‖² = ‖3‖^(2j+1)`), witnessed by an eigenvector lying in the `ω²`-eigenspace of
the diamond operator.  The two pipelines have never been composed —
`TateFredholm/Riesz.lean` does not import `PhD/NewtonPolygons` — this wave is the
composition.

**Verified inventory** (all read this session):
- `TateFredholm.exists_eigenvector_of_evalT_charPowerSeries_eq_zero` /
  `evalT_charPowerSeries_eq_zero_iff` (Riesz.lean:2208/:2221): zero `a` of
  `det(1−Tu)` (as `PowerSeries.evalT`, Riesz.lean:111 tsum) ⟺ eigenvector
  `u x = a⁻¹ • x`; over any `[NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]`, `{I} [DecidableEq I]` — no discreteness (ℂ₃-compatible;
  the `exists_riesz_decomposition` multiplicity layer DOES need discreteness and
  is deliberately NOT used).
- NewtonPolygons: `exists_weierstrass_factorisation` (PowerSeriesZeros:571,
  Blueprint 5.13 — polynomial factor along the polygon, polygon-agreement clause),
  `hasSum_zero_iff_aeval_eq_zero` (:818, Cor 5.14 — zeros in an isometric
  extension = roots of the 5.13 factor), `card_roots_slope`
  (PolynomialRoots:955, Thm 5.11 — root count at each slope), all at
  `negLogNorm`-normalisation.
- Slopes: `unitSlope_newtonPolygon₀OfPowerSeries_M22op` (4_SlopeReading:417,
  generic K) at `(ϖ₃ h3).val`-normalisation: `unitSlope j = j + 1/2`; underlying
  coefficient data `val_charCoeff_M22op`.  The E-wave crosses the
  `(ϖ₃ h3).val` ↔ `negLogNorm` seam by re-deriving the polygon data at
  `negLogNorm` from the same coefficient computation (scale `L = −log‖3‖`).
- Conjugation: `lemma210` (4_DiamondW:1203, PUBLIC):
  `Binvop ∘ (U3MatrixOp ∘ Bop) = blockOp diag(M11, M22, M33)`; `Bop_comp_Binvop`
  / `Binvop_comp_Bop` (:1001/:957); `blockOp_blockIncl` (1_BlockOp:631);
  `isCompactoid_M22op` (2_U3Data:1078, public), `isCompactoid_U3MatrixOp`
  (4_DiamondW:407, public).
- Base change: 8_HeckeSlopes' abstract layer (`map_charPowerSeriesU3`,
  transport lemmas incl. `map_sq_ν₃`) instantiates at ANY isometric
  `f : K₃ →+* L` — Wave E takes `L := ℂ_[3]`.
- Embedding: mathlib `Padic.adicCompletionEquiv` / `adicCompletion.padicEquiv`
  (Mathlib/NumberTheory/Padics/HeightOneSpectrum.lean:217) — continuous
  ℚ-algebra iso `v.adicCompletion ℚ ≃ ℚ_[p]`; compose with
  `algebraMap ℚ_[3] ℂ_[3]` (isometric by `PadicComplex.norm_extends'`).

New files: `PhD/JacobsSlash/U3/2_PadicEmbedding.lean` (ιC : K₃ →+* ℂ_[3],
isometric), `PhD/JacobsSlash/5_EigenSlopes.lean` (generic slope→zero→eigenvector
bridge + the M22 instantiation), `PhD/JacobsSlash/U3/9_EigenvaluesU3.lean` (the
milestones).

**Generality directive (user, 2026-08-06, BINDING)**: the bridge theorem — every
Newton-polygon slope of an entire series is the valuation of a reciprocal
eigenvalue — is stated in FULL generality (`exists_eigenvector_of_slope_charPowerSeries`
in E01: arbitrary complete algebraically closed ultrametric `K`, arbitrary
`{I} [DecidableEq I]`, arbitrary compactoid operator; zero Jacobs content).  It
lives in `5_EigenSlopes.lean` for now but is a public-API candidate for the
`TateFredholm`/`NewtonPolygons` seam (upstream once folder ownership with the
tatefredholm-eigen board is settled); E02 consumes it as a pure instantiation.

**Statement-form decisions**: valuations are expressed norm-side without `rpow`:
`‖a‖ ^ 2 = ‖(3 : ℂ_[3])‖ ^ (2 * j + 1)` (ℕ-powers; docstrings state
`v₃(a) = j + ½`).  Eigen-equations in the `u y = a • y` form (eigenVALUE `a`, so
the det-zero is at `a⁻¹`).  The W-eigenspace clause is `Wop … y = ωC • y` (W02 flip: block 1 = ω-eigenblock; thesis ω² = relabeling) —
model-level from W02 alone; E05 upgrades its reading to the genuine `W` via W07.

## Dependency graph (Phase 2)

```
W01 (oracle) ──→ W05 ──→ W06 ──┐
W03 ──→ W04 ──→ W05            ├─→ W07 (W-HEADLINE) ──┐
W02 (Wop diag) ────────────────┘                      │
   └──────────────→ E03                               ├─→ E05 (FINAL MILESTONE)
E00 (ιC) ──────────→ E03 ──→ [CLEANUP-ALL-2] ──→ E04 ─┘
E01 ──→ E02 ───────→ E03
```

---

# Phase 3 (opened 2026-08-07, user-directed): close the two audit gaps by REPLACEMENT

The 2026-08-07 audit of `PhD/JacobsSlash` found exactly two gaps (everything else is
certified; the sole assumption is the contracted `hClassNumberOne`).  The user's binding
instruction: **close them by replacing what they supersede — do not add parallel code.**

## Gap 1 — the U₃ and W form spaces are not identified

`heckeU3` lives on `kappaForms` (built from the narrow acting monoid `Δ₁ = toMatrix⁻¹Σ₁(9)`)
and `heckeW` on `kappaFormsWide` (built from `Δ₁(3) = toMatrix⁻¹Σ₁(3)`).  Same mathematical
space, different Lean objects, so no statement can apply both operators to one form.

**The minimal fix (prove `kappaFormsWide = kappaForms` and transport) is REJECTED**: it
leaves two space definitions, two level-slash actions, and two κ-operators alive — exactly
the parallel code the user forbade.

**The replacement fix (adopted): Σ₁(3) is the acting monoid, full stop.**  This is not a
convenience — it is what the W03 analysis established: all three `γ₉`-uses in the κ-layer
are `hγ9le3` weakenings, i.e. *the κ-analytics only ever need the mod-3 threshold*.  The
narrow monoid was never the honest domain.  Consequences:

- `η₃ ∈ Δ₁(3)` (its `(1,1)`-entry is literally `1`, so `v(1−1) = 0 ≤ γ₃`), so **both**
  `heckeU3` and `heckeW` are `heckeOperatorSlash` at the *same* `Δ' = Δ₁(3)` and the
  *same* `slashFixedPointsOfLE` — one space, by construction.  `kappaFormsWide_eq_kappaForms`
  is then not a lemma to prove but a duplication to delete.
- The narrow layer becomes dead and is removed: `levelMonoid1`, `levelMonoid1ToSigma1`,
  `kappaLevelSlashAction`, `kappaLevelSMulSlashClass`, `kappaFormsWide`,
  `kappaWideLevelSlashAction`, `kappaSlashWide_restrict`, and — inside `«4_KappaSlash»` —
  the whole Σ₁(9) κ-layer (`kappaSlash` on `Sigma1`, its `ofGenFun` inputs, the six
  `norm_sigma1_*` workhorses, the summability family, the cocycle, `kappaSlashAction`).
- **Import structure forces the direction of the move.**  `blockEntry` (`«6_Matrix»`,
  prefix 6) must be built from the *wide* κ-operator, because the S11 recipe returns the
  `Δ'`-slash.  So the wide layer cannot stay in `«7_DiamondHecke»` (prefix 7) — it moves
  **down** into `«4_KappaSlash»`, replacing the narrow layer there, and `Σ₁(3)` moves into
  `U3/«1_Setting»` next to `Σ₁(9)`.  Net LOC decreases (~275 duplicated lines removed).
- Naming after the move: the surviving operator is `kappaSlash` (the `Wide` suffix loses
  its meaning once there is only one), the surviving monoid is `levelMonoid1₃`, the
  surviving space is `kappaForms`.  `Sigma1` survives — but only as the *level congruence*
  defining `U₁(9)`, no longer as an acting monoid.

Verified preconditions (2026-08-07): the narrow workhorses have **no** users outside
`«4_KappaSlash»`; the only external narrow-layer users are the four `letI := kappaSlashAction`
lines in `«6_Matrix»`/`«7_Fredholm»`, all inside plumbing that this tranche deletes; every
Σ₁(9) membership fact `«6_Matrix»` needs composes with the existing `sigma1_le_sigma1₃`, so
nothing is re-proved.

## Gap 2 — E05's two clauses are parallel, not composed

E05 conjoins a ℂ₃-level fact (`Wop … y = ωC • y`) with a K₃-level fact (`heckeW` acts by the
transcribed `δ`).  Both are true; neither is linked to the other, because the δ-side has no
base-change layer (the ε-side has `map_h01 … map_h21` in `«3_BaseChange»`).

**Replacement fix**: build the missing δ base change, then restate E05's W-clause so the two
facts fuse into one:

```lean
∀ W', (∀ x z, matrixCoeff W' x z = ιC (matrixCoeff (Wop norm_three_lt_one ht) x z)) →
      W' y = ωC • y
```

— "`y` is an `ω`-eigenvector of **the base change of the K₃-matrix of the genuine `W`**",
that matrix being `Wop` by `heckeW_apply_classRep_eq_delta`.  The old `∀ φ i, heckeW …`
conjunct is then *removed*, not kept alongside: it is the hypothesis's justification, not a
second clause.

Placement is forced again: `map_delta*` cannot join `map_h*` in `«3_BaseChange»` (prefix 3)
because the `δ`s live in `«4_DiamondW»` (prefix 4).  They go in `«4_DiamondW»` beside the
`δ`s and `Wop`, which gains `import PhD.JacobsSlash.«3_BaseChange»` (legal: prefix stays
`1 + max(3,3,1) = 4`; no cycle — `3_BaseChange` imports only `2_U3Data` + TateFredholm).

## A third duplication removed on the way (in scope, not new work)

`«7_DiamondHecke»`'s `sigmaTableW = ![1,2,0]` and `deltaOf = ![δ₀₁, δ₁₂, δ₂₀]` re-express
data that `Wop`'s own block layout already fixes.  Both move to `«4_DiamondW»` (as `sigmaW`,
`deltaOf`) and the coincidence becomes the theorem `Wop_eq_blockOp_deltaOf` — which is also
exactly what Gap 2's `map_Wop` needs.  The certificate tables then *index off the same
`sigmaW`*, so "the certificate permutation equals `Wop`'s block layout" stops being an
informal remark and becomes definitional.

## Dependency graph (Phase 3)

```
U1 (Σ₁(3) → 1_Setting) ──→ U2 (κ-layer → 4_KappaSlash, narrow deleted) ──┬──→ U3 (6_Matrix) ──→ U4 (7_Fredholm)
                                                                          └──→ U5 (7_DiamondHecke) ──┐
M1 (sigmaW/deltaOf/Wop_eq_blockOp → 4_DiamondW) ──→ M2 (map_delta*, map_Wop) ──────────────────────────┴──→ M3 (E05 composed)
M1 ──→ U5   (U5's certificates index off the moved sigmaW)
```
