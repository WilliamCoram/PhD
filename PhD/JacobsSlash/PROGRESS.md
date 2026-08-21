# PhD/JacobsSlash — the right-slash thesis formalisation (fork map)

**Status: COMPLETE AND SORRY-FREE 2026-08-10** (boards
`.mathlib-quality/slashRefactor/` Phases 1–3, then `.mathlib-quality/hurwitz-cn1/`).
All modules build green with **zero sorries**: the last one, `hClassNumberOne`, was
proven 2026-08-10 in the new subfolder `CN1/` after the FLT deferral was cancelled
(see *Axiom contract* below).  The 2026-08-07 audit found exactly two gaps; Phase 3
closed both **by replacement** — see the last section.

This folder is the **self-enclosed** formalisation of Jacobs' thesis Ch. 2 in the
thesis's own **right-action ("slash") convention**, replacing `PhD/Jacobs`
(left-action original, now legacy-bound: NEVER import it).  Allowed imports:
`Mathlib`, `PhD.TateFredholm`, `PhD.QMF` (including the right-slash layer
`PhD.QMF.Slash`), `PhD.NewtonPolygons`, and earlier `PhD.JacobsSlash` files.
`import PhD.Jacobs` anywhere in this folder is a defect.

## Naming and conventions

* Files carry digit prefixes giving the dependency depth: a file's prefix is
  1 + max prefix among its JacobsSlash imports.  Module names need guillemets:
  `import PhD.JacobsSlash.U3.«6_Matrix»`.
* Everything lives in the flat namespace `JacobsSlash` (no `.U3` subnamespace).
* Right slash throughout: `RightSlashAction` / `f ∣ₛ δ` (`PhD.QMF.Slash.Basic`),
  right cosets `Quotient (QuotientGroup.rightRel U)`, the Hecke recipe
  `heckeOperatorSlash_apply_rep` in the thesis's `Σₜ φ(cᵢₜ)|κ(uₜvₜ)` display shape.
* `Σ₀'` is the d-unit form; `Σ₁(9)` is the thesis's `c ≡ 0, d ≡ 1 mod 9` congruence,
  which cuts out the **level** `U₁(9)`; `Σ₁(3)` (same integrality, `(1,1)`-entry a
  `1`-unit only mod `3`) is the **single acting monoid** — the honest domain of the
  weight-`κ` slash, since every analytic estimate needs only the mod-`3` threshold.
  Both live in `U3/1_Setting`.  `η₃ = (3 0; 0 1)`, `vₜ = η₃·uₜ` with `uₜ = (1 0; 9t 1)`,
  `μ = diag(1,4)`.

## The headline chain (statement names)

1. `heckeU3 := QMF.Weight.heckeOperator` at `η₃` on `kappaForms := QMF.Weight.Forms Dˣ θ
   (jacobsWeight t ht) U₁(9)` = `L(U₁(9), A₃)` (`U3/6_Matrix`; the fork's own action/space/
   Hecke definitions were replaced by the headline ones on 2026-08-19, forms-headline board).
2. `heckeU3_apply_classRep` — **unconditional**: `(U₃ φ)(cᵢ) = Σⱼ blockEntry i j (φ(cⱼ))` —
   the general matrix recipe `QMF.Weight.heckeOperator_apply_rep` at the `«5_Factorisations»`
   certificates, with `blockEntry := QMF.Weight.heckeBlock … etaRep … sigmaTable uTable`
   (2026-08-19, forms-headline T016: the fork's block layer is the general
   `PhD/QMF/Weight/Compact.lean` model instantiated — `evalU3 := evalAtReps … classRep`,
   `evalU3_heckeU3 := evalAtReps_heckeOperator`, `isCompactoid_blockOpU3 :=
   isCompactoid_heckeBlockOp` at `‖det (η₃)₃‖ = ‖3‖`).
3. **Twist-free identification** (`U3/5_Factorisations` + `U3/6_Matrix`): the
   certificate blocks equal the transcribed `ε`-operators ON THE NOSE —
   `blockEntry_eq_epsOp` is an exact equality, with no classWeight coboundary
   scalar (the left library's B15 twist vanishes identically in the thesis
   orientation; oracle record in `U3/certificate_search.py`).
4. `charPowerSeriesU3 := det(1 − T·U₃)` through the block model (`U3/7_Fredholm`);
   `charPowerSeriesU3_eq_U3MatrixOp` is definitional-after-rewrite (no
   determinant-twist bridge needed).
5. `charPowerSeriesU3_factorisation` (`U3/8_HeckeSlopes`) — over any complete
   ultrametric `L ⊇ K₃` (isometric) with `ω² + ω + 1 = 0`:
   `det(1 − T·U₃) = det(1 − T·M₁,₁)·det(1 − T·M₂,₂)·det(1 − T·M₃,₃)`, witnessed at
   `L₃ = ℚ₃(ζ₃)` by `charPowerSeriesU3_factorisation_L₃`.  With
   `unitSlope_newtonPolygon₀OfPowerSeries_M22op` (slopes `1/2, 3/2, 5/2, …`) this
   is [Jacobs, Cor 2.16] about the genuine `U₃`.

## Axiom contract (audited 2026-08-06)

* `heckeU3_apply_classRep`, `matrixCoeff_blockEntry`, `blockEntry_eq_epsOp`,
  `charPowerSeries_blockEntry_eq_U3MatrixOp`, `evalU3_heckeU3`,
  `isCompactoid_blockOpU3`, `map_charPowerSeriesU3`,
  `charPowerSeriesU3_factorisation`, `charPowerSeriesU3_factorisation_L₃`:
  exactly `[propext, Classical.choice, Quot.sound]`.
* `bijective_evalU3`, `kappaFormsModelEquiv`, `eval_classRep_injective`,
  `exists_classRep_factorisation`: same axioms — they take
  `hcn : HClassNumberOne` as an explicit hypothesis.
* **`hClassNumberOne : HClassNumberOne` is PROVEN** (`CN1/«4_Dictionary»`,
  [Jacobs, Lemma 1.22 (1.4.4)]) — axioms exactly `[propext, Classical.choice,
  Quot.sound]`.  History: deferred to FLT's `completed_units` 2026-08-05, deferral
  cancelled 2026-08-10 (FLT dropped its Hurwitz material) and proven in-repo via
  [Voight GTM 288] 11.3.2 → 11.3.4 → 27.6.8 (board `.mathlib-quality/hurwitz-cn1/`).
  Its only term-level consumer is `eval_classRep_injective'` (`U3/6_Matrix`) — every
  other statement carries the hypothesis explicitly.

## File map

Root (analytic layer, ports of the left originals):

| file | role |
|---|---|
| `1_PadicAnalytic` | p-adic analytic prerequisites (VERBATIM port) |
| `1_GenFun` | generating-function calculus, `idx`, `ext_matrixCoeff` norm form |
| ~~`1_BlockOp`~~ → `PhD/TateFredholm/BlockOp.lean` (moved 2026-08-18, namespace `TateFredholm`; forms-headline board R0) | `cSpace` blocks, `blockOp`, `matrixCoeff_*`, compactoid closure |
| `1_SlopeTheorem` | the slope machinery endpoint |
| `2_U3Data` | the transcribed [Jacobs p. 28] `ε`-displays + `h01…h21` (misprint at `eps12M2` corrected) |
| `3_BinomialTheorem` | p-adic binomial theorem at `K₃` |
| `3_Slopes` / `4_SlopeReading` | Newton-polygon slope reading of the `M`-blocks |
| `3_BaseChange` | the `map_h` entrywise base-change layer |
| `4_DiamondW` | `epsOp*`, `U3MatrixOp`, `M11op/M22op/M33op`, `charPowerSeries_U3MatrixOp`, `unitSlope_…_M22op` |
| `5_Instance` | the `ℂ_[3]` instantiation |

`U3/` (the quaternionic identification, right-slash native):

| file | role |
|---|---|
| `1_Setting` | `K₃` (normed-field pack: mathlib + `ForMathlib/…/Completion/FinitePlace` `NontriviallyNormedField` instance), `ν₃`, `θ : D⊗K₃ ≅ M₂(K₃)`, `Σ₁(9)` |
| `1_Hurwitz` | Hurwitz order units |
| `1_Compose` | composition prerequisites for the κ-cocycle |
| `2_Level` | `U₀(1)`, `U₁(9)`, `HClassNumberOne` statement (proven in `CN1/`) |
| `3_ClassSet` | class set = 3 reps (row-mirror invariant `(0,1)·red(u⁻¹)`), `classRep_complete`/`classRep_bijective` (Theorem 2.1), `stabilizerAt_classRep = ⊥` (Lemma 2.2) |
| `3_EtaDecomposition` | `η₃`, `etaRep`, right-coset decomposition + finiteness |
| `4_KappaColumn` (was `4_KappaSlash`, slimmed 2026-08-19, forms-headline T002) | the `Σ₁(3)` norm bounds and the κ-column closed form `coeff_yCoeff_kappaSeries₂`/`kappaSeries₂_eq_yExtend`; the weight *action* now lives in `PhD/QMF/Weight/` |
| `5_KappaWeight` | field-generic `sigma1Norm`, `jacobsCharOf`, `jacobsExpansionDataOf`, **`jacobsWeightOf`**; the thesis weight **`jacobsWeight := (jacobsWeightOf …).restrict sigma1₃_le_sigma1Norm`**, `genFun_jacobsWeight`, `matrixCoeff_kappaSlash_jacobsWeight` |
| `5_Factorisations` | the nine `cᵢ·vₜ⁻¹ = d·c_σ·u` certificates + `sum_weightGenFun_eq_h` (twist-free, oracle `certificate_search.py`) |
| `6_Matrix` | `kappaForms := QMF.FormsQ ℚ D v₃ (jacobsWeight t ht) U₁(9)` (= Buzzard's `S^D_κ(U)`), `heckeU3 := QMF.heckeUpiQ … 3 …` (= `U_ϖ`), `blockEntry := QMF.Weight.heckeBlock … etaRep … sigmaTable uTable` (abbrevs, 2026-08-19), `matrixCoeff_blockEntry`, `blockEntry_eq_epsOp`, `heckeU3_apply_classRep` (= `heckeOperator_apply_rep`), `eval_classRep_injective` (= `ext_of_forall_rep` at `classRep_bijective`) |
| `7_Fredholm` | `evalU3 := QMF.Weight.evalAtReps … classRep` (abbrev), `bijective_evalU3` (= `bijective_evalAtReps_of_stabilizer_eq_bot` at `classRep_bijective`/`stabilizerAt_classRep`), `kappaFormsModelEquiv`, `evalU3_heckeU3` (= `evalAtReps_heckeOperator`), `norm_det_toMatrix_eta3_le`, `isCompactoid_blockOpU3` (= `isCompactoid_heckeBlockOp`), `charPowerSeriesU3 := QMF.Weight.heckeCharPowerSeries …` (abbrev) |
| `8_HeckeSlopes` | base change (`matrixCoeff_U3MatrixOp_map`, `map_charPowerSeriesU3`) + eigenblock factorisation + `L₃` witness (**milestone**) |
| `10_Eigenforms` (2026-08-20, forms-riesz) | the thesis data over any isometric `L ⊇ K₃` (`thetaL`, `jacobsWeightL := jacobsWeightOf … (ι t)`, `kappaFormsL`, `heckeU3L`), `heckeBlockOpL_eq_U3MatrixOp`, `heckeCharPowerSeriesL_eq_map`, `bijective_evalU3L`, and **`exists_eigenform_U3_halfIntegral`** — Cor 2.16 as an eigen*form* statement over `ℂ₃` |

`CN1/` (class number one: the proof of `hClassNumberOne`, added 2026-08-10, board
`.mathlib-quality/hurwitz-cn1/`; route [Voight GTM 288] replacing the thesis's
Jacquet–Langlands citation):

| file | role |
|---|---|
| `2_Euclidean` | Hurwitz covering bound ≤ ½ (11.3.1), right division `a = b*q + r` (11.3.2), right ideals principal (11.3.4) |
| `3_LocalApprox` | local order coordinates over `𝓞_w`, ℤ-density in `𝓞_w`, finite-set integer approximation |
| `3_AdeleIntegrality` | integral scaling: `∃ N ≠ 0` clearing every place of a finite adele (cofinite integrality) |
| `4_Dictionary` | `latticeOf g` (denominator lattice), the local–global crux, generator factorisation, **`hClassNumberOne`** (27.6.8) |

## Phase 2 (2026-08-06): the W-identification and the eigenvalue endgame

### Wave E — **the crux, PROVEN**

`U3/9_EigenvaluesU3.lean` — `exists_eigenvalue_U3_halfIntegral`: over `ℂ₃`, for every
`j : ℕ` the base-changed matrix of the genuine `U₃` has an eigenvalue `a` with
`‖a‖² = ‖3‖^(2j+1)` (`3`-adic valuation **`j + ½`**), whose reciprocal is a zero of the
base-changed `det(1 − T·U₃)`, and whose eigenvector lies in the `ω`-eigenblock of the
transcribed diamond operator.  **Unconditional** — axioms exactly
`[propext, Classical.choice, Quot.sound]`, no `hClassNumberOne`.

Supporting files:

| file | role |
|---|---|
| `U3/2_PadicEmbedding` | `ιC : K₃ →+* ℂ_[3]`, isometric (`norm_ιC`), via mathlib's `Padic.adicCompletionEquiv` + a valuation squeeze; also `norm_three_eq : ‖3‖ = 3⁻¹` |
| `5_EigenSlopes` | **the general bridge** `exists_eigenvector_of_slope_charPowerSeries` — over any complete algebraically closed ultrametric field, every finite Newton-polygon slope of `det(1 − T·u)` of a compactoid `u` is the valuation of a reciprocal eigenvalue (Jacobs-free; **public-API candidate for the `TateFredholm` × `NewtonPolygons` seam**).  Plus the strict-slope transport, the `M₂,₂` slope data at `negLogNorm`, `exists_eigenvector_M22op`, and the block transport `exists_eigenvector_U3MatrixOp_of_M22` |
| `4_DiamondW` (+W02) | `Binvop_comp_Wop_comp_Bop`: `B⁻¹WB = diag(1, ω, ω²)` — block `1` (the `M₂,₂` slot) is the **ω**-eigenblock (the thesis's "ω²" is the ω ↦ ω² relabeling) |

### Wave W — `Wop` **is** the genuine `[U₁(9)·μ·U₁(9)]` (complete)

`U3/7_DiamondHecke.lean` — the wide monoid `Σ₁(3)` (the μ-acting elements are `1`-units
only mod `3`), `kappaSlashWide` with `_restrict`/`_mul`; the thesis's own
`μ = diag(1,4)` (fork handedness flip — in the d-form `U₁(9)` the trap is `diag(4,1)`),
its single right coset, and the three certificates
`σ_W = (1,2,0)`, `d_W = (−1,−1,+1)`, `u(i) = diag(−1/5,−1/8), diag(−5/7,−1/8), diag(7,1)`,
whose acting matrices `u(i)·μ = diag(−1/5,−1/2), diag(−5/7,−1/2), diag(7,4)` are the
thesis's `δ`-data **on the nose** — the identification is **twist-free**, exactly as the
`ε`-side turned out to be (oracle: `U3/certificate_search_w.py`).  Endpoints:
`kappaSlashWide_acting_eq_delta` (each acting operator *is* `δ₀,₁/δ₁,₂/δ₂,₀`, no
scalar), `heckeW := heckeOperatorSlash` at `μ` on `kappaFormsWide`, and
**`heckeW_apply_classRep_eq_delta`**: `(Wφ)(cᵢ) = δᵢ(φ(c_{σ_W(i)}))` — the transcribed
`Wop` is the matrix of the genuine `W`.  All unconditional.

### The culmination

`U3/9_EigenvaluesU3.lean` — `exists_eigenvalue_U3_in_W_eigenspace`: for every `j`, the
genuine `U₃` has an eigenvalue of `3`-adic valuation `j + ½` whose eigenvector lies in
the `ω`-eigenblock of the **genuine** diamond operator `W`, with the reciprocal
eigenvalue a zero of `det(1 − T·U₃)`.  [Jacobs, Cor 2.16] + the Lemma 2.9/2.10
eigenspace reading, as one theorem about the genuine Hecke operators.  Axioms exactly
`[propext, Classical.choice, Quot.sound]`.

### The culmination, for forms (2026-08-20, forms-riesz board)

`U3/10_Eigenforms.lean` — `exists_eigenform_U3_halfIntegral`: for every `j`, there is an
**eigenform** `φ` of `U₃` in the thesis's space of overconvergent forms *base-changed to*
`ℂ₃` (`kappaFormsL ιC norm_ιC t ht = QMF.Weight.Forms Dˣ (θ₃ ∘ ι) (jacobsWeightL …) U₁(9)`)
with `U₃ φ = a φ` and `‖a‖² = ‖3‖^{2j+1}`.  The thesis's own objects stay over `K₃`; only
the eigenvalue statement needs `ℂ₃`, because the eigenvalues of valuation `j + ½` are not in
`K₃`.  The transport is the general `QMF.Weight.BaseChange` layer (weight actions, Hecke
blocks, `det(1 − T·[UηU])` commute with an isometric `ι`) plus the field-generic
`jacobsWeightOf`.  Axioms exactly `[propext, Classical.choice, Quot.sound]`.

## Phase 3 (2026-08-07): the two audit gaps, closed by replacement

The audit found two gaps.  Both were closed by *replacing* what they superseded — no
parallel code was added; the fork lost more lines than it gained.

**Gap 1 — the `U₃` and `W` form spaces were not identified.**  Rather than prove
`kappaFormsWide = kappaForms` and transport (which would have left two spaces, two
level-slash actions and two κ-operators alive), the development now takes **`Σ₁(3)` as
the single acting monoid**.  Since `η₃`'s `(1,1)`-entry is `1`, `η₃ ∈ Δ₁(3)` as well as
`μ`, so `heckeU3` and `heckeW` are the *same* `heckeOperatorSlash` construction over the
same `slashFixedPointsOfLE` — **one space, by construction**, and the identification
lemma is not needed at all.  Deleted: `levelMonoid1`, `levelMonoid1ToSigma1`,
`kappaFormsWide`, `kappaWideLevelSlashAction`, `kappaSlashWide*` and the entire
Σ₁(9)-indexed κ-layer (its Σ₁(3) form is the only one).  Acceptance:
`(heckeU3 t ht).comp (heckeW t ht)` elaborates, and one `φ : kappaForms t ht` feeds both
operators' theorems in a single context.

**Gap 2 — the culmination's two clauses were parallel, not composed.**  `«4_DiamondW»`
gained the δ-side base change (`map_delta01/12/20`, `map_Wop` — the counterpart of the
ε-side `map_h*`) plus `sigmaW`, `deltaOf` and `Wop_eq_blockOp_deltaOf`, which makes "the
certificate permutation equals `Wop`'s block layout" definitional instead of a remark.
`exists_eigenvalue_U3_in_W_eigenspace` now ends in one clause —
`∀ W', (matrixCoeff W' = ιC ∘ matrixCoeff (Wop over K₃)) → W' y = ωC • y` — i.e. *`y` is
an `ω`-eigenvector of the base change of the matrix of the genuine `W`*; the old
`∀ φ, heckeW …` conjunct was deleted (it is the hypothesis's justification,
`heckeW_apply_classRep_eq_delta`, not a second conclusion).

## slopes-hecke board (2026-08-20)

* `1_SlopeTheorem.lean` no longer carries its own Hadamard/minor/combinatorics lemmas: the
  σ-general versions live in `PhD/TateFredholm/Slopes.lean` (`norm_det_le_pow_of_row_bound`,
  `norm_minor_le_pow_sum`, `choose_two_le_sum`, `choose_two_lt_sum_of_ne_range`,
  `norm_charCoeff_le_pow`), and the fork's *equality* (unit minors) is what stays here.
* `4_SlopeReading.lean` keeps only the two Jacobs cases; `NewtonPolygon₀.ofSlopes` and the four
  spec-level lemmas moved to `PhD/NewtonPolygons/OfSlopes.lean`.
* `5_KappaWeight.lean`'s `sigma1Norm` is now an abbreviation for the general
  `QMF.SigmaOne K ‖(3:K)‖`; `4_KappaColumn.lean`'s two valuation↔norm lemmas were deleted in
  favour of mathlib's `Valued.toNormedField.norm_le_iff` / `norm_le_one_iff`.
* NEW `U3/2_LevelTopology.lean`: the Hurwitz basis as a `Module.Basis`, the adelic coordinate
  maps, the lattice identity `{x | ∀ w, toLocal w x ∈ localOrder w} = QMF.integralTensor …`, and
  the level topology — **`isCompact_U0`, `isOpen_U0`, `isCompact_U1_9`, `isOpen_U1_9`** and
  `finite_image_doubleCoset_U1_9` (Hecke finiteness for every `η`, no representatives needed;
  `3_EtaDecomposition.lean`'s explicit `finite_image_eta3` stays, it is what computes the matrix).
  Five lemmas in `U3/2_Level.lean` were un-`private`d for it, and the file instantiates
  `QMF.RigidificationAt.IsCompletionLinear` from `theta_one_tmul`.

## Relation to the rest of the repo

* `PhD/QMF/Slash/` — the general right-slash abstract layer this fork consumes
  (`Sigma0'`, `RightSlashAction`, automorphic slash, `heckeOperatorSlash` +
  matrix recipe, right-slash quaternionic forms with the `spaceSlash_eq_space`
  agreement corollary to the left/FLT interface).
* `PhD/Jacobs/` — the left-action original: kept as history, to be moved to
  legacy by the user; nothing here may import it.  A future "the two `U₃`'s
  agree" bridge, if ever wanted, must itself be self-enclosed (explicitly
  deferred, user decision).
