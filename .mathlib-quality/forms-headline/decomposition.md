# Decomposition for forms-headline (A = Jacobs at the headline, B = classical inclusion, C = compactness of `U_ϖ`)

## Skeleton location (revised 2026-08-19 — replacement design)

Every *new* leaf is a `:= by sorry` declaration in:

- `PhD/QMF/Weight/Forms.lean` (defs `kappaLevelSlashActionTwisted` l. 118,
  `kappaLevelSMulSlashClassTwisted` l. 125 (proved), `Forms` l. 146, `heckeOperator` l. 176;
  sorries `mem_forms_iff` l. 156, `mem_forms_iff_one` l. 166)
- `PhD/QMF/Weight/Compact.lean` (NEW; defs `evalAtReps` l. 86 (proved), `heckeBlock` l. 113,
  `heckeBlockOp` l. 121; sorries `blockProj_evalAtReps` l. 92, `evalAtReps_injective` l. 99,
  `evalAtReps_heckeOperator` l. 128, `exists_mul_eta_mul_of_bijOn` l. 146,
  `norm_det_toMatrix_certificate_le` l. 157, `isCompactoid_heckeBlock` l. 168,
  `isCompactoid_heckeBlockOp` l. 181)
- `PhD/QMF/Weight/Algebraic.lean` (defs `classicalForms` l. 878, `classicalHeckeOperator`
  l. 888; sorries `map_classicalForms_le_forms`, `mem_map_classicalForms_iff`,
  `heckeOperator_mapCoeff_polyEmbed` — lines shift after T006)
- `PhD/QMF/Weight/Series.lean` (`LevelBounds.norm_det_le_one` l. 136,
  `LevelBounds.norm_apply_zero_zero_le_of_norm_det_le` l. 144, `rowIntAt_genFun` l. 316)
- `PhD/QMF/Weight/SlashAction.lean` (`norm_matrixCoeff_kappaSlash_le` l. 386,
  `isCompactoid_kappaSlash` l. 393, `isCompactoid_kappaSlash_of_norm_det_le` l. 399)
- `PhD/QMF/Weight/Char.lean` (`AnalyticWeight.isCompactoid_kappaSlash` l. 867)
- `PhD/TateFredholm/GenFun.lean` (`isCompactoid_of_row_decay'` l. 231)
- `PhD/TateFredholm/WeightGenFun.lean` (`RowIntAt.mono` l. 159)
- `PhD/TateFredholm/Riesz.lean` (`isCompactoid_zero` l. 624, `IsCompactoid.finset_sum` l. 628)
- `PhD/JacobsSlash/U3/5_KappaWeight.lean` (`genFun_jacobsWeight`, `matrixCoeff_kappaSlash_jacobsWeight`, after `kappaSlash_eq_jacobsWeight`)

`lake build PhD.QMF.Weight.Algebraic PhD.QMF.Weight.Compact PhD.QMF.Slash.Quaternionic
PhD.JacobsSlash.U3.«9_EigenvaluesU3» PhD.JacobsSlash.U3.«5_KappaWeight»` passes with **25
`sorry` warnings and no errors** (verified 2026-08-19).  R0 (the `1_BlockOp.lean →
TateFredholm/BlockOp.lean` move) is executed and the fork rebuilt green.

The refactoring tranches A′, B′, U have **no new leaves beyond those listed**: their
"leaves" are existing, proven fork/Algebraic theorems whose *statements* are preserved
while the duplicated *definitions* underneath them are replaced (spec in `tickets.md`).
One statement cannot be pre-stated (`evalU3_eq_evalAtReps`, T005: it needs `kappaForms` to
already be `Forms`); its exact text is fixed in T005.

Prior-B2 log (`.mathlib-quality/b2_log.jsonl`, 2 entries: `NewtonPolygon₀.unitSlope_cases`,
`NewtonPolygon₀.lengths_final`): **no name or shape match** with any leaf — clean.

Notation: `θ : G →* M₂(K)`, `S` the acting monoid with `hb : LevelBounds S ρ`,
`κ : AnalyticWeight UK S ρ`, `χ : S →* Kˣ`, `Forms Γ θ κ U hU χ`, `Δ = levelMonoidOf θ S`.

---

## Result A′ — the Jacobs endpoint at the headline, by replacement (README §5.2)

### Plain-English proof

[Jacobs, Def 1.27] defines `‖_κ` as the continuous extension of `z^k ↦ κ(cz+d)/(cz+d)²
((az+b)/(cz+d))^k`, "by κ(cz+d) we mean the power series expansion of κ(cz+d) at zero";
[Def 1.30] `L(U, A) = {φ : φ(dgu) = φ(g)‖_κ u_p}`; [Def 1.32] `[UvU]φ = Σ_t φ|v_t`.  The
general layer formalises exactly these for any `AnalyticWeight`; the fork's
`kappaSlash t ht`, `kappaForms`, `heckeU3` are the same definitions specialised to Jacobs's
`κ(u) = u^t` (the fork's own cocycle proof being the ODE argument of `kappaCol_cocycle`).
With `jacobsWeight := ofExpansionData (jacobsExpansionData t ht)` — the honest character
`jacobsChar` (`u ↦ u^t` on the principal units, [Jacobs p. 29] `κ(cx+d) = (cx+d)^t`) and its
expansion (`kappaSeries₂`, row decay, `hasSum_jacobsCol_unitPow`) — the general layer's
cocycle-by-evaluation-injectivity replaces the ODE, and the fork's objects can simply be
*defined* as the headline ones.  The only non-definitional fact needed downstream is that
the headline generating function at `jacobsWeight` is the fork's transcribed `weightGenFun`
(`genFun_jacobsWeight`; `matrixCoeff_kappaSlash_jacobsWeight` is the fork-facing matrix
formula), which is the identity `yExtend(κ-column) = kappaSeries₂` (the fork's
`yExtend_jacobsCol`) — `rfl` at the column since `AnalyticWeight` carries its expansion datum.

### Leaves

- **A′1** (leaf, project): `genFun_jacobsWeight`, `matrixCoeff_kappaSlash_jacobsWeight` —
  `5_KappaWeight.lean` (after `kappaSlash_eq_jacobsWeight`)
  ```lean
  theorem genFun_jacobsWeight (t : K₃) (ht : ‖t‖ < 1) (g : Matrix (Fin 2) (Fin 2) K₃) :
      (jacobsWeight t ht).toWeightSeries.genFun g = weightGenFun t g
  theorem matrixCoeff_kappaSlash_jacobsWeight (t : K₃) (ht : ‖t‖ < 1) (g : Sigma1₃) (m r : ℕ) :
      TateFredholm.matrixCoeff ((jacobsWeight t ht).kappaSlash g) m r
        = MvPowerSeries.coeff (TateFredholm.idx m r) (weightGenFun t g.1)
  ```
  - Source: [Jacobs, Prop 2.6, p. 29] (verbatim): "The generating function of the operator
    ‖_κ (a b; c d) is given by κ(cx+d)/((cx+d)(cx+d−axy−by))."  Both sides are this series
    (`QMF.WeightSeries.genFun`, Series.lean:221; `weightGenFun`, `2_U3Data`).
  - Discharged by: `rw [QMF.WeightSeries.genFun, weightGenFun]`; the column of
    `(jacobsWeight t ht).toWeightSeries` is `PowerSeries.mk fun n => unitPow t d *
    (binomialCoeff t n * (c/d)^n)` (`rfl`: `AnalyticWeight` carries the datum), and `yExtend` of it
    is `kappaSeries₂ t c d` (the fork's `yExtend_jacobsCol` proof).  Second lemma:
    `rw [AnalyticWeight.matrixCoeff_kappaSlash, genFun_jacobsWeight]`.
  - Attacks: [1] counterexample — none (R7: `jacobsWeightSeries_eq_toWeightSeries := WeightSeries.ext rfl`
    for the same datum); [3] hypothesis-strength — this pass first found that with the *Prop*
    version of `AnalyticWeight` (`Nonempty`/`Classical.choice`) the all-`g` statement was
    unprovable (column determined only on the level); the design was changed to carry the
    datum (user's question), after which the statement is `rfl`-based for all `g`.  [4] Prop 2.6
    is exactly this; [5] `matrixCoeff_kappaSlash` (Char.lean) verified.  SURVIVED (after the
    design change).

- **A′2** (refactor, spec = existing statements): T002–T005 (see `tickets.md`).  Composition
  attack: could deleting the fork's action change any downstream *theorem*?  No — every
  downstream statement is about `kappaForms`, `heckeU3`, `blockEntry`, `charPowerSeriesU3`,
  `U3MatrixOp`, whose *statements* are preserved; only definitions and proofs change, and the
  build is the oracle.  Risk: proofs that `unfold` the old `kappaSlash` (e.g. `heckeU3_apply_classRep`,
  `coeff_weightGenFun_diagonal`) must be re-routed through `matrixCoeff_kappaSlash_jacobsWeight` — ticketed.

---

## Result B′ — the classical inclusion at the headline, by replacement (README §5.3)

### Plain-English proof

[Buzzard §11 p. 73]: `L_{n,v} → A_{κ,r}` is `M₁`-equivariant, hence `L(U, L_{n,v}) ⊆ L(U, A_{κ,r})`.
In the project the injection is `polyEmbed` and equivariance is `polyEmbed_slash` (R6), stated
at the hand-built `algWeightSeries` twisted by `detTwist ν`.  Replacing `algWeightSeries` by
`(algWeight hb n).toWeightSeries` (same column: the polynomial `(C d + C c X)^(n+2)` — the
cocycle is now derived, not hand-proved) and the hand-built twisted level action by
`kappaLevelSlashActionTwisted θ (algWeight hb n) (detTwist ν)`, the R6 theorems become the
`Forms`-statements `map_classicalForms_le_forms`, `mem_map_classicalForms_iff`,
`heckeOperator_mapCoeff_polyEmbed` with the same proofs.

### Leaves

- **B′1** (refactor, T006): `algWeightSeries → algWeight`, delete `twistedKappaLevelAction`.
  Composition attack: `algExpansionData` currently *uses* `algWeightSeries.col/rowDecay` — made
  standalone first (T006 step 1) so nothing depends on the deleted def.  The polynomial cocycle
  proof becomes dead code and is deleted; the ExpansionData route derives it.  SURVIVED.
- **B′2** (leaf, project): `map_classicalForms_le_forms` — Algebraic.lean
  - Source: [Buzzard §11 p. 73] (verbatim): "If r ∈ (N_K)^J then there is a natural injection
    L_{n,v} → A_{κ,r} = O(B_r) induced from the natural inclusion B_r ⊂ (A¹)^I and one checks
    easily that this is an M₁-equivariant inclusion.  If U ⊂ D×_f is a compact open subgroup of
    level ≥ π then we get an inclusion S^D_{k,w}(U) = L(U, L_{n,v}) ⊆ L(U, A_{κ,r}) = S^D_κ(U; r)."
  - Lean ↔ source: `classicalForms` = `L(U, L_{n,v})` ([Buzzard §9 p. 70]), `mapCoeff (polyEmbed n ν)`
    = postcomposition with the injection, `Forms … (algWeight hb n) … (detTwist ν)` = `S^D_κ(U; r)` at
    `κ = (u ↦ u^(n+2), ν∘det)`; `Submodule.map … ≤ …` is "⊆".  Our twist is `ν` on the whole monoid;
    Buzzard normalises `v(π) = 1` — a different valid `χ` (README §3); the inclusion is unaffected.
  - Discharged by: `mapCoeff_mem_levelSubmoduleSlash (polyEmbed n ν) (polyEmbed_slash_level …) hU hφ`
    (R6's proof of `classicalToOverconvergent_mem`, Algebraic.lean:~676/809).
  - Attacks: [2] `n = 0, ν = 1` consistent (weight 2); [3] `hb` needed to state `algWeight`
    (Buzzard's "level ≥ π"); [4] verbatim; [5] lemma verified.  SURVIVED.
- **B′3** (leaf, project): `mem_map_classicalForms_iff` — the R6 endpoint
  `mem_range_classicalToOverconvergent_iff` (Algebraic.lean:960, proof ported verbatim).  Attacks:
  [3] polynomial-valued at *all* `g` as in R6; [5] verified.  SURVIVED.
- **B′4** (leaf, project): `heckeOperator_mapCoeff_polyEmbed` — R6's
  `heckeOperatorSlash_classicalToOverconvergent` (Algebraic.lean:829) via
  `heckeOperatorSlash_mapCoeff`, element identified by `Subtype.ext hψ`.  Attacks: [3] stated with
  `ψ, hψ` (the subtype-constructor form timed out at `whnf` in the skeleton — recorded); [5] verified.
  SURVIVED.

---

## Result C — compactness of `U_ϖ` at general weight (README §5.1)

### Plain-English proof (Jacobs Lemma 2.7 + Buzzard Lemma 12.2, in the Tate model)

**Step 1 (one matrix).**  For `g ∈ S`, the matrix of `κ.kappaSlash g` is the coefficient
array of `κ(cx+d)/((cx+d)(cx+d−axy−by))` (Prop 2.6, `matrixCoeff_kappaSlash`).  Each factor
is *row-integral at level σ* (`RowIntAt σ`: `‖coeff (x^j y^i)‖ ≤ σ^j`) as soon as `‖a‖ ≤ σ`,
`ρ ≤ σ`: `κ(cx+d)` by the weight's `rowDecay` (at ρ, hence at σ), `(cx+d)^{-1}` because
`‖c‖ ≤ ρ ≤ σ` and `‖d‖ = 1` (`rowIntAt_linSeries`, `RowIntAt.inv`), and `(cx+d−axy−by)^{-1}`
because additionally `‖a‖ ≤ σ`, `‖b‖ ≤ 1` (`rowIntAt_quadSeries`, `RowIntAt.inv`); products
of row-integral series are row-integral (`RowIntAt.mul`).  Hence `‖matrixCoeff j i‖ ≤ σ^j`
uniformly in `i`, and Jacobs Cor 1.10 / Serre (`isCompactoid_of_row_decay'`) gives
compactoid.  On a bounded level, `‖det g‖ ≤ σ` forces `‖a‖ ≤ σ` (`ad = det + bc`, `‖d‖=1`,
`‖bc‖ ≤ ρ`), which is Buzzard's hypothesis form.
**Step 2 (the double coset).**  Every coset representative `vₜ` of `UηU = ∐ U vₜ` is
`u₁ η u₂` (right-coset relation), so every certificate element `u(i,t)·vₜ` maps under θ to
`s·θ(η)·s'` with `s, s' ∈ S` integral, hence `‖det θ(u vₜ)‖ ≤ ‖det θ(η)‖ ≤ σ` (Buzzard:
"`det((x_δ)_p)/det(η_p)` is a unit").
**Step 3 (assembly).**  Evaluation at representatives `c : ι → G` sends `Forms` into
`c(ι × ℕ, K)`; by the matrix recipe ([Jacobs pp. 20–21], `heckeOperatorSlash_apply_rep`)
`[UηU]` acts as the block operator with blocks `Σ_{t : idx i t = j} χ(θ(u vₜ)) • κ.kappaSlash
(θ(u vₜ))` (Jacobs's `ε_{i,j}`); each block is a finite sum of scalar multiples of compactoid
operators (Step 1 + Step 2), and block operators with compactoid blocks are compactoid
(`isCompactoid_blockOp`), which is Buzzard's "hence `U_π` … is also … compact".  At a
section of `Γ\G/U`, evaluation is injective ([Buzzard §9 p. 69]), so the operator on `Forms`
is the restriction of the compactoid block operator.

### Lemmas (in order)

- **C1** (leaf, mathlib+project): `isCompactoid_of_row_decay'` — `TateFredholm/GenFun.lean:231`
  ```lean
  theorem isCompactoid_of_row_decay' {u : c(ℕ, K) →L[K] c(ℕ, K)} {σ C : ℝ} (hσ0 : 0 ≤ σ)
      (hσ : σ < 1) (h : ∀ j i, ‖matrixCoeff u j i‖ ≤ C * σ ^ j) : IsCompactoid u
  ```
  - Source: [Jacobs, Cor 1.10, p. 10] (verbatim): "Suppose that the matrix (n_{ji}) of u has
    all its entries in O_K.  If D(1/p)(n_{ji}) has all its entries in O_K, then u is
    compact."  (Row `j` scaled by `p^{-j}` integral ⟺ `‖n_{ji}‖ ≤ ‖p‖^j`.)
  - Lean ↔ source: `IsCompactoid u := Tendsto (rowNorm u) cofinite (𝓝 0)` with `rowNorm u j
    = ⨆ i, ‖matrixCoeff u j i‖`; the hypothesis gives `rowNorm u j ≤ C σ^j → 0`.  Real `σ`
    generalises the existing `isCompactoid_of_row_decay` (`‖q‖`, `q : K`) verbatim.
  - Discharged by: copy of `isCompactoid_of_row_decay`'s proof (`GenFun.lean:218–229`) with
    `‖q‖ ↦ σ`: `tendsto_pow_atTop_nhds_zero_of_lt_one hσ0 hσ`, `.const_mul`,
    `Nat.cofinite_eq_atTop`, `Real.iSup_le`, `tendsto_of_tendsto_of_tendsto_of_le_of_le`.
  - Attacks: [2] `σ = 0`: `σ^j = 0` for `j ≥ 1` — hypothesis then says rows ≥1 vanish; still
    compactoid ✓ (`0 ^ 0 = 1` handles j = 0); `C < 0`: hypothesis unsatisfiable unless u = 0
    — fine; [3] `hσ0` needed for `Real.iSup_le`'s nonneg side and the pow tendsto; [5]
    template proof compiles today.  SURVIVED.

- **C2** (leaf, mathlib): `RowIntAt.mono` — `WeightGenFun.lean:159`
  ```lean
  lemma RowIntAt.mono {σ : ℝ} (hρ0 : 0 ≤ ρ) (hρσ : ρ ≤ σ) {φ} (hφ : RowIntAt ρ φ) : RowIntAt σ φ
  ```
  - Source: none (monotonicity of `ρ^n` in `ρ ≥ 0`).  Discharged by: `fun p => (hφ p).trans
    (pow_le_pow_left₀ hρ0 hρσ _)`.  Attacks: [3] `hρ0` needed (`(-2)^1 ≤ (-1)^1` fails);
    [5] `pow_le_pow_left₀` (mathlib, `0 ≤ a → a ≤ b → a^n ≤ b^n`) — name to be confirmed
    with `lean_loogle` (variants `pow_le_pow_left`); trivial either way.  SURVIVED.

- **C3** (leaf, mathlib): `isCompactoid_zero`, `IsCompactoid.finset_sum` — `Riesz.lean:624, 628`
  ```lean
  theorem isCompactoid_zero : IsCompactoid (0 : c(I, R) →L[R] c(J, R))
  theorem IsCompactoid.finset_sum [IsTate R] {ι} (s : Finset ι) {f : ι → c(I, R) →L[R] c(J, R)}
      (hf : ∀ i ∈ s, IsCompactoid (f i)) : IsCompactoid (∑ i ∈ s, f i)
  ```
  - Source: [Serre] compact operators form a closed subspace; the project has `IsCompactoid.add`
    (`Riesz.lean:618`).  Discharged by: `rowNorm 0 j = 0` (`matrixCoeff` of `0` is `0`:
    `ContinuousLinearMap.zero_apply`; `Real.iSup` of the constant `0` is `0` — `ciSup_const`
    for nonempty `I`, `Real.iSup_of_isEmpty` otherwise, or `le_antisymm (Real.iSup_le …
    le_rfl) (rowNorm_nonneg _ _)`), so `tendsto_const_nhds`; `Finset.induction_on` with
    `Finset.sum_empty`, `Finset.sum_insert`, `IsCompactoid.add`.
  - Attacks: [2] empty `s`: sum is `0` — needs `isCompactoid_zero` (that is why it is a leaf);
    [3] `[IsTate R]` inherited from `IsCompactoid.add` (needed there for the ultrametric row
    bound); [5] `IsCompactoid.add` verified at `Riesz.lean:618`.  SURVIVED.

- **C4** (leaf, mathlib): `LevelBounds.norm_det_le_one` — `Series.lean:136`
  ```lean
  theorem LevelBounds.norm_det_le_one (hb : LevelBounds S ρ) {g} (hg : g ∈ S) : ‖g.det‖ ≤ 1
  ```
  - Source: [Buzzard, Lemma 12.2 proof] implicitly ("integral" entries); pure algebra.
    Discharged by: `Matrix.det_fin_two`, `IsUltrametricDist.norm_sub_le_max`/`norm_add_le_max`,
    `norm_mul`, `hb.integral hg i j`, `mul_le_one₀`.
  - Attacks: [2] `g = 1`: det = 1, `‖1‖ = 1 ≤ 1` ✓; [3] uses only `integral` — correct
    hypothesis strength; [5] `Matrix.det_fin_two` mathlib ✓.  SURVIVED.

- **C5** (leaf, mathlib): `LevelBounds.norm_apply_zero_zero_le_of_norm_det_le` — `Series.lean:144`
  ```lean
  theorem LevelBounds.norm_apply_zero_zero_le_of_norm_det_le (hb : LevelBounds S ρ) {σ}
      (hρσ : ρ ≤ σ) {g} (hg : g ∈ S) (hdet : ‖g.det‖ ≤ σ) : ‖g 0 0‖ ≤ σ
  ```
  - Source: [Buzzard, Lemma 12.2 proof, p. 79] (verbatim): "det((x_δ)_p)/det(η_p) is a unit
    at all places of F above p, and hence by Lemma 8.1(b) the endomorphism of A_{κ,r} induced
    by (x_δ)_p can be factored as the inclusion A_{κ,r} ⊂ A_{κ,r|π|} followed by a
    norm-decreasing map".  In the Tate model the "factoring through the smaller disc" is the
    smallness of the `a`-entry: `‖a‖·‖d‖ = ‖det g + b·c‖ ≤ max(σ, ρ) = σ`.
  - Discharged by: `Matrix.det_fin_two` (`det = g00*g11 − g01*g10`), so `g00 * g11 = det +
    g01*g10`; `norm_mul`, `hb.d_unit hg`, `IsUltrametricDist.norm_add_le_max`, `hb.integral
    hg 0 1`, `hb.c_le hg`, `max_le hdet (le_trans … hρσ)`.
  - Attacks: [1] counterexample search: `g = (a b; c d)` with `‖a‖ > σ` but `‖det‖ ≤ σ`
    requires `‖bc‖ = ‖ad‖ > σ ≥ ρ ≥ ‖c‖ ≥ ‖bc‖` — impossible ✓; [2] `g = 1`: det = 1 so
    hypothesis forces σ ≥ 1, conclusion `‖1‖ ≤ σ` ✓; [3] `hρσ` needed (`bc` term is only
    ρ-small); [4] the passage is about the *action*, our lemma is the matrix fact behind it
    — documented as such; [5] mathlib names ✓.  SURVIVED.

- **C6** (leaf, project): `WeightSeries.rowIntAt_genFun` — `Series.lean:316`
  ```lean
  theorem rowIntAt_genFun (W : WeightSeries S ρ) {g} (hg : g ∈ S) {σ} (hρσ : ρ ≤ σ)
      (ha : ‖g 0 0‖ ≤ σ) : RowIntAt σ (W.genFun g)
  ```
  - Source: [Jacobs, Lemma 2.7 proof, p. 30] (verbatim): "Note that by definition, h_{k,l}(x,y)
    ∈ O_3[[x,y]].  By Corollary 1.10, it suffices to prove that every entry in D(1/3)ε_{k,l}
    is in O_3.  Equivalently, we need to show that h_{k,l}(x/3, y) lies in O_3[[x,y]].  It
    is simply a case of checking that every coefficient of x is divisible by 3 in O_3."
  - Lean ↔ source: `RowIntAt σ (genFun g)` is "`h(x/σ, y)` integral": `‖coeff (x^j y^i)‖ ≤
    σ^j`.  Jacobs checks it per explicit `h_{k,l}`; here it is proved from the factorisation
    `genFun = yExtend(κcol) · linSeries⁻¹ · quadSeries⁻¹` (`Series.lean:221–223`) and the
    entry bounds — the fork's `norm_coeff_hXY_le` in general form.
  - Discharged by: `RowIntAt.mul hσ0 (RowIntAt.mul hσ0 ?_ ?_) ?_` with
    `(W.rowIntAt_yExtend hg).mono hρ0 hρσ` (C2), `(rowIntAt_linSeries hσ0 (hb.integral hg 1 1)
    ((hb.c_le hg).trans hρσ)).inv hσ0 (W.norm_constantCoeff_linSeries hg)`,
    `(rowIntAt_quadSeries hσ0 (hb.integral hg 1 1) ((hb.c_le hg).trans hρσ) ha (hb.integral hg 0 1)).inv
    hσ0 (W.norm_constantCoeff_quadSeries hg)`; `hσ0 : 0 ≤ σ := hb.rho_nonneg.trans hρσ`.
    All names verified in `WeightGenFun.lean:108,123,158,167` and `Series.lean:275,282`.
  - Attacks: [1] counterexample: `g = 1` (`a = 1`): hypothesis `‖1‖ ≤ σ` forces `σ ≥ 1`, and
    `RowIntAt σ` for `σ ≥ 1` is weaker than `CoeffInt` (`coeffInt_genFun`) ✓ — the recorded
    adversarial finding "full row decay is FALSE at γ = 1" (`WeightGenFun.lean:~178`) is
    exactly why `ha` is a hypothesis; [2] `σ = ρ` (Jacobs: `‖3‖`): the fork's bound; [3]
    `ha` cannot be dropped (γ = 1); `ρ ≤ σ` needed for the `c`-terms; `σ ≤ 1` NOT needed
    (RowIntAt is stated for any σ ≥ 0) ✓ minimal; [4] source: Jacobs's per-matrix
    divisibility check *is* this bound (with `‖a‖ = ‖3‖ = ρ` for his `vₜ = η₃uₜ`); [5]
    `RowIntAt.inv` requires `‖constantCoeff‖ = 1` — supplied by `d_unit` lemmas ✓ (verified
    signatures above).  SURVIVED.

- **C7** (leaf, project): `norm_matrixCoeff_kappaSlash_le`, `isCompactoid_kappaSlash`,
  `isCompactoid_kappaSlash_of_norm_det_le` — `SlashAction.lean:386–402`; re-export
  `AnalyticWeight.isCompactoid_kappaSlash` — `Char.lean:867`
  ```lean
  theorem norm_matrixCoeff_kappaSlash_le (W) (g : S) {σ} (hρσ : ρ ≤ σ) (ha : ‖g.1 0 0‖ ≤ σ) (j i) :
      ‖matrixCoeff (W.kappaSlash g) j i‖ ≤ σ ^ j
  theorem isCompactoid_kappaSlash (W) (g : S) {σ} (hρσ) (hσ : σ < 1) (ha) : IsCompactoid (W.kappaSlash g)
  theorem isCompactoid_kappaSlash_of_norm_det_le (W) (g : S) {σ} (hρσ) (hσ) (hdet : ‖g.1.det‖ ≤ σ) : …
  theorem AnalyticWeight.isCompactoid_kappaSlash (κ) (g : S) {σ} (hρσ) (hσ) (hdet) : IsCompactoid (κ.kappaSlash g)
  ```
  - Source: [Jacobs, Lemma 2.7, p. 30] (verbatim): "Every non-zero ε_{k,l} is compact." (proof
    quoted at C6); [Jacobs, Cor 1.10] (quoted at C1).
  - Discharged by: `matrixCoeff_kappaSlash` (`SlashAction.lean:364`), `idx_apply_zero`
    (`GenFun.lean:44`), C6; then `isCompactoid_of_row_decay' (C := 1) hσ0 hσ (by simpa using
    …)`; det form via C5; re-export by `κ.kappaSlash_def` (`κ.kappaSlash g =
    κ.toWeightSeries.kappaSlash g`, `rfl`).
  - Attacks: [2] `σ = 0`: `‖a‖ ≤ 0` forces `a = 0`; then `det = −bc`, `‖det‖ ≤ ρ`… consistent
    (`RowIntAt 0` says rows ≥ 1 vanish: `genFun` with `a = 0, c = 0`: `κ(d)/(d(d − by))` has
    no `x` — indeed only row 0 ✓ sanity); [3] `hσ < 1` needed for compactness (γ = 1, σ = 1
    is *not* compact — identity); [4] Jacobs proves compactness of each explicit `ε`; the
    general statement is his argument for an arbitrary `g` with small `a` — no drift; [5]
    `matrixCoeff_kappaSlash`, `idx_apply_zero` verified.  SURVIVED.

- **C8** (leaf, project): `blockProj_evalAtReps` — `Compact.lean:92`
  ```lean
  theorem blockProj_evalAtReps (c : ι → G) (φ : Forms Γ θ κ U hU χ) (i : ι) :
      cSpace.blockProj i (evalAtReps θ κ U hU χ c φ) = (φ : AutomorphicFunction G Γ c(ℕ, K)) (c i)
  ```
  - Source: [Buzzard §9 p. 69] (quote at A4).  Discharged by: exactly `blockProj_evalU3`'s
    proof (`7_Fredholm.lean:59–63`): `simp only [evalAtReps, LinearMap.coe_mk, AddHom.coe_mk,
    map_sum, cSpace.blockProj_blockIncl, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
  - Attacks: [2] `ι` empty: no `i` — vacuous ✓; [5] `cSpace.blockProj_blockIncl` verified
    (`BlockOp.lean:615`).  SURVIVED.

- **C9** (leaf, project): `evalAtReps_injective` — `Compact.lean:99`
  ```lean
  theorem evalAtReps_injective [Fintype (DoubleCoset.Quotient ↑Γ ↑U)] [DecidableEq …]
      (σ : DoubleCoset.Quotient ↑Γ ↑U → G) (hσ : ∀ q, Quotient.mk'' (σ q) = q) :
      Function.Injective (evalAtReps (Γ := Γ) θ κ U hU χ σ)
  ```
  - Source: [Buzzard §9 p. 69] (verbatim): "Note that f ∈ L(U,A) is determined by f(τ_λ)".
  - Discharged by: `bijective_evalAtRepsSlash K hU σ hσ` (`Slash/HeckeMatrix.lean:181`,
    sorry-free) `.1`: from `evalAtReps φ = evalAtReps ψ` get `φ (σ q) = ψ (σ q)` for all q
    (`blockProj_evalAtReps`, C8), hence `evalAtRepsSlash φ = evalAtRepsSlash ψ` (`funext q,
    Subtype.ext`), hence `φ = ψ`.
  - Attacks: [3] `hσ` (a genuine section) is required — for an arbitrary family evaluation
    is not injective; [4] Buzzard's "determined by" is injectivity ✓; [5] the bijectivity
    theorem exists with exactly `(σ, hσ)` hypotheses ✓.  SURVIVED.

- **C10** (leaf, project): `evalAtReps_heckeOperator` — `Compact.lean:128`
  ```lean
  theorem evalAtReps_heckeOperator {η} (hη) (h) (c : ι → G) (vRep : T → G) (hvΔ) (hv : BijOn …)
      (hvinj) (idx : ι → T → ι) (d : ι → T → G) (hd : ∀ i t, d i t ∈ Γ) (u : ι → T → U)
      (hfact : ∀ i t, c i * (vRep t)⁻¹ = d i t * c (idx i t) * (u i t : G)) (φ : Forms Γ θ κ U hU χ) :
      evalAtReps θ κ U hU χ c (heckeOperator θ κ U hU hη h φ)
        = heckeBlockOp θ κ U hU χ vRep hvΔ idx u (evalAtReps θ κ U hU χ c φ)
  ```
  - Source: [Jacobs pp. 20–21] (verbatim): "(U_p φ)(c_i) = Σ_{j∈I} ε_{i,j} φ(c_j) = Σ_{t∈T}
    (φ|v_t)(c_i) … = Σ_{t∈T} φ(c(i,t))‖_κ (u(i,t) v_t)_p.  We may think of ε_{i,j} as being
    ‖_κ (u(i,t) v_t)_p if c_j = c(i,t)."
  - Lean ↔ source: `heckeBlock i j = Σ_{t : idx i t = j} χ(θ(u vₜ)) • κ.kappaSlash (θ(u vₜ))`
    is Jacobs's `ε_{i,j}` (with Buzzard's scalar); the identity is his display, read through
    `blockOp`.
  - Discharged by: `heckeOperatorSlash_apply_rep K hU hη h φ vRep hvΔ hv hvinj (c i) (fun t =>
    c (idx i t)) (d i) (hd i) (u i) (hfact i) (fun t => mul_mem (hU (u i t).2) (hvΔ t))`
    (`Slash/HeckeMatrix.lean:57`) at each `i` gives `(heckeOperator φ)(c i) = Σ_t φ(c (idx i t))
    ∣ₛ ⟨u vₜ, _⟩`; the coefficient slash is `χ(…) • κ.kappaSlash (…)` (`twist_slash`,
    `comap_slash`); then as in `evalU3_heckeU3` (`7_Fredholm.lean:113–118`): `simp only
    [evalAtReps, map_sum, blockOp_blockIncl]`, regroup the `t`-sum by `j = idx i t`
    (`Finset.sum_fiberwise` / `Finset.sum_comm` + `Finset.sum_filter`), `heckeBlock` unfolds,
    `ContinuousLinearMap.sum_apply`, `smul_apply`.
  - Attacks: [2] `T` empty (η ∉ …): both sides `0` ✓; single class `ι = Unit`: `heckeBlock` =
    the full sum, `blockOp` = that operator ✓; [3] `hvinj` and `hv` are the recipe's
    hypotheses (present in `heckeOperatorSlash_apply_rep`), not extra; `hd`,`hfact` are the
    factorisation certificates — Jacobs's "we decompose c_i v_t^{-1} as d(i,t)c(i,t)u(i,t)";
    [4] the display is transcribed verbatim (right cosets `U·vₜ`, factorisation of `cᵢvₜ⁻¹`);
    [5] `heckeOperatorSlash_apply_rep` verified with matching hypothesis shapes; the
    `blockOp_blockIncl` lemma verified (`BlockOp.lean:631`).  SURVIVED.
  - LOC: Jacobs's display is 6 lines (p. 21) and the fork's `evalU3_heckeU3` is 5 lines of
    Lean given `heckeU3_apply_classRep` (which is ~25 lines from the recipe); expect ~40 LOC.

- **C11** (leaf, mathlib): `exists_mul_eta_mul_of_bijOn` — `Compact.lean:146`
  ```lean
  theorem exists_mul_eta_mul_of_bijOn {η} {vRep : T → G} (hv : BijOn mk (range vRep) (mk '' ({η} * U)))
      (t : T) : ∃ u₁ ∈ U, ∃ u₂ ∈ U, vRep t = u₁ * η * u₂
  ```
  - Source: [Buzzard, Lemma 12.2 proof] "If one decomposes UηU into a finite disjoint union
    ∐_δ U x_δ of cosets" — `x_δ ∈ UηU`.  Discharged by: `hv.mapsTo ⟨t, rfl⟩ : mk (vRep t) ∈
    mk '' ({η} * U)` gives `x = η * u₂` with `mk x = mk (vRep t)`; `Quotient.eq''` +
    `QuotientGroup.rightRel_apply` (`mk x = mk y ↔ y * x⁻¹ ∈ U`) gives `vRep t * (η u₂)⁻¹ =: u₁
    ∈ U`, so `vRep t = u₁ * η * u₂` (`mul_inv_cancel_right`, `mul_assoc`).
  - Attacks: [2] `η = 1`: `vRep t ∈ U` ✓; [3] only `MapsTo` part of `BijOn` used ✓ (weaker
    hypothesis would do; stated with `BijOn` to match the recipe's data); [5] mathlib names ✓
    (`Mathlib/GroupTheory/Coset/Defs.lean:111`).  SURVIVED.

- **C12** (leaf, project): `norm_det_toMatrix_certificate_le` — `Compact.lean:157`
  ```lean
  theorem norm_det_toMatrix_certificate_le {σ} {η} (hdet : ‖(θ η).det‖ ≤ σ) {vRep} (hv) (u : U) (t : T) :
      ‖(θ ((u : G) * vRep t)).det‖ ≤ σ
  ```
  - Source: [Buzzard, Lemma 12.2 proof] (quoted at C5): "det((x_δ)_p)/det(η_p) is a unit at
    all places of F above p".  Discharged by: C11 (`vRep t = u₁ η u₂`), `map_mul`,
    `Matrix.det_mul`, `norm_mul`, `hb.norm_det_le_one` (C4) at `θ (u u₁)`, `θ u₂` (members of
    `S` by `hU`), `mul_le_of_le_one_left/right`, `hdet`.
  - Attacks: [3] needs `hU : ↑U ⊆ Δ` — a section variable ✓; [4] Buzzard's "unit" ratio is
    our "≤ 1 outer factors" — same content in norm terms; [5] `Matrix.det_mul` ✓.  SURVIVED.

- **C13** (leaf, project): `isCompactoid_heckeBlock` — `Compact.lean:168`
  ```lean
  theorem isCompactoid_heckeBlock {σ} (hρσ : ρ ≤ σ) (hσ : σ < 1) {η} (hdet : ‖(θ η).det‖ ≤ σ)
      {vRep} (hvΔ) (hv) (idx) (u) (i j : ι) : IsCompactoid (heckeBlock θ κ U hU χ vRep hvΔ idx u i j)
  ```
  - Source: [Jacobs, Lemma 2.7] "Every non-zero ε_{k,l} is compact."  Discharged by:
    `IsCompactoid.finset_sum` (C3) over the filter, each term `IsCompactoid.smul _
    (κ.isCompactoid_kappaSlash _ hρσ hσ (norm_det_toMatrix_certificate_le …))` (C7, C12).
  - Attacks: [2] empty filter (no `t` with `idx i t = j`): block is `0` — `isCompactoid_zero`
    (C3) ✓ (Jacobs: "here ε_{i,j} is the zero endomorphism"); [3] `[IsTate K]` for the
    closure lemmas: instance for nontrivially normed fields (`Tate.lean:239`) ✓; [5]
    `IsCompactoid.smul` verified (`Riesz.lean:635`, scalar `a : R`; our scalar is `(χ … : K)`).
    SURVIVED.

- **C14** (leaf, project): `isCompactoid_heckeBlockOp` — `Compact.lean:181`
  ```lean
  theorem isCompactoid_heckeBlockOp … : IsCompactoid (heckeBlockOp θ κ U hU χ vRep hvΔ idx u)
  ```
  - Source: [Buzzard, Lemma 12.2] (verbatim): "and hence U_π, considered as an endomorphism
    of S^D_κ(U; r), is also norm-decreasing and compact."  Discharged by:
    `isCompactoid_blockOp fun i j => isCompactoid_heckeBlock …` (`BlockOp.lean:678`).
  - Attacks: [3] `[Fintype ι] [DecidableEq ι]` needed by `blockOp` ✓; [5] `isCompactoid_blockOp`
    verified (needs `[IsTate R]` ✓).  SURVIVED.

### Internal nodes (composition attacks)

- **C = C14 ∘ (C13 ∘ (C7, C12, C3)) ∘ C10**: could the blocks be compactoid and the block
  operator not? No — `isCompactoid_blockOp` is unconditional for finite `ι`.  Could the
  transport (C10) hold and the operator on `Forms` fail to be "compact"? The operator on
  `Forms` is the restriction of the block operator along the (injective at a section, C9)
  `evalAtReps`; that is the precise content, stated as such — no stronger claim ("`Forms` is a
  Banach space") is made or needed.  Composition SURVIVED.
- **A**: A2/A3 rest on A1 (instance equality) via A0'; A4/A5 on the fork's proven theorems.
  Could A1 be false? Only if `kappaSlash t ht g ≠ (jacobsWeight t ht).kappaSlash g` — R8
  proved equality.  SURVIVED.
- **B**: B3/B4/B5 rest on B2 + R6 theorems + A0'.  Composition SURVIVED.

## Result U — the fork's block layer as the instance of C

- `evalU3 = evalAtReps … classRep` (both `∑ i, blockIncl i (φ (classRep i))`),
  `blockEntry = heckeBlock … etaRep sigmaTable uTable` (both `∑_{σ(i,t')=j} (jacobsWeight).kappaSlash
  (θ(u(i,t')·vₜ'))`, the general one carrying `(1 : K₃) •`), `evalU3_heckeU3 = evalAtReps_heckeOperator`
  at the fork's certificates, `isCompactoid_blockOpU3 = isCompactoid_heckeBlockOp` at
  `‖det θ(η₃)‖ = ‖3‖ = ρ`.  Composition attack: the fork's certificate tables
  (`5_Factorisations`: `classRep i * (etaRep t')⁻¹ = d · classRep (sigmaTable i t') · uTable i t'`)
  have exactly the shape of `hfact`; `bijOn_etaRep` (`3_EtaDecomposition`) is `hv`; `etaRep`
  injective is `hvinj` — all verified present by name.  If any table is indexed differently,
  T016 says: generalise `heckeBlock`, never duplicate.  SURVIVED (as a plan; the build is the oracle).

### API gaps

None: every leaf is discharged from mathlib or existing project code (verified names above);
the only new *infrastructure* is the R0 module move (done) and the three tiny TateFredholm
lemmas C1–C3.  The refactoring tranches carry re-certification risk, not mathematical risk:
every statement they touch is already proven today.
