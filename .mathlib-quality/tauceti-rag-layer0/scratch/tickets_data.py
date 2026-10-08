# -*- coding: utf-8 -*-
"""Ticket data for the board `tauceti-rag-layer0`. Statements are NOT stored here: the generator
copies them verbatim from the skeleton (through sorries.json). A ticket lists its declarations as
(file, name) or (file, name, occurrence)."""

B = 'TateAlgebra/Basic.lean'
RED = 'TateAlgebra/Reduction.lean'
EV = 'TateAlgebra/Eval.lean'
EVR = 'TateAlgebra/EvalReduction.lean'
SUP = 'SupSeminorm.lean'
MM = 'TateAlgebra/MaxModulus.lean'
DIST = 'TateAlgebra/Distinguished.lean'
FIN = 'TateAlgebra/Finiteness.lean'
CH = 'TateAlgebra/Chart.lean'
RU = 'Rueckert.lean'
TRU = 'TateAlgebra/Rueckert.lean'
BALD = 'Bald.lean'
ON = 'PadicFunctionalAnalysis/Orthonormal.lean'
LIFT = 'OrthonormalLift.lean'
SC = 'TateAlgebra/StrictlyClosed.lean'
WS = 'WeaklyStable.lean'
JAP = 'Japanese.lean'
ST = 'TateAlgebra/Stable.lean'
EX = 'TateAlgebra/Examples.lean'

T = []  # proof tickets, in board order

def t(**kw):
    T.append(kw)

# ---------------------------------------------------------------- G1 Basic
t(id='T001', title='Gauss terms and truncations', file=B, deps='none', par='yes (with T002, G5, G10, G12, G13, G16, G17, T038)',
  typ='lemmas', leaves='L1.1, L1.2, L1.6',
  decls=[(B,'norm_coeff_mul_prod_le'),(B,'exists_norm_eq_norm_coeff_mul_prod'),(B,'exists_finset_norm_sub_sum_monomial_lt')],
  sketch="""1. `norm_coeff_mul_prod_le`: `exact (norm_le_iff c f).mp le_rfl t` (the floor's criterion).
2. `exists_norm_eq_norm_coeff_mul_prod`: `obtain ⟨t, ht⟩ := exists_achievesGaussNorm c f` and
   `exact ⟨t, (norm_def c f).trans ht.symm⟩` — the proof of the floor's `exists_coeff_ne_zero_norm_eq`
   without its `f ≠ 0`.
3. `exists_finset_norm_sub_sum_monomial_lt`: unfold `hasSum_monomial c f` exactly as the floor's own proof
   does (`rw [HasSum, SummationFilter.unconditional_filter, Metric.tendsto_atTop]`), take the finset `s` it
   gives for `ε`, and rewrite `dist` to `‖f - ∑ …‖` with `dist_eq_norm`, `norm_sub_rev`.""",
  mathlib="""Floor: `Restricted.norm_le_iff`, `Restricted.exists_achievesGaussNorm`, `Restricted.norm_def`, `Restricted.hasSum_monomial`. Mathlib: `Metric.tendsto_atTop`, `dist_eq_norm`, `norm_sub_rev`.""",
  sources="""[BGR] 5.1.1, `bgr-5.1.md:27–36`; decomposition L1.1, L1.2, L1.6.""",
  gen="""A normed ring `R` and an arbitrary polyradius `c` (the floor's generality). No `f ≠ 0` in item 2.""")

t(id='T002', title='Constants embed: nontriviality, characteristic zero, domain', file=B, deps='none', par='yes (with T001)',
  typ='instances', leaves='L1.3, L1.4, L1.5',
  decls=[(B,'instNontrivial'),(B,'instCharZero'),(B,'instIsDomain')],
  sketch="""⚠ The elaborated statements carry **no** `Fact (∀ i, 0 < c i)` (checked in `scratch/signatures.txt`), so
the norm is not available; all three proofs go through the underlying power series.

1. `instNontrivial`: `⟨⟨0, 1, fun h ↦ zero_ne_one (α := R) ?_⟩⟩`, where the goal follows from
   `congrArg (fun f : Restricted R c ↦ MvPowerSeries.constantCoeff f.1) h` with `val_zero`, `val_one`,
   `map_zero`, `map_one`.
2. `instCharZero`: `charZero_of_injective_ringHom (f := C c) ?_`; injectivity: from `C c a = C c b` apply
   `congrArg (fun f ↦ MvPowerSeries.constantCoeff f.1)` and `val_C`, `MvPowerSeries.constantCoeff_C`.
   (`RingHom.charZero` goes the other way.)
3. `instIsDomain`: `haveI : NoZeroDivisors R := NormMulClass.toNoZeroDivisors`; then
   `NoZeroDivisors (Restricted R c)`: from `f * g = 0` get `f.1 * g.1 = 0` (`congrArg Subtype.val`-style
   through `val_mul`, `val_zero`), use Mathlib's instance `NoZeroDivisors (MvPowerSeries σ R)`, and return
   with `Restricted.ext`. Finish with `NoZeroDivisors.to_isDomain`.""",
  mathlib="""`charZero_of_injective_ringHom`, `MvPowerSeries.constantCoeff_C`, `NormMulClass.toNoZeroDivisors`, `NoZeroDivisors.to_isDomain`, the instance `NoZeroDivisors (MvPowerSeries σ R)` (found by `inferInstance`). Floor: `Restricted.ext`, `val_zero`, `val_one`, `val_mul`, `val_C`.""",
  sources="""[BGR] 5.1.2/1, `bgr-5.1.md:67`, `:84`; [Bo] `bosch-lectures.txt:376`; [RM] §0.1.4; decomposition L1.3–L1.5.""",
  gen="""Every polyradius, no positivity. `instCharZero` is on `Restricted R c` because Mathlib already has `IsFractionRing.charZero`. `NormMulClass R` (not `NoZeroDivisors R`) in `instIsDomain`: it is the companion of the floor's `NormMulClass (Restricted R c)`.""")

t(id='T003', title='Polynomials are dense; the Gauss norm is a `K`-algebra norm', file=B, deps='T001', par='no',
  typ='lemmas', leaves='L1.7, L1.8',
  decls=[(B,'denseRange_toRestricted'),(B,'norm_smul_eq')],
  sketch="""1. `denseRange_toRestricted`: `rw [Metric.denseRange_iff]`; for `f`, `ε` take `s` from
   `exists_finset_norm_sub_sum_monomial_lt c f hε` (T001) and the polynomial
   `p := ∑ t ∈ s, MvPolynomial.monomial t (coeff t f.1)`; `map_sum` and `MvPolynomial.toRestricted_monomial`
   identify `toRestricted c p` with the truncation; `dist_eq_norm`.
2. `norm_smul_eq`: `le_antisymm`.
   - `≤`: `(norm_le_iff c _).mpr fun t ↦ ?_`; `val_smul`, `MvPowerSeries.coeff_smul`, `norm_mul`, `mul_assoc`,
     then `mul_le_mul_of_nonneg_left (norm_coeff_mul_prod_le c f t) (norm_nonneg a)`.
   - `≥`: if `a = 0`, `simp`. Otherwise apply the `≤` just proved to `a⁻¹` and `a • f`:
     `‖f‖ = ‖a⁻¹ • a • f‖ ≤ ‖a‖⁻¹ * ‖a • f‖`, and clear the inverse (`le_inv_mul_iff₀`-style, or multiply by
     `‖a‖ > 0` and `linarith`).
   The instance `instNormedAlgebra` below it is already complete and uses this lemma.""",
  mathlib="""`Metric.denseRange_iff`, `MvPowerSeries.coeff_smul`, `norm_mul`, `norm_inv`, `inv_smul_smul₀`, `mul_le_mul_of_nonneg_left`. Floor: `MvPolynomial.toRestricted_monomial`, `Restricted.val_smul`, `Restricted.norm_le_iff`.""",
  sources="""[BGR] 5.1.1/1, `bgr-5.1.md:34–36`; [Bo] `bosch-lectures.txt:373`; decomposition L1.7, L1.8.""",
  gen="""Density for a normed commutative ring (needed by `MvPolynomial`); the equality `‖a • f‖ = ‖a‖ * ‖f‖` for a normed field (over a ring only `≤` holds).""")

t(id='T004', title='The unit polyradius: the Gauss norm is the largest coefficient', file=B, deps='CLEANUP-1', par='no',
  typ='lemmas', leaves='L1.9–L1.12',
  decls=[(B,'norm_coeff_le'),(B,'exists_norm_coeff_eq'),(B,'norm_le_iff_forall_norm_coeff_le'),(B,'norm_lt_iff_forall_norm_coeff_lt')],
  sketch="""Private helper first: `prod_one_pow (t : σ →₀ ℕ) : t.prod ((1 : σ → ℝ) · ^ ·) = 1`
(`simp [Finsupp.prod]`: `Pi.one_apply`, `one_pow`, `Finset.prod_const_one`).

1. `norm_coeff_le`: `norm_coeff_mul_prod_le 1 f t` rewritten with the helper and `mul_one`.
2. `exists_norm_coeff_eq`: `exists_norm_eq_norm_coeff_mul_prod 1 f`, rewritten, `.symm`.
3. `norm_le_iff_forall_norm_coeff_le`: `(norm_le_iff 1 f).trans` and `simp only [helper, mul_one]`.
4. `norm_lt_iff_forall_norm_coeff_lt`: the same with the floor's `norm_lt_iff`.""",
  mathlib="""`Finsupp.prod`, `Finset.prod_const_one`, `one_pow`. Floor: `Restricted.norm_le_iff`, `Restricted.norm_lt_iff`.""",
  sources="""[BGR] 5.1.1, `bgr-5.1.md:29`; 5.1.2, `bgr-5.1.md:74–75`; [RM] §0.1.2; decomposition L1.9–L1.12.""",
  gen="""Any index type `σ` and any normed ring. These four lemmas are the only place the product `1 ^ t` is simplified; everything later uses them.""")

t(id='T005', title='`|Tₙ| = |K|` and normalisation', file=B, deps='T004', par='no',
  typ='lemmas', leaves='L1.13–L1.16',
  decls=[(B,'tendsto_norm_coeff_cofinite'),(B,'finite_setOf_le_norm_coeff'),(B,'norm_mem_range_norm'),(B,'exists_norm_smul_eq_one')],
  sketch="""1. `tendsto_norm_coeff_cofinite`: `f.2` is the defining `Tendsto (fun t ↦ ‖coeff t f.1‖ * t.prod (1 · ^ ·))
   cofinite (𝓝 0)`; `refine f.2.congr fun t ↦ ?_` and the helper of T004 (the floor reads `f.2` the same way
   in `hasSum_monomial`).
2. `finite_setOf_le_norm_coeff`: `have h := (tendsto_norm_coeff_cofinite f).eventually_lt_const hε`;
   `rw [Filter.eventually_cofinite] at h`; `exact h.subset fun t ht ↦ not_lt.2 ht`.
3. `norm_mem_range_norm`: `obtain ⟨t, ht⟩ := exists_norm_coeff_eq f; exact ⟨_, ht⟩`.
4. `exists_norm_smul_eq_one`: `obtain ⟨t, ht⟩ := exists_norm_coeff_eq f`; `‖coeff t f.1‖ = ‖f‖ ≠ 0`, so
   `a := (coeff t f.1)⁻¹ ≠ 0`; `norm_smul_eq`, `norm_inv`, `ht`, `inv_mul_cancel₀`.""",
  mathlib="""`Filter.Tendsto.eventually_lt_const`, `Filter.eventually_cofinite`, `Set.Finite.subset`, `norm_inv`, `inv_mul_cancel₀`, `norm_ne_zero_iff`.""",
  sources="""[BGR] 5.1.1, `bgr-5.1.md:18–19`, `:38–41` (Observation 2); decomposition L1.13–L1.16.""",
  gen="""Items 1–3 for a normed ring; item 4 for a normed field, with `a ≠ 0` recorded because the scaling is undone later (T026, T043).""")

# ---------------------------------------------------------------- G2 Reduction
t(id='T006', title='The reduced coefficients form a polynomial; additive laws', file=RED, deps='CLEANUP-2', par='yes (with G3)',
  typ='lemmas', leaves='L2.1, L2.2, L2.4, L2.5',
  decls=[(RED,'finite_support_residue_unitBallCoeff'),(RED,'reductionFun_one'),(RED,'reductionFun_zero'),(RED,'reductionFun_add')],
  sketch="""Private helper: `residue_unitBallCoeff_eq_zero_iff (f) (t) :
residue _ (unitBallCoeff f t) = 0 ↔ ‖coeff t f.1.1‖ < 1` — `residue_eq_zero_iff`,
`maximalIdeal_unitClosedBall`, `mem_openUnitBallIdeal`, `coe_unitBallCoeff`.

1. `finite_support_residue_unitBallCoeff`: `(finite_setOf_le_norm_coeff f.1 one_pos).subset fun t ht ↦ ?_`;
   `ht` says the residue is nonzero, so by the helper `¬ ‖coeff t f.1.1‖ < 1`, i.e. `1 ≤ ‖…‖`.
2. `reductionFun_zero`, `_one`, `_add`: `MvPolynomial.ext _ _ fun t ↦ ?_`, `coeff_reductionFun`; the element
   `unitBallCoeff (f + g) t` equals `unitBallCoeff f t + unitBallCoeff g t` by `Subtype.ext` (`val_add`,
   `map_add`), similarly for `0` and `1` (`MvPowerSeries.coeff_one`, an `if` on `t = 0`, matched with
   `MvPolynomial.coeff_one`); then `map_add`, `map_zero`, `map_one` of `residue`.""",
  mathlib="""`IsLocalRing.residue_eq_zero_iff`, `MvPolynomial.ext`, `MvPolynomial.coeff_one`, `MvPolynomial.coeff_add`, `MvPowerSeries.coeff_one`, `Finsupp.ofSupportFinite_coe`. Chain: `NormedRing.maximalIdeal_unitClosedBall`, `NormedRing.mem_openUnitBallIdeal`.""",
  sources="""[BGR] 5.1.2, `bgr-5.1.md:78–83`; [Bo] `bosch-lectures.txt:382–389`; decomposition L2.1, L2.2, L2.4, L2.5.""",
  gen="""Any normed field (no completeness, trivial valuation allowed) and any `σ`.""")

t(id='T007', title='The reduction is multiplicative', file=RED, deps='T006', par='no',
  typ='lemma', leaves='L2.3',
  decls=[(RED,'reductionFun_mul')],
  sketch="""`MvPolynomial.ext _ _ fun t ↦ ?_`; `coeff_reductionFun`, `MvPolynomial.coeff_mul`. On the left,
`coeff t (f * g).1.1 = ∑ p ∈ Finset.antidiagonal t, coeff p.1 f.1.1 * coeff p.2 g.1.1`
(`val_mul`, `MvPowerSeries.coeff_mul`), so
`unitBallCoeff (f * g) t = ∑ p ∈ antidiagonal t, unitBallCoeff f p.1 * unitBallCoeff g p.2` by `Subtype.ext`
(push the coercion through the sum with `AddSubmonoidClass.coe_finsetSum`). Then
`map_sum`, `map_mul` and `coeff_reductionFun` again.""",
  mathlib="""`MvPolynomial.coeff_mul`, `MvPowerSeries.coeff_mul`, `map_sum`, `map_mul`, `AddSubmonoidClass.coe_finsetSum`.""",
  sources="""[Bo] `bosch-lectures.txt:384–385` (`π` is an epimorphism of rings); decomposition L2.3.""",
  gen="""As T006. Both antidiagonals are over `σ →₀ ℕ`, so no reindexing is needed.""")

t(id='T008', title='The kernel of the reduction', file=RED, deps='T007', par='no',
  typ='lemmas', leaves='L2.6–L2.8',
  decls=[(RED,'reduction_eq_zero_iff'),(RED,'norm_eq_one_of_reduction_ne_zero'),(RED,'ker_reduction')],
  sketch="""1. `reduction_eq_zero_iff`: `rw [MvPolynomial.ext_iff]`; `simp only [coeff_reduction, MvPolynomial.coeff_zero]`;
   the helper of T006 turns each condition into `‖coeff t f.1.1‖ < 1`; conclude with
   `(norm_lt_iff_forall_norm_coeff_lt f.1).symm`.
2. `norm_eq_one_of_reduction_ne_zero`: `le_antisymm (Subring.norm_le_one f) (not_lt.1 fun h ↦ hf ((reduction_eq_zero_iff f).2 h))`.
3. `ker_reduction`: `Ideal.ext fun f ↦ ?_`; `RingHom.mem_ker`, item 1, `mem_openUnitBallIdeal`.""",
  mathlib="""`MvPolynomial.ext_iff`, `MvPolynomial.coeff_zero`, `RingHom.mem_ker`. Chain: `Subring.norm_le_one`, `NormedRing.mem_openUnitBallIdeal`.""",
  sources="""[BGR] `bgr-5.1.md:83`; [Bo] `bosch-lectures.txt:390–391`; [RM] §0.1.2; decomposition L2.6–L2.8.""",
  gen="""As T006.""")

t(id='T009', title='Surjectivity: polynomials over the unit ball', file=RED, deps='CLEANUP-3', par='no',
  typ='lemmas', leaves='L2.9–L2.13',
  decls=[(RED,'norm_toRestricted_map_subtype_le_one'),(RED,'reduction_ofUnitBallPolynomial'),(RED,'exists_sub_ofUnitBallPolynomial_mem_openUnitBallIdeal'),(RED,'reduction_surjective'),(RED,'reductionEquiv_mk')],
  sketch="""Private helper: `coeff_toRestricted_map_subtype (p) (t) :
coeff t (MvPolynomial.toRestricted 1 (MvPolynomial.map (unitClosedBall K).subtype p)).1 = (p.coeff t : K)` —
`MvPolynomial.val_toRestricted`, `MvPolynomial.coeff_coe`, `MvPolynomial.coeff_map`.

1. `norm_toRestricted_map_subtype_le_one`: `(norm_le_iff_forall_norm_coeff_le _).2 fun t ↦ ?_`; helper;
   `Subring.norm_le_one`.
2. `reduction_ofUnitBallPolynomial`: `MvPolynomial.ext`; `coeff_reduction`, `MvPolynomial.coeff_map`; the two
   elements of `K⁰` agree by `Subtype.ext` and the helper (`coe_ofUnitBallPolynomial`).
3. `exists_sub_ofUnitBallPolynomial_mem_openUnitBallIdeal`: `s := (finite_setOf_le_norm_coeff f.1 one_pos).toFinset`,
   `p := ∑ t ∈ s, MvPolynomial.monomial t (unitBallCoeff f t)`; `mem_openUnitBallIdeal` and
   `norm_lt_iff_forall_norm_coeff_lt`: the coefficient of the difference at `t` is `0` for `t ∈ s` and
   `coeff t f` (of norm `< 1`) otherwise (`MvPolynomial.coeff_sum`, `coeff_monomial`, `Finset.sum_ite_eq`).
4. `reduction_surjective`: for `q`, `obtain ⟨p, rfl⟩ := MvPolynomial.map_surjective _ residue_surjective q`;
   `exact ⟨ofUnitBallPolynomial p, reduction_ofUnitBallPolynomial p⟩`.
5. `reductionEquiv_mk`: `rfl`, or `simp [reductionEquiv, Ideal.quotEquivOfEq_mk]` with
   `RingHom.quotientKerEquivOfSurjective_apply_mk`.""",
  mathlib="""`MvPolynomial.coeff_coe`, `MvPolynomial.coeff_map`, `MvPolynomial.map_surjective`, `IsLocalRing.residue_surjective`, `Ideal.quotEquivOfEq_mk`, `RingHom.quotientKerEquivOfSurjective`, `MvPolynomial.coeff_monomial`, `Finset.sum_ite_eq`. Floor: `MvPolynomial.val_toRestricted`.""",
  sources="""[BGR] 5.1.2/2, `bgr-5.1.md:69`, `:83`; `bgr-5.2.md:78–82`; [Bo] `bosch-lectures.txt:382–385`; decomposition L2.9–L2.13.""",
  gen="""Item 3 (`T⁰ = K⁰[X] + T⁰⁰`) is stated separately because T020 and T021 consume it.""")

t(id='T010', title='Power-bounded and topologically nilpotent series', file=RED, deps='T009', par='no',
  typ='lemmas', leaves='L2.14, L2.15',
  decls=[(RED,'isPowerBounded_iff_forall_norm_coeff_le_one'),(RED,'isTopologicallyNilpotent_iff_forall_norm_coeff_lt_one')],
  sketch="""1. `isPowerBounded_iff_forall_norm_coeff_le_one`:
   `PowerBounded.isPowerBounded_iff_norm_le_one.trans (norm_le_iff_forall_norm_coeff_le f)`. The chain lemma
   needs `[NormMulClass (Restricted 𝕜 1)]` (floor instance) and `[NeBot (𝓝[≠] (0 : Restricted 𝕜 1))]`
   (floor instance from `NeBot (𝓝[≠] (0 : 𝕜))`, which is `NormedField.nhdsNE_neBot`).
2. `isTopologicallyNilpotent_iff_forall_norm_coeff_lt_one`:
   `isTopologicallyNilpotent_iff_norm_lt_one.trans (norm_lt_iff_forall_norm_coeff_lt f)`.""",
  mathlib="""`NormedField.nhdsNE_neBot`. Chain: `PowerBounded.isPowerBounded_iff_norm_le_one`, `isTopologicallyNilpotent_iff_norm_lt_one`.""",
  sources="""[BGR] 5.1.2, `bgr-5.1.md:86` (`T̊ₙ = Tₙ°`, `Ťₙ = Tₙˇ`); [RM] §0.1.2; decomposition L2.14, L2.15.""",
  gen="""Power-boundedness over a nontrivially normed field (the chain lemma's hypothesis; [RM] convention 1); topological nilpotence over any normed field.""")

t(id='T011', title='Units of the Tate algebra and of its unit ball', file=RED, deps='T010', par='no',
  typ='lemmas', leaves='L2.16–L2.18',
  decls=[(RED,'isUnit_iff_norm_coeff_lt'),(RED,'isUnit_iff_isUnit_reduction'),(RED,'isUnit_coe_iff_isUnit_reduction')],
  sketch="""1. `isUnit_iff_norm_coeff_lt`: `rw [Restricted.isUnit_iff]` (floor, `c = 1`), then
   `constantCoeff_eq_coeff_zero`, `isUnit_iff_ne_zero`, and the helper `prod_one_pow` of T004 inside the
   `∀ t ≠ 0` (use `forall_congr'`).
2. `isUnit_iff_isUnit_reduction`: `(NormedRing.isUnit_iff_isUnit_mk f).trans ?_`; then
   `rw [← reductionEquiv_mk]` and `(isUnit_map_iff reductionEquiv _).symm` (the `IsLocalHom` instance of an
   equivalence is `isLocalHom_equiv`).
3. `isUnit_coe_iff_isUnit_reduction`: `←`: item 2 and `IsUnit.map (unitClosedBall _).subtype`. `→`: from
   `hu : IsUnit (f : T)` get `g` with `f * g = 1`; `norm_mul`, `hf`, `norm_one` give `‖g‖ = 1`, so
   `g ∈ unitClosedBall _`; build the unit of `T⁰` (`isUnit_iff_exists_inv`, `Subtype.ext`) and use item 2.""",
  mathlib="""`isUnit_iff_ne_zero`, `isUnit_map_iff`, `isLocalHom_equiv`, `IsUnit.map`, `isUnit_iff_exists_inv`, `norm_mul`, `norm_one`. Floor: `Restricted.isUnit_iff`, `Restricted.constantCoeff_eq_coeff_zero`. Chain: `NormedRing.isUnit_iff_isUnit_mk`.""",
  sources="""[BGR] 5.1.3/1, `bgr-5.1.md:96–104`; [Bo] 1.2/4, `bosch-lectures.txt:431–441`; decomposition L2.16–L2.18.""",
  gen="""`K` complete. `coeff 0 f.1 ≠ 0` is a separate conjunct so that the statement is right for `σ` empty. Item 3 needs `‖f‖ = 1` (`f = p` is a unit of `T` with reduction `0`).""")

t(id='T012', title='The Jacobson radical of the Tate algebra is zero', file=RED, deps='CLEANUP-4', par='no',
  typ='lemmas', leaves='L2.19, L2.20',
  decls=[(RED,'exists_norm_eq_one_not_isUnit_C_add'),(RED,'jacobson_bot')],
  sketch="""1. `exists_norm_eq_one_not_isUnit_C_add` (BGR's two cases; `a₀ := coeff 0 f.1`, `‖a₀‖ ≤ 1` by
   `norm_coeff_le`).
   - `‖a₀‖ < 1`: take `a = 1`. By `exists_norm_coeff_eq f` there is `t` with `‖coeff t f.1‖ = 1`, and `t ≠ 0`.
     The constant coefficient of `C 1 1 + f` is `1 + a₀`, of norm `1`
     (`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`), and its coefficient at `t` is `coeff t f.1`
     (`val_add`, `val_C`, `MvPowerSeries.coeff_C`, `if_neg`), of norm `1`: the strict inequality of
     `isUnit_iff_norm_coeff_lt` fails at `t`.
   - `‖a₀‖ = 1`: take `a = -a₀`; the constant coefficient of `C 1 (-a₀) + f` is `0`, so it is not a unit by
     `isUnit_iff_norm_coeff_lt`.
2. `jacobson_bot`: `eq_bot_iff.2 fun f hf ↦ ?_`; by contradiction assume `f ≠ 0`. Take `a ≠ 0` with
   `‖a • f‖ = 1` (`exists_norm_smul_eq_one`); `a • f = C 1 a * f` lies in `jacobson ⊥` (ideal). Take `c`
   from item 1 for `a • f`; `c ≠ 0`. `Ideal.mem_jacobson_bot` at `y := C 1 c⁻¹` gives
   `IsUnit (a • f * C 1 c⁻¹ + 1)`, and `a • f * C 1 c⁻¹ + 1 = C 1 c⁻¹ * (C 1 c + a • f)` with `C 1 c⁻¹` a
   unit — contradiction.""",
  mathlib="""`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, `MvPowerSeries.coeff_C`, `Ideal.mem_jacobson_bot`, `IsUnit.mul_iff`, `Algebra.smul_def`. Floor: `Restricted.algebraMap_apply`, `Restricted.val_C`.""",
  sources="""[BGR] 5.1.3/2–3, `bgr-5.1.md:108–124`; decomposition L2.19, L2.20.""",
  gen="""Any index type `σ` (no finiteness). Only the forward half of the unit criterion is used.""")

# ---------------------------------------------------------------- G3 Eval
t(id='T013', title='The evaluated series converges', file=EV, deps='CLEANUP-2', par='yes (with G2)',
  typ='lemmas', leaves='L3.1–L3.3',
  decls=[(EV,'norm_map_mul_prod_pow_le'),(EV,'tendsto_map_coeff_mul_prod_pow'),(EV,'summable_map_coeff_mul_prod_pow')],
  sketch="""1. `norm_map_mul_prod_pow_le`: `B` has no `NormOneClass`, so split on `t`.
   - `t = 0`: `Finsupp.prod_zero_index`, `mul_one` on both sides, `hφ a`.
   - `t ≠ 0`: `(norm_mul_le _ _).trans (mul_le_mul (hφ a) ?_ (norm_nonneg _) (norm_nonneg _))`, and for the
     product (`Finsupp.prod` is a `Finset.prod` over the nonempty `t.support`):
     `Finset.norm_prod_le'` (nonempty), then `Finset.prod_le_prod` with, on the support (where `0 < t i`),
     `norm_pow_le'` and `pow_le_pow_left₀ (norm_nonneg _) (hx i)`.
2. `tendsto_map_coeff_mul_prod_pow`: `squeeze_zero_norm' (Filter.Eventually.of_forall fun t ↦ ?_) f.2` with
   item 1 (`f.2` is the nullity of the Gauss terms).
3. `summable_map_coeff_mul_prod_pow`:
   `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (tendsto_map_coeff_mul_prod_pow c φ x hφ hx f)`.""",
  mathlib="""`Finset.norm_prod_le'`, `norm_pow_le'`, `pow_le_pow_left₀`, `Finset.prod_le_prod`, `Finsupp.prod_zero_index`, `squeeze_zero_norm'`, `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`.""",
  sources="""[BGR] 5.1.4, `bgr-5.1.md:219–223`, `:253`; decomposition L3.1–L3.3.""",
  gen="""A contractive ring homomorphism `φ : R →+* B` into a normed commutative ring and any polyradius; `B` complete and ultrametric only for summability. No `NormOneClass B`.""")

t(id='T014', title='Evaluation: zero, one, addition', file=EV, deps='T013', par='no',
  typ='lemmas', leaves='L3.4–L3.6',
  decls=[(EV,'eval₂Fun_zero'),(EV,'eval₂Fun_one'),(EV,'eval₂Fun_add')],
  sketch="""1. `eval₂Fun_zero`: `simp [eval₂Fun]` (`val_zero`, `map_zero`, `zero_mul`, `tsum_zero`).
2. `eval₂Fun_one`: `unfold eval₂Fun`; `rw [tsum_eq_single 0]`; at `0`: `val_one`, `MvPowerSeries.coeff_one`,
   `map_one`, `Finsupp.prod_zero_index`, `mul_one`; for `t ≠ 0` the coefficient is `0`. No summability is
   needed, which is why the statement has no hypothesis.
3. `eval₂Fun_add`: `unfold eval₂Fun`; rewrite the summand with `val_add`, `map_add`, `add_mul`;
   `Summable.tsum_add` with `summable_map_coeff_mul_prod_pow` twice.""",
  mathlib="""`tsum_eq_single`, `tsum_zero`, `Summable.tsum_add`, `MvPowerSeries.coeff_one`, `Finsupp.prod_zero_index`.""",
  sources="""[BGR] 5.1.3/5, `bgr-5.1.md:153–155`; decomposition L3.4–L3.6.""",
  gen="""As T013.""")

t(id='T015', title='Evaluation is multiplicative (Cauchy product)', file=EV, deps='T013', par='no',
  typ='lemma', leaves='L3.7',
  decls=[(EV,'eval₂Fun_mul')],
  sketch="""Add `import PhD.TauCeti.Code.PadicFunctionalAnalysis.Sums` to the file (Mathlib's
`Summable.mul_of_nonarchimedean` needs a `NonarchimedeanRing` instance that an ultrametric normed ring
does not have at the pin).

Write `u f t := φ (coeff t f.1) * t.prod fun i k ↦ x i ^ k`.
1. `hf : Summable (u f)`, `hg : Summable (u g)` (T013), and
   `hfg : Summable fun p : (σ →₀ ℕ) × (σ →₀ ℕ) ↦ u f p.1 * u g p.2` from
   `IsUltrametricDist.summable_prod_map₂ (b := (· * ·)) norm_mul_le hf hg`.
2. `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal hf hg hfg :
   (∑' t, u f t) * ∑' t, u g t = ∑' t, ∑ p ∈ Finset.antidiagonal t, u f p.1 * u g p.2`.
3. Termwise, `u (f * g) t = ∑ p ∈ antidiagonal t, u f p.1 * u g p.2`: `val_mul`, `MvPowerSeries.coeff_mul`,
   `map_sum`, `map_mul`, `Finset.sum_mul`, and for `p ∈ antidiagonal t` (`p.1 + p.2 = t`):
   `Finsupp.prod_add_index'` (with `pow_zero`, `pow_add`) to split `x ^ t`; reorder with `mul_mul_mul_comm`.
4. `tsum_congr` and item 2.""",
  mathlib="""`Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`, `MvPowerSeries.coeff_mul`, `Finsupp.prod_add_index'`, `Finset.mem_antidiagonal`, `mul_mul_mul_comm`, `tsum_congr`. Chain: `IsUltrametricDist.summable_prod_map₂`.""",
  sources="""[BGR] 5.1.3/5, `bgr-5.1.md:153–155`; the Cauchy product, `bgr-2.md:56–59`; decomposition L3.7.""",
  gen="""Commutativity of `B` is used to reorder `x ^ p.1 * φ b`. This is the one substantial computation of the file.""")

t(id='T016', title='Values, contraction and continuity of `eval₂`', file=EV, deps='CLEANUP-6', par='no',
  typ='lemmas', leaves='L3.8–L3.13',
  decls=[(EV,'eval₂_monomial'),(EV,'eval₂_C'),(EV,'eval₂_X'),(EV,'eval₂_toRestricted'),(EV,'norm_eval₂_le'),(EV,'continuous_eval₂')],
  sketch="""1. `eval₂_monomial`: `rw [eval₂_apply, tsum_eq_single t]`; `val_monomial`, `MvPowerSeries.coeff_monomial`
   (`if_pos rfl` at `t`, `if_neg`, `map_zero`, `zero_mul` elsewhere).
2. `eval₂_C`: the same with `val_C`, `MvPowerSeries.coeff_C`, and `Finsupp.prod_zero_index`, `mul_one` at `0`.
3. `eval₂_X`: `val_X`, `MvPowerSeries.coeff_X`, the single term at `Finsupp.single i 1`;
   `Finsupp.prod_single_index (pow_zero _)`, `pow_one`, `map_one`, `one_mul`.
4. `eval₂_toRestricted`: prove `(eval₂ c φ x hφ hx).comp (MvPolynomial.toRestricted c) = MvPolynomial.eval₂Hom φ x`
   by `MvPolynomial.ringHom_ext` (`toRestricted_C`, `toRestricted_X`, items 2–3, `MvPolynomial.eval₂_C`,
   `eval₂_X`), then `RingHom.congr_fun`.
5. `norm_eval₂_le`: `IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg f) fun t ↦
   (norm_map_mul_prod_pow_le c φ x hφ hx _ t).trans (norm_coeff_mul_prod_le c f t)`.
6. `continuous_eval₂`: `AddMonoidHomClass.continuous_of_bound _ 1 fun f ↦ by rw [one_mul]; exact norm_eval₂_le hφ hx f`.""",
  mathlib="""`tsum_eq_single`, `MvPowerSeries.coeff_monomial`, `MvPowerSeries.coeff_C`, `MvPowerSeries.coeff_X`, `Finsupp.prod_single_index`, `MvPolynomial.ringHom_ext`, `MvPolynomial.eval₂_C`, `MvPolynomial.eval₂_X`, `IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg`, `AddMonoidHomClass.continuous_of_bound`. Floor: `MvPolynomial.toRestricted_C`, `MvPolynomial.toRestricted_X`.""",
  sources="""[BGR] 5.1.3/5, `bgr-5.1.md:150–155`; 5.1.4/2, `bgr-5.1.md:250–255`; decomposition L3.8–L3.13.""",
  gen="""Continuity is of the homomorphism `f ↦ f(x)`; continuity in `x` is not claimed.""")

t(id='T017', title='A continuous homomorphism is determined on constants and variables', file=EV, deps='T003', par='yes (with T013–T016)',
  typ='lemmas', leaves='L3.14, L3.19',
  decls=[(EV,'ringHom_ext_of_continuous'),(EV,'algHom_ext_of_continuous')],
  sketch="""1. `ringHom_ext_of_continuous`: `DFunLike.coe_injective ?_`, then
   `(denseRange_toRestricted c).equalizer h₁ h₂ (funext fun p ↦ ?_)`; the pointwise goal is
   `RingHom.congr_fun (MvPolynomial.ringHom_ext (f := ψ₁.comp (MvPolynomial.toRestricted c))
   (g := ψ₂.comp (MvPolynomial.toRestricted c)) ?_ ?_) p`, with the two goals closed by `toRestricted_C`,
   `hC` and `toRestricted_X`, `hX`.
2. `algHom_ext_of_continuous`: `AlgHom.coe_ringHom_injective` (or `AlgHom.ext` after `RingHom.congr_fun`) of
   item 1 applied to the underlying ring homomorphisms; `hC a` is
   `by rw [← algebraMap_apply]; simp [AlgHom.commutes]`.""",
  mathlib="""`DenseRange.equalizer`, `MvPolynomial.ringHom_ext`, `AlgHom.commutes`, `AlgHom.coe_ringHom_injective`. Floor: `MvPolynomial.toRestricted_C`, `MvPolynomial.toRestricted_X`, `Restricted.algebraMap_apply`.""",
  sources="""[BGR] 5.1.3/5, `bgr-5.1.md:151–153`; decomposition L3.14, L3.19.""",
  gen="""The target is any Hausdorff topological semiring; continuity is a hypothesis (BGR's automatic continuity, 5.1.3/4, is specific to Tate algebras and is not on the board).""")

t(id='T018', title='Evaluation as a `K`-algebra homomorphism', file=EV, deps='T016', par='no',
  typ='lemmas', leaves='L3.15–L3.18',
  decls=[(EV,'aeval_X'),(EV,'aeval_toRestricted'),(EV,'norm_aeval_le'),(EV,'continuous_aeval')],
  sketch="""`aeval c x hx f` is definitionally `eval₂ c (algebraMap K B) x _ hx f`.
1. `aeval_X`: `eval₂_X _ hx i`.
2. `aeval_toRestricted`: `(eval₂_toRestricted _ hx p).trans (MvPolynomial.aeval_def x p).symm` (after
   `MvPolynomial.coe_eval₂Hom` if needed).
3. `norm_aeval_le`: `norm_eval₂_le _ hx f`.
4. `continuous_aeval`: `continuous_eval₂ _ hx`.""",
  mathlib="""`MvPolynomial.aeval_def`, `norm_algebraMap'`.""",
  sources="""[BGR] 5.1.3/5, 5.1.4/2; decomposition L3.15–L3.18.""",
  gen="""`B` a Banach `K`-algebra with `NormOneClass` (needed for `algebraMap` to be contractive). Instances of use: `B = L` a complete extension field, `B` a Tate algebra.""")

# ---------------------------------------------------------------- G4 EvalReduction
t(id='T019', title='The map of unit balls is local; evaluation preserves unit balls', file=EVR, deps='CLEANUP-5, CLEANUP-7', par='no',
  typ='instance + lemma', leaves='L4.1, L4.2',
  decls=[(EVR,'(anonymous)'),(EVR,'norm_aeval_le_one')],
  sketch="""1. `IsLocalHom (unitClosedBallMap K L)`: `⟨fun a ha ↦ ?_⟩`; `rw [NormedRing.isUnit_iff_norm_eq_one] at ha ⊢`;
   `coe_unitClosedBallMap` and `norm_algebraMap'` turn `ha` into `‖(a : K)‖ = 1`.
2. `norm_aeval_le_one`: `(norm_aeval_le hx _).trans (Subring.norm_le_one f)`.""",
  mathlib="""`norm_algebraMap'`. Chain: `NormedRing.isUnit_iff_norm_eq_one`, `Subring.norm_le_one`.""",
  sources="""[BGR] 5.1.4, `bgr-5.1.md:257–266`; decomposition L4.1, L4.2.""",
  gen="""`L` any normed field that is a normed `K`-algebra; `B` any Banach `K`-algebra in item 2.""")

t(id='T020', title='Reduction commutes with evaluation at a point', file=EVR, deps='T019', par='no',
  typ='theorem', leaves='L4.3',
  decls=[(EVR,'residue_aeval')],
  sketch="""Private lemma (shared with T021), for any ring `S`:
`ringHom_ext_of_openUnitBall {ψ₁ ψ₂ : unitClosedBall (Restricted K 1) →+* S}
  (h₁ : ∀ f ∈ openUnitBallIdeal _, ψ₁ f = 0) (h₂ : ∀ f ∈ openUnitBallIdeal _, ψ₂ f = 0)
  (h : ∀ p, ψ₁ (ofUnitBallPolynomial p) = ψ₂ (ofUnitBallPolynomial p)) : ψ₁ = ψ₂` —
for `f` take `p` from `exists_sub_ofUnitBallPolynomial_mem_openUnitBallIdeal f` and write
`f = ofUnitBallPolynomial p + (f - ofUnitBallPolynomial p)`.

Then, with `ev : unitClosedBall (Restricted K 1) →+* unitClosedBall L` the restriction of `aeval 1 x hx`
(`RingHom.codRestrict` of `(aeval …).toRingHom.comp (unitClosedBall _).subtype`, membership by
`norm_aeval_le_one`):
1. `ψ₁ := (residue _).comp ev`, `ψ₂ := (MvPolynomial.eval₂Hom (residueFieldMap K L) x̃).comp reduction`,
   where `x̃ i := residue _ ⟨x i, _⟩`. The statement is `RingHom.congr_fun (… : ψ₁ = ψ₂) f` up to proof
   irrelevance in the subtype.
2. `h₁`: `‖aeval x f‖ ≤ ‖f‖ < 1`, so the residue is `0` (`residue_eq_zero_iff`,
   `maximalIdeal_unitClosedBall`). `h₂`: `reduction_eq_zero_iff`.
3. `h`: both sides are ring homomorphisms in `p : MvPolynomial σ (unitClosedBall K)`; `MvPolynomial.ringHom_ext`.
   On `C a`: left is the residue of `algebraMap K L a` (`aeval_toRestricted`, `MvPolynomial.aeval_C`), which
   is `residueFieldMap K L (residue _ a)` by `IsLocalRing.ResidueField.map_residue`; right is the same by
   `reduction_ofUnitBallPolynomial`, `MvPolynomial.map_C`, `MvPolynomial.eval₂_C`. On `X i`: both are `x̃ i`.""",
  mathlib="""`MvPolynomial.ringHom_ext`, `MvPolynomial.eval₂Hom`, `MvPolynomial.aeval_C`, `MvPolynomial.aeval_X`, `MvPolynomial.map_C`, `MvPolynomial.map_X`, `IsLocalRing.ResidueField.map_residue`, `IsLocalRing.residue_eq_zero_iff`, `RingHom.codRestrict`.""",
  sources="""[BGR] 5.1.4, `bgr-5.1.md:257–266`; [Bo] 1.2/5, `bosch-lectures.txt:449–456`; decomposition L4.3.""",
  gen="""`L` any complete nonarchimedean normed extension field of `K` (BGR's `k_a` is not complete; see T025–T027). `K` need not be complete.""")

t(id='T021', title='Reduction commutes with substitution', file=EVR, deps='T020', par='no',
  typ='theorem', leaves='L4.4',
  decls=[(EVR,'reduction_aeval')],
  sketch="""The same argument with target `MvPolynomial τ k`:
`ψ₁ := reduction.comp ev` (`ev` the restriction of `aeval 1 x hx` to unit balls, into the unit ball of
`Restricted K (1 : τ → ℝ)`), `ψ₂ := (MvPolynomial.aeval fun i ↦ reduction ⟨x i, _⟩).toRingHom.comp reduction`.
1. Vanishing on the open unit ball: `norm_aeval_le` and `reduction_eq_zero_iff` on both sides.
2. On polynomials over `K⁰`, `MvPolynomial.ringHom_ext`. On `C a`: private lemma
   `reduction_C (a : unitClosedBall K) : reduction ⟨C 1 (a : K), _⟩ = MvPolynomial.C (residue _ a)`
   (`MvPolynomial.ext`, `coeff_reduction`, `val_C`, `MvPowerSeries.coeff_C`, `MvPolynomial.coeff_C`, split on
   `t = 0`); with `aeval_toRestricted`, `MvPolynomial.aeval_C`, `algebraMap_apply`. On `X i`: `aeval_X`,
   `MvPolynomial.aeval_X`.""",
  mathlib="""`MvPolynomial.ringHom_ext`, `MvPolynomial.aeval_C`, `MvPolynomial.aeval_X`, `MvPolynomial.coeff_C`, `MvPowerSeries.coeff_C`.""",
  sources="""[BGR] `bgr-5.2.md:244` (`(σ(f))~ = σ̃(f̃)`); 5.1.3/7, `bgr-5.1.md:165–166`; decomposition L4.4.""",
  gen="""`K` complete (the target Tate algebra must be complete). Source and target index types `σ`, `τ` independent.""")

# ---------------------------------------------------------------- G5 SupSeminorm
t(id='T022', title='Values at a point; kernels of points', file=SUP, deps='none', par='yes',
  typ='lemmas', leaves='L5.1–L5.4',
  decls=[(SUP,'evalNorm_nonneg'),(SUP,'evalNorm_eq_zero_of_mem'),(SUP,'isMaximal_ker_of_isAlgebraic'),(SUP,'finite_quotient_ker')],
  sketch="""1. `evalNorm_nonneg`: `spectralValue_nonneg _`.
2. `evalNorm_eq_zero_of_mem`: `haveI := x.isMaximal`; `unfold evalNorm`;
   `rw [Ideal.Quotient.eq_zero_iff_mem.2 hf, minpoly.zero]`; `X = X ^ 1` and `spectralValue_X_pow 1`.
3. `isMaximal_ker_of_isAlgebraic`: the quotient `A ⧸ RingHom.ker φ` is isomorphic to `φ.range`
   (`Ideal.quotientKerAlgEquivOfSurjective` for `φ.rangeRestrict`), and `φ.range` is a field by
   `Subalgebra.isField_of_algebraic`; transfer with `MulEquiv.isField` and conclude by
   `Ideal.Quotient.maximal_of_isField`.
4. `finite_quotient_ker`: `FiniteDimensional.of_injective (Ideal.kerLiftAlg φ).toLinearMap (Ideal.kerLiftAlg_injective φ)`.""",
  mathlib="""`spectralValue_nonneg`, `Ideal.Quotient.eq_zero_iff_mem`, `minpoly.zero`, `spectralValue_X_pow`, `Subalgebra.isField_of_algebraic`, `Ideal.quotientKerAlgEquivOfSurjective`, `MulEquiv.isField`, `Ideal.Quotient.maximal_of_isField`, `Ideal.kerLiftAlg`, `Ideal.kerLiftAlg_injective`, `FiniteDimensional.of_injective`.""",
  sources="""[BGR] 3.8.1/1–2, `bgr-3.8.md:18–35`; 5.1.4/6, `bgr-5.1.md:314–321`; `bgr-7.1.1.md:11–12`; decomposition L5.1–L5.4.""",
  gen="""Items 1–2 for a normed field and any commutative `K`-algebra; items 3–4 for abstract fields (no norm). `φ` need not be surjective: an algebraic target makes the range a field.""")

t(id='T023', title='The value at the kernel of a point', file=SUP, deps='T022', par='no',
  typ='theorem', leaves='L5.5',
  decls=[(SUP,'evalNorm_eq_norm_algHom')],
  sketch="""1. `ψ : A ⧸ x.asIdeal →ₐ[K] L := Ideal.Quotient.liftₐ x.asIdeal φ fun a ha ↦ by rw [hx] at ha; exact ha`
   (`RingHom.mem_ker`), with `ψ (Ideal.Quotient.mk _ f) = φ f` (`Ideal.Quotient.liftₐ_apply` / `rfl`).
2. `ψ` is injective: `injective_iff_map_eq_zero`; a class `mk a` with `φ a = 0` has `a ∈ ker φ = x.asIdeal`
   (`Ideal.Quotient.mk_surjective` to pick representatives).
3. `unfold evalNorm`; `rw [← minpoly.algHom_eq ψ hψ]`; the left side is now
   `spectralValue (minpoly K (φ f)) = spectralNorm K L (φ f)` by definition, and
   `(NormedAlgebra.norm_eq_spectralNorm K (φ f)).symm` finishes.""",
  mathlib="""`Ideal.Quotient.liftₐ`, `minpoly.algHom_eq`, `NormedAlgebra.norm_eq_spectralNorm`, `injective_iff_map_eq_zero`, `Ideal.Quotient.mk_surjective`.""",
  sources="""[BGR] 5.1.4/6, `bgr-5.1.md:319–322`; decomposition L5.5.""",
  gen="""`K` complete and nontrivially normed (the hypotheses of the Mathlib lemma: over a complete field the norm of an algebraic normed extension is the spectral norm). `L` need not be finite over `K`.""")

t(id='T024', title='`|f(x)| ≤ ‖f‖` in a Banach algebra', file=SUP, deps='T022', par='no',
  typ='theorem + corollaries', leaves='L5.6–L5.8',
  decls=[(SUP,'evalNorm_le_norm'),(SUP,'bddAbove_range_evalNorm'),(SUP,'supSeminorm_le_norm')],
  sketch="""`evalNorm_le_norm` (Bosch's unit argument). Let `y := Ideal.Quotient.mk x.asIdeal f`, `q := minpoly K y`,
`σ := spectralValue q`; `haveI := x.isMaximal`.
0. If `y` is not integral over `K`: `minpoly.eq_zero`, and `spectralValue 0 = 0` (unfold `spectralValue`,
   `spectralValueTerms`; every term is `0`), so the claim is `0 ≤ ‖f‖`.
1. Otherwise `q` is monic, irreducible (`minpoly.irreducible`; the quotient by a maximal ideal is a field),
   of degree `r ≥ 1` (`minpoly.natDegree_pos`). Suppose `‖f‖ < σ`.
2. `σ ^ r = ‖q.coeff 0‖`: in `AdjoinRoot q` (`Fact (Irreducible q)`), `minpoly K (AdjoinRoot.root q) = q`
   (`AdjoinRoot.minpoly_root`, `q` monic), so `σ = spectralNorm K (AdjoinRoot q) (root q)` and
   `spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow` gives `σ = ‖q.coeff 0‖ ^ (1 / r)`; raise to the `r`.
   In particular `q.coeff 0 ≠ 0`.
3. `‖q.coeff n‖ ≤ σ ^ (r - n)` for `n < r`: `le_ciSup (spectralValueTerms_bddAbove q) n` and
   `spectralValueTerms_of_lt_natDegree`, then raise to the power `r - n` (`Real.rpow_natCast`,
   `Real.rpow_mul`); for `n = r`, `‖1‖ = 1`.
4. `Polynomial.aeval f q = algebraMap K A (q.coeff 0) + w`, `w := ∑ n ∈ Finset.Icc 1 r, q.coeff n • f ^ n`
   (`Polynomial.aeval_eq_sum_range`, split off `n = 0`), and `‖w‖ < σ ^ r`: each term has norm
   `≤ σ ^ (r - n) * ‖f‖ ^ n < σ ^ r` (`norm_smul_le`, `norm_pow_le'`, `pow_lt_pow_left₀`), and a finite sum
   in an ultrametric group is bounded by a strict bound on its terms (take the maximum of finitely many
   terms: `IsUltrametricDist.exists_norm_finsetSum_le`).
5. `Polynomial.aeval f q` is a unit of `A`: it is `c • (1 - u)` with `c := q.coeff 0 ≠ 0`,
   `u := -(c⁻¹ • w)`, `‖u‖ < 1`; `isUnit_one_sub_of_norm_lt_one`.
6. But `Ideal.Quotient.mk _ (aeval f q) = aeval y q = 0` (`Polynomial.aeval_algHom_apply` for
   `Ideal.Quotient.mkₐ K _`, `minpoly.aeval`), so `aeval f q ∈ x.asIdeal`; `Ideal.eq_top_of_isUnit_mem`
   contradicts `x.isMaximal.ne_top`.

`bddAbove_range_evalNorm`: `⟨‖f‖, by rintro _ ⟨x, rfl⟩; exact evalNorm_le_norm x f⟩`.
`supSeminorm_le_norm`: `rcases isEmpty_or_nonempty (MaximalSpectrum A)`; `Real.iSup_of_isEmpty` and
`norm_nonneg`, or `ciSup_le fun x ↦ evalNorm_le_norm x f`.""",
  mathlib="""`minpoly.eq_zero`, `minpoly.irreducible`, `minpoly.monic`, `minpoly.natDegree_pos`, `minpoly.aeval`, `AdjoinRoot.minpoly_root`, `spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow`, `spectralValueTerms_of_lt_natDegree`, `spectralValueTerms_bddAbove`, `le_ciSup`, `Polynomial.aeval_eq_sum_range`, `Polynomial.aeval_algHom_apply`, `IsUltrametricDist.exists_norm_finsetSum_le`, `norm_pow_le'`, `pow_lt_pow_left₀`, `isUnit_one_sub_of_norm_lt_one`, `Ideal.eq_top_of_isUnit_mem`, `Real.iSup_of_isEmpty`, `ciSup_le`.""",
  sources="""[BGR] 3.8.2/1–2, `bgr-3.8.md:122–126`, `:147–152`; [Bo] 1.2/12, `bosch-lectures.txt:655–671`; decomposition L5.6–L5.8.""",
  gen="""Any complete nonarchimedean Banach `K`-algebra; no `NormOneClass`, no power-multiplicativity, no normalisation of `‖f‖`. Steps 2–4 are worth three private lemmas.""")

# ---------------------------------------------------------------- G6 MaxModulus
t(id='T025', title='Roots of unity with distinct residues', file=MM, deps='none', par='yes',
  typ='lemmas', leaves='L6.1, L6.2',
  decls=[(MM,'NormedField.exists_lt_natCast_norm_eq_one'),(MM,'exists_finset_splittingField_X_pow_sub_one')],
  sketch="""1. `NormedField.exists_lt_natCast_norm_eq_one`: `by_cases h : ‖((d + 1 : ℕ) : K)‖ = 1`: take `m = d + 1`.
   Otherwise `‖((d + 1 : ℕ) : K)‖ < 1` (`IsUltrametricDist.norm_natCast_le_one`, `lt_of_le_of_ne`) and
   `m = d + 2`: `Nat.cast_succ`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` with `norm_one`,
   `max_eq_right`.
2. `exists_finset_splittingField_X_pow_sub_one`. Let `P : K[X] := X ^ m - 1`, `L := P.SplittingField`.
   - `(m : K) ≠ 0` from `hmK`; `P` separable: `Polynomial.separable_X_pow_sub_C 1 _ one_ne_zero`
     (`map_one`); `P` splits in `L`; so `Fintype.card (P.rootSet L) = m`
     (`Polynomial.card_rootSet_eq_natDegree`, `Polynomial.natDegree_X_pow_sub_C`). `S := (P.rootSet L).toFinset`.
   - `letI := spectralNorm.normedField K L; letI := spectralNorm.normedAlgebra K L`; now
     `‖z‖ = spectralNorm K L z` (`NormedAlgebra.norm_eq_spectralNorm K z`, or `rfl`), the norm is
     multiplicative and nonarchimedean (`isNonarchimedean_spectralNorm`).
   - For `s ∈ S`: `s ^ m = 1` (`Polynomial.mem_rootSet`, `aeval`), so `‖s‖ ^ m = 1` and `‖s‖ = 1`
     (`pow_eq_one_iff_of_nonneg`).
   - For `s ≠ t` in `S`: `Polynomial.Splits.eval_root_derivative` for `P.map (algebraMap K L)` at `s` gives
     `(m : L) * s ^ (m - 1) = ∏ over the other roots u of (s - u)`; the left side has norm `1`
     (`spectralNorm_extends`, `hmK`); every factor has norm `≤ max ‖s‖ ‖u‖ = 1`; a product of numbers in
     `[0, 1]` equal to `1` has every factor equal to `1` (if one were `< 1` the product would be `< 1`:
     `Finset.prod_le_prod` after isolating that factor).""",
  mathlib="""`IsUltrametricDist.norm_natCast_le_one`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, `Polynomial.separable_X_pow_sub_C`, `Polynomial.SplittingField.splits`, `Polynomial.card_rootSet_eq_natDegree`, `Polynomial.natDegree_X_pow_sub_C`, `Polynomial.Splits.eval_root_derivative`, `Polynomial.derivative_X_pow`, `spectralNorm.normedField`, `spectralNorm.normedAlgebra`, `NormedAlgebra.norm_eq_spectralNorm`, `spectralNorm_extends`, `isNonarchimedean_spectralNorm`, `isPowMul_spectralNorm` (there is no `spectralNorm_pow`).""",
  sources="""[BGR] 5.1.4/3, `bgr-5.1.md:270–285` (the remark on extensions with large residue field); `bgr-3.2.md:76–79`; decomposition L6.1, L6.2, N6.""",
  gen="""Item 1: any nonarchimedean normed field. Item 2: `K` complete and nontrivially normed (for the spectral normed-field structure), in `Type u` so that the splitting field is in the same universe. ⚠ Declared deviation: this replaces BGR's Lemma 3.4.1/4.""")

t(id='T026', title='Maximum modulus at the points of an extension field', file=MM, deps='CLEANUP-5, CLEANUP-8', par='no',
  typ='theorem', leaves='L6.3',
  decls=[(MM,'exists_norm_aeval_eq_norm')],
  sketch="""0. `f = 0`: `rcases isEmpty_or_nonempty σ`. If `σ` is empty, `x := isEmptyElim`. Otherwise `hf 0 (by simp)`
   at any `i` gives `0 < S.card`, so pick `s ∈ S` and `x := fun _ ↦ s`; `map_zero`.
1. `f ≠ 0`: take `a ≠ 0` with `‖a • f‖ = 1` (`exists_norm_smul_eq_one`); `g : unitClosedBall _ := ⟨a • f, _⟩`.
   The indices `t` with `‖coeff t (a • f).1‖ = 1` are those with `‖coeff t f.1‖ = ‖f‖` (`norm_smul_eq`).
2. `q := reduction g ≠ 0` (`reduction_eq_zero_iff`); for `t ∈ q.support`, `‖coeff t g.1.1‖ = 1`, so `t i < S.card`
   by `hf`; hence `q.degreeOf i < S.card` (`MvPolynomial.degreeOf_lt_iff` / `degreeOf_le_iff`).
3. `Q := MvPolynomial.map (NormedField.residueFieldMap K L) q ≠ 0` (`MvPolynomial.map_injective`, a field
   homomorphism is injective) and `Q.degreeOf i ≤ q.degreeOf i` (`MvPolynomial.degrees_map_le`).
4. `S̃ := S.attach.image fun s ↦ residue _ ⟨s, _⟩` has `S.card` elements (`Finset.card_image_of_injOn`): for
   `s ≠ t`, `‖s - t‖ = 1` means `s - t ∉` the maximal ideal, so the residues differ.
5. `MvPolynomial.eq_zero_of_eval_zero_at_prod_finset Q (fun _ ↦ S̃)` contraposed: some `x̃` with `x̃ i ∈ S̃` has
   `MvPolynomial.eval x̃ Q ≠ 0`. Lift `x̃ i` to `x i ∈ S`.
6. `residue_aeval hx g` and `MvPolynomial.eval_map` give `residue ⟨aeval x (a • f), _⟩ = eval x̃ Q ≠ 0`, so
   `‖aeval x (a • f)‖ = 1` (not `< 1`, and `≤ 1` by `norm_aeval_le_one`). Undo the scaling: `map_smul`,
   `norm_smul`, `norm_smul_eq`.""",
  mathlib="""`MvPolynomial.eq_zero_of_eval_zero_at_prod_finset`, `MvPolynomial.map_injective`, `MvPolynomial.degrees_map_le`, `MvPolynomial.degreeOf_le_iff`, `MvPolynomial.eval_map`, `Finset.card_image_of_injOn`, `IsLocalRing.residue_eq_zero_iff`, `RingHom.injective` (field).""",
  sources="""[BGR] 5.1.4/3, `bgr-5.1.md:277–285`; [Bo] 1.2/5, `bosch-lectures.txt:442–456`; decomposition L6.3.""",
  gen="""`K` any nonarchimedean normed field, `L` complete, `σ` finite (the Nullstellensatz lemma). The hypothesis on `S` is the exact count the proof uses, not BGR's "infinite".""")

t(id='T027', title='Maximum modulus on the maximal spectrum', file=MM, deps='T025, T026, CLEANUP-9', par='no',
  typ='theorems', leaves='L6.4, L6.5',
  decls=[(MM,'exists_evalNorm_eq_norm'),(MM,'exists_evalNorm_eq_norm_and_notMem')],
  sketch="""Private lemma `exists_point (f) (hf : f ≠ 0) : ∃ (L : Type u) (_ : NormedField L) (_ : NormedAlgebra K L)
(_ : IsUltrametricDist L) (_ : CompleteSpace L) (_ : FiniteDimensional K L) (x : σ → L) (hx : ∀ i, ‖x i‖ ≤ 1),
‖aeval 1 x hx f‖ = ‖f‖`:
- the set `{t | ‖coeff t f.1‖ = ‖f‖}` is finite (`finite_setOf_le_norm_coeff f (norm_pos_iff.2 hf)`); let `d`
  bound all `t i` on it (`Finset.sup`, `σ` finite);
- `m > d` with `‖(m : K)‖ = 1` and `S` from T025; `L := (X ^ m - 1 : K[X]).SplittingField` with
  `letI := spectralNorm.normedField K L`, `spectralNorm.normedAlgebra K L`,
  `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm isNonarchimedean_spectralNorm`,
  `spectralNorm.completeSpace K L` (the block compiles: `scratch/spot3.lean`, item 4);
- `exists_norm_aeval_eq_norm S … f` (T026).

1. `exists_evalNorm_eq_norm`: for `f ≠ 0` take the point; `φ := aeval 1 x hx`;
   `x₀ := ⟨RingHom.ker φ, isMaximal_ker_of_isAlgebraic φ⟩`; `finite_quotient_ker φ`;
   `evalNorm_eq_norm_algHom φ x₀ rfl f`. For `f = 0` use the point of `1` and `evalNorm_eq_zero_of_mem`.
2. `exists_evalNorm_eq_norm_and_notMem`: for `f ≠ 0` apply the private lemma to `f * g ≠ 0` (domain):
   `‖φ f‖ * ‖φ g‖ = ‖f‖ * ‖g‖` (`map_mul`, `norm_mul` twice), with `‖φ f‖ ≤ ‖f‖`, `‖φ g‖ ≤ ‖g‖`
   (`norm_aeval_le`) and both right sides positive, so both are equalities; then `evalNorm x₀ g = ‖g‖ ≠ 0`
   and `g ∉ x₀` by `evalNorm_eq_zero_of_mem`. For `f = 0` apply item 1 to `g`.""",
  mathlib="""`spectralNorm.normedField`, `spectralNorm.normedAlgebra`, `spectralNorm.completeSpace`, `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`, `isNonarchimedean_spectralNorm`, `Polynomial.IsSplittingField.finiteDimensional`, `Algebra.IsAlgebraic.of_finite`, `Finset.sup`, `Finset.le_sup`.""",
  sources="""[BGR] 5.1.4/6, `bgr-5.1.md:307–323`; 5.1.4/4, `bgr-5.1.md:289–293`; [RM] §0.1.3–§0.1.4; decomposition L6.4, L6.5.""",
  gen="""`K : Type u` complete, nontrivially normed; `σ` finite. The residue field of the point is finite by construction (no Noether normalisation; erratum E4).""")

t(id='T028', title='The Gauss norm is the supremum norm', file=MM, deps='CLEANUP-ALL-1', par='no',
  typ='theorem (milestone M1)', leaves='L6.6, L6.7', milestone='M1',
  decls=[(MM,'supSeminorm_eq_norm'),(MM,'eq_zero_of_forall_mem')],
  sketch="""1. `supSeminorm_eq_norm`: `le_antisymm (supSeminorm_le_norm f) ?_`; `obtain ⟨x, -, hx⟩ := exists_evalNorm_eq_norm f`;
   `hx ▸ le_ciSup (bddAbove_range_evalNorm f) x`. The Banach-algebra instances on `Restricted K 1` are the
   floor's (`NormedCommRing`, `IsUltrametricDist`, `CompleteSpace`) and T003's `NormedAlgebra`.
2. `eq_zero_of_forall_mem`: `obtain ⟨x, -, hx⟩ := exists_evalNorm_eq_norm f`;
   `norm_eq_zero.1 (hx ▸ evalNorm_eq_zero_of_mem K (hf x))`.""",
  mathlib="""`le_ciSup`, `norm_eq_zero`.""",
  sources="""[BGR] 5.1.4/5–6, `bgr-5.1.md:295–300`, `:307–311`; [RM] §0.1.4; decomposition L6.6, L6.7.""",
  gen="""Milestone M1. Stated for `Restricted K (1 : σ → ℝ)` with `σ` finite, which covers `TateAlgebra K n`.""")

# ---------------------------------------------------------------- G7 Distinguished
t(id='T029', title='The coefficients in `X 0`', file=DIST, deps='CLEANUP-2', par='yes (with G2–G6)',
  typ='lemmas', leaves='L7.1–L7.5',
  decls=[(DIST,'coeffX0_add'),(DIST,'coeffX0_smul'),(DIST,'norm_coeffX0_le'),(DIST,'norm_le_iff_forall_norm_coeffX0_le'),(DIST,'tendsto_norm_coeffX0')],
  sketch="""The seam is crossed only through `coeff_coeffX0` (Tower):
`coeff t (coeffX0 g ν).1 = coeff (Finsupp.cons ν t) g.1`.
1. `coeffX0_add`, `coeffX0_smul`: `Restricted.ext (MvPowerSeries.ext fun t ↦ ?_)`; `coeff_coeffX0` on each
   side; `val_add`, `map_add` (resp. `val_smul`, `MvPowerSeries.coeff_smul`).
2. `norm_coeffX0_le`: `(norm_le_iff_forall_norm_coeff_le _).2 fun t ↦ ?_`; `coeff_coeffX0`; `norm_coeff_le g _`.
3. `norm_le_iff_forall_norm_coeffX0_le`: `→`: item 2 and transitivity. `←`:
   `(norm_le_iff_forall_norm_coeff_le g).2 fun t ↦ ?_`; rewrite `t` as
   `Finsupp.cons (t 0) (Finsupp.tail t)` (`Finsupp.cons_tail`), then `← coeff_coeffX0` and
   `(norm_coeff_le _ _).trans (h (t 0))`.
4. `tendsto_norm_coeffX0`: `Metric.tendsto_atTop`; for `ε > 0` the set `{t | ε ≤ ‖coeff t g.1‖}` is finite
   (`finite_setOf_le_norm_coeff`); let `N` be the supremum of `t 0` over it; for `ν > N` every coefficient of
   `coeffX0 g ν` has norm `< ε` (`coeff_coeffX0`, `Finsupp.cons_zero`), so `‖coeffX0 g ν‖ < ε` by
   `norm_lt_iff_forall_norm_coeff_lt`. Do **not** go through the floor's `(finSuccEquiv …).2`.""",
  mathlib="""`MvPowerSeries.ext`, `MvPowerSeries.coeff_smul`, `Finsupp.cons_tail`, `Finsupp.cons_zero`, `Metric.tendsto_atTop`, `Finset.sup`, `Finset.le_sup`. Tower: `coeff_coeffX0`.""",
  sources="""[BGR] 5.1.1, `bgr-5.1.md:24` (`Tₙ = Tₙ₋₁⟨Xₙ⟩`); `bgr-5.2.md:175`; decomposition L7.1–L7.5.""",
  gen="""Any normed field; no completeness.""")

t(id='T030', title='Polynomials in `X 0` inside the Tate algebra', file=DIST, deps='T029', par='no',
  typ='lemmas', leaves='L7.6–L7.11',
  decls=[(DIST,'ofTail_injective'),(DIST,'ofPolynomial_X'),(DIST,'ofTail_X'),(DIST,'ofTail_C'),(DIST,'norm_ofPolynomial_le_iff'),(DIST,'norm_ofTail')],
  sketch="""1. `ofTail_injective`: `ofPolynomial_injective.comp Polynomial.C_injective`.
2. `ofPolynomial_X`, `ofTail_X`, `ofTail_C`: `Restricted.ext (MvPowerSeries.ext fun t ↦ ?_)`;
   `coeff_ofPolynomial` (Tower) on the left; `Polynomial.coeff_X`, `Polynomial.coeff_C` for the polynomial
   coefficient; `val_X`, `val_C`, `val_one`, `MvPowerSeries.coeff_X`, `coeff_C`, `coeff_one` on both sides. The
   index facts are: `t = Finsupp.single 0 1 ↔ t 0 = 1 ∧ Finsupp.tail t = 0`,
   `t = Finsupp.single i.succ 1 ↔ t 0 = 0 ∧ Finsupp.tail t = Finsupp.single i 1`,
   `t = 0 ↔ t 0 = 0 ∧ Finsupp.tail t = 0`; prove them once as private lemmas from `Finsupp.cons_tail`
   (`Finsupp.ext`, `Fin.cases`).
3. `norm_ofPolynomial_le_iff`: `(norm_le_iff_forall_norm_coeffX0_le _).trans` and
   `simp only [coeffX0_ofPolynomial]`.
4. `norm_ofTail`: `le_antisymm`; `≤` by item 3 with `Polynomial.coeff_C` (split on `i = 0`); `≥` by
   `norm_coeffX0_le (ofTail K n f) 0` and `coeffX0_ofPolynomial`, `Polynomial.coeff_C_zero`.""",
  mathlib="""`Polynomial.C_injective`, `Polynomial.coeff_X`, `Polynomial.coeff_C`, `Polynomial.coeff_C_zero`, `MvPowerSeries.coeff_X`, `MvPowerSeries.coeff_C`, `Finsupp.cons_tail`, `Finsupp.tail_cons`, `Finsupp.cons_zero`. Tower: `coeff_ofPolynomial`, `coeffX0_ofPolynomial`, `ofPolynomial_injective`.""",
  sources="""[BGR] 5.2.3/3, `bgr-5.2.md:144–147`, `:175`; decomposition L7.6–L7.11.""",
  gen="""The three value lemmas are `@[simp]`. `n = 0` makes `ofTail_X` vacuous.""")

t(id='T031', title='Distinguished series: nonzero, scalars, order zero', file=DIST, deps='T029, CLEANUP-4', par='no',
  typ='lemmas', leaves='L7.12–L7.14',
  decls=[(DIST,'ne_zero_of_isMulDistinguishedX0'),(DIST,'isMulDistinguishedX0_smul_iff'),(DIST,'isMulDistinguishedX0_zero_iff')],
  sketch="""All three go through `isMulDistinguishedX0_iff` (Tower).
1. `ne_zero_of_isMulDistinguishedX0`: `rintro rfl`; the first component says `coeffX0 0 s` is a unit; it is
   `0` (`Restricted.ext`, `coeff_coeffX0`, `val_zero`), contradicting `not_isUnit_zero`.
2. `isMulDistinguishedX0_smul_iff`: rewrite both sides; `coeffX0_smul`, `norm_smul_eq` (cancel `‖a‖ > 0`
   with `mul_lt_mul_left`, `mul_right_inj'`); for units, `a • h = C 1 a * h` (`Algebra.smul_def`,
   `algebraMap_apply`) and `IsUnit.mul_iff` with `C 1 a` a unit.
3. `isMulDistinguishedX0_zero_iff`: with `g₀ := coeffX0 g 0`, `coeff 0 g₀.1 = coeff 0 g.1`
   (`coeff_coeffX0`, `Finsupp.cons_zero_zero`).
   - `→`: `isUnit_iff_norm_coeff_lt` for `g₀` gives `coeff 0 ≠ 0` and dominance inside `g₀`, whence
     `‖g₀‖ = ‖coeff 0 g.1‖` (`exists_norm_coeff_eq`). For `t ≠ 0`: if `t 0 = 0`, `coeff t g.1` is a nonconstant
     coefficient of `g₀`; if `t 0 > 0`, `‖coeff t g.1‖ ≤ ‖coeffX0 g (t 0)‖ < ‖g₀‖`. Conclude by
     `isUnit_iff_norm_coeff_lt` for `g`.
   - `←`: from `isUnit_iff_norm_coeff_lt` for `g`: `g₀` is a unit (its constant coefficient dominates its
     other coefficients), `‖g₀‖ = ‖coeff 0 g.1‖ = ‖g‖`, and for `ν > 0` every coefficient of `coeffX0 g ν` is a
     coefficient of `g` at an index `≠ 0`, so `‖coeffX0 g ν‖ < ‖g₀‖` by `norm_lt_iff_forall_norm_coeff_lt`.""",
  mathlib="""`not_isUnit_zero`, `IsUnit.mul_iff`, `Algebra.smul_def`, `mul_lt_mul_left`, `Finsupp.cons_zero_zero`, `Finsupp.cons_ne_zero_iff`. Tower: `isMulDistinguishedX0_iff`, `coeff_coeffX0`.""",
  sources="""[BGR] 5.2.1/1, `bgr-5.2.md:29–33`, `:57`; [Bo] `bosch-lectures.txt:477–478`; decomposition L7.12–L7.14.""",
  gen="""Completeness only in item 3 (both directions use the unit criterion).""")

t(id='T032', title='Distinguishedness is read off the reduction', file=DIST, deps='CLEANUP-11', par='no',
  typ='lemmas', leaves='L7.15, L7.16',
  decls=[(DIST,'coeff_finSuccEquiv_reduction'),(DIST,'isMulDistinguishedX0_iff_reduction')],
  sketch="""1. `coeff_finSuccEquiv_reduction`: `MvPolynomial.ext _ _ fun t ↦ ?_`;
   `MvPolynomial.finSuccEquiv_coeff_coeff`, `coeff_reduction` on both sides; the two elements of `K⁰` agree
   by `Subtype.ext` and `coeff_coeffX0`.
2. `isMulDistinguishedX0_iff_reduction`. Let `P := finSuccEquiv _ n (reduction g)` and
   `g_ν := ⟨coeffX0 g ν, _⟩ ∈ T⁰`, so `P.coeff ν = reduction g_ν` (item 1). Rewrite the left side with
   `isMulDistinguishedX0_iff` and `hg`.
   - `→`: `‖coeffX0 g s‖ = 1`, `coeffX0 g s` a unit, `‖coeffX0 g ν‖ < 1` for `ν > s`. Then `P.coeff ν = 0`
     for `ν > s` (`reduction_eq_zero_iff`), `P.coeff s` is a unit (`isUnit_coe_iff_isUnit_reduction`), in
     particular nonzero: `P.natDegree = s` (`Polynomial.natDegree_le_iff_coeff_eq_zero`, `le_natDegree_of_ne_zero`)
     and `P.leadingCoeff = P.coeff s`.
   - `←`: `P.leadingCoeff = P.coeff s = reduction g_s` is a unit, hence nonzero: `‖coeffX0 g s‖ = 1`
     (`norm_eq_one_of_reduction_ne_zero`), `coeffX0 g s` is a unit (`isUnit_coe_iff_isUnit_reduction`), and
     for `ν > s`, `P.coeff ν = 0` (`Polynomial.coeff_eq_zero_of_natDegree_lt`) gives `‖coeffX0 g ν‖ < 1`.""",
  mathlib="""`MvPolynomial.finSuccEquiv_coeff_coeff`, `Polynomial.natDegree_le_iff_coeff_eq_zero`, `Polynomial.le_natDegree_of_ne_zero`, `Polynomial.coeff_eq_zero_of_natDegree_lt`, `Polynomial.leadingCoeff`.""",
  sources="""[BGR] 5.2.1, `bgr-5.2.md:35–38`; [Bo] 1.2/6, `bosch-lectures.txt:469–477`; decomposition L7.15, L7.16.""",
  gen="""`‖g‖ = 1` and completeness are both necessary. "Unitary of degree `s`" is `natDegree = s ∧ IsUnit leadingCoeff`; the junk case (zero reduction) cannot occur and is false on both sides.""")

t(id='T033', title='Weierstrass polynomials', file=DIST, deps='T030', par='no',
  typ='lemmas', leaves='L7.17–L7.21',
  decls=[(DIST,'isWeierstrassPolynomial_iff'),(DIST,'isWeierstrassPolynomial_X_pow'),(DIST,'IsWeierstrassPolynomial.of_mul_left'),(DIST,'IsWeierstrassPolynomial.of_mul_right'),(DIST,'IsWeierstrassPolynomial.isMulDistinguishedX0')],
  sketch="""Private helper: `one_le_norm_ofPolynomial (h : ω.Monic) : 1 ≤ ‖ofPolynomial K n ω‖` — from
`norm_coeffX0_le (ofPolynomial K n ω) ω.natDegree`, `coeffX0_ofPolynomial`, `h.coeff_natDegree`, `norm_one`.
1. `isWeierstrassPolynomial_iff`: `→`: `⟨h.monic, (norm_ofPolynomial_le_iff ω).1 h.norm_eq_one.le⟩`. `←`:
   `⟨hm, le_antisymm ((norm_ofPolynomial_le_iff ω).2 hc) (helper hm)⟩`.
2. `isWeierstrassPolynomial_X_pow`: item 1, `Polynomial.monic_X_pow`, `Polynomial.coeff_X_pow` (split the
   `if`; `norm_one`, `norm_zero`).
3. `of_mul_left`, `of_mul_right`: `a := ‖ofPolynomial K n ω₁‖`, `b := ‖ofPolynomial K n ω₂‖`;
   `a * b = 1` (`map_mul`, `norm_mul`, `h.norm_eq_one`), `1 ≤ a`, `1 ≤ b` (helper); then `a = 1` because
   `a ≤ a * b` (`le_mul_of_one_le_right`), and symmetrically.
4. `IsWeierstrassPolynomial.isMulDistinguishedX0`: `isMulDistinguishedX0_iff.2 ⟨?_, ?_, ?_⟩` with
   `coeffX0_ofPolynomial`: the coefficient at `natDegree` is `1` (`isUnit_one`, `norm_one`, `hω.norm_eq_one`);
   later coefficients vanish (`Polynomial.coeff_eq_zero_of_natDegree_lt`, `norm_zero`, `zero_lt_one`).""",
  mathlib="""`Polynomial.Monic.coeff_natDegree`, `Polynomial.monic_X_pow`, `Polynomial.coeff_X_pow`, `Polynomial.coeff_eq_zero_of_natDegree_lt`, `le_mul_of_one_le_right`, `norm_mul`.""",
  sources="""[BGR] 5.2.3/1–2, `bgr-5.2.md:122–131`; 5.2.2/1, `bgr-5.2.md:96–99`; decomposition L7.17–L7.21.""",
  gen="""BGR's definition (monic of Gauss norm one), **not** the roadmap's "non-leading coefficients of norm `< 1`" (erratum E1). `of_mul` (the pair) is already assembled in the skeleton. No completeness.""")

t(id='T034', title='Weierstrass preparation on Weierstrass polynomials', file=DIST, deps='T032, T033', par='no',
  typ='theorems', leaves='L7.22, L7.23',
  decls=[(DIST,'exists_isWeierstrassPolynomial_of_isMulDistinguishedX0'),(DIST,'IsWeierstrassPolynomial.eq_of_mul_eq_mul')],
  sketch="""1. `exists_isWeierstrassPolynomial_of_isMulDistinguishedX0`:
   `obtain ⟨ω, e, hm, hd, hn, he, hge⟩ := weierstrassPreparation_exists hg`;
   `exact ⟨ω, he.unit, ⟨hm, hn⟩, Polynomial.natDegree_eq_of_degree_eq_some hd, by simpa using hge⟩`.
2. `IsWeierstrassPolynomial.eq_of_mul_eq_mul`. Put `u := e₁⁻¹ * e₂`, so
   `ofPolynomial K n ω₁ = u * ofPolynomial K n ω₂`, and `sᵢ := ωᵢ.natDegree`.
   - `s₁ = s₂`: `‖u‖ = 1` (`norm_mul`, both polynomials of norm one). In `T⁰`:
     `⟨ofPolynomial ω₁, _⟩ = ⟨u, _⟩ * ⟨ofPolynomial ω₂, _⟩`, so the reductions satisfy `r₁ = ũ * r₂` with `ũ`
     a unit (`isUnit_coe_iff_isUnit_reduction`). Apply `MvPolynomial.finSuccEquiv`: `P₁ = U * P₂`, `U` a unit
     of a polynomial ring over a domain, so `U.natDegree = 0` (`Polynomial.natDegree_eq_zero_of_isUnit`) and
     `P₁.natDegree = P₂.natDegree` (`Polynomial.natDegree_mul`). By T032 (`→`) applied to the distinguished
     series `ofPolynomial ωᵢ` (T033), `Pᵢ.natDegree = sᵢ`.
   - `weierstrassPreparation_omega_unique (h₁.isMulDistinguishedX0) h₁.monic _ isUnit_one (one_mul _).symm
     h₂.monic _ u.isUnit ‹_›`, the degree arguments from `Polynomial.degree_eq_natDegree` and `s₁ = s₂`.
   Alternative for the degree step: Euclidean division of `ω₁` by `ω₂` and the floor's
   `weierstrassDivision_polynomial_of_isMulDistinguishedX0`.""",
  mathlib="""`Polynomial.natDegree_eq_of_degree_eq_some`, `Polynomial.degree_eq_natDegree`, `Polynomial.natDegree_mul`, `Polynomial.natDegree_eq_zero_of_isUnit`, `IsUnit.unit`. Tower: `weierstrassPreparation_exists`, `weierstrassPreparation_omega_unique`.""",
  sources="""[BGR] 5.2.2/1, `bgr-5.2.md:96–116`, `:133–134`; [Bo] 1.2/9, `bosch-lectures.txt:584–605`; decomposition L7.22, L7.23.""",
  gen="""`K` complete. Item 2 is stronger than BGR's uniqueness (the degrees are not assumed equal); the extra step is the reduction argument.""")

# ---------------------------------------------------------------- G8 Finiteness
t(id='T035', title='Remainders modulo a Weierstrass polynomial', file=FIN, deps='CLEANUP-12', par='no',
  typ='theorems', leaves='L8.1, L8.2',
  decls=[(FIN,'IsWeierstrassPolynomial.existsUnique_remainder'),(FIN,'IsWeierstrassPolynomial.bijective_quotientMap')],
  sketch="""Let `g := ofPolynomial K n ω`, `s := ω.natDegree`, `hg := hω.isMulDistinguishedX0`, and
`ω.degree = s` (`Polynomial.degree_eq_natDegree hω.monic.ne_zero`).
1. `existsUnique_remainder`: existence — `obtain ⟨q, r, hr, hf⟩ := weierstrassDivision_exists hg f`;
   `f - ofPolynomial K n r = q * g` gives membership (`Ideal.mem_span_singleton'`). Uniqueness — from
   `f - ofPolynomial K n rᵢ = qᵢ * g` rebuild `f = g * qᵢ + ofPolynomial K n rᵢ` and apply
   `weierstrassDivision_r_unique hg`.
2. `bijective_quotientMap`. Note `(Ideal.span {ω}).map (ofPolynomial K n) = Ideal.span {g}`
   (`Ideal.map_span`, `Set.image_singleton`).
   - Surjective: `Ideal.Quotient.mk_surjective` gives `f`; take its remainder `r`; the image of the class of
     `r` is the class of `ofPolynomial K n r`, equal to that of `f` (`Ideal.Quotient.eq`).
   - Injective: `injective_iff_map_eq_zero`; for a class `mk p` mapping to `0`, `ofPolynomial K n p ∈ span {g}`.
     Write `p = ω * (p /ₘ ω) + p %ₘ ω` (`Polynomial.modByMonic_add_div`), `r₀ := p %ₘ ω`,
     `r₀.degree < ω.degree` (`Polynomial.degree_modByMonic_lt`). Then `ofPolynomial K n r₀ ∈ span {g}`, so both
     `r₀` and `0` are remainders of `f := ofPolynomial K n r₀`; by item 1, `r₀ = 0`, hence `p ∈ span {ω}`.""",
  mathlib="""`Ideal.mem_span_singleton'`, `Ideal.map_span`, `Set.image_singleton`, `Ideal.Quotient.mk_surjective`, `Ideal.Quotient.eq`, `Ideal.Quotient.eq_zero_iff_mem`, `injective_iff_map_eq_zero`, `Polynomial.modByMonic_add_div`, `Polynomial.degree_modByMonic_lt`, `Polynomial.degree_eq_natDegree`, `Ideal.quotientMap_mk`. Tower: `weierstrassDivision_exists`, `weierstrassDivision_r_unique`.""",
  sources="""[BGR] 5.2.3/3, `bgr-5.2.md:137–140`, `:164–168`; [Bo] `bosch-lectures.txt:696–703`; decomposition L8.1, L8.2.""",
  gen="""`bijective_quotientMap` is stated in the exact shape of axiom (2) of `IsRueckert`. The isometry part of BGR 5.2.3/3 is not needed in Layer 0 and is not stated.""")

t(id='T036', title='`Tₙ → T_{n+1} ⧸ (ω)` is finite, and injective in positive degree', file=FIN, deps='T035', par='no',
  typ='theorems', leaves='L8.3, L8.4',
  decls=[(FIN,'IsWeierstrassPolynomial.finite_mk_comp_ofTail'),(FIN,'IsWeierstrassPolynomial.injective_mk_comp_ofTail')],
  sketch="""1. `finite_mk_comp_ofTail`: the map factors as
   `Tₙ →[C] Tₙ[X] →[mk] Tₙ[X] ⧸ span {ω} →[quotientMap] T_{n+1} ⧸ (span {ω}).map (ofPolynomial K n)
   →[Ideal.quotEquivOfEq] T_{n+1} ⧸ span {ofPolynomial K n ω}`. The first composite `mk ∘ C` is finite: it is
   the `algebraMap` of `Polynomial.Monic.finite_quotient hω.monic` (`RingHom.Finite` unfolds to
   `Module.Finite` for `toAlgebra`; use `RingHom.finite_algebraMap`). The last two are surjective
   (`bijective_quotientMap`, an equivalence), hence finite (`RingHom.Finite.of_surjective`). Compose with
   `RingHom.Finite.comp` and identify the composite with the statement's map by `RingHom.ext`
   (`Ideal.quotientMap_mk`, `Ideal.quotEquivOfEq_mk`, `ofTail`).
2. `injective_mk_comp_ofTail`: `injective_iff_map_eq_zero`; if `ofTail K n a ∈ span {ofPolynomial K n ω}`, then
   for `f := ofTail K n a = ofPolynomial K n (Polynomial.C a)` both `Polynomial.C a` (degree `≤ 0 < ω.degree`
   by `hdeg`, `Polynomial.degree_C_le`) and `0` are remainders; uniqueness gives `C a = 0`, so `a = 0`.""",
  mathlib="""`Polynomial.Monic.finite_quotient`, `RingHom.finite_algebraMap`, `RingHom.Finite.of_surjective`, `RingHom.Finite.comp`, `Ideal.quotEquivOfEq`, `Ideal.quotEquivOfEq_mk`, `Ideal.quotientMap_mk`, `Polynomial.degree_C_le`, `Polynomial.C_eq_zero`.""",
  sources="""[BGR] 5.2.3/4, `bgr-5.2.md:185–187`; decomposition L8.3, L8.4.""",
  gen="""Injectivity needs `0 < ω.natDegree` (for `ω = 1` the target is the zero ring); BGR's "monomorphism" assumes it silently.""")

t(id='T037', title='The Weierstrass finiteness theorem', file=FIN, deps='T036', par='no',
  typ='theorems', leaves='L8.5–L8.7',
  decls=[(FIN,'IsWeierstrassPolynomial.finite_comp_ofTail'),(FIN,'finite_mk_comp_ofTail_of_isMulDistinguishedX0'),(FIN,'IsWeierstrassPolynomial.finite_compHom')],
  sketch="""1. `finite_comp_ofTail`: `φ̄ := Ideal.Quotient.lift (Ideal.span {ofPolynomial K n ω}) φ ?_` (the ideal is
   in the kernel by `h0`: `Ideal.span_le`/`Ideal.mem_span_singleton'`), `φ = φ̄.comp (Ideal.Quotient.mk _)`
   (`Ideal.Quotient.lift_comp_mk`). `φ̄` is finite by `RingHom.Finite.of_comp_finite`; the map of T036 is
   finite; `RingHom.Finite.comp`, and `φ.comp (ofTail K n) = φ̄.comp ((Ideal.Quotient.mk _).comp (ofTail K n))`
   by `RingHom.ext`.
2. `finite_mk_comp_ofTail_of_isMulDistinguishedX0`: `obtain ⟨ω, e, hω, -, hge⟩ := exists_isWeierstrassPolynomial…`;
   apply item 1 to `φ := Ideal.Quotient.mk (Ideal.span {g})` (finite: surjective) with
   `h0 : mk (ofPolynomial K n ω) = 0` because `ofPolynomial K n ω = e⁻¹ * g ∈ span {g}`.
3. `finite_compHom`: `letI := Module.compHom M (ofTail K n)`. From generators `m₁, …, m_k` of `M` over
   `T_{n+1}` (`Module.Finite.fg_top`), the finite family `X 0 ^ i • m_j` (`i < ω.natDegree`) spans `M` over
   `Tₙ`: for `f` and `m_j`, `f = ofPolynomial ω * q + ofPolynomial r` (division), `ofPolynomial ω • m_j = 0`
   by `h`, and `ofPolynomial r • m_j = ∑ i ∈ range s, ofTail (r.coeff i) • (X 0 ^ i • m_j)`
   (`Polynomial.as_sum_range'`, `map_sum`, `ofPolynomial_X`). Conclude with `Module.Finite.of_fg` /
   `Submodule.fg_def` over the image finset.""",
  mathlib="""`Ideal.Quotient.lift`, `Ideal.Quotient.lift_comp_mk`, `RingHom.Finite.of_comp_finite`, `RingHom.Finite.comp`, `RingHom.Finite.of_surjective`, `Module.Finite.fg_top`, `Polynomial.as_sum_range'`, `Submodule.fg_def`.""",
  sources="""[BGR] 5.2.3/4, `bgr-5.2.md:183–201`; [Bo] 1.2/10, `bosch-lectures.txt:618–626`; [RM] §0.2.2; decomposition L8.5–L8.7.""",
  gen="""`A` is any commutative ring (BGR's Banach structure on `A` is not used). The module form is the roadmap's; explicit generators avoid a scalar-tower detour.""")

# ---------------------------------------------------------------- G9 Chart
t(id='T038', title='The shear of a polynomial ring', file=CH, deps='none', par='yes',
  typ='lemmas', leaves='L9.1–L9.3',
  decls=[(CH,'shearAlgHom_comp_shearAlgHom',0),(CH,'shear_X_zero',0),(CH,'shear_X_succ',0)],
  sketch="""1. `shearAlgHom_comp_shearAlgHom`: `MvPolynomial.algHom_ext fun j ↦ ?_`; `Fin.cases` on `j`.
   `j = 0`: `AlgHom.comp_apply`, `shearAlgHom`, `MvPolynomial.aeval_X`, `Fin.cases_zero` twice. `j = i.succ`:
   `aeval_X`, `Fin.cases_succ`, then `map_add`, `map_mul`, `map_pow`, `MvPolynomial.aeval_C`
   (`algebraMap = C`), `aeval_X`; the result is `X i.succ + C a * X 0 ^ e i + C b * X 0 ^ e i`; collect with
   `← add_mul`, `← map_add`, `hab`, `map_zero`, `zero_mul`, `add_zero`.
2. `shear_X_zero`, `shear_X_succ`: the coercion of `AlgEquiv.ofAlgHom` is `shearAlgHom R e 1` (`rfl`);
   `MvPolynomial.aeval_X`, `Fin.cases_zero` / `Fin.cases_succ`, `map_one`, `one_mul`.""",
  mathlib="""`MvPolynomial.algHom_ext`, `MvPolynomial.aeval_X`, `MvPolynomial.aeval_C`, `Fin.cases_zero`, `Fin.cases_succ`, `AlgEquiv.ofAlgHom`.""",
  sources="""[BGR] 5.1.3, Example, `bgr-5.1.md:198–204`; decomposition L9.1–L9.3.""",
  gen="""Any commutative ring and any exponents. The parametrised `shearAlgHom R e a` exists so that the inverse (`a = -1`) is the same definition.""")

t(id='T039', title='Degree and leading coefficient of a sheared monomial', file=CH, deps='T038', par='no',
  typ='lemmas', leaves='L9.4–L9.6',
  decls=[(CH,'sum_pow_mul_ne_of_lt'),(CH,'degreeOf_zero_shear_monomial'),(CH,'leadingCoeff_finSuccEquiv_shear_monomial')],
  sketch="""1. `sum_pow_mul_ne_of_lt`: prove the contrapositive for functions by induction on `n`, generalising `v w`:
   `∀ v w : Fin (n + 1) → ℕ, (∀ i, v i < t) → (∀ i, w i < t) → ∑ i, t ^ i.val * v i = ∑ i, t ^ i.val * w i → v = w`.
   `Fin.sum_univ_succ` gives `v 0 + t * ∑ i : Fin n, t ^ i.val * v i.succ` (`pow_succ`, `Finset.mul_sum`);
   reducing modulo `t` (`Nat.add_mul_mod_self_left`, `Nat.mod_eq_of_lt`) gives `v 0 = w 0`; cancel
   (`Nat.eq_of_mul_eq_mul_left`, `0 < t` from `hv 0`) and apply the induction hypothesis to the tails;
   `Fin.cases` to conclude. Transfer to `Finsupp` with `DFunLike.ext`.
2. Private product formula, for `e : Fin n → ℕ`, `v`, `a : k`:
   `finSuccEquiv k n (shear k e (monomial v a)) =
     Polynomial.C (C a) * Polynomial.X ^ v 0 * ∏ i : Fin n, (Polynomial.C (X i) + Polynomial.X ^ e i) ^ v i.succ`
   — `MvPolynomial.monomial_eq`, `Finsupp.prod_fintype`, `Fin.prod_univ_succ`, then `map_mul`, `map_prod`,
   `map_pow`, `shear_X_zero`, `shear_X_succ`, `AlgEquiv.commutes`, and `finSuccEquiv_X_zero`,
   `finSuccEquiv_X_succ`, `finSuccEquiv` on constants.
3. `degreeOf_zero_shear_monomial`: `← MvPolynomial.natDegree_finSuccEquiv`, the formula,
   `Polynomial.natDegree_mul`, `natDegree_C`, `natDegree_X_pow`, `Polynomial.natDegree_prod`, `natDegree_pow`,
   and `(C (X i) + X ^ e i).natDegree = e i` (`add_comm`, `Polynomial.natDegree_X_pow_add_C`). All factors are
   nonzero (`a ≠ 0`; `X ^ e + C b` is monic for `e > 0` and is `C (1 + X i) ≠ 0` for `e = 0`).
4. `leadingCoeff_finSuccEquiv_shear_monomial`: the formula, `Polynomial.leadingCoeff_mul`, `leadingCoeff_C`,
   `leadingCoeff_X_pow`, `Polynomial.leadingCoeff_prod`, `leadingCoeff_pow`,
   `Polynomial.leadingCoeff_X_pow_add_C (he i)`. (For `a = 0` both sides are `0`.)""",
  mathlib="""`Fin.sum_univ_succ`, `Fin.prod_univ_succ`, `Nat.add_mul_mod_self_left`, `Nat.mod_eq_of_lt`, `Nat.eq_of_mul_eq_mul_left`, `MvPolynomial.monomial_eq`, `Finsupp.prod_fintype`, `MvPolynomial.finSuccEquiv_X_zero`, `MvPolynomial.finSuccEquiv_X_succ`, `MvPolynomial.natDegree_finSuccEquiv`, `Polynomial.natDegree_mul`, `Polynomial.natDegree_prod`, `Polynomial.natDegree_X_pow_add_C`, `Polynomial.leadingCoeff_mul`, `Polynomial.leadingCoeff_prod`, `Polynomial.leadingCoeff_X_pow_add_C`. (`Nat.ofDigits_inj_of_len_eq` is an alternative for item 1.)""",
  sources="""[Bo] 1.2/7, `bosch-lectures.txt:505–527`; [BGR] 5.2.4/1, `bgr-5.2.md:242–254`; decomposition L9.4–L9.6.""",
  gen="""Strict bound `v i < t` (Bosch), so that base-`t` expansions are unique. The leading-coefficient lemma needs `0 < e i` (defect D1); the degree lemma does not.""")

t(id='T040', title='The shear makes the leading coefficient a unit', file=CH, deps='T039', par='no',
  typ='theorem', leaves='L9.7',
  decls=[(CH,'isUnit_leadingCoeff_finSuccEquiv_shear')],
  sketch="""Let `e i := t ^ (i.val + 1)` (positive: `0 < t` since `f.support` is nonempty and `ht`), and
`D v := ∑ j : Fin (n + 1), t ^ j.val * v j`; by `Fin.sum_univ_succ`, `D v = v 0 + ∑ i, e i * v i.succ`
(`pow_zero`, `one_mul`, `mul_comm`), the degree of T039.
1. `f = ∑ v ∈ f.support, monomial v (f.coeff v)` (`MvPolynomial.as_sum`); apply `shear` and `finSuccEquiv`
   (`map_sum`): `P = ∑ v ∈ f.support, P_v`, `P_v.natDegree = D v` and `P_v.leadingCoeff = C (f.coeff v)`
   (T039; `f.coeff v ≠ 0` on the support).
2. `obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image f.support D (MvPolynomial.support_nonempty.2 hf)`; for
   `v ≠ m` in the support, `D v < D m` (`hmax` and `sum_pow_mul_ne_of_lt`).
3. `Finset.sum_eq_add_sum_sdiff_singleton_of_mem` (or `Finset.add_sum_erase`): `P = P_m + R` with
   `R.degree < P_m.degree` (`Polynomial.degree_sum_le`, `Finset.sup_lt_iff`, `Polynomial.degree_eq_natDegree`);
   `Polynomial.leadingCoeff_add_of_degree_lt'` (the form for the larger summand first) gives
   `P.leadingCoeff = C (f.coeff m)`, a unit (`IsUnit.map`, `isUnit_iff_ne_zero`).""",
  mathlib="""`MvPolynomial.as_sum`, `MvPolynomial.support_nonempty`, `Finset.exists_max_image`, `Finset.add_sum_erase`, `Polynomial.degree_sum_le`, `Polynomial.leadingCoeff_add_of_degree_lt`, `Polynomial.leadingCoeff_add_of_degree_lt'`, `IsUnit.map`, `isUnit_iff_ne_zero`.""",
  sources="""[Bo] 1.2/7, `bosch-lectures.txt:498–528`; [BGR] 5.2.4/1, `bgr-5.2.md:249–254`; decomposition L9.7.""",
  gen="""A field `k` (the residue field). `n = 0` is the statement that a nonzero one-variable polynomial has a unit leading coefficient.""")

t(id='T041', title='The shear of the Tate algebra is an isometric automorphism', file=CH, deps='CLEANUP-14, CLEANUP-7', par='no',
  typ='lemmas', leaves='L9.8–L9.12',
  decls=[(CH,'norm_shearTuple_le_one'),(CH,'shearAlgHom_comp_shearAlgHom',1),(CH,'shear_X_zero',1),(CH,'shear_X_succ',1),(CH,'norm_shear')],
  sketch="""1. `norm_shearTuple_le_one`: `Fin.cases` on `i`. `0`: `Restricted.norm_X`, `norm_one`, `mul_one`. `succ`:
   `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)`; the first is `norm_X`; the second
   `norm_mul_le`, `norm_C`, `norm_pow_le`, `norm_X`, `one_pow`, `mul_one`, `ha`.
2. `shearAlgHom_comp_shearAlgHom`: `algHom_ext_of_continuous ?_ continuous_id fun j ↦ ?_` (T017); continuity
   of the composite from `continuous_aeval` twice (T018); on `X j`: `AlgHom.comp_apply`, `aeval_X`, `Fin.cases`
   on `j`, and for a successor `map_add`, `map_mul`, `map_pow`, `aeval_X`, with
   `Restricted.C 1 b = algebraMap K _ b` (`algebraMap_apply`) and `AlgHom.commutes`; collect as in T038.
3. `shear_X_zero`, `shear_X_succ`: the coercion of `AlgEquiv.ofAlgHom` is `aeval 1 (shearTuple K n e 1) _`;
   `aeval_X`, `shearTuple`, `Fin.cases_zero` / `Fin.cases_succ`, `map_one`, `one_mul`.
4. `norm_shear`: `le_antisymm (norm_aeval_le _ f) ?_`; `calc ‖f‖ = ‖(shear K n e).symm (shear K n e f)‖`
   (`AlgEquiv.symm_apply_apply`) `≤ ‖shear K n e f‖` (`norm_aeval_le`, the inverse being
   `aeval 1 (shearTuple K n e (-1)) _`).""",
  mathlib="""`IsUltrametricDist.norm_add_le_max`, `norm_mul_le`, `norm_pow_le`, `AlgHom.comp_apply`, `AlgHom.commutes`, `AlgEquiv.symm_apply_apply`, `continuous_id`. Floor: `Restricted.norm_X`, `Restricted.norm_C`, `Restricted.algebraMap_apply`.""",
  sources="""[BGR] 5.1.3, Example, `bgr-5.1.md:198–204`; [Bo] 1.2/7, `bosch-lectures.txt:488–497`; decomposition L9.8–L9.12.""",
  gen="""`K` complete (substitution into a complete algebra). The isometry is Bosch's two-sided contraction; BGR's 5.1.3/4 is not needed.""")

t(id='T042', title='The reduction of the shear is the shear of the reduction', file=CH, deps='T041, CLEANUP-8', par='no',
  typ='theorem', leaves='L9.13',
  decls=[(CH,'reduction_shear')],
  sketch="""Private lemma `reduction_X (i) : reduction ⟨Restricted.X K 1 i, _⟩ = MvPolynomial.X i` — `MvPolynomial.ext`,
`coeff_reduction`, `val_X`, `MvPowerSeries.coeff_X`, `MvPolynomial.coeff_X`; the residue of `1` is `1` and
of `0` is `0` (split the `if`).

Then `reduction_aeval (x := shearTuple K n e 1) _ f` (T021) gives
`reduction ⟨shear K n e f, _⟩ = MvPolynomial.aeval (fun i ↦ reduction ⟨shearTuple K n e 1 i, _⟩) (reduction f)`
(the two membership proofs agree by proof irrelevance; `shear K n e f` unfolds to the `aeval` by `rfl`), and
`MvPolynomial.shear _ e = aeval (Fin.cases (X 0) fun i ↦ X i.succ + C 1 * X 0 ^ e i)`. So it remains to show
the two tuples are equal: `funext`, `Fin.cases`. At `0`: `reduction_X`. At `i.succ`: the element of `T⁰` is
`⟨X i.succ, _⟩ + ⟨C 1 1, _⟩ * ⟨X 0, _⟩ ^ e i` (`Subtype.ext`), so `map_add`, `map_mul`, `map_pow`,
`reduction_X`, and the reduction of `C 1 1 = 1` is `1 = C 1`.""",
  mathlib="""`MvPolynomial.coeff_X`, `MvPowerSeries.coeff_X`, `MvPolynomial.ext`, `Fin.cases_zero`, `Fin.cases_succ`.""",
  sources="""[BGR] 5.2.4/1, `bgr-5.2.md:244`; decomposition L9.13.""",
  gen="""Stated for the unit ball element `⟨shear K n e f, _⟩` with the membership proof spelled in the statement.""")

t(id='T043', title='Distinguished charts', file=CH, deps='T040, T042, CLEANUP-12', par='no',
  typ='theorems', leaves='L9.14–L9.16',
  decls=[(CH,'exists_isMulDistinguishedX0_shear'),(CH,'exists_shear_isMulDistinguishedX0'),(CH,'exists_shear_forall_isMulDistinguishedX0')],
  sketch="""1. `exists_isMulDistinguishedX0_shear`. Let `e i := t ^ (i.val + 1)`, `σ := shear K n e`.
   - Take `a ≠ 0` with `‖a • f‖ = 1`; `g : unitClosedBall _ := ⟨a • f, _⟩`; `q := reduction g ≠ 0`.
   - For `v ∈ q.support`: `‖coeff v (a • f).1‖ = 1`, so `‖coeff v f.1‖ = ‖f‖` (`norm_smul_eq`,
     `MvPowerSeries.coeff_smul`) and `ht` gives `v i < t`.
   - `isUnit_leadingCoeff_finSuccEquiv_shear` (T040) for `q`; `reduction_shear e g` (T042) rewrites the
     reduction of `σ (a • f)`; `norm_shear` gives `‖σ (a • f)‖ = 1`.
   - `isMulDistinguishedX0_iff_reduction` (`←`) with `s := (finSuccEquiv _ n (shear _ e q)).natDegree`.
   - `σ (a • f) = a • σ f` (`map_smul`) and `isMulDistinguishedX0_smul_iff ha`.
2. `exists_shear_isMulDistinguishedX0`: `hfin := finite_setOf_le_norm_coeff f (norm_pos_iff.2 hf)`;
   `t := (hfin.toFinset.sup fun ν ↦ Finset.univ.sup fun i ↦ ν i) + 1`; an index with `‖coeff ν f.1‖ = ‖f‖`
   lies in `hfin.toFinset`, so `ν i < t` (`Finset.le_sup`, `Nat.lt_succ_of_le`); item 1.
3. `exists_shear_forall_isMulDistinguishedX0`: the same with `t` the maximum of the bounds over `f ∈ F`
   (`Finset.sup` over `F.attach`, or induction on `F` with `max`); item 1 for each `f`.""",
  mathlib="""`MvPowerSeries.coeff_smul`, `map_smul`, `Finset.sup`, `Finset.le_sup`, `Set.Finite.toFinset`, `Nat.lt_succ_of_le`, `norm_pos_iff`.""",
  sources="""[BGR] 5.2.4/1–2, `bgr-5.2.md:219–264`; [Bo] 1.2/7, `bosch-lectures.txt:479–531`; decomposition L9.14–L9.16.""",
  gen="""`t` strictly exceeds the exponents of the coefficients of maximal norm, exponents `t ^ (i + 1)`: Bosch's convention, equal to BGR's `(1 + t)^j` after the shift. The relative form of Bosch 1.8/13 is not here (erratum E8).""")

# ---------------------------------------------------------------- G10 Rueckert
t(id='T044', title='Two facts about the Krull dimension', file=RU, deps='none', par='yes',
  typ='lemmas', leaves='L10.1, L10.2',
  decls=[(RU,'ringKrullDim_le_of_isIntegral'),(RU,'ringKrullDim_le_add_one_of_forall_quotient_le')],
  sketch="""1. `ringKrullDim_le_of_isIntegral`: `algebraize [f]` (or `letI := f.toAlgebra`); then
   `Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) fun p q hpq ↦ ?_`. From
   `hpq : p < q`: `p.asIdeal ≤ q.asIdeal` and some `x ∈ q.asIdeal`, `x ∉ p.asIdeal`
   (`SetLike.exists_of_lt`); `Ideal.comap_lt_comap_of_integral_mem_sdiff hpq.le ⟨hx, hx'⟩ (hf x)` is the
   strict inequality of the contractions (unfold `RingHom.IsIntegral` to `IsIntegral R x`).
2. `ringKrullDim_le_add_one_of_forall_quotient_le`: `ringKrullDim R = Order.krullDim (PrimeSpectrum R)` is
   `⨆ p : LTSeries _, p.length`; `iSup_le fun p ↦ ?_`. Case `p.length = 0`: `0 ≤ d + 1` from `hd`. Case
   `p.length = ℓ + 1`: `x := p 1` (`⟨1, by omega⟩ : Fin (p.length + 1)`), `p 0 < p 1` (`p.strictMono`).
   `Order.rev_index_le_coheight p 1` gives `ℓ ≤ coheight x`; `Order.coheight_eq_krullDim_Ici x` turns it into
   `ℓ ≤ krullDim (Set.Ici x)`; `Set.Ici x = PrimeSpectrum.zeroLocus x.asIdeal` (`Set.ext`,
   `PrimeSpectrum.mem_zeroLocus`, `PrimeSpectrum.asIdeal_le_asIdeal`), and `ringKrullDim_quotient` identifies
   that with `ringKrullDim (R ⧸ x.asIdeal) ≤ d` (`h` with `q := (p 0).asIdeal`). Finish in `WithBot ℕ∞`:
   `Nat.cast_add_one`-style casts and `add_le_add_right`.""",
  mathlib="""`Order.krullDim_le_of_strictMono`, `PrimeSpectrum.comap`, `Ideal.comap_lt_comap_of_integral_mem_sdiff`, `Order.rev_index_le_coheight`, `Order.coheight_eq_krullDim_Ici`, `ringKrullDim_quotient`, `PrimeSpectrum.mem_zeroLocus`, `LTSeries.strictMono`. (There is no `Order.krullDim_le_iff` and no Mathlib lemma for integral maps.)""",
  sources="""[BGR] 6.1.2, Remark, `bgr-6.1.2.md:49–57` (Nagata 10.10; chains of primes); [Bo] `bosch-lectures.txt:631–632`; decomposition L10.1, L10.2.""",
  gen="""Item 1 needs no injectivity. Item 2 needs `0 ≤ d` (a field has dimension `0` and no pair `q < p`).""")

t(id='T045', title='Rückert overrings: the noetherian property', file=RU, deps='T044', par='no',
  typ='theorems', leaves='L10.3–L10.5',
  decls=[(RU,'finite_mk_comp_C'),(RU,'exists_ringEquiv_mem_map'),(RU,'isNoetherianRing')],
  sketch="""1. `finite_mk_comp_C`: `(Ideal.Quotient.mk (span {ω})).comp C` is finite
   (`Polynomial.Monic.finite_quotient (h.monic ω hω)` through `RingHom.finite_algebraMap`); the quotient map
   of axiom (2) is surjective, hence finite; `RingHom.Finite.comp`; the composite is the statement's map by
   `Ideal.quotientMap_comp_mk` (`RingHom.comp_assoc`).
2. `exists_ringEquiv_mem_map`: `obtain ⟨f, hfa, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha`;
   `obtain ⟨σ, e, ω, hω, he⟩ := h.exists_mul_mem f hf0`; `⟨σ, ω, hω, he ▸ Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hfa)⟩`.
3. `isNoetherianRing`: `(isNoetherianRing_iff_ideal_fg _).2 fun a ↦ ?_`; `a = ⊥` is finitely generated.
   Otherwise take `σ`, `ω` from item 2, `J := (Ideal.span {ω}).map φ`, `a' := a.map (σ : I' →+* I')`.
   - `I' ⧸ J` is noetherian: `isNoetherianRing_of_ringEquiv _ (RingEquiv.ofBijective _ (h.bijective_quotientMap ω hω))`
     from `Ideal.Quotient.isNoetherianRing` and `Polynomial.isNoetherianRing`.
   - `a'.FG`: `Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective (f := Ideal.Quotient.mk J) ?_ ?_ Ideal.Quotient.mk_surjective`;
     the image is finitely generated (noetherian ring); `a' ⊓ RingHom.ker (mk J) = J` (`Ideal.mk_ker`,
     `inf_eq_right`, `J ≤ a'` from `φ ω ∈ a'` and `Ideal.map_span`), finitely generated by one element.
   - back to `a`: `a = a'.map σ.symm` (`Ideal.map_of_equiv`) and `Ideal.FG.map`.""",
  mathlib="""`Polynomial.Monic.finite_quotient`, `RingHom.Finite.of_surjective`, `RingHom.Finite.comp`, `Ideal.quotientMap_comp_mk`, `Submodule.exists_mem_ne_zero_of_ne_bot`, `Ideal.mem_map_of_mem`, `isNoetherianRing_iff_ideal_fg`, `Polynomial.isNoetherianRing`, `Ideal.Quotient.isNoetherianRing`, `RingEquiv.ofBijective`, `isNoetherianRing_of_ringEquiv`, `Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective`, `Ideal.mk_ker`, `Ideal.map_of_equiv`, `Ideal.FG.map`, `Ideal.map_span`.""",
  sources="""[BGR] 5.2.5/1–2, `bgr-5.2.md:272–297`; decomposition L10.3–L10.5.""",
  gen="""Abstract `IsRueckert φ W` for commutative rings; injectivity of `φ` is not used here.""")

t(id='T046', title='Rückert overrings: the Jacobson property', file=RU, deps='T045', par='no',
  typ='theorems', leaves='L10.6, L10.7',
  decls=[(RU,'jacobson_eq_radical'),(RU,'isJacobsonRing')],
  sketch="""1. `jacobson_eq_radical`: `le_antisymm ?_ Ideal.radical_le_jacobson`. `rw [Ideal.radical_eq_sInf]`;
   `le_sInf fun p ⟨hap, hp⟩ ↦ ?_`; it suffices that `p.jacobson = p` (then `Ideal.jacobson_mono hap`). The
   prime `p` is nonzero (`a ≠ ⊥`, `a ≤ p`).
   Private lemma `jacobson_eq_self_of_isPrime (h : IsRueckert φ W) [IsJacobsonRing I] {p : Ideal I'}
   [p.IsPrime] (hp : p ≠ ⊥) : p.jacobson = p`:
   - `obtain ⟨σ, ω, hω, hmem⟩ := h.exists_ringEquiv_mem_map hp`; `p' := p.map σ` is prime
     (`Ideal.map_isPrime_of_equiv`) and it suffices to treat `p'`
     (`Ideal.map_jacobson_of_bijective σ.bijective`, `Ideal.map_of_equiv`).
   - `J := (Ideal.span {ω}).map φ ≤ p'`. The map `I → I' ⧸ p'` is
     `(Ideal.Quotient.factor _).comp ((Ideal.Quotient.mk J).comp (φ.comp C))`: integral, as a finite map
     (`h.finite_mk_comp_C hω`, `RingHom.Finite.to_isIntegral`) followed by a surjection
     (`RingHom.isIntegral_of_surjective`, `RingHom.IsIntegral.trans`).
   - `isJacobsonRing_of_isIntegral'` makes `I' ⧸ p'` a Jacobson ring; it is a domain, so `⊥` is radical and
     `(⊥ : Ideal (I' ⧸ p')).jacobson = ⊥` (`IsJacobsonRing.out`); `Ideal.jacobson_eq_iff_jacobson_quotient_eq_bot`.
2. `isJacobsonRing`: `isJacobsonRing_iff_prime_eq.2 fun P hP ↦ ?_`; `by_cases hP0 : P = ⊥` (use `h0`);
   otherwise `(h.jacobson_eq_radical hP0).trans hP.radical`.""",
  mathlib="""`Ideal.radical_le_jacobson`, `Ideal.radical_eq_sInf`, `Ideal.jacobson_mono`, `Ideal.map_isPrime_of_equiv`, `Ideal.map_jacobson_of_bijective`, `Ideal.map_of_equiv`, `Ideal.Quotient.factor`, `RingHom.Finite.to_isIntegral`, `RingHom.isIntegral_of_surjective`, `RingHom.IsIntegral.trans`, `isJacobsonRing_of_isIntegral'`, `Ideal.jacobson_eq_iff_jacobson_quotient_eq_bot`, `isJacobsonRing_iff_prime_eq`, `Ideal.IsPrime.radical`.""",
  sources="""[BGR] 5.2.5/3, `bgr-5.2.md:299–329`; 5.2.6/3, `bgr-5.2.md:392–396`; decomposition L10.6, L10.7.""",
  gen="""`a ≠ ⊥` is necessary (`k⟦X⟧` over `k`). The hypothesis `h0` of `isJacobsonRing` is BGR 5.1.3/3 for the Tate algebra.""")

t(id='T047', title='Rückert overrings: factoriality', file=RU, deps='CLEANUP-16', par='no',
  typ='theorem', leaves='L10.8',
  decls=[(RU,'uniqueFactorizationMonoid')],
  sketch="""`UniqueFactorizationMonoid.of_exists_prime_factors fun f hf ↦ ?_`.
1. `obtain ⟨σ, e, ω, hω, he⟩ := h.exists_mul_mem f hf`; `hm := h.monic ω hω`.
2. In the factorial ring `I[X]` (`Polynomial.uniqueFactorizationMonoid`):
   `obtain ⟨s, hs, hsω⟩ := UniqueFactorizationMonoid.exists_prime_factors ω hm.ne_zero`. Each `q ∈ s` divides
   `ω`, so its leading coefficient is a unit (`Polynomial.Monic.isUnit_leadingCoeff_of_dvd hm`); replace `q`
   by the monic associate `q' := C ↑(u⁻¹) * q`, still prime (`Associated.prime`). The product of the `q'`
   is monic (`Polynomial.monic_multiset_prod_of_monic`) and associated to `ω`, hence equal
   (`Polynomial.eq_of_monic_of_associated`).
3. Private lemma, by `Multiset.induction_on`: if every member of `s'` is monic and `s'.prod ∈ W`, every member
   is in `W` (`h.of_mul` on `q ::ₘ s'`, `Multiset.prod_cons`).
4. For `q' ∈ W` prime in `I[X]`: `I[X] ⧸ span {q'}` is a domain (`Ideal.span_singleton_prime`,
   `Ideal.Quotient.isDomain_iff_prime`), so `I' ⧸ (span {q'}).map φ` is a domain (`RingEquiv.ofBijective` of
   axiom (2), `MulEquiv.isDomain`), so `span {φ q'}` is prime (`Ideal.map_span`), so `φ q'` is prime
   (`φ q' ≠ 0` by `h.injective`).
5. `φ ω = (s'.map φ).prod` (`map_multiset_prod`), `σ f = ↑e⁻¹ * φ ω`, so
   `f = σ.symm ↑e⁻¹ * ((s'.map φ).map σ.symm).prod`; the members are prime (`MulEquiv.prime_iff`), and the
   product is associated to `f` (unit `σ.symm ↑e⁻¹`).""",
  mathlib="""`UniqueFactorizationMonoid.of_exists_prime_factors`, `UniqueFactorizationMonoid.exists_prime_factors`, `Polynomial.uniqueFactorizationMonoid`, `Polynomial.Monic.isUnit_leadingCoeff_of_dvd`, `Polynomial.eq_of_monic_of_associated`, `Polynomial.monic_multiset_prod_of_monic`, `Associated.prime`, `Ideal.span_singleton_prime`, `Ideal.Quotient.isDomain_iff_prime`, `MulEquiv.isDomain`, `MulEquiv.prime_iff`, `map_multiset_prod`, `Multiset.induction_on`.""",
  sources="""[BGR] 5.2.5/4, `bgr-5.2.md:336–364`; decomposition L10.8.""",
  gen="""`I` a factorial domain, `I'` a domain. BGR's direct Gauss-lemma argument is replaced by "`I[X]` is factorial", which BGR itself names as the reason (`bgr-5.2.md:341–342`).""")

t(id='T048', title='Rückert overrings: the dimension goes up by one', file=RU, deps='T047', par='no',
  typ='theorems', leaves='L10.9–L10.11',
  decls=[(RU,'ringKrullDim_quotient_le'),(RU,'ringKrullDim_le'),(RU,'ringKrullDim_add_one_le')],
  sketch="""1. `ringKrullDim_quotient_le`: `ringKrullDim_le_of_isIntegral _ (h.finite_mk_comp_C hω).to_isIntegral`.
2. `ringKrullDim_le`: `rcases subsingleton_or_nontrivial I`. Subsingleton: `I[X]` and then `I'` are trivial
   (`φ 1 = 1`, `φ 0 = 0`), `ringKrullDim_eq_bot_of_subsingleton`, `bot_le`. Nontrivial:
   `ringKrullDim_le_add_one_of_forall_quotient_le ringKrullDim_nonneg_of_nontrivial fun p q hp hq hqp ↦ ?_`;
   `p ≠ ⊥` (`bot_le.trans_lt hqp`); `obtain ⟨σ, ω, hω, hmem⟩ := h.exists_ringEquiv_mem_map hp0`;
   `R ⧸ p ≃+* R ⧸ p.map σ` (`Ideal.quotientEquiv p _ σ rfl`, `ringKrullDim_eq_of_ringEquiv`);
   `(Ideal.span {ω}).map φ ≤ p.map σ`, so `Ideal.Quotient.factor` is surjective and
   `ringKrullDim_le_of_surjective`; then item 1.
3. `ringKrullDim_add_one_le`: `x := φ X ≠ 0` (`h.injective`, `Polynomial.X_ne_zero`; `I` is nontrivial because
   `I'` is), so `x ∈ nonZeroDivisors I'` (`mem_nonZeroDivisors_of_ne_zero`).
   `ringKrullDim_quotient_succ_le_of_nonZeroDivisor` gives `ringKrullDim (I' ⧸ span {x}) + 1 ≤ ringKrullDim I'`.
   And `I' ⧸ span {x} ≃+* I`: `span {x} = (span {X}).map φ` (`Ideal.map_span`), axiom (2) for `X`
   (`RingEquiv.ofBijective`), and `Polynomial.quotientSpanXSubCAlgEquiv 0` after `X = X - C 0`;
   `ringKrullDim_eq_of_ringEquiv`.""",
  mathlib="""`RingHom.Finite.to_isIntegral`, `ringKrullDim_eq_bot_of_subsingleton`, `ringKrullDim_nonneg_of_nontrivial`, `Ideal.quotientEquiv`, `ringKrullDim_eq_of_ringEquiv`, `Ideal.Quotient.factor`, `ringKrullDim_le_of_surjective`, `mem_nonZeroDivisors_of_ne_zero`, `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`, `Polynomial.quotientSpanXSubCAlgEquiv`, `Polynomial.X_ne_zero`, `Ideal.map_span`.""",
  sources="""[BGR] 6.1.2, Remark, `bgr-6.1.2.md:49–57`; [Bo] 1.2/10, `bosch-lectures.txt:618–632`; decomposition L10.9–L10.11.""",
  gen="""The upper bound replaces BGR's use of 7.1.1/3 (erratum E5). The lower bound needs `X ∈ W` and a domain. `ringKrullDim_eq` is already assembled in the skeleton.""")

# ---------------------------------------------------------------- G11 TateAlgebra/Rueckert
t(id='T049', title='The Tate algebra is a Rückert overring', file=TRU, deps='CLEANUP-13, CLEANUP-15', par='no',
  typ='theorem', leaves='L11.1',
  decls=[(TRU,'isRueckert_ofPolynomial')],
  sketch="""`refine ⟨ofPolynomial_injective, fun _ hω ↦ hω.monic, fun _ _ hp hq h ↦ IsWeierstrassPolynomial.of_mul hp hq h,
fun _ hω ↦ IsWeierstrassPolynomial.bijective_quotientMap hω, fun f hf ↦ ?_⟩` (the first four fields compile
as written: `scratch/spot3.lean`, item 1). For axiom (3):
`obtain ⟨e, s, hs⟩ := exists_shear_isMulDistinguishedX0 hf`;
`obtain ⟨ω, u, hω, -, hu⟩ := exists_isWeierstrassPolynomial_of_isMulDistinguishedX0 hs`;
`exact ⟨(shear K n e).toRingEquiv, u⁻¹, ω, hω, by rw [show (shear K n e).toRingEquiv f = shear K n e f from rfl, hu, Units.inv_mul_cancel_left]⟩`.""",
  mathlib="""`AlgEquiv.toRingEquiv`, `Units.inv_mul_cancel_left`.""",
  sources="""[BGR] 5.2.5–5.2.6, `bgr-5.2.md:282–283`, `:366–368`; decomposition L11.1.""",
  gen="""`K` complete, as an explicit binder (the section-variable trap, defect D5).""")

t(id='T050', title='`Tₙ` is noetherian, factorial, Jacobson, of dimension `n`', file=TRU, deps='CLEANUP-ALL-2', par='no',
  typ='instances + theorem (milestone M2)', leaves='L11.2–L11.5', milestone='M2',
  decls=[(TRU,'instIsNoetherianRing'),(TRU,'instUniqueFactorizationMonoid'),(TRU,'instIsJacobsonRing'),(TRU,'ringKrullDim_eq')],
  sketch="""Each by `induction n`, with `e₀ : TateAlgebra K 0 ≃+* K := Restricted.isEmptyEquiv K (1 : Fin 0 → ℝ)`.
1. `instIsNoetherianRing`: base `isNoetherianRing_of_ringEquiv K e₀.symm`; step
   `(isRueckert_ofPolynomial K n).isNoetherianRing` (both compile: `spot3.lean`, items 2–3).
2. `instUniqueFactorizationMonoid`: base `e₀.toMulEquiv.symm.uniqueFactorizationMonoid inferInstance` (a field
   is factorial); step `(isRueckert_ofPolynomial K n).uniqueFactorizationMonoid` (the `IsDomain` instances are
   T002's).
3. `instIsJacobsonRing`: base `isJacobsonRing_of_surjective ⟨(e₀.symm : K →+* _), e₀.symm.surjective⟩`; step
   `(isRueckert_ofPolynomial K n).isJacobsonRing jacobson_bot` (`spot3.lean`, item 3'').
4. `ringKrullDim_eq`: base `(ringKrullDim_eq_of_ringEquiv e₀).trans ringKrullDim_eq_zero_of_field`; step
   `(isRueckert_ofPolynomial K n).ringKrullDim_eq (by simpa using isWeierstrassPolynomial_X_pow 1)`
   (`spot3.lean`, item 3'), the induction hypothesis, and `Nat.cast_add_one`-style casts in `WithBot ℕ∞`.
The `example` for `IsIntegrallyClosed` below the factorial instance already compiles.""",
  mathlib="""`isNoetherianRing_of_ringEquiv`, `MulEquiv.uniqueFactorizationMonoid`, `isJacobsonRing_of_surjective`, `ringKrullDim_eq_of_ringEquiv`, `ringKrullDim_eq_zero_of_field`. Floor: `Restricted.isEmptyEquiv`.""",
  sources="""[BGR] 5.2.6/1–3, `bgr-5.2.md:366–396`; 6.1.2, Remark, `bgr-6.1.2.md:49–57`; [Bo] 1.2/13–15, `bosch-lectures.txt:676–743`; decomposition L11.2–L11.5.""",
  gen="""Milestone M2. Instances on `TateAlgebra K n` for a complete `K`; normality follows by `inferInstance`.""")

# ---------------------------------------------------------------- G12 Bald
t(id='T051', title='Bald subrings and the localisation at elements of norm one', file=BALD, deps='none', par='yes',
  typ='lemmas', leaves='L12.1–L12.5',
  decls=[(BALD,'IsBald.mono'),(BALD,'le_unitLocalization'),(BALD,'mem_unitLocalization_iff'),(BALD,'IsBald.unitLocalization'),(BALD,'isBRing_unitLocalization')],
  sketch="""1. `IsBald.mono`: `⟨fun a ha ↦ hS'.norm_le_one a (h ha), hS'.exists_norm_le.imp fun ε hε ↦ ⟨hε.1, fun a ha ↦ hε.2 a (h ha)⟩⟩`.
2. `le_unitLocalization`: `fun x hx ↦ Subring.subset_closure (Or.inl hx)`.
3. `mem_unitLocalization_iff`: `←`: `rintro ⟨s, hs, u, hu, hu1, rfl⟩`; `div_eq_mul_inv`, `mul_mem` of
   `subset_closure (Or.inl hs)` and `subset_closure (Or.inr ⟨u, hu, hu1, rfl⟩)`. `→`:
   `Subring.closure_induction` with the predicate `∃ s ∈ S, ∃ u ∈ S, ‖u‖ = 1 ∧ x = s / u`: generators `s`
   (`s / 1`) and `u⁻¹` (`1 / u`); `0`, `1`; sums `(s₁ * u₂ + s₂ * u₁) / (u₁ * u₂)` (`div_add_div`, `norm_mul`,
   denominators nonzero since their norm is `1`); negation; products (`div_mul_div_comm`).
4. `IsBald.unitLocalization`: with item 3, `‖s / u‖ = ‖s‖` (`norm_div`, `hu1`, `div_one`); both fields
   follow from those of `S` with the same `ε`.
5. `isBRing_unitLocalization`: norms as in item 4; if `‖s / u‖ = 1` then `‖s‖ = 1`, and
   `(s / u)⁻¹ = u / s` (`inv_div`) is in the localisation by item 3 (`←`).""",
  mathlib="""`Subring.subset_closure`, `Subring.closure_induction`, `div_add_div`, `div_mul_div_comm`, `norm_div`, `norm_mul`, `inv_div`.""",
  sources="""[Bo] 1.3/2–3, `bosch-lectures.txt:767–772`, `:784–785`, `:806–807`; decomposition L12.1–L12.5.""",
  gen="""Subrings of a normed field; no ultrametric hypothesis is needed in this ticket.""")

t(id='T052', title='The prime subring is bald; adjoining small elements', file=BALD, deps='T051', par='no',
  typ='lemmas', leaves='L12.6, L12.7',
  decls=[(BALD,'isBald_bot'),(BALD,'IsBald.closure_union_of_norm_le')],
  sketch="""1. `isBald_bot`: elements of `⊥` are integer casts (`Subring.mem_bot`), of norm `≤ 1`
   (`IsUltrametricDist.norm_intCast_le_one`). For the bound: `by_cases hex : ∃ g : ℕ, 0 < g ∧ ‖(g : K)‖ < 1`.
   - No: `ε := 0`. If `‖(z : K)‖ < 1` then `z.natAbs = 0` (else it is a positive natural of norm `< 1`:
     `Int.natAbs_eq`, `norm_neg`), so `z = 0` and the norm is `0`.
   - Yes: `g := Nat.find hex`, `ε := ‖(g : K)‖`. For `z` with `‖(z : K)‖ < 1`, `m := z.natAbs`,
     `‖(m : K)‖ = ‖(z : K)‖`; write `m = g * (m / g) + m % g` (`Nat.div_add_mod`); then
     `‖((m % g : ℕ) : K)‖ ≤ max ‖(m : K)‖ ‖(g : K)‖ < 1` (cast the identity, ultrametric), and `m % g < g`
     with minimality (`Nat.find_min`) forces `m % g = 0`; so `‖(m : K)‖ = ‖(g : K)‖ * ‖((m / g : ℕ) : K)‖ ≤ ε`
     (`IsUltrametricDist.norm_natCast_le_one`).
2. `IsBald.closure_union_of_norm_le`: `obtain ⟨εS, hεS, hS'⟩ := hS.exists_norm_le`; `δ := max ε 0`;
   `Subring.closure_induction` with the predicate `∃ s ∈ S, ∃ z, ‖z‖ ≤ δ ∧ x = s + z`: generators (`s + 0`,
   `0 + t`), `0`, `1`, sums and negation (ultrametric), products
   `(s₁ + z₁) * (s₂ + z₂) = s₁ * s₂ + (s₁ * z₂ + z₁ * s₂ + z₁ * z₂)` with each term of norm `≤ δ` (`‖sᵢ‖ ≤ 1`,
   `δ < 1`). Then: norm `≤ 1` by the ultrametric inequality; if `‖s + z‖ < 1` then `‖s‖ < 1` (otherwise
   `‖s‖ = 1 > ‖z‖` and `‖s + z‖ = 1` by `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`), so
   `‖s‖ ≤ εS` and `‖s + z‖ ≤ max εS δ < 1`.""",
  mathlib="""`Subring.mem_bot`, `IsUltrametricDist.norm_intCast_le_one`, `IsUltrametricDist.norm_natCast_le_one`, `Int.natAbs_eq`, `Nat.find`, `Nat.find_min`, `Nat.div_add_mod`, `Subring.closure_induction`, `IsUltrametricDist.norm_add_le_max`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`.""",
  sources="""[Bo] 1.3/3, `bosch-lectures.txt:777–780`; decomposition L12.6, L12.7.""",
  gen="""Any nonarchimedean normed field, any characteristic. `Int.cast_natAbs` does not exist at the pin; use `Int.natAbs_eq`.""")

t(id='T053', title='Adjoining an element of norm one to a bald B-ring', file=BALD, deps='T052', par='no',
  typ='lemmas', leaves='L12.8, L12.9',
  decls=[(BALD,'IsBRing.exists_monic_norm_aeval_lt_one'),(BALD,'IsBRing.isBald_closure_insert')],
  sketch="""1. `IsBRing.exists_monic_norm_aeval_lt_one`. Let `d` be the largest `i ≤ p.natDegree` with
   `‖(p.coeff i : K)‖ = 1` (`Finset.exists_max_image` on the filtered range, nonempty by `hc`).
   `low := ∑ i ∈ Finset.range (d + 1), Polynomial.monomial i (p.coeff i)`, and `p - low` has all coefficients
   of norm `< 1`, so `‖aeval a (p - low)‖ < 1` (`Polynomial.aeval_eq_sum_range`, the ultrametric bound on a
   finite sum, `‖a ^ i‖ = 1`); hence `‖aeval a low‖ < 1`. The coefficient `p.coeff d` has norm one, so its
   inverse lies in `S` (`hS.inv_mem`): `u : S`. `g := Polynomial.C u * low` is monic of degree `d`
   (coefficient at `d` is `u * p.coeff d = 1`, higher coefficients vanish), `g.natDegree = d ≤ p.natDegree`,
   and `‖aeval a g‖ = ‖(u : K)‖ * ‖aeval a low‖ < 1`.
2. `IsBRing.isBald_closure_insert`.
   - Every element of `closure (insert a S)` is `Polynomial.aeval a p` for some `p : Polynomial S`
     (`Subring.closure_induction`: `a = aeval a X`, `s = aeval a (C ⟨s, _⟩)`, ring operations by `map_*`).
   - `‖aeval a p‖ ≤ 1` (finite ultrametric sum, `hB.norm_le_one`, `ha`).
   - Bald constant: `obtain ⟨εS, hεS, hS'⟩ := hS.exists_norm_le`.
     `by_cases hex : ∃ g : Polynomial S, g.Monic ∧ ‖aeval a g‖ < 1`.
     *No*: if `‖aeval a p‖ < 1`, no coefficient of `p` has norm one (item 1), so all are `≤ εS` and
     `‖aeval a p‖ ≤ εS`.
     *Yes*: choose `g` of minimal degree (`Nat.find` on `∃ g, g.Monic ∧ ‖aeval a g‖ < 1 ∧ g.natDegree = n`);
     `ε := max ‖aeval a g‖ εS`. For `f` with `‖aeval a f‖ < 1`: `f = g * (f /ₘ g) + f %ₘ g`
     (`Polynomial.modByMonic_add_div`), `r := f %ₘ g`, `r.natDegree < g.natDegree` when `g ≠ 1`
     (`Polynomial.natDegree_modByMonic_lt`; if `g = 1` then `‖aeval a g‖ = 1`, impossible).
     `‖aeval a r‖ < 1`. If some coefficient of `r` had norm one, item 1 would give a monic polynomial of
     smaller degree — contradiction. So `‖aeval a r‖ ≤ εS` and
     `‖aeval a f‖ ≤ max (‖aeval a g‖ * ‖aeval a (f /ₘ g)‖) ‖aeval a r‖ ≤ ε`.""",
  mathlib="""`Finset.exists_max_image`, `Polynomial.aeval_eq_sum_range`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `Polynomial.modByMonic_add_div`, `Polynomial.natDegree_modByMonic_lt`, `Nat.find`, `Nat.find_min`, `Subring.closure_induction`, `Polynomial.aeval_X`, `Polynomial.aeval_C`.""",
  sources="""[Bo] 1.3/3, `bosch-lectures.txt:781–805`; decomposition L12.8, L12.9.""",
  gen="""Bosch's dichotomy (`ã` transcendental or algebraic over `S̃`) is phrased without residue fields: either no monic `g` has `‖g(a)‖ < 1`, or one of minimal degree exists.""")

t(id='T054', title='The subring generated by a null family is bald', file=BALD, deps='CLEANUP-19', par='no',
  typ='theorems', leaves='L12.10, L12.11',
  decls=[(BALD,'IsBald.closure_insert'),(BALD,'isBald_closure_range')],
  sketch="""1. `IsBald.closure_insert`: `rcases ha.lt_or_eq with h | h`.
   - `‖a‖ < 1`: `Set.insert_eq`, `Set.union_comm`, then
     `hS.closure_union_of_norm_le h fun x hx ↦ (Set.mem_singleton_iff.1 hx ▸ le_rfl)`.
   - `‖a‖ = 1`: `S' := S.unitLocalization` is bald (`hS.unitLocalization`) and a B-ring
     (`isBRing_unitLocalization hS.norm_le_one`), so `closure (insert a S')` is bald (T053), and
     `closure (insert a S) ≤ closure (insert a S')` (`Subring.closure_mono`, `Set.insert_subset_insert`,
     `le_unitLocalization`); `IsBald.mono`.
2. `isBald_closure_range`: `F := {i | (1/2 : ℝ) < ‖a i‖}` is finite (`ha0.norm`, `eventually_le_const`-style:
   `Filter.Tendsto.eventually_lt_const`, `Filter.eventually_cofinite`).
   - `R₀ := closure (a '' F)` is bald: `Set.Finite.induction_on` on the finite set `a '' F`; base
     `Subring.closure_empty` and `isBald_bot`; step `closure (insert x s) = closure (insert x ↑(closure s))`
     (`Subring.closure_union`, `Subring.closure_eq`, `Set.insert_eq`) and item 1 (`‖x‖ ≤ 1` from `ha`).
   - `closure (↑R₀ ∪ a '' Fᶜ)` is bald by `closure_union_of_norm_le` with `ε = 1/2`.
   - `closure (range a) ≤` that (`Subring.closure_mono`: `range a ⊆ a '' F ∪ a '' Fᶜ`,
     `Subring.subset_closure`); `IsBald.mono`.""",
  mathlib="""`Subring.closure_mono`, `Subring.closure_empty`, `Subring.closure_eq`, `Subring.closure_union`, `Set.Finite.induction_on`, `Set.Finite.image`, `Filter.Tendsto.eventually_lt_const`, `Filter.eventually_cofinite`, `Set.insert_eq`.""",
  sources="""[Bo] 1.3/3, `bosch-lectures.txt:774–785`; decomposition L12.10, L12.11.""",
  gen="""A family indexed by any type, null along the cofinite filter (Bosch's "zero sequence"). Nullity is necessary over a densely valued field.""")

# ---------------------------------------------------------------- G13 Orthonormal
t(id='T055', title='Orthonormal families: finite sums', file=ON, deps='none', par='yes',
  typ='lemmas', leaves='L13.1–L13.3',
  decls=[(ON,'norm_coeff_le_norm_sum'),(ON,'norm_sum_le'),(ON,'linearIndependent')],
  sketch="""`he.2 s a : ‖∑ i ∈ s, a i • e i‖₊ = s.sup fun i ↦ ‖a i • e i‖₊`, and `‖a i • e i‖₊ = ‖a i‖₊`
(`nnnorm_smul`, `he.1 i` in `ℝ≥0`, `mul_one`).
1. `norm_coeff_le_norm_sum`: in `ℝ≥0`, `‖a i‖₊ = ‖a i • e i‖₊ ≤ s.sup _ = ‖∑‖₊` (`Finset.le_sup hi`); coerce
   (`NNReal.coe_le_coe`, `coe_nnnorm`).
2. `norm_sum_le`: lift `C` to `ℝ≥0` (`C.toNNReal`, `Real.coe_toNNReal C hC`); `rw [he.2]`;
   `Finset.sup_le fun i hi ↦ ?_`.
3. `linearIndependent`: `linearIndependent_iff'.2 fun s g hg i hi ↦ ?_`;
   `norm_le_zero_iff.1 ((he.norm_coeff_le_norm_sum s g hi).trans_eq (by rw [hg, norm_zero]))`.""",
  mathlib="""`nnnorm_smul`, `Finset.le_sup`, `Finset.sup_le`, `linearIndependent_iff'`, `norm_le_zero_iff`, `NNReal.coe_le_coe`, `Real.coe_toNNReal`.""",
  sources="""[Bo] 1.3/5, `bosch-lectures.txt:820–831`; PFA roadmap convention 5, §2.2.1; decomposition L13.1–L13.3.""",
  gen="""A normed space over a normed field; no ultrametricity or completeness. `hC : 0 ≤ C` covers the empty sum.""")

t(id='T056', title='Orthonormal families: convergent sums', file=ON, deps='T055', par='no',
  typ='lemmas', leaves='L13.4–L13.7',
  decls=[(ON,'tendsto_cofinite_of_hasSum'),(ON,'norm_coeff_le_of_hasSum'),(ON,'norm_le_of_hasSum'),(ON,'eq_of_hasSum')],
  sketch="""1. `tendsto_cofinite_of_hasSum`: `tendsto_zero_iff_norm_tendsto_zero.2 ?_`;
   `hx.summable.tendsto_cofinite_zero.norm` rewritten with `norm_smul`, `he.1`, `mul_one`, `norm_zero`.
2. `norm_coeff_le_of_hasSum`: `hx.norm : Tendsto (fun s ↦ ‖∑ j ∈ s, a j • e j‖) atTop (𝓝 ‖x‖)`;
   `ge_of_tendsto` (or `le_of_tendsto'` on the constant) with
   `(Filter.eventually_ge_atTop {i}).mono fun s hs ↦ he.norm_coeff_le_norm_sum s a (hs (Finset.mem_singleton_self i))`.
3. `norm_le_of_hasSum`: `le_of_tendsto' hx.norm fun s ↦ he.norm_sum_le s a hC fun i _ ↦ h i`.
4. `eq_of_hasSum`: `funext i`; `sub_eq_zero.1 (norm_le_zero_iff.1 ?_)`;
   `(he.norm_coeff_le_of_hasSum (a := a - b) (x := 0) ?_ i).trans_eq norm_zero`, the `HasSum` from
   `ha.sub hb` with `Pi.sub_apply`, `sub_smul`, `sub_self`.""",
  mathlib="""`tendsto_zero_iff_norm_tendsto_zero`, `Summable.tendsto_cofinite_zero`, `Filter.Tendsto.norm`, `ge_of_tendsto`, `le_of_tendsto'`, `Filter.eventually_ge_atTop`, `HasSum.sub`, `sub_smul`.""",
  sources="""[Bo] 1.3/5 (iii), `bosch-lectures.txt:829–831`; decomposition L13.4–L13.7.""",
  gen="""No completeness: the expansions are hypotheses.""")

t(id='T057', title='Expansions in an orthonormal basis exist', file=ON, deps='T056', par='no',
  typ='theorems', leaves='L13.8, L13.9',
  decls=[(ON,'summable_smul'),(ON,'exists_hasSum')],
  sketch="""1. `summable_smul`: `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`; the terms tend to zero by
   `tendsto_zero_iff_norm_tendsto_zero` and `norm_smul`, `he.1`.
2. `IsOrthonormalBasis.exists_hasSum` (`K` complete — false otherwise, see the docstring).
   - `he.2 x : x ∈ closure (span K (range e))`; `mem_closure_iff_seq_limit` gives `u : ℕ → V` in the span
     with `u k → x`; `Finsupp.mem_span_range_iff_exists_finsupp` gives `l k : I →₀ K` with
     `(l k).sum (fun i c ↦ c • e i) = u k`.
   - For `k`, `m` and `i`: `‖l k i - l m i‖ ≤ ‖u k - u m‖` (`he.1.norm_coeff_le_norm_sum` on the finset
     `(l k).support ∪ (l m).support` for the family `l k - l m`; when `i` is outside both supports the left
     side is `0`).
   - So for each `i`, `k ↦ l k i` is Cauchy (`u` is Cauchy: `Filter.Tendsto.cauchySeq`); `a i` := its limit
     (`cauchySeq_tendsto_of_complete`). Passing to the limit in `m`: `‖l k i - a i‖ ≤ δ k` with
     `δ k := sup over m ≥ k of ‖u k - u m‖`, more simply: for `ε > 0` choose `N` with `‖u k - u m‖ ≤ ε` for
     `k, m ≥ N`; then `‖l k i - a i‖ ≤ ε` for `k ≥ N` and all `i` (`le_of_tendsto`).
   - `a → 0` cofinitely: outside `(l N).support`, `‖a i‖ ≤ ε`.
   - `y := ∑' i, a i • e i` exists (item 1), and `‖y - u k‖ ≤ ε` for `k ≥ N`
     (`he.1.norm_le_of_hasSum` for the family `a - l k`, whose sum is `y - u k`: `HasSum.sub` and
     `hasSum_sum_of_ne_finset_zero` for the finitely supported `l k`). Hence `u k → y`, and `y = x`
     (`tendsto_nhds_unique`).""",
  mathlib="""`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`, `tendsto_zero_iff_norm_tendsto_zero`, `mem_closure_iff_seq_limit`, `Finsupp.mem_span_range_iff_exists_finsupp`, `Filter.Tendsto.cauchySeq`, `cauchySeq_tendsto_of_complete`, `le_of_tendsto`, `HasSum.sub`, `hasSum_sum_of_ne_finset_zero`, `tendsto_nhds_unique`.""",
  sources="""[Bo] 1.3/5 (ii), `bosch-lectures.txt:820–826`; `:813–814` (`K` complete); decomposition L13.8, L13.9.""",
  gen="""`[CompleteSpace K]` is necessary (defect D7: `ℚ ⊂ ℚ_p`). `summable_smul` needs only `V` complete and ultrametric.""")

# ---------------------------------------------------------------- G14 OrthonormalLift
t(id='T058', title='Descent to a subfield; the residue field of a B-ring', file=LIFT, deps='CLEANUP-20', par='yes (with G13)',
  typ='lemma + definition', leaves='L14.1, L14.2',
  decls=[(LIFT,'Finsupp.mem_span_range_of_mapRange_mem_span'),(LIFT,'Subring.IsBRing.residueSubfield')],
  sketch="""1. `Finsupp.mem_span_range_of_mapRange_mem_span`. `ι := Algebra.linearMap F E` is injective
   (`(algebraMap F E).injective`); `obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective ι (LinearMap.ker_eq_bot.2 _)`,
   so `π (algebraMap F E c) = c`. `obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 h` with
   `l : M →₀ E`. Claim `w = (l.mapRange π (map_zero π)).sum fun μ c ↦ c • v μ`; then
   `Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨_, rfl⟩`-style. Check at `n : N`: evaluate `hl` at `n`
   (`Finsupp.sum_apply`, `Finsupp.smul_apply`, `Finsupp.mapRange_apply`):
   `algebraMap (w n) = ∑ μ ∈ l.support, l μ * algebraMap (v μ n)`; apply `π` (`map_sum`), and
   `π (l μ * algebraMap c) = π (c • l μ) = c * π (l μ)` (`Algebra.smul_def`, `mul_comm`, `map_smul`).
   Terms with `π (l μ) = 0` are harmless (`Finsupp.sum_mapRange_index` or sum over `l.support`).
2. `residueSubfield`: the six fields. Write `ρ s hs := residue _ ⟨s, _⟩`. `one_mem'`, `zero_mem'`:
   `⟨1, S.one_mem, by simp⟩`-style (`map_one`, `map_zero`, the subtype is `1` / `0`). `add_mem'`,
   `mul_mem'`, `neg_mem'`: `⟨s + t, S.add_mem hs ht, by rw [← map_add]; rfl⟩` etc. `inv_mem'`: for
   `z = ρ s hs`, `rcases (hS.norm_le_one s hs).lt_or_eq`: if `‖s‖ < 1` then `z = 0` (`residue_eq_zero_iff`,
   `maximalIdeal_unitClosedBall`) and `inv_zero`; if `‖s‖ = 1` then `s⁻¹ ∈ S` (`hS.inv_mem`), and
   `ρ s⁻¹ = z⁻¹` by `eq_inv_of_mul_eq_one_right` (`← map_mul`, the product in `K⁰` is `1`).""",
  mathlib="""`LinearMap.exists_leftInverse_of_injective`, `Finsupp.mem_span_range_iff_exists_finsupp`, `Finsupp.sum_apply`, `Finsupp.mapRange_apply`, `Algebra.smul_def`, `IsLocalRing.residue_eq_zero_iff`, `eq_inv_of_mul_eq_one_right`.""",
  sources="""[Bo] 1.3/3 and 1.3/6, `bosch-lectures.txt:785–786`, `:869–874`; decomposition L14.1, L14.2.""",
  gen="""Item 1 is pure linear algebra over a field extension `F → E` (false for rings). Item 2 is a `Subfield` of the residue field of `K`, so that Bosch's `S̃ ⊂ k` is literal.""")

t(id='T059', title='Independent reductions are orthonormal', file=LIFT, deps='CLEANUP-21', par='no',
  typ='theorem', leaves='L14.3',
  decls=[(LIFT,'IsOrthonormalFamily.of_linearIndependent_residue')],
  sketch="""`refine ⟨fun μ ↦ ?_, fun s a ↦ ?_⟩`.
1. `‖y μ‖ = 1`: `≤` by `hx.norm_le_of_hasSum (hy μ) zero_le_one (hc μ)`. `≥`: `r μ ≠ 0`
   (`hli.ne_zero μ`), so some `ν` has `r μ ν ≠ 0`; by `hr` and `residue_eq_zero_iff`,
   `maximalIdeal_unitClosedBall`, `¬ ‖c μ ν‖ < 1`, so `1 ≤ ‖c μ ν‖ ≤ ‖y μ‖` (`hx.norm_coeff_le_of_hasSum`).
2. The identity `‖∑ μ ∈ s, a μ • y μ‖₊ = s.sup fun μ ↦ ‖a μ • y μ‖₊`. Reduce to reals; `‖a μ • y μ‖ = ‖a μ‖`.
   - `≤`: `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`.
   - `≥`: let `μ₀ ∈ s` maximise `‖a μ‖` (`Finset.exists_max_image`; `s = ∅` is trivial); if `a μ₀ = 0` all are
     `0`. Otherwise `b μ := a μ / a μ₀`, `‖b μ‖ ≤ 1`, `b μ₀ = 1`, and it suffices that `1 ≤ ‖∑ μ ∈ s, b μ • y μ‖`.
     `HasSum (fun ν ↦ (∑ μ ∈ s, b μ * c μ ν) • x ν) (∑ μ ∈ s, b μ • y μ)` (`hasSum_sum`, `HasSum.const_smul`,
     `Finset.sum_smul`, `mul_smul`). The coefficients `d ν` lie in `K⁰`, with residues
     `(∑ μ ∈ s, b̃ μ • r μ) ν` (`map_sum`, `map_mul`, `hr`). Since `b̃ μ₀ = 1 ≠ 0` and `hli`, that combination
     is nonzero (`linearIndependent_iff'`), so some `ν` has `‖d ν‖ = 1`, and
     `hx.norm_coeff_le_of_hasSum _ ν` concludes.""",
  mathlib="""`LinearIndependent.ne_zero`, `linearIndependent_iff'`, `hasSum_sum`, `HasSum.const_smul`, `Finset.exists_max_image`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `IsLocalRing.residue_eq_zero_iff`. Chain: `IsOrthonormalFamily.norm_le_of_hasSum`, `IsOrthonormalFamily.norm_coeff_le_of_hasSum`.""",
  sources="""[Bo] 1.3/6, `bosch-lectures.txt:849–851`; decomposition L14.3.""",
  gen="""No baldness and no completeness: independence of the reductions alone gives orthonormality.""")

t(id='T060', title='Spanning reductions give approximation up to the bald constant', file=LIFT, deps='T058, T059', par='no',
  typ='theorem', leaves='L14.4',
  decls=[(LIFT,'exists_norm_sub_le_of_span_residue')],
  sketch="""1. `S' := S.unitLocalization`, bald (`hS.unitLocalization`) and a B-ring
   (`isBRing_unitLocalization hS.norm_le_one`); `obtain ⟨ε, hε, hbald⟩ := hS'.exists_norm_le`;
   `F := hB.residueSubfield`. Use this `ε`.
2. The family over `F`: `rF μ : N →₀ F := Finsupp.onFinset (r μ).support (fun ν ↦ ⟨r μ ν, _⟩) _`, membership
   by `hr` and `c μ ν ∈ S ≤ S'`; `Finsupp.mapRange (algebraMap F _) _ (rF μ) = r μ`.
3. Fix `ν`. `Finsupp.single ν 1` lies in `span k (range r) = ⊤`, and it is the `mapRange` of
   `Finsupp.single ν (1 : F)`, so by T058 it lies in `span F (range rF)`:
   `obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 _` with `l : M →₀ F`. For `μ ∈ l.support`
   choose `b μ ∈ S'` with `l μ = ρ (b μ)` (`mem_residueSubfield`).
4. `z := ∑ μ ∈ l.support, b μ • y μ ∈ span K (range y)`. Expansion of `x ν - z` in `x`:
   `HasSum (fun ν' ↦ d ν' • x ν') (x ν - z)` with `d ν' := (if ν' = ν then 1 else 0) - ∑ μ ∈ l.support, b μ * c μ ν'`
   (`hasSum_ite_eq`-type for `x ν`, `hasSum_sum`, `HasSum.const_smul`, `HasSum.sub`).
5. `d ν' ∈ S'` (subring), and its residue is `(single ν 1 - ∑ l μ • r μ) ν' = 0` by `hl`; so `‖d ν'‖ < 1`,
   hence `‖d ν'‖ ≤ ε` (`hbald`). `hx.norm_le_of_hasSum _ (le of 0 ≤ ε) _` gives `‖x ν - z‖ ≤ ε`; `0 ≤ ε`
   because `0 ∈ S'` has norm `0 < 1`.""",
  mathlib="""`Finsupp.onFinset`, `Finsupp.mem_span_range_iff_exists_finsupp`, `Finsupp.mapRange_apply`, `hasSum_sum`, `HasSum.const_smul`, `HasSum.sub`, `hasSum_ite_eq`, `Submodule.sum_mem`, `Submodule.smul_mem`, `Submodule.subset_span`.""",
  sources="""[Bo] 1.3/6, `bosch-lectures.txt:851–876`; decomposition L14.4.""",
  gen="""The uniform `ε` is the bald constant of the localisation of `S`. Baldness is necessary (counterexample in the module docstring). No completeness.""")

t(id='T061', title='Lifting of orthonormal bases', file=LIFT, deps='CLEANUP-22', par='no',
  typ='theorems', leaves='L14.5, L14.6',
  decls=[(LIFT,'dense_span_of_forall_exists_norm_sub_le'),(LIFT,'IsOrthonormalBasis.of_residue_basis')],
  sketch="""1. `dense_span_of_forall_exists_norm_sub_le`. `ε' := max ε (1/2)`, `0 < ε' < 1`, and `h` holds with `ε'`.
   `U := (Submodule.span K (range y)).toAddSubgroup`; apply
   `AddSubgroup.dense_of_infDist_le U ε' _ _ fun v ↦ ?_` (BGR 1.1.4/2, in the floor), i.e. show
   `Metric.infDist v U ≤ ε' * dist v 0`. `v = 0` is trivial. Otherwise:
   - by density of `span K (range x)` (`hx.2`) choose `v'` in it with `‖v - v'‖ ≤ ε' * ‖v‖`
     (`Metric.mem_closure_iff`); then `‖v'‖ ≤ ‖v‖` (ultrametric);
   - `v' = ∑ ν ∈ s, a ν • x ν` (`Finsupp.mem_span_range_iff_exists_finsupp`); choose `z ν` from `h`;
     `z' := ∑ ν ∈ s, a ν • z ν ∈ U`, and
     `‖v' - z'‖ = ‖∑ a ν • (x ν - z ν)‖ ≤ ε' * ‖v'‖` (`IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`,
     `norm_smul`, `hx.1.norm_coeff_le_norm_sum`);
   - `‖v - z'‖ ≤ max ‖v - v'‖ ‖v' - z'‖ ≤ ε' * ‖v‖`, and `Metric.infDist_le_dist_of_mem`.
2. `IsOrthonormalBasis.of_residue_basis`:
   `⟨hx.1.of_linearIndependent_residue hy (fun μ ν ↦ hS.norm_le_one _ (hcS μ ν)) r hr hli, ?_⟩`, and for the
   density `obtain ⟨ε, hε, h⟩ := exists_norm_sub_le_of_span_residue hx.1 hy hS hcS r hr hspan`;
   `exact dense_span_of_forall_exists_norm_sub_le hx hε h`.""",
  mathlib="""`Metric.mem_closure_iff`, `Metric.infDist_le_dist_of_mem`, `Finsupp.mem_span_range_iff_exists_finsupp`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `IsUltrametricDist.norm_add_le_max`. Floor: `AddSubgroup.dense_of_infDist_le`.""",
  sources="""[Bo] 1.3/6, `bosch-lectures.txt:839–883`; BGR 1.1.4/2 (the floor's lemma); decomposition L14.5, L14.6.""",
  gen="""The conclusion is the dense-span form of `IsOrthonormalBasis`, and holds without completeness of `K` or `V` (defect D4); Bosch's "by iteration" is the density lemma.""")

# ---------------------------------------------------------------- G15 StrictlyClosed
t(id='T062', title='A basis of `k[X]^ι` adapted to a submodule', file=SC, deps='none', par='yes',
  typ='theorem', leaves='L15.1',
  decls=[(SC,'exists_basis_adaptedFamily')],
  sketch="""Write `P := MvPolynomial σ k`, `W := ι → P`, `G : (σ →₀ ℕ) × Fin r → W := fun a ↦ monomial a.1 1 • h a.2`,
`E : (Σ _ : ι, σ →₀ ℕ) → W := fun b ↦ Pi.single b.1 (monomial b.2 1)`, and `v := Sum.elim G E` on the index
type `J := ((σ →₀ ℕ) × Fin r) ⊕ (Σ _ : ι, σ →₀ ℕ)`.
1. `A₀ := (linearIndepOn_empty k v).extend (Set.empty_subset (Set.range Sum.inl))`: a subset of
   `range Sum.inl`, `LinearIndepOn k v A₀` (`LinearIndepOn.linearIndepOn_extend`), and
   `v '' range Sum.inl ⊆ span k (v '' A₀)` (`LinearIndepOn.subset_span_extend`).
2. `C := h₀.extend (A₀ ⊆ Set.univ)`: `A₀ ⊆ C` (`LinearIndepOn.subset_extend`), `LinearIndepOn k v C`, and
   `range v ⊆ span k (v '' C)`. Moreover `C ∩ range Sum.inl = A₀`: an index `Sum.inl a ∈ C \\ A₀` would make
   `v` dependent on `A₀ ∪ {inl a} ⊆ C`, because `v (inl a) ∈ span k (v '' A₀)` (step 1) while
   `(hC.mono _).notMem_span_of_insert` says it is not (`LinearIndepOn.mono`, `LinearIndepOn.notMem_span_of_insert`).
3. `A := Sum.inl ⁻¹' C`, `B := Sum.inr ⁻¹' C`; the map `A ⊕ B → C` is a bijection and
   `adaptedFamily h A B = v ∘ (that map)`, so `LinearIndependent k (adaptedFamily h A B)`
   (`LinearIndepOn` is `LinearIndependent` of the restriction; `LinearIndependent.comp` with an injective map,
   or `linearIndependent_equiv`).
4. Span `= ⊤`: `range E` spans `W` over `k` — `E` is the basis `Pi.basis fun _ : ι ↦ basisMonomials σ k`
   (`Pi.basis_apply`, `basisMonomials_apply`; `scratch/spot3.lean`, item 6) — and
   `range E ⊆ range v ⊆ span k (v '' C)`.
5. Third conjunct. `span k (range fun a : A ↦ G a) = span k (v '' A₀) = span k (range G)` (step 1 and
   monotonicity), and `span k (range G) = (span P (range h)).restrictScalars k`: `⊆` since
   `monomial ν 1 • h j ∈ span P (range h)`; `⊇` by `Submodule.span_induction` over `P`: the `k`-span of `range G`
   is stable under `p • ·` because `p = ∑ monomial μ (coeff μ p)` (`MvPolynomial.as_sum`) and
   `monomial μ c * monomial ν 1 = monomial (μ + ν) c` (`MvPolynomial.monomial_mul`).""",
  mathlib="""`linearIndepOn_empty`, `LinearIndepOn.extend`, `LinearIndepOn.linearIndepOn_extend`, `LinearIndepOn.subset_extend`, `LinearIndepOn.subset_span_extend`, `LinearIndepOn.mono`, `LinearIndepOn.notMem_span_of_insert`, `Pi.basis`, `MvPolynomial.basisMonomials`, `Module.Basis.span_eq`, `Submodule.span_induction`, `MvPolynomial.as_sum`, `MvPolynomial.monomial_mul`, `Submodule.restrictScalars`.""",
  sources="""[Bo] 1.3/7 and 1.3/10, `bosch-lectures.txt:896–900`, `:973–978`; decomposition L15.1.""",
  gen="""A field `k`, any `σ`, a finite `ι`. The choice is of **index sets** (the family `G` may repeat vectors or contain `0`).""")

t(id='T063', title='The monomial vectors are an orthonormal basis of `T^ι`', file=SC, deps='CLEANUP-2, CLEANUP-21', par='yes (with T062)',
  typ='theorems', leaves='L15.2–L15.4',
  decls=[(SC,'isOrthonormalBasis_monomial'),(SC,'isOrthonormalBasis_single_monomial'),(SC,'hasSum_coeff_smul_single_monomial')],
  sketch="""Private helper in this file (or as a constructor in the proof): to prove the `ℝ≥0` identity of
`IsOrthonormalFamily` it is enough to prove, for every real `C ≥ 0`,
`‖∑ i ∈ s, a i • e i‖ ≤ C ↔ ∀ i ∈ s, ‖a i‖ ≤ C` (then `le_antisymm` with `Finset.sup_le` and
`Finset.le_sup`, using `‖e i‖ = 1`).
1. `isOrthonormalBasis_monomial`.
   - `‖monomial 1 t 1‖ = 1`: `norm_monomial`, `norm_one`, the helper `prod_one_pow` of T004.
   - the coefficient of `∑ t ∈ s, a t • monomial 1 t 1` at `u` is `a u` if `u ∈ s`, else `0`
     (`val_sum`, `val_smul`, `val_monomial`, `MvPowerSeries.coeff_monomial`, `Finset.sum_ite_eq`); the iff is
     then `norm_le_iff_forall_norm_coeff_le`.
   - density: `(denseRange_toRestricted 1).mono`-style: every `toRestricted 1 p` is in the span
     (`MvPolynomial.as_sum`, `map_sum`, `toRestricted_monomial`, `monomial 1 t c = c • monomial 1 t 1`), so the
     span contains a dense set (`Dense.mono`).
2. `isOrthonormalBasis_single_monomial`: `Pi.norm_single` for norm one; the component `i` of
   `∑ p ∈ s, a p • Pi.single p.1 (monomial 1 p.2 1)` is the sum over `p ∈ s` with `p.1 = i`
   (`Finset.sum_apply`, `Pi.smul_apply`, `Pi.single_apply`), so by item 1's computation its coefficient at `u`
   is `a ⟨i, u⟩` if `⟨i, u⟩ ∈ s`, else `0`; `pi_norm_le_iff_of_nonneg` and
   `norm_le_iff_forall_norm_coeff_le`. Density: a tuple is approximated componentwise by tuples of
   polynomials, which lie in the span (`dense_pi`-type argument, or directly with `pi_norm_lt_iff`).
3. `hasSum_coeff_smul_single_monomial`: `Pi.hasSum.2 fun i ↦ ?_`; the `i`-th component of the summand at `p`
   is `monomial 1 p.2 (coeff p.2 (f i).1)` if `p.1 = i`, else `0`;
   `(Function.Injective.hasSum_iff (g := fun t ↦ ⟨i, t⟩) sigma_mk_injective ?_).1 (hasSum_monomial 1 (f i))`,
   the side condition being that the summand vanishes off the fibre over `i`.""",
  mathlib="""`Pi.norm_single`, `Pi.hasSum`, `Function.Injective.hasSum_iff`, `sigma_mk_injective`, `pi_norm_le_iff_of_nonneg`, `pi_norm_lt_iff`, `Finset.sum_apply`, `Pi.single_apply`, `MvPowerSeries.coeff_monomial`, `Dense.mono`. Floor: `Restricted.norm_monomial`, `Restricted.hasSum_monomial`, `Restricted.val_sum`, `Restricted.val_monomial`.""",
  sources="""[Bo] 1.3/5 and 1.3/10, `bosch-lectures.txt:832–833`, `:981–985`; decomposition L15.2–L15.4.""",
  gen="""No completeness. The index type of the basis of `T^ι` is `Σ _ : ι, σ →₀ ℕ`, matching `Pi.basis` on the reduction side.""")

t(id='T064', title='The reduction of a submodule', file=SC, deps='CLEANUP-5', par='no',
  typ='lemma + definition + theorem', leaves='L15.5–L15.7',
  decls=[(SC,'reductionPi_eq_zero_iff'),(SC,'reductionSubmodule'),(SC,'exists_generators_reductionSubmodule')],
  sketch="""1. `reductionPi_eq_zero_iff`: `funext_iff`, `reduction_eq_zero_iff` at each `i`, and
   `pi_norm_lt_iff zero_lt_one`.
2. `reductionSubmodule`, the three fields. `zero_mem'`: `⟨0, by simp, N.zero_mem, by ext; simp [reductionPi]⟩`
   (`map_zero` of `reduction`). `add_mem'`: from `⟨x, hx, hxN, rfl⟩`, `⟨x', hx', hx'N, rfl⟩` take `x + x'`,
   `‖x + x'‖ ≤ max ‖x‖ ‖x'‖ ≤ 1` (the ultrametric instance on `ι → 𝕋` from
   `Mathlib.Topology.MetricSpace.Ultra.Pi`), and componentwise `map_add` of `reduction` (the subtype element
   of a sum is the sum of the subtype elements). `smul_mem'`: for `p` take `P` with `reduction P = p`
   (`reduction_surjective`); `(P : 𝕋) • x ∈ N`, `‖(P : 𝕋) • x‖ ≤ 1` (`pi_norm_le_iff_of_nonneg`,
   `norm_mul_le`, `Subring.norm_le_one`), and componentwise `map_mul`.
3. `exists_generators_reductionSubmodule`: `P := MvPolynomial σ 𝕜` is noetherian
   (`MvPolynomial.isNoetherianRing`, `σ` finite), so `ι → P` is a noetherian module (`isNoetherian_pi`) and
   `reductionSubmodule N` is finitely generated: `obtain ⟨S, hS⟩ := (IsNoetherian.noetherian _)` (a finset
   with span equal to it). `S' := S.erase 0` has the same span. Each `u ∈ S'` is `reductionPi x_u _` with
   `x_u ∈ N`, `‖x_u‖ ≤ 1` (`Submodule.subset_span`, `mem_reductionSubmodule`), and `‖x_u‖ = 1` since `u ≠ 0`
   (item 1). Enumerate `S'` by `S'.equivFin` and choose the lifts (`Classical.choose`); the span of the
   reductions is the span of `S'`.""",
  mathlib="""`pi_norm_lt_iff`, `pi_norm_le_iff_of_nonneg`, `norm_le_pi_norm`, `MvPolynomial.isNoetherianRing`, `isNoetherian_pi`, `IsNoetherian.noetherian`, `Submodule.fg_def`, `Finset.equivFin`, `Submodule.span_sdiff_singleton_zero`.""",
  sources="""[Bo] 1.3/10, `bosch-lectures.txt:968–973`; decomposition L15.5–L15.7.""",
  gen="""`[Finite σ]` only in item 3 (`k[X]` must be noetherian). No completeness.""")

t(id='T065', title='The adapted family is an orthonormal basis', file=SC, deps='CLEANUP-24, CLEANUP-23, CLEANUP-20', par='no',
  typ='theorems', leaves='L15.8, L15.9',
  decls=[(SC,'exists_isBald_forall_coeff_mem'),(SC,'isOrthonormalBasis_adaptedFamily')],
  sketch="""1. `exists_isBald_forall_coeff_mem`: the family
   `a : Fin r × ι × (σ →₀ ℕ) → K := fun q ↦ coeff q.2.2 (g q.1 q.2.1).1`; `‖a q‖ ≤ 1` (`norm_coeff_le`,
   `norm_le_pi_norm`, `hg`); null along the cofinite filter: for `ε > 0` the exceptional set is contained in
   the finite union over `(j, i)` of `{(j, i)} ×ˢ {t | ε ≤ ‖coeff t (g j i).1‖}` (`finite_setOf_le_norm_coeff`,
   `Set.Finite.biUnion`, `Metric.tendsto_nhds` / `Filter.eventually_cofinite`). `Subring.isBald_closure_range`
   and `Subring.subset_closure ⟨_, rfl⟩`.
2. `isOrthonormalBasis_adaptedFamily`: apply `IsOrthonormalBasis.of_residue_basis` (T061) with
   - `x :=` the monomial vectors (`isOrthonormalBasis_single_monomial`);
   - `c μ p := coeff p.2 ((adaptedFamily g A B μ) p.1).1`, so `hy μ := hasSum_coeff_smul_single_monomial _`;
   - `S` from item 1 enlarged by nothing: for `μ = inl a` the coordinates of `monomial 1 ν 1 • g j` are
     coefficients of `g j` or `0` (coefficient of `monomial ν 1 * f` at `t` is `coeff (t - ν) f` if `ν ≤ t`,
     else `0`: `MvPowerSeries.coeff_monomial_mul`), for `μ = inr b` they are `0` or `1`; all in `S`;
   - `r μ := (Pi.basis fun _ : ι ↦ MvPolynomial.basisMonomials σ 𝕜).repr
       (MvPolynomial.adaptedFamily (fun j ↦ reductionPi (g j) _) A B μ)`;
   - `hr`: `r μ p = MvPolynomial.coeff p.2 ((reduced adapted family μ) p.1)` (`Pi.basis_repr`,
     `basisMonomials` coordinates are coefficients), and the reduced adapted family is the reduction of the
     adapted family componentwise: for `inl`, `reduction` is multiplicative and
     `reduction ⟨monomial 1 ν 1, _⟩ = monomial ν 1`; for `inr`, `Pi.single`. Then `coeff_reduction`.
   - `hli`, `hspan` for `r`: transport along the linear equivalence `repr` (`LinearIndependent.map'`,
     `Submodule.map_span`, `LinearEquiv.range`).""",
  mathlib="""`Set.Finite.biUnion`, `Filter.eventually_cofinite`, `MvPowerSeries.coeff_monomial_mul`, `Pi.basis`, `Pi.basis_repr`, `MvPolynomial.basisMonomials`, `LinearIndependent.map'`, `Submodule.map_span`. Board: `Subring.isBald_closure_range`, `IsOrthonormalBasis.of_residue_basis`.""",
  sources="""[Bo] 1.3/10, `bosch-lectures.txt:984–991`; decomposition L15.8, L15.9.""",
  gen="""No completeness. This ticket is the bridge between the index conventions of the Tate side and of the residue side; expect bookkeeping, not mathematics.""")

t(id='T066', title='Regrouping a series in the multiples `X^ν g_j`', file=SC, deps='CLEANUP-2', par='yes (with T062–T065)',
  typ='theorem', leaves='L15.10',
  decls=[(SC,'exists_eq_sum_smul_of_hasSum')],
  sketch="""For `j : Fin r` let `u j : A → 𝕋 := fun μ ↦ if μ.1.2 = j then c μ • monomial 1 μ.1.1 1 else 0`.
1. `‖u j μ‖ ≤ ‖c μ‖` (`norm_smul_eq`, `norm_monomial`, `norm_one`), so `u j → 0` cofinitely (from `hc0`,
   `squeeze_zero_norm`) and `u j` is summable in the complete ultrametric `𝕋`
   (`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`). `q j := ∑' μ, u j μ`.
2. `‖q j‖ ≤ C`: `IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC0 fun μ ↦ (… ).trans (hC μ)`.
3. `HasSum (fun μ ↦ u j μ • g j) (q j • g j)`: `(hasSum of u j).smul_const (g j)` (`ContinuousSMul 𝕋 (ι → 𝕋)`;
   if the instance is not found, argue componentwise with `Pi.hasSum` and `HasSum.mul_right`).
4. `hasSum_sum` over `j`: `HasSum (fun μ ↦ ∑ j, u j μ • g j) (∑ j, q j • g j)`, and
   `∑ j, u j μ • g j = c μ • (monomial 1 μ.1.1 1 • g μ.1.2)` (`Finset.sum_ite_eq`, `smul_assoc`).
5. `HasSum.unique ha` gives `a = ∑ j, q j • g j`.""",
  mathlib="""`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`, `IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg`, `squeeze_zero_norm`, `HasSum.smul_const`, `hasSum_sum`, `HasSum.unique`, `Finset.sum_ite_eq`, `smul_assoc`.""",
  sources="""[Bo] 1.3/7, `bosch-lectures.txt:911–914`; decomposition L15.10.""",
  gen="""`hC0 : 0 ≤ C` (defect D2) and `hc0` (nullity of `c`, supplied by T056 at the call site). `g` is arbitrary here.""")

t(id='T067', title='Elements of `N` have no monomial-vector part', file=SC, deps='T065, T066, T062, T064', par='no',
  typ='theorems', leaves='L15.11, L15.12',
  decls=[(SC,'coeff_inr_eq_zero_of_mem'),(SC,'exists_isOrthonormalBasis_adaptedFamily')],
  sketch="""Write `e := adaptedFamily g A B`, `ẽ := MvPolynomial.adaptedFamily (fun j ↦ reductionPi (g j) _) A B`.

Private lemma (reduction of an expansion): if `HasSum (fun μ ↦ d μ • e μ) z`, `‖d μ‖ ≤ 1` for all `μ` and
`d → 0`, then `‖z‖ ≤ 1` and `reductionPi z _ = ∑ μ ∈ F, residue _ ⟨d μ, _⟩ • ẽ μ` for the finite set
`F := {μ | ‖d μ‖ = 1}`. Proof: `z - ∑ μ ∈ F, d μ • e μ` is the sum of the remaining terms, all of norm `< 1`,
with a largest one (`Filter.Tendsto.exists_forall_norm_le`), so it has norm `< 1`
(`IsUltrametricDist.norm_tsum_lt_of_forall_lt`, or `hON.1.norm_le_of_hasSum` with that largest value); hence
the two reductions agree (`reductionPi_eq_zero_iff` for the difference, additivity), and the reduction of
`d μ • e μ` is `residue (d μ) • ẽ μ` (`reduction` multiplicative, reduction of a constant, `reductionPi` of
the adapted family as in T065).

1. `coeff_inr_eq_zero_of_mem`. `hc0 := hON.1.tendsto_cofinite_of_hasSum hc`.
   - `A`-part: `x' := ∑' a : A, c (inl a) • e (inl a)` (summable: `hON.1.summable_smul` composed with `inl`);
     by T066 with `C := ‖x‖` (`hON.1.norm_coeff_le_of_hasSum hc`), `x' = ∑ j, q j • g j ∈ N`.
   - `x'' := x - x' ∈ N` has the expansion with coefficients `c'' := fun μ ↦ Sum.elim (fun _ ↦ 0) (c ∘ inr) μ`
     (`HasSum.sub hc` and `Function.Injective.hasSum_iff Sum.inl_injective` for the `A`-part).
   - Suppose `c (inr b) ≠ 0`. Let `b₁` maximise `‖c (inr ·)‖` (`Filter.Tendsto.exists_forall_norm_le` on
     `c ∘ inr`), `d := c (inr b₁) ≠ 0`; `z := d⁻¹ • x'' ∈ N`, with coefficients `d⁻¹ * c''` of norm `≤ 1`, equal
     to `1` at `inr b₁`. By the private lemma, `w := reductionPi z _` is a combination of the `ẽ (inr b)` with
     coefficient `1` at `b₁`, so `w ≠ 0` (`hli`, `linearIndependent_iff'`) and
     `w ∈ span 𝕜 (ẽ '' range inr)`.
   - `w ∈ reductionSubmodule N` (definition), so by `hA`, `w ∈ span 𝕜 (ẽ '' range inl)`.
   - `hli.disjoint_span_image` (ranges of `inl` and `inr` are disjoint) forces `w = 0`. Contradiction.
2. `exists_isOrthonormalBasis_adaptedFamily`: the assembly of `scratch/spot4.lean`, first example, which
   compiles against the skeleton: `exists_generators_reductionSubmodule N`,
   `MvPolynomial.exists_basis_adaptedFamily`, `isOrthonormalBasis_adaptedFamily`, item 1 with
   `hA.trans (by rw [hspan])`.""",
  mathlib="""`Function.Injective.hasSum_iff`, `HasSum.sub`, `Sum.inl_injective`, `LinearIndependent.disjoint_span_image`, `linearIndependent_iff'`, `Submodule.disjoint_def`. Chain: `Filter.Tendsto.exists_forall_norm_le`, `IsUltrametricDist.norm_tsum_lt_of_forall_lt`, `IsOrthonormalFamily.summable_smul`, `IsOrthonormalFamily.tendsto_cofinite_of_hasSum`, `IsOrthonormalFamily.norm_coeff_le_of_hasSum`, `IsOrthonormalFamily.norm_le_of_hasSum`.""",
  sources="""[Bo] 1.3/7, `bosch-lectures.txt:907–934`; decomposition L15.11, L15.12.""",
  gen="""`K` complete (the `A`-part must converge and be regrouped). The deepest ticket of the board; the private lemma is the reusable part.""")

t(id='T068', title='Generators with a nearest point', file=SC, deps='CLEANUP-25', par='no',
  typ='theorem', leaves='L15.13',
  decls=[(SC,'exists_generators_forall_exists_isNearest')],
  sketch="""`classical`; `obtain ⟨r, g, A, B, hgN, hg, hON, hN⟩ := exists_isOrthonormalBasis_adaptedFamily N`;
`refine ⟨r, g, hgN, hg, fun f ↦ ?_⟩`. Let `e := adaptedFamily g A B`.
1. `obtain ⟨c, hc⟩ := hON.exists_hasSum f` (`K` and `ι → 𝕋` complete), `hc0 := hON.1.tendsto_cofinite_of_hasSum hc`,
   `‖c μ‖ ≤ ‖f‖` (`hON.1.norm_coeff_le_of_hasSum hc`).
2. `A`-part: `f_A := ∑' a : A, c (inl a) • e (inl a)`; T066 with `C := ‖f‖` gives `q` with `‖q j‖ ≤ ‖f‖` and
   `f_A = ∑ j, q j • g j`. Use this `q`.
3. `f_B := f - f_A` has the expansion with coefficients `c_B := Sum.elim (fun _ ↦ 0) (c ∘ inr)` (as in T067).
4. For `a ∈ N`: `obtain ⟨d, hd⟩ := hON.exists_hasSum a`, and `d (inr b) = 0` for all `b` (`hN a ha d hd`).
   Then `f_B - a` has coefficients `c_B - d`, equal to `c (inr b)` at `inr b`. So every coefficient of `f_B`
   (namely `0` at `inl`, `c (inr b)` at `inr b`) has norm `≤ ‖f_B - a‖`
   (`hON.1.norm_coeff_le_of_hasSum (hsum of f_B - a)`), and `hON.1.norm_le_of_hasSum (hsum of f_B)
   (norm_nonneg _) _` gives `‖f_B‖ ≤ ‖f_B - a‖`.""",
  mathlib="""`HasSum.sub`, `Function.Injective.hasSum_iff`, `Sum.inl_injective`. Chain: `IsOrthonormalBasis.exists_hasSum`, `IsOrthonormalFamily.norm_coeff_le_of_hasSum`, `IsOrthonormalFamily.norm_le_of_hasSum`, `IsOrthonormalFamily.tendsto_cofinite_of_hasSum`.""",
  sources="""[Bo] 1.3/9, `bosch-lectures.txt:944–954`; 1.3/10, `:956–993`; decomposition L15.13.""",
  gen="""One statement from which Bosch 1.3/7–1.3/10 and BGR 5.2.7/8 are read off. `DecidableEq ι` is not in the statement; open `classical`.""")

t(id='T069', title='Submodules of `T^ι` are strictly closed', file=SC, deps='T068', par='no',
  typ='theorems', leaves='L15.14–L15.17',
  decls=[(SC,'exists_generators_norm_le'),(SC,'exists_forall_norm_sub_le'),(SC,'isClosed_submodule'),(SC,'infDist_mem_range_norm')],
  sketch="""1. `exists_generators_norm_le`: the second example of `scratch/spot4.lean` (compiles): apply T068 to `x ∈ N`;
   the nearest-point inequality at `a := x - ∑ j, q j • g j ∈ N` gives `‖x - ∑ …‖ ≤ 0`.
2. `exists_forall_norm_sub_le`: from T068, `a₀ := ∑ j, q j • g j ∈ N` (`N.sum_mem`, `N.smul_mem`); for
   `a ∈ N` apply the inequality to `a - a₀ ∈ N`: `f - a₀ - (a - a₀) = f - a` (`sub_sub_sub_cancel_right`).
3. `isClosed_submodule`: `isClosed_of_closure_subset fun f hf ↦ ?_`; take `a₀` from item 2;
   `Metric.mem_closure_iff.1 hf ε` gives `a ∈ N` with `dist f a < ε`, so `‖f - a₀‖ < ε` for every `ε > 0`,
   hence `f = a₀ ∈ N` (`le_of_forall_pos_lt_add`-style, `norm_le_zero_iff`, `sub_eq_zero`).
4. `infDist_mem_range_norm`: with `a₀` from item 2, `Metric.infDist f N = ‖f - a₀‖`
   (`le_antisymm (Metric.infDist_le_dist_of_mem a₀.2) ((Metric.le_infDist ⟨0, N.zero_mem⟩).2 _)`,
   `dist_eq_norm`). Then `‖f - a₀‖ ∈ range norm`: `rcases isEmpty_or_nonempty ι`; empty: the norm is `0`
   (`⟨0, norm_zero⟩`); nonempty: `Pi.norm_def`, `Finset.exists_mem_eq_sup` give `i` with
   `‖f - a₀‖ = ‖(f - a₀) i‖`, and `norm_mem_range_norm`.""",
  mathlib="""`Submodule.sum_mem`, `Submodule.smul_mem`, `Submodule.sub_mem`, `isClosed_of_closure_subset`, `Metric.mem_closure_iff`, `Metric.infDist_le_dist_of_mem`, `Metric.le_infDist`, `Pi.norm_def`, `Finset.exists_mem_eq_sup`, `dist_eq_norm`.""",
  sources="""[Bo] 1.3/8–10, `bosch-lectures.txt:935–967`; [BGR] 5.2.7/1, 5.2.7/7, 5.2.7/8, `bgr-5.2.md:403–420`, `:486–493`; decomposition L15.14–L15.17.""",
  gen="""Submodules of a finite free module with the maximum norm. Closedness is read off strict closedness (Bosch sums series instead).""")

t(id='T070', title='Ideals of the Tate algebra are strictly closed', file=SC, deps='CLEANUP-ALL-3', par='no',
  typ='theorems (milestone M3)', leaves='L15.18–L15.21', milestone='M3',
  decls=[(SC,'exists_generators_norm_le_ideal'),(SC,'exists_forall_norm_sub_le_ideal'),(SC,'isClosed_ideal'),(SC,'norm_quotient_mk_mem_range_norm')],
  sketch="""Specialise T069 to `ι := Unit` and `N := Submodule.comap (LinearMap.proj () : (Unit → 𝕋) →ₗ[𝕋] 𝕋) I`
(`x ∈ N ↔ x () ∈ I`); for `x : Unit → 𝕋`, `‖x‖ = ‖x ()‖` (`Pi.norm_def`, `Finset.univ_unique`,
`Finset.sup_singleton`), and `x = fun _ ↦ x ()`.
1. `exists_generators_norm_le_ideal`: from `exists_generators_norm_le N` take `g' j := g j ()`; for `x ∈ I`
   apply it to `fun _ ↦ x` and evaluate at `()` (`Finset.sum_apply`, `Pi.smul_apply`, `smul_eq_mul`).
2. `exists_forall_norm_sub_le_ideal`: from `exists_forall_norm_sub_le N (fun _ ↦ f)`, `a₀ ()`; for `a ∈ I`
   use `fun _ ↦ a`.
3. `isClosed_ideal`: as T069 item 3, from item 2, or the preimage of `isClosed_submodule N`
   under the continuous map `f ↦ fun _ ↦ f`.
4. `norm_quotient_mk_mem_range_norm`: the quotient seminorm is the distance to `I`
   (`QuotientAddGroup.norm_mk`, after unfolding the `Ideal.Quotient` norm instance; `Metric.infDist_eq_iInf`
   if needed); with `a₀` from item 2, the distance is `‖f - a₀‖` as in T069 item 4; `norm_mem_range_norm`.""",
  mathlib="""`LinearMap.proj`, `Submodule.comap`, `Pi.norm_def`, `Finset.sup_singleton`, `QuotientAddGroup.norm_mk`, `Metric.infDist_le_dist_of_mem`, `Metric.le_infDist`, `Metric.mem_closure_iff`.""",
  sources="""[Bo] 1.3/7–9, `bosch-lectures.txt:885–954`; [BGR] 5.2.7/2, 5.2.7/8, `bgr-5.2.md:418`, `:492–493`; [RM] §0.3.1; decomposition L15.18–L15.21.""",
  gen="""Milestone M3. `σ` finite, `K` complete. The quotient norm on `𝕋 ⧸ I` is Mathlib's seminorm, defined for every ideal; item 3 makes it a norm.""")

# ---------------------------------------------------------------- G16 WeaklyStable
t(id='T071', title='Bounded functionals that separate points are all functionals', file=WS, deps='none', par='yes',
  typ='theorem', leaves='L16.1',
  decls=[(WS,'Module.Dual.exists_bound_of_forall_exists_ne_zero')],
  sketch="""`W : Submodule K (Module.Dual K V)` with carrier `{φ | ∃ C : ℝ, ∀ y, ‖φ y‖ ≤ C * N y}`:
- `zero_mem'`: `⟨0, fun y ↦ by simp⟩`.
- `add_mem'`: from `C₁`, `C₂` take `C₁ + C₂`: `norm_add_le` and `add_mul` (no sign condition on `N`).
- `smul_mem'`: from `C` take `‖a‖ * C`: `norm_mul`, `mul_assoc`, `mul_le_mul_of_nonneg_left`.
Then `W.dualCoannihilator = ⊥`: `eq_bot_iff`; if `x` is killed by all of `W` and `x ≠ 0`, `h x` gives
`φ ∈ W` with `φ x ≠ 0` (`Submodule.mem_dualCoannihilator`). Hence
`W = W.dualCoannihilator.dualAnnihilator = ⊤` (`Subspace.dualAnnihilator_dualCoannihilator_eq`,
`Submodule.dualAnnihilator_bot`), and `ψ ∈ W`.""",
  mathlib="""`Subspace.dualAnnihilator_dualCoannihilator_eq`, `Submodule.dualCoannihilator`, `Submodule.mem_dualCoannihilator`, `Submodule.dualAnnihilator_bot`.""",
  sources="""[BGR] 2.3.1/2–3, `bgr-2.md:121–133`; decomposition L16.1.""",
  gen="""`N : V → ℝ` is an arbitrary function: the proof uses none of its properties. Finite dimension is necessary.""")

t(id='T072', title='The trace is a contraction; separable extensions are weakly cartesian', file=WS, deps='T071', par='no',
  typ='theorems', leaves='L16.2, L16.3',
  decls=[(WS,'norm_trace_le_spectralNorm'),(WS,'exists_bound_of_isSeparable')],
  sketch="""1. `norm_trace_le_spectralNorm`: `q := minpoly K x`, `r := q.natDegree ≥ 1` (`minpoly.natDegree_pos`, `x`
   integral: `Algebra.IsIntegral.isIntegral`).
   `rw [trace_eq_finrank_mul_minpoly_nextCoeff]`: the trace is `(finrank K⟮x⟯ L : K) * -q.nextCoeff`; `norm_mul`,
   `norm_neg`, and `‖(n : K)‖ ≤ 1` (`IsUltrametricDist.norm_natCast_le_one`) reduce to
   `‖q.nextCoeff‖ ≤ spectralNorm K L x`. `Polynomial.nextCoeff_of_natDegree_pos` gives
   `q.nextCoeff = q.coeff (r - 1)`. `spectralNorm K L x = spectralValue q` (definition), and
   `le_ciSup (spectralValueTerms_bddAbove q) (r - 1)` with `spectralValueTerms_of_lt_natDegree`
   (`r - 1 < r`): the term is `‖q.coeff (r - 1)‖ ^ (1 / (r - (r - 1) : ℝ)) = ‖q.coeff (r - 1)‖`
   (`Nat.cast_sub`, `sub_sub_cancel`, `div_one`, `Real.rpow_one`).
2. `exists_bound_of_isSeparable`: `Module.Dual.exists_bound_of_forall_exists_ne_zero (spectralNorm K L) ?_ φ`.
   For `x ≠ 0`: the trace form is nondegenerate (`traceForm_nondegenerate K L`), so there is `y₀` with
   `Algebra.trace K L (x * y₀) ≠ 0`. `φₓ := (Algebra.trace K L).comp (LinearMap.mulRight K y₀)`, bounded by
   `C := spectralNorm K L y₀`: item 1 and `map_mul_le_mul (spectralAlgNorm K L) y y₀`
   (`spectralAlgNorm K L z = spectralNorm K L z` by `rfl`), `mul_comm`.""",
  mathlib="""`trace_eq_finrank_mul_minpoly_nextCoeff`, `Polynomial.nextCoeff_of_natDegree_pos`, `minpoly.natDegree_pos`, `IsUltrametricDist.norm_natCast_le_one`, `spectralValueTerms_of_lt_natDegree`, `spectralValueTerms_bddAbove`, `le_ciSup`, `Real.rpow_one`, `traceForm_nondegenerate`, `LinearMap.BilinForm.Nondegenerate`, `spectralAlgNorm`, `map_mul_le_mul`, `LinearMap.mulRight`.""",
  sources="""[BGR] 3.2.3/2, `bgr-3.2.md:49–54`; 3.5.1/3, `bgr-3.5.md:57–64`; decomposition L16.2, L16.3.""",
  gen="""A nonarchimedean normed field, not complete, possibly trivially valued. Ultrametricity is necessary for item 1.""")

t(id='T073', title='Perfect fields and complete fields are weakly stable', file=WS, deps='T072', par='no',
  typ='theorems', leaves='L16.4, L16.5',
  decls=[(WS,'isWeaklyStable_of_perfectField'),(WS,'isWeaklyStable_of_completeSpace')],
  sketch="""1. `isWeaklyStable_of_perfectField`: `intro L _ _ _ φ`;
   `haveI : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField`;
   `exact exists_bound_of_isSeparable φ`.
2. `isWeaklyStable_of_completeSpace`: `intro L _ _ _ φ`; `letI := spectralNorm.normedField K L`;
   `letI := spectralNorm.normedAlgebra K L`; then `L` is a finite-dimensional normed space over the complete
   field `K`, `φ' := LinearMap.toContinuousLinearMap φ`, and `⟨‖φ'‖, fun y ↦ φ'.le_opNorm y⟩` after
   identifying `‖y‖` with `spectralNorm K L y` (`rfl`, or `(NormedAlgebra.norm_eq_spectralNorm K y)`).""",
  mathlib="""`Algebra.IsAlgebraic.isSeparable_of_perfectField`, `spectralNorm.normedField`, `spectralNorm.normedAlgebra`, `LinearMap.toContinuousLinearMap`, `ContinuousLinearMap.le_opNorm`, `NormedAlgebra.norm_eq_spectralNorm`.""",
  sources="""[BGR] 3.5.1/4, 3.5.2, `bgr-3.5.md:66–71`, `:80–90`; 2.3.3/4, `bgr-2.md:217–224`; decomposition L16.4, L16.5.""",
  gen="""Item 2 needs `NontriviallyNormedField` (Mathlib's finite-dimensional continuity). `IsWeaklyStable` quantifies over extensions in the universe of `K`.""")

t(id='T074', title='The norm of a fraction field', file=WS, deps='CLEANUP-27', par='yes (with T071–T073)',
  typ='definition + lemmas', leaves='L16.6–L16.8',
  decls=[(WS,'normAbsoluteValue'),(WS,'normAbsoluteValue_algebraMap'),(WS,'normAbsoluteValue_div')],
  sketch="""`A` is a domain (`NormMulClass.toNoZeroDivisors`, `Nontrivial A`), and `algebraMap A Q` is injective
(`IsFractionRing.injective A Q`).

Private lemma about the raw function `ν q := ‖(IsLocalization.sec (nonZeroDivisors A) q).1‖ /
‖((IsLocalization.sec (nonZeroDivisors A) q).2 : A)‖`:
`ν_div (a) {b} (hb : b ≠ 0) : ν (algebraMap A Q a / algebraMap A Q b) = ‖a‖ / ‖b‖`. Proof:
`IsLocalization.sec_spec` gives `q * algebraMap s = algebraMap r`; with `q = a / b` and injectivity,
`a * s = r * b` in `A`; `norm_mul` twice and `div_eq_div_iff` (`‖s‖ ≠ 0`, `‖b‖ ≠ 0`).

1. `normAbsoluteValue`, the four fields; every `q` is `a / b` (`IsFractionRing.div_surjective`).
   `map_mul'`: `(a / b) * (c / d) = (a * c) / (b * d)` (`div_mul_div_comm`, `map_mul`), `ν_div` three times,
   `norm_mul`. `nonneg'`: `div_nonneg`. `eq_zero'`: `ν (a / b) = 0 ↔ ‖a‖ = 0 ↔ a = 0 ↔ a / b = 0`.
   `add_le'`: `a / b + c / d = (a * d + c * b) / (b * d)` (`div_add_div`), `ν_div`, `norm_add_le`,
   `norm_mul`, and division by `‖b‖ * ‖d‖ > 0`.
2. `normAbsoluteValue_div`: `ν_div`. `normAbsoluteValue_algebraMap`: the case `b = 1` (`map_one`, `div_one`,
   `norm_one` — `NormOneClass A` follows from `NormMulClass` and nontriviality: `norm_one` may need
   `NormMulClass.toNormOneClass`; otherwise use `ν_div a one_ne_zero` and `‖(1 : A)‖ = 1` from
   `‖1‖ * ‖1‖ = ‖1‖`).""",
  mathlib="""`IsLocalization.sec`, `IsLocalization.sec_spec`, `IsFractionRing.injective`, `IsFractionRing.div_surjective`, `NormMulClass.toNoZeroDivisors`, `div_eq_div_iff`, `div_mul_div_comm`, `div_add_div`, `norm_mul`.""",
  sources="""[BGR] `bgr-3.5.md:143–144` ("the valuation on `K` extends the valuation on `A`"); `bgr-5.2.md:495–497`; decomposition L16.6–L16.8.""",
  gen="""Any normed commutative ring with multiplicative norm and any model `Q` of its fraction field (`IsFractionRing A Q`). The hypotheses are explicit binders (defect D6).""")

t(id='T075', title='The fraction-field norm is nonarchimedean', file=WS, deps='T074', par='no',
  typ='theorems', leaves='L16.9, L16.10',
  decls=[(WS,'isNonarchimedean_normAbsoluteValue'),(WS,'isUltrametricDist')],
  sketch="""1. `isNonarchimedean_normAbsoluteValue`: for `q = a / b`, `q' = c / d`:
   `q + q' = (a * d + c * b) / (b * d)`; `normAbsoluteValue_div`; `‖a * d + c * b‖ ≤ max ‖a * d‖ ‖c * b‖`
   (`IsUltrametricDist.norm_add_le_max`); divide by `‖b‖ * ‖d‖` and simplify each branch of the `max`
   (`max_div_div_right`, `mul_div_mul_right`).
2. `IsFractionRing.isUltrametricDist`: `letI := normedField A Q`;
   `IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ isNonarchimedean_normAbsoluteValue A Q x y`
   (the norm of `AbsoluteValue.toNormedField` is the absolute value, by `rfl`).""",
  mathlib="""`IsUltrametricDist.norm_add_le_max`, `IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm`, `AbsoluteValue.toNormedField`, `max_div_div_right`, `IsNonarchimedean`.""",
  sources="""[BGR] `bgr-3.5.md:143–144`; decomposition L16.9, L16.10.""",
  gen="""`IsFractionRing.normedField` is a reducible definition, not an instance; statements introduce it with `letI`.""")

# ---------------------------------------------------------------- G17 Japanese
t(id='T076', title='Dedekind: perfect fraction field implies Japanese', file=JAP, deps='none', par='yes',
  typ='theorem', leaves='L17.1',
  decls=[(JAP,'isJapaneseRing_of_perfectField')],
  sketch="""`intro L _ _ _ _ _`;
`haveI : Algebra.IsSeparable (FractionRing A) L := Algebra.IsAlgebraic.isSeparable_of_perfectField`;
`exact IsIntegralClosure.finite A (FractionRing A) L (integralClosure A L)`.
The instance `IsIntegralClosure (integralClosure A L) A L` is `integralClosure.isIntegralClosure`; the scalar
tower `A → integralClosure A L → L` is the subalgebra's.""",
  mathlib="""`IsIntegralClosure.finite`, `integralClosure.isIntegralClosure`, `Algebra.IsAlgebraic.isSeparable_of_perfectField`.""",
  sources="""[BGR] 4.2/1, 4.3/1–2, `bgr-4.md:106–119`, `:126–138`; decomposition L17.1.""",
  gen="""`IsJapaneseRing A` is a `Prop` on the domain, with the extension `L : Type u` given as an algebra over `A` and over `FractionRing A` with a scalar tower.""")

# ---------------------------------------------------------------- G18 Stable
t(id='T077', title='`Q(Tₙ)` is weakly stable and `Tₙ` is Japanese, in characteristic zero', file=ST, deps='CLEANUP-ALL-4', par='no',
  typ='theorems (milestone M4)', leaves='L18.1, L18.2', milestone='M4',
  decls=[(ST,'isWeaklyStable_fractionRing'),(ST,'isJapaneseRing')],
  sketch="""Both proofs compile against the skeleton (`scratch/spot5.lean`).
1. `isWeaklyStable_fractionRing`:
   `letI := IsFractionRing.normedField (TateAlgebra K n) (FractionRing (TateAlgebra K n))`;
   `haveI := IsFractionRing.isUltrametricDist (TateAlgebra K n) (FractionRing (TateAlgebra K n))`;
   `exact isWeaklyStable_of_perfectField _`. The instances used: `CharZero (TateAlgebra K n)` (T002),
   Mathlib's `IsFractionRing.charZero` and `PerfectField.ofCharZero`, `NormMulClass` and `Nontrivial` on the
   Tate algebra (floor, T002).
2. `isJapaneseRing`: `isJapaneseRing_of_perfectField _`, with `IsDomain` (T002), `IsNoetherianRing` and
   `UniqueFactorizationMonoid` (T050; normality by `inferInstance`).""",
  mathlib="""`PerfectField.ofCharZero`, `IsFractionRing.charZero`.""",
  sources="""[BGR] 5.3.1/1, 5.3.1/3, `bgr-5.3.1.md:38–41`, `:89–92`; decomposition L18.1, L18.2.""",
  gen="""Milestone M4. Characteristic zero only: the characteristic-`p` case is BGR 5.3.1/2 with Part A's b-separable modules and is **not on this board** (plan, "Not on this board"). Item 1 holds without completeness of `K` (`omit [CompleteSpace K]`).""")

# ---------------------------------------------------------------- G19 Examples
t(id='T078', title='Examples: variables, a chart, a rational point', file=EX, deps='CLEANUP-15, CLEANUP-9', par='no',
  typ='examples', leaves='L19.1–L19.4',
  decls=[(EX,'norm_X'),(EX,'not_isMulDistinguishedX0_X_one'),(EX,'isMulDistinguishedX0_shear_X_one'),(EX,'isMaximal_ker_aeval')],
  sketch="""1. `norm_X`: `rw [Restricted.norm_X, norm_one, one_mul]; rfl` (the polyradius is `1`).
2. `not_isMulDistinguishedX0_X_one`: `X K 1 1 = ofTail K 1 (X K 1 0)` (`(ofTail_X 0).symm`, `Fin.succ_zero_eq_one`).
   Suppose distinguished of order `s`; `isMulDistinguishedX0_iff` gives `IsUnit (coeffX0 _ s)`, and
   `coeffX0 (ofTail K 1 f) s = (Polynomial.C f).coeff s` (`coeffX0_ofPolynomial`). `s = 0`: the variable of
   `T₁` is not a unit — `Restricted.norm_coeff_lt_norm_constantCoeff_of_isUnit` (floor) at `t = single 0 1`
   would give `1 < 0`, or use `isUnit_iff` and `coeff 0 (X 0) = 0`. `s > 0`: the coefficient is `0`
   (`Polynomial.coeff_C`), `not_isUnit_zero`.
3. `isMulDistinguishedX0_shear_X_one`: `shear_X_succ (fun _ ↦ 1) 0` and `pow_one` give
   `X 1 + X 0 = ofPolynomial K 1 (Polynomial.X + Polynomial.C (X K 1 0))` (`map_add`, `ofPolynomial_X`,
   `ofTail_X`); `ω := X + C a` is monic of `natDegree 1` (`Polynomial.monic_X_add_C`,
   `Polynomial.natDegree_X_add_C`) with coefficients of norm `≤ 1`, so `isWeierstrassPolynomial_iff` and
   `IsWeierstrassPolynomial.isMulDistinguishedX0`.
4. `isMaximal_ker_aeval`: `haveI : Algebra.IsAlgebraic K K := Algebra.IsAlgebraic.of_finite K K`;
   `exact Affinoid.isMaximal_ker_of_isAlgebraic _`.""",
  mathlib="""`Polynomial.monic_X_add_C`, `Polynomial.natDegree_X_add_C`, `Polynomial.coeff_C`, `Fin.succ_zero_eq_one`, `not_isUnit_zero`, `Algebra.IsAlgebraic.of_finite`. Floor: `Restricted.norm_X`, `Restricted.norm_coeff_lt_norm_constantCoeff_of_isUnit`.""",
  sources="""[RM] Layer 0, Examples; [BGR] 5.1.3 Example, 5.2.4; decomposition L19.1–L19.4.""",
  gen="""The chart example is the variable that is not the distinguished one (the roadmap's `X₁ − X₂` is already distinguished: erratum E12). The generators of the maximal ideal of a rational point are Layer 3.""")

t(id='T079', title='Examples over `ℚ_[p]`: a unit and a reduction', file=EX, deps='T078', par='no',
  typ='examples', leaves='L19.5–L19.7',
  decls=[(EX,'norm_one_add_p_mul_X'),(EX,'isUnit_one_add_p_mul_X'),(EX,'reduction_p_add_X_add_p_mul_X_sq')],
  sketch="""`hp : ‖(p : ℚ_[p])‖ < 1`: `Padic.norm_p` and `inv_lt_one_of_one_lt₀` (`1 < (p : ℝ)`, `Nat.Prime.one_lt`).
`hu : ‖C 1 (p : ℚ_[p]) * X ℚ_[p] 1 0‖ < 1`: `norm_mul`, `norm_C`, `norm_X` (T078), `mul_one`.
1. `norm_one_add_p_mul_X`: `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` (`‖1‖ = 1 ≠ ‖…‖`), `norm_one`,
   `max_eq_left hu.le`.
2. `isUnit_one_add_p_mul_X`: `1 + u = 1 - (-u)` and `isUnit_one_sub_of_norm_lt_one (by rwa [norm_neg])`
   (`ℚ_[p]` is complete, so the Tate algebra is).
3. `reduction_p_add_X_add_p_mul_X_sq`: in the subring, the element is
   `⟨C 1 p, _⟩ + ⟨X 0, _⟩ + ⟨C 1 p, _⟩ * ⟨X 0, _⟩ ^ 2` (`Subtype.ext`); `map_add`, `map_mul`, `map_pow`;
   `reduction ⟨C 1 p, _⟩ = 0` by `reduction_eq_zero_iff` (`norm_C`, `hp`); `reduction ⟨X 0, _⟩ = X 0` (the
   coefficientwise lemma of T042, or `MvPolynomial.ext` directly); `zero_add`, `zero_mul`, `add_zero`.""",
  mathlib="""`Padic.norm_p`, `inv_lt_one_of_one_lt₀`, `Nat.Prime.one_lt`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, `isUnit_one_sub_of_norm_lt_one`. Floor: `Restricted.norm_C`.""",
  sources="""[RM] Layer 0, Examples; decomposition L19.5–L19.7.""",
  gen="""`padicNormE.norm_p` no longer exists at the pin; the name is `Padic.norm_p`.""")

t(id='T080', title='Examples over `ℚ_[p]`: a Weierstrass polynomial and a quadratic point', file=EX, deps='T079, CLEANUP-13', par='no',
  typ='examples', leaves='L19.8, L19.9',
  decls=[(EX,'isWeierstrassPolynomial_example'),(EX,'isMaximal_span_X_sq_sub_p')],
  sketch="""1. `isWeierstrassPolynomial_example`: `isWeierstrassPolynomial_iff.2 ⟨?_, fun i ↦ ?_⟩`. Monic:
   `X ^ 2 - (C a * X + C b)` with `Polynomial.monic_X_pow_sub` (`degree (C a * X + C b) < 2`,
   `Polynomial.degree_linear_le`), after `sub_sub`. Coefficients: `0`, `1`, `-a`, `-b` with
   `a = C 1 p * X 0`, `b = C 1 p`, of norm `≤ 1` (`norm_neg`, `norm_mul`, `norm_C`, `norm_X`, `Padic.norm_p`);
   compute them with `Polynomial.coeff_sub`, `coeff_X_pow`, `coeff_C_mul_X`, `coeff_C` and a case split on `i`.
2. `isMaximal_span_X_sq_sub_p`. `ω := X ^ 2 - C (C 1 p) : (TateAlgebra ℚ_[p] 0)[X]`.
   - `ω` is a Weierstrass polynomial (as in item 1), so `bijective_quotientMap` (T035) gives a ring
     isomorphism `(TateAlgebra ℚ_[p] 0)[X] ⧸ span {ω} ≃+* TateAlgebra ℚ_[p] 1 ⧸ (span {ω}).map (ofPolynomial _ 0)`
     (`RingEquiv.ofBijective`), and `(span {ω}).map (ofPolynomial _ 0) = span {ofPolynomial _ 0 ω}`
     (`Ideal.map_span`, `Set.image_singleton`).
   - `span {ω}` is maximal: transport along `Polynomial.mapEquiv (Restricted.isEmptyEquiv ℚ_[p] 1)` to
     `span {X ^ 2 - C (p : ℚ_[p])}` in `ℚ_[p][X]` (`Ideal.map_isMaximal_of_equiv` for the inverse,
     `Polynomial.map_sub`, `map_pow`, `map_X`, `map_C`, `isEmptyEquiv` of a constant), which is maximal by
     `PrincipalIdealRing.isMaximal_of_irreducible` once `X ^ 2 - C p` is irreducible:
     `Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three` (monic of `natDegree 2`) and no root:
     `a ^ 2 = p` would give `‖a‖ ^ 2 = (p : ℝ)⁻¹`, but `‖a‖ = (p : ℝ) ^ (-a.valuation)`
     (`Padic.norm_eq_zpow_neg_valuation`), so `2 * a.valuation = 1` in `ℤ` (`zpow_right_injective₀`), absurd
     (`omega`).
   - a quotient by a maximal ideal is a field; fields transfer along the ring isomorphism
     (`MulEquiv.isField`); `Ideal.Quotient.maximal_of_isField`; rewrite the ideal.""",
  mathlib="""`Polynomial.monic_X_pow_sub`, `Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three`, `PrincipalIdealRing.isMaximal_of_irreducible`, `Ideal.map_isMaximal_of_equiv`, `Polynomial.mapEquiv`, `RingEquiv.ofBijective`, `MulEquiv.isField`, `Ideal.Quotient.maximal_of_isField`, `Ideal.map_span`, `Padic.norm_eq_zpow_neg_valuation`, `Padic.norm_p`, `zpow_right_injective₀`.""",
  sources="""[RM] Layer 0, Examples (the Weierstrass polynomial `X₂² − pX₁X₂ − p`; a maximal ideal with a quadratic residue field); decomposition L19.8, L19.9.""",
  gen="""The quadratic point is `(X² − p) ⊂ T₁` over `ℚ_[p]` for every prime `p`, including `p = 2`. The example "`Q(T₁)` is not complete" of the roadmap is not here (erratum E9).""")

# ---------------------------------------------------------------- End
t(id='T081', title='Add the layer to the chain root', file='PhD/TauCeti.lean', deps='all final per-file cleanups (CLEANUP-2, -5, -7, -8, -9, -10, -12, -13, -15, -17, -18, -20, -21, -23, -26, -28, -29, -30, -31)', par='no',
  typ='build', leaves='—',
  decls=[],
  statement_override="""-- appended to PhD/TauCeti.lean (append-only; another board may be editing the same file)
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Examples""",
  sketch="""1. `grep -rn "sorry" PhD/TauCeti/Code/RigidAnalyticGeometry PhD/TauCeti/Code/PadicFunctionalAnalysis/Orthonormal.lean`
   must be empty.
2. Append the import line above to `PhD/TauCeti.lean`, keeping the file's ordering convention (re-read the
   file first; do not reorder or remove other boards' lines). `TateAlgebra.Examples` imports every file of
   the board, including `PadicFunctionalAnalysis/Orthonormal.lean`.
3. `lake build PhD.TauCeti` (never `lake build PhD`). Check the CI import rule:
   `grep -rn "import PhD.Main" PhD/TauCeti` is empty.
4. `#print axioms` on the four milestone declarations and on `ringKrullDim_eq`.""",
  mathlib="""none.""",
  sources="""plan.md, "Build and verification protocol".""",
  gen="""The root lists leaf modules only.""")
