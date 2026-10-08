# -*- coding: utf-8 -*-
"""Ticket data for the board `tauceti-rag-layer1`. Statements are NOT stored here: the generator
copies them verbatim from the skeleton (through sorries.json). A ticket lists its declarations as
(file, name) or (file, name, occurrence)."""

ALG = 'Restricted/Algebra.lean'
EV = 'TateAlgebra/Eval.lean'
PB = 'PadicFunctionalAnalysis/PowerBounded.lean'
NQ = 'NormedQuotient.lean'
SUM = 'Restricted/Sum.lean'
BAS = 'Affinoid/Basic.lean'
EXT = 'Affinoid/Extend.lean'
NOE = 'BanachAlgebra/Noetherian.lean'
BCO = 'BanachAlgebra/Continuity.lean'
NTH = 'Affinoid/Noether.lean'
ACO = 'Affinoid/Continuity.lean'
TEN = 'Affinoid/Tensor.lean'
FRA = 'Affinoid/Fractions.lean'
BCH = 'Affinoid/BaseChange.lean'
POL = 'Affinoid/Polydisc.lean'
EXA = 'Affinoid/Examples.lean'

T = []  # proof tickets, in board order

def t(**kw):
    T.append(kw)

# ---------------------------------------------------------------- G0 floor restoration (M1)
t(id='T001', title='`K`-scalars on `Restricted S c`: restrictedness and the algebra map', file=ALG, deps='none',
  par='yes (with T002, T004, T005, T012, T013, T021, T022, T024, T027, T032, T034, T043, T062)',
  typ='lemmas', leaves='L0.1, L0.2',
  decls=[(ALG,"isRestricted.smul'"),(ALG,'algebraMap_eq_C_comp')],
  sketch="""⚠ This file is in Layer 0's cone: `lake build PhD.TauCeti.Code.RigidAnalyticGeometry.Restricted.Algebra`
then the leaf `…TateAlgebra.Examples` (about 3 minutes) must pass before marking done.

1. `isRestricted.smul'`: `IsRestricted c f` is `Tendsto (fun t ↦ ‖coeff t f‖ * t.prod (c · ^ ·)) cofinite (𝓝 0)`
   (read the definition in `Restricted/Basic.lean`). Rewrite `coeff t (k • f) = k • coeff t f`
   (`MvPowerSeries.coeff_smul`) and `k • r = (k • (1 : R)) * r` (`smul_mul_assoc`, `one_mul`, in that
   order: `(k • 1) * r = k • (1 * r)`), so `‖coeff t (k • f)‖ ≤ ‖k • 1‖ * ‖coeff t f‖` (`norm_mul_le`).
   Conclude by `squeeze_zero` with `(hf.const_mul ‖k • (1 : R)‖)` after `mul_assoc`.
2. `algebraMap_eq_C_comp`: `RingHom.ext fun r ↦ ?_`; `Algebra.ofModule`'s algebra map is
   `fun r ↦ r • 1` (`Algebra.algebraMap_eq_smul_one`); then `Restricted.ext`, the general smul is
   `rfl` on values (`(k • f).1 = k • f.1`), and `MvPowerSeries.smul_eq_C_mul`? — simplest: show both
   values are `MvPowerSeries.C (algebraMap K S r)`: `r • (1 : MvPowerSeries σ S) = C (algebraMap K S r)`
   by `MvPowerSeries.ext` with `coeff_smul`, `coeff_one`, `coeff_C`, `Algebra.smul_def`, `mul_ite`,
   `mul_one`, `mul_zero`. The floor's `algebraMap_apply` (the case `K = S`) is the model: its proof
   `simp [Algebra.algebraMap_eq_smul_one, MvPowerSeries.smul_eq_C_mul]` may close this one after
   `Algebra.smul_def`/`IsScalarTower.algebraMap_smul`.""",
  mathlib="""`MvPowerSeries.coeff_smul`, `smul_mul_assoc`, `norm_mul_le`, `squeeze_zero`, `Filter.Tendsto.const_mul`, `Algebra.algebraMap_eq_smul_one`, `MvPowerSeries.smul_eq_C_mul`, `MvPowerSeries.coeff_C`, `Algebra.smul_def`, `IsScalarTower.algebraMap_smul`. Floor: `MvPowerSeries.IsRestricted` (definition), `Restricted.ext`, `Restricted.algebraMap_apply` (model proof).""",
  sources="""[BGR] 3.7.1, `bgr-3.7.md:15–16`; [RM] §1.1.3; decomposition L0.1–L0.2.""",
  gen="""Any `[Semiring K] [Module K R] [IsScalarTower K R R]` (the tower makes `k • r = (k • 1) * r`); the `K = R` case is the floor's instance syntactically.""")

t(id='T002', title='Bounded monomials: the contractive case and finitely many power-bounded elements', file=EV, deps='none',
  par='yes (with T001)', typ='lemmas', leaves='L0.3, L0.4',
  decls=[(EV,'norm_prod_pow_le_of_norm_le'),(EV,'exists_forall_norm_prod_pow_le')],
  sketch="""⚠ Layer 0 cone (see T001): rebuild through `…TateAlgebra.Examples` before marking done.

1. `norm_prod_pow_le_of_norm_le`: `rw [one_mul]`; `Finsupp.prod` is a `Finset.prod` over `t.support`;
   `norm_prod_le` (needs `NormOneClass B`) gives `‖∏ x i ^ t i‖ ≤ ∏ ‖x i ^ t i‖`, then termwise
   `norm_pow_le` (`NormOneClass`) and `pow_le_pow_left₀ (norm_nonneg _) (hx i)`; `Finset.prod_le_prod`
   with nonnegativity of norms.
2. `exists_forall_norm_prod_pow_le`: `choose C hC using hx`; `C i ≥ ‖1‖ ≥ 0`? — use `max 1 (C i)`
   to avoid sign issues; `letI := Fintype.ofFinite σ`; take
   `Cx := max ‖(1 : B)‖ (∏ i, max 1 (C i))`. For `t`, the product over `t.support`:
   if `t.support = ∅` the product is `1` (`Finsupp.prod` with `Finset.prod_empty`) and `‖1‖ ≤ Cx`
   (`le_max_left`); otherwise `Finset.norm_prod_le'` (nonempty support, no `NormOneClass`) bounds by
   `∏_{support} ‖x i ^ t i‖ ≤ ∏_{support} max 1 (C i) ≤ ∏_{univ} max 1 (C i) ≤ Cx`
   (`Finset.prod_le_prod`, `Finset.prod_le_prod_of_subset_of_one_le'` with `1 ≤ max 1 _`,
   `le_max_right`). Finish with `t.prod ((1 : σ → ℝ) · ^ ·) = 1` (`Pi.one_apply`, `one_pow`,
   `Finsupp.prod_const_one`-style `simp`) and `mul_one`.""",
  mathlib="""`norm_prod_le`, `Finset.norm_prod_le'`, `norm_pow_le`, `pow_le_pow_left₀`, `Finset.prod_le_prod`, `Finset.prod_le_prod_of_subset_of_one_le'`, `Finsupp.prod`, `Finset.prod_empty`, `Fintype.ofFinite`, `le_max_left`, `le_max_right`.""",
  sources="""[BGR] 6.1.1/4, `bgr-6.1.1.md:51`; 1.2.5/2, `bgr-3.7.md:159–160`; decomposition L0.3–L0.4.""",
  gen="""Normed commutative ring `B`; `NormOneClass` only in item 1 (empty product); `Finite σ` in item 2 is necessary.""")

t(id='T003', title='Evaluation along a bounded coefficient map: term bounds and the norm bound', file=EV, deps='T002',
  par='no (same file as T002)', typ='lemmas', leaves='L0.5, L0.6, L0.7',
  decls=[(EV,'norm_map_mul_prod_pow_le'),(EV,'tendsto_map_coeff_mul_prod_pow'),(EV,'norm_eval₂_le_mul')],
  sketch="""⚠ Layer 0 cone (see T001).

1. `norm_map_mul_prod_pow_le`: `calc ‖φ a * m‖ ≤ ‖φ a‖ * ‖m‖ := norm_mul_le _ _` then
   `mul_le_mul (hφ a) (hx t) (norm_nonneg _) (le_trans (norm_nonneg _) (hφ a))` and the identity
   `Cφ * ‖a‖ * (Cx * c^t) = Cφ * Cx * (‖a‖ * c^t)` by `ring`.
2. `tendsto_map_coeff_mul_prod_pow`: `tendsto_zero_iff_norm_tendsto_zero.2`; `squeeze_zero (fun _ ↦ norm_nonneg _)
   (fun t ↦ norm_map_mul_prod_pow_le c φ x hφ hx _ t)`; the right side is `(Cφ * Cx) * (‖coeff t f.1‖ * c^t)`
   and `f.2 : IsRestricted c f.1` is exactly `Tendsto (fun t ↦ ‖coeff t f.1‖ * t.prod (c · ^ ·)) cofinite (𝓝 0)`
   (unfold as the floor does), so `(f.2.const_mul (Cφ * Cx))` with `mul_zero`.
3. `norm_eval₂_le_mul`: unfold `eval₂_apply`; the ultrametric bound for a convergent sum:
   Layer 0's `norm_eval₂_le` proof (now `simpa` from this lemma — read its old proof in git history
   `git show HEAD:PhD/TauCeti/Code/RigidAnalyticGeometry/TateAlgebra/Eval.lean` for the sum lemma it
   used, from `PadicFunctionalAnalysis/Sums.lean`: `norm_tsum_le_of_forall_le`-type with
   nonnegative bound, or `tsum`'s `norm_tsum_le_of_le`? **(search)** the chain's lemma name in
   `Sums.lean`); the termwise bound is item 1 followed by
   `Cφ * Cx * (‖a‖ * c^t) ≤ |Cφ * Cx| * ‖f‖` (`le_abs_self`, `norm_coeff_mul_prod_le c f t`,
   `mul_le_mul_of_nonneg_left`, `abs_nonneg`); the ultrametric sum lemma needs the bound `|Cφ Cx| ‖f‖`
   to be nonnegative ✓ (`mul_nonneg (abs_nonneg _) (norm_nonneg _)`).""",
  mathlib="""`norm_mul_le`, `mul_le_mul`, `tendsto_zero_iff_norm_tendsto_zero`, `squeeze_zero`, `Filter.Tendsto.const_mul`, `le_abs_self`, `abs_nonneg`, `mul_le_mul_of_nonneg_left`. Chain: `PadicFunctionalAnalysis/Sums.lean` (the ultrametric `tsum` norm bound used by Layer 0's `norm_eval₂_le`), floor `norm_coeff_mul_prod_le`, `Restricted.eval₂_apply`, `hasSum_eval₂`.""",
  sources="""[BGR] 6.1.1/4, `bgr-6.1.1.md:49–51`; 5.1.4/2; decomposition L0.5–L0.7 (the `|Cφ Cx|` repair).""",
  gen="""Arbitrary real constants; the absolute value makes the bound true when `B` is the zero ring with a negative `Cx`.""")

t(id='T004', title='Power-boundedness in a normed algebra over a nontrivially normed field', file=PB, deps='none',
  par='yes (with T001)', typ='lemmas', leaves='L0.8, L0.9, L0.10', milestone='M1 — after this ticket and CLEANUP-ALL-1, `lake build PhD.TauCeti` is sorry-free below this board (check it: `grep -rn sorry PhD/TauCeti/Code/PadicFunctionalAnalysis PhD/TauCeti/Code/RigidAnalyticGeometry/Restricted PhD/TauCeti/Code/RigidAnalyticGeometry/TateAlgebra` must be empty)',
  decls=[(PB,'_root_.TopologicalRing.IsBounded.exists_norm_le_of_normedAlgebra'),(PB,'IsPowerBounded.exists_norm_pow_le'),(PB,'IsPowerBounded.map')],
  sketch="""1. `exists_norm_le_of_normedAlgebra`: read the chain's `TopologicalRing.IsBounded` (top of
   `PowerBounded.lean`): for every `U ∈ 𝓝 0` there is `V ∈ 𝓝 0` with `V * S ⊆ U` (or the chain's exact
   spelling — adapt). Take `U := Metric.ball 0 1`; get `V`, then `ε > 0` with `ball 0 ε ⊆ V`
   (`Metric.mem_nhds_iff`); `NormedField.exists_norm_lt K (half_pos hε)` gives `c : K` with
   `0 < ‖c‖ < ε/2`, so `algebraMap K R c = c • 1 ∈ V` (`norm_algebraMap`/`norm_smul`, `‖1‖` may be
   `> 1`: use `‖c • 1‖ ≤ ‖c‖ * ‖1‖` and choose `‖c‖ < ε / (‖1‖ + 1)` instead); then for `s ∈ S`,
   `‖(c • 1) * s‖ < 1`, i.e. `‖c‖ * ‖s‖ < 1`?? — careful: `‖(c • 1) * s‖ = ‖c • s‖ = ‖c‖ * ‖s‖` by
   `smul_mul_assoc`, `one_mul`, `norm_smul`; so `‖s‖ < ‖c‖⁻¹` (`lt_inv_mul_iff₀`-type); `C := ‖c‖⁻¹`.
2. `IsPowerBounded.exists_norm_pow_le`: item 1 on `Set.range (a ^ ·)`; `C` with `∀ n, ‖a ^ n‖ ≤ C`
   via `Set.mem_range_self`.
3. `IsPowerBounded.map`: `obtain ⟨M, hM⟩ := ha.exists_norm_pow_le`; `isPowerBounded_of_norm_pow_le
   (C := C * M) fun n ↦ by rw [← map_pow]; exact (hφ _).trans (mul_le_mul_of_nonneg_left (hM n) ?_)`
   — `0 ≤ C` is not given: if `C < 0` then `‖φ r‖ ≤ C ‖r‖ ≤ 0` for all `r`, so `φ = 0` and the claim
   is `IsPowerBounded 0` (`isPowerBounded_of_norm_le_one` with `norm_zero`); split on `le_or_gt 0 C`.""",
  mathlib="""`Metric.mem_nhds_iff`, `NormedField.exists_norm_lt`, `norm_smul`, `smul_mul_assoc`, `Set.mem_range_self`, `map_pow`, `mul_le_mul_of_nonneg_left`, `le_or_gt`. Chain: `TopologicalRing.IsBounded` (definition in `PowerBounded.lean`), `PowerBounded.isPowerBounded_of_norm_pow_le`, `isPowerBounded_of_norm_le_one`.""",
  sources="""[BGR] 1.2.5/1, `bgr-3.7.md:155`; 6.1.1, `bgr-6.1.1.md:43`; [RM] §0.2.1; decomposition L0.8–L0.10.""",
  gen="""`NontriviallyNormedField K` and `NormedAlgebra K R` for a normed ring `R` (no commutativity, no completeness).""")

# ---------------------------------------------------------------- G1 NormedQuotient
t(id='T005', title='The quotient seminorm of an ultrametric group is ultrametric; nearest representatives', file=NQ, deps='none',
  par='yes (with T001)', typ='instance + lemma', leaves='L1.1, L1.2',
  decls=[(NQ,'isUltrametricDist'),(NQ,'norm_mk_eq_norm_of_forall_le')],
  sketch="""1. `QuotientAddGroup.isUltrametricDist`: `IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
   fun x y ↦ ?_` (if that constructor name differs, `IsUltrametricDist.mk` through `dist_eq_norm`);
   `le_of_forall_lt fun ε hε ↦ ?_` where `hε : max ‖x‖ ‖y‖ < ε`: `QuotientAddGroup.norm_lt_iff.1
   (lt_of_le_of_lt (le_max_left _ _) hε)` gives `m₁` with `↑m₁ = x`, `‖m₁‖ < ε`; same `m₂`;
   `QuotientAddGroup.norm_lt_iff.2 ⟨m₁ + m₂, by simp [*], (IsUltrametricDist.norm_add_le_max
   m₁ m₂).trans_lt (max_lt h₁ h₂)⟩`. (Watch the direction of `le_of_forall_lt` versus
   `le_of_forall_gt`: we need `‖x + y‖ ≤ max`, so "for all `ε > max`, `‖x + y‖ < ε`".)
2. `norm_mk_eq_norm_of_forall_le`: `rw [QuotientAddGroup.norm_mk]` (the ideal as `I.toAddSubgroup`
   — state the `show` if the coercion differs); `le_antisymm (Metric.infDist_le_dist_of_mem
   (I.zero_mem) ▸ by simp) ((Metric.le_infDist ⟨0, I.zero_mem⟩).2 fun a ha ↦ by rw [dist_eq_norm]; exact h a ha)`
   — Layer 0's `norm_quotient_mk_mem_range_norm` (`StrictlyClosed.lean`, last lemma) has exactly this
   `infDist` computation; copy it.""",
  mathlib="""`QuotientAddGroup.norm_lt_iff`, `QuotientAddGroup.norm_mk`, `IsUltrametricDist.norm_add_le_max`, `le_of_forall_lt`, `max_lt`, `Metric.infDist_le_dist_of_mem`, `Metric.le_infDist`, `dist_eq_norm`. Layer 0: `norm_quotient_mk_mem_range_norm` (model).""",
  sources="""[BGR] 6.1.1, `bgr-6.1.1.md:6–10`; [Bo] 1.4/4, `bosch-lectures.txt:1032–1033`; decomposition L1.1–L1.2.""",
  gen="""Any seminormed ultrametric group and any additive subgroup (no closedness); the nearest-point lemma for any seminormed commutative ring.""")

t(id='T006', title='`‖1‖ = 1` in the quotient by a proper closed ideal', file=NQ, deps='T005', par='no', typ='lemma', leaves='L1.3',
  decls=[(NQ,'normOneClass_of_ne_top')],
  sketch="""`⟨?_⟩`; `norm_mk_eq_norm_of_forall_le (f := 1) ?_ ▸ norm_one` after `map_one`
(the class of `1` is `1`); the hypothesis: for `a ∈ I`, `by_contra hlt; push_neg at hlt` gives
`‖1 - a‖ < ‖1‖ = 1`; `have := isUnit_one_sub_of_norm_lt_one (x := 1 - a) (by rwa [norm_one] at hlt)`
is `IsUnit (1 - (1 - a))`, and `sub_sub_cancel` makes it `IsUnit a`; then `hI (Ideal.eq_top_of_isUnit_mem I ha this)`.""",
  mathlib="""`isUnit_one_sub_of_norm_lt_one`, `Ideal.eq_top_of_isUnit_mem`, `sub_sub_cancel`, `norm_one`, `map_one`.""",
  sources="""[BGR] 6.1.1, `bgr-6.1.1.md:6–9`; 1.2.4/4, `bgr-3.7.md:135–136`; decomposition L1.3.""",
  gen="""Complete normed commutative ring with `‖1‖ = 1`, ultrametric (for the quotient instance), closed proper ideal.""")

# ---------------------------------------------------------------- G2 Sum
t(id='T007', title='`R⟨X ⊕ Y⟩ → R⟨Y⟩⟨X⟩ → R⟨X ⊕ Y⟩`: the variable bounds and both compositions', file=SUM, deps='T003',
  par='yes (with T005)', typ='lemmas', leaves='L2.1, L2.2, L2.3',
  decls=[(SUM,'norm_sumTuple_le'),(SUM,'iterToSum_comp_sumToIter'),(SUM,'sumToIter_comp_iterToSum')],
  sketch="""1. `norm_sumTuple_le`: `rcases i with i | j <;> simp only [sumTuple, Sum.elim_inl, Sum.elim_inr]`;
   `norm_X` gives `‖(1 : Restricted R (c ∘ inr))‖ * (c ∘ inl) i`, `norm_one` (the floor's `NormOneClass
   (Restricted R c)` instance from `NormOneClass R`), `one_mul`, `Function.comp_apply`; for `inr j`:
   `norm_C` then `norm_X`, `norm_one`.
2. `iterToSum_comp_sumToIter`: `ringHom_ext_of_continuous (continuous_eval₂.comp continuous_eval₂)?` —
   both sides as `RingHom`s: `(continuous_eval₂ _ _).comp (continuous_eval₂ _ _)` (the `Fact` on
   `σ ⊕ τ` is in scope); `hC`: `RingHom.comp_apply`, `eval₂_C` twice (`sumToIter (C r) = C (C r)`, then
   `iterToSum (C (C r)) = (inner eval₂) (C r) = C r`); `hX`: `rcases i with i | j`; `eval₂_X`,
   `sumTuple`, `Sum.elim_inl` and `eval₂_X` again, or for `inr j`: `sumToIter (X (inr j)) = C (X j)`,
   then `iterToSum (C g) = inner g` and `inner (X j) = X (inr j)` by `eval₂_X`.
3. `sumToIter_comp_iterToSum`: outer `ringHom_ext_of_continuous` on `R⟨Y⟩⟨X⟩` (the `Fact` for
   `c ∘ inl`); `hX`: `eval₂_X` twice; `hC g`: the goal `sumToIter (inner g) = C g` for all `g`; make it
   `RingHom.congr_fun ?_ g` with the inner equality `(sumToIter c).comp inner = C (c ∘ inl)` proved by a
   second `ringHom_ext_of_continuous` on `R⟨Y⟩` (`Fact` for `c ∘ inr`; continuity `continuous_eval₂.comp
   continuous_eval₂` and `continuous_C`-type: `C` is an isometry — see T018's `continuous_C` in
   `Extend.lean`, or prove `Continuous (C c)` inline with `AddMonoidHomClass.continuous_of_bound _ 1` and
   `norm_C`); on `C r`: `inner (C r) = C r`, `sumToIter (C r) = C (C r)`; on `X j`: `inner (X j) = X (inr j)`,
   `sumToIter (X (inr j)) = C (X j)`.""",
  mathlib="""`RingHom.comp_apply`, `RingHom.congr_fun`, `Sum.elim_inl`, `Sum.elim_inr`, `Function.comp_apply`, `AddMonoidHomClass.continuous_of_bound`. Floor/board: `norm_X`, `norm_C`, `norm_one`, `eval₂_C`, `eval₂_X`, `continuous_eval₂`, `ringHom_ext_of_continuous`.""",
  sources="""[BGR] 6.1.1/7, `bgr-6.1.1.md:91–99`; decomposition L2.1–L2.3.""",
  gen="""Complete normed commutative ring `R` with `NormOneClass`, ultrametric; any index types; any positive polyradius on `σ ⊕ τ`.""")

t(id='T008', title='`R⟨X ⊕ Y⟩ ≅ R⟨Y⟩⟨X⟩`: values, isometry, continuity', file=SUM, deps='T007', par='no', typ='lemmas',
  leaves='L2.4–L2.9',
  decls=[(SUM,'sumEquiv_C',0),(SUM,'sumEquiv_X_inl'),(SUM,'sumEquiv_X_inr'),(SUM,'norm_sumEquiv',0),(SUM,'continuous_sumEquiv'),(SUM,'continuous_sumEquiv_symm')],
  sketch="""1. `sumEquiv_C`, `sumEquiv_X_inl`, `sumEquiv_X_inr`: `RingEquiv.ofRingHom_apply` (or `rfl`/`show`)
   reduces to `sumToIter`, then `eval₂_C` (with `RingHom.comp_apply` for `(C _).comp (C _)`) and
   `eval₂_X` with `sumTuple`, `Sum.elim_inl/inr`.
2. `norm_sumEquiv`: `le_antisymm (norm_eval₂_le _ _ f)` — `sumToIter` was defined with `(Cφ := 1)` and
   `norm_prod_pow_le_of_norm_le` (bound `1`), so `norm_eval₂_le` applies — and for `≥`:
   `have := norm_eval₂_le _ _ (sumEquiv c f)` for `iterToSum` (its bounds are also the `1`-forms), and
   `RingHom.congr_fun (iterToSum_comp_sumToIter c) f` rewrites `iterToSum (sumToIter f) = f`.
3. `continuous_sumEquiv`: `show Continuous (sumToIter c); exact continuous_eval₂ _ _`;
   `continuous_sumEquiv_symm`: `RingEquiv.ofRingHom_symm_apply`/`show Continuous (iterToSum c)`.""",
  mathlib="""`RingEquiv.ofRingHom_apply`, `RingEquiv.ofRingHom_symm_apply`, `RingHom.congr_fun`, `le_antisymm`. Board: `eval₂_C`, `eval₂_X`, `norm_eval₂_le`, `continuous_eval₂`, T007.""",
  sources="""[BGR] 6.1.1/7, `bgr-6.1.1.md:95–99`; decomposition L2.4–L2.9.""",
  gen="""As T007.""")

t(id='T009', title='Renaming the variables along a bijection, at the unit polyradius', file=SUM, deps='T003',
  par='yes (with T007)', typ='definition + lemmas', leaves='L2.10–L2.13',
  decls=[(SUM,'renameEquiv'),(SUM,'renameEquiv_C'),(SUM,'renameEquiv_X'),(SUM,'norm_renameEquiv')],
  sketch="""Follow the proved pattern of `sumEquiv` (T007–T008) with evaluations:
`toFun := eval₂ (Cφ := 1) (1 : σ → ℝ) (C (1 : τ → ℝ)) (fun i ↦ X R 1 (e i)) (fun r ↦ by simp [norm_C])
(norm_prod_pow_le_of_norm_le _ _ fun i ↦ by simp [norm_X])`, `invFun` the same with `e.symm`,
`RingEquiv.ofRingHom` with the two compositions by `ringHom_ext_of_continuous` (`eval₂_C`, `eval₂_X`,
`Equiv.symm_apply_apply`, `Equiv.apply_symm_apply`). Then `renameEquiv_C`, `renameEquiv_X` are `eval₂_C`,
`eval₂_X`; `norm_renameEquiv` is `le_antisymm` of two `norm_eval₂_le` as in T008.
Alternative (if preferred): restrict Mathlib's `MvPowerSeries.renameEquiv e` to the subrings
(`IsRestricted` is preserved: the Gauss terms are permuted by `Finsupp.mapDomain e`, use
`Equiv.tendsto_cofinite`-type reindexing); then the norm equality is a reindexed `iSup`. The evaluation
route reuses more of the board and is the planned one.""",
  mathlib="""`RingEquiv.ofRingHom`, `Equiv.symm_apply_apply`, `Equiv.apply_symm_apply`, `Function.comp_apply`. Board: `eval₂`, `eval₂_C`, `eval₂_X`, `norm_eval₂_le`, `continuous_eval₂`, `ringHom_ext_of_continuous`, `norm_prod_pow_le_of_norm_le`.""",
  sources="""[BGR] 5.1.3 (charts); [RM] §1.1.3; decomposition L2.10–L2.13 (D5).""",
  gen="""Unit polyradius only (D5): the consumers (`IsAffinoidAlgebra.restricted`, the examples) never need another.""")

t(id='T010', title='`Tₙ⟨Y₁, …, Y_m⟩ ≅ T_{m+n}` as `K`-algebras, isometrically', file=SUM, deps='T008', par='no',
  typ='definition + lemmas', leaves='L2.14–L2.17',
  decls=[(SUM,'sumEquiv'),(SUM,'norm_sumEquiv',1),(SUM,'sumEquiv_C',1),(SUM,'sumEquiv_X')],
  sketch="""Build `sumEquiv K n m` by `AlgEquiv.ofAlgHom` with:
- forward `F : Restricted (TateAlgebra K n) (1 : Fin m → ℝ) →ₐ[K] TateAlgebra K (m + n)` from the ring
  homomorphism `eval₂ (Cφ := 1) (1 : Fin m → ℝ) (inner).toRingHom (fun j ↦ X K 1 (Fin.castAdd n j))
  (fun f ↦ by rw [one_mul]; exact norm_aeval_le? …)` where `inner : TateAlgebra K n →ₐ[K] TateAlgebra K (m + n)`
  is `aeval (1 : Fin n → ℝ) (fun i ↦ X K 1 (Fin.natAdd m i)) (fun i ↦ by simp [norm_X])` (contractive:
  `norm_aeval_le`) — but the statement `sumEquiv_C` names the inner map as
  `eval₂ (Cφ := 1) 1 (C 1) (X ∘ natAdd m) …`; `aeval` *is* that `eval₂` with `algebraMap = C` (the floor's
  `algebraMap_apply`), so either use that `eval₂` directly as the ring hom and add `commutes'` by
  `algebraMap_eq_C_comp` (T001) + `eval₂_C`, or prove `sumEquiv_C` by `aeval_apply`/`eval₂_apply` unfolding;
  the `eval₂` spelling of the statement is the intended definition;
  `commutes' r`: `algebraMap K (Restricted Tₙ 1) r = C 1 (C 1 r)` (T001's `algebraMap_eq_C_comp` with
  `algebraMap_apply`), then `eval₂_C` twice.
- inverse `G := aeval (1 : Fin (m + n) → ℝ) (Fin.append (fun j ↦ X _ 1 j) (fun i ↦ C 1 (X K 1 i)))
  (by intro k; refine Fin.addCases ?_ ?_ k <;> simp [Fin.append_left, Fin.append_right, norm_X, norm_C])`.
- `F.comp G = id`: `algHom_ext_of_continuous` on `T_{m+n}` (coefficients `K`): continuity
  `(continuous_eval₂ _ _).comp (continuous_aeval _)`; on `X k`: `Fin.addCases`; `aeval_X`,
  `Fin.append_left/right`, then `eval₂_X` or `eval₂_C` + inner `aeval_X`.
- `G.comp F = id`: `ringHom_ext_of_continuous` on `Restricted Tₙ 1` (coefficients `Tₙ`): on `X j`:
  `eval₂_X`, `aeval_X`, `Fin.append_left`; on `C f`: reduce to the inner map by `eval₂_C`, then a
  second `algHom_ext_of_continuous` on `Tₙ` for `G ∘ inner` versus `IsScalarTower.toAlgHom K Tₙ _`
  (both continuous; on `X i`: `aeval_X`, `Fin.append_right`, `algebraMap_apply`).
Then `norm_sumEquiv`: `le_antisymm (norm_eval₂_le …) (by simpa using norm_aeval_le … (sumEquiv f))` as in
T008; `sumEquiv_C`: `eval₂_C` (the inner map applied); `sumEquiv_X`: `eval₂_X`.""",
  mathlib="""`AlgEquiv.ofAlgHom`, `Fin.castAdd`, `Fin.natAdd`, `Fin.append`, `Fin.append_left`, `Fin.append_right`, `Fin.addCases`. Board/floor: `eval₂`, `eval₂_C`, `eval₂_X`, `aeval`, `aeval_X`, `norm_aeval_le`, `norm_eval₂_le`, `continuous_eval₂`, `continuous_aeval`, `ringHom_ext_of_continuous`, `algHom_ext_of_continuous`, `algebraMap_apply`, `algebraMap_eq_C_comp` (T001), `IsScalarTower.toAlgHom`.""",
  sources="""[BGR] 6.1.1/8, `bgr-6.1.1.md:107–108`; decomposition L2.14–L2.17.""",
  gen="""The Tate algebras over a complete ultrametric normed field; the new `m` variables come first (`castAdd`), the old `n` last (`natAdd`).""")

# ---------------------------------------------------------------- G3 Affinoid/Basic
t(id='T011', title='Residue norms are attained, take values in `‖K‖`, and classes can be normalised', file=BAS, deps='T005',
  par='yes (with T012, T013)', typ='lemmas', leaves='L3.1, L3.3, L3.4',
  decls=[(BAS,'exists_norm_quotient_mk_eq'),(BAS,'norm_quotient_mem_range_norm'),(BAS,'exists_norm_smul_quotient_eq_one')],
  sketch="""1. `exists_norm_quotient_mk_eq`: `obtain ⟨a₀, ha₀, hmin⟩ := exists_forall_norm_sub_le_ideal I f`;
   `refine ⟨a₀, ha₀, ?_⟩`; `have : Ideal.Quotient.mk I f = Ideal.Quotient.mk I (f - a₀) := by rw [map_sub,
   Ideal.Quotient.eq_zero_iff_mem.2 ha₀, sub_zero]`; rewrite and apply T005's
   `Ideal.Quotient.norm_mk_eq_norm_of_forall_le` with `h a ha := by simpa [sub_sub] using hmin (a₀ + a) (I.add_mem ha₀ ha)`
   (`‖f - a₀‖ ≤ ‖f - (a₀ + a)‖ = ‖(f - a₀) - a‖`).
2. `norm_quotient_mem_range_norm`: `obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x`; Layer 0's
   `norm_quotient_mk_mem_range_norm I f`.
3. `exists_norm_smul_quotient_eq_one`: `obtain ⟨a, ha⟩ := norm_quotient_mem_range_norm I x`; `a ≠ 0` since
   `‖x‖ ≠ 0` (`norm_ne_zero_iff.2 hx`, the quotient is a normed group: `IsClosed` instance);
   `⟨a⁻¹, by rw [norm_smul, norm_inv, ← ha, inv_mul_cancel₀ (norm_ne_zero_iff.2 ha0)]⟩`.""",
  mathlib="""`Ideal.Quotient.mk_surjective`, `Ideal.Quotient.eq_zero_iff_mem`, `map_sub`, `norm_smul`, `norm_inv`, `inv_mul_cancel₀`, `norm_ne_zero_iff`. Layer 0: `exists_forall_norm_sub_le_ideal`, `norm_quotient_mk_mem_range_norm`; T005.""",
  sources="""[BGR] 6.1.1/2, `bgr-6.1.1.md:23–25`; [Bo] 1.4/4 (iii), `bosch-lectures.txt:1032–1034`; decomposition L3.1, L3.3, L3.4.""",
  gen="""Quotients of `TateAlgebra K n` by any ideal, `K` complete (Layer 0's strict closedness).""")

t(id='T012', title='Ideals of `Tₙ ⧸ I` are closed', file=BAS, deps='none', par='yes (with T011)', typ='lemma', leaves='L3.2',
  decls=[(BAS,'isClosed_ideal_quotient')],
  sketch="""`have h : (J : Set _) = Ideal.Quotient.mk I '' (J.comap (Ideal.Quotient.mk I))` from
`Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective J` (`Ideal.map` of a surjective map is the image:
`Ideal.map_comap_of_surjective`, then `Ideal.coe_map`? — easier: show `IsClosed (mk ⁻¹' J)` and use
`(QuotientAddGroup.isQuotientMap_mk I.toAddSubgroup).isCoinducing.isClosed_preimage.1`; the preimage `mk ⁻¹' (J : Set _)`
is `((J.comap (mk I) : Ideal _) : Set _)` by `rfl`/`Ideal.coe_comap`, closed by Layer 0's `isClosed_ideal`).
If the `IsQuotientMap` lemma's topology instance does not unify with the normed quotient's
(`QuotientAddGroup.instTopologicalSpace` versus the `SeminormedAddCommGroup` topology), prove the
quotient-map property directly from `QuotientAddGroup.isOpenMap_coe`-style lemmas, or use
`isClosed_of_closure_subset` with `QuotientAddGroup.norm_mk` and the nearest-point lemma T011/1
(a limit of classes `mk fₙ` with `fₙ ∈ J'` … ) — the first route is expected to work since Mathlib's
quotient-norm file states the topologies agree.""",
  mathlib="""`QuotientAddGroup.isQuotientMap_mk`, `Topology.IsQuotientMap.isCoinducing`, `Topology.IsCoinducing.isClosed_preimage`, `Ideal.coe_comap`, `Ideal.map_comap_of_surjective`, `Ideal.Quotient.mk_surjective`. Layer 0: `isClosed_ideal`.""",
  sources="""[BGR] 6.1.1/3, `bgr-6.1.1.md:34–35`; decomposition L3.2.""",
  gen="""Quotients of `Tₙ` only (the general statement for any Banach norm on an affinoid algebra is T037's corollary `IsAffinoidAlgebra.isClosed_ideal`).""")

t(id='T013', title='Affinoid algebras: images, quotient presentations, noetherian and Jacobson', file=BAS, deps='none',
  par='yes (with T011)', typ='lemmas', leaves='L3.5–L3.8',
  decls=[(BAS,'of_surjective'),(BAS,'exists_algEquiv_quotient'),(BAS,'isNoetherianRing'),(BAS,'isJacobsonRing')],
  sketch="""1. `of_surjective`: `obtain ⟨n, α, hα⟩ := hA; exact ⟨n, φ.comp α, hφ.comp hα⟩`.
2. `exists_algEquiv_quotient`: `⟨n, RingHom.ker α, ⟨Ideal.quotientKerAlgEquivOfSurjective hα⟩⟩`.
3. `isNoetherianRing`: `obtain ⟨n, α, hα⟩ := hA; exact isNoetherianRing_of_surjective _ _ α.toRingHom hα`
   (Layer 0's instance `instIsNoetherianRing` is found with `[CompleteSpace K]`).
4. `isJacobsonRing`: `isJacobsonRing_of_surjective ⟨α.toRingHom, hα⟩` — check the hypothesis shape
   (`#check @isJacobsonRing_of_surjective`: it takes `∃ f : R →+* S, Surjective f`).""",
  mathlib="""`Ideal.quotientKerAlgEquivOfSurjective`, `isNoetherianRing_of_surjective`, `isJacobsonRing_of_surjective`, `Function.Surjective.comp`. Layer 0: `Affinoid.TateAlgebra.instIsNoetherianRing`, `instIsJacobsonRing`.""",
  sources="""[BGR] 6.1.1/3, `bgr-6.1.1.md:31–36`; 6.1.1, `:17–18`; [Bo] 1.4/2, `bosch-lectures.txt:1008–1012`; decomposition L3.5–L3.8.""",
  gen="""Any `K`-algebras (no norm); `CompleteSpace K` for Layer 0's instances.""")

# ---------------------------------------------------------------- G4 Affinoid/Extend
t(id='T014', title='`A⟨X⟩` is a normed `K`-algebra; the variables are power-bounded; bounded monomials', file=EXT, deps='T002, T004',
  par='yes (with T005, T007)', typ='lemmas', leaves='L4.1–L4.3',
  decls=[(EXT,'norm_smul_le_of_normedAlgebra'),(EXT,'isPowerBounded_X'),(EXT,'exists_forall_norm_prod_pow_le_of_isPowerBounded')],
  sketch="""1. `norm_smul_le_of_normedAlgebra`: `refine (norm_le_iff c _).2 fun t ↦ ?_`; `(k • f).1 = k • f.1` is
   `rfl` (general `Module` instance), `MvPowerSeries.coeff_smul`, `norm_smul_le k _`, `mul_assoc`, then
   `mul_le_mul_of_nonneg_left (norm_coeff_mul_prod_le c f t) (norm_nonneg k)`. Do not `rw` under the
   coercion: `simp only [MvPowerSeries.coeff_smul]` after a `show`/`change` on `(k • f).1`.
2. `isPowerBounded_X`: `isPowerBounded_of_norm_pow_le (C := ‖(1 : A)‖) fun k ↦ ?_`;
   `X A 1 i ^ k = monomial 1 (Finsupp.single i k) 1` (floor: `X_pow_eq`? — if absent, `Restricted.ext`
   with `MvPowerSeries.X_pow_eq` and `val_monomial`), `norm_monomial` gives `‖1‖ * (single i k).prod (1 · ^ ·) = ‖1‖`
   (`Finsupp.prod_single_index`, `one_pow`). For `k = 0`: `pow_zero`, `le_rfl`.
3. `exists_forall_norm_prod_pow_le_of_isPowerBounded`: `exists_forall_norm_prod_pow_le 1 b fun i ↦
   (hb i).exists_norm_pow_le` (T002, T004).""",
  mathlib="""`norm_smul_le`, `MvPowerSeries.coeff_smul`, `MvPowerSeries.X_pow_eq`, `Finsupp.prod_single_index`, `pow_zero`. Floor: `norm_le_iff`, `norm_coeff_mul_prod_le`, `norm_monomial`, `val_monomial`. Board: T002, T004.""",
  sources="""[BGR] 3.7.1, `bgr-3.7.md:15–16`; 6.1.1/4, `bgr-6.1.1.md:51`; decomposition L4.1–L4.3.""",
  gen="""Any normed commutative `K`-algebra `A` (ultrametric), no `NormOneClass` (D9), no completeness.""")

t(id='T015', title='`extendAlgHom`: the extension of a continuous homomorphism to `A⟨X⟩` and its values', file=EXT, deps='T014, T001, T003',
  par='no', typ='definition + lemmas', leaves='L4.4–L4.7',
  decls=[(EXT,'extendAlgHom'),(EXT,'extendAlgHom_C'),(EXT,'extendAlgHom_X'),(EXT,'extendAlgHom_comp_toAlgHom')],
  sketch="""1. `commutes' r`: `rw [algebraMap_eq_C_comp]` (T001: `algebraMap K (Restricted A 1) = (C 1).comp (algebraMap K A)`),
   `RingHom.comp_apply`, then the goal is `eval₂ … (C 1 (algebraMap K A r)) = algebraMap K B r`:
   `eval₂_C` and `φ.commutes r` (`AlgHom.toRingHom` coercion: `AlgHom.coe_toRingHom`).
2. `extendAlgHom_C`: `show eval₂ … (C 1 a) = φ a`, `eval₂_C`.
3. `extendAlgHom_X`: `eval₂_X`.
4. `extendAlgHom_comp_toAlgHom`: `AlgHom.ext fun a ↦ ?_`, `AlgHom.comp_apply`, `IsScalarTower.toAlgHom_apply`,
   `algebraMap_apply` (floor: `algebraMap A (Restricted A 1) a = C 1 a`), `extendAlgHom_C`.""",
  mathlib="""`RingHom.comp_apply`, `AlgHom.comp_apply`, `AlgHom.ext`, `AlgHom.coe_toRingHom`, `IsScalarTower.toAlgHom_apply`. Floor/board: `eval₂_C`, `eval₂_X`, `algebraMap_apply`, `algebraMap_eq_C_comp` (T001).""",
  sources="""[BGR] 6.1.1/4, `bgr-6.1.1.md:45–50`; [Bo] 1.4/18, `bosch-lectures.txt:1393–1396`; decomposition L4.4–L4.7.""",
  gen="""`NontriviallyNormedField K` (for the bound of `φ`), normed `K`-algebras `A` (ultrametric) and Banach `B`; `Finite σ`.""")

t(id='T016', title='`extendAlgHom`: continuity, bound, uniqueness, and the case `A = K`', file=EXT, deps='T015', par='no',
  typ='lemmas', leaves='L4.8–L4.12',
  decls=[(EXT,'continuous_extendAlgHom'),(EXT,'exists_forall_norm_extendAlgHom_le'),(EXT,'extendAlgHom_unique'),(EXT,'existsUnique_extend'),(EXT,'extendAlgHom_ofId_eq_aeval')],
  sketch="""1. `continuous_extendAlgHom`: `show Continuous (eval₂ …); exact continuous_eval₂ _ _`.
2. `exists_forall_norm_extendAlgHom_le`: `⟨|Cφ * Cx|, fun f ↦ norm_eval₂_le_mul _ _ f⟩` with the two
   `choose` constants (`exact ⟨_, fun f ↦ norm_eval₂_le_mul _ _ f⟩` lets Lean find them).
3. `extendAlgHom_unique`: `AlgHom.coe_ringHom_injective (ringHom_ext_of_continuous hψ
   (continuous_extendAlgHom …) (fun a ↦ by simpa [extendAlgHom_C] using hC a) (fun i ↦ by simpa
   [extendAlgHom_X] using hX i))` — the ring-level ext because the coefficient ring is `A`, not `K`
   (L4.10); the `Fact (∀ i, 0 < (1 : σ → ℝ) i)` instance is the floor's.
4. `existsUnique_extend`: `⟨extendAlgHom φ hφ b hb, ⟨continuous_extendAlgHom …, extendAlgHom_C …, extendAlgHom_X …⟩,
   fun ψ ⟨h₁, h₂, h₃⟩ ↦ extendAlgHom_unique φ hφ b hb ψ h₁ h₂ h₃⟩`.
5. `extendAlgHom_ofId_eq_aeval`: `algHom_ext_of_continuous (continuous_extendAlgHom …) (continuous_aeval _)
   fun i ↦ by rw [extendAlgHom_X, aeval_X]` (coefficients `K`, so the `K`-algebra ext applies).""",
  mathlib="""`AlgHom.coe_ringHom_injective`, `ExistsUnique`. Floor/board: `continuous_eval₂`, `norm_eval₂_le_mul`, `ringHom_ext_of_continuous`, `algHom_ext_of_continuous`, `continuous_aeval`, `aeval_X`, T015.""",
  sources="""[BGR] 6.1.1/4, `bgr-6.1.1.md:52–54`; decomposition L4.8–L4.12.""",
  gen="""As T015; item 5 needs `IsUltrametricDist K` and `NormOneClass B` for `aeval`.""")

t(id='T017', title='Affinoid generating systems from module generators (BGR 6.1.1/5, first half)', file=EXT, deps='T016', par='no',
  typ='lemmas', leaves='L4.13–L4.15',
  decls=[(EXT,'isAffinoidGeneratingSystem_of_forall_exists_sum'),(EXT,'exists_forall_norm_smul_le_one'),(EXT,'exists_isAffinoidGeneratingSystem_of_finite')],
  sketch="""1. `isAffinoidGeneratingSystem_of_forall_exists_sum`: `⟨hb, fun y ↦ ?_⟩`; `obtain ⟨q, rfl⟩ := hgen y`;
   `⟨∑ i, C 1 (q i) * X A 1 i, by simp [map_sum, map_mul, extendAlgHom_C, extendAlgHom_X]⟩`.
2. `exists_forall_norm_smul_le_one`: `obtain ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one K`;
   `M := ∑ i, ‖a i‖` (so `‖a i‖ ≤ M`, `Finset.single_le_sum`); `obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
   (by positivity : 0 < 1 / (M + 1)) hx1` gives `‖x‖ ^ N < 1 / (M + 1)`; `c := x ^ N`, `c ≠ 0`
   (`pow_ne_zero _ (norm_pos_iff.1 hx0)`); `‖c • a i‖ ≤ ‖c‖ * ‖a i‖ = ‖x‖^N * ‖a i‖ ≤ ‖x‖^N * (M + 1) ≤ 1`
   (`norm_smul_le`, `norm_pow`, `mul_le_mul_of_nonneg_left`, `div_mul_cancel₀`-style arithmetic with
   `M + 1 > 0`; use `le_div_iff₀`).
3. `exists_isAffinoidGeneratingSystem_of_finite`: `letI := φ.toRingHom.toAlgebra`; `hfin : Module.Finite A B`
   (that is the definition of `RingHom.Finite`); `obtain ⟨m, a, ha⟩ := Module.Finite.exists_fin (R := A) (M := B)`
   (`span A (range a) = ⊤`); `obtain ⟨c, hc0, hc⟩ := exists_forall_norm_smul_le_one (K := K) a`;
   `refine ⟨m, fun i ↦ c • a i, isAffinoidGeneratingSystem_of_forall_exists_sum φ hφ
   (fun i ↦ isPowerBounded_of_norm_le_one (hc i)) fun y ↦ ?_⟩`;
   `have hy : y ∈ Submodule.span A (Set.range a) := ha ▸ Submodule.mem_top`;
   `obtain ⟨q, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hy`;
   `refine ⟨fun i ↦ c⁻¹ • q i, ?_⟩`; termwise: `q i • a i = φ (q i) * a i` (`RingHom.smul_toAlgebra`,
   i.e. `Algebra.smul_def` for the `toAlgebra` instance), and
   `φ (c⁻¹ • q i) * (c • a i) = (c⁻¹ • φ (q i)) * (c • a i) = (c⁻¹ * c) • (φ (q i) * a i)`
   (`map_smul`, `smul_mul_smul_comm`), `inv_mul_cancel₀ hc0`, `one_smul`.""",
  mathlib="""`map_sum`, `map_mul`, `NormedField.exists_norm_lt_one`, `exists_pow_lt_of_lt_one`, `Finset.single_le_sum`, `norm_smul_le`, `norm_pow`, `pow_ne_zero`, `norm_pos_iff`, `le_div_iff₀`, `Module.Finite.exists_fin`, `Submodule.mem_span_range_iff_exists_fun`, `RingHom.smul_toAlgebra`, `Algebra.smul_def`, `map_smul`, `smul_mul_smul_comm`, `inv_mul_cancel₀`, `one_smul`. Board: T015, T016, PFA `isPowerBounded_of_norm_le_one`.""",
  sources="""[BGR] 6.1.1/5, `bgr-6.1.1.md:66–70`; 7.2.5, `bgr-3.7.md:166–171`; decomposition L4.13–L4.15.""",
  gen="""As T015; `Fintype σ` in items 1–2 (finite sums), `Fin m` in item 3.""")

t(id='T018', title='Functoriality `A⟨X⟩ → B⟨X⟩` along a continuous homomorphism, coefficientwise', file=EXT, deps='T015',
  par='yes (with T017)', typ='lemmas', leaves='L4.16–L4.19',
  decls=[(EXT,'continuous_algebraMap_restricted'),(EXT,'mapAlgHom_C'),(EXT,'mapAlgHom_X'),(EXT,'coeff_mapAlgHom')],
  sketch="""1. `continuous_algebraMap_restricted`: `have : ⇑(algebraMap A (Restricted A c)) = ⇑(C c) := funext (algebraMap_apply c)`;
   `rw [this]; exact continuous_C c`.
2. `mapAlgHom_C`: `extendAlgHom_C` then `AlgHom.comp_apply`, `IsScalarTower.toAlgHom_apply`, `algebraMap_apply`.
3. `mapAlgHom_X`: `extendAlgHom_X`.
4. `coeff_mapAlgHom`: `have h := hasSum_eval₂ … f` for the underlying `eval₂` of `mapAlgHom`
   (`show` it); the map `g ↦ coeff t g.1` is a continuous additive homomorphism
   (`AddMonoidHom.mk` with `val_add`; continuity by `AddMonoidHomClass.continuous_of_bound _ 1` and
   `norm_coeff_le`); `h.map` it: `HasSum (fun ν ↦ coeff t (C 1 (α a_ν) * X^ν).1) (coeff t (mapAlgHom … f).1)`;
   the summand is `if ν = t then α (coeff ν f.1) else 0` (`val_mul`, `val_C`, `MvPowerSeries.coeff_C_mul`,
   `X^ν = monomial ν 1` as in T014, `MvPowerSeries.coeff_monomial`); `(hasSum_ite_eq t _).unique h`.""",
  mathlib="""`HasSum.map`, `hasSum_ite_eq`, `HasSum.unique`, `AddMonoidHomClass.continuous_of_bound`, `MvPowerSeries.coeff_C_mul`, `MvPowerSeries.coeff_monomial`, `MvPowerSeries.X_pow_eq`. Floor/board: `algebraMap_apply`, `continuous_C`, `hasSum_eval₂`, `norm_coeff_le`, `val_add`, `val_mul`, `val_C`, T015.""",
  sources="""[BGR] 6.1.1/9, `bgr-6.1.1.md:113–115`; decomposition L4.16–L4.19.""",
  gen="""Continuous `α : A →ₐ[K] B` into a Banach algebra; no surjectivity.""")

t(id='T019', title='`A⟨X⟩ ↠ B⟨X⟩` for a surjective continuous homomorphism (open mapping)', file=EXT, deps='T018', par='no',
  typ='lemma', leaves='L4.20',
  decls=[(EXT,'surjective_mapAlgHom_of_surjective')],
  sketch="""`α` as a continuous linear map `αL : A →L[K] B := ⟨α.toLinearMap, hα⟩` (`LinearMap.mkContinuous`
with the bound of `exists_forall_norm_le_mul_of_continuous`, or `⟨_, hα⟩` directly); `obtain ⟨C, hC0, hC⟩ :=
ContinuousLinearMap.exists_preimage_norm_le αL hsurj`; for `g : Restricted B 1`, `choose a ha hna using fun ν ↦
hC (coeff ν g.1)`; `hres : IsRestricted 1 (fun ν ↦ a ν : MvPowerSeries σ A)`: unfold, `squeeze_zero` with
`‖a ν‖ * 1 ≤ C * ‖coeff ν g.1‖ * 1` and `g.2.const_mul C`; `refine ⟨⟨_, hres⟩, ?_⟩`; `Restricted.ext
(MvPowerSeries.ext fun t ↦ ?_)`, `coeff_mapAlgHom` (T018) and `ha t`.""",
  mathlib="""`ContinuousLinearMap.exists_preimage_norm_le`, `LinearMap.mkContinuous`, `squeeze_zero`, `Filter.Tendsto.const_mul`. Board: `coeff_mapAlgHom` (T018), floor `Restricted.ext`, `MvPowerSeries.ext`, `IsRestricted`.""",
  sources="""[BGR] 6.1.1/9, `bgr-6.1.1.md:113–115`; decomposition L4.20.""",
  gen="""Banach `A` and `B` over a nontrivially normed field (Banach's theorem).""")

t(id='T020', title='Affinoid from generating systems; BGR 6.1.1/5 for the source `Tₙ`', file=EXT, deps='T017, T010, T013', par='no',
  typ='lemmas', leaves='L4.21–L4.23',
  decls=[(EXT,'of_isAffinoidGeneratingSystem'),(EXT,'of_isAffinoidGeneratingSystem_tateAlgebra'),(EXT,'of_finite_tateAlgebra')],
  sketch="""1. `of_isAffinoidGeneratingSystem`: `obtain ⟨hb, hsurj⟩ := hb; exact ⟨n, _, hsurj⟩` (the domain of
   `extendAlgHom (Algebra.ofId K B) _ b hb` is `Restricted K (1 : Fin n → ℝ) = TateAlgebra K n` by `abbrev`).
2. `of_isAffinoidGeneratingSystem_tateAlgebra`: `obtain ⟨hb, hsurj⟩ := hb;
   exact ⟨m + n, (extendAlgHom φ hφ b hb).comp (TateAlgebra.sumEquiv K n m).symm.toAlgHom,
   hsurj.comp (TateAlgebra.sumEquiv K n m).symm.surjective⟩`.
3. `of_finite_tateAlgebra`: `obtain ⟨m, b, hb⟩ := exists_isAffinoidGeneratingSystem_of_finite φ hφ hfin;
   exact of_isAffinoidGeneratingSystem_tateAlgebra φ hφ hb`.""",
  mathlib="""`AlgEquiv.symm`, `AlgEquiv.surjective`, `Function.Surjective.comp`. Board: T010, T017.""",
  sources="""[BGR] 6.1.1, `bgr-6.1.1.md:56–59`; 6.1.1/5, `:66–70`; decomposition L4.21–L4.23.""",
  gen="""Banach `B` over a complete ultrametric nontrivially normed field.""")

# ---------------------------------------------------------------- G5 BanachAlgebra/Noetherian
t(id='T021', title='The nonarchimedean Nakayama lemma (BGR 1.2.4/6)', file=NOE, deps='none', par='yes (with T022)', typ='lemma', leaves='L5.1',
  decls=[(NOE,'Ideal.forall_mem_of_forall_exists_eq_add_sum_mul_of_norm_lt_one')],
  sketch="""Work over the subring `A° := Subring.unitClosedBall A` acting on `A` (`#synth Module (unitClosedBall A) A`
gives `Algebra.toModule` through `Algebra.ofSubsemiring`): `N' : Submodule A° A := Submodule.span A° (Set.range x)`,
`N : Submodule A° A := I.restrictScalars A°` (`Submodule.restrictScalars`), `𝔫 := NormedRing.openUnitBallIdeal A`.
`have hle : N' ≤ N ⊔ 𝔫 • N' := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; obtain ⟨y, hy, c, hc, hx⟩ := h i;
rw [hx]; exact Submodule.add_mem_sup hy (Submodule.sum_mem _ fun μ _ ↦ Submodule.smul_mem_smul
(mem_openUnitBallIdeal.2 (hc μ)) (Submodule.subset_span (Set.mem_range_self μ))))` — `c μ * x μ` must be
written as `(⟨c μ, (hc μ).le⟩ : A°) • x μ` (`Subring.smul_def`/`Submonoid.smul_def`: the smul of a subring
element is multiplication). Then `have := Submodule.le_of_le_smul_of_le_jacobson_bot
(Submodule.fg_span (Set.finite_range x)) NormedRing.openUnitBallIdeal_le_jacobson_bot hle` and
`fun i ↦ this (Submodule.subset_span (Set.mem_range_self i))` (membership in `restrictScalars` is membership
in `I`: `Submodule.restrictScalars_mem`). The matrix argument of BGR is inside Mathlib's lemma.""",
  mathlib="""`Submodule.le_of_le_smul_of_le_jacobson_bot`, `Submodule.fg_span`, `Set.finite_range`, `Submodule.span_le`, `Submodule.add_mem_sup`, `Submodule.sum_mem`, `Submodule.smul_mem_smul`, `Submodule.subset_span`, `Submodule.restrictScalars`, `Submodule.restrictScalars_mem`, `Subring.smul_def`, `Algebra.ofSubsemiring`. PFA: `NormedRing.openUnitBallIdeal`, `mem_openUnitBallIdeal`, `openUnitBallIdeal_le_jacobson_bot`, `Subring.unitClosedBall`.""",
  sources="""[BGR] 1.2.4/6, `bgr-3.7.md:142–151`; 1.2.4/4 remark, `:137`; decomposition L5.1.""",
  gen="""Complete ultrametric normed commutative ring with `‖1‖ = 1` (so that `A°` is a subring and `𝔫 ≤ jacobson ⊥`); stated for the ring itself as a module.""")

t(id='T022', title='Banach open mapping for a finitely generated closed ideal; the closure of an ideal', file=NOE, deps='none', par='yes (with T021)',
  typ='lemmas', leaves='L5.2, L5.3',
  decls=[(NOE,'Ideal.exists_forall_exists_eq_sum_mul_norm_le'),(NOE,'Ideal.isClosed_coe_closure_restrictScalars')],
  sketch="""1. `exists_forall_exists_eq_sum_mul_norm_le`: `Jₖ := J.restrictScalars K` with `IsClosed (Jₖ : Set A)` (`hJ`),
   hence `CompleteSpace ↥Jₖ` (`IsClosed.completeSpace_coe`); the linear map `π : (Fin n → A) →ₗ[K] ↥Jₖ`,
   `π a := ⟨∑ i, a i * x i, J.sum_mem fun i _ ↦ J.mul_mem_left _ (hx ▸ Ideal.subset_span (Set.mem_range_self i))⟩`
   (`LinearMap.codRestrict` of `∑ i, (LinearMap.proj i) * x i`-style, or `LinearMap.mk` with `Finset.sum_add_distrib`,
   `Finset.smul_sum`); continuity: `continuous_finsetSum` of `(continuous_apply i).mul continuous_const`
   composed with `Continuous.subtype_mk`; `πL := LinearMap.mkContinuous`? — simpler `⟨π, hcont⟩ : _ →L[K] _`;
   surjective: for `⟨y, hy⟩`, `hx ▸ hy : y ∈ span (range x)` and `Ideal.mem_span_range_iff_exists_fun`
   gives `a` with `∑ a i * x i = y`; `obtain ⟨C, hC0, hC⟩ := ContinuousLinearMap.exists_preimage_norm_le πL hsurj`;
   `refine ⟨C, hC0, fun y hy ↦ ?_⟩`; `obtain ⟨a, ha, hna⟩ := hC ⟨y, hy⟩`; `⟨a, congrArg Subtype.val ha ▸ rfl?, fun i ↦
   (norm_le_pi_norm a i).trans hna⟩` (the norm of `⟨y, hy⟩` is `‖y‖`: `Submodule.coe_norm`).
2. `isClosed_coe_closure_restrictScalars`: `show IsClosed (closure (I : Set A))` via `Ideal.coe_closure`
   (`Submodule.coe_restrictScalars`), `isClosed_closure`.""",
  mathlib="""`IsClosed.completeSpace_coe`, `LinearMap.codRestrict`, `continuous_finsetSum`, `continuous_apply`, `Continuous.subtype_mk`, `ContinuousLinearMap.exists_preimage_norm_le`, `Ideal.mem_span_range_iff_exists_fun`, `Ideal.subset_span`, `Ideal.sum_mem`, `Ideal.mul_mem_left`, `norm_le_pi_norm`, `Submodule.coe_norm`, `Ideal.coe_closure`, `Submodule.coe_restrictScalars`, `isClosed_closure`.""",
  sources="""[BGR] 3.7.2/1, `bgr-3.7.md:29–31`; decomposition L5.2–L5.3.""",
  gen="""Banach algebra over a nontrivially normed field; the ideal is closed and generated by the given finite family (D1).""")

t(id='T023', title='Ideals of a noetherian Banach algebra are closed (BGR 3.7.2/1–2)', file=NOE, deps='T021, T022', par='no',
  typ='lemma', leaves='L5.4',
  decls=[(NOE,'Ideal.isClosed_of_fg_closure')],
  sketch="""`obtain ⟨n, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg` (`span (range x) = I.closure`);
`obtain ⟨C, hC0, hC⟩ := Ideal.exists_forall_exists_eq_sum_mul_norm_le x I.closure
(by rw [Ideal.coe_closure]; exact isClosed_closure) hx`; claim `∀ i, x i ∈ I` by T021 with `h i`:
`have hxi : x i ∈ closure (I : Set A) := by rw [← Ideal.coe_closure, ← hx]; exact Ideal.subset_span (Set.mem_range_self i)`;
`obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.1 hxi (C⁻¹) (inv_pos.2 hC0)`;
`have hmem : x i - y ∈ I.closure := I.closure.sub_mem (hx ▸ Ideal.subset_span …) (Ideal.le_closure? hy)`
(`I ≤ I.closure`: `Ideal.le_closure`? — `subset_closure` through `Ideal.coe_closure`);
`obtain ⟨c, hc, hcn⟩ := hC _ hmem`; `refine ⟨y, hy, c, fun μ ↦ ?_, by rw [← hc]; abel? ⟩` with
`‖c μ‖ ≤ C * ‖x i - y‖ < C * C⁻¹ = 1` (`dist_eq_norm`, `mul_lt_mul_of_pos_left`, `mul_inv_cancel₀`).
Then `I.closure ≤ I`: `hx ▸ Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact this i)`, so
`closure (I : Set A) ⊆ I` (`Ideal.coe_closure ▸`), and `isClosed_of_closure_subset`.""",
  mathlib="""`Submodule.fg_iff_exists_fin_generating_family`, `Metric.mem_closure_iff`, `dist_eq_norm`, `inv_pos`, `mul_lt_mul_of_pos_left`, `mul_inv_cancel₀`, `Ideal.coe_closure`, `subset_closure`, `Ideal.span_le`, `isClosed_of_closure_subset`. Board: T021, T022.""",
  sources="""[BGR] 3.7.2/1, `bgr-3.7.md:27–33`; 3.7.2/2, `:39–41`; decomposition L5.4.""",
  gen="""Complete ultrametric normed commutative `K`-algebra with `‖1‖ = 1`, `K` nontrivially normed; the ideal's closure finitely generated (noetherian in `isClosed_of_isNoetherianRing`).""")

# ---------------------------------------------------------------- G6 BanachAlgebra/Continuity
t(id='T024', title='Linear maps into finite-dimensional spaces with closed kernel are continuous; the residue maps of BGR 3.7.5/1', file=BCO, deps='none',
  par='yes (with T021)', typ='lemmas', leaves='L6.1, L6.2',
  decls=[(BCO,'LinearMap.continuous_of_isClosed_ker_of_finiteDimensional'),(BCO,'AlgHom.continuous_quotient_mk_comp_of_isClosed')],
  sketch="""1. `continuous_of_isClosed_ker_of_finiteDimensional`: `haveI : IsClosed ((LinearMap.ker f : Submodule K E) : Set E) := hf`
   (the instance for `Submodule.Quotient.normedAddCommGroup`); `haveI : FiniteDimensional K (E ⧸ LinearMap.ker f) :=
   (f.quotKerEquivRange).finiteDimensional` (the range is a submodule of the finite-dimensional `F`:
   instance `FiniteDimensional.finiteDimensional_submodule`); `have : ⇑f = ⇑((LinearMap.ker f).liftQ f le_rfl) ∘ ⇑(LinearMap.ker f).mkQ :=
   by ext; simp [Submodule.liftQ_apply]`; `rw [this]; exact (LinearMap.continuous_of_finiteDimensional _).comp
   continuous_quot_mk` — the domain `E ⧸ ker f` is `T2` because it is a normed group (closed kernel).
2. `continuous_quotient_mk_comp_of_isClosed`: apply item 1 to `((Ideal.Quotient.mkₐ K 𝔟).comp Φ).toLinearMap`;
   its kernel as a set is `𝔟.comap Φ`: `LinearMap.ker` of the `toLinearMap` equals `RingHom.ker` as sets
   (`AlgHom.toLinearMap_apply`, `Ideal.mem_comap`, `Ideal.Quotient.eq_zero_iff_mem`); `Set.ext` and `hA`.""",
  mathlib="""`LinearMap.quotKerEquivRange`, `LinearEquiv.finiteDimensional`, `FiniteDimensional.finiteDimensional_submodule`, `Submodule.liftQ`, `Submodule.liftQ_apply`, `Submodule.mkQ`, `continuous_quot_mk`, `LinearMap.continuous_of_finiteDimensional`, `Submodule.Quotient.normedAddCommGroup`, `Ideal.Quotient.mkₐ`, `Ideal.mem_comap`, `Ideal.Quotient.eq_zero_iff_mem`, `AlgHom.toLinearMap_apply`.""",
  sources="""[BGR] 3.7.5/1, `bgr-3.7.md:103–107`; decomposition L6.1–L6.2.""",
  gen="""Normed spaces over a complete nontrivially normed field (Mathlib's finite-dimensional continuity needs completeness of `K`).""")

t(id='T025', title='BGR 3.7.5/1: continuity by the closed graph theorem', file=BCO, deps='T024', par='no', typ='lemma', leaves='L6.3',
  decls=[(BCO,'AlgHom.continuous_of_forall_isClosed_of_finiteDimensional')],
  sketch="""`have := LinearMap.continuous_of_seq_closed_graph Φ.toLinearMap fun u x y hu hΦu ↦ ?_; exact this`
(coercions: `⇑Φ.toLinearMap = ⇑Φ`). For the graph condition: `suffices y - Φ x ∈ sInf 𝔅 by rwa [hinf, Ideal.mem_bot, sub_eq_zero] at this`;
`Ideal.mem_sInf.2 fun 𝔟 h𝔟 ↦ ?_`; `haveI := hB 𝔟 h𝔟; haveI := hfin 𝔟 h𝔟`;
`have h₁ : Tendsto (fun n ↦ Ideal.Quotient.mk 𝔟 (Φ (u n))) atTop (𝓝 (Ideal.Quotient.mk 𝔟 (Φ x))) :=
((Φ.continuous_quotient_mk_comp_of_isClosed 𝔟 (hA 𝔟 h𝔟)).tendsto x).comp hu` (as a composite function:
`(mkₐ K 𝔟).comp Φ` applied is `mk (Φ _)`); `have h₂ : Tendsto (fun n ↦ mk 𝔟 (Φ (u n))) atTop (𝓝 (mk 𝔟 y)) :=
(continuous_quot_mk.tendsto y).comp hΦu`; `have := tendsto_nhds_unique h₁ h₂` (the quotient is `T2`: normed
with closed `𝔟`); `rwa [Ideal.Quotient.eq] at this` (gives `Φ x - y ∈ 𝔟`; adjust sign with `𝔟.neg_mem`/`neg_sub`).""",
  mathlib="""`LinearMap.continuous_of_seq_closed_graph`, `Ideal.mem_sInf`, `Ideal.mem_bot`, `sub_eq_zero`, `Filter.Tendsto.comp`, `Continuous.tendsto`, `continuous_quot_mk`, `tendsto_nhds_unique`, `Ideal.Quotient.eq`, `Ideal.neg_mem_iff`, `neg_sub`. Board: T024.""",
  sources="""[BGR] 3.7.5/1, `bgr-3.7.md:97–111`; decomposition L6.3.""",
  gen="""Banach algebras `A`, `B` over a complete nontrivially normed field; the family `𝔅` arbitrary.""")

t(id='T026', title='BGR 3.7.5/2–3: noetherian Banach algebras', file=BCO, deps='T025, T023', par='no', typ='lemmas', leaves='L6.4–L6.6',
  decls=[(BCO,'AlgHom.continuous_of_isNoetherianRing'),(BCO,'AlgEquiv.continuous_symm_of_isNoetherianRing'),(BCO,'AlgEquiv.exists_forall_norm_le_mul_of_isNoetherianRing')],
  sketch="""1. `continuous_of_isNoetherianRing`: `Φ.continuous_of_forall_isClosed_of_finiteDimensional 𝔅
   (fun 𝔟 _ ↦ 𝔟.isClosed_of_isNoetherianRing) (fun 𝔟 _ ↦ (𝔟.comap Φ).isClosed_of_isNoetherianRing) hfin hinf`.
2. `continuous_symm_of_isNoetherianRing`: `e.toLinearEquiv.continuous_symm (e.continuous_of_isNoetherianRing 𝔅 hfin hinf)`
   (`LinearEquiv.continuous_symm` needs both spaces complete ✓; coercions `AlgEquiv.toLinearEquiv_apply`).
3. `exists_forall_norm_le_mul_of_isNoetherianRing`: `obtain ⟨C, -, hC⟩ := SemilinearMapClass.bound_of_continuous
   e.toAlgHom (…)`, same for `e.symm.toAlgHom`; `⟨C, C', hC, hC'⟩`.""",
  mathlib="""`LinearEquiv.continuous_symm`, `AlgEquiv.toLinearEquiv`, `SemilinearMapClass.bound_of_continuous`. Board: T023, T025.""",
  sources="""[BGR] 3.7.5/2–3, `bgr-3.7.md:113–121`; decomposition L6.4–L6.6.""",
  gen="""Noetherian Banach algebras with `‖1‖ = 1`, ultrametric (G5's hypotheses), over a complete nontrivially normed field.""")

# ---------------------------------------------------------------- G7 Affinoid/Noether
t(id='T027', title='Weierstrass finiteness and injectivity for a distinguished kernel element', file=NTH, deps='none',
  par='yes (with T021)', typ='lemmas', leaves='L7.1, L7.2',
  decls=[(NTH,'finite_comp_ofTail_of_isMulDistinguishedX0'),(NTH,'injective_mk_comp_ofTail_of_isMulDistinguishedX0')],
  sketch="""1. `finite_comp_ofTail_of_isMulDistinguishedX0`: copy Layer 0's `IsWeierstrassPolynomial.finite_comp_ofTail`
   (`TateAlgebra/Finiteness.lean`) with `g` in place of `ofPolynomial K n ω`: `hle : Ideal.span {g} ≤ RingHom.ker φ`
   (`Ideal.span_le`, `Set.singleton_subset_iff`, `h0`); `φ' := Ideal.Quotient.lift _ φ (fun a ha ↦ hle ha)`;
   `φ = φ'.comp (Ideal.Quotient.mk _)` (`Ideal.Quotient.lift_comp_mk`); `RingHom.Finite.of_comp_finite` gives
   `φ'.Finite`; `rw [hφ', RingHom.comp_assoc]; exact hfin.comp (finite_mk_comp_ofTail_of_isMulDistinguishedX0 hg)`.
2. `injective_mk_comp_ofTail_of_isMulDistinguishedX0`: `intro f₁ f₂ h`; reduce to `f = 0` for
   `f := f₁ - f₂` via `injective_iff_map_eq_zero` (`(injective_iff_map_eq_zero _).2 fun f hf ↦ ?_`);
   `rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hf; obtain ⟨q, hq⟩ := hf`
   (`q * g = ofTail K n f`); two Weierstrass divisions of `ofTail K n f` by `g`:
   `h₁ : q * g + ofPolynomial K n 0 = ofTail K n f` (`map_zero`, `add_zero`) and
   `h₂ : 0 * g + ofPolynomial K n (Polynomial.C f) = ofTail K n f` (`zero_mul`, `zero_add`, `ofTail_apply`);
   `weierstrassDivision_r_unique hg` with the degree hypotheses `(Polynomial.degree 0 < s)` (`Polynomial.degree_zero`,
   `WithBot.bot_lt_coe`) and `(Polynomial.C f).degree < s` (`Polynomial.degree_C_le.trans_lt`, `hs` as `0 < s`
   via `Nat.pos_of_ne_zero`, cast to `WithBot ℕ`) — read the exact argument order with
   `#check @Affinoid.TateAlgebra.weierstrassDivision_r_unique` first (Layer 0's `existsUnique_remainder` in
   `Finiteness.lean` shows a use); conclude `Polynomial.C f = 0` (`ofPolynomial_injective`), `Polynomial.C_eq_zero`.""",
  mathlib="""`Ideal.span_le`, `Set.singleton_subset_iff`, `Ideal.Quotient.lift`, `Ideal.Quotient.lift_comp_mk`, `RingHom.Finite.of_comp_finite`, `RingHom.Finite.comp`, `RingHom.comp_assoc`, `injective_iff_map_eq_zero`, `Ideal.Quotient.eq_zero_iff_mem`, `Ideal.mem_span_singleton'`, `Polynomial.degree_zero`, `Polynomial.degree_C_le`, `Polynomial.C_eq_zero`, `WithBot.bot_lt_coe`. Layer 0: `finite_mk_comp_ofTail_of_isMulDistinguishedX0`, `weierstrassDivision_r_unique`, `ofTail_apply`, `ofPolynomial_injective`, `IsWeierstrassPolynomial.finite_comp_ofTail` (model).""",
  sources="""[BGR] 6.1.2/1, `bgr-6.1.2.md:37–40`; 5.2.3/4; decomposition L7.1–L7.2 (D6).""",
  gen="""Any `X 0`-distinguished `g` (not only Weierstrass polynomials); `s ≠ 0` for injectivity.""")

t(id='T028', title='The induction step of Noether normalisation; the case `n = 0`', file=NTH, deps='T027', par='no',
  typ='lemmas', leaves='L7.3, L7.4',
  decls=[(NTH,'exists_finite_comp_shear_symm_comp_ofTail'),(NTH,'injective_of_nontrivial')],
  sketch="""1. `exists_finite_comp_shear_symm_comp_ofTail`: `obtain ⟨e, s, hs⟩ := exists_shear_isMulDistinguishedX0 hf`;
   `refine ⟨e, ?_⟩`; `have hβ' : (β.comp (shear K n e).symm.toAlgHom).toRingHom.Finite :=
   hβ.comp (RingHom.Finite.of_surjective _ (shear K n e).symm.surjective)` (match the coercions:
   `AlgHom.comp_toRingHom`, `AlgEquiv.toAlgHom_toRingHom`); `have h0' : (β.comp (shear K n e).symm.toAlgHom) (shear K n e f) = 0 :=
   by simp [h0]` (`AlgEquiv.symm_apply_apply`); `exact finite_comp_ofTail_of_isMulDistinguishedX0 _ hβ' hs h0'`
   (after `show` that `((β.comp _).comp (ofTailAlgHom K n)).toRingHom = (β.comp _).toRingHom.comp (ofTail K n)`,
   `rfl`).
2. `injective_of_nontrivial`: `have : Function.Injective (β.toRingHom.comp (Restricted.isEmptyEquiv K (1 : Fin 0 → ℝ)).symm.toRingHom) :=
   RingHom.injective _` (division ring source, nontrivial target); `fun a b h ↦ (isEmptyEquiv K 1).injective? …` —
   cleaner: `intro a b hab; have := this (congrArg … )`: rewrite `a = e.symm (e a)` (`RingEquiv.symm_apply_apply`)
   and apply injectivity of the composite to `e a`, `e b`.""",
  mathlib="""`RingHom.Finite.of_surjective`, `RingHom.Finite.comp`, `AlgEquiv.symm_apply_apply`, `AlgEquiv.surjective`, `RingHom.injective`, `RingEquiv.symm_apply_apply`, `RingEquiv.injective`. Layer 0: `exists_shear_isMulDistinguishedX0`, `shear`, `isEmptyEquiv`; board T027, `ofTailAlgHom`.""",
  sources="""[BGR] 6.1.2/1, `bgr-6.1.2.md:31–34`; decomposition L7.3–L7.4.""",
  gen="""Any `K`-algebra `A` (no norm); `Nontrivial A` for item 2.""")

t(id='T029', title='BGR 6.1.2/1 (i): the induction', file=NTH, deps='T028', par='no', typ='lemma', leaves='L7.5',
  decls=[(NTH,'exists_finite_injective_comp',0)],
  sketch="""`induction n with` (generalising `β`):
- `zero`: `exact ⟨0, le_rfl, AlgHom.id K _, by simpa using hβ, by simpa using injective_of_nontrivial β⟩`
  (`AlgHom.comp_id`).
- `succ n ih`: `by_cases hker : RingHom.ker β.toRingHom = ⊥`.
  · `exact ⟨n + 1, le_rfl, AlgHom.id K _, by simpa using hβ, by simpa using (RingHom.injective_iff_ker_eq_bot _).2 hker⟩`.
  · `obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker` (`f ∈ ker`, `f ≠ 0`);
    `obtain ⟨e, hfin⟩ := exists_finite_comp_shear_symm_comp_ofTail β hβ hf0 (by simpa using hf)`
    (`RingHom.mem_ker`); `obtain ⟨d, hd, ψ', hfin', hinj'⟩ := ih _ hfin`;
    `refine ⟨d, hd.trans (Nat.le_succ n), ((shear K n e).symm.toAlgHom.comp (ofTailAlgHom K n)).comp ψ', ?_, ?_⟩ <;>
    simpa [AlgHom.comp_assoc] using hfin'` / `hinj'` (the composite `β.comp (((shear).symm).comp (ofTailAlgHom)).comp ψ'`
    is `((β.comp (shear).symm).comp ofTailAlgHom).comp ψ'` by `AlgHom.comp_assoc`; `convert` if `simpa` fails).""",
  mathlib="""`AlgHom.comp_id`, `AlgHom.comp_assoc`, `RingHom.injective_iff_ker_eq_bot`, `Submodule.exists_mem_ne_zero_of_ne_bot`, `RingHom.mem_ker`, `Nat.le_succ`. Board: T028.""",
  sources="""[BGR] 6.1.2/1, `bgr-6.1.2.md:31–41`; decomposition L7.5.""",
  gen="""For every finite `β : Tₙ →ₐ[K] A` into a nontrivial algebra (BGR's (i)).""")

t(id='T030', title='Noether normalisation (BGR 6.1.2/1 (ii) and 6.1.2/2)', file=NTH, deps='T029', par='no', typ='lemmas', leaves='L7.6, L7.7',
  milestone='M2 — `IsAffinoidAlgebra.exists_finite_injective`: every nonzero affinoid algebra is a finite extension of a Tate algebra ([RM] §1.2.1; BGR 6.1.2/2; Bosch 1.4/2 (iii)). `#print axioms` must be standard.',
  decls=[(NTH,'exists_finite_injective_comp',1),(NTH,'exists_finite_injective')],
  sketch="""1. `IsAffinoidAlgebra.exists_finite_injective_comp`: `obtain ⟨n, α, hα⟩ := hB`;
   `have hfin : (φ.comp α).toRingHom.Finite := hφ.comp (RingHom.Finite.of_surjective _ hα)` (coercions as in T028);
   `obtain ⟨d, -, ψ, h₁, h₂⟩ := Affinoid.TateAlgebra.exists_finite_injective_comp n (φ.comp α) hfin`;
   `exact ⟨d, α.comp ψ, by rwa [← AlgHom.comp_assoc], by rwa [← AlgHom.comp_assoc]⟩`.
2. `exists_finite_injective`: `obtain ⟨d, ψ, h₁, h₂⟩ := hA.exists_finite_injective_comp (AlgHom.id K A) RingHom.Finite.id`;
   `exact ⟨d, ψ, by simpa using h₁, by simpa using h₂⟩` (`AlgHom.id_comp`).
Then run `#print axioms IsAffinoidAlgebra.exists_finite_injective` (`scratch/axioms.py`).""",
  mathlib="""`RingHom.Finite.of_surjective`, `RingHom.Finite.comp`, `RingHom.Finite.id`, `AlgHom.comp_assoc`, `AlgHom.id_comp`. Board: T029.""",
  sources="""[BGR] 6.1.2/1 (ii), `bgr-6.1.2.md:27–30`; 6.1.2/2, `:46–47`; [Bo] 1.4/2, `bosch-lectures.txt:1011–1012`; decomposition L7.6–L7.7.""",
  gen="""Nonzero `K`-algebras, no norm.""")

t(id='T031', title='`dim A = d`: going-up for the Krull dimension', file=NTH, deps='T030', par='no', typ='lemmas', leaves='L7.8–L7.10',
  decls=[(NTH,'ringKrullDim_le_of_isIntegral_of_injective'),(NTH,'ringKrullDim_eq_of_finite_injective'),(NTH,'exists_ringKrullDim_eq')],
  sketch="""1. `ringKrullDim_le_of_isIntegral_of_injective`: `letI := f.toAlgebra; haveI : Algebra.IsIntegral R S := ⟨hf⟩`
   (`RingHom.IsIntegral` unfolds to `∀ x, IsIntegral R x` under `toAlgebra`; if the constructor shape differs use
   `Algebra.IsIntegral.mk`); `unfold ringKrullDim; refine Order.krullDim_le_of_… `? — direct: `Order.krullDim`
   is `⨆ l : LTSeries α, l.length`; use `Order.krullDim_le_iff`/`iSup_le fun l ↦ ?_` (name: `Order.krullDim_le_iff`
   **(search)** if absent, `Order.LTSeries.length_le_krullDim` plus `iSup_le`); for `l : LTSeries (PrimeSpectrum R)`,
   `haveI := l.head.isPrime`; `obtain ⟨P, -, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal ⊥
   (by rw [Ideal.comap_bot_of_injective? ]…)` — the hypothesis is `(⊥ : Ideal S).comap (algebraMap R S) ≤ l.head.asIdeal`,
   and `Ideal.comap ⊥ = RingHom.ker = ⊥` by `RingHom.ker_eq_bot_iff`? (`(RingHom.injective_iff_ker_eq_bot f).1 hinj`,
   `RingHom.ker_eq_comap_bot`), then `bot_le`; `haveI : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩`
   (`Ideal.LiesOver` is `P.under = p`: `Ideal.under_def`); `obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P`;
   `exact hlen ▸ Order.LTSeries.length_le_krullDim L` (cast `ℕ → WithBot ℕ∞`).
2. `ringKrullDim_eq_of_finite_injective`: `le_antisymm`; `≤`: `(ringKrullDim_le_of_isIntegral φ.toRingHom hφ.to_isIntegral).trans_eq
   (Affinoid.TateAlgebra.ringKrullDim_eq K d)`; `≥`: `(Affinoid.TateAlgebra.ringKrullDim_eq K d) ▸
   ringKrullDim_le_of_isIntegral_of_injective φ.toRingHom hφ.to_isIntegral hinj`.
3. `exists_ringKrullDim_eq`: `obtain ⟨d, φ, h₁, h₂⟩ := hA.exists_finite_injective; exact ⟨d, ringKrullDim_eq_of_finite_injective φ h₁ h₂⟩`.""",
  mathlib="""`RingHom.toAlgebra`, `Algebra.IsIntegral`, `Algebra.HasGoingUp.of_isIntegral`, `Ideal.exists_ideal_over_prime_of_isIntegral`, `Ideal.exists_ltSeries_of_hasGoingUp`, `Ideal.LiesOver`, `Ideal.under_def`, `RingHom.injective_iff_ker_eq_bot`, `RingHom.ker_eq_comap_bot`, `Order.LTSeries.length_le_krullDim`, `Order.krullDim`, `iSup_le`, `RingHom.Finite.to_isIntegral`, `PrimeSpectrum.isPrime`. Layer 0: `ringKrullDim_le_of_isIntegral`, `Affinoid.TateAlgebra.ringKrullDim_eq`. Imports: `Mathlib.RingTheory.Ideal.HasGoingUp` (already).""",
  sources="""[BGR] 6.1.2 (Remark), `bgr-6.1.2.md:49–51`; decomposition L7.8–L7.10.""",
  gen="""Item 1 for any injective integral ring homomorphism of commutative rings (a general Mathlib-shaped lemma).""")

t(id='T032', title='Finite over `T₀` is finite-dimensional; reduced injectivity; a Tate algebra that is a field', file=NTH, deps='none',
  par='yes (with T027)', typ='lemmas', leaves='L7.11–L7.13',
  decls=[(NTH,'finiteDimensional_of_finite_zero'),(NTH,'injective_factor_comp_of_injective'),(NTH,'_root_.Affinoid.TateAlgebra.eq_zero_of_isField')],
  sketch="""1. `finiteDimensional_of_finite_zero`: `letI := φ.toRingHom.toAlgebra; haveI : Module.Finite (TateAlgebra K 0) A := hφ;
   haveI : IsScalarTower K (TateAlgebra K 0) A := IsScalarTower.of_algebraMap_eq fun c ↦ (φ.commutes c).symm`
   (check the direction: `algebraMap K A c = algebraMap (T₀) A (algebraMap K T₀ c)` with
   `RingHom.algebraMap_toAlgebra`); `haveI : Module.Finite K (TateAlgebra K 0) :=
   Module.Finite.of_surjective? ` — use the linear equivalence `T₀ ≃ₗ[K] K` from `isEmptyEquiv`: build
   `(Restricted.isEmptyEquiv K 1).toAddEquiv.toLinearEquiv` with `map_smul` from `isEmptyEquiv_apply`
   (`constantCoeff` of `c • f` is `c * constantCoeff f`), then `LinearEquiv.finiteDimensional`
   (`Module.Finite.self K`); finally `Module.Finite.trans (TateAlgebra K 0) A`.
2. `injective_factor_comp_of_injective`: `(injective_iff_map_eq_zero _).2 fun r hr ↦ ?_`;
   `obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (φ r)`; `rw [RingHom.comp_apply, ← ha, Ideal.Quotient.factor_mk,
   Ideal.Quotient.eq_zero_iff_mem] at hr` (`a ∈ 𝔮.radical`); `obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.1 hr`? —
   `Ideal.mem_radical_iff : r ∈ I.radical ↔ ∃ n, r ^ n ∈ I`; then `φ (r ^ m) = (φ r) ^ m = mk (a ^ m) = 0`
   (`map_pow`, `← ha`, `Ideal.Quotient.eq_zero_iff_mem.2 hm`), so `r ^ m = 0` (`hφ`, `map_zero`),
   `(pow_eq_zero_iff? )`: `IsReduced` gives `r = 0` from `r ^ m = 0` (`pow_eq_zero_iff` needs `m ≠ 0`:
   if `m = 0` then `1 ∈ 𝔮`, so `mk a = 0`… handle by `rcases m` or use `pow_eq_zero_iff`).
3. `eq_zero_of_isField`: `have h1 := ringKrullDim_eq_zero_of_isField h; rw [Affinoid.TateAlgebra.ringKrullDim_eq K d] at h1;
   exact_mod_cast h1` (through `WithBot ℕ∞`: `Nat.cast_eq_zero` after `WithBot.coe_eq_zero`/`Nat.cast_eq_zero`;
   `norm_cast at h1` first).""",
  mathlib="""`RingHom.toAlgebra`, `RingHom.algebraMap_toAlgebra`, `IsScalarTower.of_algebraMap_eq`, `Module.Finite.trans`, `Module.Finite.self`, `LinearEquiv.finiteDimensional`, `AddEquiv.toLinearEquiv`, `injective_iff_map_eq_zero`, `Ideal.Quotient.mk_surjective`, `Ideal.Quotient.factor_mk`, `Ideal.Quotient.eq_zero_iff_mem`, `Ideal.mem_radical_iff`, `map_pow`, `pow_eq_zero_iff`, `ringKrullDim_eq_zero_of_isField`, `WithBot.coe_eq_zero`, `Nat.cast_eq_zero`. Layer 0: `isEmptyEquiv`, `isEmptyEquiv_apply`, `Affinoid.TateAlgebra.ringKrullDim_eq`.""",
  sources="""[BGR] 6.1.2/3, `bgr-6.1.2.md:62–65`; decomposition L7.11–L7.13.""",
  gen="""Item 2 for any reduced ring `R` and any ideal; item 1 for any `K`-algebra.""")

t(id='T033', title='BGR 6.1.2/3: residue rings with maximal radical are finite-dimensional; preimages of maximal ideals', file=NTH, deps='T030, T032', par='no',
  typ='lemmas', leaves='L7.14, L7.15',
  decls=[(NTH,'finiteDimensional_quotient_of_radical_isMaximal'),(NTH,'_root_.Ideal.isMaximal_comap_of_isAffinoidAlgebra')],
  sketch="""1. `finiteDimensional_quotient_of_radical_isMaximal`: `haveI : Nontrivial (A ⧸ 𝔮) := Ideal.Quotient.nontrivial_iff.2
   (fun h𝔮 ↦ h.ne_top (by rw [h𝔮, Ideal.radical_top]))`; `obtain ⟨d, φ, hφ, hinj⟩ := (hA.quotient 𝔮).exists_finite_injective`;
   `ψ := (Ideal.Quotient.factor 𝔮.le_radical).comp φ.toRingHom`; `hψinj := injective_factor_comp_of_injective 𝔮 φ.toRingHom hinj`
   (`T_d` is reduced: `IsDomain` instance from Layer 0, `IsReduced` from `IsDomain`); `hψint : ψ.IsIntegral :=
   (RingHom.Finite.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.factor_surjective) hφ).to_isIntegral`;
   `letI := ψ.toAlgebra; haveI : Algebra.IsIntegral (TateAlgebra K d) (A ⧸ 𝔮.radical) := ⟨hψint⟩`;
   `haveI : 𝔮.radical.IsMaximal := h; letI := Ideal.Quotient.field 𝔮.radical`;
   `have hfield : IsField (TateAlgebra K d) := (Algebra.IsIntegral.isField_iff_isField hψinj).2 (Field.toIsField _)`;
   `obtain rfl := Affinoid.TateAlgebra.eq_zero_of_isField hfield`; `exact finiteDimensional_of_finite_zero φ hφ`.
   (If `Ideal.Quotient.field` conflicts with the existing `CommRing` instance, use `Ideal.Quotient.isField`? —
   `Ideal.Quotient.maximal_ideal_iff_isField_quotient`: `(Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 h`.)
2. `isMaximal_comap_of_isAffinoidAlgebra`: `haveI : 𝔪.IsPrime := ‹𝔪.IsMaximal›.isPrime`;
   `haveI : (𝔪.comap φ).IsPrime := Ideal.IsPrime.comap φ`; `hfd : FiniteDimensional K (B ⧸ 𝔪) :=
   hB.finiteDimensional_quotient_of_isMaximal 𝔪`; the injective `K`-linear map
   `(Ideal.quotientMapₐ 𝔪 φ le_rfl).toLinearMap` with `Ideal.quotientMap_injective` gives
   `FiniteDimensional K (A ⧸ 𝔪.comap φ)` (`FiniteDimensional.of_injective`); `haveI : IsDomain (A ⧸ 𝔪.comap φ) :=
   Ideal.Quotient.isDomain _`; `Ideal.Quotient.maximal_of_isField _ (isField_of_isIntegral_of_isField'
   (Field.toIsField K))` with `Algebra.IsIntegral.of_finite` (instance from `Module.Finite K _`).""",
  mathlib="""`Ideal.Quotient.nontrivial_iff`, `Ideal.radical_top`, `Ideal.Quotient.factor`, `Ideal.Quotient.factor_surjective`, `RingHom.Finite.comp`, `RingHom.Finite.of_surjective`, `RingHom.Finite.to_isIntegral`, `Algebra.IsIntegral.isField_iff_isField`, `Ideal.Quotient.field`, `Ideal.Quotient.maximal_ideal_iff_isField_quotient`, `Field.toIsField`, `Ideal.IsPrime.comap`, `Ideal.quotientMapₐ`, `Ideal.quotientMap_injective`, `FiniteDimensional.of_injective`, `Ideal.Quotient.isDomain`, `Ideal.Quotient.maximal_of_isField`, `isField_of_isIntegral_of_isField'`, `Algebra.IsIntegral.of_finite`. Board: T030, T032; Layer 0 `instIsDomain`.""",
  sources="""[BGR] 6.1.2/3, `bgr-6.1.2.md:59–65`; [Bo] 1.4/3, `bosch-lectures.txt:1013–1019`; [RM] §1.2.4; decomposition L7.14–L7.15.""",
  gen="""Item 2 needs only the target affinoid (E3).""")

t(id='T034', title='The fraction field of a finite extension of domains', file=NTH, deps='none', par='yes (with T027)', typ='lemmas', leaves='L7.16, L7.17',
  decls=[(NTH,'_root_.IsFractionRing.isLocalization_algebraMapSubmonoid_of_isIntegral'),(NTH,'_root_.FractionRing.finiteDimensional_of_finite')],
  sketch="""1. `isLocalization_algebraMapSubmonoid_of_isIntegral`: build `IsLocalization M (FractionRing S)` for
   `M := Algebra.algebraMapSubmonoid S (nonZeroDivisors R)` with the constructor (`IsLocalization.mk`? use
   `{ map_units := …, surj := …, exists_of_eq := … }` after `#check @IsLocalization.mk`):
   - `map_units ⟨_, ⟨r, hr, rfl⟩⟩`: `IsLocalization.map_units (FractionRing S) ⟨algebraMap R S r, _⟩` with
     `algebraMap R S r ∈ S⁰` (`mem_nonZeroDivisors_of_ne_zero`, `hinj.ne (nonZeroDivisors.ne_zero hr)`-style;
     `map_ne_zero_of_mem_nonZeroDivisors`).
   - `surj z`: `obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.surj (nonZeroDivisors S) z` (`z * algebraMap t = algebraMap s`);
     the key lemma **(search)**: for `t ≠ 0` integral over `R`, `∃ u : S, ∃ r : R, r ≠ 0 ∧ t * u = algebraMap R S r`.
     Prove it inline: `obtain ⟨p, hp, hpt⟩ := (Algebra.IsIntegral.isIntegral t)`, `p` monic with `aeval t p = 0`;
     `Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd`-free route: write `p = X ^ k * q` with
     `¬ X ∣ q` (`Polynomial.X_pow_dvd_iff`, `Polynomial.natTrailingDegree`: `p = X^{natTrailingDegree p} * q`
     with `q.coeff 0 ≠ 0`, Mathlib: `Polynomial.eq_X_pow_mul_shift?`/`Polynomial.coeff_zero_eq_eval_zero`…;
     alternatively use the *minimal polynomial* `minpoly R t`? no (R not a field)); since `S` is a domain and
     `t ≠ 0`, `aeval t q = 0`; then `q = X * q' + C (q.coeff 0)` (`Polynomial.X_mul_divX_add`), so
     `t * aeval t q' = -algebraMap (q.coeff 0)` with `q.coeff 0 ≠ 0` ✓. Then `z = mk' (s * u) ⟨algebraMap r, _⟩`:
     `IsLocalization.mk'_eq_iff_eq_mul`/`IsLocalization.eq_mk'_iff_mul_eq`.
   - `exists_of_eq h`: `⟨1, by simpa using (IsFractionRing.injective S (FractionRing S)) h⟩`.
   This is the hardest leaf of G7; budget 80 lines.
2. `finiteDimensional_of_finite`: `haveI := isLocalization_algebraMapSubmonoid_of_isIntegral R S hinj`
   (with `Algebra.IsIntegral.of_finite`); `exact Module.Finite.of_isLocalization R S (nonZeroDivisors R)`
   (import `Mathlib.RingTheory.Localization.Finiteness`; its instance arguments: `IsLocalization R⁰ (FractionRing R)` ✓,
   the given algebra and tower, `IsScalarTower R S (FractionRing S)` ✓).""",
  mathlib="""`IsLocalization` (constructor), `IsLocalization.map_units`, `IsLocalization.surj`, `IsLocalization.mk'`, `IsLocalization.eq_mk'_iff_mul_eq`, `IsFractionRing.injective`, `map_ne_zero_of_mem_nonZeroDivisors`, `mem_nonZeroDivisors_of_ne_zero`, `Algebra.IsIntegral.isIntegral`, `Polynomial.X_mul_divX_add`, `Polynomial.X_pow_dvd_iff`, `Polynomial.aeval_mul`, `Polynomial.aeval_X_pow`, `Module.Finite.of_isLocalization`, `Algebra.IsIntegral.of_finite`. Import: `Mathlib.RingTheory.Localization.Finiteness`.""",
  sources="""[BGR] 6.1.2/4, `bgr-6.1.2.md:72–73`; decomposition L7.16–L7.17.""",
  gen="""General commutative algebra (domains, injective integral/finite maps); Mathlib-shaped.""")

t(id='T035', title='Affinoid domains are Japanese (BGR 6.1.2/4, characteristic zero)', file=NTH, deps='T030, T034', par='no', typ='lemma', leaves='L7.18',
  decls=[(NTH,'isJapaneseRing')],
  sketch="""`intro L _ _ _ _ _` (unfold `IsJapaneseRing`; read its definition in `Japanese.lean`);
`obtain ⟨d, φ, hφ, hinj⟩ := hA.exists_finite_injective`; set up the tower `T_d → A → FractionRing A → L` and
`T_d → FractionRing T_d → L`:
- `letI : Algebra (TateAlgebra K d) A := φ.toRingHom.toAlgebra`; `haveI : Module.Finite (TateAlgebra K d) A := hφ`;
  `haveI : IsScalarTower K (TateAlgebra K d) A := IsScalarTower.of_algebraMap_eq fun c ↦ (φ.commutes c).symm`.
- `letI : Algebra (TateAlgebra K d) L := ((algebraMap A L).comp φ.toRingHom).toAlgebra`;
  `haveI : IsScalarTower (TateAlgebra K d) A L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl`.
- `haveI : FaithfulSMul (TateAlgebra K d) L` from injectivity of `T_d → L` (`A → L` injective: `A → FractionRing A`
  injective (`IsFractionRing.injective`) and `FractionRing A → L` injective (field hom); `(faithfulSMul_iff_algebraMap_injective _ _).2`);
  `letI : Algebra (FractionRing (TateAlgebra K d)) L := FractionRing.liftAlgebra _ _`;
  `haveI := FractionRing.isScalarTower_liftAlgebra (TateAlgebra K d) L`.
- `letI : Algebra (FractionRing (TateAlgebra K d)) (FractionRing A) := FractionRing.liftAlgebra _ _`
  (`FaithfulSMul (T_d) (FractionRing A)` similarly); `haveI : IsScalarTower (FractionRing T_d) (FractionRing A) L`:
  both composites `Frac T_d → L` are `IsFractionRing.lift` of the same injective map, so
  `IsScalarTower.of_algebraMap_eq` from `IsLocalization.ringHom_ext (nonZeroDivisors T_d)` (compare on `algebraMap T_d _`).
- `haveI : FiniteDimensional (FractionRing T_d) (FractionRing A) := FractionRing.finiteDimensional_of_finite _ _ hinj`
  (T034; `IsScalarTower T_d (Frac T_d) (Frac A)` is `isScalarTower_liftAlgebra`);
  `haveI : FiniteDimensional (FractionRing T_d) L := Module.Finite.trans (FractionRing A) L`.
- `have hJ := Affinoid.TateAlgebra.isJapaneseRing (K := K) d L` (Layer 0; `Module.Finite T_d (integralClosure T_d L)`).
- `integralClosure (TateAlgebra K d) L = (integralClosure A L).restrictScalars? `: as subalgebras over `T_d`,
  `(integralClosure A L).restrictScalars (TateAlgebra K d) = integralClosure (TateAlgebra K d) L` by
  `Subalgebra.ext`: `⊆`: `IsIntegral.tower_top`; `⊇`: `isIntegral_trans` (`Algebra.IsIntegral T_d A` from `hφ`:
  `Algebra.IsIntegral.of_finite`). Transport `Module.Finite` along the equality (`Subalgebra.equivOfEq`,
  `LinearEquiv.finiteDimensional`-style `Module.Finite.equiv`), giving `Module.Finite T_d (integralClosure A L)`
  (as a `T_d`-module through restriction of scalars), then `Module.Finite.of_restrictScalars_finite (TateAlgebra K d) A _`.
Budget 150 lines; instance management is the whole difficulty. Use `letI`/`haveI` in the order above so that
each `IsScalarTower` refers to the intended `Algebra` instances.""",
  mathlib="""`RingHom.toAlgebra`, `IsScalarTower.of_algebraMap_eq`, `FaithfulSMul`, `faithfulSMul_iff_algebraMap_injective`, `IsFractionRing.injective`, `FractionRing.liftAlgebra`, `FractionRing.isScalarTower_liftAlgebra`, `IsLocalization.ringHom_ext`, `Module.Finite.trans`, `IsIntegral.tower_top`, `isIntegral_trans`, `Algebra.IsIntegral.of_finite`, `Subalgebra.restrictScalars`, `Subalgebra.equivOfEq`, `Module.Finite.equiv`, `Module.Finite.of_restrictScalars_finite`, `integralClosure`. Layer 0: `IsJapaneseRing`, `Affinoid.TateAlgebra.isJapaneseRing`; board T030, T034.""",
  sources="""[BGR] 6.1.2/4, `bgr-6.1.2.md:69–75`; decomposition L7.18 (V6).""",
  gen="""Characteristic zero (Layer 0's `T_d`); `K`, `A` in one universe `u` as Layer 0's definition requires.""")

# ---------------------------------------------------------------- G8 Affinoid/Continuity
t(id='T036', title='The powers of the maximal ideals: zero intersection and finite-dimensional quotients', file=ACO, deps='T033', par='no',
  typ='lemmas', leaves='L8.1, L8.2',
  decls=[(ACO,'Ideal.sInf_maximalPowers_eq_bot'),(ACO,'finiteDimensional_of_mem_maximalPowers')],
  sketch="""1. `sInf_maximalPowers_eq_bot` (import `Mathlib.RingTheory.Filtration`): `rw [eq_bot_iff]; intro f hf;
   rw [Ideal.mem_bot]; by_contra hf0`; the annihilator ideal `I₀ : Ideal A := { carrier := {r | r * f = 0}, … }`
   (or `Submodule.annihilator (Submodule.span A {f})`, or `RingHom.ker`-free: use `Ideal.span`? — build it with
   `Submodule.mk`: closed under `+` and `A`-multiplication by `add_mul`, `mul_assoc`); `I₀ ≠ ⊤` since `1 ∉ I₀`
   (`one_mul`, `hf0`); `obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal I₀ hI₀`; for all `ν`,
   `f ∈ 𝔪 ^ ν` (`Ideal.mem_sInf.1 hf ⟨𝔪, ν, h𝔪, rfl⟩`); `have hinf : f ∈ ⨅ i : ℕ, 𝔪 ^ i • (⊤ : Submodule A A) :=
   Submodule.mem_iInf.2 fun i ↦ by rw [smul_eq_mul, mul_top]; exact …` (`Ideal.mul_top`); `obtain ⟨⟨r, hr⟩, hrf⟩ :=
   (Ideal.mem_iInf_smul_pow_eq_bot_iff 𝔪 f).1 hinf` (`r • f = f`); then `(1 - r) * f = 0` (`sub_mul`, `one_mul`,
   `smul_eq_mul ▸ hrf`, `sub_self`), so `1 - r ∈ I₀ ≤ 𝔪`, and `1 = (1 - r) + r ∈ 𝔪` (`Ideal.add_mem`),
   contradicting `h𝔪.ne_top` (`Ideal.eq_top_iff_one`).
2. `finiteDimensional_of_mem_maximalPowers`: `obtain ⟨𝔪, ν, h𝔪, rfl⟩ := hI`; `rcases ν with _ | ν`;
   `· rw [pow_zero, Ideal.one_eq_top]; haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.2 rfl;
   exact Module.Finite.of_finite` (a subsingleton type is `Finite`: `Finite.of_subsingleton`);
   `· exact hA.finiteDimensional_quotient_pow 𝔪 (Nat.succ_ne_zero ν)` (with `haveI := h𝔪`).""",
  mathlib="""`Ideal.mem_iInf_smul_pow_eq_bot_iff` (`Mathlib.RingTheory.Filtration`), `Ideal.exists_le_maximal`, `Ideal.mem_sInf`, `Submodule.mem_iInf`, `Ideal.mul_top`, `smul_eq_mul`, `Ideal.eq_top_iff_one`, `Ideal.add_mem`, `Ideal.one_eq_top`, `Ideal.Quotient.subsingleton_iff`, `Module.Finite.of_finite`, `Finite.of_subsingleton`. Board: T033 (`finiteDimensional_quotient_pow`).""",
  sources="""[BGR] 6.1.3, `bgr-6.1.3-6.1.5.md:7–17`; decomposition L8.1–L8.2 (E4).""",
  gen="""Item 1 for any noetherian commutative ring (no Jacobson hypothesis, E4).""")

t(id='T037', title='BGR 6.1.3/1: every homomorphism of a noetherian Banach algebra into an affinoid algebra is continuous', file=ACO, deps='T036, T026', par='no',
  typ='lemma', leaves='L8.3',
  milestone='M3 — `AlgHom.continuous_of_isAffinoidAlgebra` ([RM] §1.3.2; BGR 6.1.3/1; Bosch 1.4/19); with it the skeleton\'s `continuous_of_isAffinoidAlgebra\'`, `continuous_presentation`, `isClosed_ideal`, `continuous_symm_of_isAffinoidAlgebra` close. `#print axioms` must be standard.',
  decls=[(ACO,'AlgHom.continuous_of_isAffinoidAlgebra')],
  sketch="""`haveI := hB.isNoetherianRing; exact AlgHom.continuous_of_isNoetherianRing (Ideal.maximalPowers B)
(fun _ h ↦ hB.finiteDimensional_of_mem_maximalPowers h) hB.sInf_maximalPowers_eq_bot Φ`.
Then `#print axioms` on it and on the four complete corollaries below it.""",
  mathlib="""Board: T026, T036.""",
  sources="""[BGR] 6.1.3/1, `bgr-6.1.3-6.1.5.md:19–22`; [Bo] 1.4/19, `bosch-lectures.txt:1426–1431`; decomposition L8.3 (V1).""",
  gen="""Any Banach norms with `‖1‖ = 1`, ultrametric, on both sides (plan, "Banach algebra conventions").""")

t(id='T038', title='Norm equivalence, power-boundedness and topological nilpotence are norm-independent', file=ACO, deps='T037, T004', par='no',
  typ='lemmas', leaves='L8.4–L8.6',
  decls=[(ACO,'AlgEquiv.exists_forall_norm_le_mul_of_isAffinoidAlgebra'),(ACO,'AlgEquiv.isPowerBounded_map_iff_of_isAffinoidAlgebra'),(ACO,'AlgEquiv.isTopologicallyNilpotent_map_iff_of_isAffinoidAlgebra')],
  sketch="""1. `exists_forall_norm_le_mul_…`: `obtain ⟨C, -, hC⟩ := SemilinearMapClass.bound_of_continuous e.toAlgHom
   (e.toAlgHom.continuous_of_isAffinoidAlgebra' hA hB)`, same for `e.symm.toAlgHom` with `hB hA`; `⟨C, C', hC, hC'⟩`.
2. `isPowerBounded_map_iff_…`: `obtain ⟨C, C', hC, hC'⟩ := …`; `constructor <;> intro h <;>
   rw [isPowerBounded_iff_exists_norm_pow_le] at h ⊢ <;> obtain ⟨M, hM⟩ := h`;
   `⟨max 0 C' * M, fun n ↦ by rw [← e.symm_apply_apply a, ← map_pow]? …⟩`: `‖a ^ n‖ = ‖e.symm ((e a) ^ n)‖ ≤ C' * ‖(e a)^n‖ ≤ C' M`
   (`map_pow`, `AlgEquiv.symm_apply_apply`); use `max 0 C'` to keep nonnegativity, `le_max_right`, `mul_le_mul`.
3. `isTopologicallyNilpotent_map_iff_…`: unfold `IsTopologicallyNilpotent` (`Tendsto (a ^ ·) atTop (𝓝 0)`);
   `(e a) ^ n = e (a ^ n)` (`map_pow`); `⟨fun h ↦ by simpa [map_zero] using (he'.tendsto 0).comp h, fun h ↦ by
   simpa [map_zero, map_pow] using (he.tendsto 0).comp h⟩` with `he := e.toAlgHom.continuous_of_isAffinoidAlgebra' hA hB`,
   `he' := e.continuous_symm_of_isAffinoidAlgebra hA hB`, composing with `e.symm_apply_apply`.""",
  mathlib="""`SemilinearMapClass.bound_of_continuous`, `map_pow`, `AlgEquiv.symm_apply_apply`, `Filter.Tendsto.comp`, `Continuous.tendsto`, `map_zero`, `le_max_right`, `mul_le_mul`. Board: T004 (`isPowerBounded_iff_exists_norm_pow_le`), T037's corollaries.""",
  sources="""[RM] §1.3.3; [Bo] 1.4/16–17, `bosch-lectures.txt:1335–1336`, `:1376–1377`; decomposition L8.4–L8.6.""",
  gen="""Any two Banach algebra structures (with `‖1‖ = 1`, ultrametric) on `K`-algebras related by an isomorphism.""")

t(id='T039', title='Homomorphisms are determined by generating systems; generating systems exist; BGR 6.1.1/5', file=ACO, deps='T037, T020', par='no',
  typ='lemmas', leaves='L8.7–L8.9',
  decls=[(ACO,'AlgHom.ext_of_isAffinoidGeneratingSystem'),(ACO,'IsAffinoidAlgebra.exists_isAffinoidGeneratingSystem'),(ACO,'IsAffinoidAlgebra.of_finite_of_continuous')],
  sketch="""1. `ext_of_isAffinoidGeneratingSystem`: `obtain ⟨hb, hsurj⟩ := ha`; set `Φ := extendAlgHom (Algebra.ofId K A) _ a hb`;
   `have : ψ₁.comp Φ = ψ₂.comp Φ := algHom_ext_of_continuous ((ψ₁.continuous_of_isAffinoidAlgebra' hA hB).comp
   (continuous_extendAlgHom _ _ _ _)) (…) fun i ↦ by simp [extendAlgHom_X, h i]` (coefficients `K`: the
   `K`-algebra ext applies); `AlgHom.ext fun x ↦ ?_; obtain ⟨y, rfl⟩ := hsurj x; exact AlgHom.congr_fun this y`.
2. `exists_isAffinoidGeneratingSystem`: `obtain ⟨n, α, hα⟩ := hA; have hc := hA.continuous_presentation α`
   (or `α.continuous_of_isAffinoidAlgebra hA` with Layer 0's noetherian instance); `obtain ⟨C, hC⟩ :=
   exists_forall_norm_le_mul_of_continuous α hc`; `hb i := IsPowerBounded.map hC (isPowerBounded_of_norm_le_one
   (by simp [Affinoid.TateAlgebra.Examples.norm_X]? …))` — `‖X K 1 i‖ = 1` (`norm_X`, `norm_one`, `one_mul`, `Pi.one_apply`);
   `have heq : extendAlgHom (Algebra.ofId K A) (continuous_algebraMap K A) (fun i ↦ α (X K 1 i)) hb = α :=
   (extendAlgHom_unique _ _ _ _ α hc (fun c ↦ by rw [← algebraMap_apply]; exact α.commutes c) fun i ↦ rfl).symm`;
   `exact ⟨n, _, hb, heq ▸ hα⟩`.
3. `of_finite_of_continuous`: `obtain ⟨n, α, hα⟩ := hA; exact IsAffinoidAlgebra.of_finite_tateAlgebra (φ.comp α)
   (hφ.comp (hA.continuous_presentation α)) (hfin.comp (RingHom.Finite.of_surjective _ hα))`.""",
  mathlib="""`AlgHom.congr_fun`, `AlgHom.ext`, `RingHom.Finite.of_surjective`, `RingHom.Finite.comp`, `Pi.one_apply`. Board: T016 (`extendAlgHom_unique`, `continuous_extendAlgHom`), T020, T037's `continuous_presentation`, T004 (`IsPowerBounded.map`), floor `algebraMap_apply`, `norm_X`, `algHom_ext_of_continuous`, PFA `isPowerBounded_of_norm_le_one`.""",
  sources="""[BGR] 6.1.1, `bgr-6.1.1.md:52–59`; 6.1.1/5, `:68`; [RM] §1.1.3–1.1.4; decomposition L8.7–L8.9.""",
  gen="""Affinoid Banach algebras with `‖1‖ = 1`, ultrametric.""")

t(id='T040', title='`A⟨X₁, …, Xₘ⟩` is affinoid for affinoid `A`', file=ACO, deps='T037, T019, T009, T010', par='no', typ='lemma', leaves='L8.10',
  decls=[(ACO,'IsAffinoidAlgebra.restricted')],
  sketch="""`obtain ⟨n, α, hα⟩ := hA; have hc := hA.continuous_presentation α`;
`have hsurj := surjective_mapAlgHom_of_surjective (σ := σ) α hc hα` (T019; `Tₙ` is complete);
`letI := Fintype.ofFinite σ; let e := Fintype.equivFin σ` (`σ ≃ Fin m` with `m := Fintype.card σ`);
`let r : Restricted (TateAlgebra K n) (1 : σ → ℝ) ≃ₐ[K] Restricted (TateAlgebra K n) (1 : Fin m → ℝ) :=
AlgEquiv.ofRingEquiv (f := renameEquiv (TateAlgebra K n) e) fun c ↦ by rw [algebraMap_eq_C_comp, algebraMap_eq_C_comp,
RingHom.comp_apply, RingHom.comp_apply, renameEquiv_C]` (T009, T001);
`have h1 : IsAffinoidAlgebra K (Restricted (TateAlgebra K n) (1 : σ → ℝ)) :=
(IsAffinoidAlgebra.tateAlgebra (m + n)).of_algEquiv ((TateAlgebra.sumEquiv K n m).symm.trans r.symm)` (T010);
`exact h1.of_surjective (mapAlgHom α hc) hsurj`.""",
  mathlib="""`Fintype.ofFinite`, `Fintype.equivFin`, `AlgEquiv.ofRingEquiv`, `AlgEquiv.trans`, `AlgEquiv.symm`. Board: T001, T009, T010, T019, T037's `continuous_presentation`, T013 (`of_algEquiv`, `of_surjective`).""",
  sources="""[BGR] 6.1.4, `bgr-6.1.3-6.1.5.md:64–66`; 6.1.1/9, `bgr-6.1.1.md:113–117`; decomposition L8.10 (E2).""",
  gen="""Any finite index type `σ`; affinoid Banach `A` with `‖1‖ = 1`.""")

t(id='T041', title='BGR 6.1.3/3: contractive renorming of the target of a homomorphism', file=ACO, deps='T039, T040, T006', par='no', typ='lemma', leaves='L8.11',
  decls=[(ACO,'IsAffinoidAlgebra.exists_algEquiv_quotient_norm_comp_le')],
  sketch="""`obtain ⟨n, a, hb, hsurj₀⟩ := hA.exists_isAffinoidGeneratingSystem` (T039);
`have hφ := φ.continuous_of_isAffinoidAlgebra' hB hA`; `let ψ := extendAlgHom φ hφ a hb`;
`have hψ : Function.Surjective ψ`: `ψ.comp (mapAlgHom (Algebra.ofId K B) (continuous_algebraMap K B)) =
extendAlgHom (Algebra.ofId K A) _ a hb` by `extendAlgHom_unique` (continuity of the composite; on `C c`:
`mapAlgHom_C`, `extendAlgHom_C`, `φ.commutes`; on `X i`: `mapAlgHom_X`, `extendAlgHom_X`), hence
`hsurj₀` gives surjectivity of the composite, hence of `ψ` (`Function.Surjective.of_comp`);
`refine ⟨n, RingHom.ker ψ, Ideal.quotientKerAlgEquivOfSurjective hψ, ?_, ?_, fun b ↦ ?_⟩`;
- continuity of `e`: `(QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2` with `⇑e ∘ mk = ⇑ψ` (`rfl`
  for `quotientKerAlgEquivOfSurjective`: `Ideal.quotientKerAlgEquivOfSurjective_apply`? check) and
  `continuous_extendAlgHom`.
- continuity of `e.symm`: `rcases subsingleton_or_nontrivial A with hA0 | hA0`;
  · `exact continuous_of_const fun _ _ ↦ Subsingleton.elim _ _`;
  · `haveI : IsClosed ((RingHom.ker ψ : Ideal _) : Set _) := hB.restricted.isClosed_ideal _` (T040 + T037's
    corollary; `NormOneClass (Restricted B 1)` from `NormOneClass B`); `haveI : NormOneClass (Restricted B 1 ⧸ RingHom.ker ψ) :=
    Ideal.Quotient.normOneClass_of_ne_top _ (by intro h; … 1 ∈ ker ψ → ψ 1 = 0 → (0 : A) = 1 … )` (T006);
    `exact e.continuous_symm_of_isAffinoidAlgebra (hB.restricted.quotient _) hA`.
- the bound: `have : e.symm (φ b) = Ideal.Quotient.mk _ (C 1 b) := e.symm_apply_eq.2 (by simp [extendAlgHom_C])`
  (`e (mk x) = ψ x`); `rw [this]; exact (Ideal.Quotient.norm_mk_le _ _).trans (norm_C _ _).le`.""",
  mathlib="""`Ideal.quotientKerAlgEquivOfSurjective`, `Function.Surjective.of_comp`, `QuotientAddGroup.isQuotientMap_mk`, `Topology.IsQuotientMap.continuous_iff`, `continuous_of_const`, `subsingleton_or_nontrivial`, `AlgEquiv.symm_apply_eq`, `Ideal.Quotient.norm_mk_le`. Board: T006, T016, T018, T037's corollaries, T039, T040; floor `norm_C`.""",
  sources="""[BGR] 6.1.3/3, `bgr-6.1.3-6.1.5.md:35–42`; decomposition L8.11.""",
  gen="""Affinoid Banach algebras with `‖1‖ = 1`; the zero target handled separately.""")

# ---------------------------------------------------------------- G9 Affinoid/Tensor
t(id='T042', title='The inclusions `A⟨X⟩ → A⟨X ⊕ Y⟩ ← A⟨Y⟩` on constants', file=TEN, deps='T015', par='yes (with T043)', typ='lemmas', leaves='L9.1–L9.4',
  decls=[(TEN,'inlAlgHom_C'),(TEN,'inrAlgHom_C'),(TEN,'inlAlgHom_comp_toAlgHom'),(TEN,'inrAlgHom_comp_toAlgHom')],
  sketch="""`inlAlgHom_C`: `rw [inlAlgHom, extendAlgHom_C, IsScalarTower.toAlgHom_apply, algebraMap_apply]`; same for `inr`.
`inlAlgHom_comp_toAlgHom`: `AlgHom.ext fun a ↦ by simp [IsScalarTower.toAlgHom_apply, algebraMap_apply, inlAlgHom_C]`.""",
  mathlib="""`IsScalarTower.toAlgHom_apply`, `AlgHom.ext`, `AlgHom.comp_apply`. Board: T015, floor `algebraMap_apply`.""",
  sources="""[BGR] 6.1.1/7, `bgr-6.1.1.md:96`; decomposition L9.1–L9.4.""",
  gen="""Any normed `K`-algebra `A` (ultrametric, complete), finite `σ`, `τ`.""")

t(id='T043', title='Uniqueness of the affinoid tensor product; transport along an isomorphism of a factor', file=TEN, deps='none',
  par='yes (with T042)', typ='lemmas', leaves='L9.5, L9.6',
  decls=[(TEN,'IsAffinoidTensorProduct.exists_algEquiv'),(TEN,'IsAffinoidTensorProduct.of_algEquiv_left')],
  sketch="""1. `exists_algEquiv`: `obtain ⟨F, ⟨hF, hF₁, hF₂⟩, huF⟩ := h.existsUnique_lift ι₁' ι₂' h'.continuous_ι₁ h'.continuous_ι₂ h'.comp_eq`;
   `obtain ⟨G, ⟨hG, hG₁, hG₂⟩, huG⟩ := h'.existsUnique_lift ι₁ ι₂ h.continuous_ι₁ h.continuous_ι₂ h.comp_eq`;
   `have hGF : G.comp F = AlgHom.id K T := by obtain ⟨-, -, hu⟩ := h.existsUnique_lift ι₁ ι₂ h.continuous_ι₁ h.continuous_ι₂ h.comp_eq;
   exact (hu _ ⟨hG.comp hF, by rw [AlgHom.comp_assoc, hF₁, hG₁], by rw [AlgHom.comp_assoc, hF₂, hG₂]⟩).trans
   (hu _ ⟨continuous_id, AlgHom.id_comp _, AlgHom.id_comp _⟩).symm` — note `ExistsUnique` gives
   `∀ y, P y → y = x`, so both candidates equal the chosen one; symmetric `hFG`;
   `exact ⟨AlgEquiv.ofAlgHom F G hFG hGF, hF, hG, hF₁, hF₂⟩` (coercions `AlgEquiv.ofAlgHom` to `toAlgHom`: `rfl`).
2. `of_algEquiv_left`: `refine ⟨h.continuous_ι₁.comp he, h.continuous_ι₂, ?_, ?_⟩`;
   `comp_eq`: `rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc e.toAlgHom, AlgEquiv.comp_symm? ]` — `e.toAlgHom.comp e.symm.toAlgHom = AlgHom.id`
   (`AlgEquiv.comp_symm`), then `AlgHom.id_comp`, `h.comp_eq`;
   lift: `intro C _ _ _ _ f₁ f₂ hf₁ hf₂ hcomp`; apply `h.existsUnique_lift (f₁.comp e.symm.toAlgHom) f₂ (hf₁.comp he') hf₂
   (by rw [AlgHom.comp_assoc]; exact hcomp)`; from `⟨F, ⟨hF, hF₁, hF₂⟩, hu⟩` return `⟨F, ⟨hF, ?_, hF₂⟩, ?_⟩` where
   `F.comp (ι₁.comp e.toAlgHom) = f₁` from `hF₁` by composing with `e` (`AlgHom.comp_assoc`, `AlgEquiv.symm_comp`),
   and uniqueness: a lift of `(f₁ ∘ e.symm, f₂)` through `(ι₁ ∘ e, ι₂)` is a lift through `(ι₁, ι₂)` by the same
   rewriting.""",
  mathlib="""`ExistsUnique`, `AlgHom.comp_assoc`, `AlgHom.id_comp`, `AlgHom.comp_id`, `AlgEquiv.ofAlgHom`, `AlgEquiv.comp_symm`, `AlgEquiv.symm_comp`, `continuous_id`, `Continuous.comp`.""",
  sources="""[BGR] 6.1.1/10, `bgr-6.1.1.md:137–139`; 3.1.1/2 (cited); decomposition L9.5–L9.6 (D2).""",
  gen="""Predicate-level, for Banach algebras in one universe `v`.""")

t(id='T044', title='`B₂ ⧸ 𝔞B₂` is the tensor product of `A ⧸ 𝔞` and `B₂` (BGR 6.1.1/11, the case `𝔟₂ = 0`)', file=TEN, deps='T037', par='no',
  typ='lemma', leaves='L9.7',
  decls=[(TEN,'isAffinoidTensorProduct_quotient_map')],
  sketch="""`haveI : IsClosed ((𝔞.map α₂ : Ideal B₂) : Set B₂) := hB₂.isClosed_ideal _`; `refine ⟨?_, continuous_quot_mk, ?_, ?_⟩`:
- `ι₁ := Ideal.quotientMapₐ (𝔞.map α₂) α₂ Ideal.le_comap_map` continuous: `(QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2`
  with `⇑ι₁ ∘ mk = ⇑(mkₐ K _) ∘ ⇑α₂` (`funext`, `Ideal.quotientMap_mk`) and `continuous_quot_mk.comp hα₂`.
- `comp_eq`: `AlgHom.ext fun a ↦ Ideal.quotientMap_mk …` (both sides `mk (α₂ a)`).
- lift: `intro C _ _ _ _ f₁ f₂ hf₁ hf₂ hcomp`; `have hker : ∀ b ∈ 𝔞.map α₂, f₂ b = 0 := fun b hb ↦ by
  have : 𝔞.map α₂ ≤ RingHom.ker f₂ := Ideal.map_le_iff_le_comap.2 fun a ha ↦ by
  rw [Ideal.mem_comap, RingHom.mem_ker, ← AlgHom.comp_apply, ← hcomp, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
  Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]; exact this hb`;
  `refine ⟨Ideal.Quotient.liftₐ _ f₂ hker, ⟨?_, ?_, Ideal.Quotient.liftₐ_comp _ _ _⟩, ?_⟩`;
  continuity: quotient map with `liftₐ ∘ mk = f₂`; `F.comp ι₁ = f₁`: `Ideal.Quotient.algHom_ext K fun a ↦ ?_`
  (ext on `mkₐ K 𝔞`: `Ideal.Quotient.algHom_ext`), both sides `f₂ (α₂ a) = f₁ (mk a)` by `hcomp`;
  uniqueness: `rintro F' ⟨-, -, hF'₂⟩; exact Ideal.Quotient.algHom_ext K (by simpa using hF'₂)` (equality on
  `mkₐ`).""",
  mathlib="""`Ideal.quotientMapₐ`, `Ideal.quotientMap_mk`, `Ideal.le_comap_map`, `QuotientAddGroup.isQuotientMap_mk`, `Topology.IsQuotientMap.continuous_iff`, `continuous_quot_mk`, `Ideal.map_le_iff_le_comap`, `Ideal.mem_comap`, `RingHom.mem_ker`, `Ideal.Quotient.mkₐ_eq_mk`, `Ideal.Quotient.eq_zero_iff_mem`, `Ideal.Quotient.liftₐ`, `Ideal.Quotient.liftₐ_comp`, `Ideal.Quotient.algHom_ext`. Board: T037's `isClosed_ideal`.""",
  sources="""[BGR] 6.1.1/11, `bgr-6.1.1.md:142–151`; decomposition L9.7.""",
  gen="""`B₂` affinoid with `‖1‖ = 1`; `𝔞` any closed ideal of the Banach algebra `A`.""")

t(id='T045', title='BGR 6.1.1/11: `B₂ → B₁ ⊗̂_A B₂` is surjective when `A → B₁` is', file=TEN, deps='T043, T044', par='no', typ='lemma', leaves='L9.8',
  decls=[(TEN,'IsAffinoidTensorProduct.surjective_ι₂_of_surjective')],
  sketch="""`have hcl : IsClosed ((RingHom.ker α₁ : Ideal A) : Set A) := isClosed_singleton.preimage hα₁` (the kernel is
`α₁ ⁻¹' {0}`: `RingHom.ker` as a set, `Set.ext` with `RingHom.mem_ker`); `haveI := hcl`;
`let e : (A ⧸ RingHom.ker α₁) ≃ₐ[K] B₁ := Ideal.quotientKerAlgEquivOfSurjective hα₁'`;
`have he : Continuous e := (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 hα₁` (`⇑e ∘ mk = ⇑α₁`, `rfl`);
`have he' : Continuous e.symm := e.toLinearEquiv.continuous_symm he` (both complete);
`have h' := h.of_algEquiv_left e he he'` (T043): a tensor product for `(e.symm ∘ α₁, α₂, ι₁ ∘ e, ι₂)`, and
`e.symm.toAlgHom.comp α₁ = Ideal.Quotient.mkₐ K (RingHom.ker α₁)` (`AlgHom.ext`, `AlgEquiv.symm_apply_eq`,
`Ideal.quotientKerAlgEquivOfSurjective_apply`? / `rfl` on `mk`); rewrite `h'` with it;
`have h'' := isAffinoidTensorProduct_quotient_map hB₂ α₂ hα₂ (RingHom.ker α₁)` (T044);
`obtain ⟨ε, -, -, -, hε₂⟩ := h'.exists_algEquiv h''` (T043; universes `B₂ T : Type v` ✓);
`intro t'`; from `hε₂ : ε.toAlgHom.comp ι₂ = mkₐ _` and `Ideal.Quotient.mk_surjective (ε t')` obtain `b` with
`ε (ι₂ b) = ε t'`, so `ι₂ b = t'` (`ε.injective`).""",
  mathlib="""`isClosed_singleton`, `IsClosed.preimage`, `RingHom.mem_ker`, `Ideal.quotientKerAlgEquivOfSurjective`, `QuotientAddGroup.isQuotientMap_mk`, `LinearEquiv.continuous_symm`, `AlgEquiv.toLinearEquiv`, `AlgEquiv.symm_apply_eq`, `Ideal.Quotient.mk_surjective`, `AlgEquiv.injective`, `AlgHom.congr_fun`. Board: T043, T044.""",
  sources="""[BGR] 6.1.1/11, `bgr-6.1.1.md:144–146`; [RM] §1.1.5; decomposition L9.8 (D3).""",
  gen="""`B₂` affinoid with `‖1‖ = 1`; `α₁` continuous and surjective; `B₂`, `T` in one universe.""")

t(id='T046', title='The structure maps of `A⟨X ⊕ Y⟩ ⧸ (𝔟₁, 𝔟₂)`', file=TEN, deps='T042', par='no', typ='definitions + lemmas', leaves='L9.9–L9.13',
  decls=[(TEN,'tensorInl'),(TEN,'tensorInr'),(TEN,'continuous_tensorInl'),(TEN,'continuous_tensorInr'),(TEN,'tensorInl_comp_eq_tensorInr_comp')],
  sketch="""1. The `liftₐ` obligations: `fun f hf ↦ by rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem];
   exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf)` (and `mem_sup_right` for `inr`); `tensorIdeal` unfolds by `rfl`/`show`.
2. `continuous_tensorInl`: `(QuotientAddGroup.isQuotientMap_mk 𝔟₁.toAddSubgroup).continuous_iff.2` with
   `⇑(tensorInl …) ∘ mk = ⇑(mk _) ∘ ⇑(inlAlgHom K A σ τ)` (`funext`, `tensorInl_mk`) and
   `continuous_quot_mk.comp (continuous_inlAlgHom _ _)`.
3. `tensorInl_comp_eq_tensorInr_comp`: `AlgHom.ext fun a ↦ ?_`; both sides reduce to `mk (C 1 a)`:
   `IsScalarTower.toAlgHom_apply`, `Ideal.Quotient.algebraMap_eq`, `tensorInl_mk`, `inlAlgHom_C` (T042), `algebraMap_apply`.""",
  mathlib="""`Ideal.Quotient.mkₐ_eq_mk`, `Ideal.Quotient.eq_zero_iff_mem`, `Ideal.mem_sup_left`, `Ideal.mem_sup_right`, `Ideal.mem_map_of_mem`, `QuotientAddGroup.isQuotientMap_mk`, `continuous_quot_mk`, `Ideal.Quotient.algebraMap_eq`, `IsScalarTower.toAlgHom_apply`. Board: T042, `continuous_inlAlgHom`, floor `algebraMap_apply`.""",
  sources="""[BGR] 6.1.1/11, `bgr-6.1.1.md:147–149`; decomposition L9.9–L9.13.""",
  gen="""Any normed `K`-algebra `A` (ultrametric, complete); no closedness needed for these.""")

t(id='T047', title='The universal property of `A⟨X ⊕ Y⟩ ⧸ (𝔟₁, 𝔟₂)` (BGR 6.1.1/10–11)', file=TEN, deps='T046, T016, T040', par='no', typ='lemma', leaves='L9.14',
  milestone='M4 — `Affinoid.isAffinoidTensorProduct_tensorQuotient`: the affinoid tensor product by presentations is the pushout among Banach algebras ([RM] §1.1.5; BGR 6.1.1/10–11). `#print axioms` must be standard.',
  decls=[(TEN,'isAffinoidTensorProduct_tensorQuotient')],
  sketch="""`refine ⟨continuous_tensorInl …, continuous_tensorInr …, tensorInl_comp_eq_tensorInr_comp …, ?_⟩`;
`intro C _ _ _ _ f₁ f₂ hf₁ hf₂ hcomp`; write `ι := IsScalarTower.toAlgHom K A (Restricted A 1_σ ⧸ 𝔟₁)` etc.
- Images of the variables: `b : σ ⊕ τ → C := Sum.elim (fun i ↦ f₁ (mk (X A 1 i))) (fun j ↦ f₂ (mk (X A 1 j)))`;
  power-bounded: `IsPowerBounded.map` (T004) along `f₁ ∘ mk` with the bound from `exists_forall_norm_le_mul_of_continuous`
  of `(f₁.comp (mkₐ K 𝔟₁))` (continuous: `hf₁.comp continuous_quot_mk`) applied to `isPowerBounded_X i`
  (in `Restricted A 1_σ`; the quotient's norm is the residue seminorm — `IsPowerBounded` through a bounded map
  needs the *target* normed: `C` ✓ and the source `Restricted A 1_σ` ✓; do not pass through the quotient).
- `F₀ := extendAlgHom (f₁.comp (ι)) ((hf₁.comp continuous_quot_mk).comp (continuous_algebraMap_restricted _)) b hb`
  (the map `A → C` is `f₁ ∘ mk ∘ C`, continuous).
- `hinl : F₀.comp (inlAlgHom K A σ τ) = f₁.comp (Ideal.Quotient.mkₐ K 𝔟₁)`: `AlgHom.coe_ringHom_injective`
  (`ringHom_ext_of_continuous`): continuity of both; on `C a`: `inlAlgHom_C`, `extendAlgHom_C`, and on the right
  `mk (C a) = algebraMap A _ a` (`Ideal.Quotient.algebraMap_eq`, `algebraMap_apply`); on `X i`: `inlAlgHom_X`,
  `extendAlgHom_X`, `Sum.elim_inl`. Similarly `hinr` with `hcomp` to identify `f₂ (mk (C a)) = f₁ (mk (C a))`
  (`AlgHom.congr_fun hcomp a`).
- `hker : tensorIdeal K A 𝔟₁ 𝔟₂ ≤ RingHom.ker F₀`: `sup_le (Ideal.map_le_iff_le_comap.2 fun g hg ↦ ?_) (…)`:
  `F₀ (inlAlgHom g) = f₁ (mk g) = f₁ 0 = 0` by `AlgHom.congr_fun hinl g` and `Ideal.Quotient.eq_zero_iff_mem.2 hg`.
- `F := Ideal.Quotient.liftₐ _ F₀ (fun x hx ↦ hker hx)`; `F.comp tensorInl = f₁`: `Ideal.Quotient.algHom_ext K`,
  then on `mk g`: `tensorInl_mk`, `Ideal.Quotient.liftₐ_apply`, `AlgHom.congr_fun hinl g`; same for `ι₂`.
- continuity of `F`: quotient map, `⇑F ∘ mk = ⇑F₀` (`Ideal.Quotient.liftₐ_apply`), `continuous_extendAlgHom`.
- uniqueness: `rintro F' ⟨hF', h₁, h₂⟩`; `Ideal.Quotient.algHom_ext K ?_` reduces to `F'.comp (mkₐ K _) = F₀`:
  `AlgHom.coe_ringHom_injective (ringHom_ext_of_continuous (hF'.comp continuous_quot_mk) (continuous_extendAlgHom …) ?_ ?_)`;
  on `C a`: `F' (mk (C a)) = F' (tensorInl (mk (C a))) = f₁ (mk (C a))` (via `h₁` and `tensorInl_mk`,
  `inlAlgHom_C`) `= F₀ (C a)` (`extendAlgHom_C`); on `X (inl i)`: `mk (X (inl i)) = tensorInl (mk (X i))`
  (`tensorInl_mk`, `inlAlgHom_X`), then `h₁`, `extendAlgHom_X`, `Sum.elim_inl`; `inr` likewise with `h₂`.
`#print axioms` afterwards.""",
  mathlib="""`Sum.elim_inl`, `Sum.elim_inr`, `sup_le`, `Ideal.map_le_iff_le_comap`, `Ideal.Quotient.eq_zero_iff_mem`, `Ideal.Quotient.liftₐ`, `Ideal.Quotient.liftₐ_apply`, `Ideal.Quotient.algHom_ext`, `Ideal.Quotient.algebraMap_eq`, `AlgHom.congr_fun`, `AlgHom.coe_ringHom_injective`, `QuotientAddGroup.isQuotientMap_mk`, `continuous_quot_mk`. Board: T004 (`IsPowerBounded.map`), T014 (`isPowerBounded_X`), T015–T016 (`extendAlgHom_*`, `continuous_extendAlgHom`), T018 (`continuous_algebraMap_restricted`), T042, T046, floor `ringHom_ext_of_continuous`.""",
  sources="""[BGR] 6.1.1/10–11, `bgr-6.1.1.md:131–151`; 6.1.1/4; [RM] §1.1.5; decomposition L9.14.""",
  gen="""`A` affinoid with `‖1‖ = 1` (for the `IsClosed` instances in the statement only); the universal property for every universe of test algebras.""")

t(id='T048', title='The algebraic tensor product is dense in the affinoid one', file=TEN, deps='T046', par='no', typ='definitions + lemma', leaves='L9.15–L9.17',
  decls=[(TEN,'tensorInlₐ'),(TEN,'tensorInrₐ'),(TEN,'denseRange_tensorLift')],
  sketch="""1. `tensorInlₐ.commutes' a`: `show tensorInl … (algebraMap A _ a) = algebraMap A _ a`; both are
   `mk (C 1 a)`: `Ideal.Quotient.algebraMap_eq`, `algebraMap_apply`, `tensorInl_mk`, `inlAlgHom_C`.
2. `denseRange_tensorLift`: `have h1 : Set.range (⇑(Ideal.Quotient.mk _) ∘ ⇑(MvPolynomial.toRestricted (1 : σ ⊕ τ → ℝ))) ⊆ Set.range (tensorLift K A 𝔟₁ 𝔟₂)`:
   `rintro _ ⟨p, rfl⟩`; induction on `p` (`MvPolynomial.induction_on`): constants `C a ↦ tensorLift (mk (C 1 a) ⊗ₜ 1)`
   (`Algebra.TensorProduct.lift_tmul`, `map_one`, `mul_one`, `tensorInlₐ` on `mk (C a)`), sums and products
   (`map_add`, `map_mul`, `Set.mem_range` witnesses `x + y`, `x * y`), variables `X (inl i) ↦ tensorLift (mk (X i) ⊗ₜ 1)`,
   `X (inr j) ↦ tensorLift (1 ⊗ₜ mk (X j))`;
   `have h2 : DenseRange (⇑(Ideal.Quotient.mk _) ∘ ⇑(MvPolynomial.toRestricted 1)) :=
   (Ideal.Quotient.mk_surjective.denseRange).comp (denseRange_toRestricted _) continuous_quot_mk`
   (`DenseRange.comp (hg : DenseRange g) (hf : DenseRange f) (cg : Continuous g)`);
   `exact h2.mono h1`.""",
  mathlib="""`Ideal.Quotient.algebraMap_eq`, `MvPolynomial.induction_on`, `Algebra.TensorProduct.lift_tmul`, `Algebra.TensorProduct.includeLeft_apply`? (not needed), `map_add`, `map_mul`, `Function.Surjective.denseRange`, `DenseRange.comp`, `Dense.mono` (a `DenseRange` is a `Dense`, so `h.mono` works), `continuous_quot_mk`. Board: T046, T042; floor `denseRange_toRestricted`, `MvPolynomial.toRestricted` (its `C`, `X` lemmas `MvPolynomial.toRestricted_C`, `MvPolynomial.toRestricted_X`), `algebraMap_apply`.""",
  sources="""[RM] §1.1.5; [BGR] 6.1.1/7, `bgr-6.1.1.md:91–99`; decomposition L9.15–L9.17.""",
  gen="""Any normed `K`-algebra `A`; no closedness (density is topological).""")

# ---------------------------------------------------------------- G10 Affinoid/Fractions
t(id='T049', title='Generalised fractions at the level of universal properties: uniqueness, associativity, units, `g = 1`', file=FRA, deps='T004',
  par='yes (with T042)', typ='lemmas', leaves='L10.1–L10.4',
  decls=[(FRA,'IsGeneralisedFractions.exists_algEquiv'),(FRA,'IsGeneralisedFractions.trans'),(FRA,'IsGeneralisedFractions.of_isUnit'),(FRA,'IsRationalFractions.isGeneralisedFractions_of_one')],
  sketch="""1. `exists_algEquiv`: as T043/1 with one structure map (`h.existsUnique_lift φ₀' h'.continuous h'.isUnit h'.isPowerBounded_f
   h'.isPowerBounded_inv`, and symmetrically; `AlgEquiv.ofAlgHom`).
2. `trans`: `refine ⟨h'.continuous.comp h.continuous, ?_, ?_, ?_, ?_⟩`; units/power-boundedness by `Fin.addCases`
   (`Fin.append_left`, `Fin.append_right`): for the `g` part `(h.isUnit j).map φ₁` (`IsUnit.map`), for
   `g'` `h'.isUnit j'` (note `φ₁ (φ₀ (g' j'))` is `(φ₁.comp φ₀) (g' j')` and `h'` is about `φ₀ ∘ g'`); `f`:
   `IsPowerBounded.map (bound of φ₁ from exists_forall_norm_le_mul_of_continuous) (h.isPowerBounded_f i)`;
   inverses: `↑((h.isUnit j).map φ₁).unit⁻¹ = φ₁ ↑(h.isUnit j).unit⁻¹` (`Units.ext`-free: both are inverses
   of `φ₁ (φ₀ (g j))`, `Units.inv_unique`/`IsUnit.unit_spec`, or `Units.map`), then `IsPowerBounded.map`;
   UP: `intro B _ _ _ _ φ hφ hg hf hg'`; split the hypotheses along `Fin.append` (`fun j ↦ hg (Fin.castAdd _ j)` etc.);
   `obtain ⟨φ', ⟨hφ', hφ'₀⟩, hu⟩ := h.existsUnique_lift φ hφ …`; the data for `h'`: `φ' (φ₀ (g' j'))` is a unit since
   `φ'.comp φ₀ = φ` (`AlgHom.congr_fun hφ'₀`), likewise power-boundedness; `obtain ⟨φ'', ⟨hφ'', hφ''₁⟩, hu'⟩ :=
   h'.existsUnique_lift φ' hφ' …`; `refine ⟨φ'', ⟨hφ'', by rw [← AlgHom.comp_assoc, hφ''₁, hφ'₀]⟩, ?_⟩`;
   uniqueness: `rintro χ ⟨hχ, hχ₀⟩`; `have := hu (χ.comp φ₁) ⟨hχ.comp h'.continuous, by rw [AlgHom.comp_assoc]; exact hχ₀⟩`
   (so `χ.comp φ₁ = φ'`); `exact hu' χ ⟨hχ, this⟩`.
3. `of_isUnit`: `⟨continuous_id, hg, hf, hg', fun φ hφ _ _ _ ↦ ⟨φ, ⟨hφ, AlgHom.comp_id φ⟩, fun χ ⟨_, hχ⟩ ↦ by simpa using hχ⟩⟩`.
4. `isGeneralisedFractions_of_one`: `have hu : h.isUnit.unit = 1 := Units.ext (by simp [map_one])`;
   `refine ⟨h.continuous, fun j ↦ j.elim0, fun i ↦ by simpa [hu] using h.isPowerBounded_div i, fun j ↦ j.elim0, ?_⟩`;
   `intro B _ _ _ _ φ hφ hg hf hg'`; `obtain ⟨φ', hφ', hu'⟩ := h.existsUnique_lift φ hφ (by simp) (fun i ↦ by simpa using hf i)`
   (`(isUnit_one).unit⁻¹ = 1` after `map_one`); `exact ⟨φ', hφ', hu'⟩`.""",
  mathlib="""`AlgEquiv.ofAlgHom`, `Fin.addCases`, `Fin.append_left`, `Fin.append_right`, `Fin.castAdd`, `Fin.natAdd`, `IsUnit.map`, `Units.map`, `IsUnit.unit_spec`, `Units.inv_unique`, `Units.ext`, `AlgHom.comp_assoc`, `AlgHom.comp_id`, `AlgHom.congr_fun`, `Fin.elim0`, `isUnit_one`, `continuous_id`. Board: T004 (`IsPowerBounded.map`), `exists_forall_norm_le_mul_of_continuous` (T015's file).""",
  sources="""[BGR] 6.1.4, `bgr-6.1.3-6.1.5.md:100–101`, `:119–126`, `:157–158`; decomposition L10.1–L10.4 (D4).""",
  gen="""Predicate-level; associativity for arbitrary systems `f, f', g, g'`.""")

t(id='T050', title='`A⟨f, g⁻¹⟩`: the canonical map, the units and the power-bounded elements', file=FRA, deps='T014, T018', par='no',
  typ='lemmas', leaves='L10.5–L10.9',
  decls=[(FRA,'continuous_toFractions'),(FRA,'toFractions_mul_mk_X_inr'),(FRA,'toFractions_f'),(FRA,'isPowerBounded_toFractions_f'),(FRA,'isPowerBounded_inv_toFractions')],
  sketch="""1. `continuous_toFractions`: `continuous_quot_mk.comp (continuous_algebraMap_restricted _)` (after `show`).
2. `toFractions_mul_mk_X_inr`: `toFractions K A f g (g j) = mk (C 1 (g j))` (`rfl`/`Ideal.Quotient.mkₐ_eq_mk`,
   `IsScalarTower.toAlgHom_apply`, `algebraMap_apply`); `rw [← map_mul, ← sub_eq_zero, ← map_one, ← map_sub,
   Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span (Set.mem_union_right _ ⟨j, rfl⟩)`.
3. `toFractions_f`: `Ideal.Quotient.eq.2`: `C (f i) - X (inl i) ∈ fractionIdeal` as `-(X (inl i) - C (f i))`
   (`Ideal.neg_mem_iff`, `Ideal.subset_span (Set.mem_union_left _ ⟨i, rfl⟩)`), or `eq_comm` + `Ideal.Quotient.eq`.
4. `isPowerBounded_toFractions_f`: `rw [toFractions_f]; exact IsPowerBounded.map (C := 1) (fun x ↦ by rw [one_mul];
   exact Ideal.Quotient.norm_mk_le _ x) (isPowerBounded_X _)` (`mk` as a ring hom with bound `1`).
5. `isPowerBounded_inv_toFractions`: `have : ↑(isUnit_toFractions K A f g j).unit⁻¹ = Ideal.Quotient.mk _ (X A 1 (Sum.inr j)) :=
   Units.inv_eq_of_mul_eq_one_right? …` — `(IsUnit.unit h : Aˣ)` has `↑h.unit = toFractions (g j)` (`IsUnit.unit_spec`);
   `Units.inv_eq_of_mul_eq_one_right (by rw [IsUnit.unit_spec]; exact toFractions_mul_mk_X_inr …)`; then as item 4.""",
  mathlib="""`continuous_quot_mk`, `Ideal.Quotient.mkₐ_eq_mk`, `IsScalarTower.toAlgHom_apply`, `Ideal.Quotient.eq_zero_iff_mem`, `Ideal.Quotient.eq`, `Ideal.subset_span`, `Set.mem_union_left`, `Set.mem_union_right`, `Ideal.neg_mem_iff`, `Ideal.Quotient.norm_mk_le`, `IsUnit.unit_spec`, `Units.inv_eq_of_mul_eq_one_right`. Board: T014 (`isPowerBounded_X`), T018 (`continuous_algebraMap_restricted`), T004 (`IsPowerBounded.map`), floor `algebraMap_apply`.""",
  sources="""[BGR] 6.1.4, `bgr-6.1.3-6.1.5.md:105–106`; decomposition L10.5–L10.9.""",
  gen="""Any normed `K`-algebra `A` (the quotient seminorm suffices for these).""")

t(id='T051', title='BGR 6.1.4/1–2: the universal property of `A⟨X, Y⟩ ⧸ (X − f, gY − 1)`', file=FRA, deps='T050, T016, T040', par='no', typ='lemma', leaves='L10.10',
  decls=[(FRA,'isGeneralisedFractions_toFractions')],
  sketch="""`haveI : IsClosed ((fractionIdeal A f g : Ideal _) : Set _) := hA.restricted.isClosed_ideal _`;
`refine ⟨continuous_toFractions K A f g, isUnit_toFractions K A f g, isPowerBounded_toFractions_f K A f g,
isPowerBounded_inv_toFractions K A f g, ?_⟩`; `intro B _ _ _ _ φ hφ hg hf hg'`;
`let b : Fin m ⊕ Fin n → B := Sum.elim (fun i ↦ φ (f i)) (fun j ↦ ↑(hg j).unit⁻¹)`;
`have hb : ∀ k, IsPowerBounded (b k) := Sum.rec hf hg'` (or `fun k ↦ by cases k <;> simp [b, *]`);
`let φ'' := extendAlgHom φ hφ b hb`; `have hker : fractionIdeal A f g ≤ RingHom.ker φ''`:
`Ideal.span_le.2 (Set.union_subset ?_ ?_)`: `rintro _ ⟨i, rfl⟩; simp [RingHom.mem_ker, extendAlgHom_X, extendAlgHom_C, b]`
and for `C (g j) * X (inr j) - 1`: `simp […, IsUnit.mul_val_inv]` (`↑u * ↑u⁻¹ = 1` with `IsUnit.unit_spec`);
`refine ⟨Ideal.Quotient.liftₐ _ φ'' (fun x hx ↦ hker hx), ⟨?_, ?_⟩, ?_⟩`;
- continuity: quotient map, `liftₐ ∘ mk = φ''` (`Ideal.Quotient.liftₐ_apply`), `continuous_extendAlgHom`;
- `liftₐ.comp toFractions = φ`: `AlgHom.ext fun a ↦ by simp [toFractions, Ideal.Quotient.liftₐ_apply, extendAlgHom_C]`
  (through `IsScalarTower.toAlgHom_apply`, `algebraMap_apply`);
- uniqueness: `rintro χ ⟨hχ, hχ₀⟩`; `Ideal.Quotient.algHom_ext K` to `χ.comp (mkₐ K _) = φ''`:
  `AlgHom.coe_ringHom_injective (ringHom_ext_of_continuous (hχ.comp continuous_quot_mk) (continuous_extendAlgHom …) ?_ ?_)`;
  on `C a`: `χ (mk (C a)) = χ (toFractions a) = φ a` (`AlgHom.congr_fun hχ₀ a`), `= φ'' (C a)` (`extendAlgHom_C`);
  on `X (inl i)`: `mk (X (inl i)) = toFractions (f i)` (`toFractions_f`), so `χ … = φ (f i) = φ'' (X (inl i))`;
  on `X (inr j)`: `χ (mk (X (inr j))) * φ (g j) = χ (mk (X (inr j)) * toFractions (g j)) = χ 1 = 1`
  (`map_mul`, `mul_comm`, `toFractions_mul_mk_X_inr`), so `χ (mk (X (inr j))) = ↑(hg j).unit⁻¹`
  (`Units.eq_inv_of_mul_eq_one_left` with `IsUnit.unit_spec`), `= φ'' (X (inr j))` (`extendAlgHom_X`).""",
  mathlib="""`Ideal.span_le`, `Set.union_subset`, `RingHom.mem_ker`, `IsUnit.mul_val_inv`, `IsUnit.unit_spec`, `Ideal.Quotient.liftₐ`, `Ideal.Quotient.liftₐ_apply`, `Ideal.Quotient.algHom_ext`, `AlgHom.coe_ringHom_injective`, `Units.eq_inv_of_mul_eq_one_left`, `AlgHom.congr_fun`, `QuotientAddGroup.isQuotientMap_mk`, `continuous_quot_mk`. Board: T015–T016, T040, T050, T037's `isClosed_ideal`, floor `ringHom_ext_of_continuous`.""",
  sources="""[BGR] 6.1.4/1–2, `bgr-6.1.3-6.1.5.md:93–117`; decomposition L10.10.""",
  gen="""`A` affinoid with `‖1‖ = 1` (so the quotient is a Banach algebra); universal among all Banach `K`-algebras in universe `v`.""")

t(id='T052', title='`A⟨f/g⟩`: `g` becomes a unit and `X̄ᵢ = fᵢ/g` is power-bounded', file=FRA, deps='T014', par='yes (with T049)',
  typ='lemmas', leaves='L10.11–L10.14',
  decls=[(FRA,'continuous_toRational'),(FRA,'isUnit_toRational'),(FRA,'toRational_mul_inv'),(FRA,'isPowerBounded_toRational_div')],
  sketch="""1. `continuous_toRational`: as T050/1.
2. `isUnit_toRational`: `obtain ⟨a, a', h⟩ := hgen`; `refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ (C 1 a + ∑ i, C 1 (a' i) * X A 1 i)) ?_`
   — careful with the order: `IsUnit.of_mul_eq_one (b) (h : a * b = 1) : IsUnit a`, so prove
   `toRational g * mk (C a + Σ …) = 1`: `toRational g = mk (C 1 g)`; `← map_mul`, `← map_one`, `Ideal.Quotient.eq`:
   `C g * (C a + Σ C (a' i) * X i) - C 1 ∈ rationalIdeal`: expand (`mul_add`, `Finset.mul_sum`, `← map_mul`),
   and use `C (g * a) + Σ C (a' i) * (C g * X i) - C 1 = Σ C (a' i) * (C g * X i - C (f i))` modulo
   `C (g * a + Σ a' i * f i) = C 1` (`h`): `Ideal.Quotient.eq` and `Ideal.sum_mem` with `Ideal.mul_mem_left` and
   the generators `Ideal.subset_span ⟨i, rfl⟩`; the algebra: show the difference of the two sides is the sum
   `Σ C (a' i) * (C g * X i - C (f i))` by `ring_nf`/`simp [mul_sub, Finset.sum_sub_distrib, map_sum, map_mul, map_add, h]`.
3. `toRational_mul_inv`: `have hmk : Ideal.Quotient.mk _ (C 1 (f i)) = Ideal.Quotient.mk _ (C 1 g * X A 1 i) :=
   Ideal.Quotient.eq.2 (by rw [← Ideal.neg_mem_iff? ]…)`: `C (f i) - C g * X i = -(C g * X i - C (f i))`
   (`neg_sub`, `Ideal.neg_mem_iff`, `Ideal.subset_span ⟨i, rfl⟩`); then `toRational (f i) = mk (C (f i))`, rewrite,
   `map_mul`, `mul_comm`, `mul_assoc`, `IsUnit.mul_val_inv`? — `mk (C g) * ↑u⁻¹ = 1` where `↑u = toRational g = mk (C g)`
   (`IsUnit.unit_spec`), `mul_one`.
4. `isPowerBounded_toRational_div`: `rw [toRational_mul_inv]; exact IsPowerBounded.map (C := 1) (norm bound of mk) (isPowerBounded_X i)`.""",
  mathlib="""`IsUnit.of_mul_eq_one`, `Ideal.Quotient.eq`, `Ideal.sum_mem`, `Ideal.mul_mem_left`, `Ideal.subset_span`, `Finset.mul_sum`, `Finset.sum_sub_distrib`, `map_sum`, `neg_sub`, `Ideal.neg_mem_iff`, `IsUnit.unit_spec`, `IsUnit.mul_val_inv`, `Ideal.Quotient.norm_mk_le`. Board: T014, T004, floor `algebraMap_apply`.""",
  sources="""[BGR] 6.1.4, `bgr-6.1.3-6.1.5.md:145–151`; decomposition L10.11–L10.14.""",
  gen="""Any normed `K`-algebra `A`; the unit-ideal hypothesis `hgen` as in BGR (`a g + Σ aᵢ fᵢ = 1`).""")

t(id='T053', title='BGR 6.1.4/3–4: the universal property of `A⟨X⟩ ⧸ (gX − f)`', file=FRA, deps='T052, T016, T040', par='no', typ='lemma', leaves='L10.15',
  milestone='M5 — with T051, the universal properties of `A⟨f, g⁻¹⟩` and `A⟨f/g⟩` ([RM] §1.4.1–1.4.2; BGR 6.1.4/1–4). `#print axioms` must be standard on both.',
  decls=[(FRA,'isRationalFractions_toRational')],
  sketch="""As T051 with `b i := φ (f i) * ↑hg.unit⁻¹` and `hb := hf`: `haveI : IsClosed … := hA.restricted.isClosed_ideal _`;
`refine ⟨continuous_toRational K A f g, isUnit_toRational K A f g hgen, isPowerBounded_toRational_div K A f g hgen, ?_⟩`;
`intro B _ _ _ _ φ hφ hg hf`; `φ'' := extendAlgHom φ hφ b hf`; kernel: `C g * X i - C (f i) ↦ φ g * (φ (f i) * (φ g)⁻¹) - φ (f i) = 0`
(`extendAlgHom_C`, `extendAlgHom_X`, `mul_comm`, `mul_assoc`, `IsUnit.mul_val_inv`? — `↑u⁻¹ * ↑u = 1` with
`IsUnit.unit_spec`: `Units.inv_mul`, `mul_one`); `liftₐ`; continuity and `comp toRational = φ` as in T051;
uniqueness: on `X i`: `χ (mk (X i)) * φ g = χ (mk (C g * X i)) = χ (mk (C (f i))) = φ (f i)` (the generator), so
`χ (mk (X i)) = φ (f i) * ↑hg.unit⁻¹` (`Units.eq_mul_inv_iff_mul_eq` with `IsUnit.unit_spec`), `= φ'' (X i)`.
`#print axioms` on this and on T051's theorem.""",
  mathlib="""As T051, plus `Units.eq_mul_inv_iff_mul_eq`, `Units.inv_mul`. Board: T016, T040, T052.""",
  sources="""[BGR] 6.1.4/3–4, `bgr-6.1.3-6.1.5.md:140–154`; decomposition L10.15.""",
  gen="""`A` affinoid with `‖1‖ = 1`; `hgen` as BGR.""")

t(id='T054', title='`A[g⁻¹]` is dense in `A⟨f/g⟩`', file=FRA, deps='T052', par='no', typ='lemma', leaves='L10.16',
  decls=[(FRA,'denseRange_awayLift')],
  sketch="""As T048/2: the range of `awayLift` contains `mk (C 1 a)` (`IsLocalization.Away.lift_eq`/`liftAlgHom_apply`,
`Algebra.ofId_apply`, `Ideal.Quotient.algebraMap_eq`, `algebraMap_apply`) and `mk (X A 1 i)` (`toRational_mul_inv` (T052):
`mk (X i) = toRational (f i) * ↑u⁻¹ = awayLift (IsLocalization.mk' _ (f i) ⟨g, _⟩)` by `IsLocalization.lift_mk'`
— `lift (mk' x s) = g x * ↑(hg s)⁻¹`-type lemma `IsLocalization.lift_mk'`; the away version
`IsLocalization.Away.lift` is `IsLocalization.lift` on `Submonoid.powers g`), closed under `+`, `*`
(`map_add`, `map_mul`), hence contains `mk (toRestricted p)` for every polynomial (`MvPolynomial.induction_on`);
`Dense.mono` (a `DenseRange` is a `Dense`, so `h.mono` works) from `(Ideal.Quotient.mk_surjective.denseRange).comp (denseRange_toRestricted _) continuous_quot_mk`.""",
  mathlib="""`IsLocalization.Away.lift_eq`, `IsLocalization.Away.liftAlgHom_apply`, `IsLocalization.lift_mk'`, `IsLocalization.mk'`, `Algebra.ofId_apply`, `MvPolynomial.induction_on`, `Function.Surjective.denseRange`, `DenseRange.comp`, `Dense.mono` (a `DenseRange` is a `Dense`, so `h.mono` works), `continuous_quot_mk`. Board: T052, floor `denseRange_toRestricted`, `MvPolynomial.toRestricted_C`, `MvPolynomial.toRestricted_X`.""",
  sources="""[BGR] 6.1.4, `bgr-6.1.3-6.1.5.md:75–77`, `:135–137`; [RM] §1.4.2; decomposition L10.16 (V2).""",
  gen="""Any normed `K`-algebra `A`; density is topological.""")

# ---------------------------------------------------------------- G11 Affinoid/BaseChange
t(id='T055', title="`Tₙ(K) → Tₙ(K')` is an isometric `K`-algebra map; the base-change map on pure tensors", file=BCH, deps='T001', par='yes (with T049)',
  typ='definition + lemmas', leaves='L11.1–L11.3',
  decls=[(BCH,'mapBase'),(BCH,'norm_mapBase'),(BCH,'baseChangeAlgHom_tmul')],
  sketch="""1. `mapBase.commutes' a`: `Restricted.ext`; `val_map`, `algebraMap_apply` (left: `algebraMap K Tₙ(K) a = C 1 a`),
   `algebraMap_eq_C_comp` (right: `algebraMap K Tₙ(K') a = C 1 (algebraMap K K' a)`, T001), `val_C`,
   `MvPowerSeries.map_C`.
2. `norm_mapBase`: `rw [norm_def, norm_def]` (floor: `‖f‖ = gaussNorm norm 1 f.1`); `val_map`;
   `MvPowerSeries.gaussNorm` is a `sSup`/`iSup` of `‖coeff t _‖ * 1^t` (read the floor's definition); show the
   term functions are equal: `funext t; rw [MvPowerSeries.coeff_map, norm_algebraMap']` (`NormOneClass K'`).
3. `baseChangeAlgHom_tmul`: `Algebra.TensorProduct.lift_tmul` gives `algebraMap K' _ c * mapBase f`;
   `Algebra.smul_def`.""",
  mathlib="""`MvPowerSeries.map_C`, `MvPowerSeries.coeff_map`, `norm_algebraMap'`, `Algebra.TensorProduct.lift_tmul`, `Algebra.smul_def`, `Algebra.ofId_apply`. Floor: `Restricted.map`, `val_map`, `val_C`, `norm_def`, `algebraMap_apply`; board T001.""",
  sources="""[BGR] 6.1.1/8, `bgr-6.1.1.md:104–108`; decomposition L11.1–L11.3.""",
  gen="""Any normed field extension `K'` of `K` with `‖algebraMap c‖ = ‖c‖` (`NormOneClass K'`); finiteness enters only in T056.""")

t(id='T056', title="`K' ⊗_K Tₙ(K) ≅ Tₙ(K')` for a finite extension", file=BCH, deps='T055', par='no', typ='lemmas', leaves='L11.4, L11.5',
  decls=[(BCH,'exists_sum_smul_mapBase'),(BCH,'bijective_baseChangeAlgHom')],
  sketch="""1. `exists_sum_smul_mapBase`: for each `k`, the coordinate `b.coord k : K' →ₗ[K] K` is continuous
   (`LinearMap.continuous_of_finiteDimensional`, needs `CompleteSpace K`), so bounded:
   `obtain ⟨C, -, hC⟩ := SemilinearMapClass.bound_of_continuous (b.coord k) …`; define
   `h k : TateAlgebra K n := ⟨fun ν ↦ b.coord k (coeff ν g.1), hres⟩` with `hres` from `g.2` by `squeeze_zero`
   (`‖coord k x‖ * 1 ≤ C * (‖x‖ * 1)`); the identity: `Restricted.ext (MvPowerSeries.ext fun ν ↦ ?_)`;
   the coefficient of `∑ k, b k • mapBase (h k)` is `∑ k, b k • b.coord k (coeff ν g.1)` (`val_smul` for
   `K'`-scalars (`rfl`), `MvPowerSeries.coeff_smul`, `coeff_map`, `map_sum`-type `MvPowerSeries.coeff_sum`?
   — the floor's `val_add`/`Finset.sum` through `Subtype.val` as an additive hom: `map_sum (Restricted.valAddHom? )`;
   if absent, induct on the finset), which is `coeff ν g.1` by `b.sum_repr`? (`Module.Basis.sum_repr : ∑ k, b.repr x k • b k = x`;
   our form has `b k • coord k x` with `coord k x = b.repr x k` — `Module.Basis.coord_apply`, and `c • b k = b k * c`?
   no: scalars `K` acting on `K'`: `b.repr x k • b k` is the `K`-action, while `b k • (algebraMap K K' c)`-style
   products need `Algebra.smul_def` and `mul_comm`; align with `Algebra.smul_def` + `mul_comm`).
2. `bijective_baseChangeAlgHom`: `constructor`:
   - injective: every `x : K' ⊗[K] Tₙ(K)` is `∑ k, b k ⊗ₜ h k` for a unique `h` — use the basis of the tensor
     product **(search)**: `Algebra.TensorProduct.basis`? `Module.Basis.baseChange`? For `b : Basis ι K K'`,
     Mathlib has `(b.baseChange A)`? — the available statement is for `A ⊗[K] M` with `M`'s basis; here the
     *left* factor carries the basis. Use `TensorProduct.comm K K' (Tₙ K)` to move to `Tₙ(K) ⊗[K] K'` and
     `Module.Basis.baseChange (Tₙ K) b : Basis ι (Tₙ K) ((Tₙ K) ⊗[K] K')` (name to verify by `exact?`/Loogle
     `Basis ?ι ?A (?A ⊗[?R] ?M)`); then `x = ∑ k, h k • (1 ⊗ₜ b k)` with `h := (basis).repr x`, and
     `baseChangeAlgHom x = ∑ k, b k • mapBase (h k)` (`map_sum`, `baseChangeAlgHom_tmul`, `TensorProduct.comm_tmul`,
     `TensorProduct.smul_tmul'`); if this is `0`, coefficientwise `∑ k, coeff ν (h k) • b k = 0` in `K'`
     (`MvPowerSeries.coeff_smul`, `coeff_map`, `Algebra.smul_def`), so all `coeff ν (h k) = 0`
     (`b.linearIndependent`, `Fintype.linearIndependent_iff`), so `h = 0` and `x = 0` (`injective_iff_map_eq_zero`).
   - surjective: `obtain ⟨h, rfl⟩ := exists_sum_smul_mapBase K K' n b g`; `⟨∑ k, b k ⊗ₜ h k, by simp [map_sum, baseChangeAlgHom_tmul]⟩`.""",
  mathlib="""`LinearMap.continuous_of_finiteDimensional`, `SemilinearMapClass.bound_of_continuous`, `Module.Basis.coord`, `Module.Basis.coord_apply`, `Module.Basis.sum_repr`, `Module.Basis.linearIndependent`, `Fintype.linearIndependent_iff`, `Module.Basis.baseChange` (search), `TensorProduct.comm`, `TensorProduct.comm_tmul`, `TensorProduct.smul_tmul'`, `MvPowerSeries.coeff_smul`, `MvPowerSeries.coeff_map`, `Algebra.smul_def`, `injective_iff_map_eq_zero`, `squeeze_zero`. Board: T055, floor `Restricted.ext`, `val_map`.""",
  sources="""[BGR] 6.1.1/8, `bgr-6.1.1.md:107–108`; 3.7.1, `bgr-3.7.md:17–19`; decomposition L11.4–L11.5 (D8).""",
  gen="""Finite extensions `K'/K` (`Fintype ι` basis), `K` complete.""")

t(id='T057', title="`K' ⊗_K A` is `K'`-affinoid", file=BCH, deps='T056', par='no', typ='lemma', leaves='L11.6',
  decls=[(BCH,'baseChange')],
  sketch="""`obtain ⟨n, α, hα⟩ := hA`; `have hsurj := Algebra.TensorProduct.map_surjective (AlgHom.id K' K') α Function.surjective_id hα`
(check the implicit arguments: `map (f : A →ₐ[S] B) (g : C →ₐ[R] D)` with `S := K'`, `R := K`);
`exact ⟨n, (Algebra.TensorProduct.map (AlgHom.id K' K') α).comp (TateAlgebra.baseChangeEquiv K K' n).symm.toAlgHom,
hsurj.comp (TateAlgebra.baseChangeEquiv K K' n).symm.surjective⟩`.""",
  mathlib="""`Algebra.TensorProduct.map`, `Algebra.TensorProduct.map_surjective`, `Function.surjective_id`, `AlgEquiv.surjective`. Board: T056 (`baseChangeEquiv`).""",
  sources="""[BGR] 6.1.1/9, `bgr-6.1.1.md:110–117`; [RM] §1.1.6; decomposition L11.6 (V7).""",
  gen="""Finite `K'/K`; `A` any affinoid `K`-algebra.""")

# ---------------------------------------------------------------- G12 Affinoid/Polydisc
t(id='T058', title='The rescaling `Tₙ → T_{n,ρ}`, `Xᵢ ↦ cᵢ Xᵢ^{sᵢ}`: norm one and injectivity', file=POL, deps='T003', par='yes (with T049)',
  typ='lemmas', leaves='L12.1, L12.2',
  decls=[(POL,'norm_smul_X_pow'),(POL,'injective_rescaleAlgHom')],
  sketch="""1. `norm_smul_X_pow`: `rw [norm_smul, norm_pow, norm_X, norm_one, one_mul, mul_comm]; exact hc i`
   (`NormMulClass (Restricted K ρ)` for `norm_pow`; `norm_X : ‖X K ρ i‖ = ‖(1 : K)‖ * ρ i`).
2. `injective_rescaleAlgHom`: coefficient formula first: `have hcoeff : ∀ f t, coeff t (rescaleAlgHom ρ s c hc f).1 =
   if ∃ μ, t = μ * s then …` — cleaner: define `shift : (Fin n →₀ ℕ) → (Fin n →₀ ℕ) := fun μ ↦ Finsupp.ofSupportFinite
   (fun i ↦ μ i * s i) _` (injective by `hs`: `Nat.eq_of_mul_eq_mul_right`), and show by `hasSum_eval₂` mapped through
   the continuous `coeff t` (as T018/4) that `coeff (shift μ) (φ f).1 = coeff μ f.1 * ∏ i, c i ^ μ i`
   (`(c i • X i ^ s i) ^ k = c i ^ k • X i ^ (s i * k)` by `smul_pow`, `pow_mul`; the monomial `∏ (c i • X i^{s i})^{μ i}`
   is `(∏ c i ^ μ i) • monomial (shift μ) 1` — `Finsupp.prod`, `MvPowerSeries.X_pow_eq`, `monomial_mul_monomial`,
   `Finset.prod_smul`? (`smul_mul_smul_comm`); the summand's coefficient at `shift μ` is nonzero only for `ν = μ`
   (`hasSum_ite_eq` with `shift` injective)); then `(injective_iff_map_eq_zero _).2 fun f hf ↦ Restricted.ext
   (MvPowerSeries.ext fun μ ↦ ?_)`: `coeff (shift μ) (φ f).1 = 0` gives `coeff μ f.1 * ∏ c i ^ μ i = 0`, and the product
   is nonzero (`Finset.prod_ne_zero_iff`, `pow_ne_zero`, `c i ≠ 0` from `hc i`: `ρ i ^ s i * ‖c i‖ = 1` forces `‖c i‖ ≠ 0`).""",
  mathlib="""`norm_smul`, `norm_pow`, `norm_one`, `smul_pow`, `pow_mul`, `Finsupp.ofSupportFinite`, `Nat.eq_of_mul_eq_mul_right`, `HasSum.map`, `hasSum_ite_eq`, `HasSum.unique`, `MvPowerSeries.X_pow_eq`, `MvPowerSeries.monomial_mul_monomial`, `smul_mul_smul_comm`, `Finset.prod_ne_zero_iff`, `pow_ne_zero`, `injective_iff_map_eq_zero`. Floor: `norm_X`, `hasSum_eval₂` (through `aeval`'s definition), `norm_coeff_mul_prod_le` (continuity of `coeff`), `Restricted.ext`.""",
  sources="""[BGR] 6.1.5/4, `bgr-6.1.3-6.1.5.md:201–203`; decomposition L12.1–L12.2 (D7).""",
  gen="""Any positive polyradius `ρ` and `s`, `c` with `ρᵢ^{sᵢ} ‖cᵢ‖ = 1`, `sᵢ ≠ 0`.""")

t(id='T059', title='`T_{n,ρ}` is a finite `Tₙ`-module via the rescaling (BGR 6.1.5/4, the computation)', file=POL, deps='T058', par='no', typ='lemmas', leaves='L12.3, L12.4',
  decls=[(POL,'isRestricted_shiftCoeff'),(POL,'finite_rescaleAlgHom')],
  sketch="""1. `isRestricted_shiftCoeff`: unfold `IsRestricted` at `1` (`t.prod (1 · ^ ·) = 1`); the term is
   `‖coeff (shift μ + l) f.1‖ * ∏ i, ‖c i‖⁻¹ ^ μ i` (`norm_mul`, `norm_prod`, `norm_pow`, `norm_inv`);
   with `hc`: `‖c i‖⁻¹ = ρ i ^ s i`, so the product is `ρ^{shift μ}` and the term equals
   `(‖coeff (shift μ + l) f.1‖ * ρ^{shift μ + l}) * ρ^{-l}` (`Finsupp.prod_add_index'`, `pow_add`, `mul_inv_cancel₀`);
   `f.2` composed with the injective `μ ↦ shift μ + l` (`Function.Injective.tendsto_cofinite`,
   `Filter.Tendsto.comp`) and `Tendsto.mul_const`, `zero_mul`.
2. `finite_rescaleAlgHom`: `letI := (rescaleAlgHom ρ s c hc).toRingHom.toAlgebra`; `Module.Finite` with the
   generating set `S := (Fintype.piFinset fun i ↦ Finset.range (s i)).image (fun l ↦ monomial ρ (Finsupp.equivFunOnFinite.symm l) 1)`
   (as `X^λ`): `⟨S, ?_⟩` (`Submodule.fg_def`/`Module.Finite.iff_fg`, `Submodule.span = ⊤`):
   for `f`, write `f = ∑ l ∈ piFinset, φ (g l) * X^l` where `g l := ⟨Σ_μ coeff (shift μ + l) f.1 * ∏ (c i)⁻¹^{μ i} X^μ, isRestricted_shiftCoeff …⟩`;
   proof by `Restricted.ext (MvPowerSeries.ext fun ν ↦ ?_)`: decompose `ν = shift (ν / s) + (ν % s)` uniquely
   (`Nat.div_add_mod`, componentwise `Finsupp` arithmetic), the coefficient of `φ (g l) * X^l` at `ν` is the coefficient
   of `φ (g l)` at `ν - l` (`MvPowerSeries.coeff_mul_X_pow'`? — `coeff_mul_monomial` with `le`), which by T058's
   formula is `coeff (shift μ + l) f.1 * ∏ c^μ * ∏ c⁻¹^μ = coeff ν f.1` when `l = ν % s`, `μ = ν / s`, and `0` for the
   other `l` (not of the form `shift μ' + l`); `Finset.sum_eq_single`. Then `Submodule.mem_span` via
   `Submodule.sum_mem`, `Submodule.smul_mem` (`φ (g l) • X^l = φ (g l) * X^l` by `Algebra.smul_def`/`RingHom.smul_toAlgebra`).
   Budget 120 lines: isolate `private` lemmas for the coefficient of `φ (g l) * X^l` and for the `div/mod` decomposition.""",
  mathlib="""`Finsupp.prod_add_index'`, `pow_add`, `mul_inv_cancel₀`, `Function.Injective.tendsto_cofinite`, `Filter.Tendsto.comp`, `Filter.Tendsto.mul_const`, `Fintype.piFinset`, `Finset.range`, `Finsupp.equivFunOnFinite`, `Module.Finite.iff_fg`, `Submodule.fg_def`, `Submodule.mem_span`, `Submodule.sum_mem`, `Submodule.smul_mem`, `Nat.div_add_mod`, `MvPowerSeries.coeff_mul_monomial`, `Finset.sum_eq_single`, `RingHom.smul_toAlgebra`, `Algebra.smul_def`. Board: T058 (coefficient formula), floor `monomial`, `val_monomial`, `norm_prod` (Mathlib `norm_prod` for `NormMulClass`).""",
  sources="""[BGR] 6.1.5/4, `bgr-6.1.3-6.1.5.md:203–212`; decomposition L12.3–L12.4.""",
  gen="""As T058, with `cᵢ ≠ 0` explicit.""")

t(id='T060', title='`T_{n,ρ}` is affinoid for `ρᵢ^s ∈ |K^×|`; the open-disc example', file=POL, deps='T059, T020', par='no', typ='lemmas', leaves='L12.5, L12.6',
  decls=[(POL,'isAffinoidAlgebra_of_forall_exists_pow_eq_norm'),(POL,'exists_summable_not_isRestricted')],
  sketch="""1. `isAffinoidAlgebra_of_forall_exists_pow_eq_norm`: `choose s c hs hc0 h using h`; `have hc : ∀ i, ρ i ^ s i * ‖(c i)⁻¹‖ = 1 :=
   fun i ↦ by rw [norm_inv, ← h i, mul_inv_cancel₀ (pow_ne_zero _ (Fact.out (p := ∀ i, 0 < ρ i) i).ne')]`;
   `exact IsAffinoidAlgebra.of_finite_tateAlgebra (rescaleAlgHom ρ s (fun i ↦ (c i)⁻¹) hc) (continuous_rescaleAlgHom hc)
   (finite_rescaleAlgHom hc hs fun i ↦ inv_ne_zero (hc0 i))`.
2. `exists_summable_not_isRestricted`: `obtain ⟨π, hπ⟩ := NormedField.exists_one_lt_norm K`; for each `ν`,
   `obtain ⟨k, hk₁, hk₂⟩ := exists_mem_Ico_zpow (x := ρ⁻¹ ^ ν) (by positivity) hπ` (`‖π‖^k ≤ ρ^{-ν} < ‖π‖^{k+1}`);
   `choose k hk using this`; `a ν := π ^ k ν` (`zpow`, `norm_zpow`); `f := PowerSeries.mk a`;
   - summability: `Summable.of_norm_bounded (g := fun ν ↦ (‖x‖ / ρ) ^ ν) (summable_geometric_of_lt_one (by positivity) (div_lt_one hρ |>.2 hx))
     fun ν ↦ ?_`: `‖a ν * x ^ ν‖ = ‖a ν‖ * ‖x‖^ν ≤ ρ^{-ν} ‖x‖^ν = (‖x‖/ρ)^ν` (`norm_mul`, `norm_pow`, `hk₁`,
     `div_pow`, `inv_pow`, `mul_le_mul_of_nonneg_right`);
   - not restricted: `intro hres; rw [PowerSeries.IsRestricted.isRestricted_iff? ]` (the floor's `isRestricted_iff`:
     `Tendsto (fun n ↦ ‖coeff n f‖ * ρ ^ n) cofinite (𝓝 0)`); `‖a ν‖ ρ^ν > ‖π‖⁻¹` for all `ν` (`hk₂`: `ρ^{-ν} < ‖π‖^{k+1}`
     gives `‖π‖⁻¹ < ‖π‖^k ρ^ν`, `zpow_add₀`, `zpow_one`, `inv_lt_iff`-style); `(hres.eventually (gt_mem_nhds (inv_pos.2 …))).exists`
     with `Filter.eventually_cofinite`/`Filter.Eventually.exists` (cofinite is `NeBot` on `ℕ`) gives a `ν` with
     `‖coeff ν f‖ * ρ^ν < ‖π‖⁻¹`, contradiction (`PowerSeries.coeff_mk`).""",
  mathlib="""`NormedField.exists_one_lt_norm`, `exists_mem_Ico_zpow`, `norm_zpow`, `zpow_add₀`, `zpow_one`, `PowerSeries.mk`, `PowerSeries.coeff_mk`, `Summable.of_norm_bounded`, `summable_geometric_of_lt_one`, `div_lt_one`, `div_pow`, `inv_pow`, `norm_mul`, `norm_pow`, `gt_mem_nhds`, `Filter.Eventually.exists`, `Filter.Tendsto.eventually`, `inv_ne_zero`, `pow_ne_zero`, `mul_inv_cancel₀`, `norm_inv`. Board: T020 (`of_finite_tateAlgebra`), T058–T059, floor `PowerSeries.isRestricted_iff` (`Restricted/PowerSeries/Basic.lean`).""",
  sources="""[BGR] 6.1.5/4, `bgr-6.1.3-6.1.5.md:199–213`; 6.1.5, `:180–185`; [RM] §1.5.2; decomposition L12.5–L12.6 (V4, E6).""",
  gen="""Item 1: every positive polyradius with `ρᵢ^{sᵢ} ∈ |K^×|`; item 2: every `ρ > 0` over a nontrivially normed field.""")

# ---------------------------------------------------------------- G13 Affinoid/Examples
t(id='T061', title='Examples: `K⟨X⟩ ⧸ (X² − a)` is two-dimensional; `K⟨X⟩ ⧸ (X − a) ≅ K`', file=EXA, deps='T013', par='yes (with T062)',
  typ='lemmas', leaves='L13.1–L13.3',
  decls=[(EXA,'finrank_quotient_X_sq_sub'),(EXA,'ker_aeval_eq_span'),(EXA,'nonempty_algEquiv_quotient_X_sub')],
  sketch="""1. `finrank_quotient_X_sq_sub`: `ω : Polynomial (TateAlgebra K 0) := X ^ 2 - C (C 1 a)`; `hω : IsWeierstrassPolynomial K 0 ω`
   by Layer 0's `isWeierstrassPolynomial_iff` (monic: `Polynomial.monic_X_pow_sub_C`? for degree `2 > 0`; coefficient
   norms `≤ 1`: `norm_C`, `ha.le`, `norm_one`, `norm_zero` — see Layer 0's `isWeierstrassPolynomial_example` in
   `TateAlgebra/Examples.lean` for the exact pattern); `ofPolynomial K 0 ω = X K 1 0 ^ 2 - C 1 a` (`map_sub`, `map_pow`,
   Layer 0's `ofPolynomial_X`/`ofPolynomial_C`, with `C (C a) ↦ C a` through `T₀`'s constants — or `Restricted.ext`
   on coefficients); `hω.bijective_quotientMap` gives `T₀[X] ⧸ (ω) ≃+* T₁ ⧸ (ofPolynomial ω)` (`RingEquiv.ofBijective`),
   upgrade to `≃ₗ[K]` (`K`-linearity: the quotient map is a `K`-algebra map); `finrank` of `T₀[X] ⧸ (ω)`:
   `AdjoinRoot ω` (`AdjoinRoot` is definitionally `Polynomial _ ⧸ span {ω}`), `(AdjoinRoot.powerBasis hω.monic.ne_zero).finrank`
   gives `finrank T₀ _ = natDegree ω = 2`, then `finrank K _ = finrank K T₀ * finrank T₀ _ = 1 * 2`
   (`Module.finrank_mul_finrank` with the tower `K → T₀ → _`, `finrank K T₀ = 1` by `isEmptyEquiv`) — or directly
   build a `K`-basis `1, X̄` from `existsUnique_remainder`. Budget 80 lines.
2. `ker_aeval_eq_span`: `le_antisymm`; `⊇`: `Ideal.span_le.2 (Set.singleton_subset_iff.2 (by simp [RingHom.mem_ker, aeval_X, aeval_C]))`
   (`aeval (C 1 a) = a`: `aeval_C`? — `aeval_toRestricted` with `MvPolynomial.C`, or the algebra map); `⊆`: for `f` with
   `aeval f = 0`: `hg : IsMulDistinguishedX0 (X K 1 0 - C 1 a) 1` by `isMulDistinguishedX0_iff` (coefficients of `X 0`:
   `coeffX0 _ 1 = 1`, `coeffX0 _ 0 = -C a`, higher `0`; norms via `norm_C`, `ha`); `obtain ⟨q, r, hr, hf⟩ :=
   weierstrassDivision_exists hg f` (`r.degree < 1`, so `r = Polynomial.C r₀`: `Polynomial.eq_C_of_degree_le_zero`);
   apply `aeval` to `hf`: `0 = aeval q * 0 + aeval (ofPolynomial (C r₀))`, and `aeval (ofPolynomial (C r₀)) = aeval (ofTail r₀)`
   is `r₀` viewed in `K` (`ofTail_apply`, `aeval_toRestricted`-style, `isEmptyEquiv`); so `r₀ = 0`, `f = q * (X - C a)`,
   `Ideal.mem_span_singleton'`.
3. `nonempty_algEquiv_quotient_X_sub`: `⟨(Ideal.quotientEquivAlgOfEq K (ker_aeval_eq_span ha)).symm.trans
   (Ideal.quotientKerAlgEquivOfSurjective hsurj)⟩` with `hsurj : Surjective (aeval 1 (fun _ ↦ a) _)` from
   `fun c ↦ ⟨algebraMap K _ c, by simp⟩` (`AlgHom.commutes`).""",
  mathlib="""`Polynomial.monic_X_pow_sub_C`, `AdjoinRoot.powerBasis`, `PowerBasis.finrank`, `Module.finrank_mul_finrank`, `RingEquiv.ofBijective`, `Polynomial.eq_C_of_degree_le_zero`, `Ideal.mem_span_singleton'`, `Ideal.span_le`, `Ideal.quotientEquivAlgOfEq`, `Ideal.quotientKerAlgEquivOfSurjective`, `AlgHom.commutes`. Layer 0: `isWeierstrassPolynomial_iff`, `IsWeierstrassPolynomial.bijective_quotientMap`, `IsWeierstrassPolynomial.existsUnique_remainder`, `isMulDistinguishedX0_iff`, `weierstrassDivision_exists`, `ofPolynomial`, `ofTail_apply`, `aeval_X`, `aeval_toRestricted`, `isEmptyEquiv`, `Examples.isWeierstrassPolynomial_example` (model).""",
  sources="""[RM] Layer 1 Examples; [BGR] 5.2.3/3 (Layer 0); decomposition L13.1–L13.3.""",
  gen="""`‖a‖ < 1` in item 1 (the roadmap's `a = p`; `‖a‖ ≤ 1` would suffice with Layer 0's definition), `‖a‖ ≤ 1` in items 2–3.""")

t(id='T062', title='Examples: `aX − 1` is a unit for `‖a‖ < 1`; the cusp is distinguished', file=EXA, deps='none', par='yes (with T061)',
  typ='lemmas', leaves='L13.4, L13.5, L13.7',
  decls=[(EXA,'isUnit_C_mul_X_sub_one'),(EXA,'subsingleton_quotient_C_mul_X_sub_one'),(EXA,'isMulDistinguishedX0_cusp')],
  sketch="""1. `isUnit_C_mul_X_sub_one`: `have h : ‖C 1 a * X K 1 0‖ < 1 := by rw [norm_mul, norm_C, Examples.norm_X? ]` —
   `norm_X` then `norm_one`, `Pi.one_apply`, `mul_one`; `rw [← neg_sub, IsUnit.neg_iff]`; `isUnit_one_sub_of_norm_lt_one h`
   (Layer 0's `isUnit_one_add_p_mul_X` is the model).
2. `subsingleton_quotient_C_mul_X_sub_one`: `Ideal.Quotient.subsingleton_iff.2 (Ideal.span_singleton_eq_top.2 (isUnit_C_mul_X_sub_one ha))`.
3. `isMulDistinguishedX0_cusp`: `rw [isMulDistinguishedX0_iff]` (Layer 0 `Tower.lean`; read its exact shape: a unit
   leading coefficient `coeffX0 g 2`, `‖coeffX0 g 2‖ = ‖g‖`, and `‖coeffX0 g ν‖ < ‖g‖` for `ν > 2`); write
   `X K 1 0 ^ 2 - X K 1 1 ^ 3 = ofPolynomial K 1 (Polynomial.X ^ 2 - Polynomial.C (X K 1 0 ^ 3))` (`map_sub`, `map_pow`,
   `ofPolynomial`'s `X`/`C` lemmas in `Distinguished.lean`: `ofTail_X` gives `X 1 = ofTail (X 0)`), then `coeffX0_ofPolynomial`
   and `Polynomial.coeff_sub`, `coeff_X_pow`, `coeff_C`; norms: `‖g‖ = 1` (`norm_sub_eq_max_of_norm_ne_norm`? both terms have
   norm `1`: use `norm_le_iff` + the coefficient at `single 0 2`), `‖1‖ = 1`, `‖0‖ < 1`.""",
  mathlib="""`neg_sub`, `IsUnit.neg_iff`, `isUnit_one_sub_of_norm_lt_one`, `Ideal.Quotient.subsingleton_iff`, `Ideal.span_singleton_eq_top`, `Polynomial.coeff_sub`, `Polynomial.coeff_X_pow`, `Polynomial.coeff_C`. Layer 0: `norm_X`, `norm_C`, `isMulDistinguishedX0_iff`, `coeffX0_ofPolynomial`, `ofTail_X`, `ofPolynomial`, `Examples.isUnit_one_add_p_mul_X` (model).""",
  sources="""[RM] Layer 1 Examples; decomposition L13.4, L13.5, L13.7.""",
  gen="""`‖a‖ < 1` (the `p`-adic instance is the complete `subsingleton_quotient_p_mul_X_sub_one`).""")

t(id='T063', title='Examples: `K⟨X⟩⟨X⁻¹⟩ = K⟨X, Y⟩ ⧸ (XY − 1)`; the two presentations of `K` have equal residue norms', file=EXA, deps='T009, T010, T005, T061', par='no',
  typ='lemmas', leaves='L13.6, L13.8',
  decls=[(EXA,'nonempty_algEquiv_generalisedFractions_X'),(EXA,'exists_algEquiv_quotient_X_norm_eq')],
  sketch="""1. `nonempty_algEquiv_generalisedFractions_X`: `e₀ : Fin 0 ⊕ Fin 1 ≃ Fin 1 := Equiv.sumEmpty? ` — use
   `(Equiv.sumComm _ _).trans (Equiv.sumEmpty (Fin 1) (Fin 0))` or `Equiv.emptySum`, whichever exists (`IsEmpty (Fin 0)`);
   `e₁ : Restricted (TateAlgebra K 1) (1 : Fin 0 ⊕ Fin 1 → ℝ) ≃ₐ[K] Restricted (TateAlgebra K 1) (1 : Fin 1 → ℝ) :=
   AlgEquiv.ofRingEquiv (f := renameEquiv _ e₀) (by …)` (T009, T001 as in T040); `e₂ := TateAlgebra.sumEquiv K 1 1`;
   `e := e₁.trans e₂`; `⟨Ideal.quotientEquivAlg (fractionIdeal _ _ _) (Ideal.span {X K 1 0 * X K 1 1 - 1}) e ?_⟩` with
   `Ideal.map e (fractionIdeal …) = span {…}`: `fractionIdeal` is the span of `range (Fin.elim0-indexed) ∪ range (fun j ↦ C (X 0) * X (inr j) - 1)`;
   `Ideal.map_span`, `Set.image_union`, the first range is empty (`Set.range_eq_empty`), the second image is
   `{e (C (X 0) * X (inr 0) - 1)}` (`Set.range_unique`-style with `Fin 1`), computed by `map_sub`, `map_mul`, `map_one`,
   `renameEquiv_C`, `renameEquiv_X`, `sumEquiv_C`, `sumEquiv_X` (`castAdd 1 0 = 0`, `natAdd 1 0 = 1` by `decide`/`rfl`),
   `mul_comm`. Expect seam friction on `Fin.castAdd`/`Fin.natAdd` numerals: state the two `X` images as `have`s.
2. `exists_algEquiv_quotient_X_norm_eq`: `e := (Ideal.quotientEquivAlgOfEq K (ker_aeval_eq_span (a := 0) (by simp))).symm.trans
   (Ideal.quotientKerAlgEquivOfSurjective hsurj)` (with `C 1 0 = 0`: `map_zero`, `sub_zero`); `refine ⟨e, fun x ↦ ?_⟩`;
   `obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x`; `e (mk f) = aeval 1 (fun _ ↦ 0) _ f = coeff 0 f.1`
   (`aeval_apply`: the `tsum` of `coeff t f * ∏ 0 ^ t i` is the `t = 0` term: `tsum_eq_single 0`, `Finsupp.prod_pow`,
   `zero_pow`, `ne_eq`); `‖mk f‖ = ‖coeff 0 f.1‖`: `Ideal.Quotient.norm_mk_eq_norm_of_forall_le` (T005) applied to
   the representative `C 1 (coeff 0 f.1)` (same class: `f - C (coeff 0 f) ∈ span {X}`, from Weierstrass division or from
   `ker_aeval_eq_span`: `aeval (f - C c₀) = c₀ - c₀ = 0`), with `h : ∀ g ∈ span {X}, ‖C c₀‖ ≤ ‖C c₀ - g‖` by
   `norm_coeff_le` at `t = 0`: `coeff 0 (C c₀ - g) = c₀` since `coeff 0 g = 0` for `g = q * X` (`MvPowerSeries.coeff_zero_mul_X`);
   finish with `norm_C`.""",
  mathlib="""`Equiv.sumEmpty`, `Equiv.emptySum`, `Equiv.sumComm`, `AlgEquiv.ofRingEquiv`, `Ideal.quotientEquivAlg`, `Ideal.map_span`, `Set.image_union`, `Set.range_eq_empty`, `Ideal.quotientEquivAlgOfEq`, `Ideal.quotientKerAlgEquivOfSurjective`, `tsum_eq_single`, `Finsupp.prod_pow`, `zero_pow`, `MvPowerSeries.coeff_zero_mul_X`, `Ideal.Quotient.mk_surjective`. Board: T005, T009, T010, T061; floor `norm_coeff_le`, `norm_C`, `aeval_apply`.""",
  sources="""[RM] Layer 1 Examples; [BGR] 6.1.4, `bgr-6.1.3-6.1.5.md:99–102`; decomposition L13.6, L13.8.""",
  gen="""Concrete examples over any complete ultrametric nontrivially normed field.""")

# ---------------------------------------------------------------- chain root
t(id='T064', title='Chain root: import the board and run the full gate', file='PhD/TauCeti.lean', deps='CLEANUP-1 … CLEANUP-24 (every final per-file cleanup)', par='no',
  typ='gate', leaves='—',
  decls=[],
  statement_override="""-- PhD/TauCeti.lean: add, in alphabetical position among the RigidAnalyticGeometry imports,
import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.Examples
-- (Layer 0's leaf `…TateAlgebra.Examples` stays; the new leaf imports it.)""",
  sketch="""1. Add the import line to `PhD/TauCeti.lean` (keep the file's alphabetical order).
2. `lake build PhD.TauCeti` must pass (expect about 3 600 jobs) with **no** `sorry` warning anywhere.
3. `grep -rn "sorry" PhD/TauCeti/Code/RigidAnalyticGeometry PhD/TauCeti/Code/PadicFunctionalAnalysis` must be empty.
4. `scratch/axioms.py` (or a `#print axioms` file imported from the chain root) on the five milestones:
   `IsAffinoidAlgebra.exists_finite_injective`, `AlgHom.continuous_of_isAffinoidAlgebra`,
   `Affinoid.isAffinoidTensorProduct_tensorQuotient`, `Affinoid.isGeneralisedFractions_toFractions`,
   `Affinoid.isRationalFractions_toRational`, and on `IsAffinoidAlgebra.isJapaneseRing`,
   `MvPowerSeries.Restricted.isAffinoidAlgebra_of_forall_exists_pow_eq_norm`, `IsAffinoidAlgebra.baseChange`:
   only `propext`, `Classical.choice`, `Quot.sound`.
5. Never `import PhD.Main.*`: `grep -rn "PhD.Main" PhD/TauCeti` must be empty.""",
  mathlib="""—""",
  sources="""[RM] Layer 1; the Layer 0 board's T081 (model).""",
  gen="""—""")
