# ---------------- Map ----------------
ticket("T013", "Functoriality in the ring: `map φ`", MA, "CLEANUP-5", "no", "definition + lemmas", "L13.1–L13.5",
 ["map", "map_single", "norm_map_apply_le", "norm_map_apply_of_forall_norm_eq", "map_reindex"],
 """1. `map`'s tendsto: `squeeze_zero_norm (fun i ↦ (hφ (f i)).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg _)))`-style
   with the bound `max C 0 * ‖f i‖ → 0` (`(tendsto_cofinite f).norm.const_mul _`, `mul_zero`); `map_add'`: `ext; simp [map_add]`;
   `map_smul'`: `ext i; simp [smul_apply, smul_eq_mul, map_mul]` (`φ (r * f i) = φ r * φ (f i)` and the target action is `φ r • _`);
   the `mkContinuous` bound with `max C 0`: `norm_le_of_forall_le (mul_nonneg (le_max_right _ _) (norm_nonneg f)) fun i ↦
   (hφ (f i)).trans (mul_le_mul (le_max_left _ _) (norm_apply_le f i) (norm_nonneg _) (le_max_right _ _))`.
2. `map_single`: `ext j; by_cases h : j = i <;> simp [map_apply, coe_single, Pi.single_apply, h, map_zero]`.
3. `norm_map_apply_le`: `norm_le_of_forall_le (mul_nonneg hC (norm_nonneg f)) fun i ↦ (hφ (f i)).trans (mul_le_mul_of_nonneg_left (norm_apply_le f i) hC)`.
4. `norm_map_apply_of_forall_norm_eq`: `le_antisymm` via `norm_le_of_forall_le` twice, each coordinate by `hφ` and `norm_apply_le`.
5. `map_reindex`: `ext; rfl`.""",
 "`squeeze_zero_norm`, `Filter.Tendsto.const_mul`, `map_add`, `map_mul`, `map_zero`, `Pi.single_apply`, `mul_le_mul`, `le_max_left`, `le_max_right`.",
 "[RM] §2.1.5 (\"A bounded ring homomorphism `φ : R → S` induces `C₀(I, R) → C₀(I, S)` of norm at most the bound of `φ`, an isometry when `φ` is, and compatible with `single`, `eval`, and reindexing\").",
 "The bound `C` is an explicit argument; the `mkContinuous` constant is `max C 0` so the obligation holds for every `C` (plan decision 7); `norm_map_apply_le` takes `0 ≤ C`.")

cleanup("CLEANUP-6", MA, "T013", "Final cleanup of `Map.lean`")

# ---------------- Truncation ----------------
ticket("T014", "Coordinate truncations: definition and pointwise lemmas", TR, "CLEANUP-2", "yes (parallel with T006–T013)", "definition + lemmas", "L14.1–L14.8",
 ["truncation", "truncation_apply_of_mem", "truncation_apply_of_notMem", "norm_truncation_apply_le", "norm_truncation_le", "truncation_truncation", "truncation_single", "norm_sub_truncation_le"],
 """1. `truncation`'s tendsto: `squeeze_zero_norm (fun i ↦ by split_ifs <;> simp) (tendsto_cofinite f).norm` (`‖if i ∈ S then f i else 0‖ ≤ ‖f i‖`);
   `map_add'`/`map_smul'`: `ext i; simp only [...]; split_ifs <;> simp`; the bound `1`: `norm_le_of_forall_le (by simp) fun i ↦ by
   rw [one_mul]; split_ifs <;> simp [norm_apply_le]`.
2. `truncation_apply_of_mem`: `if_pos hi`; `truncation_apply_of_notMem`: `if_neg hi`.
3. `norm_truncation_apply_le`: `norm_le_of_forall_le (norm_nonneg f) fun i ↦ by rw [truncation_apply]; split_ifs <;> simp [norm_apply_le]`.
4. `norm_truncation_le`: `opNorm_le_bound _ zero_le_one fun f ↦ by rw [one_mul]; exact norm_truncation_apply_le S f`.
5. `truncation_truncation`: `ext i; simp only [truncation_apply]; split_ifs <;> rfl`.
6. `truncation_single`: `ext j; by_cases hj : j ∈ S <;> by_cases hji : j = i <;> simp [truncation_apply, coe_single, Pi.single_apply, *]`
   (the right-hand `if` is on `i ∈ S`; when `j = i` the two conditions agree).
7. `norm_sub_truncation_le`: `norm_le_of_forall_le hε fun i ↦ by rw [sub_apply, truncation_apply]; split_ifs with hi <;> simp [h i, *]`
   (`sub_self`, `norm_zero`, `sub_zero`, `h i hi`).""",
 "`squeeze_zero_norm`, `if_pos`, `if_neg`, `ContinuousLinearMap.Ultra.opNorm_le_bound` [L1], `Pi.single_apply`, `sub_apply`, `norm_apply_le`.",
 "[RM] §2.6.3 (\"the truncation `π_S : C₀(I, R) →L[R] C₀(I, R)` (restriction of coordinates to `S`) has norm at most `1`\"); [Bel] l. 2038–2042 (\"`π_S : M → M` the projection of `M` onto `M_S` sending `e_i` to `e_i` if `i ∈ S`, and `e_i` to `0` if `i ∉ S`\").",
 "Stated for an arbitrary `S : Set I` with `[DecidablePred (· ∈ S)]`; the finite case is `S = ↑s` for `s : Finset I`.")

ticket("T015", "The range of a truncation: closed direct summand, finite free module", TR, "T014", "no", "lemmas", "L15.1–L15.3",
 ["mem_range_truncation_iff", "closedComplemented_range_truncation", "range_truncation_finset"],
 """1. `mem_range_truncation_iff`: `⟨by rintro ⟨g, rfl⟩ i hi; exact truncation_apply_of_notMem S g hi, fun h ↦ ⟨f, by ext i; rw [truncation_apply]; split_ifs with hi; · rfl; · exact (h i hi).symm⟩⟩`
   (`LinearMap.mem_range`).
2. `closedComplemented_range_truncation`: unfold `Submodule.ClosedComplemented` (`∃ f : E →L[R] p, ∀ x : p, f x = x`); take
   `(truncation S).codRestrict (LinearMap.range _) (fun g ↦ LinearMap.mem_range_self _ g)` and, for `x = ⟨_, g, rfl⟩`,
   `Subtype.ext (truncation_truncation S g)`.
3. `range_truncation_finset`: `le_antisymm`: (≤) `rintro _ ⟨g, rfl⟩`; `truncation ↑s g = ∑ i ∈ s, g i • single i 1` (`ext j`, `sum_apply`,
   `smul_single`, `coe_single`, `Finset.sum_pi_single'`), which is in the span (`Submodule.sum_mem`, `Submodule.smul_mem`,
   `Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩`); (≥) `Submodule.span_le.2`: `rintro _ ⟨⟨i, hi⟩, rfl⟩`; `mem_range_truncation_iff.2 fun j hj ↦
   single_apply_of_ne (fun h ↦ hj (h ▸ hi)) 1`.""",
 "`LinearMap.mem_range`, `LinearMap.mem_range_self`, `ContinuousLinearMap.codRestrict`, `Submodule.ClosedComplemented` (def), `Subtype.ext`, `Finset.sum_pi_single'`, `Submodule.span_le`, `Submodule.sum_mem`, `Submodule.smul_mem`, `Submodule.subset_span`.",
 "[RM] §2.6.3 (\"has range the finite free module on `S`\"), §2.2.5 (\"the closed span of `e|_S` is a closed direct summand with the projection `π_S`\"), the model-space case; [Bel] l. 2038–2042 (\"`M_S` the finite free sub-module of `M` generated by the `e_s`, `s ∈ S`\").",
 "Any normed ring `R`.")

ticket("T016", "Truncations converge to the identity along finite subsets", TR, "T014", "yes (parallel with T015)", "lemma", "L16.1",
 ["tendsto_truncation_finset"],
 """`Metric.tendsto_atTop.2 fun ε hε ↦ ?_`. Let `B := {i | ¬ ‖f i‖ < ε / 2}`, finite by `Filter.eventually_cofinite.1 (Metric.tendsto_nhds.1
(tendsto_cofinite f) (ε / 2) (half_pos hε))` (after `dist_zero_right`); take `N := B.toFinset`. For `s ≥ N`:
`dist (truncation ↑s f) f = ‖f - truncation ↑s f‖` (`dist_eq_norm'`), bounded by `ε / 2` through `norm_sub_truncation_le _ f (half_pos hε).le
fun i hi ↦ le_of_lt (not_not.1 fun h ↦ hi (hs (Set.Finite.mem_toFinset.2 h)))`, and `ε / 2 < ε`.""",
 "`Metric.tendsto_atTop`, `Metric.tendsto_nhds`, `Filter.eventually_cofinite`, `Set.Finite.mem_toFinset`, `dist_eq_norm'`, `half_pos`, `half_lt_self`.",
 "[RM] §2.6.3 (\"`π_S ∘ u → u` pointwise along the filter of finite subsets for every bounded `u` into `C₀(I, R)`\"); [Bel] proof of Prop II.1.9 l. 2062–2064 (\"the sequence `(π_S ∘ φ)_{S ⊂ I, S finite}` converges\").",
 "Any normed ring; the `∘ u` form `tendsto_truncation_finset_comp` is already a term.")

cleanup("CLEANUP-7", TR, "T015, T016", "Final cleanup of `Truncation.lean`")

# ---------------- Orthogonal ----------------
ticket("T017", "Orthogonal and `t`-orthogonal families: implications, independence, scaling, reindexing", OR, "T001, CLEANUP-3", "no",         "lemmas", "L17.2–L17.10",
 ["IsOrthonormalFamily.isOrthogonalFamily", "IsOrthogonalFamily.isTOrthogonalFamily", "IsOrthogonalFamily.norm_smul_le_norm_sum", "IsOrthogonalFamily.linearIndependent", "IsTOrthogonalFamily.linearIndependent", "IsOrthogonalFamily.smul", "IsTOrthogonalFamily.smul", "IsOrthonormalFamily.comp_equiv", "IsOrthonormalBasis.comp_equiv"],
 """1. `IsOrthonormalFamily.norm_smul_eq` (`‖a • eᵢ‖ = ‖a‖`) is proved in `Orthonormal.lean` (T001).
2. `isOrthogonalFamily`: `intro s a; rw [he.2 s a]; exact Finset.sup_congr rfl fun i _ ↦ by rw [← NNReal.coe_inj, coe_nnnorm, coe_nnnorm, he.norm_smul_eq]`.
3. `isTOrthogonalFamily`: `intro s a i hi; exact (mul_le_of_le_one_left (norm_nonneg _) ht).trans (he.norm_smul_le_norm_sum s a hi)`.
4. `norm_smul_le_norm_sum`: `exact_mod_cast (he s a).symm ▸ Finset.le_sup (f := fun j ↦ ‖a j • e j‖₊) hi` (as in `Orthonormal.lean`'s `norm_coeff_le_norm_sum`).
5. `IsOrthogonalFamily.linearIndependent`: `linearIndependent_iff'.2 fun s g hg i hi ↦ ?_`; from `he.norm_smul_le_norm_sum s g hi` and
   `hg`, `‖g i • e i‖ ≤ 0`, so `g i • e i = 0` (`norm_le_zero_iff`); `norm_smul` gives `‖g i‖ * ‖e i‖ = 0`, and `norm_ne_zero_iff.2 (h0 i)`
   leaves `‖g i‖ = 0` (`mul_eq_zero`, `norm_eq_zero`).
6. `IsTOrthogonalFamily.linearIndependent`: the same with `t * ‖g i • e i‖ ≤ ‖0‖ = 0` and `ht` (`mul_nonneg`, `le_antisymm`).
7. `IsOrthogonalFamily.smul`: `intro s b; simp_rw [smul_smul]; exact he s fun i ↦ b i * a i`. 8. `IsTOrthogonalFamily.smul`: likewise.
9. `IsOrthonormalFamily.comp_equiv`: `⟨fun j ↦ he.1 (σ j), fun s a ↦ ?_⟩`; `have h := he.2 (s.map σ.toEmbedding) (a ∘ σ.symm)`; rewrite the sum with
   `Finset.sum_map` and the sup with `Finset.sup_map` (`σ.symm_apply_apply`), so that `h` is the goal.
10. `IsOrthonormalBasis.comp_equiv`: `⟨he.1.comp_equiv σ, by rwa [Set.range_comp, σ.surjective.range_eq? ]⟩` — concretely
   `Set.range (e ∘ σ) = Set.range e` by `σ.surjective.range_comp e` (`Function.Surjective.range_comp`).""",
 "`Finset.sum_singleton`, `Finset.sup_singleton`, `Finset.sup_congr`, `Finset.le_sup`, `NNReal.coe_inj`, `coe_nnnorm`, `mul_le_of_le_one_left`, `linearIndependent_iff'`, `norm_le_zero_iff`, `norm_smul`, `norm_ne_zero_iff`, `mul_eq_zero`, `smul_smul`, `Finset.sum_map`, `Finset.sup_map`, `Function.Surjective.range_comp`.",
 "[RM] §2.2.1 (\"orthonormal implies orthogonal implies `t`-orthogonal; an orthogonal family with nonzero members is linearly independent; the scaled family `aᵢ • eᵢ` of an orthogonal family is orthogonal\"); [Sch] Prop 10.4 l. 3080–3083 (\"We obviously can scale the vectors `vₙ` without changing the properties (a) and (b) and hence (c)\"); E21 for the `NormSMulClass` hypothesis.",
 "Any normed ring and normed module; `NormSMulClass R M` only for the two linear-independence lemmas about (`t`-)orthogonal families (E21).")

ticket("T018", "The isometric embedding of the model space given by an orthonormal family", OR, "T017, CLEANUP-3", "no", "lemmas", "L18.1–L18.2",
 ["IsOrthonormalFamily.norm_ofBounded_apply", "IsOrthonormalFamily.linearIsometry_single"],
 """1. `norm_ofBounded_apply`: `le_antisymm`: (≤) `rw [ofBounded_apply]; exact IsUltrametricDist.norm_tsum_le_of_forall_le (norm_nonneg f)
   fun i ↦ by rw [he.norm_smul_eq]; exact norm_apply_le f i`; (≥) `rcases isEmpty_or_nonempty I` — if `I` is empty, `f = 0`
   (`eq_of_empty`) and both sides are `0`; otherwise `obtain ⟨i₀, hi₀⟩ := exists_norm_apply_eq_norm f` and
   `hi₀ ▸ he.norm_coeff_le_of_hasSum (hasSum_ofBounded R e he.exists_bound f) i₀` (the ring form from T001).
2. `linearIsometry_single`: `ofBounded_single R e he.exists_bound i`.""",
 "`IsUltrametricDist.norm_tsum_le_of_forall_le`, `isEmpty_or_nonempty`, `ZeroAtInftyContinuousMap.eq_of_empty`, `exists_norm_apply_eq_norm` (T002), `IsOrthonormalFamily.norm_coeff_le_of_hasSum` (T001), `hasSum_ofBounded`, `ofBounded_single` (T007–T008).",
 "[RM] §2.2.1 (\"for an orthonormal family the map `C₀(I, R) → M`, `a ↦ ∑' aᵢ • eᵢ` is an isometric embedding\"); [Sch] Prop 10.1 l. 2975–2976 (\"A continuity argument now shows that we have `‖f()‖ = ‖‖_∞` for any `` in `c₀(X)`\").",
 "`M` ultrametric and complete (for `ofBounded`), any normed ring `R`.")

ticket("T019", "Expansion coefficients of an orthonormal basis", OR, "T018", "no", "definition + lemmas", "L19.1–L19.6",
 ["IsOrthonormalBasis.exists_hasSum'", "IsOrthonormalBasis.coeff_eq_of_hasSum", "IsOrthonormalBasis.tendsto_coeff", "IsOrthonormalBasis.norm_coeff_le", "IsOrthonormalBasis.norm_eq_iSup_of_hasSum", "IsOrthonormalBasis.coeffCLM"],
 """1. `exists_hasSum'`: `he.exists_hasSum x` (T001's ring form; if T001 kept a field-only `exists_hasSum`, prove it here by the same Cauchy argument).
2. `coeff_eq_of_hasSum`: `he.1.eq_of_hasSum (he.hasSum_coeff x) ha` (check the argument order of `eq_of_hasSum`).
3. `tendsto_coeff`: `he.1.tendsto_cofinite_of_hasSum (he.hasSum_coeff x)`. 4. `norm_coeff_le`: `he.1.norm_coeff_le_of_hasSum (he.hasSum_coeff x) i`.
5. `norm_eq_iSup_of_hasSum`: `le_antisymm (he.1.norm_le_of_hasSum ha (Real.iSup_nonneg fun _ ↦ norm_nonneg _) fun i ↦ le_ciSup ⟨‖x‖, by rintro _ ⟨i, rfl⟩; exact he.1.norm_coeff_le_of_hasSum ha i⟩ i)
   (Real.iSup_le (fun i ↦ he.1.norm_coeff_le_of_hasSum ha i) (norm_nonneg x))`.
6. `coeffCLM`'s `map_add'`: `he.coeff_eq_of_hasSum (by simpa only [add_smul] using (he.hasSum_coeff x).add (he.hasSum_coeff y)) ▸ rfl`-style
   (show `he.coeff (x + y) = he.coeff x + he.coeff y` then `congrFun`); `map_smul'`: `(he.hasSum_coeff x).const_smul r` with `smul_smul`.""",
 "`IsOrthonormalFamily.{eq_of_hasSum, tendsto_cofinite_of_hasSum, norm_coeff_le_of_hasSum, norm_le_of_hasSum}` (T001), `Real.iSup_le`, `le_ciSup`, `Real.iSup_nonneg`, `HasSum.add`, `HasSum.const_smul`, `add_smul`, `smul_smul`.",
 "[RM] §2.2.2 (\"every `x` has a unique expansion `x = ∑' aᵢ • eᵢ` with `a → 0` cofinitely, and then `‖x‖ = sup ‖aᵢ‖` … and the expansion coefficients are continuous linear functionals\"); [Bel] Def II.1.5 l. 2010–2015.",
 "`[CompleteSpace R]` for the existence of expansions (Layer 0's `exists_hasSum` docstring explains why); the coefficient functional has norm at most `1` by `norm_coeff_le`.")

cleanup("CLEANUP-8", OR, "T017, T018, T019", "Three proof tickets landed on `Orthogonal.lean`")

ticket("T020", "The Bellaïche–Colmez characterisation of orthonormal bases", OR, "CLEANUP-8", "no", "lemma", "L20.1",
 ["isOrthonormalBasis_of_forall_hasSum"],
 """`refine ⟨⟨fun i ↦ ?_, fun s a ↦ ?_⟩, ?_⟩`.
1. `‖e i‖ = 1`: apply `h₂ (Pi.single i 1) (e i)` to `HasSum (fun j ↦ Pi.single i (1 : R) j • e j) (e i)`, which is `hasSum_single i`
   after `Pi.single_eq_of_ne`/`zero_smul` off `i` and `Pi.single_eq_same`/`one_smul` at `i`; the right-hand side `⨆ j, ‖Pi.single i 1 j‖` is `1`:
   `le_antisymm (Real.iSup_le (fun j ↦ by by_cases h : j = i <;> simp [h, norm_one]) zero_le_one) (le_ciSup_of_le ⟨1, …⟩ i (by simp [norm_one]))`.
2. The identity: apply `h₂ (fun j ↦ if j ∈ s then a j else 0) (∑ j ∈ s, a j • e j)` to `hasSum_sum_of_ne_finset_zero (fun j hj ↦ by simp [hj])`
   (after `Finset.sum_congr` with `if_pos`); then convert `⨆ j, ‖if j ∈ s then a j else 0‖` to `↑(s.sup fun j ↦ ‖a j‖₊)`: both `≤` by
   `Real.iSup_le`/`Finset.sup_le` and `Finset.le_sup`/`le_ciSup_of_le` (`coe_nnnorm`, `NNReal.coe_le_coe`); finish with `NNReal.coe_inj`.
3. Density: `Metric.dense_iff`/`mem_closure_iff_seq_limit` is not needed: for `x`, `obtain ⟨a, ha⟩ := h₁ x`; `ha` is
   `Tendsto (fun s ↦ ∑ i ∈ s, a i • e i) atTop (𝓝 x)`, and each partial sum lies in the span (`Submodule.sum_mem`, `Submodule.smul_mem`,
   `Submodule.subset_span ⟨i, rfl⟩`), so `mem_closure_of_tendsto ha (Filter.Eventually.of_forall …)`; `Dense` is `∀ x, x ∈ closure _`.""",
 "`hasSum_single`, `hasSum_sum_of_ne_finset_zero`, `Pi.single_eq_same`, `Pi.single_eq_of_ne`, `Real.iSup_le`, `le_ciSup_of_le`, `Finset.sup_le`, `Finset.le_sup`, `coe_nnnorm`, `NNReal.coe_le_coe`, `NNReal.coe_inj`, `mem_closure_of_tendsto`, `Filter.Eventually.of_forall`, `Submodule.sum_mem`, `Submodule.smul_mem`, `Submodule.subset_span`.",
 "[RM] §2.2.2 (\"Prove the equivalent formulations … (Bellaïche's Definition II.1.5, Colmez's Définition 1.1.3)\"); [Bel] Def II.1.5 l. 2010–2015; [Col] Déf 1.1.3 l. 95–112 (\"(i) tout élément `x` de `B` peut s'écrire de manière unique … (ii) `v_B(x) = inf_i v_p(a_i)`\").",
 "`[NormOneClass R]` for `‖e i‖ = ‖1‖ = 1`; the uniqueness of expansions is a consequence of the norm formula, so it is not assumed (plan design).")

cleanup("CLEANUP-9", OR, "T020", "Final cleanup of `Orthogonal.lean`")

# ---------------- ONable ----------------
ticket("T021", "ON-ability: the implications, the model space and its canonical basis", ON, "T020, CLEANUP-5, CLEANUP-7", "no", "lemmas", "L21.1–L21.6",
 ["IsONable.isPotentiallyONable", "IsPotentiallyONable.hasPr", "isONable_zeroAtInfty", "isOrthonormalBasis_single", "LinearIsometryEquiv.isOrthonormalBasis_symm_single", "IsOrthonormalFamily.injective"],
 """1. `IsONable.isPotentiallyONable`: `obtain ⟨I, _, _, ⟨e⟩⟩ := h; exact ⟨I, _, _, ⟨e.toContinuousLinearEquiv⟩⟩`.
2. `IsPotentiallyONable.hasPr`: `obtain ⟨I, _, _, ⟨e⟩⟩ := h; exact ⟨I, _, _, e, e.symm, e.symm_comp_self⟩` (`ContinuousLinearEquiv.symm_comp_self`).
3. `isONable_zeroAtInfty`: `⟨ULift.{u} I, inferInstance, inferInstance, ⟨reindex (R := R) (E := R) Equiv.ulift.symm⟩⟩`.
4. `isOrthonormalBasis_single`: `⟨⟨fun i ↦ by rw [norm_single, norm_one], fun s a ↦ ?_⟩, dense_span_range_single_one⟩`; pointwise
   `(∑ i ∈ s, a i • single i 1) j = if j ∈ s then a j else 0` (`sum_apply`, `smul_single`, `smul_eq_mul`, `mul_one`, `Finset.sum_pi_single'`),
   then the nnnorm identity by `le_antisymm`: `‖∑‖₊ ≤ sup` from `norm_le_of_forall_le` (every coordinate is some `‖a j‖` or `0`, bounded by
   the sup via `Finset.le_sup`), and `‖a j‖₊ ≤ ‖∑‖₊` for `j ∈ s` from `norm_apply_le` at `j` (`NNReal.coe_le_coe`, `coe_nnnorm`).
5. `LinearIsometryEquiv.isOrthonormalBasis_symm_single`: `⟨⟨fun i ↦ by rw [e.symm.norm_map, norm_single, norm_one], fun s a ↦ ?_⟩, ?_⟩`;
   `∑ a i • e.symm (single i 1) = e.symm (∑ a i • single i 1)` (`map_sum`, `map_smul`), `e.symm.nnnorm_map`, then `isOrthonormalBasis_single.1.2`;
   density: `Submodule.span R (Set.range fun i ↦ e.symm (single i 1)) = (Submodule.span R (Set.range fun i ↦ single i 1)).map e.symm.toLinearEquiv`
   (`Submodule.map_span`, `Set.range_comp`) and `DenseRange.dense_image e.symm.surjective.denseRange e.symm.continuous dense_span_range_single_one`.
6. `IsOrthonormalFamily.injective`: `fun i j hij ↦ by_contra fun h ↦ ?_`; with `a k := if k = i then (1 : R) else -1` on `s := {i, j}`:
   `∑ k ∈ {i, j}, a k • e k = e i - e j = 0` (`Finset.sum_pair h`, `one_smul`, `neg_smul`, `hij`, `sub_self`), so by `he.2` the sup
   `{i, j}.sup ‖a k‖₊ = 1` (`Finset.sup_insert`, `Finset.sup_singleton`, `nnnorm_one`, `nnnorm_neg`) equals `‖0‖₊ = 0`, contradicting `one_ne_zero`.""",
 "`LinearIsometryEquiv.toContinuousLinearEquiv`, `ContinuousLinearEquiv.symm_comp_self`, `Equiv.ulift`, `Finset.sum_pi_single'`, `LinearIsometryEquiv.{norm_map, nnnorm_map, surjective, continuous}`, `map_sum`, `map_smul`, `Submodule.map_span`, `Set.range_comp`, `DenseRange.dense_image`, `Function.Surjective.denseRange`, `Finset.sum_pair`, `Finset.sup_insert`, `Finset.sup_singleton`, `nnnorm_one`, `nnnorm_neg`.",
 "[RM] §2.2.3 (\"an isometry `M ≃ₗᵢ C₀(I, R)` corresponds to the basis `i ↦ e⁻¹ (single i 1)` … prove that `C₀(I, R)` is ON-able with the canonical basis\"); [Bel] Ex II.1.7 l. 2017–2021; [Buz07] l. 243–248 (\"to give an ON basis for `M` is to give an isometric isomorphism `M ≅ c_A(I)`\"); [JN] Def 2.1.5 l. 537–541.",
 "`[NormOneClass R]` wherever `‖single i 1‖ = 1` is used; the index universe is handled by `ULift` (plan decision 3).")

ticket("T022", "Stability of the three notions under transport, finite products and `C₀(J, −)`", ON, "T021, CLEANUP-5", "no", "lemmas", "L22.1–L22.9",
 ["IsONable.of_linearIsometryEquiv", "IsPotentiallyONable.of_continuousLinearEquiv", "HasPr.of_continuousLinearEquiv", "IsONable.prod", "IsPotentiallyONable.prod", "HasPr.prod", "IsONable.zeroAtInfty", "IsPotentiallyONable.zeroAtInfty", "HasPr.zeroAtInfty"],
 """1. `of_linearIsometryEquiv`: `obtain ⟨I, _, _, ⟨f⟩⟩ := h; exact ⟨I, _, _, ⟨e.symm.trans f⟩⟩`; `of_continuousLinearEquiv` (potential): the same with `ContinuousLinearEquiv.trans`;
   `HasPr.of_continuousLinearEquiv`: `⟨I, _, _, ι.comp e.symm, e.toContinuousLinearMap.comp π, by ext; simp [h']⟩` where `h' : π.comp ι = id` is used through `congrArg`.
2. `IsONable.prod`: a private `prodCongr (e : M ≃ₗᵢ[R] M') (f : N ≃ₗᵢ[R] N') : M × N ≃ₗᵢ[R] M' × N'` built from `e.toLinearEquiv.prodCongr f.toLinearEquiv`
   with `norm_map'` by `Prod.norm_def` and the two `norm_map`; then `⟨I ⊕ J, _, _, ⟨(prodCongr e f).trans sumEquiv.symm⟩⟩`.
   `IsPotentiallyONable.prod`: `(ContinuousLinearEquiv.prodCongr e f).trans sumEquiv.symm.toContinuousLinearEquiv`.
   `HasPr.prod`: `ι := sumEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (ι₁.prodMap ι₂)`, `π := (π₁.prodMap π₂).comp sumEquiv.toContinuousLinearEquiv.toContinuousLinearMap`;
   `π.comp ι = id` by `ext ⟨x, y⟩ <;> simp [h₁', h₂']`.
3. `IsONable.zeroAtInfty`: `⟨J × I, _, _, ⟨(congrRight e).trans prodEquiv.symm⟩⟩` (index `J × I : Type v`).
   `IsPotentiallyONable.zeroAtInfty`: `(congrRightL e).trans prodEquiv.symm.toContinuousLinearEquiv`.
   `HasPr.zeroAtInfty`: `ι' := prodEquiv.symm… ∘ compL ι`, `π' := compL π ∘ prodEquiv…`; `compL π ∘ compL ι = compL (π ∘ ι) = compL id = id` by `ext; simp [compL_apply, h']`.""",
 "`LinearIsometryEquiv.trans`, `ContinuousLinearEquiv.trans`, `LinearEquiv.prodCongr`, `Prod.norm_def`, `ContinuousLinearEquiv.prodCongr`, `ContinuousLinearMap.prodMap`, `sumEquiv`, `prodEquiv`, `congrRight`, `congrRightL`, `compL` (T010–T012).",
 "[RM] §2.2.3 (\"all three notions are stable under reindexing, finite products, `C₀(J, −)`, and bounded-equivalent norms (potentially ON-able and (Pr) only)\"); [JN] l. 657–659 (\"having property (Pr) is stable when changing the norms on `(R, M)` to equivalent ones\").",
 "Targets stay in universe `v` (plan decision 3); the `C₀(J, −)` statements for the potential notions need `[IsTate R]` (seam S3).")

cleanup("CLEANUP-ALL-1", "project", "T022, CLEANUP-9", "Pre-milestone sweep before M1 (`/cleanup-all` on the board's files)")

ticket("T023", "MILESTONE M1 — orthonormalisable means having an orthonormal basis", ON, "CLEANUP-ALL-1", "no", "milestone", "L23.1–L23.3",
 ["IsOrthonormalBasis.surjective_linearIsometry", "IsOrthonormalBasis.isONable", "Module.isONable_iff_exists_isOrthonormalBasis"],
 """1. `surjective_linearIsometry`: `intro x; obtain ⟨a, ha⟩ := he.exists_hasSum' x`; `refine ⟨ofTendsto a (he.1.tendsto_cofinite_of_hasSum ha), ?_⟩`;
   `rw [linearIsometry_apply]; exact ha.tsum_eq` (`coe_ofTendsto`).
2. `IsOrthonormalBasis.isONable`: `letI : TopologicalSpace (Set.range e) := ⊥; haveI : DiscreteTopology (Set.range e) := discreteTopology_bot _`
   (**the subtype would otherwise inherit the topology of `M`**); `σ := (Equiv.ofInjective e he.1.injective).symm : Set.range e ≃ I`;
   `exact ⟨Set.range e, ⊥, inferInstance, ⟨(he.comp_equiv σ).linearIsometryEquiv.symm⟩⟩`.
3. `isONable_iff_exists_isOrthonormalBasis`: `⟨fun ⟨I, _, _, ⟨Φ⟩⟩ ↦ by classical exact ⟨I, _, Φ.isOrthonormalBasis_symm_single⟩, fun ⟨I, e, he⟩ ↦ he.isONable⟩`.""",
 "`Filter.Tendsto` (T019's `tendsto_coeff` form), `HasSum.tsum_eq`, `discreteTopology_bot`, `Equiv.ofInjective`, `LinearIsometryEquiv.ofSurjective`, `IsOrthonormalBasis.comp_equiv` (T017), `LinearIsometryEquiv.isOrthonormalBasis_symm_single` (T021).",
 "[RM] §2.2.3 (\"`IsONable R M ↔ ∃ (I : Type) (e : I → M), IsOrthonormalBasis e`\"); [Buz07] l. 246–248; [Bel] Ex II.1.7 l. 2021–2024 (\"A Banach `R`-module `M` is orthonormalizable … if and only if it is isometric … to `c_I(R)` for some set `I`\"); [Sch] Prop 10.1 l. 2977–2981 (surjectivity via density).",
 "`[CompleteSpace R]` (expansions), `M` ultrametric complete, `[NormOneClass R]`; the index set of the basis lives in any universe, the theorem's in `v` (decision 3).")

cleanup("CLEANUP-10", ON, "T021, T022, T023", "Three proof tickets landed on `ONable.lean`")

ticket("T024", "Direct summands and (Pr)", ON, "CLEANUP-10", "no", "lemmas", "L24.1–L24.2",
 ["Submodule.ClosedComplemented.hasPr", "Module.HasPr.exists_closedComplemented"],
 """1. `Submodule.ClosedComplemented.hasPr`: `obtain ⟨I, _, _, ⟨e⟩⟩ := hM; obtain ⟨f, hf⟩ := hp` (`f : M →L[R] p`, `∀ x : p, f x = x`);
   `exact ⟨I, _, _, e.toContinuousLinearMap.comp p.subtypeL, f.comp e.symm.toContinuousLinearMap, by ext x; simp [hf]⟩`.
2. `HasPr.exists_closedComplemented`: `obtain ⟨I, _, _, ι, π, h⟩ := h`; `p := LinearMap.range (ι : M →ₗ[R] C₀(I, R))`; the projector
   `(ι.comp π).codRestrict p (fun x ↦ LinearMap.mem_range_self _ _)` fixes `p` pointwise (`rintro ⟨_, m, rfl⟩; exact Subtype.ext (by simp [congrArg (· m) h])`);
   `M ≃L[R] p` by `ContinuousLinearEquiv.equivOfInverse (ι.codRestrict p _) (π.comp p.subtypeL) (fun m ↦ by simp [congrArg (· m) h]) (by rintro ⟨_, m, rfl⟩; exact Subtype.ext (by simp [congrArg (· m) h]))`.""",
 "`Submodule.subtypeL`, `ContinuousLinearMap.codRestrict`, `LinearMap.mem_range_self`, `ContinuousLinearEquiv.equivOfInverse`, `Subtype.ext`.",
 "[RM] §2.2.3 (\"a closed direct summand of a potentially ON-able module has (Pr)\"), convention 4; [Bel] II.1.6 l. 2223–2225 (\"`P` has property (Pr) if there exists a Banach module `Q` such that `P ⊕ Q` is potentially orthonormalizable\"); [JN] l. 543–545.",
 "The retract form of `HasPr` (decision 4) makes both directions one-liners; no completeness needed.")

ticket("T025", "Orthogonal complements and projections for an orthonormal basis (§2.2.5)", ON, "T024", "no", "lemmas", "L25.1–L25.3",
 ["IsOrthonormalBasis.closedComplemented_topologicalClosure_span", "IsOrthonormalBasis.exists_projection", "IsOrthonormalBasis.nonempty_linearIsometryEquiv_prod"],
 """Let `Φ := he.linearIsometryEquiv : C₀(I, R) ≃ₗᵢ[R] M` and `T := truncation S` (classical `DecidablePred`).
0. Key identity: `(Submodule.span R (e '' S)).topologicalClosure = (LinearMap.range (T : C₀(I, R) →ₗ[R] C₀(I, R))).map Φ.toLinearEquiv`.
   (⊇) for `g`, `Φ (T g) = ∑' i, (T g) i • e i` is the limit of partial sums `∑ i ∈ s, (T g) i • e i ∈ span (e '' S)` (only `i ∈ S` contribute),
   so `mem_closure_of_tendsto` (`Submodule.topologicalClosure_coe`); (⊆) `Submodule.topologicalClosure_minimal`: `span (e '' S) ≤ map Φ (range T)`
   since `e i = Φ (single i 1) = Φ (T (single i 1))` for `i ∈ S` (`truncation_single`, `linearIsometryEquiv_single`), and `map Φ (range T)` is closed:
   `range T = ker (id - T)` (`truncation_truncation`) is closed (`ContinuousLinearMap.isClosed_ker`) and `Φ.toHomeomorph.isClosed_image`.
1. `closedComplemented_topologicalClosure_span`: rewrite with the key identity; the projector is `Φ ∘ T ∘ Φ.symm` cod-restricted
   (`ContinuousLinearMap.codRestrict`), fixing the range pointwise by `truncation_truncation`.
2. `exists_projection`: `π := Φ.toContinuousLinearEquiv.toContinuousLinearMap.comp (T.comp Φ.symm.toContinuousLinearEquiv.toContinuousLinearMap)`;
   `‖π x‖ = ‖T (Φ.symm x)‖ ≤ ‖Φ.symm x‖ = ‖x‖` (`norm_truncation_apply_le`, `norm_map`); membership and the fixed points from the key identity.
3. `nonempty_linearIsometryEquiv_prod`: `⟨Φ.symm.trans (setSumComplEquiv S)⟩`.""",
 "`Submodule.topologicalClosure_coe`, `Submodule.topologicalClosure_minimal`, `Submodule.map_span`, `mem_closure_of_tendsto`, `ContinuousLinearMap.isClosed_ker`, `Homeomorph.isClosed_image`, `ContinuousLinearMap.codRestrict`, `truncation_single`, `truncation_truncation`, `norm_truncation_apply_le` (T014), `setSumComplEquiv` (T011).",
 "[RM] §2.2.5 (\"For an orthonormal basis `e` and a subset `S ⊆ I`, the closed span of `e|_S` is a closed direct summand with the projection `π_S` of norm at most `1`, and `M ≅ C₀(S, R) × C₀(I ∖ S, R)`\"); [Bel] l. 2038–2042 (`M_S`, `π_S`).",
 "Everything is transported from the model-space statements of T015 along `Φ`; `[CompleteSpace R]` and `M` Banach because `Φ` needs them.")

ticket("T026", "The lifting property of (Pr)", ON, "T024, CLEANUP-5", "yes (parallel with T025)", "lemmas", "L26.1–L26.4",
 ["ZeroAtInftyContinuousMap.exists_lift", "Module.HasPr.exists_lift", "Module.exists_surjective_zeroAtInfty", "Module.hasPr_of_forall_exists_lift"],
 """1. `ZeroAtInftyContinuousMap.exists_lift`: `obtain ⟨C, hC0, hC⟩ := exists_preimage_norm_le u hu` (Layer 1 OMT, needs `N`, `N'` complete);
   `choose g hg using hC`; `obtain ⟨D, hD⟩ := exists_bound_single v`; `m i := g (v (single i 1))` is bounded by `C * D`
   (`(hg _).2`, `mul_le_mul_of_nonneg_left`); `w := ofBounded R m ⟨C * D, _⟩`; `u.comp w = v` by `ext_single fun i ↦ by rw [comp_apply, ofBounded_single, (hg _).1]`.
2. `HasPr.exists_lift`: `obtain ⟨I, _, _, ι, π, hπι⟩ := hM`; `obtain ⟨w₀, hw₀⟩ := ZeroAtInftyContinuousMap.exists_lift u hu (v.comp π)`;
   `⟨w₀.comp ι, by rw [← comp_assoc, hw₀, comp_assoc, hπι, comp_id]⟩`.
3. `exists_surjective_zeroAtInfty`: `obtain ⟨ϖ⟩ := IsTate.exists_pseudoUniformizer (R := R)`; index `I := {x : M // ‖x‖ ≤ 1}` with
   `letI : TopologicalSpace I := ⊥` and `discreteTopology_bot`; `u := ofBounded R (fun x : I ↦ (x : M)) ⟨1, fun x ↦ x.2⟩`; for `y`:
   if `y = 0` use `0`; else `obtain ⟨n, ⟨-, hn⟩, -⟩ := ϖ.existsUnique_zpow_norm_smul_mem_Ioc_one hy` (`‖(ϖ.unit ^ n : R) • y‖ ≤ 1`),
   `x : I := ⟨(ϖ.unit ^ n : R) • y, hn⟩`, `f := single x ((ϖ.unit ^ (-n) : Rˣ) : R)`; `u f = ((ϖ.unit ^ (-n)) : R) • x` (`smul_single`, `ofBounded_single`, `map_smul`)
   `= y` (`smul_smul`, `← Units.val_mul`, `zpow_neg_add? ` i.e. `ϖ.unit ^ (-n) * ϖ.unit ^ n = 1`, `one_smul`).
4. `hasPr_of_forall_exists_lift`: `obtain ⟨I, _, _, u, hu⟩ := exists_surjective_zeroAtInfty (R := R) (M := M)`;
   `obtain ⟨w, hw⟩ := h C₀(I, R) M u hu (ContinuousLinearMap.id R M)`; `exact ⟨I, _, _, w, u, hw⟩`.""",
 "`ContinuousLinearMap.Ultra.exists_preimage_norm_le` [L1], `exists_bound_single` (T006), `ofBounded_single`, `ext_single`, `ContinuousLinearMap.{comp_assoc, comp_id, id_comp}`, `NormedRing.IsTate.exists_pseudoUniformizer`, `NormedRing.PseudoUniformizer.existsUnique_zpow_norm_smul_mem_Ioc_one` [L0], `zpow_neg`, `Units.val_mul`, `discreteTopology_bot`.",
 "[RM] §2.2.4 (\"A Banach module `P` has property (Pr) if and only if every continuous surjection `M → N` of Banach modules and every continuous map `P → N` admit a continuous lift `P → M` (Bellaïche, Exercise II.1.19)\"); [Bel] Ex II.1.19 l. 2226–2228; [Sch] Prop 10.5 l. 3128–3137 (the lift of the `1_x` with the bound `c⁻¹` and the universal property).",
 "The surjection from a model space uses the unit ball of `M` as index (universe `v`) and the scaling trick (needs `[IsTate R]`); `N : Type (max u v)`, `N' : Type v` in the characterisation (E29).")

cleanup("CLEANUP-11", ON, "T024, T025, T026", "Three proof tickets landed on `ONable.lean`")

ticket("T027", "A finitely generated module with (Pr) is projective (Bellaïche II.1.20)", ON, "CLEANUP-11", "no", "lemma", "L27.1",
 ["Module.HasPr.projective"],
 """`obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M` (a surjective `f : (Fin n → R) →ₗ[R] M`); `fL : (Fin n → R) →L[R] M := ⟨f, continuous_pi f⟩`
(Layer 1 `Pi.lean`); `Fin n → R` is a Banach ultrametric module (`[CompleteSpace R]`, `[IsUltrametricDist R]`, the `Pi` instances);
`obtain ⟨w, hw⟩ := hM.exists_lift fL hf (ContinuousLinearMap.id R M)`; conclude with
`Module.Projective.of_split (w : M →ₗ[R] (Fin n → R)) f (by ext m; exact congrArg (· m) hw)` (`Module.Projective (Fin n → R)` from `Module.Free`).""",
 "`Module.Finite.exists_fin'`, `ContinuousLinearMap.Ultra.continuous_pi` [L1], `Module.Projective.of_split`, `Module.Free.projective` (instance), the `Pi` ultrametric instance (`Mathlib.Topology.MetricSpace.Ultra.Pi`).",
 "[RM] §2.2.4 (\"a finitely generated module with (Pr) is projective (Bellaïche, Proposition II.1.20)\"); [Bel] Prop II.1.20 l. 2229–2235 (\"choose a surjective continuous map `f : A^r → P` and apply Exercise II.1.19 to `α = Id_P`… `P ≃ β(P)` is a direct summand of `A^r`\").",
 "Needs `M` Banach (the lift uses the OMT on `fL`), `R` Banach–Tate and ultrametric (for `Fin n → R` to be an admissible `N`).")

cleanup("CLEANUP-12", ON, "T027", "Final cleanup of `ONable.lean`")
