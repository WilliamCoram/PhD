# ---------------- Dual ----------------
ticket("T043", "The dual of the model space is `ℓ^∞`", DU, "CLEANUP-17", "no", "definition + lemmas", "L43.1–L43.3",
 ["memℓp_infty_apply_single", "dualEquivLp", "dualEquivLp_symm_apply"],
 """1. `memℓp_infty_apply_single`: `obtain ⟨C, hC⟩ := exists_bound_single l; exact memℓp_infty ⟨C, by rintro _ ⟨i, rfl⟩; exact hC i⟩`.
2. `dualEquivLp`: `invFun`'s bound `⟨‖l‖, fun i ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero l i⟩`; `map_add'`: `lp.ext (funext fun i ↦ by simp [add_apply])`;
   `map_smul'`: `lp.ext (funext fun i ↦ by simp [ContinuousLinearMap.smul_apply, smul_eq_mul, lp.coeFn_smul])`; `left_inv l := (eq_ofBounded l).symm`;
   `right_inv l := lp.ext (funext fun i ↦ ofBounded_single _ _ i)`; `norm_map' l`: `‖(l (single i 1))ᵢ‖ = ⨆ i, ‖l (single i 1)‖` (`lp.norm_eq_ciSup`)
   `= ‖ofBounded R (fun i ↦ l (single i 1)) _‖` (`norm_ofBounded`) `= ‖l‖` (`eq_ofBounded`).
3. `dualEquivLp_symm_apply`: `show ofBounded R _ _ f = _; rw [ofBounded_apply]; rfl` (`f i • l i = f i * l i`, `smul_eq_mul`).""",
 "`memℓp_infty`, `lp.norm_apply_le_norm`, `ENNReal.top_ne_zero`, `lp.ext`, `lp.coeFn_smul`, `lp.norm_eq_ciSup`, `exists_bound_single`, `eq_ofBounded`, `ofBounded_single`, `norm_ofBounded` (T006–T008).",
 "[RM] §2.5.1 (\"the continuous dual of `C₀(I, R)` is `ℓ^∞(I, R)` (bounded families, sup norm) isometrically, by the universal property §2.1.3: a functional is determined by its values on the coordinate vectors, and `‖λ‖ = sup ‖λ (single i 1)‖`\"); [Sch] §3 Example l. 617–700 (\"`c₀(X)' = ℓ^∞(X)`\"); [Col] §3 l. 172–176.",
 "`R` commutative (Layer 1's module structure on the dual), Banach–Tate, ultrametric, `NormOneClass`; the scoped operator norm (decision 9).")

ticket("T044", "The pairing with `ℓ^∞` and the evaluation into the bidual", DU, "T043", "no", "lemmas + definition", "L44.1–L44.4",
 ["summable_lp_mul", "norm_tsum_lp_mul_le", "continuous_pairing", "toBidual"],
 """1. `summable_lp_mul`: `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`; `squeeze_zero_norm` with `‖l i * f i‖ ≤ ‖l‖ * ‖f i‖` (`norm_mul_le`,
   `lp.norm_apply_le_norm`) and `(tendsto_cofinite f).norm.const_mul _`.
2. `norm_tsum_lp_mul_le`: `IsUltrametricDist.norm_tsum_le_of_forall_le (mul_nonneg (norm_nonneg l) (norm_nonneg f)) fun i ↦ (norm_mul_le _ _).trans (mul_le_mul (lp.norm_apply_le_norm _ l i) (norm_apply_le f i) (norm_nonneg _) (norm_nonneg _))`.
3. `continuous_pairing`: `continuous_iff_continuousAt.2 fun ⟨l₀, f₀⟩ ↦ Metric.continuousAt_iff.2 fun ε hε ↦ ?_`; write
   `⟨l, f⟩ - ⟨l₀, f₀⟩ = ⟨l - l₀, f⟩ + ⟨l₀, f - f₀⟩` (`tsum_sub`, `tsum_add` of summable families, `sub_mul`, `mul_sub`), bound each by step 2, and use the ultrametric
   inequality; choose `δ := min 1 (ε / (2 * (‖l₀‖ + ‖f₀‖ + 1)))`-type constant (`Prod.dist_eq`, `max_lt_iff`).
4. `toBidual`: inner `map_add'`: `(summable_lp_mul l f).tsum_add (summable_lp_mul l' f)` after `lp.coeFn_add`, `add_mul`; inner `map_smul'`:
   `lp.coeFn_smul`, `smul_eq_mul`, `mul_assoc`, `(summable_lp_mul l f).tsum_const_smul`-type (`tsum_mul_left`); inner bound: `norm_tsum_lp_mul_le` with `mul_comm`;
   outer `map_add'`/`map_smul'`: `ContinuousLinearMap.ext fun l ↦ ?_` with `mul_add`/`mul_left_comm` and `tsum_add`/`tsum_mul_right`;
   `norm_map'`: `le_antisymm (opNorm_le_bound _ (norm_nonneg f) fun l ↦ by rw [mul_comm]; exact norm_tsum_lp_mul_le l f)` and, for `≥`,
   `Real.iSup_le`/`norm_eq_iSup` with `‖f i‖ = ‖toBidual f (lp.single ∞ i 1)‖` (`lp.single_apply`, `tsum_eq_single i`, `one_mul`) `≤ ‖toBidual f‖ * ‖lp.single ∞ i 1‖`
   (`le_opNorm_of_bound`) and `‖lp.single ∞ i 1‖ = 1` (`lp.norm_eq_ciSup`, `lp.single_apply`, `norm_one`, `[NormOneClass R]`).""",
 "`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`, `squeeze_zero_norm`, `norm_mul_le`, `lp.norm_apply_le_norm`, `IsUltrametricDist.norm_tsum_le_of_forall_le`, `continuous_iff_continuousAt`, `Metric.continuousAt_iff`, `Prod.dist_eq`, `tsum_add`, `tsum_sub`, `tsum_mul_left`, `tsum_mul_right`, `lp.coeFn_add`, `lp.coeFn_smul`, `lp.single`, `lp.single_apply`, `tsum_eq_single`, `ContinuousLinearMap.Ultra.{opNorm_le_bound, le_opNorm_of_bound}` [L1].",
 "[RM] §2.5.2 (\"The pairing `ℓ^∞(I, R) × C₀(I, R) → R`, `⟨λ, f⟩ = ∑' λᵢ fᵢ`, is continuous with `‖⟨λ, f⟩‖ ≤ ‖λ‖ ‖f‖`, and the evaluation `C₀ → (C₀)'' = (ℓ^∞)'` is an isometric embedding. ⚠ It is not surjective\"); [Sch] §3 l. 617–700.",
 "`toBidual` needs `[IsTate R]` only because the operator-norm instance on `lp … →L[R] R` does; non-surjectivity (non-reflexivity) is out of scope, as the roadmap says.")

ticket("T045", "Transposes and the dual of an orthonormalisable module", DU, "T044, CLEANUP-12", "no", "lemmas", "L45.1–L45.3",
 ["dualEquivLp_comp_apply", "opNorm_comp_linearIsometryEquiv", "Module.IsONable.exists_dual_linearIsometryEquiv_lp"],
 """1. `dualEquivLp_comp_apply`: LHS `= l (u (single j 1))` (`dualEquivLp_apply`, `comp_apply`); `u (single j 1) = ∑' i, matrixCoeff u i j • single i 1`
   (`hasSum_smul_single_one`), so `l (…) = ∑' i, matrixCoeff u i j * l (single i 1)` (`HasSum.mapL l`, `map_smul`, `smul_eq_mul`, `HasSum.tsum_eq`); finish with `mul_comm`.
2. `opNorm_comp_linearIsometryEquiv`: `le_antisymm (opNorm_le_bound _ (opNorm_nonneg u) fun x ↦ by rw [comp_apply, ← e.norm_map x]; exact le_opNorm u (e x))
   (opNorm_le_bound _ (opNorm_nonneg _) fun y ↦ by have := le_opNorm (u.comp _) (e.symm y); rwa [comp_apply, e.apply_symm_apply, e.symm.norm_map]? …)`
   — the second direction evaluates at `e.symm y` and uses `‖e.symm y‖ = ‖y‖`.
3. `exists_dual_linearIsometryEquiv_lp`: `obtain ⟨I, _, _, ⟨Φ⟩⟩ := h; classical`; the precomposition `(M →L[R] R) ≃ₗᵢ[R] (C₀(I, R) →L[R] R)`:
   `LinearIsometryEquiv.mk` on the `LinearEquiv` with `toFun l := l.comp Φ.symm.toContinuousLinearEquiv.toContinuousLinearMap`, inverse with `Φ`,
   `map_add'`/`map_smul'` by `ext; rfl`, inverses by `ext; simp`, and `norm_map'` from step 2; then `⟨I, _, _, ⟨(this).trans (dualEquivLp R I)⟩⟩`.""",
 "`hasSum_smul_single_one` (T005), `HasSum.mapL`, `HasSum.tsum_eq`, `ContinuousLinearMap.Ultra.{opNorm_le_bound, le_opNorm, opNorm_nonneg}` [L1], `LinearIsometryEquiv.{norm_map, apply_symm_apply}`, `LinearIsometryEquiv.mk`, `LinearIsometryEquiv.trans`.",
 "[RM] §2.5.3 (\"For an orthonormalisable `M` with basis `e`, the dual is identified with bounded families indexed by the basis, and the transpose of `u : M →L[R] N` between orthonormalisable modules has the transposed matrix (§2.6)\"); [Buz07] l. 284–296 (the matrix entries are the coordinates of the images of the basis).",
 "The transpose is precomposition `l ↦ l.comp u` (no separate definition); `opNorm_comp_linearIsometryEquiv` is a Layer-1-style helper placed here because nothing in Layer 1 needs it.")

cleanup("CLEANUP-19", DU, "T043, T044, T045", "Final cleanup of `Dual.lean`")

# ---------------- Closed ----------------
ticket("T046", "Approximation of finitely generated closed submodules (Bellaïche 3.1.12)", CL, "CLEANUP-7, CLEANUP-17", "yes (parallel with the Dual chain)", "lemma", "L46.1",
 ["exists_truncation_near"],
 """`obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hP` (`Submodule.span R (Set.range g) = P`);
`obtain ⟨C, hC0, hC⟩ := NormedRing.exists_forall_exists_eq_sum_smul_norm_le g P hclosed hg` (Layer 1: every `p ∈ P` is `∑ k, a k • g k` with `‖a k‖ ≤ C * ‖p‖`);
for each `k`, `tendsto_truncation_finset (g k)` and `Metric.tendsto_atTop` give `s k : Finset I` with `‖truncation ↑(s k) (g k) - g k‖ ≤ ε / C` for all larger finsets;
`S := Finset.univ.sup s`; by monotonicity (`norm_sub_truncation_le` with `s k ⊆ S`) the same holds for `S`. For `p ∈ P` write `p = ∑ k, a k • g k`;
`truncation ↑S p - p = ∑ k, a k • (truncation ↑S (g k) - g k)` (`map_sum`, `map_smul`, `Finset.sum_sub_distrib`, `smul_sub`), so
`‖truncation ↑S p - p‖ ≤ max_k ‖a k‖ * ‖…‖ ≤ (C * ‖p‖) * (ε / C) = ε * ‖p‖` (`IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `norm_smul_le`, `mul_div_cancel₀`).""",
 "`Submodule.fg_iff_exists_fin_generating_family`, `NormedRing.exists_forall_exists_eq_sum_smul_norm_le` [L1], `tendsto_truncation_finset` (T016), `Metric.tendsto_atTop`, `Finset.sup`, `Finset.le_sup`, `norm_sub_truncation_le` (T014), `map_sum`, `map_smul`, `Finset.sum_sub_distrib`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `norm_smul_le`, `mul_div_cancel₀`.",
 "[Bel] Lemma II.1.8 l. 2043–2056 (\"Since `P` is finite, there exists a surjective continuous morphism `π : A^r → P`. By the open mapping theorem, there is a constant `c > 0` such that for every `p ∈ P`, there exists `m ∈ A^r` such that `π(m) = p` and `|m| ≤ c|p|` … there exists a finite subset `S` of `I` such that `|π_S(π(e_i)) − π(e_i)| ≤ ε/c` … `|π_S(p) − p| ≤ ε|m|/c ≤ ε|p|`\"); [Buz07] Lemma 2.3(c) l. 370–390; [RM] §2.6.4 (\"The proof is the open mapping theorem applied to a surjection `R ^ r → P`, which is why closedness is a hypothesis\").",
 "Closedness is a hypothesis (the counterexample is T055); `R` commutative Banach–Tate ultrametric (Layer 1's OMT corollary).")

cleanup("CLEANUP-ALL-4", "project", "T046, CLEANUP-18", "Pre-milestone sweep before M4")

ticket("T047", "MILESTONE M4 — finitely generated submodules of the model space are closed over a Noetherian ring (Buzzard 2.3)", CL, "CLEANUP-ALL-4", "no", "milestone", "L47.1–L47.2",
 ["exists_truncation_injOn", "isClosed_of_fg"],
 """1. `exists_truncation_injOn`: generators `g : Fin n → C₀(I, R)` of `P`; column vectors `c : I → (Fin n → R)`, `c i k := g k i`; `N := Submodule.span R (Set.range c)`
   is finitely generated (`IsNoetherian.noetherian N`, `Fin n → R` is a Noetherian module over the Noetherian `R`); from `N.FG` and
   `Submodule.mem_span_finite_of_mem_span` (each generator of `N` lies in the span of finitely many `c i`) extract a finite `S : Finset I` with `N = span (c '' S)`
   (`Finset.biUnion`, `Submodule.span_le`, `Submodule.span_mono`). Injectivity on `P`: for `p = ∑ a k • g k`, `q = ∑ b k • g k`
   (`Submodule.mem_span_range_iff_exists_fun`) with `truncation ↑S p = truncation ↑S q`, the linear functional `λ v := ∑ k, (a k - b k) * v k` on `Fin n → R`
   vanishes on `c i` for `i ∈ S` (coordinates of `truncation ↑S (p - q)`), hence on `N` (`Submodule.span_le` into `LinearMap.ker λ`), hence on every `c i`,
   i.e. `(p - q) i = 0` for all `i` (`sum_apply`, `smul_apply`); so `p = q`.
2. `isClosed_of_fg`: with `S` from 1, let `F := LinearMap.range (truncation (R := R) ↑S)` (finite free: `range_truncation_finset`, `Module.Finite.span_of_finite`),
   `Q := P.map (truncation ↑S) ≤ F`; `Q` is closed in `F` by Layer 1's `Submodule.isClosed_of_isNoetherianRing` (on the Banach module `F`, closed in `C₀`), hence closed in
   `C₀(I, R)` and complete; `τ : P →L[R] Q` is a continuous linear bijection (injective by 1, surjective by construction) and its algebraic inverse `ψ : Q →ₗ[R] P`
   is continuous by Layer 1's `continuous_of_finite` (`Q` is finitely generated: a submodule of the Noetherian module `F`; `Q` complete, ultrametric);
   so `P ≃L[R] Q` and `P` is complete (`UniformEquiv.completeSpace_iff` after `AddMonoidHomClass.uniformContinuous_of_continuousAt_zero` both ways), hence closed
   (`completeSpace_coe_iff_isComplete`, `IsComplete.isClosed`). Pattern: [SRC] `05_Noetherian.lean` `isClosed_of_fg`.""",
 "`IsNoetherian.noetherian`, `Submodule.mem_span_finite_of_mem_span`, `Submodule.mem_span_range_iff_exists_fun`, `Submodule.span_le`, `LinearMap.ker`, `range_truncation_finset` (T015), `Module.Finite.span_of_finite`, `Submodule.isClosed_of_isNoetherianRing` [L1], `ContinuousLinearMap.Ultra.continuous_of_finite` [L1], `AddMonoidHomClass.uniformContinuous_of_continuousAt_zero`, `UniformEquiv.completeSpace_iff`, `completeSpace_coe_iff_isComplete`, `IsComplete.isClosed`.",
 "[Buz07] Lemma 2.3(a)–(b) l. 335–369 (\"For `i ∈ I` let `v_i` be the element `(a_{α,i})` of `A^r`. The `A`-submodule of `A^r` generated by the `v_i` is finitely-generated, as `A` is Noetherian, and hence there is a finite set `S ⊆ I` such that this module is generated by `{v_i : i ∈ S}` … (b) … the injection `P → A^S` induces a continuous injection from `P` onto a submodule of `A^S` which is closed by Proposition 3.7.3/1 of [1] … continuous by Lemma 2.2 … and hence the norms on `P` and `Q` are equivalent\"); [Lud] Lemma 2.26 l. 371–395; [RM] §2.6.5 (\"This discharges the hypothesis of clause 4 over Noetherian bases and is the statement §1.4.3 defers to here\").",
 "`[IsNoetherianRing R]` with `R` commutative Banach–Tate ultrametric; the Noetherian hypothesis is used exactly twice (the column module, the closedness in `F`).")

cleanup("CLEANUP-20", CL, "T047", "Final cleanup of `Closed.lean`")

# ---------------- Unitriangular ----------------
ticket("T048", "Surjectivity by successive approximation; the columns of a unitriangular perturbation", UT, "CLEANUP-17, CLEANUP-12", "yes (parallel with Dual/Closed)", "lemmas", "L48.1–L48.2",
 ["surjective_of_forall_exists_approx", "tendsto_column"],
 """1. `surjective_of_forall_exists_approx`: `intro y; choose g hg₁ hg₂ using h`; `q' := max q 0` (`q' < 1`, `0 ≤ q'`); `r n := (fun z ↦ z - u (g z))^[n] y`;
   `‖r n‖ ≤ q' ^ n * ‖y‖` by induction (`Function.iterate_succ_apply'`, `hg₂`, `mul_le_mul_of_nonneg_left`); `x := ∑' n, g (r n)` is summable
   (`Summable.of_norm_bounded _ (summable_geometric_of_lt_one … |>.mul_left (C * ‖y‖))`, `hg₁`); `u x = ∑' n, u (g (r n))` (`ContinuousLinearMap.map_tsum`)
   `= ∑' n, (r n - r (n + 1))` (`Function.iterate_succ_apply'`, `sub_sub_cancel`) `= y - lim r n = y` (`HasSum.tendsto_sum_nat`, `Finset.sum_range_sub'`,
   `tendsto_pow_atTop_nhds_zero_of_lt_one`, `tendsto_nhds_unique`). Pattern: Layer 1 `OpenMapping.lean` l. 136–180.
2. `tendsto_column`: `tendsto_const_nhds.congr' (Filter.eventually_cofinite.2 (ha.column_finite j))`-style (`not_not`).""",
 "`Function.iterate_succ_apply'`, `Summable.of_norm_bounded`, `summable_geometric_of_lt_one`, `ContinuousLinearMap.map_tsum`, `HasSum.tendsto_sum_nat`, `Finset.sum_range_sub'`, `tendsto_pow_atTop_nhds_zero_of_lt_one`, `tendsto_nhds_unique`, `Filter.eventually_cofinite`, `Filter.Tendsto.congr'`.",
 "[RM] §2.7.1 (\"`T` is surjective (successive approximation with contraction factor `q`)\"); [L1] `exists_preimage_norm_le` (the same iteration with factor `1/2`).",
 "The helper is stated over a Tate ring for `u` bounded (`le_opNorm`); `M` complete; no ultrametricity.")

ticket("T049", "A unitriangular perturbation is an isometry (the largest-index argument)", UT, "T048", "no", "lemma", "L49.1",
 ["norm_toCLM_apply"],
 """`le_antisymm`: (≤) `norm_le_of_forall_le (norm_nonneg f) fun i ↦ ?_`: `ha.toCLM f i = ∑' j, a i j * f j` (`toCLM_apply`); `IsUltrametricDist.norm_tsum_le_of_forall_le
(norm_nonneg f) fun j ↦ (norm_mul_le _ _).trans (by simpa using mul_le_mul (ha.norm_le_one i j) (norm_apply_le f j) (norm_nonneg _) zero_le_one)`.
(≥) `by_cases hf : f = 0`; else `F := {j | ‖f j‖ = ‖f‖}` is nonempty (`exists_norm_apply_eq_norm`) and finite (`tendsto_cofinite f`: `‖f j‖ < ‖f‖` cofinitely,
`norm_pos_iff.2 hf`); `j₀ := F.toFinset.max' _`. Then `‖ha.toCLM f j₀‖ = ‖f‖` by Layer 0's `IsUltrametricDist.norm_tsum_eq_of_forall_lt` (summable: T039's
family; the term `j₀`: `‖a j₀ j₀ * f j₀‖ = ‖a j₀ j₀‖ * ‖f j₀‖ = ‖f‖` by `(ha.diag_isMultiplicative j₀).norm_mul` and `ha.norm_diag`; for `j ≠ j₀`:
if `j < j₀` then `‖a j₀ j * f j‖ ≤ q * ‖f j‖ ≤ q * ‖f‖ < ‖f‖` (`ha.norm_lower_le`, `ha.q_lt_one`; if `q ≤ 0` the bound is `≤ 0 < ‖f‖`);
if `j₀ < j` then `j ∉ F` (`Finset.le_max'`), so `‖f j‖ < ‖f‖` and `‖a j₀ j * f j‖ ≤ ‖f j‖ < ‖f‖` (`ha.norm_le_one`)); finally `‖f‖ = ‖ha.toCLM f j₀‖ ≤ ‖ha.toCLM f‖` (`norm_apply_le`).""",
 "`toCLM_apply`, `IsUltrametricDist.norm_tsum_le_of_forall_le`, `IsUltrametricDist.norm_tsum_eq_of_forall_lt` [L0], `exists_norm_apply_eq_norm` (T002), `Finset.max'`, `Finset.le_max'`, `norm_mul_le`, `NormedRing.IsMultiplicative.norm_mul` [L0], `norm_pos_iff`.",
 "[RM] §2.7.1 (\"`T` is an isometry (`‖T f‖ = ‖f‖`, by the largest-index argument: the largest index at which `‖fⱼ‖` is attained contributes a term that no other term can cancel)\").",
 "`R` commutative Banach ultrametric with `‖1‖ = 1`, no Tate hypothesis.")

ticket("T050", "Backward substitution and one step of the successive approximation", UT, "T049", "no", "lemmas", "L50.1–L50.2",
 ["exists_forall_tsum_eq_of_finite", "exists_norm_sub_toCLM_le"],
 """1. `exists_forall_tsum_eq_of_finite`: induction on `N`, the statement quantified over all `g` supported in `{i | i ≤ N}`. The sums are finite
   (`tsum_eq_sum` on `Finset.range (N + 1)` since `f j = 0` for `j > N`). **Base `N = 0`**: `f := single 0 ((ha.diag_isUnit 0).unit⁻¹ * g 0)`:
   row `0` gives `a 0 0 * ((a 0 0)⁻¹ * g 0) = g 0` (`Units.mul_inv_cancel_left`), rows `i > 0` give `0 = g i`; `‖f‖ = ‖g 0‖ ≤ ‖g‖` (`norm_single`,
   `(ha.diag_isMultiplicative 0).inv.norm_mul`, `ha.norm_diag`, `IsMultiplicative.norm_inv`). **Step `N → N + 1`**: `c := (ha.diag_isUnit (N+1)).unit⁻¹ * g (N+1)`,
   `g' := g - (fun i ↦ a i (N+1) * c)` truncated to `≤ N` (`ofTendsto`, `truncation (Set.Iic N)`): supported in `≤ N`, `‖g'‖ ≤ ‖g‖` (ultrametric, `‖a i (N+1) * c‖ ≤ ‖g (N+1)‖`);
   IH gives `f'`; `f := f' + single (N+1) c`; rows `i ≤ N`: `∑_{j ≥ i} a i j f j = (∑_{j ≥ i} a i j f' j) + a i (N+1) c = g' i + a i (N+1) c = g i`;
   row `N + 1`: `a (N+1) (N+1) * c = g (N+1)`; rows `> N + 1`: `0 = g i`; `‖f‖ ≤ max ‖f'‖ ‖c‖ ≤ ‖g‖` (`IsUltrametricDist.norm_add_le_max`).
2. `exists_norm_sub_toCLM_le`: `by_cases hg : g = 0` (take `f := 0`); else `q' := max q 2⁻¹`, `0 < q' < 1`; `tendsto_cofinite g` gives `N` with `‖g i‖ ≤ q' * ‖g‖`
   for `i > N` (`Metric.tendsto_nhds`, `Filter.eventually_cofinite`, `Finset.sup`); `g' := truncation (Set.Iic N) g`, `‖g - g'‖ ≤ q' * ‖g‖` (`norm_sub_truncation_le`);
   apply 1 to `g'` → `f` with `‖f‖ ≤ ‖g'‖ ≤ ‖g‖` and `(D + U) f = g'`; split `ha.toCLM f i = ∑' j, (if i ≤ j then a i j else 0) * f j + ∑' j, (if j < i then a i j else 0) * f j`
   (`tsum_add` of two summable families, each dominated by the summable `‖f j‖`-family; `ite` case split with `not_le`); the lower part has norm
   `≤ q * ‖f‖ ≤ q * ‖g‖` (`IsUltrametricDist.norm_tsum_le_of_forall_le`, `ha.norm_lower_le`; if `q < 0` it is `0`); hence
   `‖g - ha.toCLM f‖ = ‖(g - g') - L f‖ ≤ max (q' * ‖g‖) (q * ‖g‖) ≤ q' * ‖g‖` (`IsUltrametricDist.norm_sub_le_max`, `le_max_left`).""",
 "`tsum_eq_sum`, `Units.mul_inv_cancel_left`, `IsUnit.unit`, `NormedRing.IsMultiplicative.{inv, norm_inv, norm_mul}` [L0], `norm_single`, `single` (T004), `truncation`, `norm_sub_truncation_le` (T014), `IsUltrametricDist.{norm_add_le_max, norm_sub_le_max, norm_tsum_le_of_forall_le}`, `tsum_add`, `Summable.of_norm_bounded`, `Metric.tendsto_nhds`, `Filter.eventually_cofinite`.",
 "[RM] §2.7.1 (\"`T` is surjective (successive approximation with contraction factor `q`)\"); the exact solution of the upper unitriangular part on a finite truncation is the roadmap's \"finitely supported columns\" hypothesis at work; [SRC] `06_Unitriangular.lean` `exists_approx_single`/`exists_approx` (the field version).",
 "The contraction factor is `max q 2⁻¹` (not `q`) because the truncation error must be a fixed fraction `< 1` of `‖g‖` even when `q = 0`; no Tate hypothesis.")

cleanup("CLEANUP-21", UT, "T048, T049, T050", "Three proof tickets landed on `Unitriangular.lean`")
cleanup("CLEANUP-ALL-5", "project", "CLEANUP-21, CLEANUP-19, CLEANUP-20", "Pre-milestone sweep before M5")

ticket("T051", "MILESTONE M5 — the unitriangular-perturbation criterion", UT, "CLEANUP-ALL-5", "no", "milestone", "L51.1–L51.3",
 ["surjective_toCLM", "exists_linearIsometryEquiv", "IsOrthonormalBasis.of_isUnitriangularPerturbation"],
 """1. `surjective_toCLM`: `ContinuousLinearMap.Ultra.surjective_of_forall_exists_approx ha.toCLM (q := max q 2⁻¹) (C := 1) (max_lt ha.q_lt_one (by norm_num))
   fun g ↦ by obtain ⟨f, hf, hfg⟩ := ha.exists_norm_sub_toCLM_le g; exact ⟨f, by rwa [one_mul], hfg⟩`.
2. `exists_linearIsometryEquiv`: `⟨ha.linearIsometryEquiv, fun i j ↦ ?_⟩`; the coerced map is `ha.toCLM` (`ContinuousLinearMap.ext fun _ ↦ rfl`), then `ha.matrixCoeff_toCLM i j`.
3. `IsOrthonormalBasis.of_isUnitriangularPerturbation`: `Φ := he.linearIsometryEquiv`, `T := ha.linearIsometryEquiv`, `Ψ := T.trans Φ`; for each `j`,
   `Ψ (single j 1) = Φ (ofTendsto (fun i ↦ a i j) _)` (the column: `coe_linearIsometryEquiv`, `toCLM`, `ofBounded_single`) `= ∑' i, a i j • e i = f j`
   (`linearIsometryEquiv_apply`, `(hf j).tsum_eq`); so `f = fun j ↦ Ψ.symm.symm (single j 1)` and `Ψ.symm.isOrthonormalBasis_symm_single` (T021) applies after `funext`.""",
 "`ContinuousLinearMap.Ultra.surjective_of_forall_exists_approx` (T048), `exists_norm_sub_toCLM_le` (T050), `matrixCoeff_toCLM`, `LinearIsometryEquiv.trans`, `LinearIsometryEquiv.isOrthonormalBasis_symm_single` (T021), `IsOrthonormalBasis.linearIsometryEquiv_apply` (T023), `ofBounded_single`, `HasSum.tsum_eq`.",
 "[RM] §2.7.1–2.7.2 (\"hence an isometric automorphism … if `e : ℕ → M` is a family in an orthonormalisable Banach module whose matrix in an orthonormal basis, after a reindexing by a bijection of `ℕ`, is a unitriangular perturbation, then `e` is an orthonormal basis. This is the form in which Amice's theorem (§4.4) is proved\"); §2.7.3 (relation to [Col] Prop 1.1.5: no residue field needed).",
 "`[IsTate R]` enters only through the successive-approximation helper (bounded `u`); the family criterion takes the expansions `hf` as hypotheses, so no coordinate functionals are needed (plan design).")

cleanup("CLEANUP-22", UT, "T051", "Final cleanup of `Unitriangular.lean`")

# ---------------- Examples ----------------
ticket("T052", "Examples: `C(ℤ_p, ℚ_p)` is orthonormalisable; the dual of `C₀(ℕ, ℚ_p)`; nonzero ON-able modules have unit vectors", EX, "CLEANUP-16, CLEANUP-19, CLEANUP-20, CLEANUP-22", "no", "lemmas", "L52.1–L52.3",
 ["isONable_continuousMap_padic", "nonempty_dual_linearIsometryEquiv_lp_padic", "_root_.Module.not_isONable_of_forall_norm_ne_one"],
 """1. `isONable_continuousMap_padic`: `haveI := Padic.isRankOneDiscrete_valuation (p := p)`; `(Module.isONable_iff_forall_exists_norm_eq C(ℤ_[p], ℚ_[p])).2 fun g ↦ ?_`;
   `obtain ⟨x, -, hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty (continuous_norm.comp g.continuous).continuousOn`; `‖g‖ = ‖g x‖` by
   `le_antisymm ((ContinuousMap.norm_le g (norm_nonneg _)).2 fun y ↦ hx (Set.mem_univ y)) (g.norm_coe_le_norm x)`; `⟨g x, …⟩`.
2. `nonempty_dual_linearIsometryEquiv_lp_padic`: `⟨{ (dualEquivLp ℚ_[p] ℕ).toLinearEquiv with norm_map' := fun l ↦ (dualEquivLp ℚ_[p] ℕ).norm_map l }⟩` — the Ultra norm
   and Mathlib's norm on `C₀(ℕ, ℚ_[p]) →L[ℚ_[p]] ℚ_[p]` are the same function (Layer 1 `norm_eq_opNorm`, `rfl`), only the instances differ; if the elaborator
   rejects the `with`, build `LinearIsometryEquiv.mk` on the `LinearEquiv` with `norm_map'` by `show` + `rfl`-conversion.
3. `not_isONable_of_forall_norm_ne_one`: `rintro ⟨I, _, _, ⟨Φ⟩⟩`; `Nontrivial C₀(I, R)` from `Φ.symm.injective`/`Φ.surjective` and `Nontrivial M`; hence `Nonempty I`
   (an empty `I` makes `C₀(I, R)` a subsingleton, `eq_of_empty`); pick `i`, then `h (Φ.symm (single i 1))` contradicts `‖Φ.symm (single i 1)‖ = ‖single i 1‖ = ‖1‖ = 1`.""",
 "`Padic.isRankOneDiscrete_valuation` [NP], `Module.isONable_iff_forall_exists_norm_eq` (T032), `isCompact_univ`, `IsCompact.exists_isMaxOn`, `ContinuousMap.norm_le`, `ContinuousMap.norm_coe_le_norm`, `dualEquivLp` (T043), `ContinuousLinearMap.Ultra.norm_eq_opNorm` [L1], `ZeroAtInftyContinuousMap.eq_of_empty`, `norm_single`, `norm_one`.",
 "[RM] Layer 2 Examples (\"`C₀(ℕ, ℚ_p)` with its canonical basis and its dual `ℓ^∞(ℕ, ℚ_p)`; the Banach space `C(ℤ_p, ℚ_p)` is orthonormalisable (Layer 3 exhibits the basis, this layer only knows it from Serre's theorem)\"); [Sch] Remark 10.2.",
 "E28 for the dual example; `[NormOneClass R]` in the general lemma (`‖single i 1‖ = ‖1‖`).")

ticket("T053", "Examples: the doubled norm — potentially but not literally orthonormalisable", EX, "T052", "no", "instances + lemmas", "L53.1–L53.7",
 ["instance : NormedAddCommGroup (Doubled K)", "instance : IsBoundedSMul K (Doubled K)", "instance [IsUltrametricDist K] : IsUltrametricDist (Doubled K)", "instance [CompleteSpace K] : CompleteSpace (Doubled K)", "isPotentiallyONable", "not_isONable", "not_isONable_doubled_padic"],
 """1. The `AddGroupNorm` fields: `map_zero'` by `simp`; `add_le'`: `2 * ‖x + y‖ ≤ 2 * ‖x‖ + 2 * ‖y‖` (`norm_add_le`, `mul_add`, `mul_le_mul_of_nonneg_left`);
   `neg'`: `norm_neg`; `eq_zero_of_map_eq_zero'`: `mul_eq_zero`, `norm_eq_zero` (`two_ne_zero`).
2. `IsBoundedSMul`: `.of_norm_smul_le fun c x ↦ le_of_eq (by rw [norm_def, norm_def, norm_smul]; ring)` (the action is `K` on itself).
3. `IsUltrametricDist`: `⟨fun x y z ↦ by simp only [dist_eq_norm, norm_def, ← mul_max_of_nonneg _ _ zero_le_two]; exact mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_sub_le_max? …) zero_le_two⟩`
   (use `IsUltrametricDist.dist_triangle_max` on `K` after rewriting `dist` as `2 * dist`).
4. `CompleteSpace`: Layer 0's `AddEquiv.completeSpace_congr_of_bounds` (`Module.lean` l. 80) applied to `toDoubled.toAddEquiv` with the bounds `‖toDoubled x‖ ≤ 2 * ‖x‖`
   and `‖x‖ ≤ 1 * ‖toDoubled x‖`-style (check its exact statement).
5. `isPotentiallyONable`: `IsONable K C₀(Unit, K)` (`isONable_zeroAtInfty`) transported along `(LinearIsometryEquiv.funUnique Unit K K).symm.trans piEquiv.symm`-type
   isometry `K ≃ₗᵢ[K] C₀(Unit, K)` (built in the proof), then `.isPotentiallyONable.of_continuousLinearEquiv` with the `≃L` given by `toDoubled` and the two bounds
   (`AddMonoidHomClass.continuous_of_bound`).
6. `not_isONable`: `Module.not_isONable_of_forall_norm_ne_one fun x hx ↦ hK (toDoubled.symm x) (by rw [norm_def] at hx; linarith? )` — from `2 * ‖y‖ = 1` get `‖y‖ = 2⁻¹`
   (`eq_inv_of_mul_eq_one_right`), contradiction.
7. `not_isONable_doubled_padic`: `NormedField.Doubled.not_isONable fun x hx ↦ ?_`; `x ≠ 0` (`norm_zero`, `inv_ne_zero`); `Padic.norm_eq_zpow_neg_valuation hx0` gives
   `(p : ℝ) ^ (-v) = 2⁻¹`, i.e. `(p : ℝ) ^ v = 2` (`zpow_neg`, `inv_inj`); with `3 ≤ p` (`hp.1.two_le`, `hp'`, `omega`): if `v ≤ 0` then `p ^ v ≤ 1 < 2`
   (`zpow_le_one_of_nonpos₀`), if `0 < v` then `3 ≤ p ≤ p ^ v` (`le_self_zpow`); `linarith`.""",
 "`AddGroupNorm.toNormedAddCommGroup`, `norm_add_le`, `norm_neg`, `norm_eq_zero`, `IsBoundedSMul.of_norm_smul_le`, `norm_smul`, `mul_max_of_nonneg`, `IsUltrametricDist.dist_triangle_max`, `AddEquiv.completeSpace_congr_of_bounds` [L0], `isONable_zeroAtInfty` (T021), `LinearIsometryEquiv.funUnique`, `piEquiv` (T011), `AddMonoidHomClass.continuous_of_bound`, `Padic.norm_eq_zpow_neg_valuation`, `zpow_neg`, `Nat.Prime.two_le`, `zpow_le_one_of_nonpos₀`, `le_self_zpow`.",
 "[RM] §2.3.5 (\"for odd `p`, `ℂ_p` itself with the norm `2‖·‖` has no orthonormal basis, since `‖ℂ_p‖ = p^ℚ` does not contain `1/2`; the potential statement is §2.4\") and Layer 2 Examples (\"`ℂ_p` with the norm `2‖·‖` (`p` odd) is potentially but not literally orthonormalisable; a finite-dimensional `ℂ_p`-space with a norm whose values are not in `p^ℚ`\"); E23.",
 "The `ℂ_p` instances are terms already (`not_isONable_doubled_padicComplex` takes the value-group fact as a hypothesis, E23); the `ℚ_p` instance is proved outright.")

ticket("T054", "Examples: the shift and the two unitriangular perturbations", EX, "T052", "yes (parallel with T053)", "definition + lemmas", "L54.1–L54.4",
 ["shift", "matrixCoeff_shift", "isUnitriangularPerturbation_one_add", "isUnitriangularPerturbation_padicInt"],
 """1. `shift`: tendsto `(tendsto_cofinite f).comp Nat.succ_injective.tendsto_cofinite`; `map_add'`/`map_smul'`: `ext; rfl`; the bound `1`:
   `norm_le_of_forall_le (by simp) fun n ↦ by rw [one_mul]; exact norm_apply_le f (n + 1)`.
2. `matrixCoeff_shift`: `simp [matrixCoeff, shift_apply, coe_single, Pi.single_apply, eq_comm]`.
3. `isUnitriangularPerturbation_one_add`: `hlower i i (lt_irrefl _)` gives `N i i = 0`; fields: `q_lt_one := hq`; `norm_le_one`: `by_cases i = j` (`‖1 + 0‖ = 1`;
   `‖0 + N i j‖ ≤ q ≤ 1` by `hq.le`); `diag_isUnit`: `isUnit_one` after simplification; `diag_isMultiplicative`: `IsMultiplicative.one`; `norm_diag`: `norm_one`;
   `norm_lower_le`: `‖0 + N i j‖ ≤ q` (`if_neg (ne_of_gt h)`); `column_finite`: `(Set.finite_singleton j ∪ hfin j).subset` (`Set.Finite.union`, case analysis).
4. `isUnitriangularPerturbation_padicInt`: `norm_le_one := fun i j ↦ PadicInt.norm_le_one _`; `diag_isUnit := hdiag`; `diag_isMultiplicative := fun i ↦ isMultiplicative_of_normMulClass _`
   (or `fun i x ↦ PadicInt.norm_mul _ _`); `norm_diag := fun i ↦ PadicInt.isUnit_iff.1 (hdiag i)`; `norm_lower_le := fun i j h ↦ by simpa using (PadicInt.norm_le_pow_iff_dvd _ 1).2 (by simpa using hlow i j h)`;
   `column_finite := hfin`; `q_lt_one`: `inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.1.one_lt)`.""",
 "`Nat.succ_injective`, `Function.Injective.tendsto_cofinite`, `Pi.single_apply`, `isUnit_one`, `NormedRing.IsMultiplicative.one` [L0], `Set.finite_singleton`, `Set.Finite.union`, `Set.Finite.subset`, `PadicInt.norm_le_one`, `PadicInt.isUnit_iff`, `PadicInt.norm_le_pow_iff_dvd`, `NormedRing.isMultiplicative_of_normMulClass` [L0], `inv_lt_one_of_one_lt₀`, `Nat.Prime.one_lt`.",
 "[RM] Layer 2 Examples (\"the matrix of the shift on `C₀(ℕ, R)`; the unitriangular perturbation `1 + N` with `N` strictly lower triangular of norm `q`, and a matrix with entries in `ℤ_p`, unit diagonal, and lower entries in `pℤ_p`\").",
 "The `ℤ_p` example has level `p⁻¹`, the sharpest possible (`‖p‖ = p⁻¹`).")

cleanup("CLEANUP-23", EX, "T052, T053, T054", "Three proof tickets landed on `Examples.lean`")

ticket("T055", "Example: the counterexample to §2.6.4 without closedness", EX, "CLEANUP-23", "no", "instance + definition + lemmas", "L55.1–L55.4",
 ["instance : IsTate (lp (fun _ : ℕ ↦ ℚ_[p]) ∞)", "geomDelta", "not_isClosed_span_geomDelta", "exists_truncation_far_geomDelta"],
 """1. `IsTate`: the constant sequence `(p : lp …)` (`Nat.cast`) is a unit with inverse the constant `p⁻¹` (`memℓp_infty` bounded; `Units.mkOfMulEqOne`, `lp.ext`,
   `lp.infty_coeFn_mul`, `mul_inv_cancel₀`); multiplicative: `(p : lp …) * x = (p : ℚ_[p]) • x` (`lp.ext`, `lp.infty_coeFn_mul`, `lp.coeFn_smul`), so
   `‖p * x‖ = ‖(p : ℚ_[p])‖ * ‖x‖` (`lp.norm_const_smul ENNReal.top_ne_zero`) and `‖(p : lp …)‖ = ‖(p : ℚ_[p])‖` (`lp.norm_eq_ciSup`, `ciSup_const`);
   `‖(p : ℚ_[p])‖ = p⁻¹ < 1` (`Padic.norm_p`, `inv_lt_one_of_one_lt₀`).
2. `geomDelta`'s tendsto: `‖(p : ℚ_[p]) ^ n • lp.single ∞ n 1‖ = ‖p‖ ^ n` (`lp.norm_const_smul`, `norm_pow`, `‖lp.single ∞ n 1‖ = 1` via `lp.norm_eq_ciSup` and
   `lp.single_apply`), `tendsto_pow_atTop_nhds_zero_of_lt_one`, `Nat.cofinite_eq_atTop`.
3. `not_isClosed_span_geomDelta`: `g := ofTendsto (fun n ↦ (p : ℚ_[p]) ^ ((n + 1) / 2) • lp.single ∞ n 1) _` (same tendsto). (a) `g ∈ closure (span {geomDelta p})`:
   `truncation (Set.Iic k) g = rₖ • geomDelta p` with `rₖ := ∑ n ∈ Finset.range (k + 1), (p : ℚ_[p]) ^ (((n + 1) / 2 : ℕ) - n : ℤ) • lp.single ∞ n 1 ∈ lp …`
   (`lp.ext`, coordinates: `lp.single_apply`, `δₙ * δₙ = δₙ`, `zpow_add₀`), in the span (`Submodule.smul_mem`, `Submodule.mem_span_singleton_self`), and
   `truncation (Set.Iic k) g → g` (`tendsto_truncation_finset` along `Finset.range (k+1)`, or `norm_sub_truncation_le` directly); `mem_closure_of_tendsto`.
   (b) `g ∉ span {geomDelta p}`: `Submodule.mem_span_singleton` gives `r` with `r • geomDelta p = g`; comparing coordinates at `n` and evaluating at `n`
   (`lp.coeFn_smul`, `lp.infty_coeFn_mul`, `lp.single_apply`): `r n * p ^ n = p ^ ((n + 1) / 2)`, so `‖r n‖ = p ^ (n - (n + 1) / 2)` (`Padic.norm_p`, `norm_pow`,
   `norm_zpow`), unbounded in `n` (take `n := 2 m`, `‖r n‖ = p ^ m`), contradicting `‖r n‖ ≤ ‖r‖` (`lp.norm_apply_le_norm`) with `p ^ m → ∞`
   (`tendsto_pow_atTop_atTop_of_one_lt`); hence `IsClosed` fails (`IsClosed.closure_eq`, `Submodule.topologicalClosure_coe`).
4. `exists_truncation_far_geomDelta`: `m := S.sup id + 1`, `m ∉ S` (`Finset.le_sup (f := id)`, `Nat.lt_irrefl`); `f := lp.single ∞ m 1 • geomDelta p`
   (`Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)`); `f n = if n = m then (p : ℚ_[p]) ^ m • lp.single ∞ m 1 else 0` (`lp.single_apply`, `mul_ite`);
   `‖f‖ = ‖(p : ℚ_[p])‖ ^ m` (`exists_norm_apply_eq_norm`/`norm_single`-style computation) `> 0`; `truncation ↑S f = 0` (`ext n`, `truncation_apply`: `n ∈ S ⟹ n ≠ m`);
   so `‖truncation ↑S f - f‖ = ‖f‖ > 2⁻¹ * ‖f‖` (`norm_neg`, `half_lt_self`).""",
 "`memℓp_infty`, `Units.mkOfMulEqOne`, `lp.ext`, `lp.infty_coeFn_mul`, `lp.coeFn_smul`, `lp.norm_const_smul`, `lp.norm_eq_ciSup`, `lp.single`, `lp.single_apply`, `lp.norm_apply_le_norm`, `ciSup_const`, `Padic.norm_p`, `inv_lt_one_of_one_lt₀`, `norm_pow`, `norm_zpow`, `tendsto_pow_atTop_nhds_zero_of_lt_one`, `tendsto_pow_atTop_atTop_of_one_lt`, `Nat.cofinite_eq_atTop`, `Submodule.mem_span_singleton`, `Submodule.mem_span_singleton_self`, `mem_closure_of_tendsto`, `Submodule.topologicalClosure_coe`, `lp.instIsUltrametricDist` [L1], `truncation_apply`, `norm_sub_truncation_le` (T014).",
 "[RM] §2.6.4 (\"⚠ Without closedness the statement is false; record the counterexample\"); Layer 1 Examples (`ℓ^∞(ℕ, ℚ_p)` as the non-Noetherian Banach–Tate ring, E18); the construction is the plan's (R = `ℓ^∞(ℕ, ℚ_p)`, `v(n) = pⁿ δₙ`, `P = R·v`).",
 "The ring `lp (fun _ : ℕ ↦ ℚ_[p]) ∞` has `NormedCommRing`, `NormOneClass`, `CompleteSpace` (Mathlib) and `IsUltrametricDist` (Layer 1); the `IsTate` instance is new.")

cleanup("CLEANUP-24", EX, "T055", "Final cleanup of `Examples.lean`")

ticket("T056", "Integration: chain root, full build, axioms, linter, README check", "project", "CLEANUP-24, CLEANUP-14, CLEANUP-16", "no", "integration", "L56.1–L56.4",
 [],
 """1. Add `import PhD.TauCeti.Code.PadicFunctionalAnalysis.ModelSpace.Examples` to `PhD/TauCeti.lean` (alphabetically before `…PadicFunctionalAnalysis.NormComparison`).
2. `lake build PhD.TauCeti` (the whole chain, including the RAG dependents of T001); zero errors, no `sorry` warnings in the fourteen Layer 2 files.
3. `python3 .mathlib-quality/tauceti-pfa-layer2/scratch/axioms.py` adapted to the fourteen modules (every declaration: only `propext`, `Classical.choice`, `Quot.sound`);
   `lake exe runLinter PhD.TauCeti.Code.PadicFunctionalAnalysis.<Module>` for each module; fix findings inline.
4. The README errata (E19–E24, E27) were applied at plan review on 2026-10-06; check that the Lean names mentioned there still match the code
   (`Module.IsONable`, `IsTOrthogonalFamily`, `ZeroAtInftyContinuousMap.*`) and fix the prose if a name changed during execution.""",
 "none (tooling).",
 "[RM] Layer 2; plan.md errata table.",
 "The chain-separation rule and the one-Lean-process rule apply; commit only when the user asks.")

cleanup("CLEANUP-FINAL", "project", "T056", "Final `/cleanup-all` of the Layer 2 files")
