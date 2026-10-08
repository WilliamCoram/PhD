# ---------------- Serre ----------------
ticket("T028", "Reductions of orthonormal bases are bases (Bellaïche II.1.12, 'only if')", SE, "CLEANUP-12", "no", "lemmas", "L28.1–L28.2",
 ["linearIndependent_residueFamily_of_isOrthonormalFamily", "span_residueFamily_eq_top_of_isOrthonormalBasis"],
 """1. `linearIndependent_residueFamily_of_isOrthonormalFamily`: `linearIndependent_iff'.2 fun s g hg i hi ↦ ?_`. Lift `g j` to `a j : unitClosedBall R`
   (`Ideal.Quotient.mk_surjective`, `choose`); then `∑ j ∈ s, g j • residueFamily … j = Submodule.Quotient.mk (∑ j ∈ s, a j • ⟨e j, _⟩)`
   (`Submodule.Quotient.mk_sum`, `Submodule.Quotient.mk_smul`, `residueFamily`), so `hg` says `∑ j ∈ s, a j • ⟨e j, _⟩ ∈ ϖ.ideal • ⊤`
   (`Submodule.Quotient.mk_eq_zero`), i.e. `‖∑ j ∈ s, (a j : R) • e j‖ < 1` by `ϖ.mem_ideal_smul_top_iff_norm_lt_one hM`. By the orthonormal identity
   this sup is `≥ ‖(a i : R)‖`, so `‖(a i : R)‖ < 1`, i.e. `a i ∈ openUnitBallIdeal R = ϖ.ideal` (`mem_openUnitBallIdeal`, `ϖ.ideal_eq_openUnitBallIdeal hR`),
   hence `g i = Ideal.Quotient.mk _ (a i) = 0` (`Ideal.Quotient.eq_zero_iff_mem`).
2. `span_residueFamily_eq_top_of_isOrthonormalBasis`: `eq_top_iff.2 fun x _ ↦ ?_`; `obtain ⟨⟨m, hm⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x`;
   expand `m = ∑' a i • e i` (`he.exists_hasSum'`) with `‖a i‖ ≤ ‖m‖ ≤ 1`; `F := {i | ‖a i‖ = 1}` is finite (`he.1.tendsto_cofinite_of_hasSum`,
   eventually `‖a i‖ < 1`); with `s := F.toFinset`, the tail `m - ∑ i ∈ s, a i • e i = ∑' i, (if i ∈ s then 0 else a i) • e i` has every term of norm
   `≤ ‖ϖ‖` (for `i ∉ s`, `‖a i‖ < 1` and `hR` give `‖a i‖ ≤ ‖ϖ‖`: a power `‖ϖ‖ ^ n < 1` forces `n ≥ 1`), hence norm `≤ ‖ϖ‖ < 1`
   (`IsUltrametricDist.norm_tsum_le_of_forall_le`, `ϖ.norm_lt_one`), so the tail lies in `ϖ.ideal • ⊤` and `mk ⟨m, hm⟩ = ∑ i ∈ s, mk (a i) • residueFamily … i`
   (`Submodule.Quotient.eq`), an element of the span (`Submodule.sum_mem`, `Submodule.smul_mem`, `Submodule.subset_span ⟨i, rfl⟩`).""",
 "`linearIndependent_iff'`, `Ideal.Quotient.mk_surjective`, `Submodule.Quotient.{mk_sum, mk_smul, mk_eq_zero, eq, mk_surjective}`, `NormedRing.PseudoUniformizer.{mem_ideal_smul_top_iff_norm_lt_one, ideal_eq_openUnitBallIdeal}` [L0], `NormedRing.mem_openUnitBallIdeal`, `Ideal.Quotient.eq_zero_iff_mem`, `IsUltrametricDist.norm_tsum_le_of_forall_le`, `zpow_lt_one_iff_right_of_lt_one₀`-type lemma for `‖ϖ‖ ^ n < 1 → 1 ≤ n`.",
 "[Bel] Lemma II.1.12 l. 2082–2105 (\"Then `(e_i)` is an orthonormal basis of `M` if and only if `(ẽ_i)` is a basis of `M̃` … The other direction is easy and left to the reader\"); [Col] Prop 1.1.5, second half of the proof l. 158–171 (\"la réduction `ā_i` modulo `π_L` de `a_i` est nulle sauf pour un nombre fini de `i` … les `ē_i` forment une famille génératrice … et donc une base\"); [RM] §2.3.1 (\"the 'only if' direction is the reduction of the sup-norm identity\").",
 "Hypotheses `hR`, `hM` as in Layer 0 (Bellaïche's II.1.11 and `|M| ⊂ |R|`); `R` a Banach–Tate commutative ring with the `ResidueModule` instances.")

ticket("T029", "A family with linearly independent reduction is orthonormal (II.1.12, 'if', the norm identity)", SE, "T028", "no", "lemma", "L29.1",
 ["isOrthonormalFamily_of_linearIndependent_residueFamily"],
 """Prove first `key : ∀ (s : Finset I) (a : I → R), ‖∑ i ∈ s, a i • e i‖₊ = s.sup fun i ↦ ‖a i‖₊`, then `‖e i‖ = 1` is `key {i} 1` with `norm_one`.
For `key`: if `∀ i ∈ s, a i = 0` both sides are `0`. Otherwise pick `i₀ ∈ s` maximising `‖a i‖` (`Finset.exists_max_image`), `a i₀ ≠ 0`, and by `hR`
`‖a i₀‖ = ‖ϖ‖ ^ n`. Scale: `b j := ((ϖ.unit ^ (-n) : Rˣ) : R) * a j`, so `‖b j‖ = ‖ϖ‖ ^ (-n) * ‖a j‖ ≤ 1` with equality at `i₀`
(`IsMultiplicative.norm_mul`, `norm_zpow` for `ϖ.unit`). Let `x := ∑ j ∈ s, b j • e j`; `‖x‖ ≤ 1` (`IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `norm_smul_le`, `he j`).
Its reduction `mk ⟨x, _⟩ = ∑ j ∈ s, mk (b j) • residueFamily … j` is nonzero: `mk (b i₀) ≠ 0` because `b i₀ ∉ ϖ.ideal` (`ϖ.mem_ideal_iff`: `‖b i₀‖ = 1 > ‖ϖ‖`)
and `hli` (`linearIndependent_iff'`). Hence `x ∉ ϖ.ideal • ⊤`, so `¬ ‖x‖ < 1` (`mem_ideal_smul_top_iff_norm_lt_one hM`), so `‖x‖ = 1`. Finally
`∑ a j • e j = (ϖ.unit ^ n : R) • x` (`smul_sum`, `mul_smul`, `Units.inv_mul_cancel_left`-type cancellation) has norm `‖ϖ‖ ^ n * 1 = ‖a i₀‖`
(`ϖ.norm_zpow_smul`), which is the sup (`Finset.sup` attained at `i₀`, `Finset.le_sup`/`Finset.sup_le` with the maximality). Convert with `coe_nnnorm`.""",
 "`Finset.exists_max_image`, `NormedRing.IsMultiplicative.norm_mul` [L0], `NormedRing.PseudoUniformizer.{norm_zpow, norm_zpow_smul, mem_ideal_iff, mem_ideal_smul_top_iff_norm_lt_one}` [L0], `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `linearIndependent_iff'`, `Submodule.Quotient.{mk_sum, mk_smul, mk_eq_zero}`, `Finset.smul_sum`, `smul_smul`, `Finset.le_sup`, `Finset.sup_le`.",
 "[Bel] Lemma II.1.12 l. 2095–2101 (\"If `|m| = 1`, then some `a¹_i` has norm `1`, and so does `a_i`, and thus `|m| = sup_i |a_i|`. By replacing `m` by `πⁿ m` for the `n` such that `|m| = |π|^{-n}`, we see that the same result holds for any `m ∈ M`\"); [Sch] Prop 10.1 l. 2963–2974 (\"We may assume without loss of generality that `a₁ ≠ 0` and that `|a₁| ≥ |a_i|` … the vector `v_{x₁} + (a₂/a₁) v_{x₂} + … lies in `B₁(0)` but not in `B₁⁻(0)`. Hence `‖a₁ v_{x₁} + … + a_m v_{x_m}‖ = |a₁|`\"); [Col] l. 150–157.",
 "Scaling by the unit `ϖ.unit ^ (-n)` replaces Schneider's division by `a₁` (not available over a ring); `hR` provides `n`.")

ticket("T030", "Successive `ϖ`-adic approximation and the lifting of residue bases (II.1.12, 'if')", SE, "T029", "no", "lemmas", "L30.1–L30.2",
 ["exists_hasSum_of_span_residueFamily_eq_top", "isOrthonormalBasis_of_residueFamily"],
 """1. **One step** (private lemma): `∀ m : M, ‖m‖ ≤ 1 → ∃ (s : Finset I) (a : I → R), (∀ i, ‖a i‖ ≤ 1) ∧ (∀ i ∉ s, a i = 0) ∧ ‖m - ∑ i ∈ s, a i • e i‖ ≤ ‖ϖ‖`:
   `mk ⟨m, _⟩ ∈ span (range (residueFamily …)) = ⊤` gives (`Finsupp.mem_span_range_iff_exists_finsupp`) a finitely supported `c` with
   `c.sum (fun i α ↦ α • residueFamily … i) = mk ⟨m, _⟩`; lift each `c i` to `a i : unitClosedBall R` (`Ideal.Quotient.mk_surjective`, `0` off the support);
   then `m - ∑ (a i : R) • e i ∈ ϖ.ideal • ⊤` (`Submodule.Quotient.eq`, `mk_sum`, `mk_smul`), i.e. its norm is `< 1` (`mem_ideal_smul_top_iff_norm_lt_one hM`),
   hence `≤ ‖ϖ‖` (`hM`: a value `‖ϖ‖ ^ n < 1` has `n ≥ 1`).
2. **Iterate**: `m₀ := m` (first scale `m` into the unit ball with `existsUnique_zpow_norm_smul_mem_Ioc_one` and undo at the end, as Bellaïche does),
   `mₙ₊₁ := ((ϖ.unit⁻¹ : Rˣ) : R) • (mₙ - ∑ i ∈ sₙ, aₙ i • e i)` with `‖mₙ₊₁‖ ≤ 1` (`ϖ.norm_smul`, `ϖ.norm_inv`); by induction
   `m - ∑ i ∈ ⋃ₖ<ₙ sₖ, (∑ k < n, (ϖ.unit ^ k : R) * aₖ i) • e i = (ϖ.unit ^ n : R) • mₙ`, of norm `≤ ‖ϖ‖ ^ n`.
3. **Limit coefficients**: `A i := ∑' k, (ϖ.unit ^ k : R) * aₖ i`, summable in `R` (`‖(ϖ ^ k) * aₖ i‖ ≤ ‖ϖ‖ ^ k`, `summable_geometric_of_lt_one`,
   `Summable.of_norm_bounded`), with `‖A i - ∑ k < n, …‖ ≤ ‖ϖ‖ ^ n` (ultrametric tail bound). `A → 0` cofinitely: given `ε`, choose `K` with `‖ϖ‖ ^ K < ε`;
   outside the finite union of the supports `s₀ ∪ … ∪ s_{K-1}`, `‖A i‖ ≤ ‖ϖ‖ ^ K` (`IsUltrametricDist.norm_tsum_le_of_forall_le`).
4. **The sum**: `(fun i ↦ A i • e i)` is summable (`summable_smul_of_bounded`-type, `‖e i‖ ≤ 1`), and `‖m - ∑' A i • e i‖ ≤ ‖ϖ‖ ^ n` for every `n`
   (write the difference as `(ϖ ^ n) • mₙ + ∑' (Aₙ i - A i) • e i` with the tail bound), hence `= 0` (`tendsto_pow_atTop_nhds_zero_of_lt_one`).
5. `isOrthonormalBasis_of_residueFamily`: `⟨ϖ.isOrthonormalFamily_of_linearIndependent_residueFamily hR hM he hli, ?_⟩`; density from
   `exists_hasSum_of_span_residueFamily_eq_top` exactly as in T020 step 3 (`mem_closure_of_tendsto`).
Pattern: [SRC] `07_Residue.lean` `exists_expansion_of_residue_approx` (field case, same induction).""",
 "`Finsupp.mem_span_range_iff_exists_finsupp`, `Ideal.Quotient.mk_surjective`, `Submodule.Quotient.{eq, mk_sum, mk_smul}`, `NormedRing.PseudoUniformizer.{mem_ideal_smul_top_iff_norm_lt_one, norm_smul, norm_inv, norm_zpow_smul, existsUnique_zpow_norm_smul_mem_Ioc_one}` [L0], `summable_geometric_of_lt_one`, `Summable.of_norm_bounded`, `IsUltrametricDist.norm_tsum_le_of_forall_le`, `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`, `tendsto_pow_atTop_nhds_zero_of_lt_one`, `mem_closure_of_tendsto`.",
 "[Bel] Lemma II.1.12 l. 2088–2095 (\"Choosing lifts `a¹_i` of the `α_i` in `R⁰`, we have `m − ∑ a¹_i e_i = π m₁` with `m₁ ∈ M⁰`. Applying the same result to `m₁` … by induction `m − ∑ aⁿ_i e_i = πⁿ mₙ` … the sequence `(aⁿ_i)` satisfies `|aⁿ_i − aⁿ⁺¹_i| ≤ |π|ⁿ`, hence is Cauchy, and therefore converges to an element `a_i ∈ R⁰` … One has `m = ∑ a_i e_i`\"); [Col] Prop 1.1.5 l. 136–149 (the same recursion `x_{n+1} = π⁻¹(x_n − s(x_n))`); [RM] §2.3.1.",
 "Over a Banach–Tate commutative ring with `hR`, `hM`; the coefficients converge because `R` is complete. The longest ticket of the board: split sub-tickets per A2 (the one-step lemma, the iteration, the limit) when executing.")

cleanup("CLEANUP-13", SE, "T028, T029, T030", "Three proof tickets landed on `Serre.lean`")

ticket("T031", "Serre's theorem, ring form", SE, "CLEANUP-13", "no", "lemmas", "L31.1–L31.4",
 ["free_residueModule_of_isONable", "isONable_of_free_residueModule", "isPotentiallyONable_of_forall_free", "isPotentiallyONable_of_isField_residueRing"],
 """1. `free_residueModule_of_isONable`: `obtain ⟨I, _, _, ⟨Φ⟩⟩ := h`; classical; `he := Φ.isOrthonormalBasis_symm_single` (T021);
   `Module.Free.of_basis (Module.Basis.mk (ϖ.linearIndependent_residueFamily_of_isOrthonormalFamily hR hM he.1) (by rw [ϖ.span_residueFamily_eq_top_of_isOrthonormalBasis hR hM he]))`.
2. `isONable_of_free_residueModule`: `b := Module.Free.chooseBasis ϖ.ResidueRing (ϖ.ResidueModule M)` (index `Module.Free.ChooseBasisIndex … : Type v`);
   `choose e he using fun i ↦ Submodule.Quotient.mk_surjective _ (b i)` gives `e i : Submodule.unitClosedBall R M`; set `e' i := (e i : M)`, `‖e' i‖ ≤ 1`
   (`Submodule.mem_unitClosedBall`); `residueFamily ϖ e' _ = b` by `funext` (`he`); so `b.linearIndependent` and `b.span_eq` give the hypotheses of
   `isOrthonormalBasis_of_residueFamily`, and `IsOrthonormalBasis.isONable` (T023) concludes.
3. `isPotentiallyONable_of_forall_free`: `haveI := ϖ.isBoundedSMul_rescaled M hR`; `hM' : ∀ m : ϖ.Rescaled M, m ≠ 0 → ∃ n, ‖m‖ = ‖ϖ‖ ^ n := fun m hm ↦ ϖ.exists_norm_rescaled_eq_zpow hm`;
   `haveI := hfree (ϖ.ResidueModule (ϖ.Rescaled M))`; `h₁ : IsONable R (ϖ.Rescaled M) := ϖ.isONable_of_free_residueModule hR hM'`; the identity
   `ϖ.toRescaled M : M ≃ₗ[R] ϖ.Rescaled M` is a `≃L`: continuity from the bounds `‖m‖ ≤ ‖toRescaled m‖` (`norm_le_norm_toRescaled`) and
   `‖toRescaled m‖ ≤ ‖ϖ‖⁻¹ * ‖m‖` (from `norm_mul_norm_toRescaled_lt`, `ϖ.norm_pos`), via `AddMonoidHomClass.continuous_of_bound`; build
   `{ toLinearEquiv := ϖ.toRescaled M, continuous_toFun := _, continuous_invFun := _ }` and finish with `h₁.isPotentiallyONable.of_continuousLinearEquiv e.symm`.
4. `isPotentiallyONable_of_isField_residueRing`: `ϖ.isPotentiallyONable_of_forall_free hR fun N _ _ ↦ by letI := hF.toField; exact Module.Free.of_divisionRing _ _`.""",
 "`Module.Free.of_basis`, `Module.Basis.mk`, `Module.Free.chooseBasis`, `Module.Basis.{linearIndependent, span_eq}`, `Submodule.Quotient.mk_surjective`, `NormedRing.PseudoUniformizer.{isBoundedSMul_rescaled, exists_norm_rescaled_eq_zpow, toRescaled, norm_le_norm_toRescaled, norm_mul_norm_toRescaled_lt, norm_pos}` [L0], `AddMonoidHomClass.continuous_of_bound`, `IsField.toField`, `Module.Free.of_divisionRing`.",
 "[RM] §2.3.2 (\"`M` is orthonormalisable if and only if `M̃` is a free `R̃`-module; and every Banach `R`-module is potentially orthonormalisable as soon as `R̃` has the property that all its modules are free — in particular when `R̃` is a field\"); [Bel] Lemma II.1.12 l. 2086–2087 (\"In particular, `M` is orthonormalizable if and only if `M̃` is free over `R̃`\") and Thm II.1.13 l. 2108–2114 (the equivalent norm `|m|' = inf_{r ∈ p^ℤ, r ≥ |m|} r`); [RM] §0.3.3 (the rescaled norm).",
 "The rescaled module needs `hR` for its `IsBoundedSMul` (Layer 0); `hM` is only needed for the on-the-nose statements.")

cleanup("CLEANUP-ALL-2", "project", "T031, CLEANUP-12", "Pre-milestone sweep before M2")

ticket("T032", "MILESTONE M2 — Serre's theorem over a discretely valued field", SE, "CLEANUP-ALL-2", "no", "milestone", "L32.1–L32.4",
 ["NormedField.exists_pseudoUniformizer_forall_exists_norm_eq_zpow", "NormedRing.PseudoUniformizer.isField_residueRing", "Module.isPotentiallyONable_of_isRankOneDiscrete", "Module.isONable_iff_forall_exists_norm_eq"],
 """1. `exists_pseudoUniformizer_forall_exists_norm_eq_zpow`: `v := NormedField.valuation (K := K)` with `v x = ‖x‖₊` (`NormedField.valuation_apply`);
   `obtain ⟨π, hπ⟩ := Valuation.IsRankOneDiscrete.generator_mem_range K v` (`‖π‖₊ = generator v`), `π ≠ 0` (`generator_ne_zero`), `‖π‖ < 1`
   (`generator_lt_one`); `ϖ := ⟨Units.mk0 π hπ0, NormedRing.isMultiplicative_of_normMulClass _, by simpa using hlt⟩`; for `r ≠ 0`,
   [NP] `Valuation.IsRankOneDiscrete.exists_zpow_generator_eq (v := v) (by simpa)` gives `n` with `‖r‖₊ = generator v ^ n = ‖π‖₊ ^ n`, and
   `NNReal.coe_zpow`/`coe_nnnorm` turn it into `‖r‖ = ‖π‖ ^ n`.
2. `isField_residueRing`: `ϖ.ideal = openUnitBallIdeal K` (`ϖ.ideal_eq_openUnitBallIdeal hK`) `= IsLocalRing.maximalIdeal _` (`NormedRing.maximalIdeal_unitClosedBall`),
   which is maximal (`IsLocalRing.maximalIdeal.isMaximal`); `(Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1` after rewriting.
3. `isPotentiallyONable_of_isRankOneDiscrete`: `obtain ⟨ϖ, hK⟩ := NormedField.exists_pseudoUniformizer_forall_exists_norm_eq_zpow K`;
   `exact ϖ.isPotentiallyONable_of_isField_residueRing hK (ϖ.isField_residueRing hK)`.
4. `isONable_iff_forall_exists_norm_eq`: (⟹) `obtain ⟨I, _, _, ⟨Φ⟩⟩`; `‖m‖ = ‖Φ m‖`; `rcases isEmpty_or_nonempty I` — empty: `Φ m = 0`, take `k := 0`;
   nonempty: `obtain ⟨i, hi⟩ := exists_norm_apply_eq_norm (Φ m)`, take `k := Φ m i`. (⟸) with `ϖ, hK` as in 3, `hM : ∀ m ≠ 0, ∃ n, ‖m‖ = ‖ϖ‖ ^ n`
   from `h m` and `hK` (`k ≠ 0` since `‖m‖ ≠ 0`); `letI := (ϖ.isField_residueRing hK).toField; haveI := Module.Free.of_divisionRing ϖ.ResidueRing (ϖ.ResidueModule M)`;
   `ϖ.isONable_of_free_residueModule hK hM`.""",
 "`NormedField.valuation_apply`, `Valuation.IsRankOneDiscrete.{generator_mem_range, generator_lt_one, generator_ne_zero}`, `Valuation.IsRankOneDiscrete.exists_zpow_generator_eq` [NP], `NormedRing.isMultiplicative_of_normMulClass` [L0], `Units.mk0`, `NNReal.coe_zpow`, `NormedRing.PseudoUniformizer.ideal_eq_openUnitBallIdeal` [L0], `NormedRing.maximalIdeal_unitClosedBall` [L0], `IsLocalRing.maximalIdeal.isMaximal`, `Ideal.Quotient.maximal_ideal_iff_isField_quotient`, `IsField.toField`, `Module.Free.of_divisionRing`, `exists_norm_apply_eq_norm` (T002).",
 "[RM] §2.3.3 (\"Every Banach space over a discretely valued nonarchimedean field `K` is potentially orthonormalisable, and it is orthonormalisable on the nose if and only if its norm takes values in `‖K‖`\"); [Sch] Prop 10.1 l. 2948–2951 and its proof l. 2952–2960 (\"According to Lemma 1.4 we have `|K×| = r^ℤ` … `k := o/m` denote the residue class field\"), Remark 10.2 l. 3003–3006; [Sch] Lemma 1.4 l. 291–312; [Bel] Thm II.1.13 l. 2108–2114; convention 8 (`IsRankOneDiscrete`).",
 "`[Valuation.IsRankOneDiscrete (NormedField.valuation (K := K))]` is the roadmap's convention 8; the uniformiser comes from Mathlib's generator plus [NP]'s `exists_zpow_generator_eq` (seam S2).")

ticket("T033", "The index set of `C₀(I, K)` is an invariant (Schneider, Lemma 10.3)", SE, "T032", "no", "lemmas", "L33.1–L33.3",
 ["finite_of_continuousLinearEquiv", "cardinal_mk_le_of_continuousLinearEquiv", "nonempty_equiv_of_continuousLinearEquiv"],
 """1. `finite_of_continuousLinearEquiv`: `Fintype.ofFinite I`; `FiniteDimensional K C₀(I, K)` from `(piEquiv (R := K)).toLinearEquiv.symm` and
   `Module.Finite.of_surjective`/`LinearEquiv.finiteDimensional`; transport along `e.toLinearEquiv`; the family `fun j ↦ single j (1 : K)` is linearly
   independent (`isOrthonormalBasis_single.1.linearIndependent`), hence `Finite J` (`LinearIndependent.finite` / `Module.Finite.finite_of_linearIndependent`).
2. `cardinal_mk_le_of_continuousLinearEquiv`: show `Set.univ ⊆ ⋃ i : I, {j | e (single i 1) j ≠ 0}`: for `j`, if `e (single i 1) j = 0` for all `i`, then
   for every `f`, `(e f) j = 0` — write `e f = ∑' i, f i • e (single i 1)` (`hasSum_smul_apply_single (e : C₀(I, K) →L[K] C₀(J, K)) f`, map by `evalCLM K j`)
   — contradicting surjectivity at `single j 1`. Then `Cardinal.mk J = #(univ) ≤ #(⋃ …) ≤ Cardinal.sum fun i ↦ #(supp i)` (`Cardinal.mk_iUnion_le_sum_mk`)
   `≤ #I * ℵ₀` (`Cardinal.sum_le_iSup`-type bound with `#(supp i) ≤ ℵ₀` from `countable_support` and `Cardinal.mk_le_aleph0`) `= #I`
   (`Cardinal.mul_eq_left (Cardinal.aleph0_le_mk I) le_rfl? ` with `ℵ₀ ≤ #I` from `Infinite I` and `ℵ₀ ≠ 0`).
3. `nonempty_equiv_of_continuousLinearEquiv`: `rcases finite_or_infinite I`. Finite: `haveI := finite_of_continuousLinearEquiv e`, `Fintype` both; the finranks
   agree (`LinearEquiv.finrank_eq e.toLinearEquiv`, `Module.finrank_pi` through `piEquiv`), so `Fintype.card I = Fintype.card J` and `Fintype.equivOfCardEq`.
   Infinite: `Infinite J` (otherwise the finite case for `e.symm` makes `I` finite); `le_antisymm (cardinal_mk_le_of_continuousLinearEquiv e.symm) (cardinal_mk_le_of_continuousLinearEquiv e)`
   and `Cardinal.eq.1`.""",
 "`Fintype.ofFinite`, `LinearEquiv.finiteDimensional`, `LinearIndependent.finite` (or `Module.Finite.finite_of_linearIndependent`), `hasSum_smul_apply_single` (T006), `Cardinal.{mk_iUnion_le_sum_mk, sum_le_iSup, mk_le_aleph0, mul_eq_left, aleph0_le_mk, eq}`, `countable_support` (T002), `finite_or_infinite`, `LinearEquiv.finrank_eq`, `Module.finrank_pi`, `Fintype.equivOfCardEq`.",
 "[Sch] Lemma 10.3 l. 3007–3028 (\"If one of the sets is finite then already for algebraic reasons the other set has to be finite of the same cardinality … The sets `Y_x := {y ∈ Y : f(1_x)(y) ≠ 0}` … each `Y_x` is finite or countable … for any `y ∈ Y` there is an `x ∈ X` such that `y ∈ Y_x`. If not all the `f(1_x)` would be contained in the complete and hence closed vector subspace `c₀(Y∖{y})` … It follows that `|Y| ≤ |⋃ Y_x| ≤ |ℕ| · |X| = |X|`\"); [RM] §2.3.4.",
 "Over any complete nonarchimedean nontrivially normed `K` (Schneider assumes no discreteness here); `I`, `J` in one universe for `Cardinal.mk`.")

cleanup("CLEANUP-14", SE, "T033", "Final cleanup of `Serre.lean`")

# ---------------- CountableType ----------------
ticket("T034", "The distance step of Schneider's Proposition 10.4", CT, "CLEANUP-14", "no", "lemmas", "L34.1–L34.2",
 ["Submodule.exists_add_mem_forall_mul_norm_le", "norm_smul_add_ge_mul_max"],
 """1. `exists_add_mem_forall_mul_norm_le`: `d := Metric.infDist w (U : Set V)`; `0 < d` by `(hU.notMem_iff_infDist_pos ⟨0, U.zero_mem⟩).1 hw`.
   If `r ≤ 0`: `⟨0, U.zero_mem, fun u hu ↦ (mul_nonpos_of_nonpos_of_nonneg? …).trans (norm_nonneg _)⟩`. If `0 < r`: `d < d / r` (`hr`, `lt_div_iff₀`),
   so `Metric.infDist_lt_iff ⟨0, U.zero_mem⟩` gives `y ∈ U` with `dist w y < d / r`; take `u₀ := -y` (`U.neg_mem`); for `u ∈ U`:
   `‖w + u₀ + u‖ = dist w (y - u)` (`dist_eq_norm`, `sub_eq_add_neg`) `≥ d` (`Metric.infDist_le_dist_of_mem (U.sub_mem hy hu)`), while
   `r * ‖w + u₀‖ = r * dist w y < d` (`dist_eq_norm`, `mul_lt_of_lt_div`). Combine.
2. `norm_smul_add_ge_mul_max`: `by_cases ha : a = 0`: then `‖0 + u‖ = ‖u‖` and `r * max 0 ‖u‖ = r * ‖u‖ ≤ ‖u‖` (`mul_le_of_le_one_left`).
   Otherwise `‖a • v + u‖ = ‖a‖ * ‖v + a⁻¹ • u‖` (`smul_add`, `smul_smul`, `norm_smul`, `inv_mul_cancel₀`) `≥ ‖a‖ * (r * ‖v‖) = r * ‖a • v‖`
   (`hv _ (U.smul_mem _ hu)`); if `‖a • v‖ ≠ ‖u‖` then `‖a • v + u‖ = max ‖a • v‖ ‖u‖` (`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`) and
   `r * max ≤ max` (`mul_le_of_le_one_left`); if equal, `max = ‖a • v‖` and the previous bound applies.""",
 "`Metric.infDist`, `IsClosed.notMem_iff_infDist_pos`, `Metric.infDist_lt_iff`, `Metric.infDist_le_dist_of_mem`, `lt_div_iff₀`, `mul_lt_of_lt_div`, `dist_eq_norm`, `Submodule.{neg_mem, sub_mem, smul_mem, zero_mem}`, `norm_smul`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, `mul_le_of_le_one_left`.",
 "[Sch] Prop 10.4 proof l. 3047–3056 (\"Fixing some `v ∈ Vₙ ∖ Vₙ₋₁` we therefore have `inf{‖v + w‖ : w ∈ Vₙ₋₁} > 0`. There consequently exists a vector `w' ∈ Vₙ₋₁` such that `rₙ/rₙ₊₁ ≤ inf{‖v + w‖ : w ∈ Vₙ₋₁}/‖v + w'‖ ≤ 1`\") and l. 3057–3068 (\"`‖a vₙ + w‖ ≥ (rₙ/rₙ₊₁) max(‖a vₙ‖, ‖w‖)` … If `‖a vₙ‖ = ‖w‖` this is a consequence of the previous inequality; if `‖a vₙ‖ ≠ ‖w‖` this follows from `‖a vₙ + w‖ = max(‖a vₙ‖, ‖w‖)`\").",
 "Field scalars (division by `a`), `V` ultrametric; closedness of `U` as an explicit hypothesis (it will be a finite-dimensional subspace).")

ticket("T035", "The `t`-orthogonal sequence (Schneider 10.4 (a)–(d)) and the finite-dimensional case", CT, "T034", "no", "lemmas", "L35.1–L35.2",
 ["Module.IsCountableType.exists_isTOrthogonalFamily_nat", "Module.exists_isTOrthogonalFamily_fin_of_finiteDimensional"],
 """1. **A linearly independent enumeration.** `obtain ⟨s, hs, hd⟩ := hV`; `obtain ⟨b, hbs, hb, hli⟩ := exists_linearIndependent K s` (`b ⊆ s`, `span b = span s`,
   `LinearIndependent K ((↑) : b → V)`); `b` is countable (`hs.mono hbs`) and infinite (if finite, `span b` is finite-dimensional, closed
   (`Submodule.closed_of_finiteDimensional`) and dense, so `= ⊤` and `FiniteDimensional K V`, contradicting `hfin`); so `Nonempty (Denumerable b)`
   (`Set.countable_infinite_iff_nonempty_denumerable`) and `u : ℕ → V := fun n ↦ ((Denumerable.eqv b).symm n : V)` is injective with range `b`,
   `LinearIndependent K u` (`hli.comp _ (Equiv.injective _)`).
2. **The chain.** `Vₙ := Submodule.span K (u '' Set.Iio n)`; finite-dimensional hence closed; `u n ∉ Vₙ` (`LinearIndependent.notMem_span_image`, `Nontrivial K`).
3. **The sequence.** `rₖ := 1 - (1 - t) / (k + 1)` (`r₀ = t`, increasing, `< 1`), `ρₖ := rₖ / rₖ₊₁ ∈ (0, 1)`; `vₙ := u n + u₀ n` where `u₀ n ∈ Vₙ` is
   given by `Submodule.exists_add_mem_forall_mul_norm_le Vₙ _ (hu n) (ρₙ < 1)` (no recursion: `Vₙ` depends on `u`, not on earlier `v`'s).
   (a) `span (v '' Iio n) = Vₙ` by induction (`Submodule.span_insert`-style, each `v k ∈ u k + V_k`), and `v n ∉ Vₙ`.
   (b') `∀ a x, x ∈ Vₙ → ρₙ * max ‖a • vₙ‖ ‖x‖ ≤ ‖a • vₙ + x‖` (T034.2).
4. **(c) by induction on `n`:** `‖∑ i ≤ n, aᵢ • vᵢ‖ ≥ max_{i ≤ n} (rᵢ / rₙ₊₁) ‖aᵢ • vᵢ‖`: split off the top term, apply (b') with `x = ∑ i < n …` (in `Vₙ`),
   use the induction hypothesis and `ρₙ * (rᵢ / rₙ) = rᵢ / rₙ₊₁`. Since `rᵢ / rₙ₊₁ ≥ r₀ = t`, this is `IsTOrthogonalFamily K t v` (for a `Finset`
   `s`, extend `a` by `0` outside `s` and take `n := s.sup id`).
5. **(d) scaling.** `obtain ⟨ϖ⟩ := IsTate.exists_pseudoUniformizer (R := K)`; for each `n`, `existsUnique_zpow_norm_smul_mem_Ioc_one` gives `cₙ := ϖ.unit ^ mₙ`
   with `‖cₙ • vₙ‖ ∈ Ioc ‖ϖ‖ 1`; `v' n := cₙ • vₙ`: `t`-orthogonal (`IsTOrthogonalFamily.smul`), `‖v' n‖ ≤ 1`, `δ := ‖ϖ‖ > 0` bounds below, and
   `span (range v') = span (range v) = span (range u) = span b = span s` is dense (`Submodule.span_smul_eq`-type: scaling by units does not change spans).
6. `exists_isTOrthogonalFamily_fin_of_finiteDimensional`: the same construction with `u := FiniteDimensional.finBasis K V` (or `Module.Basis.ofVectorSpace`
   re-indexed by `Fin n`), steps 2–5 for `n < finrank`, and `span (range v) = ⊤` from (a).""",
 "`exists_linearIndependent`, `Set.Countable.mono`, `Submodule.closed_of_finiteDimensional`, `Set.countable_infinite_iff_nonempty_denumerable`, `Denumerable.eqv`, `LinearIndependent.comp`, `LinearIndependent.notMem_span_image`, `Submodule.span_insert`, `Finset.sup`, `NormedRing.IsTate.exists_pseudoUniformizer`, `NormedRing.PseudoUniformizer.existsUnique_zpow_norm_smul_mem_Ioc_one` [L0], `IsTOrthogonalFamily.smul` (T017), `FiniteDimensional.finBasis`, `Dense.mono`.",
 "[Sch] Prop 10.4 proof l. 3033–3083 (\"Choose an ascending sequence of vector subspaces `{0} = V₀ ⊆ V₁ ⊆ … ` … `dim_K Vₙ = n` … `⋃ Vₙ` is dense in `V`. In addition we fix an increasing sequence of real numbers `0 < r = r₁ < r₂ < … < rₙ < … < 1`. We want to inductively construct a sequence of vectors `(vₙ)` … (a) `{v₁, …, vₙ}` is a `K`-basis of `Vₙ` … (b) `‖vₙ + w‖ ≥ (rₙ/rₙ₊₁)‖vₙ‖` … We inductively deduce … (c) `‖∑ aᵢvᵢ‖ ≥ r · max(‖a₁v₁‖, …, ‖aₙvₙ‖)` … We therefore may assume that `ε ≤ ‖vₙ‖ ≤ 1` … (d) `‖∑ aᵢvᵢ‖ ≥ r · max(|a₁|, …, |aₙ|)`\"); [RM] §2.4.1–2.4.2.",
 "The second-longest ticket; split per A2 into (i) the enumeration, (ii) the chain + (a), (iii) the induction (c), (iv) the scaling. Any complete nonarchimedean `K` (no discreteness).")

cleanup("CLEANUP-ALL-3", "project", "T035, CLEANUP-14", "Pre-milestone sweep before M3")

ticket("T036", "MILESTONE M3 — Schneider's Proposition 10.4 and potential orthonormalisability of countable type", CT, "CLEANUP-ALL-3", "no", "milestone", "L36.1–L36.2",
 ["Module.IsCountableType.exists_continuousLinearEquiv_nat", "Module.IsCountableType.isPotentiallyONable"],
 """1. `exists_continuousLinearEquiv_nat`: `obtain ⟨v, hv1, ⟨δ, hδ, hvδ⟩, hvt, hdense⟩ := hV.exists_isTOrthogonalFamily_nat hfin (t := 2⁻¹) (by norm_num) (by norm_num)`;
   `f := ofBounded K v ⟨1, hv1⟩`; **lower bound** `2⁻¹ * δ * ‖a‖ ≤ ‖f a‖`: for a finite `s` and `i ∈ s`, `2⁻¹ * ‖a i • v i‖ ≤ ‖∑ j ∈ s, a j • v j‖`
   and `δ * ‖a i‖ ≤ ‖a i • v i‖` (`norm_smul`), hence `2⁻¹ * δ * ‖a i‖ ≤ ‖∑ …‖`; pass to the limit along the partial sums of `hasSum_ofBounded`
   (`le_of_tendsto`, `eventually_ge_atTop {i}`), getting the bound with `‖a i‖` for every `i`, then `Real.iSup_le`/`norm_eq_iSup`.
   **Injective and closed range**: `AntilipschitzWith.of_le_mul_dist` (constant `(2⁻¹ * δ)⁻¹`) then `AntilipschitzWith.isClosed_range` with
   `f.uniformContinuous` (`CompleteSpace C₀(ℕ, K)` from `CompleteSpace K`). **Dense range**: `range f ⊇ span (range v)` (`v n = f (single n 1)`,
   `Submodule.span_le`), so `closure (range f) = univ` (`Dense.mono`). Hence `range f = univ` (`IsClosed.closure_eq`), `Bijective f`, and
   `(ContinuousLinearMap.Ultra.continuousLinearEquivOfBijective f ⟨inj, surj⟩).symm`.
2. `isPotentiallyONable`: `by_cases hfin : FiniteDimensional K V`: then `n := finrank K V`, `V ≃L[K] (Fin n → K)` (`ContinuousLinearEquiv.ofFinrankEq`,
   `Module.finrank_fin_fun`), `(Fin n → K) ≃ₗᵢ C₀(Fin n, K)` (`piEquiv.symm`), reindex to `ULift.{v} (Fin n)` (`reindex Equiv.ulift.symm`);
   otherwise step 1 and reindex to `ULift.{v} ℕ`.""",
 "`ofBounded`, `hasSum_ofBounded` (T007), `norm_smul`, `le_of_tendsto`, `Filter.eventually_ge_atTop`, `AntilipschitzWith.of_le_mul_dist`, `AntilipschitzWith.isClosed_range`, `ContinuousLinearMap.uniformContinuous`, `Dense.mono`, `IsClosed.closure_eq`, `ContinuousLinearMap.Ultra.continuousLinearEquivOfBijective` [L1], `ContinuousLinearEquiv.ofFinrankEq`, `Module.finrank_fin_fun`, `piEquiv`, `reindex`, `Equiv.ulift`.",
 "[Sch] Prop 10.4 l. 3029–3031 and proof l. 3084–3101 (\"from the universal property of the Banach space `c₀(ℕ)` we obtain a continuous linear map `f : c₀(ℕ) → V` such that `f(1ₙ) = vₙ` … `‖f()‖ ≥ r · ‖‖_∞` … This means that `f` induces a topological isomorphism between `c₀(ℕ)` and `im(f)`. In particular, `im(f)` is complete and hence closed in `V`. On the other hand `im(f)`, by (a), is dense in `V`. Hence `im(f) = V`\"); [RM] §2.4.1 (\"Hence such a space is potentially orthonormalisable over any `K`\").",
 "Any complete nonarchimedean `K`; the finite-dimensional case is Mathlib's `ofFinrankEq` (Schneider's Prop 4.13).")

cleanup("CLEANUP-15", CT, "T034, T035, T036", "Three proof tickets landed on `CountableType.lean`")

ticket("T037", "Quotients, complements and closed subspaces of spaces of countable type (Schneider 10.5)", CT, "CLEANUP-15, CLEANUP-12", "no", "lemmas", "L37.1–L37.5",
 ["Module.IsCountableType.quotient", "Submodule.closedComplemented_of_hasPr_quotient", "Submodule.closedComplemented_of_isRankOneDiscrete", "Submodule.closedComplemented_of_isCountableType", "Module.IsCountableType.submodule"],
 """1. `quotient`: `obtain ⟨s, hs, hd⟩ := hV`; `⟨U.mkQ '' s, hs.image _, ?_⟩`; `Submodule.span K (U.mkQ '' s) = (Submodule.span K s).map U.mkQ` (`Submodule.span_image`)
   and `DenseRange.dense_image (U.mkQ_surjective.denseRange) continuous_quot_mk hd`.
2. `closedComplemented_of_hasPr_quotient`: `π : V →L[K] V ⧸ U := ⟨U.mkQ, continuous_quot_mk⟩`, surjective (`U.mkQ_surjective`);
   `obtain ⟨s, hs⟩ := h.exists_lift π hsurj (ContinuousLinearMap.id K (V ⧸ U))` (instances: `Submodule.Quotient.{normedAddCommGroup, normedSpace, completeSpace}`
   and Layer 0's `Submodule.Quotient.instIsUltrametricDist`); `ContinuousLinearMap.closedComplemented_ker_of_rightInverse π s (fun y ↦ congrArg (· y) hs)`
   and `LinearMap.ker π = U` (`Submodule.ker_mkQ`).
3. `closedComplemented_of_isRankOneDiscrete`: `closedComplemented_of_hasPr_quotient U (isPotentiallyONable_of_isRankOneDiscrete (V ⧸ U)).hasPr`.
4. `closedComplemented_of_isCountableType`: `closedComplemented_of_hasPr_quotient U (hV.quotient U).isPotentiallyONable.hasPr`.
5. `submodule`: `obtain ⟨P, hP⟩ := closedComplemented_of_isCountableType hV U` (`P : V →L[K] U`, `P u = u` on `U`), so `P` is surjective and `LinearMap.ker P` is closed;
   `hV.quotient (LinearMap.ker P)` is of countable type, and `V ⧸ ker P ≃L[K] U` by Layer 1's `quotKerEquivRangeL` (range `P = ⊤`, `LinearMap.range_eq_top.2`)
   composed with `Submodule.topEquiv`; transport with a small helper `IsCountableType.of_continuousLinearEquiv` (image of the countable set, `Submodule.span_image`, `DenseRange.dense_image`).""",
 "`Submodule.span_image`, `DenseRange.dense_image`, `Submodule.mkQ_surjective`, `continuous_quot_mk`, `Submodule.ker_mkQ`, `ContinuousLinearMap.closedComplemented_ker_of_rightInverse`, `Submodule.Quotient.{normedAddCommGroup, normedSpace, completeSpace}`, `Submodule.Quotient.instIsUltrametricDist` [L0], `ContinuousLinearMap.Ultra.quotKerEquivRangeL` [L1], `LinearMap.range_eq_top`, `Submodule.topEquiv`.",
 "[Sch] Prop 10.5 l. 3120–3137 (\"Let `V` be a `K`-Banach space and suppose that (a) `K` is discretely valued or (b) `V` contains a dense vector subspace of countable dimension; then every closed vector subspace `U ⊆ V` is complemented. Proof: By Prop. 8.3 the quotient `V/U` again is a Banach space which in case (b) contains a vector subspace of countable dimension. It therefore follows from Prop. 10.1 and Prop. 10.4 that … `g : V/U ≅ c₀(X)` … The continuous linear map `f ∘ g : V/U → V` then is a section of the projection map … and `P := (id_V − f ∘ g ∘ pr)` is a continuous projector onto `U`\"); [RM] §2.4.3; E25 (closed subspaces via complementation).",
 "The lift of the identity replaces Schneider's explicit construction through `c₀(X)` (it is the lifting property of (Pr), T026). `IsClosed U` is an instance argument because Mathlib's quotient norm needs it (seam S4).")

cleanup("CLEANUP-16", CT, "T037", "Final cleanup of `CountableType.lean`")

# ---------------- Matrix ----------------
ticket("T038", "Matrix coefficients: columns, bounds, extensionality, the action in coordinates", MX, "CLEANUP-3, CLEANUP-6", "yes (parallel with the Orthogonal/ONable/Serre chain)", "lemmas", "L38.1–L38.4",
 ["tendsto_matrixCoeff_column", "norm_matrixCoeff_le", "ext_matrixCoeff", "hasSum_matrixCoeff_mul"],
 """1. `tendsto_matrixCoeff_column`: `tendsto_cofinite (u (single j 1))` (definitional unfolding of `matrixCoeff`).
2. `norm_matrixCoeff_le`: `(norm_apply_le _ i).trans (by simpa [norm_single, norm_one] using le_opNorm u (single j 1))`.
3. `ext_matrixCoeff`: `ext_single fun j ↦ ZeroAtInftyContinuousMap.ext fun i ↦ h i j`.
4. `hasSum_matrixCoeff_mul`: `have h := (hasSum_smul_apply_single u f).mapL (evalCLM R i)`; `simpa only [evalCLM_apply, smul_apply, smul_eq_mul, mul_comm] using h`.""",
 "`tendsto_cofinite`, `norm_apply_le`, `ContinuousLinearMap.Ultra.le_opNorm` [L1], `ext_single`, `hasSum_smul_apply_single` (T006), `HasSum.mapL`, `evalCLM_apply`, `smul_apply`, `mul_comm`.",
 "[RM] convention 7 and §2.6.1 (\"each column tends to `0` cofinitely, `‖u‖ = sup_{i,j} ‖matrixCoeff u i j‖`, and `(u f) i = ∑' j, matrixCoeff u i j * f j`\"); [Buz07] l. 286–296 (\"For all `i`, `lim_{j→∞} a_{i,j} = 0` … `|a_{i,j}| ≤ C` … In fact `C` can be taken to be `|φ|`\"); [Bel] l. 2029–2034.",
 "L38.1–L38.3 over any normed ring (L38.2 Tate); L38.4 commutative (decision 6).")

ticket("T039", "The norm is the supremum of the entries; `ofMatrix`", MX, "T038", "no", "definition + lemmas", "L39.1–L39.5",
 ["opNorm_eq_iSup_matrixCoeff", "ofMatrix", "matrixCoeff_ofMatrix", "ofMatrix_apply", "norm_ofMatrix"],
 """1. `opNorm_eq_iSup_matrixCoeff`: `le_antisymm`: (≤) `opNorm_le_bound _ (Real.iSup_nonneg fun _ ↦ norm_nonneg _) fun f ↦ norm_le_of_forall_le (mul_nonneg …) fun i ↦ ?_`;
   `(u f) i = ∑' j, matrixCoeff u i j * f j` (`(hasSum_matrixCoeff_mul u f i).tsum_eq`), bounded by `IsUltrametricDist.norm_tsum_le_of_forall_le` with each term
   `‖a i j * f j‖ ≤ ‖a i j‖ * ‖f j‖ ≤ (⨆ p, ‖a p.1 p.2‖) * ‖f‖` (`norm_mul_le`, `le_ciSup ⟨‖u‖, …⟩ (i, j)` using `norm_matrixCoeff_le`, `norm_apply_le`);
   (≥) `Real.iSup_le (fun p ↦ norm_matrixCoeff_le u p.1 p.2) (opNorm_nonneg _)`.
2. `ofMatrix`'s bound: `obtain ⟨C, hC⟩ := hbdd; exact ⟨max C 0, fun j ↦ norm_le_of_forall_le (le_max_right _ _) fun i ↦ (hC i j).trans (le_max_left _ _)⟩`.
3. `matrixCoeff_ofMatrix`: `show (ofBounded R _ _ (single j 1)) i = a i j; rw [ofBounded_single]; rfl`.
4. `ofMatrix_apply`: `rw [ofMatrix, ofBounded_apply, ← (summable_smul_of_bounded f _ _).hasSum.mapL (evalCLM R i) |>.tsum_eq]`-style: evaluate the tsum
   coordinatewise with `ContinuousLinearMap.map_tsum (evalCLM R i)` and `smul_apply`, `smul_eq_mul`, `mul_comm`.
5. `norm_ofMatrix`: `rw [opNorm_eq_iSup_matrixCoeff]; simp only [matrixCoeff_ofMatrix]`.""",
 "`ContinuousLinearMap.Ultra.{opNorm_le_bound, opNorm_nonneg}` [L1], `IsUltrametricDist.norm_tsum_le_of_forall_le`, `norm_mul_le`, `le_ciSup`, `Real.iSup_le`, `Real.iSup_nonneg`, `ofBounded_single`, `ofBounded_apply`, `summable_smul_of_bounded`, `ContinuousLinearMap.map_tsum`, `HasSum.tsum_eq`.",
 "[RM] §2.6.1 (\"Conversely a matrix `a : I → J → R` whose columns tend to `0` cofinitely and whose entries are bounded is the matrix of a unique bounded operator, of norm `sup ‖a i j‖`\"); [Buz07] l. 297–300 (\"there is a unique continuous `φ : M → N` with norm `sup_{i,j} |a_{i,j}|` whose associated matrix is `(a_{i,j})`\"); [Bel] l. 2031–2034.",
 "`[IsUltrametricDist R] [CompleteSpace R]` for `ofMatrix` (the target `C₀(I, R)` must be ultrametric and complete for `ofBounded`); `[NormOneClass R] [IsTate R]` for the norm formulas.")

ticket("T040", "The matrix of a composite is the matrix product", MX, "T039", "no", "lemmas", "L40.1–L40.2",
 ["summable_matrixCoeff_mul_matrixCoeff", "matrixCoeff_comp"],
 """1. `summable_matrixCoeff_mul_matrixCoeff`: `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`; the family tends to `0` by `squeeze_zero_norm`
   with `‖a i j * b j l‖ ≤ ‖u‖ * ‖b j l‖` (`norm_mul_le`, `norm_matrixCoeff_le`) and `((tendsto_matrixCoeff_column v l).norm.const_mul _)`.
2. `matrixCoeff_comp`: `unfold matrixCoeff; rw [comp_apply]`; `(u (v (single l 1))) i = ∑' j, matrixCoeff u i j * (v (single l 1)) j` is
   `(hasSum_matrixCoeff_mul u (v (single l 1)) i).tsum_eq.symm`, and `(v (single l 1)) j = matrixCoeff v j l` by definition.""",
 "`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`, `squeeze_zero_norm`, `norm_mul_le`, `Filter.Tendsto.const_mul`, `ContinuousLinearMap.comp_apply`, `HasSum.tsum_eq`.",
 "[RM] §2.6.1 (\"The matrix of a composite is the matrix product, with the middle sum convergent by §0.1.4\"); [Buz07] l. 300–303 (\"if `φ` and `ψ` … the matrix of `ψ ∘ φ` is the product\"); [L0] `Sums.lean` (`tendsto_cofinite_prod_of_norm_le_mul`, the bounded-times-null principle).",
 "Commutative scalars (decision 6); `[IsTate R]` for the boundedness of `u`'s entries.")

cleanup("CLEANUP-17", MX, "T038, T039, T040", "Three proof tickets landed on `Matrix.lean`")

ticket("T041", "Diagonal and permutation operators", MX, "CLEANUP-17", "no", "definitions + lemmas", "L41.1–L41.7",
 ["diagonal", "matrixCoeff_diagonal", "norm_diagonal", "injective_diagonal", "denseRange_diagonal", "diagonalEquiv", "matrixCoeff_reindex"],
 """1. `diagonal`: tendsto by `squeeze_zero_norm` with `‖d i * f i‖ ≤ max C 0 * ‖f i‖`; `map_add'`: `mul_add`; `map_smul'`: `mul_left_comm`; the `mkContinuous` bound:
   `rcases isEmpty_or_nonempty I` — empty: `f = 0` and both sides vanish; nonempty: `0 ≤ C` (from `hd i`), then `norm_le_of_forall_le (mul_nonneg hC (norm_nonneg f))`
   with `norm_mul_le`, `hd i`, `norm_apply_le`.
2. `matrixCoeff_diagonal`: `by_cases h : i = j <;> simp [matrixCoeff, diagonal_apply, coe_single, Pi.single_apply, h]`.
3. `norm_diagonal`: `le_antisymm (opNorm_le_bound _ (Real.iSup_nonneg …) fun f ↦ norm_le_of_forall_le … fun i ↦ (norm_mul_le _ _).trans (mul_le_mul (le_ciSup ⟨C, …⟩ i) (norm_apply_le f i) …))`
   and `Real.iSup_le (fun i ↦ by simpa [norm_single, norm_one, diagonal_apply, single_apply_self] using le_opNorm_of_bound (diagonal d C hd) ⟨_, …⟩ (single i 1)) (opNorm_nonneg _)`
   (the value at `single i 1` has coordinate `d i` at `i`, so `‖d i‖ ≤ ‖diagonal d C hd (single i 1)‖`).
4. `injective_diagonal`: `fun f g hfg ↦ ext fun i ↦ h i _ (by have := congrArg (· i) hfg; rw [diagonal_apply, diagonal_apply] at this; rw [mul_sub, this, sub_self])`
   (then `sub_eq_zero`).
5. `denseRange_diagonal`: `DenseRange` is `Dense (Set.range _)`; `Dense.mono (Submodule.span_le.2 ?_) dense_span_range_single_one` where
   `single i 1 = diagonal d C hd (single i ((h i).unit⁻¹ : R))` (`ext j`, `by_cases j = i`, `Units.mul_inv`).
6. `diagonalEquiv`: tendsto from `‖d i * f i‖ = ‖f i‖` (`(hd i).norm_mul`, `h1 i`, `one_mul`); inverse `((d i)⁻¹ : Rˣ)` is multiplicative of norm `1`
   (`IsMultiplicative.inv`, `IsMultiplicative.norm_inv`); `map_add'`/`map_smul'`: `mul_add`, `mul_left_comm`; inverses: `Units.inv_mul_cancel_left`,
   `Units.mul_inv_cancel_left`; `norm_map'`: sandwich with `‖d i * f i‖ = ‖f i‖`.
7. `matrixCoeff_reindex`: `simp [matrixCoeff, reindex_apply, coe_single, Pi.single_apply, Equiv.symm_apply_eq]`.""",
 "`squeeze_zero_norm`, `mul_add`, `mul_left_comm`, `isEmpty_or_nonempty`, `norm_mul_le`, `le_ciSup`, `ContinuousLinearMap.Ultra.{opNorm_le_bound, le_opNorm_of_bound, opNorm_nonneg}` [L1], `Pi.single_apply`, `mul_sub`, `sub_eq_zero`, `Dense.mono`, `Submodule.span_le`, `IsUnit.unit`, `Units.mul_inv`, `NormedRing.IsMultiplicative.{norm_mul, inv, norm_inv}` [L0], `Units.inv_mul_cancel_left`, `Equiv.symm_apply_eq`.",
 "[RM] §2.6.2 (\"The diagonal operator of a bounded family `d : I → R` has norm `sup ‖dᵢ‖`; it is an isometric automorphism when every `dᵢ` is a multiplicative unit of norm `1`, and injective with dense range when every `dᵢ` is a non-zero-divisor [E22: unit for dense range] … The permutation operator of `σ : I ≃ I` is an isometric automorphism\"); Layer 1 Examples (\"diagonal operator\").",
 "Commutative `R`; `norm_diagonal` is proved without ultrametricity; E22 for `denseRange_diagonal`.")

ticket("T042", "Base change of matrices along a bounded ring homomorphism (Johansson–Newton 2.1.8)", MX, "T041, CLEANUP-6", "no", "definition + lemmas", "L42.1–L42.5",
 ["baseChange", "matrixCoeff_baseChange", "baseChange_map", "norm_baseChange_le", "baseChange_symm_baseChange"],
 """1. `baseChange`'s two obligations: columns tend to `0` by `squeeze_zero_norm` with `‖φ (a i j)‖ ≤ max C 0 * ‖a i j‖` and `tendsto_matrixCoeff_column`;
   entries bounded by `max C 0 * ‖u‖` (`norm_matrixCoeff_le`).
2. `matrixCoeff_baseChange`: `matrixCoeff_ofMatrix _ _ _ i j`.
3. `baseChange_map`: `ext i`; LHS `= ∑' j, φ (a i j) * φ (f j)` (`ofMatrix_apply`, `map_apply`); RHS `= φ (∑' j, a i j * f j)` (`map_apply`, `(hasSum_matrixCoeff_mul u f i).tsum_eq`);
   `φ` is continuous (`AddMonoidHomClass.continuous_of_bound φ C hφ`), so `((hasSum_matrixCoeff_mul u f i).map φ hcont)` with `map_mul` gives the equality via `HasSum.tsum_eq`.
4. `norm_baseChange_le`: `rw [norm_ofMatrix]; exact Real.iSup_le (fun p ↦ (hφ _).trans (mul_le_mul_of_nonneg_left (norm_matrixCoeff_le u _ _) hC)) (mul_nonneg hC (opNorm_nonneg u))`.
5. `baseChange_symm_baseChange`: `ext_matrixCoeff fun i j ↦ by simp only [matrixCoeff_baseChange, RingEquiv.symm_toRingHom_apply? , RingEquiv.symm_apply_apply]`.""",
 "`squeeze_zero_norm`, `tendsto_matrixCoeff_column`, `norm_matrixCoeff_le` (T038), `matrixCoeff_ofMatrix`, `ofMatrix_apply`, `norm_ofMatrix` (T039), `AddMonoidHomClass.continuous_of_bound`, `HasSum.map`, `map_mul`, `Real.iSup_le`, `RingEquiv.symm_apply_apply`, `ext_matrixCoeff`.",
 "[RM] §2.6.6 (\"For a bounded ring homomorphism `φ : R → S`, the operator `C₀(J, S) → C₀(I, S)` with matrix `φ (matrixCoeff u i j)` exists, is `φ`-semilinearly compatible with `u`, and has norm at most `‖φ‖ ‖u‖`; a bicontinuous ring isomorphism transports bounded operators (Johansson–Newton, Proposition 2.1.8, the part that does not mention compactness)\"); [JN] l. 655–660 (\"If we change the norms on `(R, M)` to equivalent ones, then `M` still has property (Pr)\").",
 "`R` Tate (bounded entries), `S` ultrametric complete (for `ofMatrix`), both `NormOneClass`/Tate for the norm bound.")

cleanup("CLEANUP-18", MX, "T041, T042", "Final cleanup of `Matrix.lean`")
