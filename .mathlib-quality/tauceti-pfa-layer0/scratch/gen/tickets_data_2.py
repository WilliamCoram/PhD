# ---------------- G4 Multiplicative ----------------
ticket('T015','Multiplicative elements: products and powers','Multiplicative.lean','none','yes','lemmas',
 'L4.1',
 ['RE:^theorem mul \\(ha','norm_pow_mul','RE:^theorem one :','RE:^theorem norm_pow \\(ha','RE:^theorem pow \\(ha','isMultiplicative_of_normMulClass'],
 """1. `mul`: `fun x ↦ by rw [mul_assoc, ha, hb, ha, mul_assoc]` ([SRC] `00_Tate.IsMultiplicative.mul`).
2. `norm_pow_mul`: induction on `n`; `pow_succ`, `mul_assoc`, the hypothesis at `a * x`; `pow_zero`, `one_mul` at `0`.
3. `one`: `fun x ↦ by rw [one_mul, norm_one, one_mul]`.
4. `norm_pow`: `by simpa using ha.norm_pow_mul n 1`.
5. `pow`: `fun x ↦ by rw [ha.norm_pow_mul, ha.norm_pow]`.
6. `isMultiplicative_of_normMulClass`: `fun x ↦ norm_mul a x`.""",
 '`norm_one`, `norm_mul`, `pow_succ`, `mul_assoc`.',
 '[JN] `jn.txt:487` ("`r ∈ R` is multiplicative if `|rs| = |r||s|` for all `s ∈ R`"); [RM] §0.2.4; decomposition L4.1.',
 '`SeminormedRing`; `NormOneClass` exactly for `one`, `norm_pow`, `pow` (the `n = 0` case; necessary — decomposition L4.1). Left-multiplicative; no commutativity.')
ticket('T016','Multiplicative units','Multiplicative.lean','T015','no','lemmas',
 'L4.2–L4.3',
 ['isMultiplicative_units_iff','RE:^theorem norm_pos \\(hu','RE:^theorem norm_inv \\(hu','RE:^theorem inv \\(hu','RE:^theorem zpow \\(hu','RE:^theorem norm_zpow \\(hu'],
 """1. `isMultiplicative_units_iff`. `⇒`: `hu (↑u⁻¹)` with `Units.mul_inv`, `norm_one` gives `1 = ‖u‖ * ‖u⁻¹‖`;
   `eq_inv_of_mul_eq_one_right`. `⇐`: first `0 < ‖u‖` (else `‖u⁻¹‖ = 0⁻¹ = 0` and
   `1 = ‖u * u⁻¹‖ ≤ ‖u‖ * ‖u⁻¹‖ = 0`). Then for `x`: `‖u * x‖ ≤ ‖u‖ * ‖x‖` (`norm_mul_le`) and
   `‖x‖ = ‖u⁻¹ * (u * x)‖ ≤ ‖u‖⁻¹ * ‖u * x‖`; `le_antisymm` after `le_inv_mul_iff₀`.
2. `norm_pos`: as in the `⇐` argument, from `hu (↑u⁻¹)`: `‖u‖ * ‖u⁻¹‖ = 1`. `norm_inv`: step 1 `⇒`.
3. `inv`: step 1 `⇐` for `u⁻¹`, with `inv_inv` and `norm_inv`.
4. `zpow`, `norm_zpow`: `Int.induction_on`; `zpow_add_one`, `zpow_sub_one`, `Units.val_mul`, T015 `mul`, step 3;
   norms by `hu`/`inv` applied to the previous power; `zpow_add_one₀`, `zpow_sub_one₀` with `norm_pos.ne'`.""",
 '`Units.mul_inv`, `Units.inv_mul`, `norm_mul_le`, `eq_inv_of_mul_eq_one_right`, `le_inv_mul_iff₀`, `Int.induction_on`, `zpow_add_one`, `zpow_sub_one`, `zpow_add_one₀`, `zpow_sub_one₀`, `Units.val_mul`.',
 '[JN] `jn.txt:496` ("a unit `ϖ` … is multiplicative if and only if `|ϖ⁻¹| = |ϖ|⁻¹`"); [Bel] Exercise II.1.1 (`bellaiche.txt:1963`); [RM] §0.2.4; decomposition L4.2–L4.3.',
 '`SeminormedRing` + `NormOneClass`; the iff is safe for seminorms (positivity of `‖u‖` is derived).')
ticket('T017','Multiplicative units scale module norms exactly','Multiplicative.lean','T016','no','lemmas',
 'L4.4',
 ['RE:^theorem norm_smul \\(hu','RE:^theorem norm_zpow_smul \\(hu'],
 """1. `norm_smul`: `le_antisymm (norm_smul_le _ _)`; for the other inequality
   `‖m‖ = ‖(↑u⁻¹ : R) • (u : R) • m‖ ≤ ‖↑u⁻¹‖ * ‖u • m‖ = ‖u‖⁻¹ * ‖u • m‖` (`smul_smul`, `Units.inv_mul`, `one_smul`,
   `hu.norm_inv`), then multiply by `‖u‖ > 0` ([SRC] `01_OperatorNorm.norm_pseudoUniformizer_smul`).
2. `norm_zpow_smul`: step 1 for the unit `u ^ n` with T016's `zpow` and `norm_zpow`.""",
 '`norm_smul_le`, `smul_smul`, `Units.inv_mul`, `one_smul`, `mul_le_mul_of_nonneg_left`, `mul_inv_cancel₀`.',
 '[JN] `jn.txt:519` ("if `r ∈ R` is a multiplicative unit, then one sees easily that `‖rm‖ = |r|·‖m‖` for all `m ∈ M`"); [Bel] proof of Lemma II.1.12 (`bellaiche.txt:2087`); decomposition L4.4.',
 '`SeminormedAddCommGroup M` with `IsBoundedSMul R M` — no ultrametric, no completeness.')
cleanup('CLEANUP-6','Multiplicative.lean','T017','Final per-file cleanup for `Multiplicative.lean`.')
# ---------------- G5 Module ----------------
ticket('T018','Products and submodules','Module.lean','none','yes','instances',
 'L5.1–L5.2',
 ['Prod.instIsUltrametricDist','Submodule.instIsBoundedSMul'],
 """1. `Prod.instIsUltrametricDist`: `⟨fun x y z ↦ _⟩`; `Prod.dist_eq`; `max_le` of the two coordinate inequalities
   `dist_triangle_max`, each followed by `le_max_of_le_left/right` and `max_le_max`.
2. `Submodule.instIsBoundedSMul`: the two fields are the fields of `IsBoundedSMul R M` at the coerced points:
   `dist_smul_pair' r x y := dist_smul_pair r (x : M) y`, `dist_pair_smul' r s x := dist_pair_smul r s (x : M)`
   (`Subtype.dist_eq`, `Submodule.coe_smul`).""",
 '`Prod.dist_eq`, `dist_triangle_max`, `max_le_max`, `dist_smul_pair`, `dist_pair_smul`, `Subtype.dist_eq`, `Submodule.coe_smul`.',
 '[RM] §0.3.1; decomposition L5.1–L5.2 (absence of both instances verified by a failing `inferInstance`).',
 '`PseudoMetricSpace` for the product (no group structure needed); `SeminormedRing`/`SeminormedAddCommGroup` for the submodule.')
ticket('T019','The quotient norm is ultrametric','Module.lean','T018','no','instances',
 'L5.3',
 ['QuotientAddGroup.instIsUltrametricDist','Submodule.Quotient.instIsUltrametricDist','Ideal.Quotient.instIsUltrametricDist'],
 """1. `QuotientAddGroup…`: `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`; given `x y : M ⧸ S` show
   `‖x + y‖ ≤ max ‖x‖ ‖y‖` by `le_of_forall_pos_lt_add`: for `ε > 0` pick representatives `m`, `n` with
   `‖m‖ < ‖x‖ + ε`, `‖n‖ < ‖y‖ + ε` (`QuotientAddGroup.norm_lt_iff`), then
   `‖x + y‖ ≤ ‖m + n‖ ≤ max ‖m‖ ‖n‖ < max ‖x‖ ‖y‖ + ε` (`QuotientAddGroup.norm_mk_le_norm`, `max_add_add_right`).
2. The other two: `inferInstanceAs (IsUltrametricDist (M ⧸ S.toAddSubgroup))` — Mathlib's norm on these quotients is
   defined that way; if `inferInstanceAs` fails, repeat step 1 with `Submodule.Quotient.norm_mk_lt`.""",
 '`IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`, `QuotientAddGroup.norm_lt_iff`, `QuotientAddGroup.norm_mk_le_norm`, `le_of_forall_pos_lt_add`, `IsUltrametricDist.norm_add_le_max`, `max_add_add_right`.',
 '[Sch] §5.B (`schneider.txt:975`): "for any seminorm `q` on `V` one has the quotient seminorm `q(v + U) := inf_{u ∈ U} q(v + u)`"; Prop 8.3 (`:2281`); [RM] §0.3.1; decomposition L5.3.',
 'Seminormed (no closedness of `S` needed for the ultrametric inequality); completeness is already Mathlib\'s `Submodule.Quotient.completeSpace`.')
ticket('T020','Completeness along a bounded equivalence','Module.lean','T019','yes (independent)','lemma',
 'L5.4',
 ['AddEquiv.completeSpace_congr_of_bounds'],
 """1. Both `e` and `e.symm` are Lipschitz: `AddMonoidHomClass.lipschitz_of_bound e C h`, likewise for `e.symm`.
2. Build the `UniformEquiv` with `toEquiv := e.toEquiv` and the two `LipschitzWith.uniformContinuous`.
3. `completeSpace_congr` along its `isUniformEmbedding` (or `UniformEquiv.completeSpace_iff` if present — `#check`).""",
 '`AddMonoidHomClass.lipschitz_of_bound`, `LipschitzWith.uniformContinuous`, `UniformEquiv.isUniformEmbedding`, `completeSpace_congr`.',
 '[RM] §0.3.2 ("bounded-equivalent norms have the same bounded maps and the same Cauchy sequences"); [Sch] proof of Prop 10.1 (`schneider.txt:2953`); decomposition L5.4.',
 'Two norms are two types related by an additive equivalence with a bound each way (plan decision 4). Seminormed; constants are arbitrary reals.')
cleanup('CLEANUP-7','Module.lean','T020','Final per-file cleanup for `Module.lean`.')
# ---------------- G6 Tate ----------------
ticket('T021','Pseudo-uniformisers: norms of powers','Tate.lean','CLEANUP-6','no','lemmas',
 'L6.0b–L6.1',
 ['normOneClass_of_nontrivial','RE:^theorem norm_pos : 0','RE:^theorem norm_inv : ','RE:^theorem norm_zpow \\(n','log_norm_neg','RE:^theorem norm_smul \\(m','RE:^theorem norm_zpow_smul \\(n'],
 """0. `normOneClass_of_nontrivial`: `have h := ϖ.isMultiplicative 1`; `mul_one` turns it into `‖ϖ‖ = ‖ϖ‖ * ‖1‖`;
   `‖ϖ‖ ≠ 0` is `norm_ne_zero_iff.2 ϖ.unit.ne_zero`; conclude with `mul_right_eq_self₀` (proof compiled in
   `scratch/spot2.lean`). It shows `[NormOneClass R]` below is no more than `[Nontrivial R]`.
The other six are T016–T017 at `u := ϖ.unit`, `hu := ϖ.isMultiplicative`:
`ϖ.isMultiplicative.norm_pos`, `.norm_inv`, `.norm_zpow n`, `.norm_smul m`, `.norm_zpow_smul n m`.
`log_norm_neg`: `Real.log_neg ϖ.norm_pos ϖ.norm_lt_one`.""",
 '`Real.log_neg`, `norm_ne_zero_iff`, `Units.ne_zero`, `mul_right_eq_self₀`; T016, T017.',
 '[JN] Definition 2.1.1(1) (`jn.txt:476`, "`|1| = 1`"), Definition 2.1.2 and the remarks at `jn.txt:496, 519`; [RM] §0.4.1; decomposition L6.0b–L6.1.',
 '`NormedRing` + `NormOneClass` (erratum E5: positivity needs `‖1‖ = 1`). `NormedAddCommGroup M` to match T022.')
ticket('T022','The scaling trick','Tate.lean','T021','no','lemmas',
 'L6.2–L6.3',
 ['existsUnique_zpow_norm_smul_mem_Ioc','existsUnique_zpow_norm_smul_mem_Ioc_one'],
 """Put `c := ‖(ϖ : R)‖ ∈ (0, 1)` (T021). By T021, `‖ϖ ^ n • m‖ = c ^ n * ‖m‖`, so the claim is: there is a unique
`n : ℤ` with `δ * c < c ^ n * ‖m‖ ≤ δ`.
1. Existence. `exists_mem_Ioc_zpow (x := ‖m‖ / δ) (y := c⁻¹)` (`0 < ‖m‖ / δ` from `norm_pos_iff.2 hm`; `1 < c⁻¹`
   from `one_lt_inv₀`) gives `k` with `(c⁻¹) ^ k < ‖m‖ / δ ≤ (c⁻¹) ^ (k + 1)`. Take `n := k + 1`: multiplying through
   by `c ^ (k + 1) * δ > 0` gives `δ * c < c ^ (k + 1) * ‖m‖ ≤ δ` (`inv_zpow'`, `zpow_neg`, `zpow_add_one₀`,
   `lt_div_iff₀`, `div_le_iff₀`).
2. Uniqueness. If `n < n'` both work then `n + 1 ≤ n'`, so
   `c ^ n' * ‖m‖ ≤ c ^ (n + 1) * ‖m‖ = c * (c ^ n * ‖m‖) ≤ c * δ` (`zpow_le_zpow_right_of_le_one₀`), contradicting
   `δ * c < c ^ n' * ‖m‖`. Symmetric for `n' < n`; `lt_trichotomy`.
3. `_one`: `by simpa using ϖ.existsUnique_zpow_norm_smul_mem_Ioc one_pos hm`.
""",
 '`exists_mem_Ioc_zpow`, `one_lt_inv₀`, `zpow_le_zpow_right_of_le_one₀`, `zpow_add_one₀`, `inv_zpow\'`, `zpow_neg`, `div_le_iff₀`, `lt_div_iff₀`, `norm_pos_iff`.',
 '[RM] §0.4.2; [Buz07] `buzzard.txt:156, 269` ("We use `ρ` to \'normalise\' vectors"; "one can use `ρ` to renormalise elements of `M`"); [JN] Definition 2.1.5 ("using a multiplicative pseudo-uniformizer `ϖ` for what Buzzard calls `ρ`"); decomposition L6.2–L6.3.',
 'General shell `Ioc (δ * ‖ϖ‖) δ` — Layer 1 scales into the shell of a continuity modulus; the roadmap\'s `δ = 1` is the corollary. `NormedAddCommGroup M` (a nonzero vector must have positive norm).')
ticket('T023','The valuation of a pseudo-uniformiser: values','Tate.lean','T022','yes (independent of T022)','lemmas',
 'L6.4–L6.5',
 ['val_zero','val_of_ne_zero','val_eq_top_iff','val_self','val_one','val_zpow_self'],
 """1. `val_zero`: `if_pos rfl`. `val_of_ne_zero`: `if_neg hr`. `val_eq_top_iff`: `by_cases`, `WithTop.coe_ne_top`.
2. `val_self`: `ϖ ≠ 0` (`ϖ.unit.ne_zero` in a nontrivial ring, `NormOneClass.nontrivial`), `val_of_ne_zero`,
   `div_self ϖ.log_norm_neg.ne`, `WithTop.coe_one`.
3. `val_one`: `one_ne_zero`, `norm_one`, `Real.log_one`, `zero_div`, `WithTop.coe_zero`.
4. `val_zpow_self`: `Units.ne_zero`, `ϖ.norm_zpow`, `Real.log_zpow`, `mul_div_assoc`, `div_self`, `mul_one`.""",
 '`WithTop.coe_ne_top`, `Units.ne_zero`, `NormOneClass.nontrivial`, `Real.log_one`, `Real.log_zpow`, `div_self`.',
 '[JN] Definition 2.1.2 (`jn.txt:489`): "`v_ϖ(r) = −log_a |r|`, where `a = |ϖ⁻¹|`"; [RM] §0.4.3; decomposition L6.4–L6.5.',
 '`val` takes values in `WithTop ℝ` with `⊤` exactly at `0` (never junk). `NormOneClass` from `val_self` on.')
cleanup('CLEANUP-8','Tate.lean','T023')
ticket('T024','The valuation of a pseudo-uniformiser: order and arithmetic','Tate.lean','CLEANUP-8','no','lemmas',
 'L6.6–L6.8',
 ['val_le_val_iff','val_lt_val_iff','val_nonneg_iff','val_add_val_le_val_mul','val_mul','min_val_le_val_add','norm_eq_rpow_of_val_eq'],
 """1. `val_le_val_iff`: cases on `r = 0`, `s = 0` (`val_zero`, `top_le_iff`, `val_eq_top_iff`, `norm_le_zero_iff`,
   `le_top`). Both nonzero: `WithTop.coe_le_coe`, `div_le_div_right_of_neg ϖ.log_norm_neg`, `Real.log_le_log_iff`.
2. `val_lt_val_iff`: `lt_iff_not_ge` from step 1. `val_nonneg_iff`: step 1 with `s := 1`… precisely
   `0 = val 1 ≤ val r ↔ ‖r‖ ≤ ‖1‖ = 1` (`val_one`, `norm_one`).
3. `val_add_val_le_val_mul`: if `r * s = 0` the right side is `⊤`. Else `r, s ≠ 0`; `← WithTop.coe_add`, `← add_div`,
   `div_le_div_right_of_neg`, `Real.log_mul`, `Real.log_le_log` from `norm_mul_le`.
4. `val_mul`: `mul_eq_zero` cases (`WithTop.add_top`, `top_add`); otherwise `norm_mul`, `Real.log_mul`, `add_div`.
5. `min_val_le_val_add`: from step 1: `‖r + s‖ ≤ max ‖r‖ ‖s‖` means `val (r+s) ≥ val` of whichever has the larger norm;
   `min_le_iff`, `le_max_iff`.
6. `norm_eq_rpow_of_val_eq`: `r ≠ 0` (else `⊤ = ↑q`); `WithTop.coe_inj`; `Real.rpow_def_of_pos ϖ.norm_pos`,
   `mul_div_cancel₀`… giving `exp (log ‖r‖) = ‖r‖` by `Real.exp_log`.""",
 '`WithTop.coe_le_coe`, `div_le_div_right_of_neg`, `Real.log_le_log_iff`, `Real.log_mul`, `WithTop.coe_add`, `norm_mul_le`, `norm_mul`, `IsUltrametricDist.norm_add_le_max`, `Real.rpow_def_of_pos`, `Real.exp_log`.',
 '[RM] §0.4.3 ("order-reversing in the norm, `val ϖ (r * s) ≥ val ϖ r + val ϖ s` with equality when the norm is multiplicative, `val ϖ (r + s) ≥ min`, and `‖r‖ = ‖ϖ‖ ^ (val ϖ r)`. ⚠ It is not an `AddValuation`"); decomposition L6.6–L6.8; [SRC] `00_Tate.PseudoUniformizer.val_*`.',
 'No bundled structure. `NormMulClass` only for `val_mul`; `IsUltrametricDist` only for `min_val_le_val_add`. The seam with `normAddVal` (E6) is external and not part of this ticket.')
ticket('T025','The bridge from normed algebras over a field','Tate.lean','T024','yes (independent of T022–T024)','def fields + theorem',
 'L6.9',
 ['ofNormedAlgebra','isTate_of_normedAlgebra'],
 """1. Fill the two `sorry` fields of `ofNormedAlgebra`. `isMultiplicative`: the unit coerces to `algebraMap K R c`
   (`Units.coe_map`, `Units.val_mk0`); `algebraMap K R c * x = c • x` (`Algebra.smul_def`), so `norm_smul` and
   `norm_algebraMap'`. `norm_lt_one`: `norm_algebraMap'` and `hc₁`.
2. `isTate_of_normedAlgebra`: `obtain ⟨c, hc₀, hc₁⟩ := NormedField.exists_norm_lt_one K`;
   `⟨⟨ofNormedAlgebra K (norm_pos_iff.1 hc₀) hc₁⟩⟩`.
3. The field instance is already a term (`isTate_of_normedAlgebra K K`).""",
 '`Units.coe_map`, `Units.val_mk0`, `Algebra.smul_def`, `norm_smul`, `norm_algebraMap\'`, `NormedField.exists_norm_lt_one`, `norm_pos_iff`.',
 '[RM] §0.4.4; [Wed] Example 6.13 (`wedhorn.txt:2170`): "Every normed `k`-algebra `(A, ‖·‖)` is a Tate ring"; decomposition L6.9; [SRC] `00_Tate.isTate_of_normedAlgebra`.',
 '`NontriviallyNormedField K`, `NormedAlgebra K R`, `NormOneClass R` (necessary: `‖c • 1‖ = ‖c‖`). A theorem, not an instance (`K` is not determined by `R`); the field case is the instance.')
cleanup('CLEANUP-9','Tate.lean','T025','Final per-file cleanup for `Tate.lean`.')
# ---------------- G7 NormComparison ----------------
ticket('T026','Johansson–Newton Lemma 2.1.6','NormComparison.lean','CLEANUP-9','yes (with G8, G9)','lemmas',
 'L7.1–L7.2',
 ['exists_norm_le_of_norm_map_le_one','exists_norm_le_mul_rpow_norm_map'],
 """1. Constants. Continuity of `e.symm` at `0` (`Metric.continuousAt_iff`, `map_zero`) gives `D₁ > 0` with
   `‖y‖ < D₁ → ‖e.symm y‖ < 1`. Put `D := min (D₁ / 2) (1 / 2)`. `‖ϖ ^ k‖ = ‖ϖ‖ ^ k → 0` (T015 `norm_pow`,
   `tendsto_pow_atTop_nhds_zero_of_lt_one`) and `e` is continuous at `0`, so eventually `‖e (ϖ ^ k)‖ ≤ D`; intersect
   with `Filter.eventually_ge_atTop 1` to get such an `m` with `1 ≤ m`. Put `K := ‖ϖ‖⁻¹ ^ m`, so `1 < K`
   (`one_lt_inv₀`, `one_lt_pow₀`).
2. First lemma, `C := K`. If `‖e a‖ ≤ 1` then `‖e (ϖ ^ m * a)‖ ≤ ‖e (ϖ ^ m)‖ * ‖e a‖ ≤ D < D₁`, so
   `‖ϖ ^ m * a‖ < 1` (step 1 at `y := e (ϖ ^ m * a)`, `e.symm_apply_apply`); and `‖ϖ ^ m * a‖ = ‖ϖ‖ ^ m * ‖a‖`
   (T015 `norm_pow_mul`), whence `‖a‖ ≤ K`.
3. Second lemma, `s := Real.log K / Real.log 2 > 0` and `C := K * K`. Let `1 ≤ ‖e a‖`,
   `x := Real.log ‖e a‖ / Real.log 2 ≥ 0`, `n := ⌈x⌉₊`. Then `(1 / 2) ^ n * ‖e a‖ ≤ 1` (`Nat.le_ceil`), so
   `‖e (ϖ ^ (m * n) * a)‖ ≤ ‖e (ϖ ^ m)‖ ^ n * ‖e a‖ ≤ 1` (`pow_mul`, `map_pow`, `map_mul`, `norm_mul_le`,
   `norm_pow_le'` for `0 < n`; for `n = 0` the claim is `‖e a‖ ≤ 1`, which holds since then `x = 0`). Step 2 applied
   to `ϖ ^ (m * n) * a` gives `‖ϖ‖ ^ (m * n) * ‖a‖ ≤ K`, i.e. `‖a‖ ≤ K * K ^ n`. Finally `n < x + 1`
   (`Nat.ceil_lt_add_one`), so `K ^ n ≤ K ^ (x + 1) = K * K ^ x` (`Real.rpow_natCast`,
   `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_add`) and `K ^ x = ‖e a‖ ^ s` (both are
   `exp (log K * log ‖e a‖ / log 2)`, `Real.rpow_def_of_pos`).
""",
 '`Metric.continuousAt_iff`, `Continuous.tendsto`, `tendsto_pow_atTop_nhds_zero_of_lt_one`, `Filter.eventually_ge_atTop`, `one_lt_inv₀`, `one_lt_pow₀`, `map_pow`, `RingEquiv.symm_apply_apply`, `norm_mul_le`, `norm_pow_le\'`, `Nat.ceil_lt_add_one`, `Nat.le_ceil`, `Real.rpow_natCast`, `Real.rpow_add`, `Real.rpow_def_of_pos`, `Real.rpow_le_rpow_of_exponent_le`.',
 '[JN] Lemma 2.1.6 and its proof, `jn.txt:565–600`, read in full (decomposition §0.3.2 substrate); ⚠ the *published* statement is incorrect, this is the corrected v4 form; [SRC] `08_BaseChange.norm_le_pow_of_equiv`.',
 'Split into its two inequalities (one conclusion each); the second pseudo-uniformiser `π` of [JN]/[SRC] is **dropped** — the proof never uses it. First bound stated for `‖e a‖ ≤ 1`, as proved (stronger than `< 1`). `NormedRing`, not commutative.')
ticket('T027','Johansson–Newton Lemma 2.1.7','NormComparison.lean','T026','no','lemmas',
 'L7.3–L7.5',
 ['logb_norm_map_pos','exists_norm_map_le_mul_rpow','exists_mul_rpow_le_norm_map'],
 """1. `logb_norm_map_pos`: `Real.logb_pos_iff_of_base_lt_one ϖ.norm_pos ϖ.norm_lt_one` reduces to `0 < ‖e ϖ‖ < 1`.
   Positivity: T016 `norm_pos` for the unit `Units.map (e : R →* S) ϖ.unit` of `S`. `< 1`:
   `‖e ϖ‖ ^ k = ‖e (ϖ ^ k)‖` (T015 `norm_pow` in `S`, `map_pow`) tends to `0` (`he.tendsto 0` composed with
   `‖ϖ ^ k‖ → 0`), so `‖e ϖ‖ < 1` (`tendsto_pow_atTop_nhds_zero_iff`). Keep `‖e ϖ‖ < 1` as a private helper: step 3
   needs it.
2. `exists_norm_map_le_mul_rpow`: put `s := logb ‖ϖ‖ ‖e ϖ‖`, so `‖e ϖ‖ = ‖ϖ‖ ^ s` (`Real.rpow_logb`). Continuity
   of `e` at `0` gives `D > 0` with `‖a‖ ≤ D → ‖e a‖ ≤ 1`. Take `C := (D * ‖ϖ‖) ^ (-s)`. For `a = 0`: `map_zero`,
   `Real.zero_rpow (step 1).ne'`. For `a ≠ 0` apply the **scaling trick T022** to `R` as a module over itself
   (`smul_eq_mul`) with shell radius `D`: some `n : ℤ` has `D * ‖ϖ‖ < ‖ϖ‖ ^ n * ‖a‖ ≤ D`. The upper bound gives
   `‖e (ϖ ^ n * a)‖ ≤ 1`; and `‖e (ϖ ^ n * a)‖ = ‖e ϖ‖ ^ n * ‖e a‖` by T016 (`zpow`, `norm_zpow`) for the
   multiplicative unit `Units.map e ϖ.unit` (`map_mul`, `map_zpow`, `Units.coe_map`). Hence
   `‖e a‖ ≤ ‖e ϖ‖ ^ (-n) = (‖ϖ‖ ^ (-n)) ^ s`, and the lower bound gives `‖ϖ‖ ^ (-n) < ‖a‖ / (D * ‖ϖ‖)`; conclude with
   `Real.rpow_le_rpow`, `Real.mul_rpow`, `Real.rpow_neg`.
3. `exists_mul_rpow_le_norm_map`: apply step 2 to `e.symm` with the pseudo-uniformiser
   `⟨Units.map e ϖ.unit, hϖ, step 1⟩` of `S` (its image under `e.symm` is `ϖ`, multiplicative by
   `ϖ.isMultiplicative`); its exponent is `logb ‖e ϖ‖ ‖ϖ‖ = s⁻¹` (`Real.inv_logb`). From
   `‖a‖ ≤ C' * ‖e a‖ ^ s⁻¹` raise to the power `s > 0` (`Real.rpow_le_rpow`, `Real.mul_rpow`,
   `Real.rpow_inv_rpow`) and take `C := (max C' 1) ^ (-s)`.
""",
 '`Real.logb_pos_iff_of_base_lt_one`, `Real.rpow_logb`, `Real.inv_logb`, `Real.rpow_le_rpow`, `Real.mul_rpow`, `Real.rpow_neg`, `Real.rpow_inv_rpow`, `Real.zero_rpow`, `tendsto_pow_atTop_nhds_zero_iff`, `Units.map`, `Units.coe_map`, `map_zpow`, `Metric.continuousAt_iff`; T015, T016, T022.',
 '[JN] Lemma 2.1.7 and its proof, `jn.txt:605–640` ("`C₁|a|₁^s ≤ |a|₂ ≤ C₂|a|₁^s` … where `s` is determined by `|ϖ|₂ = |ϖ|₁^s` … Swapping `|−|₁` and `|−|₂` we get a similar inequality"); [SRC] `08_BaseChange.norm_comparison_of_common_uniformizer`; decomposition L7.3–L7.5.',
 'The upper bound for a continuous ring **homomorphism** (bijectivity unused); `‖e ϖ‖ < 1` **derived** rather than assumed; the exponent explicit (`Real.logb`), so each lemma has one conclusion. `NormOneClass` on both rings.')
cleanup('CLEANUP-10','NormComparison.lean','T027','Final per-file cleanup for `NormComparison.lean`.')
