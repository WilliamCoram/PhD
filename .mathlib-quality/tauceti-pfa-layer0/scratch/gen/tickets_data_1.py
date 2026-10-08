# ---------------- G1 Sums ----------------
ticket('T001','Null families attain their largest norm','Sums.lean','none','yes (with G3, G4, G5, G11)','lemmas',
 'L1.1–L1.3',
 ['Filter.Tendsto.bddAbove_range_norm','Filter.Tendsto.exists_forall_norm_le','Filter.Tendsto.exists_norm_eq_iSup'],
 """1. `bddAbove_range_norm`: `have h := hf.norm; rw [norm_zero] at h; exact h.bddAbove_range_of_cofinite` — this
   exact proof compiles (`scratch/names2.lean`).
2. `exists_forall_norm_le`: obtain `i₁` from `Nonempty`. `by_cases h0 : ∀ i, ‖f i‖ ≤ ‖f i₁‖` — done with `i₁`.
   Otherwise take `i₂` with `‖f i₁‖ < ‖f i₂‖`, so `0 < ‖f i₂‖`. The set `{i | ‖f i₂‖ ≤ ‖f i‖}` is finite:
   `hf.norm.eventually (gt_mem_nhds _)` rewritten with `Filter.eventually_cofinite`, then `Set.Finite.subset`.
   Take a maximiser with `hfin.toFinset.exists_max_image (fun i ↦ ‖f i‖) ⟨i₂, by simp⟩`; for an index outside the
   set use `(not_le.1 _).le.trans`. The block is verbatim the inner part of `scratch/spot.lean`, which compiles.
3. `exists_norm_eq_iSup`: from 2, `le_antisymm (le_ciSup hf.bddAbove_range_norm i₀) (ciSup_le h)`.""",
 '`Filter.Tendsto.norm`, `Filter.Tendsto.bddAbove_range_of_cofinite`, `Filter.eventually_cofinite`, `gt_mem_nhds`, `Finset.exists_max_image`, `Set.Finite.toFinset`, `le_ciSup`, `ciSup_le`.',
 '[RM] §0.1.1–§0.1.2; decomposition L1.1–L1.3.',
 '`SeminormedAddCommGroup`, no ultrametric hypothesis (none is used). `Nonempty ι` replaces the roadmap\'s "some `f i ≠ 0`" — strictly weaker and necessary. In `Filter.Tendsto` for dot notation on `hf`.')
ticket('T002','The strict bound and the unique dominant term','Sums.lean','T001','no','lemmas',
 'L1.4–L1.8',
 ['norm_tsum_lt_of_forall_lt','nnnorm_tsum_lt_of_forall_lt','norm_tsum_eq_of_forall_lt','nnnorm_tsum_eq_of_forall_lt','norm_tsum_sub_tsum_le'],
 """1. `norm_tsum_lt_of_forall_lt`: `by_cases hs : Summable f`. Not summable: `tsum_eq_zero_of_not_summable`,
   `norm_zero`, `hB`. Summable: `ι` empty → `tsum_empty`/`simpa using hB`; otherwise `hs.tendsto_cofinite_zero`,
   T001's `exists_forall_norm_le` gives `i₀`, and
   `(IsUltrametricDist.norm_tsum_le f).trans_lt ((ciSup_le h).trans_lt (hlt i₀))`. **Full proof compiles in
   `scratch/spot.lean`** — copy it, replacing the inlined maximiser by T001.
2. `nnnorm_…lt`: `exact_mod_cast norm_tsum_lt_of_forall_lt (B := B) (by exact_mod_cast hB) (fun i ↦ by exact_mod_cast hlt i)`.
3. `norm_tsum_eq_of_forall_lt`: `classical`; `rw [hf.tsum_eq_add_tsum_ite i₀]`. Let `g i := if i = i₀ then 0 else f i`.
   If `‖f i₀‖ = 0`: `hlt` makes `ι` a subsingleton at `i₀` (any other `i` would have `‖f i‖ < 0`), so `g ≡ 0`,
   `tsum_zero`, `add_zero`. If `0 < ‖f i₀‖`: step 1 with `B := ‖f i₀‖` gives `‖∑' g‖ < ‖f i₀‖` (each `‖g i‖` is `0`
   or `‖f i‖`), then `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt _)` and `max_eq_left`.
4. `nnnorm_…eq`: `NNReal.eq`, step 3 with the hypotheses cast.
5. `norm_tsum_sub_tsum_le`: `rw [← hf.tsum_sub hg]; exact IsUltrametricDist.norm_tsum_le _`.""",
 '`tsum_eq_zero_of_not_summable`, `Summable.tendsto_cofinite_zero`, `IsUltrametricDist.norm_tsum_le`, `Summable.tsum_eq_add_tsum_ite`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, `Summable.tsum_sub`, `NNReal.coe_lt_coe`, `coe_nnnorm`.',
 '[RM] §0.1.2–§0.1.3, §0.1.5; [Sch] `schneider.txt:625`; [SRC] `LWX/05_Sharpness.{norm_tsum_lt_of_forall_lt, norm_tsum_eq_of_forall_lt}`; decomposition L1.4–L1.8.',
 'The strict bound carries **no** nullity or summability hypothesis (weaker than [RM] and [SRC]; proved). The dominant-term lemma takes `Summable f`, not "null + complete": equivalent in a complete group and necessary in general. `NormedAddCommGroup` from step 3 on (`tsum_eq_add_tsum_ite` needs `T2`).')
ticket('T003','Null families on a product','Sums.lean','T002','no','lemmas',
 'L1.9–L1.13',
 ['Filter.Tendsto.iSup_norm_cofinite_left','Filter.Tendsto.iSup_norm_cofinite_right','tendsto_cofinite_prod_of_tendsto_iSup_norm','tendsto_tsum_cofinite_left','tendsto_tsum_cofinite_right'],
 """1. `iSup_norm_cofinite_left`: `rw [Metric.tendsto_nhds]; intro ε hε`; with `F := {p | ε / 2 ≤ ‖f p‖}` finite
   (from `hf`, as in T001), show `∀ᶠ i in cofinite, …` by `Filter.eventually_cofinite` and
   `(hF.image Prod.fst).subset`: for `i ∉ Prod.fst '' F`, every `‖f (i, j)‖ < ε / 2`, so
   `⨆ j, ‖f (i, j)‖ ≤ ε / 2 < ε` — `ciSup_le` when `κ` is nonempty, `Real.iSup_of_isEmpty` otherwise; finish with
   `Real.dist_0_eq_abs`, `abs_of_nonneg (Real.iSup_nonneg fun _ ↦ norm_nonneg _)`.
2. `_right`: step 1 applied to `f ∘ Prod.swap` (nullity of the swap: `hf.comp (Equiv.prodComm κ ι).injective.tendsto_cofinite`).
3. `tendsto_cofinite_prod_of_tendsto_iSup_norm`: for `ε > 0`, `I := {i | ε ≤ ⨆ j, ‖f (i, j)‖}` is finite by `h₂`; for
   `i ∈ I`, `Jᵢ := {j | ε ≤ ‖f (i, j)‖}` is finite by `h₁ i`. `{p | ε ≤ ‖f p‖} ⊆ ⋃ i ∈ I, (fun j ↦ (i, j)) '' Jᵢ`, using
   `le_ciSup (h₁ i).bddAbove_range_norm j`. `Set.Finite.biUnion`, `Set.Finite.image`.
4. `tendsto_tsum_cofinite_left`: `squeeze_zero_norm (fun i ↦ IsUltrametricDist.norm_tsum_le _) hf.iSup_norm_cofinite_left`.
5. `_right`: same with step 2.""",
 '`Metric.tendsto_nhds`, `Filter.eventually_cofinite`, `Set.Finite.image`, `Set.Finite.biUnion`, `ciSup_le`, `Real.iSup_of_isEmpty`, `Real.iSup_nonneg`, `le_ciSup`, `squeeze_zero_norm`, `Function.Injective.tendsto_cofinite`, `IsUltrametricDist.norm_tsum_le`.',
 '[RM] §0.1.4–§0.1.5; decomposition L1.9–L1.13 (L1.11 records why both hypotheses are necessary).',
 'Steps 1–3 for seminormed groups with no ultrametric hypothesis; steps 4–5 need `IsUltrametricDist` but **no completeness** (a non-summable row contributes `0`).')
cleanup('CLEANUP-1','Sums.lean','T003')
ticket('T004','Iterated sums of a null family','Sums.lean','CLEANUP-1','no','lemmas',
 'L1.14–L1.15',
 ['tsum_prod_eq_tsum_tsum','tsum_tsum_comm'],
 """1. `tsum_prod_eq_tsum_tsum`: `have hs : Summable f := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hf`;
   `exact hs.tsum_prod' fun i ↦ hs.prod_factor i`.
2. `tsum_tsum_comm`: `rw [← tsum_prod_eq_tsum_tsum hf]`; for the right side apply step 1 to
   `f ∘ Prod.swap` and `(Equiv.prodComm ι κ).tsum_eq`. Alternatively `Summable.tsum_comm'` with both families of
   fibres from `prod_factor`.""",
 '`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`, `Summable.tsum_prod\'`, `Summable.prod_factor`, `Equiv.tsum_eq`, `Summable.tsum_comm\'`, `IsUltrametricDist.nonarchimedeanAddGroup` (instance).',
 '[RM] §0.1.4; decomposition L1.14–L1.15.',
 '`[NormedAddCommGroup E] [IsUltrametricDist E] [CompleteSpace E]`; completeness is necessary (summability).')
ticket('T005','Bounded biadditive maps and sums','Sums.lean','T004','no','lemmas',
 'L1.16–L1.18',
 ['tendsto_cofinite_prod_of_norm_le_mul','summable_prod_map₂','tsum_prod_map₂'],
 """1. `tendsto_cofinite_prod_of_norm_le_mul`: `squeeze_zero_norm (fun p ↦ hb _ _)`; it remains that
   `p ↦ ‖f p.1‖ * ‖g p.2‖ → 0` cofinitely. Bounds `C_f`, `C_g` from T001. For `ε > 0`:
   `{p | ε ≤ ‖f p.1‖ * ‖g p.2‖} ⊆ {i | ε / (C_g + 1) ≤ ‖f i‖} ×ˢ {j | ε / (C_f + 1) ≤ ‖g j‖}` (if both factors were
   small the product would be `< ε`); `Set.Finite.prod`.
2. `summable_prod_map₂`: step 1 with `hf.tendsto_cofinite_zero`, `hg.tendsto_cofinite_zero`, then
   `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`.
3. `tsum_prod_map₂`: `rw [tsum_prod_eq_tsum_tsum (step 1)]`. Inner sum: `b (f i) : F →+ G` is continuous by
   `AddMonoidHomClass.continuous_of_bound (b (f i)) ‖f i‖ (hb (f i))`, so `(hg.hasSum.map (b (f i)) _).tsum_eq`.
   Outer sum: the same for `b.flip (∑' j, g j)` with bound `‖∑' g‖` (`mul_comm`).""",
 '`squeeze_zero_norm`, `Set.Finite.prod`, `Summable.tendsto_cofinite_zero`, `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`, `AddMonoidHomClass.continuous_of_bound`, `HasSum.map`, `HasSum.tsum_eq`, `AddMonoidHom.flip`.',
 '[RM] §0.1.4 ("Mathlib\'s `tsum_mul_tsum_of_nonarchimedean` is the case of a ring, and the module form is what the matrix product of §2.6 needs"); decomposition L1.16–L1.18.',
 'Step 1 for an arbitrary function `b` with the norm bound (no additivity, no ultrametric). Step 3 for `b : H →+ F →+ G` — biadditive, no scalars: covers `•`, `*`, and the matrix product. `H`, `F` need be neither ultrametric nor complete; `G` both.')
cleanup('CLEANUP-2','Sums.lean','T005','Final per-file cleanup for `Sums.lean`.')
# ---------------- G2 UnitBall ----------------
ticket('T006','The closed unit ball as a subring: API','UnitBall.lean','none','yes','lemmas',
 'L2.1–L2.2',
 ['mem_unitClosedBall','norm_le_one','isOpen_unitClosedBall','isClosed_unitClosedBall'],
 """1. `mem_unitClosedBall`: `show x ∈ Metric.closedBall 0 1 ↔ _; exact mem_closedBall_zero_iff`.
2. `norm_le_one`: `mem_unitClosedBall.1 x.2`.
3. `isOpen_unitClosedBall`: `coe_unitClosedBall ▸ IsUltrametricDist.isOpen_closedBall 0 one_ne_zero`.
4. `isClosed_unitClosedBall`: `coe_unitClosedBall ▸ Metric.isClosed_closedBall`.""",
 '`mem_closedBall_zero_iff`, `IsUltrametricDist.isOpen_closedBall`, `Metric.isClosed_closedBall`.',
 '[RM] §0.2.1; [Sch] Lemma 1.2.i (`schneider.txt:184`); [Wed] Example 6.13 (`wedhorn.txt:2170`); decomposition L2.1–L2.2.',
 '`SeminormedRing` (no commutativity, no separation). The definition extends Mathlib\'s `Submonoid.unitClosedBall` (`unitClosedBall_toSubmonoid` is `rfl`).')
ticket('T007','Ball ideals of the unit ball','UnitBall.lean','T006','no','def fields + lemmas',
 'L2.3–L2.4',
 ['closedBallIdeal','openUnitBallIdeal','mem_closedBallIdeal','mem_openUnitBallIdeal','closedBallIdeal_mono','closedBallIdeal_one','closedBallIdeal_mul_le','closedBallIdeal_le_openUnitBallIdeal'],
 """1. Fill the four `sorry` proof fields of the two definitions. `add_mem'`: `(nnnorm_add_le_max _ _).trans (max_le ha hb)`
   (respectively `max_lt`). `smul_mem'`: `smul_eq_mul`, `Subring.coe_mul`,
   `(nnnorm_mul_le _ _).trans (mul_le_of_le_one_left (zero_le _) (norm_le_one r))` — the strict version with
   `lt_of_le_of_lt`.
2. `mem_*`: `Iff.rfl` after `NNReal.coe_le_coe` (`mem_closedBallIdeal` is stated with the real norm and `(ε : ℝ)`).
3. `mono`: `fun a ha ↦ le_trans ha h`. `one`: `eq_top_iff`, `norm_le_one`. `le_openUnitBallIdeal`: `lt_of_le_of_lt`.
4. `mul_le`: `Ideal.mul_le.2 fun a ha b hb ↦ _`, `nnnorm_mul_le`, `mul_le_mul'`.""",
 '`IsUltrametricDist.nnnorm_add_le_max`, `nnnorm_mul_le`, `Subring.coe_mul`, `Ideal.mul_le`, `eq_top_iff`, `NNReal.coe_le_coe`.',
 '[RM] §0.2.1, §0.4.5; [Buz07] `buzzard.txt:158`; decomposition L2.3–L2.4.',
 'Left ideals of `R⁰` for any `SeminormedRing`; radius `ε : ℝ≥0` so that no positivity proof is an argument of the definition. `openUnitBallIdeal` is separate because it is not a closed ball.')
ticket('T008','The topology of the unit ball','UnitBall.lean','T007','no','lemmas + instance',
 'L2.5–L2.8',
 ['isOpen_closedBallIdeal','isOpen_openUnitBallIdeal','hasBasis_nhds_zero_closedBallIdeal','instIsLinearTopologyUnitClosedBall','openUnitBallIdeal_le_topologicalNilradical','openUnitBallIdeal_eq_topologicalNilradical'],
 """1. Openness: the coercion `unitClosedBall R → R` is continuous; the carrier is the preimage of
   `Metric.closedBall 0 ε` (open by `IsUltrametricDist.isOpen_closedBall _ hε.ne'` with `ε` cast) respectively of
   `Metric.ball 0 1`. `IsOpen.preimage continuous_subtype_val`.
2. `hasBasis…`: `Metric.nhds_basis_closedBall` on the subtype (its metric is the restriction), reindexed from
   `ℝ` to `ℝ≥0` by `Filter.HasBasis.to_hasBasis` (`ε ↦ ⟨ε, _⟩`, `ε ↦ (ε : ℝ)`).
3. Instance: `IsLinearTopology.mk_of_hasBasis _ hasBasis_nhds_zero_closedBallIdeal` (check the exact argument
   order with `#check`; the ideals are submodules of `R⁰` over itself).
4. `le_topologicalNilradical`: `IsTopologicallyNilpotent.mem_topologicalNilradical_iff`; nullity of powers in the
   subtype from `tendsto_pow_atTop_nhds_zero_of_norm_lt_one` and `tendsto_subtype_rng`/`Subring.coe_pow`.
5. `eq_topologicalNilradical`: `le_antisymm` step 4 and, conversely, `‖aⁿ‖ = ‖a‖ⁿ` (`norm_pow`) tends to `0`, so
   `‖a‖ < 1` (`tendsto_pow_atTop_nhds_zero_iff` on `ℝ` with `abs_norm`).""",
 '`IsUltrametricDist.isOpen_closedBall`, `Metric.isOpen_ball`, `continuous_subtype_val`, `Metric.nhds_basis_closedBall`, `Filter.HasBasis.to_hasBasis`, `IsLinearTopology.mk_of_hasBasis`, `IsTopologicallyNilpotent.mem_topologicalNilradical_iff`, `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`, `tendsto_pow_atTop_nhds_zero_iff`, `norm_pow`.',
 '[RM] §0.2.1–§0.2.2; [Wed] Example 5.29(2) (`wedhorn.txt:1606`); decomposition L2.5–L2.8 (L2.8 records the counterexample `ε ∈ ℚ_p[ε]/(ε²)` without `NormMulClass`).',
 'The linear-topology instance for any `SeminormedRing`; the nilradical statements for `SeminormedCommRing` because Mathlib defines `topologicalNilradical` for commutative rings only.')
cleanup('CLEANUP-3','UnitBall.lean','T008')
ticket('T009','The Neumann series: ultrametric norms','UnitBall.lean','CLEANUP-3, T002','no','lemmas',
 'L2.9–L2.12',
 ['norm_one_sub_of_norm_lt_one','norm_tsum_geometric','norm_tsum_geometric_sub_one','isUnit_of_norm_one_sub_lt_one'],
 """1. `norm_one_sub_of_norm_lt_one`: `sub_eq_add_neg`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`
   (`‖1‖ = 1 ≠ ‖-x‖`), `max_eq_left`.
2. `norm_tsum_geometric`: T002's `norm_tsum_eq_of_forall_lt (summable_geometric_of_norm_lt_one h) (i₀ := 0)`; for
   `n ≠ 0`, `‖xⁿ‖ ≤ ‖x‖ⁿ < 1 = ‖x⁰‖` by `norm_pow_le' x (Nat.pos_of_ne_zero _)`, `pow_lt_one₀`; `pow_zero`, `norm_one`.
3. `norm_tsum_geometric_sub_one`: `x = 0`: `simp` (`tsum` of `0 ^ n`). `x ≠ 0`: `geom_series_succ x h` rewrites the left
   side as `‖∑' i, x ^ (i + 1)‖`; T002 at `i₀ = 0` with `‖x ^ (i + 2)‖ ≤ ‖x‖ ^ (i + 2) < ‖x‖` (`pow_lt_self_of_lt_one₀`
   or `mul_lt_of_lt_one_left`); summability by `(summable_geometric_of_norm_lt_one h).comp_injective`.
4. `isUnit_of_norm_one_sub_lt_one`: `x := 1 - a`; the inverse is `⟨∑' n, xⁿ, mem_unitClosedBall.2 (step 2).le⟩`;
   `mul_neg_geom_series`, `geom_series_mul_neg` with `1 - x = a`, in the subring by `Subtype.ext`.""",
 '`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, `summable_geometric_of_norm_lt_one`, `norm_pow_le\'`, `pow_lt_one₀`, `geom_series_succ`, `mul_neg_geom_series`, `geom_series_mul_neg`, `Summable.comp_injective`.',
 '[RM] §0.2.3 ("`‖(1 − x)⁻¹‖ = 1` and `‖(1 − x)⁻¹ − 1‖ = ‖x‖`; Mathlib\'s `Units.oneSub` is the unit, and the ultrametric equalities are new"); decomposition L2.9–L2.12.',
 '`NormedRing` (not commutative), `NormOneClass`, ultrametric; completeness only where the series is summed. Stated on `∑\' n, x ^ n`, which is definitionally the inverse of `Units.oneSub x h`.')
ticket('T010','Units of the unit ball and the Jacobson radical','UnitBall.lean','T009','no','lemmas',
 'L2.13–L2.14',
 ['isUnit_iff_isUnit_mk','openUnitBallIdeal_le_jacobson_bot'],
 """1. `isUnit_iff_isUnit_mk`: `⇒` `IsUnit.map`. `⇐`: obtain `b` with `mk a * mk b = 1` (surjectivity of
   `Ideal.Quotient.mk`), so `1 - a * b ∈ openUnitBallIdeal R` (`Ideal.Quotient.eq`), i.e. `‖1 - (a * b : R)‖ < 1`; T009
   gives `IsUnit (a * b)`; `isUnit_of_mul_isUnit_left`.
2. `openUnitBallIdeal_le_jacobson_bot`: `Ideal.mem_jacobson_bot.2 fun y ↦ _`; `x * y + 1` satisfies
   `‖1 - (x * y + 1)‖ = ‖x * y‖ ≤ ‖x‖ * ‖y‖ < 1`; T009.""",
 '`IsUnit.map`, `Ideal.Quotient.mk_surjective`, `Ideal.Quotient.eq`, `isUnit_of_mul_isUnit_left`, `Ideal.mem_jacobson_bot`, `norm_mul_le`.',
 '[RM] §0.2.3, **corrected** (erratum E2: the roadmap\'s "unique maximal ideal when the norm is multiplicative" is false — `ℚ_p⟨X⟩`); decomposition L2.13–L2.14; [SRC] `PowerBounded.isUnit_iff_isUnit_mk_topologicalNilradical`.',
 '`NormedCommRing` + complete: commutativity is used (quotient ring; a unit from a product).')
ticket('T011','The unit ball of a normed field is a local ring','UnitBall.lean','T010','yes (independent of T009–T010)','lemmas + instance',
 'L2.15',
 ['isUnit_iff_norm_eq_one','instIsLocalRingUnitClosedBall','maximalIdeal_unitClosedBall'],
 """1. `isUnit_iff_norm_eq_one`: `⇒`: `a * b = 1` in `K⁰` gives `‖a‖ * ‖b‖ = 1` with both `≤ 1`, so `‖a‖ = 1`
   (`mul_eq_one_iff_of_le_one`-style: `‖a‖ = ‖a‖ * 1 ≥ ‖a‖ * ‖b‖ = 1`). `⇐`: `a ≠ 0`, inverse `⟨(a : K)⁻¹, _⟩` with
   `norm_inv`, `inv_one`.
2. Instance: `IsLocalRing.of_nonunits_add`; nonunits are `‖·‖ < 1` by step 1 (`lt_of_le_of_ne`), closed under `+` by
   `norm_add_le_max`. Nontriviality of the subring from `NormOneClass`.
3. `maximalIdeal…`: `Ideal.ext`, `IsLocalRing.mem_maximalIdeal`, `mem_nonunits_iff`, step 1.""",
 '`norm_inv`, `IsLocalRing.of_nonunits_add`, `IsLocalRing.mem_maximalIdeal`, `mem_nonunits_iff`, `IsUltrametricDist.norm_add_le_max`.',
 '[Sch] Lemma 1.2 ii–iii (`schneider.txt:184`): "`m := {a ∈ K : |a| < 1}` is the unique maximal ideal of `o`; `o× = o ∖ m`"; [RM] §0.2.3 in its corrected field form; decomposition L2.15.',
 '`NormedField` with ultrametric norm; **no completeness** and no nontriviality of the valuation (then `K⁰ = K`, `K⁰⁰ = 0`, consistent).')
cleanup('CLEANUP-4','UnitBall.lean','T011','Final per-file cleanup for `UnitBall.lean`.')
# ---------------- G3 PowerBounded ----------------
ticket('T012','Norm-bounded sets are bounded','PowerBounded.lean','none','yes','lemmas',
 'L3.1–L3.2',
 ['isBounded_of_forall_norm_le','isPowerBounded_of_norm_pow_le','isPowerBounded_of_norm_le_one'],
 """1. `isBounded_of_forall_norm_le`: `intro U hU; obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU`; `C' := max C 0 + 1`;
   `V := Metric.ball 0 (ε / C')`; for `v ∈ V`, `s ∈ S`: `‖v * s‖ ≤ ‖v‖ * ‖s‖ < (ε / C') * C' = ε`
   (`Set.mul_subset_iff`, `mem_ball_zero_iff`).
2. `isPowerBounded_of_norm_pow_le`: step 1 on `Set.range (a ^ ·)` (`Set.forall_mem_range`).
3. `isPowerBounded_of_norm_le_one`: step 2 with `C := max ‖(1 : R)‖ 1`: `n = 0` gives `pow_zero`; `n + 1`:
   `norm_pow_le' a n.succ_pos` and `pow_le_one₀`.""",
 '`Metric.mem_nhds_iff`, `Set.mul_subset_iff`, `mem_ball_zero_iff`, `norm_mul_le`, `Set.forall_mem_range`, `norm_pow_le\'`, `pow_le_one₀`.',
 '[Wed] Definition 5.27 and Example 5.29(2) (`wedhorn.txt:1589, 1606`); [RM] §0.2.1; decomposition L3.0–L3.2. The two seam definitions are verbatim from mathlib4#40013 and must not be edited.',
 '`SeminormedRing`; **no `NormOneClass`** (`‖1‖` is a constant) — weaker than [SRC].')
ticket('T013','Bounded implies norm-bounded, for a multiplicative norm','PowerBounded.lean','T012','no','lemmas',
 'L3.3–L3.4',
 ['IsBounded.exists_norm_le','IsPowerBounded.norm_le_one','isPowerBounded_iff_norm_le_one'],
 """1. `IsBounded.exists_norm_le`: apply `hS` to `U := Metric.ball 0 1`; get `V ∈ 𝓝 0` with `V * S ⊆ U`. From
   `NeBot (𝓝[≠] 0)`: `V ∩ {0}ᶜ` is nonempty (`Filter.NeBot.nonempty_of_mem` with `inter_mem_nhdsWithin`), giving
   `v ∈ V`, `v ≠ 0`. For `s ∈ S`: `‖v‖ * ‖s‖ = ‖v * s‖ < 1` (`norm_mul`), so `‖s‖ ≤ ‖v‖⁻¹`.
2. `IsPowerBounded.norm_le_one`: by contradiction `1 < ‖a‖`; step 1 gives `C` with `‖a ^ n‖ ≤ C`; `‖a ^ (n+1)‖ = ‖a‖ ^ (n+1)`
   by induction from `norm_mul`; `tendsto_pow_atTop_atTop_of_one_lt` contradicts the bound.
3. iff: step 2 and T012.""",
 '`Filter.NeBot.nonempty_of_mem`, `inter_mem_nhdsWithin`, `norm_mul`, `tendsto_pow_atTop_atTop_of_one_lt`, `Filter.Tendsto.eventually_gt_atTop`.',
 '[Wed] Example 5.29(2) ("One has `A° = {x ∈ A ; |x| ≤ 1}`"); [RM] §0.2.2; decomposition L3.3–L3.4; [SRC] `ForMathlib/Analysis/Normed/Ring/PowerBounded`.',
 '`NormedRing` + `NormMulClass` + `NeBot (𝓝[≠] 0)`; both necessary (the two counterexamples are T043, T044). `NormOneClass` not assumed.')
ticket('T014','Topological nilpotency and the norm','PowerBounded.lean','T013','yes (independent of T012–T013)','lemmas',
 'L3.5',
 ['of_norm_lt_one','RE:^theorem norm_lt_one \\{R','isTopologicallyNilpotent_iff_norm_lt_one'],
 """1. `of_norm_lt_one`: `exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx` (`IsTopologicallyNilpotent` unfolds to this
   `Tendsto`; if the unfolding is not definitional use `IsTopologicallyNilpotent` `show`).
2. `norm_lt_one`: `hx.norm` gives `‖xⁿ‖ → 0`; `‖x ^ (n+1)‖ = ‖x‖ ^ (n+1)` (`norm_mul` induction); if `1 ≤ ‖x‖` the powers
   are `≥ 1`, contradiction with `eventually_lt_of_tendsto_lt`.
3. iff: `⟨norm_lt_one, of_norm_lt_one⟩`.""",
 '`tendsto_pow_atTop_nhds_zero_of_norm_lt_one`, `Filter.Tendsto.norm`, `norm_mul`, `one_le_pow₀`, `Filter.Tendsto.eventually_lt_const`.',
 '[Wed] Definition 5.25 and Example 5.29(2); [RM] §0.2.1–§0.2.2; decomposition L3.5.',
 '`of_norm_lt_one` for any `SeminormedRing`; the converse needs `NormMulClass` (not `NeBot`).')
cleanup('CLEANUP-5','PowerBounded.lean','T014','Final per-file cleanup for `PowerBounded.lean`. Do not rename or reshape the two seam definitions.')
