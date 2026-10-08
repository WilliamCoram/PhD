# -*- coding: utf-8 -*-
"""Ticket data for the board `tauceti-np-layer1`, part B (Normed … Examples), plus the cleanup tables and the
board order. Imported by tickets_data.py."""

NO = 'Normed.lean'
PA = 'Padic.lean'
LS = 'LaurentSeries.lean'
EX = 'Extension.lean'
PC = 'PadicComplex.lean'
EXA = 'Examples.lean'

T = []

def t(**kw):
    T.append(kw)

SRC_NOTE = "[SRC] is read-only: port with the new names, never `import PhD.Main.*`."

# ---------------------------------------------------------------- G7 Normed
t(id='T025', title='The norm of a normed field is the rank-one `hom` of `NormedField.valuation`', file=NO, deps='CLEANUP-10',
  par='yes (with T036–T038)', typ='lemmas', leaves='L6.1–L6.3',
  decls=[(NO, 'addVal_apply_of_ne_zero'), (NO, 'valuation_norm_eq'), (NO, 'norm_eq_coe_hom')],
  sketch="""1. `Valuation.RankOne.addVal_apply_of_ne_zero` (field): `h : RankOne.hom v (v.restrict x) ≠ 0` by `rw [Ne,
   RankOne.hom_eq_zero_iff, v.restrict_eq_zero_iff, v.zero_iff]; exact hx`; `rw [addVal_apply,
   NNReal.toRealMultZero_of_ne_zero h, WithZero.negLog_exp]; rfl` (`Valuation.norm_def`).
2. `valuation_norm_eq`: `rw [Valuation.norm_def, Valuation.restrict_def]`; `show ((embedding (restrict₀ (.ofClass
   (valuation (K := K))) x) : ℝ≥0) : ℝ) = ‖x‖` (the `RankOne` instance's `hom'` is `ValueGroup₀.embedding`);
   `rw [MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀]; rfl` (`valuation_apply`, `coe_nnnorm`).
3. `norm_eq_coe_hom`: `rw [← valuation_norm_eq K x]; rfl`.
[SRC] `Valued/AddVal.lean` `addVal_apply_of_ne_zero`, `valuation_norm_eq`, `norm_eq_coe_hom`.""",
  mathlib="`Valuation.norm_def`, `Valuation.restrict_def`, `Valuation.zero_iff`, `MonoidWithZeroHom.ValueGroup₀.embedding`, `MonoidWithZeroHom.ValueGroup₀.restrict₀`, `MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀`, `NormedField.valuation_apply`, `coe_nnnorm`.",
  sources="[RM] §1.2.2 (Q6.1), Mathlib's `NormedField.valuation` and its `RankOne` instance (Q6.6); decomposition L6.1–L6.3. " + SRC_NOTE,
  gen="`[NontriviallyNormedField K] [IsUltrametricDist K]` (the `RankOne` instance needs nontriviality); L6.1 for any rank-one valuation on a field.")

t(id='T026', title='`normAddVal`: zero, `eq_top`, `-log ‖x‖`, the defining equivalence, order reversal', file=NO, deps='T025',
  par='yes (with T036–T038)', typ='lemmas', leaves='L6.4–L6.8',
  decls=[(NO, 'normAddVal_zero'), (NO, 'normAddVal_eq_top'), (NO, 'normAddVal_apply_of_ne_zero'), (NO, 'exists_normAddVal_eq_and_norm_eq_exp_neg'), (NO, 'normAddVal_le_normAddVal')],
  sketch="""1. `normAddVal_zero`: `AddValuation.map_zero _`.
2. `normAddVal_eq_top`: `rw [normAddVal, RankOne.addVal_eq_top, Valuation.zero_iff]`.
3. `normAddVal_apply_of_ne_zero`: `rw [normAddVal, RankOne.addVal_apply_of_ne_zero _ hx, valuation_norm_eq]`.
4. `exists_normAddVal_eq_and_norm_eq_exp_neg`: `refine ⟨-Real.log ‖x‖, normAddVal_apply_of_ne_zero K hx, ?_⟩; rw
   [neg_neg, Real.exp_log (norm_pos_iff.mpr hx)]`.
5. `normAddVal_le_normAddVal`: `show (RankOne.realValuation _).addVal x ≤ _ ↔ _`; `rw [Valuation.addVal_le_addVal]`;
   `RankOne.realValuation v y ≤ RankOne.realValuation v x ↔ v y ≤ v x` is `(NNReal.toRealMultZero_strictMono.comp
   (RankOne.strictMono _)).le_iff_le` after unfolding `Valuation.map` (`rfl`); then `Valuation.restrict_le_iff`,
   `valuation_apply`, `NNReal.coe_le_coe`, `coe_nnnorm`.
[SRC] `normAddVal_zero`, `normAddVal_apply_of_ne_zero`.""",
  mathlib="`AddValuation.map_zero`, `Valuation.zero_iff`, `Real.exp_log`, `norm_pos_iff`, `neg_neg`, `StrictMono.le_iff_le`, `Valuation.restrict_le_iff`, `NNReal.coe_le_coe`, `coe_nnnorm`, `Valuation.RankOne.strictMono`.",
  sources="[RM] §1.2.2 (Q6.1), §1.2.3 (Q6.2, 'the defining equivalence'); [Kob84] III §4 (Q6.5); decomposition L6.4–L6.8. " + SRC_NOTE,
  gen="As T025.")

t(id='T027', title='`normAddVal` is the unique additive valuation with `‖x‖ = exp (-(v x))`', file=NO, deps='T026',
  par='yes (with T036–T038)', typ='theorem', leaves='L6.9',
  decls=[(NO, 'normAddVal_unique')],
  sketch="""1. `refine AddValuation.ext fun x ↦ ?_`; `rcases eq_or_ne x 0 with rfl | hx`.
2. Zero: `rw [AddValuation.map_zero, normAddVal_zero]`.
3. Nonzero: `obtain ⟨r, hr, hxr⟩ := hw x hx`; `hr' : r = -Real.log ‖x‖ := by have := congrArg Real.log hxr; rw
   [Real.log_exp] at this; linarith`; `rw [hr, hr', normAddVal_apply_of_ne_zero K hx]`.
(New: decomposition L6.9.)""",
  mathlib="`AddValuation.ext`, `AddValuation.map_zero`, `Real.log_exp`.",
  sources="[RM] §1.2.3 (Q6.2, 'the unique additive valuation into `WithTop ℝ` satisfying it'); decomposition L6.9.",
  gen="As T025; `w` arbitrary.")

t(id='T028', title='`normAddValZ`: zero, `eq_top`, the characterisation `‖x‖ = ‖π‖ ^ k`, `normAddValZ π = 1`', file=NO, deps='CLEANUP-11',
  par='yes (with T036–T038)', typ='lemmas', leaves='L6.10–L6.13',
  decls=[(NO, 'normAddValZ_zero'), (NO, 'normAddValZ_eq_top'), (NO, 'normAddValZ_eq_iff_of_isUniformizer'), (NO, 'normAddValZ_isUniformizer')],
  sketch="""1. `normAddValZ_zero`: `AddValuation.map_zero _`.
2. `normAddValZ_eq_top`: `rw [normAddValZ, IsRankOneDiscrete.addValZ_eq_top, Valuation.zero_iff]`.
3. `normAddValZ_eq_iff_of_isUniformizer`: `rw [normAddValZ, IsRankOneDiscrete.addValZ_eq_iff_of_isUniformizer _ hπ,
   valuation_apply, valuation_apply, ← NNReal.coe_inj, NNReal.coe_zpow, coe_nnnorm, coe_nnnorm]`.
4. `normAddValZ_isUniformizer`: `IsRankOneDiscrete.addValZ_isUniformizer _ hπ`.
[SRC] `normAddValZ_zero`.""",
  mathlib="`Valuation.zero_iff`, `NormedField.valuation_apply`, `NNReal.coe_inj`, `NNReal.coe_zpow`, `coe_nnnorm`.",
  sources="[RM] §1.3.4 (Q6.3), §1.3.2 (Q5.2) read through the norm; [Kob84] III §3 (Q5.4); decomposition L6.10–L6.13. " + SRC_NOTE,
  gen="`[(valuation (K := K)).IsRankOneDiscrete]` as an instance hypothesis, to be supplied by `Padic.lean` (and by any discretely valued normed field).")

t(id='T029', title='Norm recovery in the discrete case and the square `ℤ → ℝ`', file=NO, deps='T028',
  par='yes (with T036–T038)', typ='theorems', leaves='L6.14–L6.16',
  decls=[(NO, 'norm_eq_zpow_neg_normAddValZ'), (NO, 'norm_eq_zpow_neg_normAddValZ_of_isUniformizer'), (NO, 'normAddVal_eq_map_normAddValZ')],
  sketch="""1. `norm_eq_zpow_neg_normAddValZ`: `rw [norm_eq_coe_hom K x, IsRankOneDiscrete.hom_eq_zpow_neg_addValZ _ he hgen
   hd, NNReal.coe_zpow]` ([SRC] verbatim).
2. `norm_eq_zpow_neg_normAddValZ_of_isUniformizer`: `rw [(normAddValZ_eq_iff_of_isUniformizer K hπ x d).mp hd, hπe,
   inv_zpow', zpow_neg]` (check the direction of `inv_zpow'`: `a⁻¹ ^ n = a ^ (-n)`).
3. `normAddVal_eq_map_normAddValZ`: `rcases eq_or_ne x 0 with rfl | hx` (zero: `normAddVal_zero, normAddValZ_zero,
   WithTop.map_top`); `obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp ((normAddValZ_eq_top K).not.mpr hx)`; `rw [←
   hd, WithTop.map_coe, normAddVal_apply_of_ne_zero K hx, (normAddValZ_eq_iff_of_isUniformizer K hπ x d).mp hd.symm,
   Real.log_zpow]; congr 1; ring`.
[SRC] `norm_eq_zpow_neg_normAddValZ`; the other two are new.""",
  mathlib="`NNReal.coe_zpow`, `inv_zpow'`, `zpow_neg`, `WithTop.ne_top_iff_exists`, `WithTop.map_top`, `WithTop.map_coe`, `Real.log_zpow`.",
  sources="[RM] §1.3.4 (Q6.3), §1.3.3 (Q5.3), §1.4.5 (Q4.5 pattern); [Kob84] I §2 (Q5.6); [Gou20] p. 56 (Q4.7); decomposition L6.14–L6.16. " + SRC_NOTE,
  gen="`e : ℝ≥0`, `e ≠ 0` for the generator form; `e : ℝ` pinned by `‖π‖ = e⁻¹` for the uniformiser form (no positivity hypothesis).")

t(id='T030', title='`normAddValQ`: zero, `eq_top`, `normAddValQ π = 1`, the workhorse read off norms', file=NO, deps='T029',
  par='yes (with T036–T038)', typ='lemmas', leaves='L6.17–L6.20',
  decls=[(NO, 'normAddValQ_zero'), (NO, 'normAddValQ_eq_top'), (NO, 'normAddValQ_self'), (NO, 'normAddValQ_eq_of_pow_eq_pow')],
  sketch="""1. `normAddValQ_zero`: `AddValuation.map_zero _`.
2. `normAddValQ_eq_top`: `rw [normAddValQ, addValQ_eq_top, Valuation.zero_iff]`.
3. `normAddValQ_self`: `Valuation.addValQ_self _ _`.
4. `normAddValQ_eq_of_pow_eq_pow`: `refine addValQ_eq_of_pow_eq_pow _ π ((Valuation.ne_zero_iff _).mpr hx) hn ?_`;
   `rw [valuation_apply, valuation_apply, ← NNReal.coe_inj]; push_cast; exact h` (`NNReal.coe_pow`, `coe_nnnorm`).
[SRC] `normAddValQ_zero`, `normAddValQ_self`.""",
  mathlib="`Valuation.zero_iff`, `Valuation.ne_zero_iff`, `NormedField.valuation_apply`, `NNReal.coe_inj`, `NNReal.coe_pow`, `coe_nnnorm`.",
  sources="[RM] §1.4.6 (Q6.4), §1.4.2–§1.4.3 (Q4.2, Q4.3); decomposition L6.17–L6.20. " + SRC_NOTE,
  gen="`[(valuation (K := K)).IsCommensurable π]` as an instance hypothesis.")

t(id='T031', title='`‖x‖ = ‖π‖ ^ q`, and the squares `ℚ → ℝ`, `ℤ → ℚ` read off the norm', file=NO, deps='CLEANUP-12',
  par='yes (with T036–T038)', typ='theorems', leaves='L6.21–L6.23',
  decls=[(NO, 'norm_eq_norm_rpow_normAddValQ'), (NO, 'normAddVal_eq_map_normAddValQ'), (NO, 'normAddValQ_eq_map_normAddValZ')],
  sketch="""1. `norm_eq_norm_rpow_normAddValQ`: `rw [norm_eq_coe_hom K x, norm_eq_coe_hom K π]; exact
   Valuation.RankOne.hom_eq_rpow_addValQ _ π hq` ([SRC] verbatim).
2. `normAddVal_eq_map_normAddValQ`: `have := Valuation.RankOne.addVal_eq_map_addValQ (valuation (K := K)) π x`; `rwa
   [← norm_eq_coe_hom K π] at this` (unfold `normAddVal`, `normAddValQ`).
3. `normAddValQ_eq_map_normAddValZ`: `Valuation.addValQ_eq_map_addValZ _ hπ x`.
[SRC] `norm_eq_norm_rpow_normAddValQ`.""",
  mathlib="(none beyond T019, T023, T025.)",
  sources="[RM] §1.4.6 (Q6.4), §1.4.5 (Q4.5); decomposition L6.21–L6.23. " + SRC_NOTE,
  gen="As T030; the `ℤ → ℚ` square additionally assumes discreteness and a uniformiser.")

# ---------------------------------------------------------------- G8 Padic
t(id='T032', title='`ℚ_p`: the norm of `p`, and the value group is generated by `‖p‖₊`', file=PA, deps='CLEANUP-13',
  par='yes (with T039–T044)', typ='lemmas', leaves='L7.1–L7.4',
  decls=[(PA, 'nnnorm_p_eq_inv'), (PA, 'nnnorm_p_ne_zero'), (PA, 'nnnorm_p_zpow_valuation'), (PA, 'zpowers_valueGroupGen')],
  sketch="""1. `nnnorm_p_eq_inv`: `rw [← NNReal.coe_inj]; push_cast; exact Padic.norm_p`.
2. `nnnorm_p_ne_zero`: `rw [nnnorm_p_eq_inv]; exact inv_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)`.
3. `nnnorm_p_zpow_valuation`: `rw [← NNReal.coe_inj]; push_cast; rw [Padic.norm_eq_zpow_neg_valuation hx,
   Padic.norm_eq_zpow_neg_valuation (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero), Padic.valuation_p, ←
   zpow_mul]; ring_nf` ([SRC] `padic_norm_zpow_valuation`).
4. `zpowers_valueGroupGen`: `rw [Subgroup.eq_top_iff']; intro y; rw [Subgroup.mem_zpowers_iff]`; `hy : (y : ℝ≥0ˣ).val
   ∈ Units.val '' valueGroup _ := ⟨y, y.2, rfl⟩`; `rw [MonoidWithZeroHom.valueGroup_eq_range] at hy`; `obtain ⟨⟨x,
   hx⟩, hne⟩ := hy`; `hx0 : x ≠ 0` (else `‖0‖₊ = 0`, contradicting `hne`); `refine ⟨x.valuation, Subtype.ext
   (Units.ext ?_)⟩`; `rw [SubgroupClass.coe_zpow, Units.val_zpow_eq_zpow_val, show ((valueGroupGen (p := p)) :
   ℝ≥0ˣ).val = ‖(p : ℚ_[p])‖₊ from rfl, nnnorm_p_zpow_valuation hx0, ← hx]; rfl` ([SRC] `padic_zpowers_gen`).""",
  mathlib="`Padic.norm_p`, `Padic.norm_eq_zpow_neg_valuation`, `Padic.valuation_p`, `NNReal.coe_inj`, `inv_ne_zero`, `Nat.cast_ne_zero`, `Nat.Prime.ne_zero`, `Fact.out`, `zpow_mul`, `Subgroup.eq_top_iff'`, `Subgroup.mem_zpowers_iff`, `MonoidWithZeroHom.valueGroup_eq_range`, `SubgroupClass.coe_zpow`, `Units.val_zpow_eq_zpow_val`, `Subtype.ext`, `Units.ext`.",
  sources="[RM] §1.3.5 (Q7.1, 'value group generated by `‖p‖₊ = p⁻¹`'); [Kob84] I §2 (Q7.2); Mathlib `Padic` (Q7.3); decomposition L7.1–L7.4. " + SRC_NOTE,
  gen="`p` any prime (`[Fact p.Prime]`).")

t(id='T033', title='`ℚ_p` is discretely valued; `p` is a uniformiser and a normalising element', file=PA, deps='T032',
  par='yes (with T039–T044)', typ='instances + theorems', leaves='L7.5–L7.9',
  decls=[(PA, 'isCyclic_valueGroup'), (PA, 'isRankOneDiscrete_valuation'), (PA, 'coe_generator_eq'), (PA, 'isUniformizer_p'), (PA, 'isCommensurable_p')],
  sketch="""1. `isCyclic_valueGroup`: `isCyclic_iff_exists_zpowers_eq_top.mpr ⟨valueGroupGen, zpowers_valueGroupGen⟩`.
2. `isRankOneDiscrete_valuation`: `inferInstance` (`Valuation.IsRankOneDiscrete.mk'` with `isCyclic_valueGroup` and
   Mathlib's `Nontrivial (valueGroup …)` from `IsNontrivial`, part of the `RankOne` instance of
   `NormedField.valuation`). If instance search fails, provide `Nontrivial` explicitly: `⟨valueGroupGen, 1, fun h ↦
   absurd (congrArg (fun z ↦ ((z : ℝ≥0ˣ) : ℝ≥0)) h) (by simpa [valueGroupGen, nnnorm_p_eq_inv] using …)⟩` as in [SRC].
3. `coe_generator_eq`: `h : generator' (valuation) = valueGroupGen := LinearOrderedCommGroup.Subgroup.genLTOne_unique_of_zpowers_eq
   (generator'_lt_one _) (valueGroupGen_lt_one) (by rw [generator'_zpowers_eq_top, zpowers_valueGroupGen])` where
   `valueGroupGen_lt_one : valueGroupGen < 1` is `‖p‖₊ < 1` (`Padic.norm_p_lt_one`, `Subtype.coe_lt_coe`,
   `Units.val_lt_val`); then `rw [← nnnorm_p_eq_inv]; exact congrArg (fun z : valueGroup _ ↦ ((z : ℝ≥0ˣ) : ℝ≥0)) h`
   (`embedding_generator'`). ([SRC] `padic_generator'_eq`, `padic_generator_eq`.)
4. `isUniformizer_p`: `rw [Valuation.IsUniformizer.iff, valuation_apply]; exact_mod_cast (nnnorm_p_eq_inv.trans
   coe_generator_eq.symm)` (as `ℝ≥0` values; `Units.val` injective).
5. `isCommensurable_p`: `Valuation.IsRankOneDiscrete.isCommensurable _ isUniformizer_p`.""",
  mathlib="`isCyclic_iff_exists_zpowers_eq_top`, `Valuation.IsRankOneDiscrete.mk'`, `LinearOrderedCommGroup.Subgroup.genLTOne_unique_of_zpowers_eq`, `Valuation.IsRankOneDiscrete.generator'_lt_one`, `Valuation.IsRankOneDiscrete.generator'_zpowers_eq_top`, `Valuation.IsRankOneDiscrete.embedding_generator'`, `Valuation.IsUniformizer.iff`, `Padic.norm_p_lt_one`, `Subtype.coe_lt_coe`, `Units.val_lt_val`, `NormedField.valuation_apply`.",
  sources="[RM] §1.3.5 (Q7.1); [Gou20] 6.4.4 (`π = p` when `e = 1`, Q5.5); decomposition L7.5–L7.9. " + SRC_NOTE,
  gen="`p` any prime. `isCyclic_valueGroup` and `isCommensurable_p` are instances; `isRankOneDiscrete_valuation` is a theorem (the instance is `mk'`).")

t(id='T034', title='`‖x‖ = p ^ (-normAddValZ x)` and `normAddValZ ℚ_[p] x = Padic.addValuation x`', file=PA, deps='T033',
  par='yes (with T039–T044)', typ='theorems', leaves='L7.10, L7.11',
  decls=[(PA, 'norm_eq_zpow_neg_normAddValZ_padic'), (PA, 'normAddValZ_padic_apply')],
  sketch="""1. `norm_eq_zpow_neg_normAddValZ_padic`: `exact norm_eq_zpow_neg_normAddValZ_of_isUniformizer ℚ_[p]
   Padic.isUniformizer_p Padic.norm_p hd` (`‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹`).
2. `normAddValZ_padic_apply`: `by_cases hx : x = 0`. `subst hx; rw [normAddValZ_zero, AddValuation.map_zero]`. Else
   `obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp ((normAddValZ_eq_top ℚ_[p]).not.mpr hx)`; `rw [← hd,
   Padic.addValuation.apply hx]; congr 1`; `hn1 := norm_eq_zpow_neg_normAddValZ_padic hd.symm`; `hn2 :=
   Padic.norm_eq_zpow_neg_valuation hx`; `hpp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt`;
   `have := (zpow_right_strictMono₀ hpp).injective (hn1.symm.trans hn2); omega` ([SRC] `normAddValZ_padic`).""",
  mathlib="`Padic.norm_p`, `Padic.norm_eq_zpow_neg_valuation`, `Padic.addValuation.apply`, `AddValuation.map_zero`, `WithTop.ne_top_iff_exists`, `zpow_right_strictMono₀`, `Nat.Prime.one_lt`.",
  sources="[RM] §1.3.5 (Q7.1); [Kob84] I §2 (Q7.2); decomposition L7.10–L7.11. " + SRC_NOTE,
  gen="`p` any prime.")

t(id='T035', title='`normAddValZ ℚ_[p] = Padic.addValuation` as additive valuations', file=PA, deps='CLEANUP-ALL-3',
  par='no', typ='theorem', leaves='L7.12',
  milestone='M3 — `NormedField.normAddValZ_padic` ([RM] §1.3.5): the general construction reproduces Mathlib\'s `p`-adic valuation. `#print axioms` must be standard.',
  decls=[(PA, 'normAddValZ_padic')],
  sketch="""1. `AddValuation.ext normAddValZ_padic_apply`.""",
  mathlib="`AddValuation.ext`.",
  sources="[RM] §1.3.5 (Q7.1, 'as additive valuations'); decomposition L7.12.",
  gen="`p` any prime.")

# ---------------------------------------------------------------- G9 LaurentSeries
t(id='T036', title='The `X`-adic valuation of a nonzero Laurent series is `exp (-order)`', file=LS, deps='CLEANUP-10',
  par='yes (with T025–T031)', typ='theorem', leaves='L8.1',
  decls=[(LS, 'valuation_eq_exp_neg_order')],
  sketch="""1. `conv_lhs => rw [← f.single_order_mul_powerSeriesPart]`; `rw [map_mul, LaurentSeries.valuation_single_zpow]`.
2. `hF : Valued.v (f.powerSeriesPart : LaurentSeries K) = 1`: `le_antisymm ((PowerSeries.idealX K).valuation_le_one _)
   ?_`; for `1 ≤ v F`: by contradiction `h : v F < 1`; in `ℤᵐ⁰`, `v F ≠ 0` (`F ≠ 0`: its constant coefficient is
   `f.coeff f.order ≠ 0` by `LaurentSeries.powerSeriesPart_coeff f 0` and `HahnSeries.coeff_order_eq_zero.not.mpr hf`),
   so `v F = exp k` with `k < 0` (`WithZero.exp_log`, `WithZero.exp_lt_exp`), i.e. `k ≤ -1` and `v F ≤ exp (-1)`
   (`WithZero.exp_le_exp`, `Int.lt_iff_add_one_le`); then `(LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero K F
   (d := 1)).mp this 0 zero_lt_one : PowerSeries.coeff 0 F = 0`, contradiction.
3. `rw [hF, mul_one]`.
(New; the Mathlib file states only the `≤` characterisation, decomposition L8.1.)""",
  mathlib="`LaurentSeries.single_order_mul_powerSeriesPart`, `LaurentSeries.valuation_single_zpow`, `LaurentSeries.powerSeriesPart_coeff`, `LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero`, `IsDedekindDomain.HeightOneSpectrum.valuation_le_one`, `HahnSeries.coeff_order_eq_zero`, `WithZero.exp_log`, `WithZero.exp_lt_exp`, `WithZero.exp_le_exp`, `Int.lt_iff_add_one_le`, `map_mul`, `mul_one`, `le_antisymm`.",
  sources="[RM] §1.3.5 (Q8.1) and Examples ('the order of vanishing'); Mathlib docstring (Q8.2); [BGR] 1.5.2 Prop. 1 (Q8.3); decomposition L8.1.",
  gen="Any field `K` (the roadmap's `𝔽_q` is an instance); stated for `Valued.v`, not a norm (plan D1).")

t(id='T037', title='The `X`-adic valuation is discrete; its generator is `exp (-1)`; `X` is a uniformiser', file=LS, deps='T036',
  par='yes (with T025–T031)', typ='instance + theorems', leaves='L8.2–L8.4',
  decls=[(LS, 'isRankOneDiscrete_valued'), (LS, 'generator_valued_eq'), (LS, 'isUniformizer_X')],
  sketch="""1. `isRankOneDiscrete_valued`: first try `inferInstance`. Otherwise `Valuation.IsRankOneDiscrete.mk' _` after
   providing: `Nontrivial (valueGroup (.ofClass (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰)))` — from Mathlib's
   `Valuation.IsNontrivial ((PowerSeries.idealX K).valuation (LaurentSeries K))` (`LaurentSeries.valuation_def` is
   `rfl`, so `inferInstanceAs` works) through the `IsNontrivial → Nontrivial valueGroup` instance; and `IsCyclic
   (valueGroup …)`: `haveI : IsCyclic (ℤᵐ⁰ˣ) := isCyclic_of_surjective WithZero.unitsWithZeroEquiv.symm
   WithZero.unitsWithZeroEquiv.symm.surjective` (with `isCyclic_multiplicative` for `Multiplicative ℤ`), then
   `Subgroup.isCyclic _`.
2. `generator_valued_eq`: `Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
   (LaurentSeries.valuation_surjective K)`.
3. `isUniformizer_X`: `rw [Valuation.IsUniformizer.iff, generator_valued_eq, Units.val_mk0]; simpa using
   LaurentSeries.valuation_X_pow K 1` (`pow_one`, `Nat.cast_one`, `PowerSeries.coe_pow`).
(New; decomposition L8.2–L8.4.)""",
  mathlib="`Valuation.IsRankOneDiscrete.mk'`, `LaurentSeries.valuation_def`, `LaurentSeries.valued`, `isCyclic_of_surjective`, `isCyclic_multiplicative`, `WithZero.unitsWithZeroEquiv`, `Subgroup.isCyclic`, `Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective`, `LaurentSeries.valuation_surjective`, `Valuation.IsUniformizer.iff`, `Units.val_mk0`, `LaurentSeries.valuation_X_pow`, `PowerSeries.coe_pow`.",
  sources="[RM] §1.3.5 (Q8.1, 'at the uniformiser `t`'); Mathlib (Q8.2); decomposition L8.2–L8.4.",
  gen="Any field `K`.")

t(id='T038', title='`addValZ` on Laurent series: `X ↦ 1`, `single s 1 ↦ s`, `f ↦ f.order`', file=LS, deps='T037',
  par='yes (with T025–T031)', typ='theorems', leaves='L8.5–L8.7',
  decls=[(LS, 'addValZ_X'), (LS, 'addValZ_single'), (LS, 'addValZ_eq_order')],
  sketch="""1. `addValZ_X`: `Valuation.IsRankOneDiscrete.addValZ_isUniformizer _ (isUniformizer_X K)`.
2. Helper (inline or private): `hX : Valued.v ((PowerSeries.X : PowerSeries K) : LaurentSeries K) = WithZero.exp (-1)`
   from `valuation_X_pow K 1`; and `hexp : ∀ s : ℤ, WithZero.exp (-s) = WithZero.exp (-1 : ℤ) ^ s` by `rw [←
   WithZero.exp_zsmul]; congr 1; simp` (`smul_neg`, `zsmul_one`/`mul_neg_one`).
3. `addValZ_single`: `Valuation.IsRankOneDiscrete.addValZ_eq_of_zpow _ (isUniformizer_X K) (by rw
   [LaurentSeries.valuation_single_zpow, hX, hexp])`.
4. `addValZ_eq_order`: same with `valuation_eq_exp_neg_order K hf` in place of `valuation_single_zpow`.
(New; decomposition L8.5–L8.7.)""",
  mathlib="`LaurentSeries.valuation_single_zpow`, `LaurentSeries.valuation_X_pow`, `WithZero.exp_zsmul`, `smul_neg`, `zsmul_one`.",
  sources="[RM] §1.3.5 and Examples (Q8.1); Mathlib (Q8.2); decomposition L8.5–L8.7.",
  gen="Any field `K`.")

# ---------------------------------------------------------------- G10 Extension
t(id='T039', title='Commensurability passes to the completion of a valued field', file=EX, deps='CLEANUP-13',
  par='yes (with T032–T035)', typ='theorem', leaves='L9.1',
  decls=[(EX, 'isCommensurable_completion')],
  sketch="""1. `refine ⟨?_, ?_, fun x hx ↦ ?_⟩`; the first two: `rw [Valued.valuedCompletion_apply]` and use the instance's
   `val_pos`, `val_lt_one` (`Valued.v (π : Completion K) = Valued.v π`).
2. `obtain ⟨r, hr⟩ := Valued.exists_coe_eq_v x` — `hr : Valued.extensionValuation x = Valued.v r`, and `Valued.v x`
   on the completion is `Valued.extensionValuation x` by `rfl` (`Valued.valuedCompletion`'s `v` field); `hr0 : Valued.v r ≠ 0
   := hr ▸ hx`; `obtain ⟨m, n, hn, e⟩ := ‹hv.v.IsCommensurable π›.exists_zpow_eq r hr0`; `exact ⟨m, n, hn, by rw
   [show Valued.v x = Valued.v r from hr, Valued.valuedCompletion_apply, e]⟩`.
(New; decomposition L9.1.)""",
  mathlib="`Valued.exists_coe_eq_v`, `Valued.valuedCompletion_apply`, `Valued.valuedCompletion`, `Valued.extensionValuation`, `UniformSpace.Completion.coe'`.",
  sources="[RM] §1.5.3 (Q9.3); [Gou20] 6.8.7 / Lemma 3.2.10 and [BGR] 1.5.1 (Q9.8); [Kob84] III §4 (Q6.5); decomposition L9.1.",
  gen="Any `[Valued K Γ₀]` field with any `Γ₀` (no rank-one hypothesis; plan D3).")

t(id='T040', title='`normAddVal` of a normed algebra field restricts to `normAddVal` of the base', file=EX, deps='T039',
  par='yes (with T032–T035)', typ='theorem', leaves='L9.2',
  decls=[(EX, 'normAddVal_algebraMap')],
  sketch="""1. `rcases eq_or_ne x 0 with rfl | hx`; zero: `rw [map_zero, normAddVal_zero, normAddVal_zero]`.
2. Nonzero: `rw [normAddVal_apply_of_ne_zero L ((map_ne_zero (algebraMap K L)).mpr hx), normAddVal_apply_of_ne_zero K
   hx, norm_algebraMap']`.
(New; decomposition L9.2.)""",
  mathlib="`norm_algebraMap'`, `map_ne_zero`, `map_zero`.",
  sources="[RM] §1.5.1 (Q9.1); [BGR] 3.2.4/2 (Q9.6) for the spectral-norm reading; decomposition L9.2.",
  gen="Any ultrametric nontrivially normed `K`-algebra field `L` (no completeness or algebraicity: plan D4).")

t(id='T041', title='The ramification index exists and is positive; the image of a uniformiser is a normalising element', file=EX, deps='T040',
  par='yes (with T032–T035)', typ='theorems', leaves='L9.3, L9.5',
  decls=[(EX, 'exists_normAddValZ_algebraMap_eq'), (EX, 'isCommensurable_algebraMap_of_isRankOneDiscrete')],
  sketch="""1. `exists_normAddValZ_algebraMap_eq`: `hπ0 : algebraMap K L π ≠ 0 := (map_ne_zero _).mpr hπ.ne_zero`; `obtain ⟨d,
   hd⟩ := WithTop.ne_top_iff_exists.mp ((normAddValZ_eq_top L).not.mpr hπ0)`; `hv := (IsRankOneDiscrete.addValZ_eq_iff
   _ _ d).mp hd.symm : valuation (algebraMap K L π) = ↑(generator _ ^ d)`; `hlt : valuation (algebraMap K L π) < 1`
   by `valuation_apply`, `← NNReal.coe_lt_coe`, `norm_algebraMap'`, `hπ.val_lt_one` (via `valuation_apply` on `K`);
   `hd0 : 0 < d`: from `hv ▸ hlt : ↑(generator ^ d) < 1` → `generator ^ d < 1` in `Γ₀ˣ = ℝ≥0ˣ` (`Units.val_lt_val`) and
   `generator < 1` (`generator_lt_one`): `(zpow_lt_one_iff_right_of_lt_one₀ … ).mp` (on the group of units, or on
   `ℝ≥0` after `Units.val_zpow_eq_zpow_val`, using `generator_ne_zero` for positivity); `exact ⟨d.toNat, Int.toNat_pos.mpr
   hd0 ⊢ by omega, by rw [Int.toNat_of_nonneg hd0.le]; exact hd.symm⟩`.
2. `isCommensurable_algebraMap_of_isRankOneDiscrete`: `IsRankOneDiscrete.isCommensurable_of_lt_one _ ((map_ne_zero
   _).mpr hπ.ne_zero |> (Valuation.ne_zero_iff _).mpr) hlt` with `hlt` as above.
(New; decomposition L9.3, L9.5.)""",
  mathlib="`map_ne_zero`, `Valuation.IsUniformizer.ne_zero`, `Valuation.IsUniformizer.val_lt_one`, `WithTop.ne_top_iff_exists`, `Valuation.IsRankOneDiscrete.generator_lt_one`, `Valuation.IsRankOneDiscrete.generator_ne_zero`, `NNReal.coe_lt_coe`, `norm_algebraMap'`, `Units.val_lt_val`, `Units.val_zpow_eq_zpow_val`, `zpow_lt_one_iff_right_of_lt_one₀`, `Int.toNat_of_nonneg`, `Valuation.ne_zero_iff`.",
  sources="[RM] §1.3.6 (Q9.4); [Gou20] 6.4.3 and [BGR] 3.1.3 (Q9.7); [Kob84] III §3 (Q5.4); decomposition L9.3, L9.5.",
  gen="Both discreteness hypotheses as instances; no finiteness (plan D2).")

t(id='T042', title='The ramification formula `normAddValZ L (algebraMap x) = e * normAddValZ K x`', file=EX, deps='CLEANUP-ALL-4',
  par='no', typ='theorem', leaves='L9.4',
  milestone='M4 — `NormedField.normAddValZ_algebraMap` ([RM] §1.3.6, with `e` defined by `he`). `#print axioms` must be standard.',
  decls=[(EX, 'normAddValZ_algebraMap')],
  sketch="""1. `rcases eq_or_ne x 0 with rfl | hx`; zero: `rw [map_zero, normAddValZ_zero, normAddValZ_zero, WithTop.map_top]`.
2. `obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ((normAddValZ_eq_top K).not.mpr hx)`; `rw [← hk, WithTop.map_coe]`.
3. `hxK : ‖x‖ = ‖π‖ ^ k := (normAddValZ_eq_iff_of_isUniformizer K hπ x k).mp hk.symm`; `hxL : ‖algebraMap K L x‖ =
   ‖algebraMap K L π‖ ^ k := by rw [norm_algebraMap', norm_algebraMap', hxK]`.
4. `hπL : valuation (algebraMap K L π) = ↑(generator _ ^ e) := (IsRankOneDiscrete.addValZ_eq_iff _ _ e).mp he`.
5. `refine (IsRankOneDiscrete.addValZ_eq_iff _ _ (e * k)).mpr ?_`; `rw [valuation_apply, ← NNReal.coe_inj, coe_nnnorm,
   hxL, ← coe_nnnorm, ← valuation_apply, hπL, NNReal.coe_zpow, ← Units.val_zpow_eq_zpow_val, ← zpow_mul]`; finish
   with `Units.val_zpow_eq_zpow_val`/`NNReal.coe_zpow` so both sides read `((generator : ℝ≥0) : ℝ) ^ (e * k)`.
(New; decomposition L9.4 — the prose is [Kob84]'s `m = e · ord_p x`.)""",
  mathlib="`WithTop.ne_top_iff_exists`, `WithTop.map_top`, `WithTop.map_coe`, `norm_algebraMap'`, `NNReal.coe_inj`, `NNReal.coe_zpow`, `coe_nnnorm`, `Units.val_zpow_eq_zpow_val`, `zpow_mul`, `map_zero`.",
  sources="[RM] §1.3.6 (Q9.4); [Kob84] III §3 (Q5.4, `m = e·ord_p x`); [Gou20] 6.4.3 (Q9.7); decomposition L9.4.",
  gen="`e : ℤ` pinned by `he` (positive by T041); no finiteness, completeness or algebraicity (plan D2).")

t(id='T043', title='`normAddValZ L` is `e` times `normAddValQ L` normalised at the uniformiser of `K`', file=EX, deps='T042',
  par='no', typ='theorem', leaves='L9.6',
  decls=[(EX, 'map_intCast_normAddValZ_eq_map_normAddValQ')],
  sketch="""1. `he_pos : 0 < e`: as in T041 step 1 from `he` (`addValZ_eq_iff`, `‖algebraMap π‖ < 1`, `generator < 1`).
2. `rcases eq_or_ne y 0 with rfl | hy`; zero: `rw [normAddValZ_zero, normAddValQ_zero, WithTop.map_top, WithTop.map_top]`.
3. `obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp ((normAddValZ_eq_top L).not.mpr hy)`; `hyv := (IsRankOneDiscrete.addValZ_eq_iff
   _ _ d).mp hd.symm`; `hπv := (IsRankOneDiscrete.addValZ_eq_iff _ _ e).mp he`.
4. `hpow : valuation y ^ e = valuation (algebraMap K L π) ^ d := by rw [hyv, hπv, ← Units.val_zpow_eq_zpow_val, ←
   Units.val_zpow_eq_zpow_val, ← zpow_mul, ← zpow_mul, mul_comm]`.
5. `rw [← hd, WithTop.map_coe, normAddValQ, addValQ_eq_of_zpow _ _ ((Valuation.ne_zero_iff _).mpr hy) he_pos hpow,
   WithTop.map_coe, WithTop.coe_inj]`; `field_simp`/`mul_div_cancel₀ _ (by exact_mod_cast he_pos.ne' : (e : ℚ) ≠ 0)`.
(New; decomposition L9.6.)""",
  mathlib="`WithTop.ne_top_iff_exists`, `WithTop.map_top`, `WithTop.map_coe`, `WithTop.coe_inj`, `Units.val_zpow_eq_zpow_val`, `zpow_mul`, `mul_comm`, `Valuation.ne_zero_iff`, `mul_div_cancel₀`.",
  sources="[RM] §1.3.6 (Q9.4, second sentence); decomposition L9.6.",
  gen="As T042; the `IsCommensurable` instance on `L` is a hypothesis (T041 derives it).")

t(id='T044', title='`‖x‖ ^ n = ‖a₀‖` for the minimal polynomial; commensurability is inherited by algebraic extensions; `normAddValQ` restricts', file=EX, deps='T043',
  par='no', typ='theorem + instance + theorem', leaves='L9.7–L9.9',
  decls=[(EX, 'norm_pow_natDegree_minpoly'), (EX, 'isCommensurable_algebraMap'), (EX, 'normAddValQ_algebraMap')],
  sketch="""1. `norm_pow_natDegree_minpoly`: `rw [NormedAlgebra.norm_eq_spectralNorm K x, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow,
   one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x)).ne']`
   (the `IsUltrametricDist K` instance is what `NormedAlgebra.norm_eq_spectralNorm` needs; `K` complete).
2. `isCommensurable_algebraMap`: `refine ⟨?_, ?_, fun x hx ↦ ?_⟩`; `val_pos`/`val_lt_one` via `valuation_apply`,
   `nnnorm_algebraMap'` and the instance on `K`. For `x`: `hx0 : x ≠ 0 := (Valuation.ne_zero_iff _).mp hx`; `set n :=
   (minpoly K x).natDegree`, `hn : 0 < n := minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x)`; `a₀ := (minpoly K
   x).coeff 0`, `ha₀ : a₀ ≠ 0 := minpoly.coeff_zero_ne_zero (Algebra.IsIntegral.isIntegral x) hx0`; `obtain ⟨m, k, hk, e⟩
   := ‹(valuation (K := K)).IsCommensurable π›.exists_zpow_eq a₀ ((Valuation.ne_zero_iff _).mpr ha₀)`; `hxn : ‖x‖₊ ^ n =
   ‖a₀‖₊ := by rw [← NNReal.coe_inj]; push_cast; exact norm_pow_natDegree_minpoly x`; `refine ⟨m, n * k, mul_pos
   (Nat.cast_pos.mpr hn) hk, ?_⟩`; `rw [valuation_apply, valuation_apply, nnnorm_algebraMap', zpow_mul, zpow_natCast,
   hxn]; exact_mod_cast e` (the instance on `K` is stated with `valuation_apply`-free `v`; unfold with `valuation_apply`).
3. `normAddValQ_algebraMap`: `rcases eq_or_ne x 0 with rfl | hx` (zero: `map_zero`, `normAddValQ_zero` twice);
   `obtain ⟨m, n, hn, e⟩ := ‹_›.exists_zpow_eq x ((Valuation.ne_zero_iff _).mpr hx)`; `e' : valuation (algebraMap K L x)
   ^ n = valuation (algebraMap K L π) ^ m := by rw [valuation_apply, valuation_apply, nnnorm_algebraMap',
   nnnorm_algebraMap']; exact e`; `rw [normAddValQ, normAddValQ, addValQ_eq_of_zpow _ _ (by simpa using hx) hn e',
   addValQ_eq_of_zpow _ _ _ hn e]`.
(New; decomposition L9.7–L9.9; the `[CompleteSpace K] [Algebra.IsAlgebraic K L]` binders are the D1 repair.)""",
  mathlib="`NormedAlgebra.norm_eq_spectralNorm`, `spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow`, `Real.rpow_inv_natCast_pow`, `minpoly.natDegree_pos`, `minpoly.coeff_zero_ne_zero`, `Algebra.IsIntegral.isIntegral`, `norm_nonneg`, `one_div`, `nnnorm_algebraMap'`, `NormedField.valuation_apply`, `Valuation.ne_zero_iff`, `NNReal.coe_inj`, `zpow_mul`, `zpow_natCast`, `Nat.cast_pos`, `mul_pos`, `map_zero`.",
  sources="[RM] §1.5.2 (Q9.2; route through BGR 3.2.4/3 = Q9.5 rather than the `i`-th coefficient); [BGR] 3.2.4/2 (Q9.6); [Kob84] III §2 (Q9.9); [Gou20] 6.3.4–6.3.5; decomposition L9.7–L9.9.",
  gen="`[CompleteSpace K] [Algebra.IsAlgebraic K L]` explicit on each declaration (D1); `L` any ultrametric nontrivially normed `K`-algebra field (the spectral norm by Mathlib's uniqueness), so `PadicAlgCl p` is an instance.")

# ---------------------------------------------------------------- G11 PadicComplex
t(id='T045', title='Every algebraic ultrametric normed `ℚ_p`-algebra field is commensurable at `p`; the algebraic closure of `ℚ_p`', file=PC, deps='CLEANUP-15, CLEANUP-18',
  par='no', typ='instance + theorem', leaves='L10.1, L10.2',
  decls=[(PC, 'isCommensurable_natCast_prime'), (PC, 'isCommensurable_p', 0)],
  sketch="""1. `isCommensurable_natCast_prime`: `have := NormedField.isCommensurable_algebraMap (K := ℚ_[p]) (L := L) (p : ℚ_[p])`
   (instances: `Padic.isCommensurable_p`, `CompleteSpace ℚ_[p]`); `rwa [map_natCast] at this`.
2. `PadicAlgCl.isCommensurable_p`: `inferInstance` (step 1 with `L := PadicAlgCl p`; Mathlib's `PadicAlgCl.normedAlgebra`,
   `PadicAlgCl.isAlgebraic`, `PadicAlgCl.nontriviallyNormedField`, `PadicAlgCl.isUltrametricDist`).
(New; decomposition L10.1–L10.2.)""",
  mathlib="`map_natCast`, `PadicAlgCl.normedAlgebra`, `PadicAlgCl.isAlgebraic`, `PadicAlgCl.nontriviallyNormedField`, `PadicAlgCl.isUltrametricDist`.",
  sources="[RM] §1.5.4 (Q10.1, first half) via §1.5.2 (Q9.2); [Kob84] III §3 (Q10.3); decomposition L10.1–L10.2.",
  gen="`L` any algebraic ultrametric nontrivially normed `ℚ_p`-algebra field; the instance's element is `(p : L)` (a `Nat.cast`), so instance search finds it on `(p : PadicAlgCl p)`.")

t(id='T046', title='`ℂ_p`: the extended valuation is `‖·‖₊`; `ℂ_p` is commensurable at `p`', file=PC, deps='T045',
  par='no', typ='theorems + instance', leaves='L10.3–L10.5',
  decls=[(PC, 'valuation_eq_nnnorm'), (PC, 'normedField_valuation_eq'), (PC, 'isCommensurable_p', 1)],
  sketch="""1. `valuation_eq_nnnorm`: `rw [← NNReal.coe_inj, coe_nnnorm, PadicComplex.norm_eq_norm x, Valuation.norm_def,
   PadicComplex.RankOne.hom_eq_embedding, Valuation.embedding_restrict]`.
2. `normedField_valuation_eq`: `Valuation.ext fun x ↦ by rw [NormedField.valuation_apply, valuation_eq_nnnorm]`.
3. `isCommensurable_p`: `h₀ : (Valued.v : Valuation (PadicAlgCl p) ℝ≥0).IsCommensurable (p : PadicAlgCl p) :=
   PadicAlgCl.isCommensurable_p` (`PadicAlgCl.valued` is `NormedField.toValued`, so `Valued.v = NormedField.valuation`
   by `rfl`; if needed `Valuation.IsCommensurable.of_forall_eq _ _ fun x ↦ PadicAlgCl.valuation_def x`); `h₁ :=
   Valued.isCommensurable_completion (K := PadicAlgCl p) (p : PadicAlgCl p)` (T039; `UniformSpace.Completion
   (PadicAlgCl p)` is `ℂ_[p]` by `abbrev`); `rw [normedField_valuation_eq]`; `simpa only [PadicComplex.coe_natCast,
   PadicComplex.coe_eq] using h₁` (the element `((p : PadicAlgCl p) : ℂ_[p]) = (p : ℂ_[p])`).
(New; decomposition L10.3–L10.5.)""",
  mathlib="`PadicComplex.norm_eq_norm`, `PadicComplex.RankOne.hom_eq_embedding`, `Valuation.norm_def`, `Valuation.embedding_restrict`, `NNReal.coe_inj`, `coe_nnnorm`, `Valuation.ext`, `NormedField.valuation_apply`, `PadicAlgCl.valuation_def`, `PadicAlgCl.valued`, `PadicComplex.valued`, `PadicComplex.coe_natCast`, `PadicComplex.coe_eq`, `PadicComplex.valuation_extends`.",
  sources="[RM] §1.5.4 (Q10.1) via §1.5.3 (Q9.3); [Gou20] 6.8.6–6.8.7 (Q10.4); [Kob84] III §4 (Q10.3); Mathlib `PadicComplex` (Q10.5); decomposition L10.3–L10.5.",
  gen="`p` any prime; the seam `Valued.v = NormedField.valuation` on `ℂ_[p]` is a theorem, not an assumption.")

t(id='T047', title='`normAddValQ ℂ_[p] p`: `p ↦ 1`, restriction to `ℚ_p` is `Padic.addValuation`, `‖x‖ = p ^ (-q)`', file=PC, deps='T046',
  par='no', typ='theorems', leaves='L10.6–L10.8',
  decls=[(PC, 'normAddValQ_p'), (PC, 'normAddValQ_algebraMap_padic'), (PC, 'norm_eq_rpow_neg_normAddValQ')],
  sketch="""1. `normAddValQ_p`: `normAddValQ_self _ _`.
2. `normAddValQ_algebraMap_padic`: `rcases eq_or_ne x 0 with rfl | hx` (zero: `map_zero`, `normAddValQ_zero`,
   `AddValuation.map_zero`, `WithTop.map_top`); `rw [Padic.addValuation.apply hx, WithTop.map_coe]`; `hp : ‖(p : ℂ_[p])‖₊
   = ‖(p : ℚ_[p])‖₊ := by rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p])]; exact PadicComplex.nnnorm_extends' _` (or
   `nnnorm_algebraMap'`); `hxv : valuation (algebraMap ℚ_[p] ℂ_[p] x) ^ (1 : ℤ) = valuation (p : ℂ_[p]) ^ x.valuation
   := by rw [zpow_one, valuation_apply, valuation_apply, nnnorm_algebraMap', hp, Padic.nnnorm_p_zpow_valuation hx]`;
   `rw [normAddValQ, addValQ_eq_of_zpow _ _ (by simpa using hx) one_pos hxv]; norm_num`.
3. `norm_eq_rpow_neg_normAddValQ`: `rw [norm_eq_norm_rpow_normAddValQ _ _ hq]`; `hp : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
   rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]`; `rw [hp, Real.inv_rpow (by
   positivity), ← Real.rpow_neg (by positivity)]`.
(New; decomposition L10.6–L10.8.)""",
  mathlib="`Padic.addValuation.apply`, `Padic.norm_p`, `PadicComplex.nnnorm_extends'`, `nnnorm_algebraMap'`, `norm_algebraMap'`, `map_natCast`, `zpow_one`, `WithTop.map_top`, `WithTop.map_coe`, `AddValuation.map_zero`, `Real.inv_rpow`, `Real.rpow_neg`, `NormedField.valuation_apply`.",
  sources="[RM] §1.5.4 (Q10.1); [Gou20] 6.8.7 (Q10.4); decomposition L10.6–L10.8.",
  gen="`p` any prime.")

t(id='T048', title='Every rational is a value; the value group of `ℂ_p` is exactly `p^ℚ`', file=PC, deps='CLEANUP-ALL-5',
  par='no', typ='theorems', leaves='L10.9, L10.10',
  milestone='M5 — `PadicComplex.range_normAddValQ` with `PadicComplex.isCommensurable_p` ([RM] §1.5.4–§1.5.5, convention 8). `#print axioms` must be standard on both.',
  decls=[(PC, 'exists_normAddValQ_eq'), (PC, 'range_normAddValQ')],
  sketch="""1. `exists_normAddValQ_eq`: `hb : 0 < q.den := q.den_pos`; `obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((p : ℂ_[p])
   ^ q.num) hb`; `hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero` (`CharZero ℂ_[p]`); `hz0 : z ≠
   0 := fun h ↦ by simp [h, zpow_ne_zero q.num hp0] at hz` (`zero_pow hb.ne'`); `hv : valuation z ^ (q.den : ℤ) =
   valuation (p : ℂ_[p]) ^ q.num := by rw [zpow_natCast, ← map_pow, hz, map_zpow₀]`; `refine ⟨z, hz0, ?_⟩`; `rw
   [normAddValQ, addValQ_eq_of_zpow _ _ (by simpa using hz0) (by exact_mod_cast hb) hv, Rat.num_div_den]`.
2. `range_normAddValQ`: `ext y; simp only [Set.mem_range, Set.mem_insert_iff]`; `constructor`; `rintro ⟨x, rfl⟩`:
   `rcases eq_or_ne x 0 with rfl | hx`: `left; exact normAddValQ_zero _ _`; `right; obtain ⟨r, hr⟩ :=
   WithTop.ne_top_iff_exists.mp ((normAddValQ_eq_top _ _).not.mpr hx); exact ⟨r, hr⟩`. Converse: `rintro (rfl | ⟨r,
   rfl⟩)`: `⟨0, normAddValQ_zero _ _⟩`; `obtain ⟨x, -, hx⟩ := exists_normAddValQ_eq r; exact ⟨x, hx⟩`.
(New; decomposition L10.9–L10.10.)""",
  mathlib="`IsAlgClosed.exists_pow_nat_eq`, `PadicComplex.isAlgClosed`, `Rat.den_pos`, `Rat.num_div_den`, `Nat.cast_ne_zero`, `zpow_ne_zero`, `zero_pow`, `zpow_natCast`, `map_pow`, `map_zpow₀`, `Set.mem_range`, `Set.mem_insert_iff`, `WithTop.ne_top_iff_exists`.",
  sources="[RM] §1.5.5 (Q10.2); [Kob84] III §4 and Exercise 1 (Q10.3); [Gou20] 6.8.7 (Q10.4); decomposition L10.9–L10.10.",
  gen="`p` any prime.")

# ---------------------------------------------------------------- G12 Examples
t(id='T049', title='`ℚ_p` examples: `normAddValZ p = 1`, `normAddValZ (1/p²) = -2`, `normAddVal = log p · normAddValZ`', file=EXA, deps='CLEANUP-16, CLEANUP-20',
  par='no', typ='theorems', leaves='L11.1–L11.3',
  decls=[(EXA, 'normAddValZ_padic_p'), (EXA, 'normAddValZ_padic_inv_p_sq'), (EXA, 'normAddVal_padic')],
  sketch="""1. `normAddValZ_padic_p`: `normAddValZ_isUniformizer _ Padic.isUniformizer_p`.
2. `normAddValZ_padic_inv_p_sq`: `hp : (p : ℚ_[p]) ≠ 0`; `rw [normAddValZ_padic_apply, Padic.addValuation.apply
   (inv_ne_zero (pow_ne_zero 2 hp)), Padic.valuation_inv, Padic.valuation_pow, Padic.valuation_p]; norm_num`.
3. `normAddVal_padic`: `rw [normAddVal_eq_map_normAddValZ ℚ_[p] Padic.isUniformizer_p x]; congr 1; funext k; rw
   [Padic.norm_p, Real.log_inv, neg_neg]`.
(decomposition L11.1–L11.3.)""",
  mathlib="`Padic.addValuation.apply`, `Padic.valuation_inv`, `Padic.valuation_pow`, `Padic.valuation_p`, `Padic.norm_p`, `Real.log_inv`, `inv_ne_zero`, `pow_ne_zero`, `neg_neg`.",
  sources="[RM] Layer 1 Examples (Q11.1); [Kob84] I §2 (Q5.6, Q11.2-style computations); decomposition L11.1–L11.3.",
  gen="`p` any prime.")

t(id='T050', title='`√p` and `∛p` examples: `normAddValQ = 1/2`, `normAddValZ p = 2`, `normAddValQ ℂ_[p] p (∛p) = 1/3`', file=EXA, deps='T049',
  par='no', typ='theorems', leaves='L11.4–L11.6',
  decls=[(EXA, 'normAddValQ_of_sq_eq_prime'), (EXA, 'normAddValZ_prime_of_sq_eq_prime'), (EXA, 'normAddValQ_padicComplex_of_pow_three')],
  sketch="""1. `normAddValQ_of_sq_eq_prime`: `hp : (p : L) ≠ 0 := by rw [← map_natCast (algebraMap ℚ_[p] L)]; exact (map_ne_zero
   _).mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)`; `hs0 : s ≠ 0 := fun h ↦ hp (by rw [← hs, h, zero_pow
   two_ne_zero])`; `have := normAddValQ_eq_of_pow_eq_pow L (p : L) hs0 two_pos (m := 1) (by rw [← norm_pow, hs,
   pow_one])`; `simpa using this` (`Nat.cast_one`, `one_div`).
2. `normAddValZ_prime_of_sq_eq_prime`: `rw [← hs, AddValuation.map_pow, h1, two_nsmul, one_add_one_eq_two]`.
3. `normAddValQ_padicComplex_of_pow_three`: as step 1 with `n = 3`, `hp : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr …`
   (`CharZero ℂ_[p]`), `norm_pow`, `pow_one`.
(decomposition L11.4–L11.6.)""",
  mathlib="`map_natCast`, `map_ne_zero`, `Nat.cast_ne_zero`, `zero_pow`, `norm_pow`, `pow_one`, `two_pos`, `AddValuation.map_pow`, `two_nsmul`, `one_add_one_eq_two`, `PadicComplex.charZero`.",
  sources="[RM] Layer 1 Examples (Q11.1); [Gou20] Problems 242–244 (computations in `ℚ_5(√2)`, `ℚ_5(√5)`); decomposition L11.4–L11.6; plan D6 for the `ℚ_p(√p)` reading.",
  gen="Any algebraic ultrametric nontrivially normed `ℚ_p`-algebra field `L` with an `s` such that `s ^ 2 = p` (plan D6).")

t(id='T051', title='Laurent series example: `addValZ (X ^ n) = n`', file=EXA, deps='T050',
  par='no', typ='theorem', leaves='L11.7',
  decls=[(EXA, 'addValZ_X_pow')],
  sketch="""1. `rw [AddValuation.map_pow, LaurentSeries.addValZ_X]`; the goal `n • (1 : WithTop ℤ) = ((n : ℤ) : WithTop ℤ)`:
   `rw [nsmul_eq_mul, mul_one]; norm_cast` (`WithTop.coe_natCast`).
(decomposition L11.7.)""",
  mathlib="`AddValuation.map_pow`, `nsmul_eq_mul`, `mul_one`, `WithTop.coe_natCast`.",
  sources="[RM] Layer 1 Examples (Q11.1, `𝔽_q⸨t⸩`); decomposition L11.7.",
  gen="Any field `K`.")

# ---------------------------------------------------------------- G13 gate
t(id='T052', title='Chain root: build the whole Tau Ceti chain and run the full gate', file='PhD/TauCeti.lean', deps='CLEANUP-2, CLEANUP-3, CLEANUP-4, CLEANUP-5, CLEANUP-8, CLEANUP-10, CLEANUP-13, CLEANUP-15, CLEANUP-16, CLEANUP-18, CLEANUP-20, CLEANUP-21 (every final per-file cleanup)',
  par='no', typ='gate', leaves='(all)',
  decls=[],
  statement_override="""-- PhD/TauCeti.lean already imports the board's leaf:
import PhD.TauCeti.Code.NewtonPolygons.AddVal.Examples
-- Gate (no new declaration): the whole chain builds, the layer is sorry-free, axioms are standard.""",
  sketch="""1. `grep -rn "sorry" PhD/TauCeti/Code/NewtonPolygons/AddVal/` must be empty.
2. `lake build PhD.TauCeti` (the CI gate of the chain; never `lake build PhD`) must pass with no warnings from the
   twelve `AddVal` modules.
3. `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.AddVal.<Module>` for each of the twelve modules: clean.
4. A scratch file importing the leaf with `#print axioms` on the five milestones (`Valuation.addVal_map`,
   `Valuation.addValQ_unique`, `NormedField.normAddValZ_padic`, `NormedField.normAddValZ_algebraMap`,
   `PadicComplex.range_normAddValQ`) and on `PadicComplex.isCommensurable_p`: only `propext`, `Classical.choice`,
   `Quot.sound`.
5. Confirm no file imports `PhD.Main.*` (`grep -rn "import PhD.Main" PhD/TauCeti/` empty).""",
  mathlib="(none.)",
  sources="[RM] 'Existing Lean work' (the `#print axioms` gate the roadmap asks CI to run); `plan.md` worker protocol.",
  gen="n/a.")

# ---------------------------------------------------------------- cleanups and order
CLEAN = {
 'CLEANUP-1': ('NegLog.lean', 'T003', 'mid'), 'CLEANUP-2': ('NegLog.lean', 'T004', 'final'),
 'CLEANUP-3': ('RatLog.lean', 'T006', 'final'),
 'CLEANUP-4': ('Basic.lean', 'T009', 'final'),
 'CLEANUP-5': ('RankOne.lean', 'T011', 'final'),
 'CLEANUP-6': ('Commensurable.lean', 'T014', 'mid'), 'CLEANUP-7': ('Commensurable.lean', 'T017', 'mid'), 'CLEANUP-8': ('Commensurable.lean', 'T019', 'final'),
 'CLEANUP-9': ('Discrete.lean', 'T022', 'mid'), 'CLEANUP-10': ('Discrete.lean', 'T024', 'final'),
 'CLEANUP-11': (NO, 'T027', 'mid'), 'CLEANUP-12': (NO, 'T030', 'mid'), 'CLEANUP-13': (NO, 'T031', 'final'),
 'CLEANUP-14': (PA, 'T034', 'mid'), 'CLEANUP-15': (PA, 'T035', 'final'),
 'CLEANUP-16': (LS, 'T038', 'final'),
 'CLEANUP-17': (EX, 'T041', 'mid'), 'CLEANUP-18': (EX, 'T044', 'final'),
 'CLEANUP-19': (PC, 'T047', 'mid'), 'CLEANUP-20': (PC, 'T048', 'final'),
 'CLEANUP-21': (EXA, 'T051', 'final'),
}
ALL = {
 'CLEANUP-ALL-1': ('T008, CLEANUP-2, CLEANUP-3', 'M1 (T009)',
   '`NegLog.lean`, `RatLog.lean`, `Basic.lean` (so far).'),
 'CLEANUP-ALL-2': ('T016, CLEANUP-5, CLEANUP-6', 'M2 (T017)',
   '`RankOne.lean`, `Commensurable.lean` (so far) and everything they import.'),
 'CLEANUP-ALL-3': ('CLEANUP-14, CLEANUP-10, CLEANUP-13', 'M3 (T035)',
   '`Discrete.lean`, `Normed.lean`, `Padic.lean` (so far).'),
 'CLEANUP-ALL-4': ('CLEANUP-17', 'M4 (T042)',
   '`Extension.lean` (so far) and every module it imports that changed since CLEANUP-ALL-3.'),
 'CLEANUP-ALL-5': ('CLEANUP-19, CLEANUP-15, CLEANUP-16', 'M5 (T048)',
   '`Padic.lean`, `LaurentSeries.lean`, `Extension.lean`, `PadicComplex.lean` (so far).'),
}
FINAL = {
 'deps': 'T052',
 'text': ("Final sweep of the twelve files of this board (`PhD/TauCeti/Code/NewtonPolygons/AddVal/*.lean`): naming "
          "against the [PR] names and Mathlib conventions, docstrings, import minimality by hand, module docstrings "
          "list the final declaration names, `omit` of unused section instances, `runLinter` clean on every module, "
          "`lake build PhD.TauCeti` passes, `#print axioms` standard on the five milestones. Then update the Status "
          "line of this file, add a 'Status' note at the head of the roadmap README's Layer 1 section (as Layer 0 and "
          "the RigidAnalyticGeometry layers have), and the memory entry of the board."),
}
ORDER = """T001 T002 T003 CLEANUP-1 T004 CLEANUP-2
T005 T006 CLEANUP-3
T007 T008 CLEANUP-ALL-1 T009 CLEANUP-4
T010 T011 CLEANUP-5
T012 T013 T014 CLEANUP-6 T015 T016 CLEANUP-ALL-2 T017 CLEANUP-7 T018 T019 CLEANUP-8
T020 T021 T022 CLEANUP-9 T023 T024 CLEANUP-10
T025 T026 T027 CLEANUP-11 T028 T029 T030 CLEANUP-12 T031 CLEANUP-13
T032 T033 T034 CLEANUP-14 CLEANUP-ALL-3 T035 CLEANUP-15
T036 T037 T038 CLEANUP-16
T039 T040 T041 CLEANUP-17 CLEANUP-ALL-4 T042 T043 T044 CLEANUP-18
T045 T046 T047 CLEANUP-19 CLEANUP-ALL-5 T048 CLEANUP-20
T049 T050 T051 CLEANUP-21
T052 CLEANUP-FINAL""".split()
