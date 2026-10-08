# -*- coding: utf-8 -*-
"""Ticket data for the board `tauceti-np-layer2`, part A (NormedAddValuation … Extension, T001–T038).
Statements are NOT stored here: the generator copies them verbatim from the skeleton (through
sorries.json). A ticket lists its sorried declarations as (file, name) or (file, name, occurrence), and
the non-sorry definitions it introduces as `defs=[(file, name)]`."""

NAV = 'NormedAddValuation.lean'
GE = 'Generic.lean'
CV = 'CoeffVal.lean'
PS = 'PowerSeries.lean'
PO = 'Polynomial.lean'
EX = 'Extension.lean'

T = []

def t(**kw):
    T.append(kw)

SRC_NOTE = ("[SRC] is read-only: port the idea to the `(v, e, b)` form, never `import PhD.Main.*`.")
DEC = "Decomposition entry: "

# ---------------------------------------------------------------- G1 NormedAddValuation
t(id='T001', title='`NormedAddValuation`: the additive-valuation API through `CoeFun`', file=NAV, deps='none',
  par='yes (with T010, T039)', typ='structure API', leaves='L1.1–L1.9',
  defs=[(NAV, 'NormedAddValuation')],
  decls=[(NAV, 'map_zero'), (NAV, 'map_one'), (NAV, 'map_mul'), (NAV, 'map_pow'), (NAV, 'map_inv'),
         (NAV, 'min_le_map_add'), (NAV, 'eq_top_iff'), (NAV, 'ne_top_iff'), (NAV, 'exists_eq_coe')],
  sketch="""The structure is already defined (no `sorry` in it); this ticket proves the nine one-line API lemmas.
1. `map_zero` … `min_le_map_add`: `v x` unfolds to `v.toAddValuation x` by `coe_apply` (`rfl`); each lemma is
   the corresponding `AddValuation` lemma: `AddValuation.map_zero`, `map_one`, `map_mul`, `map_pow`,
   `map_inv` (`WithTop Γ` is a `LinearOrderedAddCommGroupWithTop`), `map_add`.
2. `eq_top_iff`: `AddValuation.top_iff` on the field `K` (`[Nontrivial (WithTop Γ)]` is found).
   `ne_top_iff`: `AddValuation.ne_top_iff` (or `eq_top_iff.not`).
3. `exists_eq_coe`: `WithTop.ne_top_iff_exists.mp (v.ne_top_iff.mpr hx)`.
""" + DEC + "L1.1–L1.9.",
  mathlib="`AddValuation.map_zero`, `AddValuation.map_one`, `AddValuation.map_mul`, `AddValuation.map_pow`, `AddValuation.map_inv`, `AddValuation.map_add`, `AddValuation.top_iff`, `AddValuation.ne_top_iff`, `WithTop.ne_top_iff_exists`.",
  sources="[RM] Layer 2 introduction (Q-RM-intro); [RM] convention 5.",
  gen="`[NormedField K]` only (no ultrametric, no nontriviality instance): the structure's norm axiom forces ultrametricity (T002). `Γ` any `[AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]`; universe-polymorphic.")

t(id='T002', title='The base and the norm: `norm_eq_rpow`, `embed_eq_neg_logb`, ultrametricity, `rpow_logb`', file=NAV, deps='T001',
  par='yes (with T010, T039)', typ='lemmas', leaves='L1.10–L1.15',
  decls=[(NAV, 'base_pos'), (NAV, 'log_base_pos'), (NAV, 'norm_eq_rpow'), (NAV, 'embed_eq_neg_logb'),
         (NAV, 'norm_add_le_max'), (NAV, 'rpow_logb')],
  sketch="""1. `base_pos := zero_lt_one.trans v.one_lt_base`; `log_base_pos := Real.log_pos v.one_lt_base`.
2. `norm_eq_rpow := v.norm_eq_rpow' h`.
3. `embed_eq_neg_logb`: from `‖x‖ = b ^ (-e γ)` take `Real.logb b` of both sides:
   `Real.logb_rpow v.base_pos v.one_lt_base.ne'` gives `logb b ‖x‖ = -e γ`; `neg_neg`.
4. `norm_add_le_max`: if `x + y = 0` the left side is `0 ≤ max _ _` (`norm_nonneg`); otherwise obtain `γ` with
   `v (x + y) = γ` (`exists_eq_coe`). If `x = 0` or `y = 0` the claim is trivial (`zero_add`, `le_max_right`).
   Else `v x = γ₁`, `v y = γ₂`, `min γ₁ γ₂ ≤ γ` (`min_le_map_add`, `WithTop.coe_le_coe`, `WithTop.coe_min`), so
   `e γ ≥ min (e γ₁) (e γ₂)` (`v.strictMono_embed.monotone`, `Monotone.map_min`), hence
   `b ^ (-e γ) ≤ max (b ^ (-e γ₁)) (b ^ (-e γ₂))` by `Real.rpow_le_rpow_left_iff v.one_lt_base` and
   `neg_le_neg`; rewrite the three norms with `norm_eq_rpow`.
5. `rpow_logb := Real.rpow_logb v.base_pos v.one_lt_base.ne' hc`.
""" + DEC + "L1.10–L1.15.",
  mathlib="`zero_lt_one`, `Real.log_pos`, `Real.logb_rpow`, `Real.rpow_logb`, `Real.rpow_le_rpow_left_iff`, `WithTop.coe_le_coe`, `WithTop.coe_min`, `Monotone.map_min`, `StrictMono.monotone`, `norm_nonneg`, `le_max_left`, `le_max_right`, `neg_le_neg`, `neg_neg`.",
  sources="[RM] Layer 2 introduction; [RM] convention 2 (\"e (v x) … equal -log ‖x‖\"); Layer 1's [BGR] 1.5.2 dictionary.",
  gen="As T001. `norm_add_le_max` is a theorem about the bundle, so the layer never assumes `IsUltrametricDist K` (plan decision 1).")

t(id='T003', title='`embedTop`: pushing `WithTop Γ` into `WithTop ℝ`', file=NAV, deps='T002',
  par='yes (with T010, T039)', typ='def API', leaves='L1.16–L1.23',
  defs=[(NAV, 'embedTop')],
  decls=[(NAV, 'embedTop_top'), (NAV, 'embedTop_coe'), (NAV, 'embedTop_eq_top_iff'), (NAV, 'embedTop_strictMono'),
         (NAV, 'embedTop_le_embedTop'), (NAV, 'embedTop_add'), (NAV, 'embedTop_apply_eq_top_iff'), (NAV, 'embedTop_map_one')],
  sketch="""`embedTop = WithTop.map v.embed` (no `sorry` in the definition).
1. `embedTop_top := WithTop.map_top _`; `embedTop_coe := WithTop.map_coe _ _`; `embedTop_eq_top_iff := WithTop.map_eq_top_iff`.
2. `embedTop_strictMono := WithTop.strictMono_map_iff.mpr v.strictMono_embed`;
   `embedTop_le_embedTop := v.embedTop_strictMono.le_iff_le`.
3. `embedTop_add := WithTop.map_add v.embed a b` (`Γ →+ ℝ` is an `AddHomClass`).
4. `embedTop_apply_eq_top_iff`: `embedTop_eq_top_iff.trans v.eq_top_iff`.
5. `embedTop_map_one`: `rw [v.map_one]`, then `embedTop_coe`, `map_zero`, `WithTop.coe_zero`.
""" + DEC + "L1.16–L1.23.",
  mathlib="`WithTop.map_top`, `WithTop.map_coe`, `WithTop.map_eq_top_iff`, `WithTop.strictMono_map_iff`, `StrictMono.le_iff_le`, `WithTop.map_add`, `map_zero`, `WithTop.coe_zero`.",
  sources="[RM] convention 4 (\"The points live in WithTop Γ, pushed into WithTop ℝ along e\").",
  gen="As T001; `embedTop` is stated on all of `WithTop Γ`, not only on values of `v`.")

t(id='T004', title='The term dictionary against `1`: `‖x‖ (b^m)^k ≤ 1`, `< 1`, `= 1`', file=NAV, deps='CLEANUP-1',
  par='yes (with T010, T039)', typ='lemmas', leaves='L1.24–L1.27',
  decls=[(NAV, 'norm_mul_rpow_pow_eq_rpow'), (NAV, 'norm_mul_rpow_pow_le_one_iff'),
         (NAV, 'norm_mul_rpow_pow_lt_one_iff'), (NAV, 'norm_mul_rpow_pow_eq_one_iff')],
  sketch="""1. `norm_mul_rpow_pow_eq_rpow`: rewrite `‖x‖` by `norm_eq_rpow h`; `(b ^ m) ^ k = b ^ (m * k)` by
   `← Real.rpow_natCast, ← Real.rpow_mul v.base_pos.le`; `b ^ (-eγ) * b ^ (mk) = b ^ (-eγ + mk)` by
   `← Real.rpow_add v.base_pos`; `ring_nf` for `-eγ + mk = mk - eγ`.
2. `_le_one_iff`: `rcases eq_or_ne x 0`. If `x = 0`: LHS `0 ≤ 1` (`norm_zero`, `zero_mul`, `zero_le_one`), RHS
   `_ ≤ ⊤` (`v.map_zero`, `embedTop_top`, `le_top`): both true. Else obtain `γ` (`exists_eq_coe`), rewrite with
   step 1 and `embedTop_coe`; `1 = b ^ (0:ℝ)` (`Real.rpow_zero`), `Real.rpow_le_rpow_left_iff v.one_lt_base`,
   `sub_nonpos`, `WithTop.coe_le_coe`.
3. `_lt_one_iff`: same with `Real.rpow_lt_rpow_left_iff`, `sub_neg`, `WithTop.coe_lt_coe`; `x = 0`: `0 < 1` and
   `↑(mk) < ⊤` (`WithTop.coe_lt_top`).
4. `_eq_one_iff`: `x = 0`: `0 = 1` false (`zero_ne_one`), `⊤ = ↑_` false (`WithTop.top_ne_coe`); else
   `le_antisymm_iff` on both sides with steps 2–3, or `Real.rpow_right_inj`-style via
   `(Real.rpow_le_rpow_left_iff _).antisymm_iff`; the real statement is `mk - eγ = 0 ↔ eγ = mk` (`sub_eq_zero`,
   `eq_comm`), then `WithTop.coe_inj`.
""" + DEC + "L1.24–L1.27. " + SRC_NOTE + " ([SRC] `CoeffVal.norm_mul_exp_pow_le_one_iff` and siblings are the `b = exp 1` case.)",
  mathlib="`Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_add`, `Real.rpow_zero`, `Real.rpow_le_rpow_left_iff`, `Real.rpow_lt_rpow_left_iff`, `norm_zero`, `zero_mul`, `zero_le_one`, `le_top`, `WithTop.coe_le_coe`, `WithTop.coe_lt_coe`, `WithTop.coe_lt_top`, `WithTop.coe_inj`, `WithTop.top_ne_coe`, `sub_nonpos`, `sub_neg`, `sub_eq_zero`, `le_antisymm_iff`.",
  sources="[RM] §2.1.2 (Q-RM-2.1.2); [Gou20] §7.4 p. 254 (Q-Gou-first: \"|a_j|(p^m)^j ≤ 1 for all j … = 1 … < 1\").",
  gen="Stated for every `x : K` (no nonvanishing hypothesis): the `⊤` bookkeeping is the content ([RM] \"the later layers use every direction of it\"). `m` is any real, `k` any natural.")

t(id='T005', title='The term dictionary between two terms', file=NAV, deps='T004',
  par='yes (with T010, T039)', typ='lemmas', leaves='L1.28–L1.30',
  decls=[(NAV, 'norm_mul_rpow_pow_le_iff'), (NAV, 'norm_mul_rpow_pow_lt_iff'), (NAV, 'norm_mul_rpow_pow_eq_iff')],
  sketch="""1. `_le_iff`: `rcases eq_or_ne y 0` then `rcases eq_or_ne x 0`.
   - `y = 0`: LHS `‖x‖ (b^m)^k ≤ 0 ↔ x = 0` (`mul_nonpos_iff`-free: `(mul_pos (norm_pos_iff.mpr hx) (pow_pos (Real.rpow_pos_of_pos _ _) _)).not_le` for `x ≠ 0`; `le_refl` for `x = 0`); RHS `⊤ + _ ≤ embedTop (v x) ↔ embedTop (v x) = ⊤ ↔ x = 0` (`WithTop.top_add`, `top_le_iff`, `embedTop_apply_eq_top_iff`).
   - `x = 0, y ≠ 0`: both sides true (`norm_zero`, `zero_mul`, `mul_nonneg`; `le_top`).
   - both nonzero: `norm_mul_rpow_pow_eq_rpow` twice, `embedTop_coe` twice, `WithTop.coe_add`, `WithTop.coe_le_coe`, `Real.rpow_le_rpow_left_iff v.one_lt_base`; the real inequality `mk - eγ ≤ mj - eγ' ↔ eγ' + m (k - j) ≤ eγ` is `linarith`/`ring_nf` (`mul_sub`).
2. `_lt_iff`: same case split with `Real.rpow_lt_rpow_left_iff`, `WithTop.coe_lt_coe`; `y = 0`: both false (`not_lt.mpr (mul_nonneg …)`, `not_top_lt`); `x = 0 ≠ y`: both true (`mul_pos`, `WithTop.coe_lt_top`).
3. `_eq_iff`: `x = y = 0` both true (`WithTop.top_add`); exactly one zero: both false (`WithTop.top_ne_coe`, `WithTop.coe_ne_top`, `mul_pos … |>.ne'`); both nonzero: `le_antisymm_iff` and steps of 1, or directly `Real.rpow_left_injective`-free: injectivity of `t ↦ b ^ t` from `Real.rpow_lt_rpow_left_iff` (`lt_irrefl`); the real identity `mk - eγ = mj - eγ' ↔ eγ = eγ' + m (k - j)` by `linarith` both ways.
""" + DEC + "L1.28–L1.30.",
  mathlib="`Real.rpow_le_rpow_left_iff`, `Real.rpow_lt_rpow_left_iff`, `Real.rpow_pos_of_pos`, `norm_pos_iff`, `pow_pos`, `mul_pos`, `mul_nonneg`, `norm_zero`, `zero_mul`, `WithTop.top_add`, `WithTop.coe_add`, `WithTop.coe_le_coe`, `WithTop.coe_lt_coe`, `WithTop.coe_lt_top`, `WithTop.top_ne_coe`, `WithTop.coe_ne_top`, `top_le_iff`, `not_top_lt`, `le_top`, `le_antisymm_iff`, `mul_sub`.",
  sources="[RM] §2.1.2 (\"for comparison against another term rather than against 1\"); [Gou20] pp. 258–259 (Q-Gou-second).",
  gen="As T004; `j` and `k` arbitrary naturals, `x y` arbitrary elements.")

t(id='T006', title='Two bundles on the same field differ by `scale`', file=NAV, deps='T005',
  par='yes (with T010, T039)', typ='def API', leaves='L1.31–L1.33',
  defs=[(NAV, 'scale')],
  decls=[(NAV, 'scale_pos'), (NAV, 'embed_eq_scale_mul_embed'), (NAV, 'embedTop_apply_eq_map')],
  sketch="""`scale v w = Real.log v.base / Real.log w.base` (no `sorry`).
1. `scale_pos := div_pos v.log_base_pos w.log_base_pos`.
2. `embed_eq_scale_mul_embed`: `‖x‖ = b ^ (-e γ)` (`v.norm_eq_rpow hv`) and `‖x‖ = b' ^ (-e' γ')` (`w.norm_eq_rpow hw`); apply `Real.log` to the equality of the right sides: `Real.log_rpow v.base_pos`, `Real.log_rpow w.base_pos` give `(-e γ) * log b = (-e' γ') * log b'`; solve for `e' γ'` with `field_simp [v.log_base_pos.ne', w.log_base_pos.ne']` and `ring` (unfold `scale`).
3. `embedTop_apply_eq_map`: `rcases eq_or_ne x 0`: `x = 0` gives `⊤ = WithTop.map _ ⊤` (`map_zero`, `embedTop_top`, `WithTop.map_top`); else obtain `γ`, `γ'` (`exists_eq_coe` for `v` and `w`), rewrite `embedTop_coe`, `WithTop.map_coe`, and step 2.
""" + DEC + "L1.31–L1.33.",
  mathlib="`div_pos`, `Real.log_rpow`, `WithTop.map_top`, `WithTop.map_coe`.",
  sources="[RM] §2.2.8 (Q-RM-2.2.8); plan D9 for the direction of the scalar (`e'(v' x) = (log b / log b') · e(v x)`).",
  gen="`Γ` and `Γ'` independent ordered groups; the scalar depends only on the two bases.")

t(id='T007', title='The real instance `ofNormAddVal`', file=NAV, deps='CLEANUP-2',
  par='yes (with T010, T039)', typ='def fields + lemma', leaves='L1.34–L1.35',
  decls=[(NAV, 'ofNormAddVal'), (NAV, 'ofNormAddVal_apply_of_ne_zero')],
  sketch="""1. `one_lt_base`: `Real.one_lt_exp_iff.mpr zero_lt_one`.
2. `norm_eq_rpow'`: from `normAddVal K x = ↑γ`, `x ≠ 0` by `NormedField.normAddVal_eq_top` (the value is not `⊤`); `NormedField.normAddVal_apply_of_ne_zero K hx` and `WithTop.coe_inj` give `γ = -Real.log ‖x‖`; then `(Real.exp 1) ^ (-γ) = Real.exp (-γ)` (`Real.exp_one_rpow`) `= Real.exp (Real.log ‖x‖) = ‖x‖` (`neg_neg`, `Real.exp_log (norm_pos_iff.mpr hx)`).
3. `ofNormAddVal_apply_of_ne_zero := NormedField.normAddVal_apply_of_ne_zero K hx` (the coercion is `rfl`).
""" + DEC + "L1.34–L1.35.",
  mathlib="`Real.one_lt_exp_iff`, `NormedField.normAddVal_eq_top`, `NormedField.normAddVal_apply_of_ne_zero`, `WithTop.coe_inj`, `Real.exp_one_rpow`, `Real.exp_log`, `norm_pos_iff`, `neg_neg`.",
  sources="[RM] Layer 2 introduction (\"(normAddVal K, id, exp 1) always\"); [RM] §1.2.2–§1.2.3.",
  gen="`[NontriviallyNormedField K] [IsUltrametricDist K]`, Layer 1's hypotheses for `normAddVal`.")

t(id='T008', title='The discrete instance `ofNormAddValZ`', file=NAV, deps='T007',
  par='yes (with T010, T039)', typ='def fields + lemmas', leaves='L1.36–L1.38',
  decls=[(NAV, 'ofNormAddValZ'), (NAV, 'ofNormAddValZ_apply_isUniformizer'), (NAV, 'scale_ofNormAddValZ_ofNormAddVal')],
  sketch="""1. `strictMono_embed := Int.cast_strictMono` (coerced `Int.castAddHom ℝ`; `Int.coe_castAddHom`).
2. `one_lt_base`: `one_lt_inv_iff₀.mpr ⟨hπ0, hπ1⟩` with `0 < ‖π‖` and `‖π‖ < 1`: `hπ : IsUniformizer _ π` means `valuation π = ↑(generator _)` (`Valuation.IsUniformizer.iff`), `NormedField.valuation_apply` reads `‖π‖₊ = generator`, `Valuation.IsRankOneDiscrete.generator_lt_one` gives `‖π‖₊ < 1` (`Units.val_lt_one`-style coercions) and `generator ≠ 0` (`Units.ne_zero`) gives `‖π‖₊ ≠ 0`; pass to `ℝ` with `NNReal.coe_lt_coe`, `NNReal.coe_pos`, `coe_nnnorm`.
3. `norm_eq_rpow'`: from `normAddValZ K x = ↑d`, `NormedField.normAddValZ_eq_iff_of_isUniformizer K hπ x d` gives `‖x‖ = ‖π‖ ^ d` (`zpow`); rewrite `(‖π‖⁻¹) ^ (-(d:ℝ)) = (‖π‖⁻¹) ^ (-d : ℤ)` (`Real.rpow_intCast` after `Int.cast_neg`) `= ‖π‖ ^ d` (`inv_zpow'`, `zpow_neg`, `inv_inv`).
4. `ofNormAddValZ_apply_isUniformizer := NormedField.normAddValZ_isUniformizer K hπ`.
5. `scale_ofNormAddValZ_ofNormAddVal`: unfold `scale`, `ofNormAddValZ_base`, `ofNormAddVal_base`; `Real.log_inv`, `Real.log_exp`, `div_one`.
""" + DEC + "L1.36–L1.38.",
  mathlib="`Int.cast_strictMono`, `Int.coe_castAddHom`, `one_lt_inv_iff₀`, `Valuation.IsUniformizer.iff`, `NormedField.valuation_apply`, `Valuation.IsRankOneDiscrete.generator_lt_one`, `Units.ne_zero`, `NNReal.coe_lt_coe`, `NNReal.coe_pos`, `coe_nnnorm`, `NormedField.normAddValZ_eq_iff_of_isUniformizer`, `Real.rpow_intCast`, `Int.cast_neg`, `inv_zpow'`, `zpow_neg`, `inv_inv`, `NormedField.normAddValZ_isUniformizer`, `Real.log_inv`, `Real.log_exp`, `div_one`.",
  sources="[RM] Layer 2 introduction (\"(normAddValZ K, Int.cast, ‖π‖⁻¹) for a discretely valued K with uniformiser π\"); [RM] §1.3.2, §1.3.4; §2.2.8 (\"divided by log p\").",
  gen="`[(valuation (K := K)).IsRankOneDiscrete]` as an instance, the uniformiser as an explicit hypothesis `hπ` (Layer 1's shape).")

t(id='T009', title='The rational instance `ofNormAddValQ`', file=NAV, deps='T008',
  par='yes (with T010, T039)', typ='def fields + lemma', leaves='L1.39–L1.40',
  decls=[(NAV, 'ofNormAddValQ'), (NAV, 'ofNormAddValQ_self')],
  sketch="""1. `strictMono_embed := Rat.cast_strictMono` (`Rat.coe_castHom`).
2. `one_lt_base`: `one_lt_inv_iff₀.mpr ⟨_, _⟩` from `Valuation.IsCommensurable.val_pos` (`0 < valuation π`, i.e. `0 < ‖π‖₊`, `NormedField.valuation_apply`) and `Valuation.IsCommensurable.val_lt_one` (`‖π‖₊ < 1`), coerced to `ℝ`.
3. `norm_eq_rpow'`: from `normAddValQ K π x = ↑q`, `NormedField.norm_eq_norm_rpow_normAddValQ K π hq : ‖x‖ = ‖π‖ ^ (q:ℝ)`; `(‖π‖⁻¹) ^ (-(q:ℝ)) = (‖π‖ ^ (q:ℝ))⁻¹⁻¹`: `Real.inv_rpow (norm_nonneg _)`, `Real.rpow_neg (norm_nonneg _)`, `inv_inv`.
4. `ofNormAddValQ_self := NormedField.normAddValQ_self K π`.
""" + DEC + "L1.39–L1.40.",
  mathlib="`Rat.cast_strictMono`, `Rat.coe_castHom`, `one_lt_inv_iff₀`, `Valuation.IsCommensurable.val_pos`, `Valuation.IsCommensurable.val_lt_one`, `NormedField.valuation_apply`, `NormedField.norm_eq_norm_rpow_normAddValQ`, `Real.inv_rpow`, `Real.rpow_neg`, `inv_inv`, `norm_nonneg`, `NormedField.normAddValQ_self`.",
  sources="[RM] Layer 2 introduction (\"(normAddValQ K π, Rat.cast, ‖π‖⁻¹) in the commensurable case\"); [RM] §1.4.6.",
  gen="`π` explicit with `[(valuation (K := K)).IsCommensurable π]` (convention 3: normalisation by an element).")

# ---------------------------------------------------------------- G2 Generic
t(id='T010', title='Finite support is admissible; `shiftRight` basics', file=GE, deps='none',
  par='yes (with T001, T039)', typ='def API', leaves='L2.1–L2.6',
  defs=[(GE, 'shiftRight')],
  decls=[(GE, 'isAdmissible_of_finite'), (GE, 'shiftRight_add'), (GE, 'shiftRight_of_le'), (GE, 'shiftRight_of_lt'),
         (GE, 'shiftRight_zero'), (GE, 'unitSlope_shiftRight')],
  sketch="""1. `isAdmissible_of_finite`: the image `(fun k ↦ (v k).untop₀) '' finiteSupport v` is finite (`Set.Finite.image`), hence bounded below (`Set.Finite.bddBelow`); with `y` a lower bound apply `NewtonPolygon.isAdmissible_of_line (y := y) (σ := 0)`: for `v k = ⊤` the inequality is `le_top`; for `v k ≠ ⊤`, `y + 0 * k = y ≤ (v k).untop₀` and `WithTop.coe_untop₀_of_ne_top` (`WithTop.coe_le_coe`).
2. `shiftRight_add`: `simp [shiftRight, Nat.le_add_left]` (`Nat.add_sub_cancel`). `shiftRight_of_le`: `if_pos hk`. `shiftRight_of_lt`: `if_neg (not_le.mpr hk)`. `shiftRight_zero`: `funext`, `if_pos (zero_le _)`, `Nat.sub_zero`.
3. `unitSlope_shiftRight`: `unitSlope_nat` twice; `k + n + 1 = (k + 1) + n` (`Nat.add_right_comm`) and `shiftRight_add` twice.
""" + DEC + "L2.1–L2.6.",
  mathlib="`Set.Finite.image`, `Set.Finite.bddBelow`, `WithTop.coe_untop₀_of_ne_top`, `WithTop.coe_le_coe`, `le_top`, `Nat.le_add_left`, `Nat.add_sub_cancel`, `Nat.add_right_comm`, `Nat.sub_zero`, `zero_le`, `if_pos`, `if_neg`, `not_le`, `funext`.",
  sources="[RM] §0.2.3 (\"it holds for every sequence on or above a single line\"), §2.1.3, §2.2.7 (\"the polygon of X^n · f is translated right by n\").",
  gen="Generic over `v : ℕ → WithTop ℝ` (namespace `NewtonPolygon`); Tau Ceti home Layer 0's `Basic.lean`.")

t(id='T011', title='The shifted polygon is the shifted sequence\'s polygon', file=GE, deps='T010',
  par='yes (with T001, T039)', typ='theorems', leaves='L2.7–L2.10',
  decls=[(GE, 'isConvexSeq_shiftRight_iff'), (GE, 'isNewtonPolygonOf_shiftRight_iff'), (GE, 'isAdmissible_shiftRight_iff'),
         (GE, 'newtonPolygon_shiftRight')],
  sketch="""1. `isConvexSeq_shiftRight_iff`: use `NewtonPolygon.isConvexSeq_iff_midpoint` on both sides. Midpoint: for `k + 2 < n`, `k + 1 < n` or `k + 2 = n`… case on `n ≤ k`: then all three indices are `≥ n` and the inequality is the original one at `k - n` (`shiftRight_of_le`, `Nat.sub_add_comm`); if `k < n` the right side contains `⊤` (`shiftRight_of_lt`, `WithTop.top_add`/`WithTop.add_top`, `le_top`). Order-connectedness: `finiteSupport (shiftRight n h) = (· + n) '' finiteSupport h` (`Set.ext`, `mem_finiteSupport`, `shiftRight_of_le`/`_of_lt`); an image of an interval under `· + n` is an interval (`Set.OrdConnected` unfolded: for `a + n ≤ x ≤ b + n`, `x = (x - n) + n` with `a ≤ x - n ≤ b`), and conversely the preimage.
2. `isNewtonPolygonOf_shiftRight_iff`: `constructor` on the three fields.
   (→) `convex` by 1; `le_points k`: for `n ≤ k` it is the given one at `k - n` via `shiftRight_of_le`, else `le_top`; `greatest g hg hgv k`: `shiftRight n g` is convex (1) and `≤ shiftRight n v`, so `shiftRight n g (k + n) ≤ shiftRight n h (k + n)` (`shiftRight_add`).
   (←) `convex` by 1; `le_points` by cases; `greatest g hg hgv k`: let `g' := fun k ↦ g (k + n)`; `g'` convex (`isConvexSeq_iff_midpoint` transports: midpoint at `k` is `g`'s at `k + n`; order-connectedness of a preimage under `· + n`), `g' ≤ v` (from `hgv (k + n)` and `shiftRight_add`), so `g' ≤ h`; for `n ≤ k` write `k = (k - n) + n`, `g k = g' (k - n) ≤ h (k - n) = shiftRight n h k`; for `k < n`, `shiftRight n h k = ⊤`.
3. `isAdmissible_shiftRight_iff`: `isAdmissible_iff_exists_line` both sides; given `y + σ k ≤ v k` take `(y - σ n) + σ k ≤ shiftRight n v k` (for `k ≥ n`: `(y - σn) + σk = y + σ(k - n)`, `Nat.cast_sub`; for `k < n`: `le_top`); conversely given a line below the shift, read it at `k + n` (`shiftRight_add`, `Nat.cast_add`, `ring_nf`).
4. `newtonPolygon_shiftRight`: `(isNewtonPolygonOf_shiftRight_iff n).mpr (isNewtonPolygonOf_newtonPolygon (exists_isConvexMinorant_iff_isAdmissible.mpr hv))` then `IsNewtonPolygonOf.eq_newtonPolygon`.
""" + DEC + "L2.7–L2.10.",
  mathlib="`NewtonPolygon.isConvexSeq_iff_midpoint`, `NewtonPolygon.mem_finiteSupport`, `NewtonPolygon.isAdmissible_iff_exists_line`, `NewtonPolygon.isNewtonPolygonOf_newtonPolygon`, `NewtonPolygon.exists_isConvexMinorant_iff_isAdmissible`, `NewtonPolygon.IsNewtonPolygonOf.eq_newtonPolygon`, `Set.OrdConnected`, `WithTop.top_add`, `WithTop.add_top`, `le_top`, `Nat.sub_add_comm`, `Nat.cast_sub`, `Nat.cast_add`, `Nat.sub_add_cancel`.",
  sources="[RM] §2.2.7 (\"translated right by n\"); §0.2.4 (\"phrased with newtonPolygon and its characterisation, never with the construction\").",
  gen="Generic; the `iff` forms need no admissibility, only the final `newtonPolygon_shiftRight` does.")

t(id='T012', title='`reflect` basics and its unit slopes', file=GE, deps='T011',
  par='yes (with T001, T039)', typ='def API', leaves='L2.11–L2.14',
  defs=[(GE, 'reflect')],
  decls=[(GE, 'reflect_of_le'), (GE, 'reflect_of_lt'), (GE, 'reflect_reflect'), (GE, 'unitSlope_reflect')],
  sketch="""1. `reflect_of_le := if_pos hk`; `reflect_of_lt := if_neg (not_le.mpr hk)`.
2. `reflect_reflect`: `funext k`; if `k ≤ d`: `reflect_of_le`, `Nat.sub_le`, `Nat.sub_sub_self hk`; else both `⊤` (`reflect_of_lt`, `hv k hk`).
3. `unitSlope_reflect`: `unitSlope_nat` twice, `reflect_of_le` at `k + 1 ≤ d` and `k ≤ d`; `d - k = (d - (k+1)) + 1` (`omega`); then a case analysis on `h (d - (k+1))` and `h (d - k)` being `⊤` (`WithTop.ne_top_iff_exists`): finite–finite is `LinearOrderedAddCommGroup.coe_sub`, `coe_neg`, `neg_sub`; any `⊤` gives `⊤` on both sides (`LinearOrderedAddCommGroup.top_sub`, `sub_top`, `neg_top`).
""" + DEC + "L2.11–L2.14.",
  mathlib="`if_pos`, `if_neg`, `not_le`, `Nat.sub_le`, `Nat.sub_sub_self`, `NewtonPolygon.unitSlope_nat`, `WithTop.ne_top_iff_exists`, `WithTop.LinearOrderedAddCommGroup.coe_sub`, `WithTop.LinearOrderedAddCommGroup.coe_neg`, `WithTop.LinearOrderedAddCommGroup.top_sub`, `WithTop.LinearOrderedAddCommGroup.sub_top`, `WithTop.LinearOrderedAddCommGroup.neg_top`, `neg_sub`.",
  sources="[RM] §2.2.7 (\"the polygon of Polynomial.reverse f is the reflection i ↦ h (d - i)\").",
  gen="Generic; `reflect d` is total, with `⊤` beyond `d`.")

t(id='T013', title='The reflected polygon is the reflected sequence\'s polygon', file=GE, deps='CLEANUP-4',
  par='yes (with T001, T039)', typ='theorems', leaves='L2.15–L2.17',
  decls=[(GE, 'IsConvexSeq.reflect'), (GE, 'IsNewtonPolygonOf.reflect'), (GE, 'newtonPolygon_reflect')],
  sketch="""1. `IsConvexSeq.reflect`: `isConvexSeq_iff_midpoint`. Midpoint at `k`: if `k + 2 ≤ d`, the three reflected values are `h (d-k)`, `h (d-k-1)`, `h (d-k-2)` and the inequality is `hh`'s midpoint at `d - (k+2)` with the two outer terms swapped (`add_comm`); if `k + 1 ≥ d`… cases `k + 2 > d`: the right side has a `⊤` (`reflect_of_lt`) — `le_top` after `WithTop.add_top`. Order-connectedness: `finiteSupport (reflect d h) = {k | k ≤ d ∧ h (d - k) ≠ ⊤}`; for `a ≤ x ≤ b` in it, `d - b ≤ d - x ≤ d - a` (`Nat.sub_le_sub_left`) and `hh.ordConnected.out` gives `h (d - x) ≠ ⊤`; `x ≤ b ≤ d`.
2. `IsNewtonPolygonOf.reflect`: `hd : ∀ k, d < k → h k = ⊤` from `hv` and `hh.le_points` (`top_le_iff`). `convex` by 1. `le_points k`: `reflect_of_le`/`reflect_of_lt` and `hh.le_points (d - k)`. `greatest g hg hgv k`: let `g₀ := (Set.Iic d).piecewise g ⊤` (`g` on `[0, d]`, `⊤` beyond), convex by `IsConvexSeq.piecewise_top hg Set.ordConnected_Iic`, and `g' := reflect d g₀` (equal to `reflect d g` pointwise since both read `g (d - k)` for `k ≤ d`); `g'` is convex by 1 (with `g₀ = ⊤` beyond `d`); `g' ≤ v`: for `k ≤ d`, `g (d - k) ≤ reflect d v (d - k) = v k` (`hgv`, `reflect_of_le`, `Nat.sub_sub_self`); for `k > d`, `⊤ ≤ v k` by `hv`. Hence `g' ≤ h` (`hh.greatest`), and for `k ≤ d`, `g k = g' (d - k) ≤ h (d - k) = reflect d h k`; for `k > d`, `reflect d h k = ⊤`.
3. `newtonPolygon_reflect`: `finiteSupport v ⊆ Set.Iic d` (`hv`), finite (`Set.finite_Iic`, `Set.Finite.subset`), so `isAdmissible_of_finite`, `isNewtonPolygonOf_newtonPolygon` (via `exists_isConvexMinorant_iff_isAdmissible`), `IsNewtonPolygonOf.reflect`, `eq_newtonPolygon`.
""" + DEC + "L2.15–L2.17 (the competitor-beyond-`d` attack and its repair are recorded there).",
  mathlib="`NewtonPolygon.isConvexSeq_iff_midpoint`, `NewtonPolygon.IsConvexSeq.piecewise_top`, `Set.ordConnected_Iic`, `NewtonPolygon.IsConvexSeq.ordConnected`, `Set.OrdConnected.out`, `Nat.sub_le_sub_left`, `Nat.sub_sub_self`, `top_le_iff`, `WithTop.add_top`, `le_top`, `Set.finite_Iic`, `Set.Finite.subset`, `NewtonPolygon.isNewtonPolygonOf_newtonPolygon`, `NewtonPolygon.exists_isConvexMinorant_iff_isAdmissible`, `NewtonPolygon.IsNewtonPolygonOf.eq_newtonPolygon`, `Set.piecewise`.",
  sources="[RM] §2.2.7 (\"⚠ The reflection … is a milestone, not a remark\"); [RM] §0.2.4.",
  gen="For sequences supported in `[0, d]` (`hv`), which is what `Polynomial.reverse` needs; `d` arbitrary.")

t(id='T014', title='`scaleHeight`: the polygon of a height-scaled sequence', file=GE, deps='T013',
  par='yes (with T001, T039)', typ='def API + theorems', leaves='L2.18–L2.25',
  defs=[(GE, 'scaleHeight')],
  decls=[(GE, 'scaleHeight_eq_top_iff'), (GE, 'finiteSupport_scaleHeight'), (GE, 'unitSlope_scaleHeight'),
         (GE, 'isConvexSeq_scaleHeight_iff'), (GE, 'isNewtonPolygonOf_scaleHeight_iff'), (GE, 'isAdmissible_scaleHeight_iff'),
         (GE, 'newtonPolygon_scaleHeight'), (GE, 'slopeMultiset_scaleHeight')],
  sketch="""1. `scaleHeight_eq_top_iff := WithTop.map_eq_top_iff`; `finiteSupport_scaleHeight`: `Set.ext`, `mem_finiteSupport`, 1.
2. `unitSlope_scaleHeight`: `unitSlope_nat`; cases on `h k`, `h (k+1)` (`WithTop.ne_top_iff_exists`): `WithTop.map_coe`, `LinearOrderedAddCommGroup.coe_sub`, `mul_sub`; `⊤` cases by `WithTop.map_top`, `top_sub`, `sub_top`.
3. `isConvexSeq_scaleHeight_iff (hc : 0 < c)`: unfold `IsConvexSeq`; order-connectedness by 1; `MonotoneOn (unitSlope (scaleHeight c h))` ↔ `MonotoneOn (unitSlope h)` by 2 and the order embedding `WithTop.map (c * ·)` (`WithTop.strictMono_map_iff.mpr (strictMono_mul_left_of_pos hc)`, `.le_iff_le`).
4. `isNewtonPolygonOf_scaleHeight_iff`: fields; `le_points` via `embedTop`-style `WithTop.map` monotonicity (`WithTop.map_le_iff`-free: the embedding of 3); `greatest`: a competitor `g` for `scaleHeight c v` gives `scaleHeight c⁻¹ g` for `v` (3 with `inv_pos.mpr hc`; `scaleHeight c⁻¹ (scaleHeight c x) = x` by `WithTop.map_map`-style cases and `inv_mul_cancel_left₀ hc.ne'`), and conversely.
5. `isAdmissible_scaleHeight_iff`: `isAdmissible_iff_exists_line` both sides: `y + σ k ≤ v k ↔ c y + c σ k ≤ scaleHeight c v k` (cases on `v k`; `WithTop.map_coe`, `WithTop.coe_le_coe`, `mul_le_mul_left hc`, `mul_add`); conversely scale by `c⁻¹`.
6. `newtonPolygon_scaleHeight`: spec of `v`, 4, `eq_newtonPolygon`.
7. `slopeMultiset_scaleHeight`: `slopeIndices (scaleHeight c h) = slopeIndices h` (`mem_slopeIndices_iff`, 1 at `k`, `k+1` — or 2 with `WithTop.map_eq_top_iff`); unfold `slopeMultiset` with `dif_pos` on both sides, `Multiset.map_map`, and `(WithTop.map (c * ·) x).untop₀ = c * x.untop₀` (cases).
""" + DEC + "L2.18–L2.25.",
  mathlib="`WithTop.map_eq_top_iff`, `NewtonPolygon.mem_finiteSupport`, `NewtonPolygon.unitSlope_nat`, `WithTop.ne_top_iff_exists`, `WithTop.map_coe`, `WithTop.map_top`, `WithTop.LinearOrderedAddCommGroup.coe_sub`, `WithTop.LinearOrderedAddCommGroup.top_sub`, `WithTop.LinearOrderedAddCommGroup.sub_top`, `mul_sub`, `WithTop.strictMono_map_iff`, `strictMono_mul_left_of_pos`, `StrictMono.le_iff_le`, `inv_pos`, `inv_mul_cancel_left₀`, `NewtonPolygon.isAdmissible_iff_exists_line`, `WithTop.coe_le_coe`, `mul_le_mul_left`, `mul_add`, `NewtonPolygon.mem_slopeIndices_iff`, `Multiset.map_map`, `NewtonPolygon.isNewtonPolygonOf_newtonPolygon`, `NewtonPolygon.exists_isConvexMinorant_iff_isAdmissible`, `NewtonPolygon.IsNewtonPolygonOf.eq_newtonPolygon`.",
  sources="[RM] §2.2.8 (Q-RM-2.2.8: \"differ by the positive scalar … in height\").",
  gen="Positive scalar `c` where the order matters (3–7); the bookkeeping lemmas 1–2 hold for every `c`.")

t(id='T015', title='Every slope index lies in a segment; the slope of a segment', file=GE, deps='T014',
  par='yes (with T001, T039)', typ='theorems', leaves='L2.26–L2.27',
  decls=[(GE, 'exists_isSegment_of_mem_slopeIndices'), (GE, 'IsConvexSeq.unitSlope_eq_div_of_isSegment')],
  sketch="""1. `exists_isSegment_of_mem_slopeIndices`: `hj` gives `h j ≠ ⊤`, `h (j+1) ≠ ⊤` (`mem_slopeIndices_iff`). Let `S := slopeIndices h` (finite, nonempty), `j₁ := hfin.toFinset.max'`-style largest element (`Set.Finite.bddAbove`, `Nat.sSup_mem`), `d := j₁ + 1`: then `h d ≠ ⊤` and `h (d + 1) = ⊤` (else `d ∈ S`), so `IsVertex h d` (`isVertex_of_succ_eq_top hh`). The anchor is a vertex (`isVertex_anchor ⟨j, hj.1⟩`) with `anchor h ≤ j` (`anchor_le hj.1`). Set `a := sSup {i | i ≤ j ∧ IsVertex h i}` (bounded by `j`, nonempty; `Nat.sSup_mem`) and `b := sInf {i | j < i ∧ IsVertex h i}` (nonempty: `d`, since `j < d`; `Nat.sInf_mem`). Then `IsSegment h a b`: both vertices, `a ≤ j < b`, and no vertex strictly between: a vertex `i` with `a < i < b` would be either `≤ j` (then `i ≤ a` by `le_csSup`/`Nat.le_sSup`-style, contradiction) or `> j` (then `b ≤ i`, contradiction).
2. `IsConvexSeq.unitSlope_eq_div_of_isSegment`: `IsConvexSeq.unitSlope_eq_of_isSegment hh hab haj hjb` gives `unitSlope h j = unitSlope h a`; `IsConvexSeq.eq_add_nsmul_of_isSegment hh hab le_rfl hab.2.2.1.le` at `k = b`: `h b = h a + (b - a) • unitSlope h a`; with `h a = ↑α`, `h b = ↑β` (vertices are finite, `WithTop.ne_top_iff_exists`), `unitSlope h a` is finite (`unitSlope_ne_top`), write it as `↑s`; `WithTop.coe_nsmul`, `WithTop.coe_add`, `WithTop.coe_inj`, `nsmul_eq_mul`: `β = α + (b - a) * s`, so `s = (β - α) / ((b:ℝ) - a)` (`eq_div_iff`, `Nat.cast_sub hab.2.2.1.le`, `sub_ne_zero.mpr`), and `untop₀` of the coercions by `WithTop.untop₀_coe`.
""" + DEC + "L2.26–L2.27.",
  mathlib="`NewtonPolygon.mem_slopeIndices_iff`, `Set.Finite.bddAbove`, `Nat.sSup_mem`, `Nat.sInf_mem`, `Nat.sInf_le`, `le_csSup`, `NewtonPolygon.isVertex_of_succ_eq_top`, `NewtonPolygon.isVertex_anchor`, `NewtonPolygon.anchor_le`, `NewtonPolygon.IsSegment`, `NewtonPolygon.IsConvexSeq.unitSlope_eq_of_isSegment`, `NewtonPolygon.IsConvexSeq.eq_add_nsmul_of_isSegment`, `NewtonPolygon.unitSlope_ne_top`, `WithTop.ne_top_iff_exists`, `WithTop.coe_nsmul`, `WithTop.coe_add`, `WithTop.coe_inj`, `WithTop.untop₀_coe`, `nsmul_eq_mul`, `eq_div_iff`, `Nat.cast_sub`, `sub_ne_zero`.",
  sources="[Kob84] IV §3 p. 97 (Q-Kob-vert: \"its slope is (m' − m)/(i' − i)\"); [Gou20] p. 252 (Q-Gou-feat).",
  gen="Generic over convex `h` with finitely many slopes (polygons of polynomials); a terminal ray has no right vertex, hence the finiteness hypothesis (plan D4).")

# ---------------------------------------------------------------- G3 CoeffVal
t(id='T016', title='`PowerSeries.coeffVal`: the points, `⊤` at vanishing coefficients, the term dictionary', file=CV, deps='CLEANUP-3',
  par='yes (with T063)', typ='def API', leaves='L3.1–L3.10',
  defs=[(CV, 'coeffVal')],
  decls=[(CV, 'coeffVal_eq_top_iff', 0), (CV, 'coeffVal_ne_top_iff', 0), (CV, 'coeffVal_eq_coe_iff', 0), (CV, 'finiteSupport_coeffVal', 0),
         (CV, 'coeffVal_zero'), (CV, 'coeffVal_zero_of_coeff_zero_eq_one'), (CV, 'exists_coeffVal_ne_top'),
         (CV, 'norm_coeff_mul_rpow_pow_le_one_iff'), (CV, 'norm_coeff_mul_rpow_pow_lt_one_iff'), (CV, 'norm_coeff_mul_rpow_pow_eq_one_iff')],
  sketch="""`coeffVal v f i = v.embedTop (v (coeff i f))` (no `sorry`).
1. `coeffVal_eq_top_iff := v.embedTop_apply_eq_top_iff`; `_ne_top_iff := coeffVal_eq_top_iff.not`.
2. `coeffVal_eq_coe_iff`: (←) `rw [h, embedTop_coe]`; (→) `v (coeff i f) ≠ ⊤` (else the left side is `⊤`), obtain `γ'` (`WithTop.ne_top_iff_exists`), `embedTop_coe`, `WithTop.coe_inj`, `v.strictMono_embed.injective`.
3. `finiteSupport_coeffVal`: `Set.ext`, `mem_finiteSupport`, 1. `coeffVal_zero`: `funext`, `map_zero`, `v.map_zero`, `embedTop_top`. `coeffVal_zero_of_coeff_zero_eq_one`: `rw [coeffVal_apply, h, v.embedTop_map_one]`.
4. `exists_coeffVal_ne_top`: `PowerSeries.ext_iff` negated gives `i` with `coeff i f ≠ 0`; 1.
5. `norm_coeff_mul_rpow_pow_{le,lt,eq}_one_iff := v.norm_mul_rpow_pow_{le,lt,eq}_one_iff (coeff k f) m k`.
""" + DEC + "L3.1–L3.10.",
  mathlib="`WithTop.ne_top_iff_exists`, `WithTop.coe_inj`, `StrictMono.injective`, `NewtonPolygon.mem_finiteSupport`, `map_zero`, `PowerSeries.ext_iff`, `funext`.",
  sources="[RM] §2.1.1; [Kob84] IV §3 (Q-Kob-def: \"If a_i = 0, we omit that point, or we think of it as lying \\\"infinitely\\\" far above\"); [Gou20] (Q-Gou-def).",
  gen="`[NormedField K]`, any `Γ`; `f` any power series.")

t(id='T017', title='Bounded terms are a line below the points; admissible iff bounded somewhere', file=CV, deps='T016',
  par='yes (with T063)', typ='theorems', leaves='L3.11–L3.12',
  decls=[(CV, 'hasGaussNorm_rpow_iff_exists_line'), (CV, 'isAdmissible_coeffVal_iff_exists_hasGaussNorm')],
  sketch="""1. `hasGaussNorm_rpow_iff_exists_line`: `HasGaussNorm norm c f` unfolds to `BddAbove (Set.range fun k ↦ ‖coeff k f‖ * c ^ k)` (`bddAbove_def`, `Set.forall_mem_range`).
   (→) obtain `M`. If `M ≤ 0`: every term is `0` (`le_antisymm` with `mul_nonneg (norm_nonneg _) (pow_nonneg (Real.rpow_pos_of_pos v.base_pos m).le _)`), so every coefficient vanishes (`mul_eq_zero`, `pow_ne_zero`, `norm_eq_zero`), `coeffVal = ⊤` (T016) and any `y` works (`le_top`). If `0 < M`: `y := -Real.logb v.base M`; for each `k`, if `coeff k f = 0` then `_ ≤ ⊤`; else `v (coeff k f) = ↑γ`, `norm_mul_rpow_pow_eq_rpow`, `M = b ^ (-y)` (`v.rpow_logb`, `neg_neg`), `Real.rpow_le_rpow_left_iff v.one_lt_base`: `mk - eγ ≤ -y ↔ y + mk ≤ eγ`; `embedTop_coe`, `WithTop.coe_le_coe`.
   (←) given `y`, bound `M := b ^ (-y)`: each term is `0 ≤ M` or `b ^ (mk - eγ) ≤ b ^ (-y)` by the same rewriting.
2. `isAdmissible_coeffVal_iff_exists_hasGaussNorm`: `isAdmissible_iff_exists_line`; (→) a line of slope `σ` gives `HasGaussNorm` at `c := b ^ σ > 0` (`Real.rpow_pos_of_pos`) by 1; (←) `c > 0` is `b ^ (logb b c)` (`v.rpow_logb hc`), so 1 gives a line.
""" + DEC + "L3.11–L3.12.",
  mathlib="`bddAbove_def`, `Set.forall_mem_range`, `mul_nonneg`, `norm_nonneg`, `pow_nonneg`, `Real.rpow_pos_of_pos`, `mul_eq_zero`, `pow_ne_zero`, `norm_eq_zero`, `Real.rpow_le_rpow_left_iff`, `WithTop.coe_le_coe`, `le_top`, `NewtonPolygon.isAdmissible_iff_exists_line`, `neg_neg`.",
  sources="[RM] §2.1.3, §2.3.2 (\"HasGaussNorm norm c f is equivalent to the supporting value being finite\"); [Kob84] Lemma 5 proof (Q-Kob-L5: \"ord_p(a_i x^i) = ord_p a_i − ib'\").",
  gen="Radius form through `v.base ^ m`; the positive-radius form is the second theorem.")

t(id='T018', title='Bounded at a radius ⟹ restricted at every smaller radius', file=CV, deps='T017',
  par='yes (with T063)', typ='theorem', leaves='L3.13',
  decls=[(CV, 'isRestricted_of_hasGaussNorm')],
  sketch="""`PowerSeries.isRestricted_iff'` ([RAG]) reduces to `Tendsto (fun k ↦ ‖coeff k f‖ * c ^ k) atTop (𝓝 0)`. Let `M` bound the terms at `c'` (`hf`, `bddAbove_def`), `c' > 0` from `hc.trans_lt hcc'`, `r := c / c'` with `0 ≤ r < 1` (`div_nonneg`, `div_lt_one`). For each `k`, `‖aₖ‖ cᵏ = (‖aₖ‖ c'ᵏ) rᵏ` (`div_pow`, `mul_div_assoc`, `mul_div_cancel₀`-style with `pow_ne_zero`) `≤ M rᵏ` (`mul_le_mul_of_nonneg_right`, `pow_nonneg`). Conclude with `squeeze_zero (fun k ↦ mul_nonneg (norm_nonneg _) (pow_nonneg hc k)) (bound) ((tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).const_mul M)` and `mul_zero`.
""" + DEC + "L3.13.",
  mathlib="`PowerSeries.isRestricted_iff'`, `bddAbove_def`, `div_nonneg`, `div_lt_one`, `div_pow`, `mul_div_assoc`, `mul_div_cancel₀`, `pow_ne_zero`, `mul_le_mul_of_nonneg_right`, `pow_nonneg`, `squeeze_zero`, `tendsto_pow_atTop_nhds_zero_of_lt_one`, `Filter.Tendsto.const_mul`, `mul_zero`, `norm_nonneg`.",
  sources="[RM] §2.3.2 (\"restrictedness is decay and is strictly stronger than boundedness. Prove the implication that holds\"); [Kob84] Lemma 5 (Q-Kob-L5).",
  gen="Any `[NormedRing]` would do; stated for the layer's `K`. `0 ≤ c < c'` are the honest hypotheses.")

t(id='T019', title='[M1] Admissibility is restrictedness at some positive radius; the vertical case', file=CV, deps='CLEANUP-ALL-1',
  par='no', typ='theorems', leaves='L3.14–L3.16', milestone='M1 ([RM] §2.1.3)',
  decls=[(CV, 'isAdmissible_coeffVal_iff_exists_isRestricted'), (CV, 'IsRestricted.isAdmissible_coeffVal'), (CV, 'isVertical_coeffVal_iff')],
  sketch="""1. `isAdmissible_coeffVal_iff_exists_isRestricted`: `isAdmissible_coeffVal_iff_exists_hasGaussNorm` (T017); (→) from `c > 0` with `HasGaussNorm`, `isRestricted_of_hasGaussNorm (half_pos hc).le (half_lt_self hc)` at `c / 2 > 0`; (←) from `IsRestricted c f`, [RAG] `PowerSeries.IsRestricted.hasGaussNorm`.
2. `IsRestricted.isAdmissible_coeffVal := (isAdmissible_coeffVal_iff_exists_isRestricted v).mpr ⟨c, hc, hf⟩`.
3. `isVertical_coeffVal_iff`: unfold `NewtonPolygon.IsVertical`; the first conjunct is `f ≠ 0` by `exists_coeffVal_ne_top` and `coeffVal_ne_top_iff` + `PowerSeries.ext_iff`; the second is the negation of 1 (`not_exists`, `not_and`).
""" + DEC + "L3.14–L3.16.",
  mathlib="`PowerSeries.IsRestricted.hasGaussNorm`, `half_pos`, `half_lt_self`, `NewtonPolygon.IsVertical`, `not_exists`, `not_and`, `PowerSeries.ext_iff`.",
  sources="[RM] §2.1.3 (\"admissible exactly when f is restricted at some positive radius\"); [Kob84] IV §4 p. 99 (Q-Kob-degen: \"zero radius of convergence\").",
  gen="Statement over the normed field; the radius is any positive real.")

t(id='T020', title='`Polynomial.coeffVal`: finitely supported, admissible, the coercion', file=CV, deps='T019',
  par='yes (with T063)', typ='def API', leaves='L3.17–L3.24',
  defs=[(CV, 'coeffVal')],
  decls=[(CV, 'coeffVal_eq_top_iff', 1), (CV, 'coeffVal_ne_top_iff', 1), (CV, 'coeffVal_eq_coe_iff', 1), (CV, 'finiteSupport_coeffVal', 1),
         (CV, 'finiteSupport_coeffVal_finite'), (CV, 'coeffVal_coe'), (CV, 'isAdmissible_coeffVal'), (CV, 'hasGaussNorm_coe')],
  sketch="""The generator prints both `coeffVal` definitions; this ticket concerns the `Polynomial` one (second block).
1. `coeffVal_eq_top_iff`, `_ne_top_iff`, `_eq_coe_iff`: as T016 with `f.coeff i`.
2. `finiteSupport_coeffVal`: `Set.ext`, `mem_finiteSupport`, 1, `Polynomial.mem_support_iff`, `Finset.mem_coe`. `finiteSupport_coeffVal_finite`: rewrite and `Finset.finite_toSet`.
3. `coeffVal_coe`: `funext i`, `PowerSeries.coeffVal_apply`, `Polynomial.coeff_coe`.
4. `isAdmissible_coeffVal := NewtonPolygon.isAdmissible_of_finite (finiteSupport_coeffVal_finite v)`.
5. `hasGaussNorm_coe := (Polynomial.isRestricted_toPowerSeries c f).hasGaussNorm` ([RAG]).
""" + DEC + "L3.17–L3.24.",
  mathlib="`NewtonPolygon.mem_finiteSupport`, `Polynomial.mem_support_iff`, `Finset.mem_coe`, `Finset.finite_toSet`, `Polynomial.coeff_coe`, `Polynomial.isRestricted_toPowerSeries`, `PowerSeries.IsRestricted.hasGaussNorm`.",
  sources="[RM] §2.1.1 (\"the sequence of a polynomial is finitely supported\"), §2.1.3, §2.2.5.",
  gen="As T016.")

# ---------------------------------------------------------------- G4 PowerSeries
t(id='T021', title='`PowerSeries.newtonPolygon`: the specification, anchoring at `0`', file=PS, deps='CLEANUP-5, CLEANUP-7',
  par='yes (with T039–T046, T063)', typ='def API', leaves='L4.1–L4.7',
  defs=[(PS, 'newtonPolygon')],
  decls=[(PS, 'isNewtonPolygonOf_newtonPolygon'), (PS, 'isNewtonPolygonOf_newtonPolygon_of_isRestricted'), (PS, 'newtonPolygon_le'),
         (PS, 'isConvexSeq_newtonPolygon'), (PS, 'newtonPolygon_zero'), (PS, 'newtonPolygon_zero_eq'), (PS, 'newtonPolygon_zero_of_coeff_zero_eq_one')],
  sketch="""1. `isNewtonPolygonOf_newtonPolygon := NewtonPolygon.isNewtonPolygonOf_newtonPolygon (NewtonPolygon.exists_isConvexMinorant_iff_isAdmissible.mpr hf)`; `_of_isRestricted` composes with `hf.isAdmissible_coeffVal hc` (T019).
2. `newtonPolygon_le := (isNewtonPolygonOf_newtonPolygon v hf).le_points k`; `isConvexSeq_newtonPolygon := (…).convex`.
3. `newtonPolygon_zero`: `rw [newtonPolygon_def, coeffVal_zero]`, `NewtonPolygon.newtonPolygon_eq_self NewtonPolygon.isConvexSeq_top`.
4. `newtonPolygon_zero_eq := (isNewtonPolygonOf_newtonPolygon v hf).anchor_eq (fun k hk ↦ absurd hk (Nat.not_lt_zero _)) ((coeffVal_ne_top_iff v).mpr h0)`.
5. `newtonPolygon_zero_of_coeff_zero_eq_one`: 4 with `h0 ▸ one_ne_zero`, then `coeffVal_zero_of_coeff_zero_eq_one`.
""" + DEC + "L4.1–L4.7.",
  mathlib="`NewtonPolygon.isNewtonPolygonOf_newtonPolygon`, `NewtonPolygon.exists_isConvexMinorant_iff_isAdmissible`, `NewtonPolygon.IsNewtonPolygonOf.le_points`, `NewtonPolygon.IsNewtonPolygonOf.convex`, `NewtonPolygon.newtonPolygon_eq_self`, `NewtonPolygon.isConvexSeq_top`, `NewtonPolygon.IsNewtonPolygonOf.anchor_eq`, `Nat.not_lt_zero`, `one_ne_zero`.",
  sources="[RM] §2.2.1 (\"prove the specification holds … under the hypotheses of §2.1.3\"), §2.2.6; [Kob84] IV §4 (Q-Kob-ps); [Gou20] p. 260 (Q-Gou-ps).",
  gen="Admissibility (or restrictedness at a positive radius) is the only hypothesis for the polygon to exist; the anchoring lemmas take `coeff 0 f ≠ 0`.")

t(id='T022', title='Integrality at vertices and rationality on segments', file=PS, deps='T021',
  par='yes (with T039–T046, T063)', typ='theorems', leaves='L4.8–L4.10',
  decls=[(PS, 'exists_eq_embed_of_isVertex'), (PS, 'exists_unitSlope_eq_div_of_isSegment'), (PS, 'exists_int_unitSlope_eq_div_of_isSegment')],
  sketch="""1. `exists_eq_embed_of_isVertex`: `(isNewtonPolygonOf_newtonPolygon v hf).eq_of_isVertex hk : h k = coeffVal v f k`; `hk.1 : h k ≠ ⊤` so `coeff k f ≠ 0` (`coeffVal_ne_top_iff`); `v.exists_eq_coe` gives `γ`; `⟨γ, hγ, by rw [heq, coeffVal_apply, hγ, embedTop_coe]⟩`.
2. `exists_unitSlope_eq_div_of_isSegment`: `IsConvexSeq.unitSlope_eq_div_of_isSegment (isConvexSeq_newtonPolygon v hf) hab haj hjb` (T015); from 1 at the vertices `a` and `b` (`hab.1`, `hab.2.1`) obtain `γ_a`, `γ_b` with `h a = ↑(e γ_a)`, `h b = ↑(e γ_b)`; `⟨γ_b - γ_a, _⟩` with `WithTop.untop₀_coe`, `map_sub`.
3. `exists_int_unitSlope_eq_div_of_isSegment`: 2 for `w`, then `he` rewrites `w.embed n = n`; `⟨n, _⟩` with `Rat.cast_div`, `Rat.cast_intCast`, `Rat.cast_natCast`, `Nat.cast_sub hab.2.2.1.le`.
""" + DEC + "L4.8–L4.10.",
  mathlib="`NewtonPolygon.IsNewtonPolygonOf.eq_of_isVertex`, `NewtonPolygon.IsVertex`, `WithTop.untop₀_coe`, `map_sub`, `Rat.cast_div`, `Rat.cast_intCast`, `Rat.cast_natCast`, `Nat.cast_sub`.",
  sources="[RM] §2.2.3 (\"The height of the polygon at a vertex lies in the image of e. Every unit slope … is (e γ) / l … for Γ = ℤ every slope is a rational number whose denominator divides the length of its segment\"); [Kob84] p. 97 (Q-Kob-vert); plan D4.",
  gen="Rationality for unit slopes in a bounded segment (any series), not for a terminal ray (plan D4); the `ℤ` version takes the embedding to be the cast (`he`).")

t(id='T023', title='Entire series: unbounded slopes tending to `+∞`', file=PS, deps='T022',
  par='yes (with T039–T046, T063)', typ='theorems', leaves='L4.11–L4.12',
  decls=[(PS, 'slopesUnbounded_newtonPolygon_of_forall_isRestricted'), (PS, 'tendsto_unitSlope_newtonPolygon')],
  sketch="""1. `slopesUnbounded_newtonPolygon_of_forall_isRestricted`: `hadm := (hf 1 one_pos).isAdmissible_coeffVal one_pos`; apply `(isNewtonPolygonOf_newtonPolygon v hadm).slopesUnbounded_of_forall_line`: for `σ`, `(hf (v.base ^ σ) (Real.rpow_pos_of_pos v.base_pos σ)).hasGaussNorm` and `(hasGaussNorm_rpow_iff_exists_line v σ).mp` give the line.
2. `tendsto_unitSlope_newtonPolygon`: `WithTop.tendsto_nhds_top_iff`; fix `σ`; `Filter.eventually_atTop`. Let `h := newtonPolygon v f`, convex (T021). From 1's line at slope `σ + 1`: `y + (σ+1) k ≤ h k` for all `k` (`IsNewtonPolygonOf.line_le`). Claim: `∃ N, ∀ j ≥ N, ↑σ < unitSlope h j`. By contradiction (`not_exists`, `not_forall`, `not_lt`): for every `N` some `j ≥ N` has `unitSlope h j ≤ σ`; such `j` has `h j ≠ ⊤` and `h (j+1) ≠ ⊤` (`unitSlope_ne_top_iff`, since `≤ ↑σ < ⊤`), and by `IsConvexSeq.monotoneOn` every finite index `i ≤ j` has `unitSlope h i ≤ σ`; as `j` is unbounded, all finite indices do. Then for `k ≥ a := anchor h`, `h k ≤ h a + (k - a) • ↑σ` (`IsConvexSeq.le_add_nsmul_unitSlope_self` chained, or `eq_add_sum_unitSlope` with the termwise bound), while `h k ≥ ↑(y + (σ+1) k)`: for `k` large, `y + (σ+1)k > (h a).untop₀ + σ (k - a)` (`exists_nat_gt`), contradiction (`WithTop.coe_le_coe`, `WithTop.coe_nsmul`, `nsmul_eq_mul`, `linarith`).
""" + DEC + "L4.11–L4.12 (the first sketch's defect and its repair are recorded there).",
  mathlib="`NewtonPolygon.IsNewtonPolygonOf.slopesUnbounded_of_forall_line`, `Real.rpow_pos_of_pos`, `PowerSeries.IsRestricted.hasGaussNorm`, `WithTop.tendsto_nhds_top_iff`, `Filter.eventually_atTop`, `NewtonPolygon.IsNewtonPolygonOf.line_le`, `NewtonPolygon.unitSlope_ne_top_iff`, `NewtonPolygon.IsConvexSeq.monotoneOn`, `NewtonPolygon.IsConvexSeq.le_add_nsmul_unitSlope_self`, `NewtonPolygon.eq_add_sum_unitSlope`, `NewtonPolygon.anchor_le`, `exists_nat_gt`, `WithTop.coe_le_coe`, `WithTop.coe_nsmul`, `nsmul_eq_mul`, `not_exists`, `not_forall`, `not_lt`.",
  sources="[RM] §2.2.4 (\"For a power series restricted at every positive radius (\\\"entire\\\"), prove SlopesUnbounded holds and the unit slopes tend to +∞\"); [Gou20] Lemma 7.4.8 proof (Q-Gou-L748).",
  gen="Entire = restricted at every positive radius; no anchoring hypothesis (unit slopes before the anchor are `⊤`, which is `> σ`).")

t(id='T024', title='A unit slope above `σ` forces restrictedness at `b ^ σ`', file=PS, deps='CLEANUP-8',
  par='yes (with T039–T046, T063)', typ='theorems', leaves='L4.13–L4.14',
  decls=[(PS, 'isRestricted_rpow_of_lt_unitSlope'), (PS, 'unitSlope_le_of_not_isRestricted')],
  sketch="""1. `isRestricted_rpow_of_lt_unitSlope` (`hjf : h j ≠ ⊤`, `hj : ↑σ < unitSlope h j`): `rcases eq_or_ne (unitSlope h j) ⊤`.
   - `⊤`: `unitSlope_eq_top_iff` with `hjf` gives `h (j+1) = ⊤`; `IsConvexSeq.eq_top_of_le` (anchor `≤ j`, `h j ≠ ⊤`) gives `h k = ⊤` for all `k ≥ j + 1`; `newtonPolygon_le` and `top_le_iff` give `coeffVal v f k = ⊤`, i.e. `coeff k f = 0` for `k > j`: `f` has finite support (`Set.Finite.subset (Set.finite_Iic j)`), so [RAG] `PowerSeries.isRestricted_of_finite_support`.
   - real `τ := (unitSlope h j).untop₀`, `σ < τ`: for `k ≥ j`, `h k ≥ h j + (k - j) • unitSlope h j` (`IsConvexSeq.add_nsmul_unitSlope_le`), so with `h j = ↑η`, `coeffVal v f k ≥ ↑(η + (k - j) τ)`. Term bound: for `k ≥ j` with `coeff k f ≠ 0`, `‖aₖ‖ (b^σ)^k = b ^ (σ k - e γₖ) ≤ b ^ (σ k - η - (k - j) τ) = C · (b ^ (σ - τ)) ^ k` (`norm_coeff_mul_rpow_pow_eq_rpow`-style via T004's `norm_mul_rpow_pow_eq_rpow`, `Real.rpow_le_rpow_left_iff`, `Real.rpow_add`, `Real.rpow_natCast`, `Real.rpow_mul`), `0 ≤ b ^ (σ - τ) < 1` (`Real.rpow_lt_one_of_one_lt_of_neg`, `sub_neg.mpr`); conclude by [RAG] `isRestricted_iff'`, `squeeze_zero'` with `Filter.eventually_atTop` (from `j`) and `tendsto_pow_atTop_nhds_zero_of_lt_one`, `Filter.Tendsto.const_mul`.
2. `unitSlope_le_of_not_isRestricted := not_lt.mp fun hlt ↦ hσ (isRestricted_rpow_of_lt_unitSlope v hf hjf hlt)`.
""" + DEC + "L4.13–L4.14 (the statement repair `hjf` is recorded there).",
  mathlib="`NewtonPolygon.unitSlope_eq_top_iff`, `NewtonPolygon.IsConvexSeq.eq_top_of_le`, `NewtonPolygon.anchor_le`, `top_le_iff`, `Set.Finite.subset`, `Set.finite_Iic`, `PowerSeries.isRestricted_of_finite_support`, `NewtonPolygon.IsConvexSeq.add_nsmul_unitSlope_le`, `WithTop.ne_top_iff_exists`, `Real.rpow_le_rpow_left_iff`, `Real.rpow_add`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_lt_one_of_one_lt_of_neg`, `sub_neg`, `PowerSeries.isRestricted_iff'`, `squeeze_zero'`, `Filter.eventually_atTop`, `tendsto_pow_atTop_nhds_zero_of_lt_one`, `Filter.Tendsto.const_mul`, `not_lt`.",
  sources="[RM] §2.2.4 with the direction corrected (plan D2); [Kob84] Lemma 5 (Q-Kob-L5); [SRC] `RadiusOfConvergence.isRestricted_of_lt_slope`, `not_isRestricted_of_slopes_le`. " + SRC_NOTE,
  gen="The index must be finite for the polygon (`hjf`); the radius is `v.base ^ σ`.")

t(id='T025', title='Multiplying by a constant translates the polygon', file=PS, deps='T024',
  par='yes (with T039–T046, T063)', typ='theorems', leaves='L4.15–L4.18',
  decls=[(PS, 'coeffVal_C_mul'), (PS, 'newtonPolygon_C_mul'), (PS, 'coeff_zero_C_inv_mul'), (PS, 'newtonPolygon_C_inv_mul')],
  sketch="""1. `coeffVal_C_mul`: `funext k`; `coeffVal_apply`, `PowerSeries.coeff_C_mul`, `v.map_mul`, `hc`, `embedTop_add`, `embedTop_coe`, `add_comm`.
2. `newtonPolygon_C_mul`: `rw [newtonPolygon_def, coeffVal_C_mul v hc]`, then `NewtonPolygon.newtonPolygon_add_const hf (v.embed γ)`.
3. `coeff_zero_C_inv_mul`: `PowerSeries.coeff_C_mul`, `inv_mul_cancel₀ h0`.
4. `newtonPolygon_C_inv_mul`: 2 with `c := (coeff 0 f)⁻¹` and `v c = ↑(-γ)` (`v.map_inv`, `h0`, `LinearOrderedAddCommGroup.coe_neg`), then `map_neg` of `e`.
""" + DEC + "L4.15–L4.18.",
  mathlib="`PowerSeries.coeff_C_mul`, `NewtonPolygon.newtonPolygon_add_const`, `inv_mul_cancel₀`, `WithTop.LinearOrderedAddCommGroup.coe_neg`, `map_neg`, `add_comm`.",
  sources="[RM] §2.2.6 (\"every series with coeff 0 f ≠ 0 becomes so after dividing by coeff 0 f, with the polygon translated by a constant\"); [Gou20] Problem 340 (Q-Gou-P340).",
  gen="Any nonzero constant (encoded as `v c = ↑γ`).")

t(id='T026', title='`f (cX)` shears the polygon; `X ^ n * f` shifts it', file=PS, deps='T025',
  par='yes (with T039–T046, T063)', typ='theorems', leaves='L4.19–L4.22',
  decls=[(PS, 'coeffVal_rescale'), (PS, 'newtonPolygon_rescale'), (PS, 'coeffVal_X_pow_mul'), (PS, 'newtonPolygon_X_pow_mul')],
  sketch="""1. `coeffVal_rescale`: `funext k`; `coeffVal_apply`, `PowerSeries.coeff_rescale` (`c ^ k * coeff k f`), `v.map_mul`, `v.map_pow`, `hc`, `WithTop.coe_nsmul`, `embedTop_add`, `embedTop_coe`, `map_nsmul`, `nsmul_eq_mul`, `add_comm`.
2. `newtonPolygon_rescale`: `rw [newtonPolygon_def, coeffVal_rescale v hc]`; `NewtonPolygon.newtonPolygon_add_affine hf 0 (v.embed γ)` and `zero_add` inside the coercion (`funext`, `congr`).
3. `coeffVal_X_pow_mul`: `funext k`; `coeffVal_apply`, `PowerSeries.coeff_X_pow_mul'`, `NewtonPolygon.shiftRight`; `split_ifs`: `coeffVal_apply` or `map_zero`, `v.map_zero`, `embedTop_top`.
4. `newtonPolygon_X_pow_mul`: `rw [newtonPolygon_def, coeffVal_X_pow_mul]`, `NewtonPolygon.newtonPolygon_shiftRight hf n` (T011).
""" + DEC + "L4.19–L4.22.",
  mathlib="`PowerSeries.coeff_rescale`, `WithTop.coe_nsmul`, `map_nsmul`, `nsmul_eq_mul`, `NewtonPolygon.newtonPolygon_add_affine`, `zero_add`, `PowerSeries.coeff_X_pow_mul'`, `map_zero`.",
  sources="[RM] §2.2.7 (\"the polygon of f (cX) is sheared by e (v c), the polygon of X^n · f is translated right by n\"); [Kob84] p. 101 (Q-Kob-shear).",
  gen="`rescale c f = f (cX)` for any `c ≠ 0` (as `v c = ↑γ`); `n` any natural.")

t(id='T027', title='Compatible base change and change of valuation', file=PS, deps='CLEANUP-9',
  par='yes (with T039–T046, T063)', typ='theorems', leaves='L4.23–L4.27',
  decls=[(PS, 'coeffVal_map'), (PS, 'newtonPolygon_map'), (PS, 'coeffVal_eq_scaleHeight'), (PS, 'isAdmissible_coeffVal_iff'), (PS, 'newtonPolygon_eq_scaleHeight')],
  sketch="""1. `coeffVal_map`: `funext k`; `coeffVal_apply`, `PowerSeries.coeff_map`, `hφ`, `NormedAddValuation.embedTop_apply`, `he`.
2. `newtonPolygon_map`: `simp only [newtonPolygon_def, coeffVal_map v w φ hφ he]`.
3. `coeffVal_eq_scaleHeight`: `funext k`; `coeffVal_apply`, `NewtonPolygon.scaleHeight_apply`, `v.embedTop_apply_eq_map w` (T006).
4. `isAdmissible_coeffVal_iff`: `rw [coeffVal_eq_scaleHeight v w]`, `NewtonPolygon.isAdmissible_scaleHeight_iff (v.scale_pos w)`.
5. `newtonPolygon_eq_scaleHeight`: `rw [newtonPolygon_def, coeffVal_eq_scaleHeight v w]`, `NewtonPolygon.newtonPolygon_scaleHeight (v.scale_pos w) hf`.
""" + DEC + "L4.23–L4.27.",
  mathlib="`PowerSeries.coeff_map`, `NewtonPolygon.isAdmissible_scaleHeight_iff`, `NewtonPolygon.newtonPolygon_scaleHeight`, `funext`.",
  sources="[RM] §2.2.7 (\"unchanged under an isometric scalar extension L/K carrying a compatible normed additive valuation\"), §2.2.8 (Q-RM-2.2.8); plan D7, D9.",
  gen="The extension is any ring hom `φ` with compatible `w` (plan D7); the change of valuation any second bundle on `K`.")

# ---------------------------------------------------------------- G5 Polynomial
t(id='T028', title='`Polynomial.newtonPolygon`: coercion, specification', file=PO, deps='CLEANUP-10',
  par='yes (with T039–T046, T063)', typ='def API', leaves='L5.1–L5.5',
  defs=[(PO, 'newtonPolygon')],
  decls=[(PO, 'newtonPolygon_coe'), (PO, 'isNewtonPolygonOf_newtonPolygon'), (PO, 'newtonPolygon_le'), (PO, 'isConvexSeq_newtonPolygon'), (PO, 'newtonPolygon_zero')],
  sketch="""1. `newtonPolygon_coe`: `rw [PowerSeries.newtonPolygon_def, newtonPolygon_def, coeffVal_coe]`.
2. `isNewtonPolygonOf_newtonPolygon := NewtonPolygon.isNewtonPolygonOf_newtonPolygon (NewtonPolygon.exists_isConvexMinorant_iff_isAdmissible.mpr (isAdmissible_coeffVal v))`; `newtonPolygon_le`, `isConvexSeq_newtonPolygon` are its fields.
3. `newtonPolygon_zero`: `coeffVal v 0 = fun _ ↦ ⊤` (`funext`, `Polynomial.coeff_zero`, `v.map_zero`, `embedTop_top`), then `newtonPolygon_eq_self isConvexSeq_top`.
""" + DEC + "L5.1–L5.5.",
  mathlib="`NewtonPolygon.isNewtonPolygonOf_newtonPolygon`, `NewtonPolygon.exists_isConvexMinorant_iff_isAdmissible`, `NewtonPolygon.newtonPolygon_eq_self`, `NewtonPolygon.isConvexSeq_top`, `Polynomial.coeff_zero`.",
  sources="[RM] §2.2.1, §2.2.5 (\"the polygon of a polynomial, viewed as a power series, is the polygon of the polynomial\").",
  gen="No hypothesis: every polynomial has a polygon.")

t(id='T029', title='The polygon is `⊤` exactly outside `[natTrailingDegree f, natDegree f]`', file=PO, deps='T028',
  par='yes (with T039–T046, T063)', typ='theorems', leaves='L5.6–L5.9',
  decls=[(PO, 'newtonPolygon_eq_top_of_lt_natTrailingDegree'), (PO, 'newtonPolygon_eq_top_of_natDegree_lt'), (PO, 'newtonPolygon_ne_top'), (PO, 'newtonPolygon_eq_top_iff')],
  sketch="""1. `_of_lt_natTrailingDegree`: `(isNewtonPolygonOf_newtonPolygon v).eq_top_of_forall_eq_top`: for `j ≤ k < natTrailingDegree f`, `coeff f j = 0` (`Polynomial.coeff_eq_zero_of_lt_natTrailingDegree`), `coeffVal_eq_top_iff`.
2. `_of_natDegree_lt`: `.eq_top_of_forall_le` with `Polynomial.coeff_eq_zero_of_natDegree_lt` for `j ≥ k > natDegree f`.
3. `newtonPolygon_ne_top`: `.ne_top_of_le_of_le` with `a := natTrailingDegree f` (`coeffVal_ne_top_iff`: the trailing coefficient `f.coeff f.natTrailingDegree = f.trailingCoeff ≠ 0`, `Polynomial.trailingCoeff_eq_zero.not.mpr hf`) and `b := natDegree f` (`Polynomial.coeff_natDegree`, `Polynomial.leadingCoeff_eq_zero.not.mpr hf`).
4. `newtonPolygon_eq_top_iff`: `⟨fun h ↦ by_contra (fun hn ↦ newtonPolygon_ne_top v hf (not_lt.mp (not_or.mp hn).1) (not_lt.mp (not_or.mp hn).2) h), fun h ↦ h.elim (newtonPolygon_eq_top_of_lt_natTrailingDegree v) (newtonPolygon_eq_top_of_natDegree_lt v)⟩`.
""" + DEC + "L5.6–L5.9.",
  mathlib="`NewtonPolygon.IsNewtonPolygonOf.eq_top_of_forall_eq_top`, `NewtonPolygon.IsNewtonPolygonOf.eq_top_of_forall_le`, `NewtonPolygon.IsNewtonPolygonOf.ne_top_of_le_of_le`, `Polynomial.coeff_eq_zero_of_lt_natTrailingDegree`, `Polynomial.coeff_eq_zero_of_natDegree_lt`, `Polynomial.trailingCoeff_eq_zero`, `Polynomial.trailingCoeff`, `Polynomial.coeff_natDegree`, `Polynomial.leadingCoeff_eq_zero`, `not_or`, `not_lt`.",
  sources="[RM] §2.2.2 (\"anchored at the order of vanishing at 0, its last vertex is at the degree\"), §0.2.5.",
  gen="`f ≠ 0` only where a finite value is asserted.")

t(id='T030', title='Anchor, last point and the two end vertices', file=PO, deps='T029',
  par='yes (with T039–T046, T063)', typ='theorems', leaves='L5.10–L5.14',
  decls=[(PO, 'newtonPolygon_natTrailingDegree'), (PO, 'newtonPolygon_natDegree'), (PO, 'anchor_newtonPolygon'), (PO, 'isVertex_natTrailingDegree'), (PO, 'isVertex_natDegree')],
  sketch="""1. `newtonPolygon_natTrailingDegree := (isNewtonPolygonOf_newtonPolygon v).anchor_eq (fun k hk ↦ (coeffVal_eq_top_iff v).mpr (Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hk)) ((coeffVal_ne_top_iff v).mpr (Polynomial.trailingCoeff_eq_zero.not.mpr hf))`.
2. `isVertex_natDegree := NewtonPolygon.isVertex_of_succ_eq_top (isConvexSeq_newtonPolygon v) (newtonPolygon_ne_top v hf (Polynomial.natTrailingDegree_le_natDegree f) le_rfl) (newtonPolygon_eq_top_of_natDegree_lt v (Nat.lt_succ_self _))`.
3. `newtonPolygon_natDegree := (isNewtonPolygonOf_newtonPolygon v).eq_of_isVertex (isVertex_natDegree v hf)`.
4. `anchor_newtonPolygon`: `le_antisymm (NewtonPolygon.anchor_le (newtonPolygon_ne_top v hf le_rfl (natTrailingDegree_le_natDegree f)))` and `not_lt.mp fun h ↦ NewtonPolygon.anchor_mem ⟨_, …⟩ (newtonPolygon_eq_top_of_lt_natTrailingDegree v h)` (the anchor carries a finite value, `anchor_mem`).
5. `isVertex_natTrailingDegree`: `anchor_newtonPolygon v hf ▸ NewtonPolygon.isVertex_anchor ⟨_, newtonPolygon_ne_top v hf le_rfl (natTrailingDegree_le_natDegree f)⟩`.
""" + DEC + "L5.10–L5.14.",
  mathlib="`NewtonPolygon.IsNewtonPolygonOf.anchor_eq`, `NewtonPolygon.isVertex_of_succ_eq_top`, `NewtonPolygon.IsNewtonPolygonOf.eq_of_isVertex`, `NewtonPolygon.anchor_le`, `NewtonPolygon.anchor_mem`, `NewtonPolygon.isVertex_anchor`, `Polynomial.natTrailingDegree_le_natDegree`, `Polynomial.coeff_eq_zero_of_lt_natTrailingDegree`, `Polynomial.trailingCoeff_eq_zero`, `Nat.lt_succ_self`, `le_antisymm`, `not_lt`.",
  sources="[RM] §2.2.2; [Gou20] p. 252 (Q-Gou-feat: \"(0,0) and (n, v_p(a_n)) will always be vertices\").",
  gen="`f ≠ 0`.")

t(id='T031', title='The slope indices, unbounded slopes, anchoring at the origin', file=PO, deps='CLEANUP-11',
  par='yes (with T039–T046, T063)', typ='theorems', leaves='L5.15–L5.18',
  decls=[(PO, 'slopeIndices_newtonPolygon'), (PO, 'slopeIndices_newtonPolygon_finite'), (PO, 'slopesUnbounded_newtonPolygon'), (PO, 'newtonPolygon_zero_of_coeff_zero_eq_one')],
  sketch="""1. `slopeIndices_newtonPolygon`: `Set.ext j`; `NewtonPolygon.mem_slopeIndices_iff`, `newtonPolygon_eq_top_iff v hf` at `j` and `j + 1` (negated: `not_or`, `not_lt`), `Set.mem_Ico`; `omega`.
2. `slopeIndices_newtonPolygon_finite := (isNewtonPolygonOf_newtonPolygon v).slopeIndices_finite (finiteSupport_coeffVal_finite v)`.
3. `slopesUnbounded_newtonPolygon := NewtonPolygon.slopesUnbounded_of_finite (slopeIndices_newtonPolygon_finite v)`.
4. `newtonPolygon_zero_of_coeff_zero_eq_one`: `(isNewtonPolygonOf_newtonPolygon v).anchor_eq (fun k hk ↦ absurd hk (Nat.not_lt_zero _)) _` then `coeffVal_apply`, `h0`, `v.embedTop_map_one`.
""" + DEC + "L5.15–L5.18.",
  mathlib="`NewtonPolygon.mem_slopeIndices_iff`, `Set.mem_Ico`, `NewtonPolygon.IsNewtonPolygonOf.slopeIndices_finite`, `NewtonPolygon.slopesUnbounded_of_finite`, `NewtonPolygon.IsNewtonPolygonOf.anchor_eq`, `Nat.not_lt_zero`, `not_or`, `not_lt`.",
  sources="[RM] §2.2.2 (\"exactly natDegree f - order f unit slopes, and SlopesUnbounded holds\"), §2.2.6.",
  gen="As T029.")

t(id='T032', title='`newtonSlopes`: cardinality `natDegree − natTrailingDegree`, counts', file=PO, deps='T031',
  par='yes (with T039–T046, T063)', typ='def API', leaves='L5.19–L5.20',
  defs=[(PO, 'newtonSlopes')],
  decls=[(PO, 'card_newtonSlopes'), (PO, 'count_newtonSlopes')],
  sketch="""`newtonSlopes v f = slopeMultiset (newtonPolygon v f)` (no `sorry`).
1. `card_newtonSlopes`: `NewtonPolygon.card_slopeMultiset (slopeIndices_newtonPolygon_finite v)` gives `(slopeIndices _).ncard`. `rcases eq_or_ne f 0`: for `f = 0`, `slopeIndices (newtonPolygon v 0) = ∅` (`newtonPolygon_zero`, `mem_slopeIndices_iff`, `unitSlope_eq_top_iff`), `Set.ncard_empty`, `Polynomial.natDegree_zero`, `Polynomial.natTrailingDegree_zero`; else `slopeIndices_newtonPolygon v hf`, `Set.ncard_eq_toFinset_card'`, `Set.toFinset_Ico`, `Nat.card_Ico`.
2. `count_newtonSlopes := NewtonPolygon.count_slopeMultiset (slopeIndices_newtonPolygon_finite v) σ`.
""" + DEC + "L5.19–L5.20.",
  mathlib="`NewtonPolygon.card_slopeMultiset`, `NewtonPolygon.count_slopeMultiset`, `NewtonPolygon.mem_slopeIndices_iff`, `NewtonPolygon.unitSlope_eq_top_iff`, `Set.ncard_empty`, `Set.ncard_eq_toFinset_card'`, `Set.toFinset_Ico`, `Nat.card_Ico`, `Polynomial.natDegree_zero`, `Polynomial.natTrailingDegree_zero`.",
  sources="[RM] §2.2.2 (\"Define Polynomial.newtonSlopes v f : Multiset ℝ and prove its cardinality is natDegree f - order f\"); [Gou20] (Q-Gou-feat); [Ked07] §1 (Q-Ked-def, cardinality).",
  gen="Holds for `f = 0` too (both sides `0`).")

t(id='T033', title='Rationality of the slopes of a polynomial', file=PO, deps='T032',
  par='yes (with T039–T046, T063)', typ='theorems', leaves='L5.21–L5.23',
  decls=[(PO, 'exists_isSegment_of_mem_slopeIndices'), (PO, 'exists_unitSlope_eq_div'), (PO, 'exists_int_unitSlope_eq_div')],
  sketch="""1. `exists_isSegment_of_mem_slopeIndices := NewtonPolygon.exists_isSegment_of_mem_slopeIndices (isConvexSeq_newtonPolygon v) (slopeIndices_newtonPolygon_finite v) hj` (T015).
2. `exists_unitSlope_eq_div`: obtain `a, b, hab, haj, hjb` from 1; `rw [← newtonPolygon_coe] at *` and `PowerSeries.exists_unitSlope_eq_div_of_isSegment v (isAdmissible_coeffVal v |> (coeffVal_coe v).symm ▸ ·) hab haj hjb` (adjust the admissibility through `coeffVal_coe`), obtaining `γ`; `⟨γ, b - a, Nat.sub_pos_of_lt hjb_lt, by rwa [Nat.cast_sub hab.2.2.1.le]⟩`.
3. `exists_int_unitSlope_eq_div`: as 2 with `PowerSeries.exists_int_unitSlope_eq_div_of_isSegment he`, returning `⟨a, b, n, hab, haj, hjb, _⟩`.
""" + DEC + "L5.21–L5.23.",
  mathlib="`Nat.sub_pos_of_lt`, `Nat.cast_sub`.",
  sources="[RM] §2.2.3; [Kob84] p. 97 (Q-Kob-vert).",
  gen="Every unit slope of a polynomial (all lie in bounded segments); the `ℤ` form takes `he`.")

t(id='T034', title='[M2] The polygon of `reverse f` is the reflection', file=PO, deps='CLEANUP-ALL-2',
  par='no', typ='theorems', leaves='L5.24–L5.25', milestone='M2 ([RM] §2.2.7)',
  decls=[(PO, 'coeffVal_reverse'), (PO, 'newtonPolygon_reverse')],
  sketch="""1. `coeffVal_reverse`: `funext k`; `coeffVal_apply`, `Polynomial.coeff_reverse`; `rcases le_or_lt k f.natDegree`: `Polynomial.revAt_le hk` and `NewtonPolygon.reflect_of_le hk`; else `Polynomial.revAt_eq_self_of_lt hk`, `Polynomial.coeff_eq_zero_of_natDegree_lt hk`, `v.map_zero`, `embedTop_top`, `NewtonPolygon.reflect_of_lt hk`.
2. `newtonPolygon_reverse`: `rw [newtonPolygon_def, newtonPolygon_def, coeffVal_reverse]`; `NewtonPolygon.newtonPolygon_reflect` (T013) with `hv : ∀ k, natDegree f < k → coeffVal v f k = ⊤` from `coeffVal_eq_top_iff` and `Polynomial.coeff_eq_zero_of_natDegree_lt`.
""" + DEC + "L5.24–L5.25.",
  mathlib="`Polynomial.coeff_reverse`, `Polynomial.revAt_le`, `Polynomial.revAt_eq_self_of_lt`, `Polynomial.coeff_eq_zero_of_natDegree_lt`, `le_or_gt`.",
  sources="[RM] §2.2.7 (\"the polygon of Polynomial.reverse f is the reflection i ↦ h (d - i) … ⚠ … §6.2 depends on it; it is a milestone, not a remark\").",
  gen="Any polynomial (including `0`).")

t(id='T035', title='`f (cX)` for polynomials: the coercion is `rescale`, the polygon is sheared', file=PO, deps='T034',
  par='yes (with T039–T046, T063)', typ='theorems', leaves='L5.26–L5.27',
  decls=[(PO, 'coe_comp_C_mul_X'), (PO, 'newtonPolygon_comp_C_mul_X')],
  sketch="""1. `coe_comp_C_mul_X`: both sides are ring homs applied to `f`: `(Polynomial.coeToPowerSeries.ringHom).comp (Polynomial.compRingHom (C c * X))` and `(PowerSeries.rescale c).comp Polynomial.coeToPowerSeries.ringHom`. Prove the equality of homs by `Polynomial.ringHom_ext`: on `C a`: `Polynomial.C_comp`, `Polynomial.coe_C`, and `PowerSeries.rescale c (PowerSeries.C a) = PowerSeries.C a` (`PowerSeries.ext`, `coeff_rescale`, `PowerSeries.coeff_C`: `c ^ n * (if n = 0 then a else 0)`, `split_ifs`, `pow_zero`, `mul_zero`); on `X`: `Polynomial.X_comp`, `Polynomial.coe_mul`, `coe_C`, `coe_X`, `PowerSeries.rescale_X`. Then `DFunLike.congr_fun` at `f`.
2. `newtonPolygon_comp_C_mul_X`: `rw [← newtonPolygon_coe, coe_comp_C_mul_X, PowerSeries.newtonPolygon_rescale v _ hc, newtonPolygon_coe]` with admissibility from `isAdmissible_coeffVal v` transported by `coeffVal_coe`.
""" + DEC + "L5.26–L5.27 (plan D8).",
  mathlib="`Polynomial.coeToPowerSeries.ringHom`, `Polynomial.compRingHom`, `Polynomial.ringHom_ext`, `Polynomial.C_comp`, `Polynomial.X_comp`, `Polynomial.coe_C`, `Polynomial.coe_X`, `Polynomial.coe_mul`, `PowerSeries.rescale_X`, `PowerSeries.coeff_rescale`, `PowerSeries.coeff_C`, `PowerSeries.ext`, `DFunLike.congr_fun`, `pow_zero`, `mul_zero`.",
  sources="[RM] §2.2.7 (\"the polygon of f (cX) is sheared by e (v c)\"); [Kob84] p. 101 (Q-Kob-shear).",
  gen="`c` any element (the shear statement names `γ` with `v c = ↑γ`, so `c ≠ 0`).")

t(id='T036', title='Polynomial operations: shift, constants, base change, change of valuation', file=PO, deps='T035',
  par='yes (with T039–T046, T063)', typ='theorems', leaves='L5.28–L5.33',
  decls=[(PO, 'newtonPolygon_X_pow_mul'), (PO, 'newtonPolygon_C_mul'), (PO, 'newtonPolygon_C_inv_mul'), (PO, 'newtonPolygon_map'), (PO, 'newtonPolygon_eq_scaleHeight'), (PO, 'newtonSlopes_eq_map')],
  sketch="""Each is the series statement (T025–T027) read through `newtonPolygon_coe` and the coercion lemmas, or the direct coefficient computation.
1. `newtonPolygon_X_pow_mul`: `rw [← newtonPolygon_coe, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, PowerSeries.newtonPolygon_X_pow_mul v hadm n, newtonPolygon_coe]` (`hadm` from `isAdmissible_coeffVal v` via `coeffVal_coe`).
2. `newtonPolygon_C_mul`: same with `Polynomial.coe_C`, `PowerSeries.newtonPolygon_C_mul`. `newtonPolygon_C_inv_mul`: `PowerSeries.newtonPolygon_C_inv_mul` with `Polynomial.coeff_coe` for `coeff 0`.
3. `newtonPolygon_map`: `funext`-free: `simp only [newtonPolygon_def, coeffVal_apply, Polynomial.coeff_map, hφ, NormedAddValuation.embedTop_apply, he]`.
4. `newtonPolygon_eq_scaleHeight`: `coeffVal w f = scaleHeight (v.scale w) (coeffVal v f)` (`funext`, `v.embedTop_apply_eq_map w`), then `NewtonPolygon.newtonPolygon_scaleHeight (v.scale_pos w) (isAdmissible_coeffVal v)`.
5. `newtonSlopes_eq_map`: `newtonSlopes_def`, 4, `NewtonPolygon.slopeMultiset_scaleHeight (v.scale_pos w) (slopeIndices_newtonPolygon_finite v)`.
""" + DEC + "L5.28–L5.33.",
  mathlib="`Polynomial.coe_mul`, `Polynomial.coe_pow`, `Polynomial.coe_X`, `Polynomial.coe_C`, `Polynomial.coeff_coe`, `Polynomial.coeff_map`, `NewtonPolygon.newtonPolygon_scaleHeight`, `NewtonPolygon.slopeMultiset_scaleHeight`.",
  sources="[RM] §2.2.6–§2.2.8.",
  gen="As the series versions.")

# ---------------------------------------------------------------- G6 Extension
t(id='T037', title='Compatibility of `ofNormAddVal` and `ofNormAddValQ` along an extension', file=EX, deps='CLEANUP-13',
  par='yes (with T039–T046, T063)', typ='theorems', leaves='L6.1–L6.4',
  decls=[(EX, 'ofNormAddVal_algebraMap'), (EX, 'ofNormAddVal_embed_eq'), (EX, 'ofNormAddValQ_algebraMap'), (EX, 'ofNormAddValQ_embed_eq')],
  sketch="""1. `ofNormAddVal_algebraMap`: `simpa using NormedField.normAddVal_algebraMap (L := L) x` (`ofNormAddVal_apply` is `rfl`).
2. `ofNormAddVal_embed_eq := rfl` (both `AddMonoidHom.id ℝ`).
3. `ofNormAddValQ_algebraMap`: `NormedField.normAddValQ_algebraMap π x` (Layer 1; the instance `NormedField.isCommensurable_algebraMap` supplies `(valuation (K := L)).IsCommensurable (algebraMap K L π)`).
4. `ofNormAddValQ_embed_eq := rfl`.
""" + DEC + "L6.1–L6.4.",
  mathlib="`NormedField.normAddVal_algebraMap`, `NormedField.normAddValQ_algebraMap`, `NormedField.isCommensurable_algebraMap`.",
  sources="[RM] §1.5.1–§1.5.2, §2.2.7 (plan D7).",
  gen="`L` any ultrametric nontrivially normed `K`-algebra field for the real member; `K` complete and `L/K` algebraic for the rational member (Layer 1's hypotheses, explicit `variable`s).")

t(id='T038', title='The polygon is unchanged under a compatible extension', file=EX, deps='T037',
  par='yes (with T039–T046, T063)', typ='theorems', leaves='L6.5–L6.8',
  decls=[(EX, 'Polynomial.newtonPolygon_ofNormAddVal_map'), (EX, 'PowerSeries.newtonPolygon_ofNormAddVal_map'),
         (EX, 'Polynomial.newtonPolygon_ofNormAddValQ_map'), (EX, 'PowerSeries.newtonPolygon_ofNormAddValQ_map')],
  sketch="""Each is `Polynomial.newtonPolygon_map` / `PowerSeries.newtonPolygon_map` (T036 / T027) with `φ := algebraMap K L`, `hφ := ofNormAddVal_algebraMap` resp. `ofNormAddValQ_algebraMap π`, and `he := ofNormAddVal_embed_eq` resp. `ofNormAddValQ_embed_eq π`.
""" + DEC + "L6.5–L6.8.",
  mathlib="`algebraMap`.",
  sources="[RM] §2.2.7.",
  gen="As T037. `ofNormAddValZ` is deliberately not covered (ramification scales the polygon; Layer 1 §1.3.6).")
