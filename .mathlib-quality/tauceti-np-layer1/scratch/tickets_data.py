# -*- coding: utf-8 -*-
"""Ticket data for the board `tauceti-np-layer1`, part A (NegLog … Discrete). Statements are NOT stored
here: the generator copies them verbatim from the skeleton (through sorries.json). A ticket lists its
declarations as (file, name) or (file, name, occurrence). Part B (Normed … Examples, cleanups, order)
is `tickets_data_b.py`; this module re-exports everything the generator needs."""

NL = 'NegLog.lean'
RL = 'RatLog.lean'
BA = 'Basic.lean'
RO = 'RankOne.lean'
CO = 'Commensurable.lean'
DI = 'Discrete.lean'

T = []  # proof tickets, in board order

def t(**kw):
    T.append(kw)

SRC_NOTE = ("[SRC] is read-only: port the proof with the new names (`negLogOrderAddIso → orderAddIsoWithTop`, "
            "`expMap → mapAddHom'`), never `import PhD.Main.*`.")

# ---------------------------------------------------------------- G1 NegLog
t(id='T001', title='`negLog`: zero, exp, one, `eq_top`, `eq_coe`, multiplicativity', file=NL, deps='none',
  par='yes (with T005)', typ='lemmas', leaves='L1.1–L1.6',
  decls=[(NL, 'negLog_zero'), (NL, 'negLog_exp'), (NL, 'negLog_eq_top'), (NL, 'negLog_one'), (NL, 'negLog_eq_coe'), (NL, 'negLog_mul')],
  sketch="""1. `negLog_zero`, `negLog_exp`: `rfl` — `negLog` is `expRecOn x ⊤ (fun m ↦ ↑(-m))` and `expRecOn` computes on
   the constructors `0` (= `none`) and `exp m` (= `↑(ofAdd m)`) definitionally (`WithZero.expRecOn_zero`,
   `WithZero.expRecOn_exp` are `rfl`).
2. `negLog_eq_top`: `induction x using WithZero.expRecOn with | zero => simp | exp a => simp
   [-WithTop.LinearOrderedAddCommGroup.coe_neg]`. ⚠ Exclude `coe_neg`: otherwise simp rewrites `↑(-a)` to
   `-↑a` and no longer sees `WithTop.coe_ne_top`. In the `exp` case both sides are false
   (`WithTop.coe_ne_top`, `WithZero.exp_ne_zero`).
3. `negLog_one`: `rw [← WithZero.exp_zero, negLog_exp, neg_zero, WithTop.coe_zero]`.
4. `negLog_eq_coe`: `induction x using WithZero.expRecOn`; zero case: `exact ⟨fun h ↦ absurd h (by simp),
   fun h ↦ absurd h.symm WithZero.exp_ne_zero⟩`; exp case: `rw [negLog_exp, WithTop.coe_inj, WithZero.exp_inj,
   neg_eq_iff_eq_neg]`.
5. `negLog_mul`: double `expRecOn` induction; the two zero cases close by `simp` (`WithTop.top_add`,
   `WithTop.add_top`, `zero_mul`, `mul_zero`); the exp–exp case: `rw [← WithZero.exp_add, negLog_exp, negLog_exp,
   negLog_exp, neg_add, WithTop.coe_add]`.
[SRC] `PhD/Main/ForMathlib/Algebra/Order/GroupWithZero/WithZero.lean`, lemmas of the same names.""",
  mathlib="`WithZero.expRecOn`, `WithZero.expRecOn_zero`, `WithZero.expRecOn_exp`, `WithZero.exp_ne_zero`, `WithZero.exp_zero`, `WithZero.exp_inj`, `WithZero.exp_add`, `WithTop.coe_ne_top`, `WithTop.coe_zero`, `WithTop.coe_inj`, `WithTop.coe_add`, `WithTop.top_add`, `WithTop.add_top`, `WithTop.LinearOrderedAddCommGroup.coe_neg`, `neg_eq_iff_eq_neg`, `neg_add`, `neg_zero`.",
  sources="[RM] §1.1.1 (Q1.1), [PR] #43578 (Q1.6), [BGR] 1.5.2 (Q1.5); decomposition L1.1–L1.6. " + SRC_NOTE,
  gen="Any `[AddCommGroup M]`; no order needed for these six (the order enters at T002). Universe-polymorphic.")

t(id='T002', title='`negLog` reverses the order; the isomorphism `orderAddIsoWithTop`', file=NL, deps='T001',
  par='yes (with T005, T006)', typ='lemmas + def fields', leaves='L1.7–L1.10',
  decls=[(NL, 'negLog_le_negLog'), (NL, 'negLog_lt_negLog'), (NL, 'orderAddIsoWithTop'), (NL, 'orderAddIsoWithTop_apply')],
  sketch="""1. `negLog_le_negLog`: double `expRecOn` induction. zero–any: `simp` (`le_top` on the left, `zero_le'` on the
   right). exp–zero: `simp` (`↑(-a) ≤ ⊤` true, `0 ≤ exp b` true). exp–exp: `rw [negLog_exp, negLog_exp,
   WithTop.coe_le_coe, neg_le_neg_iff, WithZero.exp_le_exp]`.
2. `negLog_lt_negLog`: `lt_iff_lt_of_le_iff_le negLog_le_negLog` (the `≤` lemma with the roles of `x, y`
   swapped gives the strict version on a linear order).
3. `orderAddIsoWithTop` fields: `left_inv x`: `induction x using WithZero.expRecOn with | zero => rfl | exp a =>
   show WithZero.exp (- -a) = WithZero.exp a; rw [neg_neg]`. `right_inv y`: `induction y using WithTop.recTopCoe
   with | top => rfl | coe m => show negLog (WithZero.exp (-m)) = (m : WithTop M); rw [negLog_exp, neg_neg]`.
   `map_add' := negLog_mul`. `map_le_map_iff' := negLog_le_negLog`. (After this the def's signature gains
   `[IsOrderedAddMonoid M]`, as intended — see decomposition L1.9.)
4. `orderAddIsoWithTop_apply`: `rfl`.
[SRC] `negLog_le_negLog`, `negLogOrderAddIso`, `negLogOrderAddIso_apply`.""",
  mathlib="`WithZero.exp_le_exp`, `WithTop.coe_le_coe`, `WithTop.recTopCoe`, `neg_le_neg_iff`, `neg_neg`, `le_top`, `zero_le'`, `lt_iff_lt_of_le_iff_le`.",
  sources="[RM] §1.1.1 (Q1.1), [PR] #43578 (Q1.6); decomposition L1.7–L1.10. " + SRC_NOTE,
  gen="`[AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]` — exactly the instances `WithZero.exp_le_exp` needs.")

t(id='T003', title="`mapAddHom'`: value on `exp`, strict monotonicity, naturality of `negLog`", file=NL, deps='T002',
  par='yes (with T005, T006)', typ='lemmas', leaves='L1.11–L1.13',
  decls=[(NL, "mapAddHom'_exp"), (NL, "mapAddHom'_strictMono"), (NL, "negLog_mapAddHom'")],
  sketch="""1. `mapAddHom'_exp`: `rfl` (`WithZero.map'_coe`; `AddMonoidHom.toMultiplicative f (ofAdd m) = ofAdd (f m)`
   definitionally).
2. `mapAddHom'_strictMono`: `WithZero.map'_strictMono fun _ _ h ↦ hf h` — the Mathlib lemma takes strict
   monotonicity of the underlying `Multiplicative M →* Multiplicative N` hom, which is `hf` read through the
   type synonyms.
3. `negLog_mapAddHom'`: `induction x using WithZero.expRecOn with | zero => rfl | exp a => rw [mapAddHom'_exp,
   negLog_exp, negLog_exp, WithTop.map_coe, map_neg]` (zero case: `map_zero` and `WithTop.map_top` are both
   `rfl`).
[SRC] `expMap_exp`, `expMap_strictMono`, `negLog_expMap`.""",
  mathlib="`WithZero.map'`, `WithZero.map'_coe`, `WithZero.map'_strictMono`, `AddMonoidHom.toMultiplicative`, `WithTop.map_coe`, `WithTop.map_top`, `map_neg`, `map_zero`.",
  sources="[RM] §1.1.2 (Q1.2), [PR] #43578 (Q1.6); decomposition L1.11–L1.13. " + SRC_NOTE,
  gen="`[AddCommGroup M] [AddCommGroup N]`, plus `[Preorder M] [Preorder N]` for the monotonicity statement only.")

t(id='T004', title='The real line: `NNReal.toRealMultZero` and `WithZeroMulReal.toNNReal`', file=NL, deps='CLEANUP-1',
  par='yes (with T005, T006)', typ='def fields + lemmas', leaves='R3/R4 inputs (`toRealMultZero_strictMono`, `toNNReal_exp`, `toNNReal_strictMono`)',
  decls=[(NL, 'toRealMultZero'), (NL, 'toRealMultZero_of_ne_zero'), (NL, 'toRealMultZero_strictMono'), (NL, 'toNNReal'), (NL, 'toNNReal_exp'), (NL, 'toNNReal_strictMono')],
  sketch="""1. `toRealMultZero` fields: `map_zero' := if_pos rfl`; `map_one'`: `rw [if_neg one_ne_zero]; simp`
   (`NNReal.coe_one`, `Real.log_one`, `WithZero.exp_zero`); `map_mul' x y`: `rcases eq_or_ne x 0 with rfl | hx`
   (`simp`), same for `y`, then `rw [if_neg (mul_ne_zero hx hy), if_neg hx, if_neg hy, ← WithZero.exp_add,
   NNReal.coe_mul, Real.log_mul (by exact_mod_cast hx) (by exact_mod_cast hy)]`.
2. `toRealMultZero_of_ne_zero`: `if_neg hx`.
3. `toRealMultZero_strictMono`: `intro x y hxy`; `hy : y ≠ 0 := (bot_le.trans_lt hxy).ne'`; if `x = 0`:
   `rw [map_zero, toRealMultZero_of_ne_zero hy]; exact WithZero.exp_pos`; else `rw [toRealMultZero_of_ne_zero hx,
   toRealMultZero_of_ne_zero hy, WithZero.exp_lt_exp]; exact Real.log_lt_log (by exact_mod_cast hx.bot_lt)
   (by exact_mod_cast hxy)`.
4. `toNNReal` fields: `map_zero' := if_pos rfl`; `map_one'`: `rw [if_neg one_ne_zero, WithZero.log_one,
   NNReal.rpow_zero]`; `map_mul'`: cases on `x = 0`, `y = 0` (`simp`), then `rw [if_neg (mul_ne_zero hx hy),
   if_neg hx, if_neg hy, WithZero.log_mul hx hy, NNReal.rpow_add he]`.
5. `toNNReal_exp`: `simp only [toNNReal, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, if_neg WithZero.exp_ne_zero,
   WithZero.log_exp]`.
6. `toNNReal_strictMono`: `intro x y hxy`; `hy : y ≠ 0`; `x = 0`: `lift y to ℝ using hy with t; rw [map_zero,
   toNNReal_exp]; exact NNReal.rpow_pos (zero_lt_one.trans he)`; else `lift x to ℝ using hx with s; lift y to ℝ
   using hy with t; rw [toNNReal_exp, toNNReal_exp]; exact NNReal.rpow_lt_rpow_of_exponent_lt he
   (WithZero.exp_lt_exp.mp hxy)` (the `lift` uses the `CanLift ℝᵐ⁰ ℝ exp (· ≠ 0)` instance; if it is not
   available, use `WithZero.exp_log hx` to rewrite `x = exp (log x)` instead).
[SRC] `PhD/Main/ForMathlib/Data/Real/WithZero.lean`.""",
  mathlib="`WithZero.exp_add`, `WithZero.exp_pos`, `WithZero.exp_lt_exp`, `WithZero.exp_log`, `WithZero.log_exp`, `WithZero.log_one`, `WithZero.log_mul`, `WithZero.exp_ne_zero`, `NNReal.coe_mul`, `NNReal.coe_one`, `NNReal.rpow_zero`, `NNReal.rpow_add`, `NNReal.rpow_pos`, `NNReal.rpow_lt_rpow_of_exponent_lt`, `Real.log_mul`, `Real.log_lt_log`, `Real.log_one`, `MonoidWithZeroHom.coe_mk`, `ZeroHom.coe_mk`, `bot_le`, `mul_ne_zero`.",
  sources="[RM] §1.2.1 (the `ℝᵐ⁰`-valued valuation needs `ℝ≥0 →*₀ ℝᵐ⁰`) and §1.4.5 (`e ^ ·` for the rank-one structure); Mathlib's `WithZeroMulInt.toNNReal` is the integer model; decomposition R3/R4 inputs. " + SRC_NOTE,
  gen="`toNNReal` for any base `e ≠ 0` (strict monotonicity only for `1 < e`), as `WithZeroMulInt.toNNReal`.")

# ---------------------------------------------------------------- G2 RatLog
t(id='T005', title='The `ℚ`-valued logarithm of a rank-one ordered group: well-definedness, additivity, normalisation', file=RL, deps='none',
  par='yes (with T001–T004)', typ='lemma + def fields + lemmas', leaves='L2.1–L2.4',
  decls=[(RL, 'ratCoeff_eq'), (RL, 'ratLog'), (RL, 'ratLog_eq'), (RL, 'ratLog_self')],
  sketch="""1. `ratCoeff_eq` (independence of the witness): `obtain ⟨hn', hmn'⟩ := (h a).choose_spec.choose_spec`;
   `set m' := (h a).choose`, `set n' := (h a).choose_spec.choose`; `key : (n' * m - n * m') • a₀ = 0` by the `calc`
   `(n' * m) • a₀ = n' • (m • a₀) = n' • (n • a) = (n' * n) • a = (n * n') • a = n • (n' • a) = n • (m' • a₀) = (n * m') •
   a₀` (`mul_smul`, `hmn`, `hmn'`, `mul_comm`), then `sub_smul`, `sub_eq_zero`; `key' : m * n' = m' * n` from
   `IsAddTorsionFree.zsmul_eq_zero_iff_left ha₀` (ordered groups are torsion-free: the instance is found);
   finish with `div_eq_div_iff` and `exact_mod_cast key'.symm`.
2. `ratLog.map_zero'`: `rw [ratCoeff_eq h ha₀.ne (m := 0) (n := 1) one_pos (by simp), Int.cast_zero, zero_div,
   neg_zero]`. `map_add' a b`: witnesses `⟨m₁, n₁, hn₁, e₁⟩ := h a`, `⟨m₂, n₂, hn₂, e₂⟩ := h b`; `e : (n₁ * n₂) •
   (a + b) = (n₂ * m₁ + n₁ * m₂) • a₀` by `smul_add, add_smul` and `mul_smul` with `e₁, e₂`; then three
   `ratCoeff_eq` rewrites, `push_cast`, `field_simp`, `ring`.
3. `ratLog_eq`: `congrArg Neg.neg (ratCoeff_eq h ha₀.ne hn hmn)`.
4. `ratLog_self`: `rw [ratLog_eq ha₀ h (m := 1) (n := 1) one_pos (by simp)]; norm_num`.
[SRC] `PhD/Main/ForMathlib/Algebra/Order/Group/Commensurable.lean`.""",
  mathlib="`mul_smul`, `sub_smul`, `sub_eq_zero`, `smul_add`, `add_smul`, `IsAddTorsionFree.zsmul_eq_zero_iff_left`, `div_eq_div_iff`, `Int.cast_zero`, `zero_div`, `neg_zero`, `one_pos`, `mul_comm`.",
  sources="[RM] §1.4.2 (Q2.1) and convention 3 (Q2.2); the well-definedness argument of decomposition R2; decomposition L2.1–L2.4. " + SRC_NOTE,
  gen="Any `[AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]`; `a₀ < 0` (the sign makes `ratLog` increasing, [RM] convention 6).")

t(id='T006', title='`ratLog` is strictly monotone and unique', file=RL, deps='T005',
  par='yes (with T001–T004)', typ='lemmas', leaves='L2.5, L2.6',
  decls=[(RL, 'ratLog_strictMono'), (RL, 'ratLog_unique')],
  sketch="""1. `ratLog_strictMono`: first `key : ∀ a, 0 < a → 0 < ratLog ha₀ h a`: witnesses `⟨m, n, hn, hmn⟩ := h a`;
   `rw [ratLog_eq ha₀ h hn hmn, neg_pos]`; `hna : 0 < m • a₀` from `hmn ▸ (zsmul_lt_zsmul_iff_left ha).mpr hn`
   (with `0 • a = 0`); `hm : m < 0` by `lt_trichotomy m 0` (the `m = 0` case contradicts `hna` by `simp`; the
   `0 < m` case gives `m • a₀ < 0` from `a₀ < 0`, contradiction); conclude `div_neg_of_neg_of_pos`. Then
   `intro a b hab; have := key (b - a) (sub_pos.mpr hab); rw [map_sub] at this; linarith`.
2. `ratLog_unique`: `AddMonoidHom.ext fun a ↦ ?_`; `⟨m, n, hn, hmn⟩ := h a`; `have : n • g a = -m := by rw
   [← map_zsmul, hmn, map_zsmul, hg]; simp` (`zsmul_neg`, `smul_eq_mul`, `mul_one`... in `ℚ`, `n • q = n * q`:
   `zsmul_eq_mul`); then `rw [ratLog_eq ha₀ h hn hmn]`; `field_simp` / `eq_div_iff (by exact_mod_cast hn.ne')`
   from `this` (`linarith` after `zsmul_eq_mul`).
[SRC] `ratLog_strictMono`; the uniqueness is new (decomposition L2.6).""",
  mathlib="`zsmul_lt_zsmul_iff_left`, `lt_trichotomy`, `div_neg_of_neg_of_pos`, `sub_pos`, `map_sub`, `neg_pos`, `AddMonoidHom.ext`, `map_zsmul`, `zsmul_eq_mul`, `eq_div_iff`, `smul_eq_mul`.",
  sources="[RM] §1.4.2 (Q2.1 'prove it strictly monotone'), §1.4.4 (Q4.4, whose substrate is L2.6); [Gou20] 3.1.3 (iv) (Q2.3) for the classical analogue; decomposition L2.5–L2.6. " + SRC_NOTE,
  gen="As T005; uniqueness among all `M →+ ℚ`, not only monotone ones.")

# ---------------------------------------------------------------- G3 Basic
t(id='T007', title='`Valuation.addVal`: `apply`, `eq_top`, `eq_coe`, order reversal', file=BA, deps='CLEANUP-2',
  par='yes (with T005, T006)', typ='lemmas', leaves='L1.14–L1.17',
  decls=[(BA, 'addVal_apply'), (BA, 'addVal_eq_top'), (BA, 'addVal_eq_coe'), (BA, 'addVal_le_addVal')],
  sketch="""1. `addVal_apply`: `rfl` (`AddValuation.map_apply` and `Valuation.toAddValuation_apply` are `rfl`;
   `orderAddIsoWithTop M` applies as `negLog`).
2. `addVal_eq_top`: `rw [addVal_apply, WithZero.negLog_eq_top]` (or `simp`, as in [SRC]).
3. `addVal_eq_coe`: `rw [addVal_apply]; exact WithZero.negLog_eq_coe`.
4. `addVal_le_addVal`: `rw [addVal_apply, addVal_apply, WithZero.negLog_le_negLog]`.
[SRC] `AddVal/Basic.lean` `addVal_apply`, `addVal_eq_top`, `addVal_eq_coe`.""",
  mathlib="`AddValuation.map_apply`, `Valuation.toAddValuation_apply`.",
  sources="[RM] §1.1.3 (Q1.3), [PR] #43580 (Q1.6); decomposition L1.14–L1.17. " + SRC_NOTE,
  gen="`[Ring R]`, `M` a linearly ordered additive group (as `addVal` itself).")

t(id='T008', title='The tautological additive valuation `addValValueGroup`', file=BA, deps='T007',
  par='no', typ='lemmas', leaves='L1.19, L1.20',
  decls=[(BA, 'addValValueGroup_apply'), (BA, 'addValValueGroup_eq_top')],
  sketch="""1. `addValValueGroup_apply`: `rfl` (it is `addVal_apply` at `v.restrict`).
2. `addValValueGroup_eq_top`: `rw [addValValueGroup_apply, WithZero.negLog_eq_top, Valuation.restrict_eq_zero_iff]`.
[SRC] `addValValueGroup_apply`.""",
  mathlib="`Valuation.restrict_eq_zero_iff`, `Valuation.restrict`, `MonoidWithZeroHom.valueGroup`.",
  sources="[RM] §1.1.4 (Q1.4), [PR] #43580 (Q1.6); decomposition L1.19–L1.20. " + SRC_NOTE,
  gen="Any `v : Valuation R Γ₀` over `[Ring R] [LinearOrderedCommGroupWithZero Γ₀]` — no rank hypothesis.")

t(id='T009', title='Naturality: `addVal_map` — the §1.1 dictionary is complete', file=BA, deps='CLEANUP-ALL-1',
  par='no', typ='theorem', leaves='L1.18',
  milestone='M1 — `Valuation.addVal_map` with `addVal_eq_coe` is the dictionary of mathlib4#43578/#43580 ([RM] §1.1). `#print axioms` must be standard on `addVal_map`, `addVal_eq_coe`, `addVal_eq_top`.',
  decls=[(BA, 'addVal_map')],
  sketch="""1. `rw [addVal_apply, addVal_apply]`; the left side is `negLog ((v.map (mapAddHom' f) _) x)` and
   `Valuation.map_apply`/`rfl` turns it into `negLog (mapAddHom' f (v x))`.
2. `exact WithZero.negLog_mapAddHom' f (v x)`.
[SRC] `addVal_map` (one line: `negLog_expMap f (v x)`).""",
  mathlib="`Valuation.map`, `Valuation.map_apply`.",
  sources="[RM] §1.1.4 (Q1.4 'Prove `Valuation.addVal_map`'), [PR] #43580 (Q1.6); decomposition L1.18. " + SRC_NOTE,
  gen="`hf : StrictMono f` only to form the monotone argument of `Valuation.map` (the PR's shape).")

# ---------------------------------------------------------------- G4 RankOne
t(id='T010', title='`RankOne.addVal`: apply, zero, `eq_top`, value `-log (hom (v x))`', file=RO, deps='CLEANUP-4',
  par='no', typ='lemmas', leaves='L3.1–L3.4',
  decls=[(RO, 'addVal_apply'), (RO, 'addVal_zero'), (RO, 'addVal_eq_top'), (RO, 'addVal_apply_of_val_ne_zero')],
  sketch="""1. `addVal_apply`: `rfl`.
2. `addVal_zero`: `AddValuation.map_zero _`.
3. `addVal_eq_top`: `rw [addVal, Valuation.addVal_eq_top]`; `show NNReal.toRealMultZero (RankOne.hom v (v.restrict
   x)) = 0 ↔ v x = 0`; `rw [map_eq_zero, RankOne.hom_eq_zero_iff, Valuation.restrict_eq_zero_iff]` — `map_eq_zero`
   needs `toRealMultZero` to be injective at `0` as a `MonoidWithZeroHom` with `[NoZeroDivisors]`-free statement:
   if `map_eq_zero` does not fire, prove `toRealMultZero y = 0 ↔ y = 0` directly by `split_ifs` and
   `WithZero.exp_ne_zero`.
4. `addVal_apply_of_val_ne_zero`: `have h : RankOne.hom v (v.restrict x) ≠ 0 := by rw [Ne, RankOne.hom_eq_zero_iff,
   Valuation.restrict_eq_zero_iff]; exact hx`; `rw [addVal_apply, NNReal.toRealMultZero_of_ne_zero h,
   WithZero.negLog_exp]`.
[SRC] `AddVal/RankOne.lean`, same names.""",
  mathlib="`Valuation.RankOne.hom`, `Valuation.RankOne.hom_eq_zero_iff`, `Valuation.restrict_eq_zero_iff`, `map_eq_zero`, `AddValuation.map_zero`.",
  sources="[RM] §1.2.1 (Q3.1), [Kob84] III §3 (Q3.2); decomposition L3.1–L3.4. " + SRC_NOTE,
  gen="`[Ring R]`, any `[RankOne v]`.")

t(id='T011', title='`RankOne.addVal` depends only on the real absolute value', file=RO, deps='T010',
  par='no', typ='lemma', leaves='L3.5',
  decls=[(RO, 'addVal_eq_of_hom_eq')],
  sketch="""1. `AddValuation.ext fun x ↦ ?_`; `rw [addVal_apply, addVal_apply, h x]`.
(New; [RM] §1.2.1's 'equivalent valuation with the matching hom' is exactly the hypothesis — `plan.md` D5.)""",
  mathlib="`AddValuation.ext`.",
  sources="[RM] §1.2.1 (Q3.1, last clause); decomposition L3.5.",
  gen="Two valuations `v w : Valuation R Γ₀` with arbitrary `RankOne` structures; the hypothesis compares `hom ∘ restrict` pointwise.")

# ---------------------------------------------------------------- G5 Commensurable
t(id='T012', title='`IsCommensurable`: basic consequences, the normalising element `commGen`', file=CO, deps='CLEANUP-3, CLEANUP-5',
  par='no', typ='lemmas', leaves='L4.1–L4.5',
  decls=[(CO, 'IsCommensurable.val_ne_zero'), (CO, 'IsCommensurable.of_forall_eq'), (CO, 'IsCommensurable.isNontrivial'), (CO, 'coe_commGen'), (CO, 'ofMul_commGen_neg')],
  sketch="""1. `val_ne_zero`: `hπ.val_pos.ne'`.
2. `of_forall_eq`: `exact ⟨by rw [h]; exact hπ.val_pos, by rw [h]; exact hπ.val_lt_one, fun x hx ↦ by
   simpa only [h] using hπ.exists_zpow_eq x (by rwa [h] at hx)⟩`.
3. `isNontrivial`: `⟨⟨π, hπ.val_pos.ne', hπ.val_lt_one.ne⟩⟩` (`Valuation.IsNontrivial` has the single field
   `exists_val_nontrivial : ∃ x, v x ≠ 0 ∧ v x ≠ 1`).
4. `coe_commGen`: `rfl`.
5. `ofMul_commGen_neg`: `show commGen v π < 1`; `rw [← Subtype.coe_lt_coe, ← Units.val_lt_val]`; `simpa using
   hπ.val_lt_one`.
[SRC] `AddVal/Commensurable.lean` (`val_ne_zero`, `coe_commGen`, `ofMul_commGen_neg`, `isNontrivial`).""",
  mathlib="`Valuation.IsNontrivial`, `Valuation.IsNontrivial.exists_val_nontrivial`, `Subtype.coe_lt_coe`, `Units.val_lt_val`, `Units.mk0`, `MonoidWithZeroHom.mem_valueGroup`.",
  sources="[RM] §1.4.1 (Q4.1); decomposition L4.1–L4.5. " + SRC_NOTE,
  gen="`[Ring R]`; `of_forall_eq` for any two valuations into the same `Γ₀`.")

t(id='T013', title='Every element of the value group is commensurable with `commGen`', file=CO, deps='T012',
  par='no', typ='lemma', leaves='L4.6',
  decls=[(CO, 'isCommensurableWith_commGen')],
  sketch="""1. `obtain ⟨a, ha, x, hax⟩ := (MonoidWithZeroHom.mem_valueGroup_iff_of_comm (f := .ofClass v)).mp g.2`;
   `simp only [MonoidWithZeroHom.coe_ofClass] at ha hax` (`ha : v a ≠ 0`, `hax : v a * ↑↑g = v x`).
2. `hx : v x ≠ 0` from `hax` (`mul_ne_zero ha (Units.ne_zero _)`).
3. Witnesses `⟨m₁, n₁, hn₁, e₁⟩ := hπ.exists_zpow_eq x hx`, `⟨m₂, n₂, hn₂, e₂⟩ := hπ.exists_zpow_eq a ha`.
4. `refine ⟨m₁ * n₂ - m₂ * n₁, n₁ * n₂, mul_pos hn₁ hn₂, ?_⟩`; `show g ^ (n₁ * n₂) = commGen v π ^ (m₁ * n₂ - m₂ *
   n₁)`; `refine Subtype.ext (Units.ext ?_)`; `simp only [SubgroupClass.coe_zpow, Units.val_zpow_eq_zpow_val,
   coe_commGen]`; `hgx : ↑↑g = v x / v a` (from `hax`, `field_simp`); `rw [hgx, div_zpow, zpow_sub₀ (val_ne_zero v
   π), show v x ^ (n₁ * n₂) = v π ^ (m₁ * n₂) by rw [zpow_mul, e₁, ← zpow_mul], show v a ^ (n₁ * n₂) = v π ^ (m₂ *
   n₁) by rw [mul_comm n₁ n₂, zpow_mul, e₂, ← zpow_mul]]`.
[SRC] `exists_zpow_eq_commGen` (verbatim route).""",
  mathlib="`MonoidWithZeroHom.mem_valueGroup_iff_of_comm`, `MonoidWithZeroHom.coe_ofClass`, `SubgroupClass.coe_zpow`, `Units.val_zpow_eq_zpow_val`, `Units.ne_zero`, `div_zpow`, `zpow_sub₀`, `zpow_mul`, `mul_pos`, `Subtype.ext`, `Units.ext`.",
  sources="[RM] §1.4.1 (Q4.1) and the closure argument of decomposition R4 ([Gou20] 6.4.2, Q4.6); decomposition L4.6. " + SRC_NOTE,
  gen="`[Ring R]` (the value group is generated by the values; commutativity of `Γ₀` is what `mem_valueGroup_iff_of_comm` uses).")

t(id='T014', title='`Valuation.ratLog`: strict monotonicity, normalisation, computation from a witness', file=CO, deps='T013',
  par='no', typ='lemmas', leaves='L4.7–L4.9',
  decls=[(CO, 'ratLog_strictMono'), (CO, 'ratLog_commGen'), (CO, 'ratLog_eq_of_zsmul')],
  sketch="""1. `ratLog_strictMono`: `AddCommGroup.ratLog_strictMono _ _`.
2. `ratLog_commGen`: `AddCommGroup.ratLog_self _ _`.
3. `ratLog_eq_of_zsmul`: `AddCommGroup.ratLog_eq _ _ hn hmn`.
[SRC] same names.""",
  mathlib="(none beyond T005/T006.)",
  sources="[RM] §1.4.2 (Q2.1); decomposition L4.7–L4.9. " + SRC_NOTE,
  gen="As T012.")

t(id='T015', title='`addValQ`: apply, zero, `eq_top`, order reversal', file=CO, deps='CLEANUP-6',
  par='no', typ='lemmas', leaves='L4.10–L4.12, L4.18',
  decls=[(CO, 'addValQ_apply'), (CO, 'addValQ_zero'), (CO, 'addValQ_eq_top'), (CO, 'addValQ_le_addValQ')],
  sketch="""1. `addValQ_apply`: `rfl` (`AddValuation.map_apply`; `AddMonoidHom.withTopMap` coerces to `WithTop.map`).
2. `addValQ_zero`: `AddValuation.map_zero _`.
3. `addValQ_eq_top`: `rw [addValQ_apply, WithTop.map_eq_top_iff, addValValueGroup_eq_top]`.
4. `addValQ_le_addValQ`: `rw [addValQ_apply, addValQ_apply, WithTop.map_le_iff _ (fun a b ↦
   (ratLog_strictMono v π).le_iff_le), addValValueGroup_apply, addValValueGroup_apply, WithZero.negLog_le_negLog,
   Valuation.restrict_le_iff]`.
[SRC] `addValQ_apply`, `addValQ_zero`; the other two are new API.""",
  mathlib="`AddValuation.map_apply`, `AddMonoidHom.withTopMap`, `WithTop.map_eq_top_iff`, `WithTop.map_le_iff`, `StrictMono.le_iff_le`, `Valuation.restrict_le_iff`.",
  sources="[RM] §1.4.2 (Q4.2); decomposition L4.10–L4.12, L4.18. " + SRC_NOTE,
  gen="As T012.")

t(id='T016', title='The workhorse `addValQ_eq_of_zpow` and its corollaries', file=CO, deps='T015',
  par='no', typ='lemmas', leaves='L4.13–L4.17',
  decls=[(CO, 'addValQ_eq_of_zpow'), (CO, 'addValQ_eq_of_pow_eq_pow'), (CO, 'addValQ_self'), (CO, 'addValQ_ne_top'), (CO, 'exists_zpow_eq_and_addValQ')],
  sketch="""1. `addValQ_eq_of_zpow`: `hr : v.restrict x ≠ 0 := by simpa using hx`; `obtain ⟨g, hg⟩ : ∃ g : valueGroup
   (.ofClass v), v.restrict x = ↑g := ⟨WithZero.unzero hr, (WithZero.coe_unzero hr).symm⟩`; `hgx : ↑↑g = v x` from
   `v.embedding_restrict x` and `hg`; `hgn : n • Additive.ofMul g = m • Additive.ofMul (commGen v π)`: `show g ^ n
   = commGen v π ^ m; refine Subtype.ext (Units.ext ?_); simp only [SubgroupClass.coe_zpow,
   Units.val_zpow_eq_zpow_val, coe_commGen, hgx]; exact hmn`; then `rw [addValQ_apply, addValValueGroup_apply, hg]`
   (so the value is `WithTop.map ratLog ↑(-(ofMul g))`), `WithTop.map_coe, map_neg, ratLog_eq_of_zsmul v π hn hgn,
   neg_neg`. (In [SRC] the `addValValueGroup` step is the private `addValValueGroup_of_coe`; inline it or keep
   it as a private lemma.)
2. `addValQ_eq_of_pow_eq_pow`: `have := addValQ_eq_of_zpow v π hx (n := n) (m := m) (by exact_mod_cast hn) (by
   simpa only [zpow_natCast] using hmn)`; `simpa [Int.cast_natCast] using this`.
3. `addValQ_self`: `rw [addValQ_eq_of_zpow v π (IsCommensurable.val_ne_zero v π) one_pos rfl]; norm_num`
   (`v π ^ (1 : ℤ) = v π ^ (1 : ℤ)` is `rfl`).
4. `addValQ_ne_top`: `obtain ⟨m, n, hn, e⟩ := hπ.exists_zpow_eq x hx; rw [addValQ_eq_of_zpow v π hx hn e]; exact
   WithTop.coe_ne_top`.
5. `exists_zpow_eq_and_addValQ`: `obtain ⟨m, n, hn, e⟩ := hπ.exists_zpow_eq x hx; exact ⟨m, n, hn, e,
   addValQ_eq_of_zpow v π hx hn e⟩`.
[SRC] `addValQ_eq_of_zpow`, `addValQ_self`, `addValQ_ne_top`, `exists_zpow_eq_and_addValQ`.""",
  mathlib="`WithZero.unzero`, `WithZero.coe_unzero`, `Valuation.embedding_restrict`, `WithTop.map_coe`, `WithTop.coe_ne_top`, `map_neg`, `zpow_natCast`, `Int.cast_natCast`, `Nat.cast_pos`, `SubgroupClass.coe_zpow`, `Units.val_zpow_eq_zpow_val`.",
  sources="[RM] §1.4.3 (Q4.3), §1.4.2 (Q4.2 `addValQ v π π = 1`); decomposition L4.13–L4.17. " + SRC_NOTE,
  gen="As T012; the `pow` form is the one the normed examples use.")

t(id='T017', title='Uniqueness: the element pins the valuation', file=CO, deps='CLEANUP-ALL-2',
  par='no', typ='theorem', leaves='L4.19',
  milestone='M2 — `Valuation.addValQ_unique` ([RM] §1.4.4, the justification of convention 3). `#print axioms` must be standard.',
  decls=[(CO, 'addValQ_unique')],
  sketch="""1. `refine AddValuation.ext fun x ↦ ?_`. Lemma inside the proof: `hw_top : ∀ x, w x = ⊤ ↔ v x = 0`: `←`: from
   `v x ≤ v 0` (`v 0 = 0`, `Valuation.map_zero`) get `w 0 ≤ w x` by `(hw 0 x).mpr`, and `w 0 = ⊤`
   (`AddValuation.map_zero`), so `top_le_iff.mp`; `→`: `w 0 ≤ w x` holds, so `v x ≤ v 0 = 0`, i.e. `v x = 0`
   (`le_zero_iff`/`nonpos_iff_eq_zero` in `Γ₀`).
2. Case `hx : v x = 0`: `rw [(hw_top x).mpr hx, eq_comm, addValQ_eq_top]; exact hx`.
3. Case `v x ≠ 0`: `obtain ⟨m, n, hn, e⟩ := hπ.exists_zpow_eq x hx`. Set `a := m.toNat`, `b := (-m).toNat`; `hab :
   (a : ℤ) - b = m := Int.toNat_sub_toNat_neg m`; `hn' : n = (n.toNat : ℤ) := (Int.toNat_of_nonneg hn.le).symm`.
   Compare the ring elements `y₁ := x ^ n.toNat * π ^ b` and `y₂ := π ^ a`: `hv : v y₁ = v y₂` by `map_mul, map_pow,
   ← zpow_natCast, ← hn', e, ← zpow_add₀ (val_ne_zero v π), hab`-style rewriting (both sides `v π ^ a`).
4. From `hv`, `(hw y₁ y₂).mpr hv.ge` and `(hw y₂ y₁).mpr hv.le` give `w y₁ = w y₂` (`le_antisymm`); rewrite with
   `AddValuation.map_mul, AddValuation.map_pow, hwπ`: `n.toNat • w x + b • (1 : WithTop ℚ) = a • 1`.
5. `w x ≠ ⊤` by `hw_top` and `hx`; `obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp this`; `rw [← hq] at *`;
   `norm_cast` / `WithTop.coe_inj` to get `(n.toNat : ℚ) * q + b = a` in `ℚ` (`nsmul_eq_mul`, `mul_one`);
   solve `q = (a - b) / n = m / n` (`eq_div_iff`, `linarith`, `push_cast [hab, hn']`).
6. `rw [← hq, addValQ_eq_of_zpow v π hx hn e]`; `congr 1`; the computed `q`.
Expect ~40 lines; the integer bookkeeping (`toNat`) is the only delicate part — keep `m` as `(a : ℤ) - b`
throughout.""",
  mathlib="`AddValuation.ext`, `AddValuation.map_zero`, `AddValuation.map_mul`, `AddValuation.map_pow`, `Valuation.map_zero`, `top_le_iff`, `le_antisymm`, `Int.toNat_sub_toNat_neg`, `Int.toNat_of_nonneg`, `zpow_natCast`, `zpow_add₀`, `map_mul`, `map_pow`, `WithTop.ne_top_iff_exists`, `WithTop.coe_inj`, `nsmul_eq_mul`, `eq_div_iff`.",
  sources="[RM] §1.4.4 (Q4.4) and convention 3 (Q2.2); [Gou20] 3.1.3 (Q2.3) for the classical analogue; decomposition L4.19 (the prose proof is in R4).",
  gen="`[Ring R]`; `w` an arbitrary `AddValuation R (WithTop ℚ)`; the order hypothesis is an `↔` for all pairs.")

t(id='T018', title='Rational rank one implies rank one, with `hom (v π) = e⁻¹`', file=CO, deps='CLEANUP-7',
  par='no', typ='def field + lemma', leaves='L4.20, L4.21',
  decls=[(CO, 'IsCommensurable.toRankLeOne'), (CO, 'IsCommensurable.toRankOne_hom_restrict')],
  sketch="""1. `toRankLeOne.strictMono'`: `(WithZeroMulReal.toNNReal_strictMono he).comp (WithZero.mapAddHom'_strictMono
   (Rat.cast_strictMono.comp (ratLog_strictMono v π)))`.
2. `toRankOne_hom_restrict`: `letI := IsCommensurable.toRankOne v π he`; `show (WithZeroMulReal.toNNReal _).comp
   (WithZero.mapAddHom' _) (v.restrict π) = e⁻¹`; `hπ' : v.restrict π = WithZero.exp (Additive.ofMul (commGen v π))`
   by `MonoidWithZeroHom.ValueGroup₀.embedding_injective` + `Valuation.embedding_restrict` + `coe_commGen` (both
   sides embed to `v π`); `rw [MonoidWithZeroHom.comp_apply, hπ', WithZero.mapAddHom'_exp, AddMonoidHom.comp_apply,
   ratLog_commGen, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, Rat.cast_neg, Rat.cast_one,
   WithZeroMulReal.toNNReal_exp, NNReal.rpow_neg_one]`.
[SRC] `toRankLeOne` (the hom and strictMono); the `hom = e⁻¹` lemma is new (it is the roadmap's clause).""",
  mathlib="`WithZeroMulReal.toNNReal_strictMono`, `WithZeroMulReal.toNNReal_exp`, `Rat.cast_strictMono`, `Rat.castHom`, `Rat.cast_neg`, `Rat.cast_one`, `NNReal.rpow_neg_one`, `MonoidWithZeroHom.ValueGroup₀.embedding_injective`, `Valuation.embedding_restrict`, `MonoidWithZeroHom.comp_apply`, `AddMonoidHom.comp_apply`, `RingHom.toAddMonoidHom_eq_coe`, `AddMonoidHom.coe_coe`.",
  sources="[RM] §1.4.5 (Q4.5, first sentence); decomposition L4.20–L4.21. " + SRC_NOTE,
  gen="Any base `1 < e`; the structure is `@[reducible]` so that `RankOne.hom v` unfolds.")

t(id='T019', title='The compatibility square `ℚ → ℝ` and `‖x‖ = ‖π‖ ^ q`', file=CO, deps='T018',
  par='no', typ='theorems', leaves='L4.22, L4.23',
  decls=[(CO, 'RankOne.addVal_eq_map_addValQ'), (CO, 'RankOne.hom_eq_rpow_addValQ')],
  sketch="""1. `addVal_eq_map_addValQ`: `rcases eq_or_ne (v x) 0 with hx | hx`. Zero: `(addValQ_eq_top v π).mpr hx`,
   `WithTop.map_top`, `(RankOne.addVal_eq_top v).mpr hx`. Nonzero: `obtain ⟨m, n, hn, e, hq⟩ :=
   exists_zpow_eq_and_addValQ v π hx`; positivity of the two real hom values (`RankOne.hom_eq_zero_iff`,
   `Valuation.restrict_eq_zero_iff`, `NNReal.coe_pos`); `hres : v.restrict x ^ n = v.restrict π ^ m` via
   `MonoidWithZeroHom.ValueGroup₀.embedding_injective` and `map_zpow₀`, `Valuation.embedding_restrict`; apply `RankOne.hom
   v` (`map_zpow₀`), coerce to `ℝ` (`NNReal.coe_zpow`), take `Real.log` (`Real.log_zpow` twice); then `rw
   [RankOne.addVal_apply_of_val_ne_zero v hx, hq, WithTop.map_coe, WithTop.coe_inj]; push_cast; field_simp;
   linarith`.
2. `hom_eq_rpow_addValQ`: `hx : v x ≠ 0` (else `addValQ = ⊤ ≠ ↑q`, by `addValQ_eq_top`); positivity as above;
   `h := addVal_eq_map_addValQ v π x`; `rw [RankOne.addVal_apply_of_val_ne_zero v hx, hq, WithTop.map_coe,
   WithTop.coe_inj] at h`; `rw [Real.rpow_def_of_pos ht, ← Real.exp_log hs]; congr 1; linarith`.
[SRC] same names (verbatim route).""",
  mathlib="`Real.log_zpow`, `Real.rpow_def_of_pos`, `Real.exp_log`, `NNReal.coe_zpow`, `NNReal.coe_pos`, `map_zpow₀`, `MonoidWithZeroHom.ValueGroup₀.embedding_injective`, `Valuation.embedding_restrict`, `Valuation.RankOne.hom_eq_zero_iff`, `WithTop.map_top`, `WithTop.map_coe`, `WithTop.coe_inj`.",
  sources="[RM] §1.4.5 (Q4.5, 'the compatibility squares'), §1.4.6 (Q6.4, abstract form); [Gou20] 3.1.3 (iv) and p. 56 (Q2.3, Q4.7); decomposition L4.22–L4.23. " + SRC_NOTE,
  gen="Any `[RankOne v]` (not only `toRankOne`); `[Ring R]`.")

# ---------------------------------------------------------------- G6 Discrete
t(id='T020', title='Discrete valuations: values are powers of the generator; commensurability at elements of valuation in `(0, 1)`', file=DI, deps='CLEANUP-8',
  par='no', typ='lemmas', leaves='L5.1–L5.4',
  decls=[(DI, 'IsRankOneDiscrete.exists_zpow_generator_eq'), (DI, 'IsRankOneDiscrete.exists_zpow_eq_of_isUniformizer'), (DI, 'IsRankOneDiscrete.isCommensurable_of_lt_one'), (DI, 'IsRankOneDiscrete.isCommensurable')],
  sketch="""1. `exists_zpow_generator_eq`: `have hu : Units.mk0 (v x) hx ∈ valueGroup (.ofClass v) := mem_valueGroup _ ⟨x,
   rfl⟩`; `rw [← generator_zpowers_eq_valueGroup, Subgroup.mem_zpowers_iff] at hu`; `obtain ⟨k, hk⟩ := hu`;
   `exact ⟨k, by rw [← Units.val_mk0 hx, ← hk]⟩`.
2. `exists_zpow_eq_of_isUniformizer`: as [SRC]: `hπ.zpowers_eq_valueGroup`, `Subgroup.mem_zpowers_iff`, then
   `rw [← Units.val_mk0 hx, ← hk, Units.val_zpow_eq_zpow_val, Units.val_mk0]`.
3. `isCommensurable_of_lt_one`: `refine ⟨zero_lt_iff.mpr h0, h1, fun x hx ↦ ?_⟩`; `⟨k, hk⟩ :=
   exists_zpow_generator_eq v hx`, `⟨j, hj⟩ := exists_zpow_generator_eq v h0`; `hj0 : 0 < j`: from `h1 : v π < 1`
   rewritten by `hj` as `↑(generator v ^ j) < 1`, i.e. `generator v ^ j < 1` in `Γ₀ˣ` (`Units.val_lt_val`,
   `Units.val_one`), and `zpow_lt_one_iff_right_of_lt_one₀`-type lemma on the ordered group `Γ₀ˣ` (if the `₀`
   version does not apply to units, use `zpow_lt_one_iff_right_of_lt_one'`/`Left.zpow_lt_one_iff` — the
   ticket's name check lists `zpow_lt_one_iff_right_of_lt_one₀`; fall back to `zpow_strictAnti`-style lemmas
   `zpow_lt_zpow_iff_right_of_lt_one₀` with exponent `0`); witnesses `⟨k, j, hj0, by rw [hk, hj, ← Units.val_zpow_eq_zpow_val,
   ← Units.val_zpow_eq_zpow_val, ← zpow_mul, ← zpow_mul, mul_comm]⟩`.
4. `isCommensurable`: `isCommensurable_of_lt_one v hπ.val_ne_zero hπ.val_lt_one`.
[SRC] `exists_zpow_eq_of_isUniformizer`, `isCommensurable`.""",
  mathlib="`MonoidWithZeroHom.mem_valueGroup`, `Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup`, `Valuation.IsUniformizer.zpowers_eq_valueGroup`, `Valuation.IsUniformizer.val_ne_zero`, `Valuation.IsUniformizer.val_lt_one`, `Subgroup.mem_zpowers_iff`, `Units.val_mk0`, `Units.val_zpow_eq_zpow_val`, `Units.val_lt_val`, `Units.val_one`, `zpow_lt_one_iff_right_of_lt_one₀`, `zpow_mul`, `zero_lt_iff`, `mul_comm`.",
  sources="[RM] §1.4.1 (Q4.1, 'IsRankOneDiscrete implies IsCommensurable at every uniformiser'), §1.3.1 (Q5.1); [Kob84] III §3 (Q5.4), [Gou20] 6.4.5 (Q5.5); decomposition L5.1–L5.4. " + SRC_NOTE,
  gen="`[Ring R]`, any discrete `v`; L5.3 is stated at any element with `0 < v π < 1` (more general than the roadmap's uniformiser).")

t(id='T021', title='`addValZ`: apply, zero, `eq_top`, order reversal', file=DI, deps='T020',
  par='no', typ='lemmas', leaves='L5.5–L5.7, L5.12',
  decls=[(DI, 'IsRankOneDiscrete.addValZ_apply'), (DI, 'IsRankOneDiscrete.addValZ_zero'), (DI, 'IsRankOneDiscrete.addValZ_eq_top'), (DI, 'IsRankOneDiscrete.addValZ_le_addValZ')],
  sketch="""1. `addValZ_apply`: `rfl`.
2. `addValZ_zero`: `AddValuation.map_zero _`.
3. `addValZ_eq_top`: `rw [addValZ_apply, WithZero.negLog_eq_top, map_eq_zero, Valuation.restrict_eq_zero_iff]`
   (`map_eq_zero` through `MonoidWithZeroHom.coe_ofClass`/the `MulEquivClass` instance of `≃*o`; if it does not
   fire, use `(valueGroup₀_equiv_withZeroMulInt v).map_eq_zero_iff`).
4. `addValZ_le_addValZ`: `rw [addValZ_apply, addValZ_apply, WithZero.negLog_le_negLog,
   (valueGroup₀_equiv_withZeroMulInt_strictMono v).le_iff_le, Valuation.restrict_le_iff]`.
[SRC] `addValZ_apply`, `addValZ_zero`.""",
  mathlib="`Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt`, `Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_strictMono`, `map_eq_zero`, `MonoidWithZeroHom.coe_ofClass`, `Valuation.restrict_eq_zero_iff`, `Valuation.restrict_le_iff`, `StrictMono.le_iff_le`.",
  sources="[RM] §1.3.1 (Q5.1); decomposition L5.5–L5.7, L5.12. " + SRC_NOTE,
  gen="As T020.")

t(id='T022', title='The characterisation `addValZ v x = k ↔ v x = generator ^ k`, at a uniformiser, and `addValZ π = 1`', file=DI, deps='T021',
  par='no', typ='theorems', leaves='L5.8–L5.11',
  decls=[(DI, 'IsRankOneDiscrete.addValZ_eq_iff'), (DI, 'IsRankOneDiscrete.addValZ_eq_of_zpow'), (DI, 'IsRankOneDiscrete.addValZ_eq_iff_of_isUniformizer'), (DI, 'IsRankOneDiscrete.addValZ_isUniformizer')],
  sketch="""1. `addValZ_eq_iff`: `rw [addValZ_apply, WithZero.negLog_eq_coe]`; `h1 : v.restrict x = generator' v ^ k ↔
   valueGroup₀_equiv_withZeroMulInt v (v.restrict x) = WithZero.exp (-k)` by `(valueGroup₀_equiv_withZeroMulInt
   v).injective.eq_iff` and `valueGroup₀_equiv_withZeroMulInt_apply_zpow`; `h2 : v.restrict x = generator' v ^ k ↔ v
   x = ↑(generator v ^ k)` by `MonoidWithZeroHom.ValueGroup₀.embedding_injective.eq_iff`, `map_zpow₀`,
   `embedding_generator'`, `Valuation.embedding_restrict`, `Units.val_zpow_eq_zpow_val`; `exact h1.symm.trans h2`.
2. `addValZ_eq_of_zpow`: [SRC] verbatim: `h1 : v.restrict x = v.restrict π ^ k` and `h2 : v.restrict π = ↑(generator'
   v)` by embedding injectivity (`map_zpow₀`, `embedding_restrict`, `hπ`), then `rw [addValZ_apply, negLog_eq_coe,
   h1, h2, valueGroup₀_equiv_withZeroMulInt_apply_zpow]`.
3. `addValZ_eq_iff_of_isUniformizer`: `rw [addValZ_eq_iff, hπ.val, ← Units.val_zpow_eq_zpow_val]`.
4. `addValZ_isUniformizer`: `have := addValZ_eq_of_zpow v hπ (x := π) (k := 1) (zpow_one _).symm; simpa using this`
   (`WithTop.coe_one`).
[SRC] `addValZ_eq_of_zpow`.""",
  mathlib="`Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_apply_zpow`, `Valuation.IsRankOneDiscrete.embedding_generator'`, `Valuation.IsRankOneDiscrete.generator'`, `Valuation.IsUniformizer.val`, `MonoidWithZeroHom.ValueGroup₀.embedding_injective`, `Valuation.embedding_restrict`, `map_zpow₀`, `Units.val_zpow_eq_zpow_val`, `zpow_one`, `WithTop.coe_one`, `MulEquiv.injective`.",
  sources="[RM] §1.3.1 (Q5.1), §1.3.2 (Q5.2); [Kob84] III §3 (Q5.4), [Gou20] 6.4.5 (Q5.5), Mathlib docstring (Q5.7); decomposition L5.8–L5.11. " + SRC_NOTE,
  gen="As T020.")

t(id='T023', title='`addValQ` at a uniformiser is `addValZ` composed with `Int.cast`', file=DI, deps='CLEANUP-9',
  par='no', typ='theorem', leaves='L5.13',
  decls=[(DI, 'addValQ_eq_map_addValZ')],
  sketch="""1. `rcases eq_or_ne (v x) 0 with hx | hx`. Zero: `(addValQ_eq_top v π).mpr hx`, `(addValZ_eq_top v).mpr hx`,
   `WithTop.map_top`.
2. Nonzero: `obtain ⟨k, hk⟩ := exists_zpow_eq_of_isUniformizer v hπ hx`; `rw [addValQ_eq_of_zpow v π hx one_pos
   (by rw [zpow_one, hk]), addValZ_eq_of_zpow v hπ hk, WithTop.map_coe]; norm_num`.
[SRC] `addValQ_eq_map_addValZ` (verbatim).""",
  mathlib="`WithTop.map_top`, `WithTop.map_coe`, `zpow_one`.",
  sources="[RM] §1.4.5 (Q4.5, last clause); decomposition L5.13. " + SRC_NOTE,
  gen="As T020; the `IsCommensurable` instance is a hypothesis (derivable by T020) so the statement is usable with any instance.")

t(id='T024', title='Norm recovery on a discrete valuation: `hom` is determined by the generator; `hom (v x) = e ^ (-d)`', file=DI, deps='T023',
  par='no', typ='theorems', leaves='L5.14–L5.16',
  decls=[(DI, 'IsRankOneDiscrete.hom_eq_toNNReal_comp'), (DI, 'IsRankOneDiscrete.hom_eq_zpow_neg_addValZ'), (DI, 'IsRankOneDiscrete.hom_eq_zpow_neg_addValZ_of_isUniformizer')],
  sketch="""1. `hom_eq_toNNReal_comp`: `refine MonoidWithZeroHom.ext fun γ ↦ ?_`; `induction γ using WithZero.recZeroCoe with
   | zero => simp | coe u => ?_`; `obtain ⟨k, rfl⟩ : ∃ k : ℤ, generator' v ^ k = u := Subgroup.mem_zpowers_iff.mp (by
   rw [generator'_zpowers_eq_top]; exact Subgroup.mem_top u)`; `rw [MonoidWithZeroHom.comp_apply,
   MonoidWithZeroHom.coe_ofClass, WithZero.coe_zpow, valueGroup₀_equiv_withZeroMulInt_apply_zpow,
   WithZeroMulInt.toNNReal_neg_apply he WithZero.exp_ne_zero, map_zpow₀, hgen, inv_zpow, ← zpow_neg]` and the
   `toAdd (unzero (exp (-k))) = -k` simp fact.
2. `hom_eq_zpow_neg_addValZ`: `rw [addValZ_apply, WithZero.negLog_eq_coe] at hd`; `rw [hom_eq_toNNReal_comp v he hgen,
   MonoidWithZeroHom.comp_apply, MonoidWithZeroHom.coe_ofClass, hd, WithZeroMulInt.toNNReal_neg_apply he
   WithZero.exp_ne_zero]`; finish the `toAdd (unzero _)` computation with `simp`.
3. `hom_eq_zpow_neg_addValZ_of_isUniformizer`: `h : v.restrict π = ↑(generator' v)` (embedding injectivity + `hπ`);
   `exact hom_eq_zpow_neg_addValZ v he (by rwa [← h]) hd`.
[SRC] `hb_of_norm_generator`, `hom_eq_zpow_neg_addValZ` (the private `toNNReal_exp` helper there is
`WithZeroMulInt.toNNReal_neg_apply` plus `WithZero.log_exp`).""",
  mathlib="`MonoidWithZeroHom.ext`, `WithZero.recZeroCoe`, `Valuation.IsRankOneDiscrete.generator'_zpowers_eq_top`, `Subgroup.mem_zpowers_iff`, `Subgroup.mem_top`, `MonoidWithZeroHom.comp_apply`, `MonoidWithZeroHom.coe_ofClass`, `WithZero.coe_zpow`, `WithZeroMulInt.toNNReal_neg_apply`, `WithZero.exp_ne_zero`, `map_zpow₀`, `inv_zpow`, `zpow_neg`, `WithZero.unzero`.",
  sources="[RM] §1.3.3 (Q5.3); [Kob84] I §2 (Q5.6); decomposition L5.14–L5.16. " + SRC_NOTE,
  gen="`he : e ≠ 0` only (the roadmap's `e > 1` is not needed); any `[RankOne v]`.")

# ---------------------------------------------------------------- part B and the board tables
from tickets_data_b import T as _TB, CLEAN, ALL, ORDER, FINAL  # noqa: E402
T = T + _TB
