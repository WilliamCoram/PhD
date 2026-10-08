
---

## Result R3 — the real additive valuation of a rank-one valuation (§1.2.1, `RankOne.lean`)

### Plain-English proof (source: [RM] §1.2.1; [Kob84] III §3, III §4)

A rank-one valuation `v` comes with `RankOne.hom v : ValueGroup₀ v →*₀ ℝ≥0`, strictly monotone
(Mathlib). Compose with `NNReal.toRealMultZero : ℝ≥0 →*₀ ℝᵐ⁰` (`0 ↦ 0`, `x ↦ exp (log x)`, strictly
monotone by `Real.log_lt_log`) to get `realValuation v : Valuation R ℝᵐ⁰ := v.restrict.map (…)`, and
set `RankOne.addVal v := (realValuation v).addVal`. By `addVal_apply` its value at `x` is `negLog
(toRealMultZero (hom (v.restrict x)))`; when `v x ≠ 0` the hom value is a nonzero real `r`, so this is
`negLog (exp (log r)) = -log r`, the classical `ord x = -log |x|` of [Kob84]; when `v x = 0` the hom
value is `0` and `negLog 0 = ⊤`. Since `addVal v` only depends on the function `hom ∘ restrict`, two
rank-one valuations with the same real absolute value have the same `addVal`. [SRC] `RankOne.lean`
proves all of it over a ring.

### Shared quotes

> **Q3.1** [RM] §1.2.1: "For `v : Valuation R Γ₀` with `[v.RankOne]`, define
> `Valuation.RankOne.realValuation v`, the `ℝᵐ⁰`-valued valuation obtained by pushing `v` along
> `RankOne.hom`, and `Valuation.RankOne.addVal v : AddValuation R (WithTop ℝ)` as its `addVal`.
> Prove `RankOne.addVal v x = -log (hom (v x))` for `v x ≠ 0`, that it is `⊤` exactly at `v x = 0`,
> and that it is unchanged when `v` is replaced by an equivalent valuation with the matching
> `hom`."

> **Q3.2** [Kob84] III §3, p. 66 (PDFPAGE 79): "Let K be an extension of ℚ_p of degree n. For
> α ∈ K we define ord_p α = −log_p |α|_p = −log_p |N_{K/ℚ_p}(α)|_p^{1/n} = −(1/n) log_p
> |N_{K/ℚ_p}(α)|_p. This agrees with the earlier definition of ord_p when α ∈ ℚ_p, and clearly has
> the property that ord_p αβ = ord_p α + ord_p β." (The natural logarithm replaces log_p in the
> unnormalised `addVal`; the normalised members are §1.3–§1.4.)

### Leaves

- **L3.1** (leaf, Mathlib) `RankOne.lean · Valuation.RankOne.addVal_apply` — `addVal v x = negLog
  (toRealMultZero (hom v (v.restrict x)))`. Source Q3.1 ("as its `addVal`"). D: `rfl`
  (`Valuation.map` applies the hom pointwise, definitionally). [SRC] `RankOne.addVal_apply`.
  Attacks: [5] `rfl` compiles in [SRC] with the same definitions ✓; [2] n/a; [4] exact
  unfolding of the clause ✓. SURVIVED.
- **L3.2** (leaf, Mathlib) `RankOne.lean · Valuation.RankOne.addVal_zero` — `addVal v 0 = ⊤`. D:
  `AddValuation.map_zero _`. Attacks: [5] ✓ elaborates; [2] n/a; [4] "`⊤` exactly at `v x = 0`"
  includes `x = 0` ✓. SURVIVED.
- **L3.3** (leaf, project) `RankOne.lean · Valuation.RankOne.addVal_eq_top` — `↔ v x = 0`. Source
  Q3.1. D: `rw [addVal, Valuation.addVal_eq_top]`; `show toRealMultZero (hom v (v.restrict x)) = 0 ↔
  v x = 0`; `rw [map_eq_zero, RankOne.hom_eq_zero_iff, restrict_eq_zero_iff]` ([SRC]).
  Attacks: [2] `x = 0` ✓; `v x = 1`: hom value `1`, `toRealMultZero 1 = exp 0 ≠ 0` ✓;
  [5] `map_eq_zero` needs `toRealMultZero` injective-at-zero: it is a `→*₀` with
  `toRealMultZero x = 0 ↔ x = 0` (by `if_neg` and `exp_ne_zero`) — [SRC] uses exactly this chain ✓;
  [3] none. SURVIVED.
- **L3.4** (leaf, project) `RankOne.lean · Valuation.RankOne.addVal_apply_of_val_ne_zero` — `addVal
  v x = ↑(-Real.log (hom v (v.restrict x)))`. Source Q3.1 ("`-log (hom (v x))` for `v x ≠ 0`"), Q3.2.
  D: `hom v (v.restrict x) ≠ 0` by `hom_eq_zero_iff`, `restrict_eq_zero_iff`; `rw [addVal_apply,
  toRealMultZero_of_ne_zero h, negLog_exp]` ([SRC]).
  Attacks: [3] `hx : v x ≠ 0` necessary (else LHS `⊤`, RHS a real) ✓; [2] `v x = 1`: `-log 1 = 0`
  consistent with `AddValuation.map_one` ✓; [5] L1.2, `NNReal.toRealMultZero_of_ne_zero` ✓.
  SURVIVED.
- **L3.5** (leaf, project) `RankOne.lean · Valuation.RankOne.addVal_eq_of_hom_eq` — equal
  `hom ∘ restrict` ⇒ equal `addVal`. Source Q3.1 ("unchanged when `v` is replaced by an equivalent
  valuation with the matching `hom`"; deviation D5 of `plan.md`: equivalence plus matching `hom` is
  exactly the hypothesis). D: `AddValuation.ext fun x ↦ by rw [addVal_apply, addVal_apply, h x]`.
  Attacks: [2] `w = v`: trivial ✓; [3] the hypothesis quantifies over all `x`; a weaker "equal on
  generators" would not suffice for a general ring ✓; [4] the roadmap's hypothesis ("equivalent …
  matching hom") *implies* ours and is what any user has ✓; [5] L3.1 ✓. SURVIVED.

### Internal node R3 ([6])

`addVal v` is the composite `addVal ∘ map (toRealMultZero ∘ hom) ∘ restrict`; L3.1 is its
unfolding and L3.3–L3.5 are consequences of L1.3, L1.2 and the hom's zero behaviour. No
composition gap. SURVIVED.

---

## Result R4 — rational rank one normalised at an element (§1.4, `Commensurable.lean`)

### Plain-English proof (source: [RM] §1.4.1–§1.4.5; [Gou20] 6.4.1–6.4.2, 3.1.3; [Kob84] III §3)

`IsCommensurable v π` says `0 < v π < 1` and every nonzero value is commensurable with `v π`:
`v x ^ n = v π ^ m`, `n > 0` (the density analogue of "the value group is infinite cyclic":
[Gou20] 6.4.2 shows the image of `v_p` on a finite extension is `(1/e)ℤ`; for `ℂ_p` it is `ℚ`,
6.8.7). It implies nontriviality (`π` has `v π ≠ 0, 1`). Let `g₀ := v π` as an element of the
value group `G := valueGroup v ⊂ Γ₀ˣ` (`commGen`); additively `g₀ < 0`. Every `g ∈ G` is
commensurable with `g₀`: by `mem_valueGroup_iff_of_comm`, `g = v x / v a` with `v a ≠ 0`, and
from witnesses `v x ^ n₁ = v π ^ m₁`, `v a ^ n₂ = v π ^ m₂` we get `g ^ (n₁ n₂) = v π ^ (m₁ n₂ −
m₂ n₁)`. So R2 applies to `(Additive G, g₀)`: `ratLog v π := AddCommGroup.ratLog` is the unique
additive hom to `ℚ` with `g₀ ↦ −1`, strictly monotone. Define `addValQ v π := addValValueGroup
v` pushed along `ratLog` (through `WithTop.map`). **Workhorse**: if `v x ^ n = v π ^ m` with
`n > 0`, then in `G`, `n • g = m • g₀` for `g = v x`, so `ratLog g = −m/n` (L2.3) and
`addValQ x = WithTop.map ratLog (negLog g) = −(−m/n) = m/n`. Hence `addValQ π = 1` (witness `1,1`),
`addValQ x ≠ ⊤` for `v x ≠ 0`, and the order reversal `addValQ x ≤ addValQ y ↔ v y ≤ v x`.
**Uniqueness** (§1.4.4): let `w : AddValuation R (WithTop ℚ)` induce the same order and have
`w π = 1`. If `v x = 0` then `w 0 ≤ w x` (from `v x ≤ v 0`) forces `w x = ⊤ = addValQ x`. If
`v x ≠ 0`, take the witness and compare the ring elements `x ^ n · π ^ m⁻` and `π ^ m⁺` (with
`m = m⁺ − m⁻`, `m⁺, m⁻ ∈ ℕ`): their `v`-values agree, so by the order hypothesis their
`w`-values agree: `n • w x + m⁻ • 1 = m⁺ • 1`, and `w x ≠ ⊤` (same argument as the `⊤` case),
so `w x = (m⁺ − m⁻)/n = m/n = addValQ x`. **Rank one**: for `1 < e`, `hom := toNNReal e ∘
mapAddHom' (Rat.cast ∘ ratLog)` is a strictly monotone `→*₀ ℝ≥0` with `hom (v π) = e ^ (ratLog g₀)
= e ^ (−1) = e⁻¹`. **Compatibility `ℚ → ℝ`**: with any rank-one structure, from `v x ^ n = v π ^ m`
apply `hom` and take logs: `n log |x| = m log |π|`, so `−log |x| = (m/n)(−log |π|)`, i.e.
`RankOne.addVal v x = WithTop.map (q ↦ q · (−log |π|)) (addValQ x)`, and exponentiating, `|x| =
|π| ^ (m/n)` — [Gou20] 3.1.3 (iv) with the exponent pinned by `π`.

### Shared quotes

> **Q4.1** [RM] §1.4.1: "Define the Prop class `Valuation.IsCommensurable v π`: `0 < v π`,
> `v π < 1`, and for every `x` with `v x ≠ 0` there are integers `m` and `n > 0` with
> `v x ^ n = v π ^ m`. Prove it implies `v.IsNontrivial`, and that `IsRankOneDiscrete` implies
> `IsCommensurable` at every uniformiser."

> **Q4.2** [RM] §1.4.2 (continuation of Q2.1): "Define `Valuation.addValQ v π : AddValuation R
> (WithTop ℚ)` by pushing the tautological `addValValueGroup` along it, and prove
> `addValQ v π π = 1`."

> **Q4.3** [RM] §1.4.3: "**The workhorse.** `v x ^ n = v π ^ m` with `n > 0` implies
> `addValQ v π x = m / n`. Everything else in this section reduces to it."

> **Q4.4** [RM] §1.4.4: "**Uniqueness.** Any additive valuation `w : AddValuation R (WithTop ℚ)`
> inducing the same order on values as `v` (`w x ≤ w y ↔ v y ≤ v x`) and satisfying `w π = 1`
> equals `addValQ v π`. This is the statement that justifies convention 3: the element pins the
> valuation."

> **Q4.5** [RM] §1.4.5: "**From rational rank one to rank one.** For every real `e > 1`, build
> `RankOne v` with `hom v (v π) = e⁻¹`, and prove the compatibility squares: `RankOne.addVal v` is
> `(-log (hom v (v π)))` times `addValQ v π`, and on a discrete valuation `addValQ v π` is
> `addValZ v` composed with `Int.cast` at a uniformiser `π`."

> **Q4.6** [Gou20] Def. 6.4.1, p. 192 (PDFPAGE 195): "For any x ∈ K, x ≠ 0, we define the p-adic
> valuation v_p(x) to be the unique rational number satisfying |x| = p^{−v_p(x)}. We extend the
> definition formally by setting v_p(0) = +∞." Prop. 6.4.2, p. 193: "The p-adic valuation v_p is
> a homomorphism from the multiplicative group K× to the additive group ℚ. Its image is of the
> form (1/e)ℤ, where e is a divisor of n = [K : ℚ_p]."

> **Q4.7** [Gou20] p. 56 (PDFPAGE 61): "an absolute value defined by |x| = c^{−v_p(x)}, where
> c > 1 was a real number. Now we can check that this is equivalent to the p-adic absolute
> value—just choose α so that c^α = p." (Q2.3 is the equivalence criterion it cites.)

### Leaves

- **L4.1** (leaf, project) `Commensurable.lean · Valuation.IsCommensurable.val_ne_zero` — `v π ≠ 0`.
  D: `hπ.val_pos.ne'`. Attacks: [5] ✓; [2]/[3] n/a (a field projection). SURVIVED.
- **L4.2** (leaf, project) `Commensurable.lean · Valuation.IsCommensurable.of_forall_eq` —
  transfer along pointwise-equal valuations. New (needed at the `ℂ_p` seam, L10.5). D:
  `constructor <;> simp only [h]`, closing with `hπ.val_pos`, `hπ.val_lt_one`, `hπ.exists_zpow_eq`.
  Attacks: [2] `w = v` ✓; [3] pointwise equality is the weakest hypothesis that transports a
  statement about values ✓; [5] field access ✓. SURVIVED.
- **L4.3** (leaf, Mathlib) `Commensurable.lean · Valuation.IsCommensurable.isNontrivial`. Source
  Q4.1 ("Prove it implies `v.IsNontrivial`"). D: `⟨⟨π, hπ.val_pos.ne', hπ.val_lt_one.ne⟩⟩`
  (`Valuation.IsNontrivial.exists_val_nontrivial : ∃ x, v x ≠ 0 ∧ v x ≠ 1`).
  Attacks: [2] trivial valuation: has no `π` with `0 < v π < 1`, so the class is empty ✓;
  [5] structure shape checked (`names_pre.lean`) ✓; [4] exact clause ✓. SURVIVED.
- **L4.4** (leaf, Mathlib) `Commensurable.lean · Valuation.coe_commGen` — `↑↑(commGen v π) = v π`.
  D: `rfl`. Attacks: [5] `Units.val_mk0` is `rfl` ✓; [2] n/a. SURVIVED.
- **L4.5** (leaf, project) `Commensurable.lean · Valuation.ofMul_commGen_neg` — `ofMul (commGen) < 0`.
  D: `show commGen v π < 1`; `rw [← Subtype.coe_lt_coe, ← Units.val_lt_val]`; `simpa using
  hπ.val_lt_one` ([SRC]). Attacks: [4] sign: `v π < 1` multiplicatively is `< 0` additively ✓
  (this is what makes `ratLog g₀ = −1` and `addValQ π = +1`); [5] `Units.val_lt_val`,
  `Subtype.coe_lt_coe` ✓; [2] n/a. SURVIVED.
- **L4.6** (leaf, Mathlib) `Commensurable.lean · Valuation.isCommensurableWith_commGen` — every
  `g ∈ valueGroup v` is commensurable with `commGen`. Source Q4.1 (every *value*) + the closure
  argument of the prose ([Gou20] 6.4.2: "Its image is therefore an additive subgroup"). D: [SRC]
  `exists_zpow_eq_commGen`: `mem_valueGroup_iff_of_comm` gives `a, x` with `v a ≠ 0`, `v a * g =
  v x`; witnesses `(m₁ n₂ − m₂ n₁, n₁ n₂)`; `Subtype.ext`, `Units.ext`, `div_zpow`, `zpow_sub₀`,
  `zpow_mul`.
  Attacks: [1] a value group element not of the form `v x / v a` would break this — Mathlib's
  `valueGroup` is the subgroup generated by the values, and `mem_valueGroup_iff_of_comm` says
  exactly that every element is such a quotient ✓; [2] `g = 1`: witnesses `(0, 1)` ✓; `g = commGen`:
  `(1,1)` ✓; [5] four Mathlib names elaborate ✓. SURVIVED.
- **L4.7** (leaf, project) `Commensurable.lean · Valuation.ratLog_strictMono`. D:
  `AddCommGroup.ratLog_strictMono _ _` (L2.5). Attacks: [5] ✓; [4] Q2.1 ✓. SURVIVED.
- **L4.8** (leaf, project) `Commensurable.lean · Valuation.ratLog_commGen` — `= −1`. D:
  `AddCommGroup.ratLog_self _ _` (L2.4). Attacks: [5] ✓. SURVIVED.
- **L4.9** (leaf, project) `Commensurable.lean · Valuation.ratLog_eq_of_zsmul`. D:
  `AddCommGroup.ratLog_eq _ _ hn hmn` (L2.3). Attacks: [5] ✓. SURVIVED.
- **L4.10** (leaf, Mathlib) `Commensurable.lean · Valuation.addValQ_apply` — `= WithTop.map (ratLog)
  (addValValueGroup x)`. D: `rfl` (`AddValuation.map_apply`, `AddMonoidHom.withTopMap` coerces to
  `WithTop.map`). Attacks: [5] [SRC] `addValQ_apply` is `rfl` ✓. SURVIVED.
- **L4.11** (leaf, Mathlib) `Commensurable.lean · Valuation.addValQ_zero`. D: `AddValuation.map_zero
  _`. SURVIVED ([5] ✓).
- **L4.12** (leaf, project) `Commensurable.lean · Valuation.addValQ_eq_top` — `↔ v x = 0`. D:
  `rw [addValQ_apply, WithTop.map_eq_top_iff, addValValueGroup_eq_top]` (L1.20).
  Attacks: [5] `WithTop.map_eq_top_iff` (Mathlib, `Order/WithBot.lean`) — verified in the ticket
  name check; [2] `x = 0` ✓. SURVIVED.
- **L4.13** (leaf, project) `Commensurable.lean · Valuation.addValQ_eq_of_zpow` — **the workhorse**.
  Source Q4.3. D ([SRC] `addValQ_eq_of_zpow`): `g := WithZero.unzero (v.restrict x ≠ 0)`; `n •
  ofMul g = m • ofMul (commGen)` from `hmn` via `Subtype.ext`, `Units.ext`,
  `SubgroupClass.coe_zpow`, `Units.val_zpow_eq_zpow_val`, `coe_commGen`, `embedding_restrict`;
  then `rw [addValQ_apply, addValValueGroup_of_coe, WithTop.map_coe, map_neg, ratLog_eq_of_zsmul,
  neg_neg]`.
  Attacks: [1] two witnesses give the same value by L2.1 ✓; [2] `x = π`, `(m, n) = (1, 1)`: `1`
  ✓; `m = 0`: `v x ^ n = 1` ⇒ `v x = 1` ⇒ `addValQ x = 0` ✓; `m < 0`: value negative — `zpow`
  handles negative `m` ✓; [3] `hx` is needed to form `g` (else LHS `⊤`); `hn : 0 < n` is needed
  (for `n = 0` the hypothesis is vacuous) ✓; [5] all names elaborate ✓. SURVIVED.
- **L4.14** (leaf, project) `Commensurable.lean · Valuation.addValQ_eq_of_pow_eq_pow` — natural
  exponents. D: L4.13 with `(m : ℤ) (n : ℤ)` after `zpow_natCast` on both sides; casts by
  `Int.cast_natCast`; `Nat.cast_pos.mpr hn`.
  Attacks: [2] `n = 1` ✓; [5] `zpow_natCast`, `Int.cast_natCast` ✓. SURVIVED.
- **L4.15** (leaf, project) `Commensurable.lean · Valuation.addValQ_self` — `addValQ v π π = 1`.
  Source Q4.2. D: `addValQ_eq_of_zpow v π (val_ne_zero) one_pos rfl` then `norm_num`.
  Attacks: [4] the roadmap's normalisation `addValQ v π π = 1` — sign chain checked:
  `negLog (exp g₀) = −g₀`, `ratLog (−g₀) = −ratLog g₀ = 1` ✓; [5] L4.13 ✓. SURVIVED.
- **L4.16** (leaf, project) `Commensurable.lean · Valuation.addValQ_ne_top`. D: witnesses from
  `hπ.exists_zpow_eq`, L4.13, `WithTop.coe_ne_top`. Attacks: [2] ✓; [5] ✓. SURVIVED.
- **L4.17** (leaf, project) `Commensurable.lean · Valuation.exists_zpow_eq_and_addValQ`
  (shared-witness existential). D: `obtain ⟨m, n, hn, e⟩ := hπ.exists_zpow_eq x hx; exact ⟨m, n, hn,
  e, addValQ_eq_of_zpow v π hx hn e⟩`. Attacks: [5] ✓; shape justified in the gate-7 check.
  SURVIVED.
- **L4.18** (leaf, project) `Commensurable.lean · Valuation.addValQ_le_addValQ` — order reversal.
  New API (used by L6.8 and in the uniqueness argument's `⊤` case). D: `rw [addValQ_apply,
  addValQ_apply, WithTop.map_le_iff _ (ratLog_strictMono v π).le_iff_le, addValValueGroup_apply,
  addValValueGroup_apply, negLog_le_negLog, Valuation.restrict_le_iff]`.
  Attacks: [2] `y = 0`: `_ ≤ ⊤ ↔ 0 ≤ v x` ✓; [5] `WithTop.map_le_iff` (Mathlib, statement `map f
  a ≤ map f b ↔ a ≤ b` given `∀ a b, f a ≤ f b ↔ a ≤ b`) — verified in the ticket name check;
  `restrict_le_iff` ✓. SURVIVED.
- **L4.19** (leaf, project) `Commensurable.lean · Valuation.addValQ_unique` — **M2**. Source Q4.4.
  D: `AddValuation.ext fun x ↦ ?_`. Case `v x = 0`: `hw 0 x` with `v x ≤ v 0 = 0` gives `w 0 ≤ w x`,
  `w 0 = ⊤` (`AddValuation.map_zero`), so `w x = ⊤` (`top_le_iff`); RHS `⊤` by L4.12. Case `v x ≠ 0`:
  `⟨m, n, hn, e⟩ := hπ.exists_zpow_eq x hx`; set `a := m.toNat`, `b := (-m).toNat`, so `(a : ℤ) − b
  = m` (`Int.toNat_sub_toNat_neg`); the ring elements `x ^ n.toNat * π ^ b` and `π ^ a` have equal
  `v`-values (`map_mul, map_pow`, `zpow_natCast`, `e`, `← zpow_add₀ (val_ne_zero)`); apply `hw`
  both ways to get `w (x ^ n.toNat * π ^ b) = w (π ^ a)`, i.e. `n • w x + b • 1 = a • 1`
  (`AddValuation.map_mul, map_pow`, `hwπ`); `w x ≠ ⊤` (as in the first case, with `v 0 ≤ v x` false
  direction: if `w x = ⊤` then `w 0 ≤ w x`, so `v x ≤ v 0 = 0`, contradiction); write `w x = ↑q`,
  solve `n q + b = a` in `ℚ` (`WithTop.coe_inj`, `nsmul_eq_mul`, `field_simp`, `linarith`/`ring`) to
  get `q = m / n`; conclude with L4.13.
  Attacks: [1] without `w π = 1`, `w = 2 • addValQ` satisfies the order hypothesis — so `hwπ` is
  necessary ✓; without commensurability, two independent values leave `w` undetermined — the
  class is used through the witness ✓; [2] `w := addValQ v π` satisfies both hypotheses (L4.18,
  L4.15) so the statement is consistent ✓; `x = 0`: handled by the first case ✓; `x = π`: `w π = 1
  = addValQ π` ✓; [3] the order hypothesis is an `↔` for all pairs; the proof uses it in both
  directions (equal values ⇒ equal `w`-values, and the `⊤` case) — a one-directional hypothesis
  would not suffice ✓; [4] Q4.4 verbatim ✓; [5] `Int.toNat_sub_toNat_neg`, `zpow_add₀`,
  `AddValuation.map_pow`, `top_le_iff` — verified in the ticket name check. SURVIVED.
- **L4.20** (leaf, project) `Commensurable.lean · Valuation.IsCommensurable.toRankLeOne`
  (`strictMono'`). Source Q4.5. D: `(WithZeroMulReal.toNNReal_strictMono he).comp
  (mapAddHom'_strictMono (Rat.cast_strictMono.comp (ratLog_strictMono v π)))` ([SRC], with
  `Rat.cast_strictMono : StrictMono ((↑) : ℚ → ℝ)`).
  Attacks: [3] `1 < e` is needed for strict monotonicity of `e ^ ·` (for `e = 1` the hom is
  constant, for `e < 1` decreasing) ✓; [5] names ✓ (L1.12, R1's `toNNReal_strictMono`). SURVIVED.
- **L4.21** (leaf, project) `Commensurable.lean · Valuation.IsCommensurable.toRankOne_hom_restrict`
  — `hom v (v.restrict π) = e⁻¹`. Source Q4.5 ("with `hom v (v π) = e⁻¹`"). D: `v.restrict π = exp
  (ofMul (commGen v π))` as elements of `(Additive G)ᵐ⁰` (by `ValueGroup₀.embedding_injective`,
  `embedding_restrict`, `coe_commGen`); then `mapAddHom'_exp`, `ratLog_commGen`, `Rat.cast_neg,
  Rat.cast_one`, `toNNReal_exp`, `NNReal.rpow_neg_one`.
  Attacks: [2] `e = 2`: `2 ^ (−1) = 1/2` ✓; [4] Q4.5 ✓; [5] `NNReal.rpow_neg_one` — verified in the
  ticket name check; the `letI` statement elaborates (signature line 143–145) ✓. SURVIVED.
- **L4.22** (leaf, project) `Commensurable.lean · Valuation.RankOne.addVal_eq_map_addValQ` — the
  square `ℚ → ℝ`. Source Q4.5, Q4.7. D ([SRC]): case `v x = 0` (both `⊤`); else
  `exists_zpow_eq_and_addValQ`, `hres : v.restrict x ^ n = v.restrict π ^ m` by embedding
  injectivity, apply `hom` (`map_zpow₀`), coerce to `ℝ`, `Real.log_zpow` twice, then
  `RankOne.addVal_apply_of_val_ne_zero`, `WithTop.map_coe`, `WithTop.coe_inj`, `push_cast`,
  `field_simp`, `linarith`.
  Attacks: [2] `x = π`: `addVal π = −log |π| = 1 · (−log |π|)` ✓; [3] `[RankOne v]` is any rank-one
  structure, not necessarily `toRankOne` — the statement is about *its* hom, correct for all ✓;
  [5] `Real.log_zpow` ✓. SURVIVED.
- **L4.23** (leaf, project) `Commensurable.lean · Valuation.RankOne.hom_eq_rpow_addValQ` —
  `|x| = |π| ^ q`. Source Q4.7 ([Gou20] 3.1.3 (iv) with pinned exponent), Q4.5. D ([SRC]): from
  L4.22 at `x`, `Real.rpow_def_of_pos`, `Real.exp_log`, `linarith`.
  Attacks: [3] `hq` carries `v x ≠ 0` implicitly (a `⊤` value is not a `↑q`) — the proof recovers
  `hx` from it ✓; [2] `q = 1`, `x = π` ✓; `q = 0`: `|x| = 1` ✓; [5] names ✓. SURVIVED.

### Internal node R4 ([6])

The children could all hold while `addValQ` were not an additive valuation only if
`AddValuation.map` were misapplied; it is Mathlib's, and the monotonicity argument is L4.7. The
uniqueness L4.19 is stated against `addValQ` itself, so a wrong normalisation sign would have
surfaced in L4.15. SURVIVED.
