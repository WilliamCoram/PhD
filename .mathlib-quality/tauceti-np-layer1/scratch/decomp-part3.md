
---

## Result R5 — discrete rank one: the `ℤ`-valued additive valuation (§1.3.1–§1.3.3, `Discrete.lean`)

### Plain-English proof (source: [RM] §1.3.1–§1.3.3; [Kob84] III §3; [Gou20] 6.4.4–6.4.5)

For `[v.IsRankOneDiscrete]` Mathlib provides `generator v : Γ₀ˣ` with `generator < 1` and `zpowers
(generator) = valueGroup v`, and an order isomorphism `valueGroup₀_equiv_withZeroMulInt v :
ValueGroup₀ v ≃*o ℤᵐ⁰` with `generator' ^ k ↦ exp (−k)`. Every nonzero value is `generator ^ k`
(membership in `zpowers`), and for a uniformiser `π` (an element with `v π = generator`) this reads
`v x = v π ^ k` — [Kob84]'s "`x = π^m u`" with `m = e·ord_p x` and [Gou20] 6.4.5 (ii). Hence a
discrete valuation is commensurable at any element with `0 < v π < 1` (`v π = g^j` with `j ≥ 1`,
`v x = g^k`, so `(v x)^j = (v π)^k`), in particular at every uniformiser. Define `addValZ v :=
(v.restrict.map equiv).addVal`; its value is `negLog (equiv (v.restrict x))`, `⊤` iff `v x = 0`,
and `addValZ x = k ↔ v x = generator ^ k` (through `negLog_eq_coe`, `equiv (generator'^k) =
exp (−k)` and injectivity), so `addValZ x = k ↔ v x = v π ^ k` at a uniformiser and `addValZ π = 1`.
Compatibility with the `ℚ`-valued valuation at a uniformiser: `v x = v π ^ k` gives `addValQ x =
k/1 = k` by the workhorse. **Norm recovery**: a `→*₀` out of `ValueGroup₀ v ≅ ℤᵐ⁰` is determined by
its value on the generator (every unit is `generator'^k`), so if `hom (generator') = e⁻¹` then
`hom = toNNReal e ∘ equiv`, whence `hom (v x) = toNNReal e (exp (−d)) = e^(−d)` when `addValZ x = d`
— the `ℚ_p` model `|x|_p = p^{−ord_p x}` of [Kob84] I §2.

### Shared quotes

> **Q5.1** [RM] §1.3.1: "Define `Valuation.IsRankOneDiscrete.addValZ v : AddValuation R (WithTop ℤ)`
> and prove its characterisation: `addValZ v x = k ↔ v x = generator v ^ k`, with `⊤` exactly at
> `v x = 0`."

> **Q5.2** [RM] §1.3.2: "Prove `addValZ v π = 1` for every uniformiser `π`, and `addValZ v x = k ↔
> v x = v π ^ k` for such a `π`."

> **Q5.3** [RM] §1.3.3: "**Norm recovery.** If `[v.RankOne]` as well and `hom v (generator v) = e⁻¹`
> for a real `e > 1`, then `hom v (v x) = e ^ (-(addValZ v x))` for `v x ≠ 0`. Prove that on a
> discrete valuation the single scalar `e` determines `hom`, because a monoid-with-zero hom out of
> an infinite cyclic group is determined by its value on the generator."

> **Q5.4** [Kob84] III §3, p. 66 (PDFPAGE 79): "Now let π ∈ K be any element such that ord_p π =
> (1/e). Then clearly any x ∈ K can be written uniquely in the form π^m u, where |u|_p = 1 and
> m ∈ ℤ (in fact, m = e·ord_p x)."

> **Q5.5** [Gou20] Def. 6.4.4, p. 194 and Prop. 6.4.5 (ii), p. 195 (PDFPAGE 197–198): "We say an
> element π ∈ K is a uniformizer if v_p(π) = 1/e." — "Any element x ∈ K can be written in the form
> x = uπ^{e v_p(x)}, where u ∈ O_K^× is a unit, and therefore satisfies v_p(u) = 0."

> **Q5.6** [Kob84] I §2, p. 2 (PDFPAGE 15): "For any nonzero integer a, let ord_p a be the highest
> power of p which divides a … (If a = 0, we agree to write ord_p 0 = ∞.) Note that ord_p behaves a
> little like a logarithm would: ord_p(a₁a₂) = ord_p a₁ + ord_p a₂." and (the display, OCR
> normalised) "|x|_p = p^{−ord_p x} if x ≠ 0; 0 if x = 0."

> **Q5.7** [Mathlib] `Valuation.IsRankOneDiscrete` docstring: "a valuation `v : A → Γ` on a ring `A`
> is *discrete*, if `genLTOne Γˣ` belongs to the image. Note that the latter is equivalent to
> asking that `1 : ℤ` belongs to the image of the corresponding additive valuation."

### Leaves

- **L5.1** (leaf, Mathlib) `Discrete.lean · Valuation.IsRankOneDiscrete.exists_zpow_generator_eq`.
  Source Q5.1 (the generator), Q5.4. D: `Units.mk0 (v x) hx ∈ valueGroup` (`mem_valueGroup _ ⟨x,
  rfl⟩`); `rw [← generator_zpowers_eq_valueGroup, Subgroup.mem_zpowers_iff] at this`; `⟨k, by rw
  [← Units.val_mk0 hx, ← hk]⟩`.
  Attacks: [2] `v x = 1`: `k = 0` ✓; [3] `hx` necessary (`0` is not a unit power) ✓; [5] names ✓.
  SURVIVED.
- **L5.2** (leaf, Mathlib) `Discrete.lean · …exists_zpow_eq_of_isUniformizer`. Source Q5.4, Q5.5.
  D ([SRC]): `hπ.zpowers_eq_valueGroup`, `Subgroup.mem_zpowers_iff`, `Units.val_zpow_eq_zpow_val`,
  `Units.val_mk0`. Attacks: as L5.1 ✓; [4] "`x = π^m u`" ⇒ `v x = v π ^ m` ✓. SURVIVED.
- **L5.3** (leaf, project) `Discrete.lean · …isCommensurable_of_lt_one` — commensurable at any
  `0 < v π < 1`. New (generalises Q4.1's "at every uniformiser"; needed for L9.5). D: `val_pos :=
  zero_lt_iff.mpr h0`; `exists_zpow_eq x hx`: L5.1 for `x` (`k`) and for `π` (`j`); `0 < j` from
  `generator ^ j < 1` and `generator < 1` (`zpow_lt_one_iff_right_of_lt_one₀` on `Γ₀ˣ`/`Γ₀`, or
  `Units.val_lt_val` and `zpow_lt_one_iff_right_of_lt_one₀`); witnesses `(k, j)`: `(g^k)^j = g^{kj}
  = (g^j)^k` (`← zpow_mul, mul_comm, zpow_mul`).
  Attacks: [1] for `v π = 1` the conclusion is false (`val_lt_one`) — excluded by `h1` ✓; [2]
  `π` a uniformiser: `j = 1` ✓; `v π = g^2`: `v x = g` has witnesses `(1, 2)` ✓; [3] `h0, h1` are
  exactly the class's first two fields, so nothing weaker can do ✓; [5] `zpow_lt_one_iff_right_of_lt_one₀`
  — verified in the ticket name check. SURVIVED.
- **L5.4** (leaf, project) `Discrete.lean · …isCommensurable` — at a uniformiser. Source Q4.1
  ("`IsRankOneDiscrete` implies `IsCommensurable` at every uniformiser"). D: `isCommensurable_of_lt_one
  v hπ.val_ne_zero hπ.val_lt_one` (or [SRC] directly with `(k, 1)`). Attacks: [5] ✓; [2] ✓. SURVIVED.
- **L5.5** (leaf, Mathlib) `Discrete.lean · …addValZ_apply`. D: `rfl`. SURVIVED ([5] [SRC] `rfl`).
- **L5.6** (leaf, Mathlib) `Discrete.lean · …addValZ_zero`. D: `AddValuation.map_zero _`. SURVIVED.
- **L5.7** (leaf, project) `Discrete.lean · …addValZ_eq_top` — `↔ v x = 0`. Source Q5.1 ("with `⊤`
  exactly at `v x = 0`"). D: `rw [addValZ_apply, negLog_eq_top, map_eq_zero, restrict_eq_zero_iff]`
  (`map_eq_zero` for the `≃*o` coerced to `→*₀`: `MonoidWithZeroHom.coe_ofClass`).
  Attacks: [2] `x = 0` ✓; [5] `map_eq_zero` needs the equivalence as a `MonoidWithZeroHomClass`
  map — `MulEquivClass` gives it (Mathlib `MulEquivClass.toMonoidWithZeroHomClass`) ✓. SURVIVED.
- **L5.8** (leaf, project) `Discrete.lean · …addValZ_eq_iff` — `addValZ x = k ↔ v x = ↑(generator ^ k)`.
  Source Q5.1. D: `rw [addValZ_apply, negLog_eq_coe]`; `v.restrict x = generator' ^ k ↔ equiv (…) =
  exp (−k)` by `(equiv).injective.eq_iff` and `valueGroup₀_equiv_withZeroMulInt_apply_zpow`; then
  `embedding_injective.eq_iff`, `map_zpow₀`, `embedding_generator'`, `embedding_restrict`,
  `Units.val_zpow_eq_zpow_val`.
  Attacks: [2] `k = 0`: `addValZ x = 0 ↔ v x = 1` ✓; `k = 1`: `↔ v x = generator` = `IsUniformizer`
  ✓ (consistent with L5.11); [4] Q5.1 verbatim; the roadmap writes `generator v ^ k` in `Γ₀`,
  the skeleton coerces from `Γ₀ˣ` — same element ✓; [5] `valueGroup₀_equiv_withZeroMulInt_apply_zpow
  : equiv (generator' ^ k) = exp (−k)` elaborates with exactly this shape ✓. SURVIVED.
- **L5.9** (leaf, project) `Discrete.lean · …addValZ_eq_of_zpow`. Source Q5.2. D ([SRC]): `h1 :
  v.restrict x = v.restrict π ^ k` (embedding injectivity), `h2 : v.restrict π = generator'`
  (embedding, `hπ`), `rw [h1, h2, valueGroup₀_equiv_withZeroMulInt_apply_zpow]`, `negLog_eq_coe`.
  Attacks: [2] `k = 1`, `x = π` ✓; [5] ✓. SURVIVED.
- **L5.10** (leaf, project) `Discrete.lean · …addValZ_eq_iff_of_isUniformizer`. Source Q5.2. D:
  L5.8 with `hπ : v π = ↑generator` (`IsUniformizer.val`) and `Units.val_zpow_eq_zpow_val`.
  Attacks: [2] as L5.8 ✓; [5] ✓. SURVIVED.
- **L5.11** (leaf, project) `Discrete.lean · …addValZ_isUniformizer` — `addValZ π = 1`. Source
  Q5.2, Q5.7 ("`1 : ℤ` belongs to the image"). D: `addValZ_eq_of_zpow v hπ (zpow_one _).symm`
  (`k = 1`), `WithTop.coe_one`. Attacks: [4] Q5.2 verbatim ✓; [5] ✓. SURVIVED.
- **L5.12** (leaf, project) `Discrete.lean · …addValZ_le_addValZ`. New API. D: `rw [addValZ_apply,
  addValZ_apply, negLog_le_negLog, (valueGroup₀_equiv_withZeroMulInt_strictMono v).le_iff_le,
  restrict_le_iff]`. Attacks: [2] `y = 0` ✓; [5] ✓. SURVIVED.
- **L5.13** (leaf, project) `Discrete.lean · Valuation.addValQ_eq_map_addValZ`. Source Q4.5 ("on a
  discrete valuation `addValQ v π` is `addValZ v` composed with `Int.cast` at a uniformiser `π`").
  D ([SRC]): case `v x = 0` (both `⊤`); else `k` from L5.2, `addValQ_eq_of_zpow v π hx one_pos (by
  rw [zpow_one, hk])`, `addValZ_eq_of_zpow v hπ hk`, `WithTop.map_coe`, `norm_num`.
  Attacks: [2] `x = π`: `1 = ↑1` ✓; [3] the `IsCommensurable` instance is a hypothesis although
  derivable (L5.4): keeping it an instance argument lets the statement be used with *any*
  instance — all instances of a `Prop` class are equal ✓; [5] ✓. SURVIVED.
- **L5.14** (leaf, project) `Discrete.lean · …hom_eq_toNNReal_comp` — `hom` determined by its value
  on `generator'`. Source Q5.3 ("a monoid-with-zero hom out of an infinite cyclic group is determined
  by its value on the generator"). D ([SRC] `hb_of_norm_generator`): `MonoidWithZeroHom.ext`;
  `induction γ using WithZero.recZeroCoe` (zero: `simp`; coe `u`: `u = generator' ^ k` by
  `generator'_zpowers_eq_top`, `Subgroup.mem_zpowers_iff`), then `MonoidWithZeroHom.comp_apply,
  coe_ofClass, WithZero.coe_zpow, valueGroup₀_equiv_withZeroMulInt_apply_zpow, toNNReal_neg_apply,
  map_zpow₀, hgen, inv_zpow, ← zpow_neg`.
  Attacks: [1] for a non-cyclic value group the statement is false — `IsRankOneDiscrete` is the
  hypothesis ✓; [2] `k = 0`: both sides `1` ✓; [3] `he : e ≠ 0` is what `toNNReal` needs; the
  roadmap's `e > 1` is stronger — we state the weaker hypothesis, true as proved ✓; [5] names ✓
  (`WithZeroMulInt.toNNReal_neg_apply : x ≠ 0 → toNNReal he x = e ^ (unzero hx).toAdd`). SURVIVED.
- **L5.15** (leaf, project) `Discrete.lean · …hom_eq_zpow_neg_addValZ` — `hom (v x) = e ^ (−d)`.
  Source Q5.3, Q5.6. D ([SRC]): `rw [addValZ_apply, negLog_eq_coe] at hd`; `rw [hom_eq_toNNReal_comp
  v he hgen, comp_apply, coe_ofClass, hd, toNNReal_neg_apply]`, `unzero (exp (−d)) = ofAdd (−d)`.
  Attacks: [2] `d = 0`: `1` ✓; `x = π`, `d = 1`: `e⁻¹` ✓ (consistent with `hgen`); [3] `he : e ≠ 0`
  (not `1 < e`) suffices, as in L5.14 ✓; [4] Q5.3 verbatim (the roadmap's `-(addValZ v x)` is our
  `d` with `addValZ x = d`) ✓; [5] ✓. SURVIVED.
- **L5.16** (leaf, project) `Discrete.lean · …hom_eq_zpow_neg_addValZ_of_isUniformizer`. D:
  `v.restrict π = generator'` (embedding injectivity + `hπ`), so `hπe` is `hgen`; apply L5.15.
  Attacks: [5] ✓; [2] as L5.15. SURVIVED.

### Internal node R5 ([6])

`addValZ` is the R1 dictionary applied to `v.restrict.map equiv`; L5.8 is the only place the
isomorphism's formula enters, and everything else is derived from L5.8/L5.9. The norm-recovery
pair L5.14–L5.15 composes `hom = toNNReal ∘ equiv` with `equiv (v.restrict x) = exp (−d)`; a
mismatch of sign conventions (`exp (−k)` vs `exp k`) would have broken L5.8 against Mathlib's
`_apply_zpow`. SURVIVED.

---

## Result R6 — the three valuations of an ultrametric normed field (§1.2.2–§1.2.3, §1.3.4, §1.4.6, `Normed.lean`)

### Plain-English proof (source: [RM] §1.2.2–§1.2.3, §1.3.4, §1.4.6; [Kob84] III §4; [Gou20] 3.1)

For a nontrivially normed ultrametric field `K`, Mathlib's `NormedField.valuation : Valuation K ℝ≥0`
is `‖·‖₊` with a `RankOne` structure whose `hom` is the embedding of the value group, so `v.norm x =
‖x‖` and `‖x‖ = hom (v.restrict x)`. Then `normAddVal K := RankOne.addVal valuation` has value
`−log ‖x‖` at `x ≠ 0` (L3.4 + L6.2), `⊤` at `0`, reverses the order of norms, and is characterised
by `‖x‖ = exp (−r)` where `r` is its value — the only additive valuation into `WithTop ℝ` with
this property, because the property determines the value `r = −log ‖x‖` at every `x ≠ 0` and
`map_zero` fixes `0`. In the discrete case `normAddValZ K := addValZ valuation`: at a uniformiser
`π`, `normAddValZ x = k ↔ ‖x‖ = ‖π‖ ^ k` (L5.10 read through `‖·‖₊`), `normAddValZ π = 1`, and
`‖x‖ = e ^ (−d)` when `‖π‖ = e⁻¹` ([Kob84] I §2 for `ℚ_p`); the real valuation is `(−log ‖π‖)` times
the integer one. In the rational-rank-one case `normAddValQ K π := addValQ valuation π`, with
`normAddValQ π = 1`, the workhorse read off norms, `‖x‖ = ‖π‖ ^ q` (L4.23) — no base, no
factorisation hypothesis — and the two squares `normAddVal = (−log ‖π‖) · normAddValQ` (L4.22) and
`normAddValQ = Int.cast ∘ normAddValZ` (L5.13).

### Shared quotes

> **Q6.1** [RM] §1.2.2: "For an ultrametric normed field, define `NormedField.normAddVal K :
> AddValuation K (WithTop ℝ)` from `NormedField.valuation`, and prove `normAddVal K x = -log ‖x‖`
> for `x ≠ 0`. This is the unnormalised member of the family: it takes no element and
> `normAddVal K π` is `-log ‖π‖`, not `1`."

> **Q6.2** [RM] §1.2.3: "Prove the defining equivalence `‖x‖ = exp (-(normAddVal K x))` for
> `x ≠ 0`, and that `normAddVal K` is the unique additive valuation into `WithTop ℝ` satisfying
> it."

> **Q6.3** [RM] §1.3.4: "For an ultrametric normed field whose valuation is discrete, define
> `NormedField.normAddValZ K : AddValuation K (WithTop ℤ)` and prove
> `‖x‖ = e ^ (-(normAddValZ K x))` when a uniformiser has norm `e⁻¹`."

> **Q6.4** [RM] §1.4.6: "**Norm recovery.** For an ultrametric normed field, define
> `NormedField.normAddValQ K π` and prove `‖x‖ = ‖π‖ ^ (normAddValQ K π x)` for `x ≠ 0`. ⚠ There is
> no exponential base and no factorisation hypothesis in this statement: normalising at `π` pins
> the base to `‖π‖⁻¹`."

> **Q6.5** [Kob84] III §4, p. 72 (PDFPAGE 85): "We also extend ord_p to Ω: ord_p x = −log_p |x|_p."

> **Q6.6** [Mathlib] `NormedField.valuation_apply : valuation x = ‖x‖₊` and the `RankOne` instance
> for `[NontriviallyNormedField K] [IsUltrametricDist K]` with `hom' := ValueGroup₀.embedding`
> (`Mathlib/Topology/Algebra/Valued/NormedValued.lean`).

### Leaves

- **L6.1** (leaf, project) `Normed.lean · Valuation.RankOne.addVal_apply_of_ne_zero` (field) —
  `addVal v x = ↑(−log (v.norm x))`. Source Q3.1/Q6.5. D ([SRC]): `hom v (v.restrict x) ≠ 0` from
  `hom_eq_zero_iff`, `restrict_eq_zero_iff`, `v.zero_iff`; `rw [addVal_apply,
  toRealMultZero_of_ne_zero h, negLog_exp]; rfl` (`Valuation.norm_def`).
  Attacks: [3] a field is needed for `v x ≠ 0 ↔ x ≠ 0` (`Valuation.zero_iff`) ✓; [5] ✓. SURVIVED.
- **L6.2** (leaf, Mathlib) `Normed.lean · NormedField.valuation_norm_eq` — `valuation.norm x = ‖x‖`.
  Source Q6.6. D ([SRC]): `rw [Valuation.norm_def, Valuation.restrict_def]; show
  ((embedding (restrict₀ _ x) : ℝ≥0) : ℝ) = ‖x‖; rw [embedding_restrict₀]; rfl`.
  Attacks: [5] the `RankOne` instance's `hom'` is literally `embedding` (Q6.6), so the `show` is
  definitional ✓; [2] `x = 0`: `0 = 0` ✓. SURVIVED.
- **L6.3** (leaf, project) `Normed.lean · NormedField.norm_eq_coe_hom`. D: `rw [← valuation_norm_eq
  K x]; rfl`. SURVIVED ([5] [SRC]).
- **L6.4** (leaf, Mathlib) `Normed.lean · NormedField.normAddVal_zero`. D: `AddValuation.map_zero _`.
  SURVIVED.
- **L6.5** (leaf, project) `Normed.lean · NormedField.normAddVal_eq_top` — `↔ x = 0`. D:
  `RankOne.addVal_eq_top` (L3.3), `Valuation.zero_iff`. Attacks: [2] ✓; [5] ✓. SURVIVED.
- **L6.6** (leaf, project) `Normed.lean · NormedField.normAddVal_apply_of_ne_zero` — `= ↑(−log ‖x‖)`.
  Source Q6.1. D ([SRC]): `rw [normAddVal, RankOne.addVal_apply_of_ne_zero _ hx, valuation_norm_eq]`.
  Attacks: [2] `‖x‖ = 1`: `0` ✓; [4] Q6.1 verbatim ✓; [5] L6.1, L6.2 ✓. SURVIVED.
- **L6.7** (leaf, project) `Normed.lean · NormedField.exists_normAddVal_eq_and_norm_eq_exp_neg`.
  Source Q6.2 ("the defining equivalence"). D: `⟨-Real.log ‖x‖, normAddVal_apply_of_ne_zero K hx,
  by rw [neg_neg, Real.exp_log (norm_pos_iff.mpr hx)]⟩`.
  Attacks: [3] `hx` necessary (`‖0‖ = 0` is not an `exp`) ✓; [5] `Real.exp_log`, `norm_pos_iff` ✓.
  SURVIVED.
- **L6.8** (leaf, project) `Normed.lean · NormedField.normAddVal_le_normAddVal` — `↔ ‖y‖ ≤ ‖x‖`. New
  API (convention 6 orientation). D: `normAddVal` unfolds to `(realValuation v).addVal`;
  `addVal_le_addVal` (L1.17); `realValuation v y ≤ realValuation v x ↔ v y ≤ v x` by the strict
  monotonicity of `toRealMultZero ∘ hom` (`StrictMono.le_iff_le`), then `valuation_apply`,
  `NNReal.coe_le_coe`.
  Attacks: [2] `y = 0` ✓; [5] L1.17 and `StrictMono.le_iff_le` ✓. SURVIVED.
- **L6.9** (leaf, project) `Normed.lean · NormedField.normAddVal_unique`. Source Q6.2 ("the unique
  additive valuation"). D: `AddValuation.ext fun x ↦ ?_`; `x = 0`: `AddValuation.map_zero` twice;
  `x ≠ 0`: `⟨r, hr, hx⟩ := hw x hx'`; `r = −log ‖x‖` from `hx` by `Real.log_exp` (apply `Real.log`,
  `neg_neg`); `rw [hr, normAddVal_apply_of_ne_zero K hx']`.
  Attacks: [1] a second valuation with the same property would have the same values — this is the
  proof; the hypothesis is used at every `x ≠ 0` ✓; [2] `w := normAddVal K` satisfies the
  hypothesis by L6.7 ✓; [3] the hypothesis is the defining equivalence of Q6.2 exactly (`∃ r`
  avoids `exp` of a `WithTop ℝ`, deviation noted in `plan.md` design 7) ✓; [5] `Real.log_exp` ✓.
  SURVIVED.
- **L6.10** (leaf, Mathlib) `Normed.lean · NormedField.normAddValZ_zero`. D: `map_zero`. SURVIVED.
- **L6.11** (leaf, project) `Normed.lean · NormedField.normAddValZ_eq_top`. D: L5.7,
  `Valuation.zero_iff`. SURVIVED ([2] ✓, [5] ✓).
- **L6.12** (leaf, project) `Normed.lean · NormedField.normAddValZ_eq_iff_of_isUniformizer` —
  `normAddValZ x = k ↔ ‖x‖ = ‖π‖ ^ k`. Source Q5.2 read through the norm, Q5.4. D: L5.10, then
  `valuation_apply`, `← NNReal.coe_inj`, `NNReal.coe_zpow`, `coe_nnnorm`.
  Attacks: [2] `k = 0`: `‖x‖ = 1` ✓; `x = 0`: both sides false (`⊤ ≠ ↑k`; `0 ≠ ‖π‖^k` as `π ≠ 0`)
  ✓; [5] `NNReal.coe_zpow`, `coe_nnnorm` ✓. SURVIVED.
- **L6.13** (leaf, project) `Normed.lean · NormedField.normAddValZ_isUniformizer`. D: L5.11.
  SURVIVED.
- **L6.14** (leaf, project) `Normed.lean · NormedField.norm_eq_zpow_neg_normAddValZ` — generator
  form. Source Q6.3, Q5.3. D ([SRC]): `rw [norm_eq_coe_hom K x, hom_eq_zpow_neg_addValZ _ he hgen
  hd, NNReal.coe_zpow]`.
  Attacks: [3] `he : e ≠ 0`; the roadmap's `e > 1` is implied by `hgen` and `generator < 1` but
  is not needed ✓; [2] `d = 0` ✓; [5] L5.15 ✓. SURVIVED.
- **L6.15** (leaf, project) `Normed.lean · NormedField.norm_eq_zpow_neg_normAddValZ_of_isUniformizer`
  — `‖π‖ = e⁻¹ → ‖x‖ = e ^ (−d)`. Source Q6.3 verbatim ("when a uniformiser has norm `e⁻¹`"), Q5.6.
  D: `(normAddValZ_eq_iff_of_isUniformizer K hπ x d).mp hd`, `hπe`, `inv_zpow'`/`inv_zpow`,
  `zpow_neg`.
  Attacks: [2] `K = ℚ_[p]`, `π = p`, `e = p`: `‖x‖ = p^{−d}` (L7.10) ✓; [3] `e : ℝ` with `‖π‖ =
  e⁻¹` forces `e > 0`; no positivity hypothesis needed ✓; [5] `inv_zpow'`, `zpow_neg` ✓. SURVIVED.
- **L6.16** (leaf, project) `Normed.lean · NormedField.normAddVal_eq_map_normAddValZ` — square
  `ℤ → ℝ`. Source Q4.5's pattern applied to `ℤ`, Q6.5/Q4.7 (base change of logarithms). D: `x = 0`:
  both `⊤` (`WithTop.map_top`); else `d` with `normAddValZ x = d` (`WithTop.ne_top_iff_exists`,
  L6.11), `‖x‖ = ‖π‖ ^ d` (L6.12), `normAddVal x = ↑(−log ‖x‖)` (L6.6), `Real.log_zpow`, `WithTop.map_coe`,
  `ring`.
  Attacks: [2] `x = π` ✓ (`1 · (−log ‖π‖)`); [5] `Real.log_zpow : log (x ^ n) = n * log x` ✓.
  SURVIVED.
- **L6.17** (leaf, Mathlib) `Normed.lean · NormedField.normAddValQ_zero`. D: `map_zero`. SURVIVED.
- **L6.18** (leaf, project) `Normed.lean · NormedField.normAddValQ_eq_top`. D: L4.12,
  `Valuation.zero_iff`. SURVIVED.
- **L6.19** (leaf, project) `Normed.lean · NormedField.normAddValQ_self`. Source Q4.2. D: L4.15.
  SURVIVED.
- **L6.20** (leaf, project) `Normed.lean · NormedField.normAddValQ_eq_of_pow_eq_pow` — the
  workhorse read off norms. Source Q4.3. D: L4.14 with `v x ≠ 0` from `hx` (`Valuation.zero_iff`),
  and `‖x‖₊ ^ n = ‖π‖₊ ^ m` from `h` (`NNReal.coe_inj`, `NNReal.coe_pow`, `coe_nnnorm`).
  Attacks: [2] `x = π`, `(1, 1)` ✓; [5] ✓. SURVIVED.
- **L6.21** (leaf, project) `Normed.lean · NormedField.norm_eq_norm_rpow_normAddValQ` —
  `‖x‖ = ‖π‖ ^ q`. Source Q6.4. D ([SRC]): `rw [norm_eq_coe_hom K x, norm_eq_coe_hom K π]; exact
  RankOne.hom_eq_rpow_addValQ _ π hq`.
  Attacks: [4] Q6.4 verbatim, "no exponential base and no factorisation hypothesis": the statement
  indeed has none ✓; [2] `q = 1` ✓; [5] L4.23 ✓. SURVIVED.
- **L6.22** (leaf, project) `Normed.lean · NormedField.normAddVal_eq_map_normAddValQ`. Source Q4.5.
  D: L4.22 at `valuation`, `norm_eq_coe_hom K π`. SURVIVED ([5] ✓).
- **L6.23** (leaf, project) `Normed.lean · NormedField.normAddValQ_eq_map_normAddValZ`. Source Q4.5.
  D: L5.13. SURVIVED ([5] ✓).

### Internal node R6 ([6])

Every leaf is R3–R5 specialised to `NormedField.valuation` plus the two Mathlib identifications
`valuation_apply` and `hom' = embedding` (Q6.6). The one genuinely new argument is L6.9, whose
composition with L6.6/L6.7 is checked in its attacks. SURVIVED.
