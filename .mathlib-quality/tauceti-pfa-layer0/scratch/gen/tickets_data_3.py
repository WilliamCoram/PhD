# ---------------- G8 Rescale ----------------
ticket('T028','`Real.zpowCeil`: the closed form','Rescale.lean','none','yes (pure real analysis)','lemmas',
 'L8.1',
 ['zpowCeil_nonneg','zpowCeil_of_nonpos','zpowCeil_of_pos','le_zpowCeil','mul_zpowCeil_lt','zpowCeil_le_of_le_zpow'],
 """Write `S x := {y | ∃ n : ℤ, y = c ^ n ∧ x ≤ c ^ n}`. Every element of `S x` is `≥ 0` (`zpow_nonneg hc₀.le`), so
`S x` is bounded below by `0`. Prove in this order (reorder the file if convenient):
1. `zpowCeil_nonneg`: `Real.sInf_nonneg` with the remark above.
2. `zpowCeil_le_of_le_zpow`: `csInf_le ⟨0, _⟩ ⟨n, rfl, h⟩`.
3. The membership equivalence, as a private helper: for `0 < x`, `x ≤ c ^ n ↔ n ≤ ⌊logb c x⌋`.
   `x = c ^ logb c x` (`Real.rpow_logb hc₀ hc₁.ne hx`), `c ^ n = c ^ (n : ℝ)` (`Real.rpow_intCast`),
   `Real.rpow_le_rpow_left_iff_of_base_lt_one hc₀ hc₁`, then `Int.le_floor`.
4. `zpowCeil_of_pos`: `IsLeast.csInf_eq`. `c ^ N ∈ S x` for `N := ⌊logb c x⌋` by step 3 (`le_rfl`); it is a lower
   bound because `n ≤ N` gives `c ^ N ≤ c ^ n` (`zpow_le_zpow_right_of_le_one₀ hc₀ hc₁.le`).
5. `zpowCeil_of_nonpos`: every `n` qualifies (`x ≤ 0 ≤ c ^ n`). `le_antisymm _ (zpowCeil_nonneg hc₀)`; for `ε > 0`
   pick `k : ℕ` with `c ^ k < ε` (`exists_pow_lt_of_lt_one`), so `sInf ≤ c ^ k < ε` by step 2; `le_of_forall_pos_lt_add`
   closes it.
6. `le_zpowCeil`: `x ≤ 0` → step 1; `0 < x` → step 4 and step 3 (`le_rfl`).
7. `mul_zpowCeil_lt`: step 4; `c * c ^ N = c ^ (N + 1)` (`zpow_add_one₀ hc₀.ne'`, `mul_comm`); `¬ x ≤ c ^ (N + 1)` by
   step 3 since `¬ N + 1 ≤ N`; `not_le`.
⚠ `Real.logb_zpow` does not exist (decomposition L8.1): stay with `rpow` + `Real.rpow_intCast`.""",
 '`Real.sInf_nonneg`, `csInf_le`, `IsLeast.csInf_eq`, `Real.rpow_logb`, `Real.rpow_intCast`, `Real.rpow_le_rpow_left_iff_of_base_lt_one`, `Int.le_floor`, `Int.lt_floor_add_one`, `zpow_le_zpow_right_of_le_one₀`, `zpow_add_one₀`, `exists_pow_lt_of_lt_one`, `le_of_forall_pos_lt_add`.',
 '[Sch] proof of Prop 10.1 (`schneider.txt:2953`): "replace a given defining norm `‖ ‖′` by the norm `‖v‖ := inf {s ∈ |K| : s ≥ ‖v‖′}` which, because of `r ≤ ‖v‖′/‖v‖ ≤ 1`, defines the same topology"; [Bel] proof of Thm II.1.13 (`bellaiche.txt:2109`); decomposition L8.1.',
 'A function on `ℝ`, independent of any ring. The lower inequality is **strict** (`c * zpowCeil c x < x`), stronger than [Sch]. `zpowCeil_nonneg` and `zpowCeil_le_of_le_zpow` need only `0 < c`.')
ticket('T029','`Real.zpowCeil`: algebra','Rescale.lean','T028','no','lemmas',
 'L8.2',
 ['exists_zpowCeil_eq_zpow','zpowCeil_zpow','zpowCeil_pos','zpowCeil_eq_zero_iff','zpowCeil_mono','zpowCeil_max','zpowCeil_zpow_mul','zpowCeil_mul_le'],
 """No logarithms are needed beyond T028: use *minimality* (`zpowCeil_le_of_le_zpow`) and `le_zpowCeil`.
1. `exists_zpowCeil_eq_zpow`: `⟨_, zpowCeil_of_pos hc₀ hc₁ hx⟩`.
2. `zpowCeil_zpow`: `le_antisymm (zpowCeil_le_of_le_zpow hc₀ le_rfl) (le_zpowCeil hc₀ hc₁)`.
3. `zpowCeil_pos`: step 1 and `zpow_pos hc₀`. `zpowCeil_eq_zero_iff`: `⇐` is `zpowCeil_of_nonpos`; `⇒` by contraposition
   from `zpowCeil_pos`.
4. `zpowCeil_mono`: let `x ≤ y`. If `y ≤ 0`, both sides are `0`. Otherwise `zpowCeil c y = c ^ N` with `y ≤ c ^ N`
   (step 1 + `le_zpowCeil`), so `x ≤ c ^ N` and minimality applies.
5. `zpowCeil_max`: `(zpowCeil_mono hc₀ hc₁).map_max`.
6. `zpowCeil_zpow_mul`: if `x ≤ 0` both sides vanish (`mul_nonpos_of_nonneg_of_nonpos`, `mul_zero`). If `0 < x`:
   `≤` by minimality at `c ^ n * c ^ N = c ^ (n + N)` (`zpow_add₀`), since `c ^ n * x ≤ c ^ n * c ^ N`; `≥` is the same
   inequality for `-n` and `c ^ n * x`, multiplied back by `c ^ n` (`zpow_neg`, `inv_mul_cancel_left₀`).
7. `zpowCeil_mul_le`: if `x = 0` or `y = 0` the left side is `zpowCeil c 0 = 0`. Otherwise `x ≤ c ^ N`, `y ≤ c ^ M`,
   `x * y ≤ c ^ (N + M)` (`mul_le_mul`), minimality.
⚠ `zpowCeil` is **not subadditive** (`c = 1/2`: `zpowCeil c 0.51 = 1 > 1/2 + 1/64`); do not try to prove
`zpowCeil c (x + y) ≤ …`. Only `max` is preserved.""",
 '`Monotone.map_max`, `zpow_pos`, `zpow_add₀`, `zpow_neg`, `mul_le_mul`, `mul_le_mul_of_nonneg_left`, `inv_mul_cancel_left₀`.',
 '[RM] §0.3.3; [Bel] proof of Lemma II.1.12 (`bellaiche.txt:2087`, `|πm| = |π||m|`); decomposition L8.2 (with the non-subadditivity attack).',
 'All for `0 < c < 1`; `zpowCeil_mul_le` for nonnegative arguments only (that is all a norm supplies).')
ticket('T030','The rescaled norm','Rescale.lean','T029, CLEANUP-9','no','def fields + lemmas',
 'L8.3',
 ['rescaledNorm','norm_toRescaled','norm_le_norm_toRescaled','norm_mul_norm_toRescaled_lt','exists_norm_rescaled_eq_zpow','norm_toRescaled_eq_of_forall_exists_zpow'],
 """Put `c := ‖(ϖ : R)‖`, with `hc₀ := ϖ.norm_pos` and `hc₁ := ϖ.norm_lt_one` (T021).
1. The four `sorry` fields of `rescaledNorm`. `map_zero'`: `norm_zero`, `Real.zpowCeil_of_nonpos hc₀ hc₁ le_rfl`.
   `add_le'`: `(Real.zpowCeil_mono hc₀ hc₁ (IsUltrametricDist.norm_add_le_max m n)).trans`, rewrite by
   `Real.zpowCeil_max`, then `max_le_add_of_nonneg` with `Real.zpowCeil_nonneg`. `neg'`: `norm_neg`.
   `eq_zero_of_map_eq_zero'`: `(Real.zpowCeil_eq_zero_iff hc₀ hc₁).1 hm`, `norm_le_zero_iff`.
2. `norm_toRescaled` is already `rfl` — it is the unfolding lemma for everything below.
3. `norm_le_norm_toRescaled`: `Real.le_zpowCeil`. `norm_mul_norm_toRescaled_lt`: `Real.mul_zpowCeil_lt` with
   `norm_pos_iff.2 hm`.
4. `exists_norm_rescaled_eq_zpow`: `change ∃ n : ℤ, Real.zpowCeil _ ‖(m : M)‖ = _`, then
   `Real.exists_zpowCeil_eq_zpow` with `norm_pos_iff.2 hm` (the `hm` of `Rescaled ϖ M` is the `hm` of `M`: same type).
5. `norm_toRescaled_eq_of_forall_exists_zpow`: `m = 0` → both sides `0` (`map_zero`, `norm_zero`); otherwise
   `‖m‖ = c ^ n` and `Real.zpowCeil_zpow`.""",
 '`IsUltrametricDist.norm_add_le_max`, `max_le_add_of_nonneg`, `norm_le_zero_iff`, `norm_pos_iff`, `AddGroupNorm.toNormedAddCommGroup`.',
 '[RM] §0.3.3 ("a norm taking values in `‖π‖ ^ ℤ ∪ {0}`, ultrametric, with `‖π‖ ‖m‖\' < ‖m‖ ≤ ‖m‖\'`"); [Sch] proof of Prop 10.1; [Col10] `colmez.txt:129`; decomposition L8.3.',
 'The rescaled norm lives on the **type synonym** `Rescaled ϖ M` (plan decision 5), never as a second norm on `M`. `[IsUltrametricDist M]` is necessary (T029\'s warning); `[NormOneClass R]` gives `0 < ‖ϖ‖`.')
cleanup('CLEANUP-11','Rescale.lean','T030')
ticket('T031','The rescaled module','Rescale.lean','CLEANUP-11, CLEANUP-7','no','instances + lemmas',
 'L8.4–L8.5',
 ['RE:^instance : IsUltrametricDist \\(Rescaled','RE:^instance \\[CompleteSpace M\\] : CompleteSpace \\(Rescaled','norm_smul_rescaled','isBoundedSMul_rescaled'],
 """1. `IsUltrametricDist`: `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`; the inequality is
   `Real.zpowCeil_mono` applied to `norm_add_le_max`, rewritten by `Real.zpowCeil_max` (first half of T030 `add_le'`).
2. `CompleteSpace`: T020 with `e : M ≃+ Rescaled ϖ M := AddEquiv.refl M` (no module structure is available here),
   `C := ‖ϖ‖⁻¹` (from `‖ϖ‖ * zpowCeil < ‖m‖` for `m ≠ 0`, trivial at `0`; `le_inv_mul_iff₀`) and `C' := 1`
   (`Real.le_zpowCeil`); conclude with `(AddEquiv.completeSpace_congr_of_bounds e h h').1 inferInstance`.
3. `norm_smul_rescaled`: unfold the norm (`change`), `ϖ.norm_smul` (T021) on the underlying `M`, then
   `Real.zpowCeil_zpow_mul hc₀ hc₁ 1` with `zpow_one`.
4. `isBoundedSMul_rescaled`: `IsBoundedSMul.of_norm_smul_le`. For `r = 0`: `zero_smul`, `norm_zero`. For `m = 0`
   likewise. Otherwise `‖r‖ = c ^ k` by `h`, the rescaled norm of `m` is `c ^ N` (T030 step 4), and
   `‖r • m‖ ≤ ‖r‖ * ‖m‖ ≤ c ^ k * c ^ N = c ^ (k + N)` on `M` (`norm_smul_le`, `Real.le_zpowCeil`), so minimality
   (`Real.zpowCeil_le_of_le_zpow`) gives the bound.""",
 '`IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`, `AddEquiv.refl`, `le_inv_mul_iff₀`, `IsBoundedSMul.of_norm_smul_le`, `norm_smul_le`, `zpow_add₀`, `zpow_one`; T020, T021.',
 '[RM] §0.3.3 ("complete when the original is, and with `‖π • m‖\' = ‖π‖ ‖m‖\'`"); [Bel] Hypothesis II.1.11 (`bellaiche.txt:2076`): "the set of non-zero norms `|R*|` is the discrete subgroup `|π|^ℤ`"; decomposition L8.4–L8.5.',
 '**Erratum E3**: `isBoundedSMul_rescaled` is a theorem under the value-group hypothesis, not an instance — without it the statement is false (`R = M = ℂ_p`, `‖r‖ = p^{-1/2}`: `‖r • 1‖\' = 1 > ‖r‖ ‖1‖\'`).')
cleanup('CLEANUP-12','Rescale.lean','T031','Final per-file cleanup for `Rescale.lean`.')
# ---------------- G9 Residue ----------------
ticket('T032','The unit ball of a module and the ideal `(ϖ)`','Residue.lean','CLEANUP-4, CLEANUP-9','yes (with G7, G8)','def fields + lemmas',
 'L9.1–L9.3',
 ['unitClosedBall','mem_unitClosedBall','toUnitClosedBall_mem_ideal','mem_ideal_iff','ideal_eq_closedBallIdeal','ideal_le_openUnitBallIdeal','ideal_eq_openUnitBallIdeal'],
 """1. Fields of `Submodule.unitClosedBall`. `add_mem'`: `(IsUltrametricDist.norm_add_le_max m n).trans (max_le hm hn)`.
   `smul_mem'`: `Subring.smul_def`, `(norm_smul_le (r : R) m).trans (mul_le_one₀ _ (norm_nonneg m) hm)` with
   `Subring.mem_unitClosedBall.1 r.2`. `mem_unitClosedBall`: `Iff.rfl`.
2. `toUnitClosedBall_mem_ideal`: `Ideal.mem_span_singleton_self _`.
3. `mem_ideal_iff`: `Ideal.mem_span_singleton'` (`∃ b, b * ϖ = a`). `⇒`: `‖b * ϖ‖ ≤ ‖b‖ * ‖ϖ‖ ≤ ‖ϖ‖`. `⇐`: take
   `b := ⟨(ϖ.unit⁻¹ : Rˣ) * a, _⟩`; its norm is `‖ϖ‖⁻¹ * ‖a‖ ≤ 1` by T016 (`ϖ.isMultiplicative.inv`, `.norm_inv`)
   and `inv_mul_le_one₀`; `Subtype.ext`, `mul_right_comm`/`mul_comm`, `Units.inv_mul`.
4. `ideal_eq_closedBallIdeal`: `Ideal.ext`; step 3, `mem_closedBallIdeal`, `coe_nnnorm`.
   `ideal_le_openUnitBallIdeal`: step 3, `mem_openUnitBallIdeal`, `lt_of_le_of_lt _ ϖ.norm_lt_one`.
5. `ideal_eq_openUnitBallIdeal`: `le_antisymm` with step 4. Given `‖a‖ < 1`: `a = 0` → `zero_mem`; otherwise
   `‖a‖ = ‖ϖ‖ ^ n < 1` forces `0 < n` (`zpow_lt_one_iff_right_of_lt_one₀`), so `‖ϖ‖ ^ n ≤ ‖ϖ‖ ^ 1`
   (`zpow_le_zpow_right_of_le_one₀`, `zpow_one`), and step 3 applies.""",
 '`Subring.smul_def`, `mul_le_one₀`, `Ideal.mem_span_singleton\'`, `Ideal.mem_span_singleton_self`, `Units.inv_mul`, `coe_nnnorm`, `zpow_lt_one_iff_right_of_lt_one₀`, `zpow_le_zpow_right_of_le_one₀`; T007 (`mem_closedBallIdeal`, `mem_openUnitBallIdeal`), T016.',
 '[Bel] §II.1.4 (`bellaiche.txt:2078`): "`M⁰ = {m ∈ M, |m| ≤ 1}`, which is an `R⁰`-submodule of `M`"; [Sch] proof of Prop 10.1: "Since `m · B₁(0) ⊆ B₁⁻(0)` …"; [RM] §0.3.4, §0.4.5 at `n = 1`; decomposition L9.1–L9.3.',
 '`M⁰` for seminormed rings and modules, no commutativity. The ideal lemmas need `NormedCommRing` (ideals of `R⁰`) and the **multiplicativity** of `ϖ` (a non-multiplicative unit of norm `< 1` can have `‖u⁻¹ a‖ > 1`). Discreteness is a hypothesis of the one lemma that needs it.')
ticket('T033','The residue module: `ϖ M⁰` is a ball','Residue.lean','T032','no','lemmas',
 'L9.5–L9.6',
 ['mem_ideal_smul_top_iff','mem_ideal_smul_top_iff_norm_lt_one'],
 """1. `mem_ideal_smul_top_iff`, `⇒`: `Submodule.smul_induction_on`. Generator `r • n` with `r ∈ ϖ.ideal`:
   `‖r • n‖ ≤ ‖r‖ * ‖n‖ ≤ ‖ϖ‖ * 1` (T032 step 3, `Submodule.mem_unitClosedBall`). Sums: `norm_add_le_max`, `max_le`.
   `⇐`: `n := ⟨(ϖ.unit⁻¹ : Rˣ) • (m : M), _⟩ ∈ M⁰` since `‖ϖ⁻¹ • m‖ = ‖ϖ‖⁻¹ * ‖m‖ ≤ 1` (T017 for `ϖ.unit⁻¹`, via T016
   `inv`/`norm_inv`); then `m = ϖ.toUnitClosedBall • n` (`Subtype.ext`, `smul_smul`, `Units.mul_inv`, `one_smul`) and
   `Submodule.smul_mem_smul ϖ.toUnitClosedBall_mem_ideal Submodule.mem_top`.
2. `mem_ideal_smul_top_iff_norm_lt_one`: rewrite by step 1; `‖m‖ ≤ ‖ϖ‖ ↔ ‖m‖ < 1`. `⇒`: `ϖ.norm_lt_one`. `⇐`: `m = 0`
   trivial; otherwise `‖m‖ = ‖ϖ‖ ^ n < 1` forces `1 ≤ n`, exactly as in T032 step 5.
The `Module ϖ.ResidueRing (ϖ.ResidueModule M)` instance is found by `inferInstance` (checked in the skeleton;
it needs `Mathlib.Algebra.Module.Torsion.Basic`) — nothing to prove there.""",
 '`Submodule.smul_induction_on`, `Submodule.smul_mem_smul`, `Submodule.mem_top`, `smul_smul`, `Units.mul_inv`, `one_smul`, `norm_smul_le`, `zpow_lt_one_iff_right_of_lt_one₀`; T016, T017.',
 '[Bel] §II.1.4 (`bellaiche.txt:2078`): "`M̃ = M⁰/πM⁰`, which is a `R̃`-module"; [RM] §0.3.4 ("if the norm of `M` takes values in `‖π‖ ^ ℤ ∪ {0}` then `π M⁰ = {m | ‖m‖ < 1}`"); [Bel] Lemma II.1.12 (`|M| ⊂ |R|`); decomposition L9.5–L9.6.',
 '`ϖ M⁰ = {‖m‖ ≤ ‖ϖ‖}` holds for **every** normed module; the open-ball form carries the value hypothesis (necessary: `ℂ_p`, T042).')
cleanup('CLEANUP-13','Residue.lean','T033','Final per-file cleanup for `Residue.lean`.')
# ---------------- G11 GaugeNorm ----------------
ticket('T037','The gauge norm: the workhorse','GaugeNorm.lean','none','yes (Mathlib-only file)','lemmas',
 'L11.1–L11.3',
 ['gaugeNorm_nonneg','exists_mem_zpow_smul','gaugeNorm_le_zpow_iff','gaugeNorm_eq_zero_or_exists_zpow','gaugeNorm_le_one_iff'],
 """Write `E r := {n : ℤ | r ∈ ((ϖ ^ n : Aˣ) : A) • (A₀ : Set A)}` and `S r := {a ^ (-n) | n ∈ E r}`; `gaugeNorm` is
`sInf (S r)` and `S r` is bounded below by `0`.
1. `gaugeNorm_nonneg`: `Real.sInf_nonneg`, `zpow_nonneg ha.le`.
2. `exists_mem_zpow_smul` (**no `hϖ`**): `A₀ ∈ 𝓝 0` is `hbasis.mem_of_mem trivial` at `n = 0` (`pow_zero`, `one_smul`).
   `(continuous_mul_right r).tendsto 0` with `zero_mul` makes `{x | x * r ∈ A₀}` a neighbourhood of `0`, so it contains
   some `ϖ ^ N • A₀` (`hbasis.mem_iff`); `ϖ ^ N = ϖ ^ N • 1` lies there (`A₀.one_mem`), so `ϖ ^ N * r ∈ A₀` and
   `r = ϖ ^ (-N) • (ϖ ^ N * r)`: take `n := -N` (`zpow_neg`, `zpow_natCast`, `Units.inv_mul_cancel_left`).
3. Two private helpers on `E r`. (a) *Down-set*: `n ∈ E r → m ≤ n → m ∈ E r`, from `ϖ ^ n • b = ϖ ^ m • (ϖ ^ (n - m) * b)`
   and `ϖ ^ (n - m) ∈ A₀` as a natural power of `ϖ ∈ A₀` (`Int.toNat_of_nonneg`, `pow_mem`) — this is where `hϖ` enters.
   (b) *Dichotomy*: either `E r = Set.univ` (unbounded above + (a)), or `E r` has a greatest element `N`
   (`Int.exists_greatest_of_bdd` with step 2) and `sInf (S r) = a ^ (-N)` (`IsLeast.csInf_eq`; `n ≤ N` gives
   `a ^ (-N) ≤ a ^ (-n)` by `zpow_le_zpow_iff_right₀ ha`).
4. `gaugeNorm_le_zpow_iff`. `⇐`: `csInf_le`. `⇒`: by (b): if `E r = univ` done; else `a ^ (-N) ≤ a ^ (-n)` gives
   `n ≤ N` and (a) applies. Both sides are true when `r ∈ ⋂ ϖ ^ n A₀` — no `T2Space`.
5. `gaugeNorm_eq_zero_or_exists_zpow`: by (b). If `E r = univ`: `sInf (S r) ≤ a ^ (-(k : ℤ))` for all `k : ℕ`, and
   `(a⁻¹) ^ k → 0` (`exists_pow_lt_of_lt_one` for `a⁻¹ < 1`), so the infimum is `0` with step 1. Else `⟨-N, _⟩`.
6. `gaugeNorm_le_one_iff`: step 4 at `n = 0` (`neg_zero`, `zpow_zero`, `Units.val_one`, `one_smul`).""",
 '`Real.sInf_nonneg`, `csInf_le`, `IsLeast.csInf_eq`, `Filter.HasBasis.mem_of_mem`, `Filter.HasBasis.mem_iff`, `continuous_mul_right`, `Int.exists_greatest_of_bdd`, `zpow_le_zpow_iff_right₀`, `exists_pow_lt_of_lt_one`, `Set.mem_smul_set`, `zpow_natCast`, `pow_mem`.',
 '[JN] Remark 2.1.3(1) (`jn.txt:502`): "If `a ∈ ℝ_{>1}`, then we may define a norm on `R` by `|r| = inf {a^{−n} | r ∈ ϖⁿR₀, n ∈ ℤ}`. Equipped with this norm, `R` is a Tate normed ring with unit ball `R₀`"; [Wed] Prop 6.14 (`wedhorn.txt:2176`): "For every `a ∈ A` there exists `n ∈ ℕ` such that `a sⁿ ∈ B`"; decomposition L11.1–L11.3.',
 'Mathlib vocabulary only (plan decision 6): a commutative topological ring `A`, a subring `A₀`, a unit `ϖ ∈ A₀`, and `hbasis` — the fact Tau Ceti\'s `IsTateRing` supplies. Absorption needs no `hϖ`; the workhorse needs no `T2Space`.')
ticket('T038','The gauge norm: the ring-norm inequalities','GaugeNorm.lean','T037','no','lemmas',
 'L11.4',
 ['gaugeNorm_add_le_max','gaugeNorm_neg','gaugeNorm_mul_le','gaugeNorm_unit_mul'],
 """Everything goes through the workhorse `gaugeNorm_le_zpow_iff` and the value lemma of T037.
1. `gaugeNorm_neg` (no hypotheses): the two defining sets coincide, since `-(ϖ ^ n • b) = ϖ ^ n • (-b)`
   (`Set.mem_smul_set`, `smul_neg`, `neg_mem`); `congrArg sInf (Set.ext _)`.
2. `gaugeNorm_add_le_max`: `ϖ ^ n • A₀` is closed under addition (`smul_add`, `add_mem`). Let `m := max (N r) (N s)`.
   By the value lemma `m = 0` or `m = a ^ k`. If `m = a ^ k = a ^ (-(-k))`: both `r, s ∈ ϖ ^ (-k) • A₀` (workhorse `⇒`),
   so `r + s` is, so `N (r + s) ≤ a ^ k`. If `m = 0`: `r, s ∈ ϖ ^ n • A₀` for every `n`, hence `N (r + s) ≤ a ^ (-n)`
   for every `n`, hence `≤ 0` (as in T037 step 5).
3. `gaugeNorm_mul_le`: `(ϖ ^ n • b) * (ϖ ^ m • b') = ϖ ^ (n + m) • (b * b')` (`zpow_add`, `mul_mul_mul_comm`). If
   `N r = a ^ k` and `N s = a ^ l`: `r * s ∈ ϖ ^ (-k - l) • A₀`, so `N (r * s) ≤ a ^ (k + l)` (`zpow_add₀`). If `N r = 0`
   (or `N s = 0`): `r ∈ ϖ ^ n • A₀` for all `n`, `s ∈ ϖ ^ m • A₀` for one `m` (T037 absorption), so `r * s` lies in
   every `ϖ ^ n • A₀` and `N (r * s) ≤ 0 = N r * N s`.
4. `gaugeNorm_unit_mul`: `ϖ * r ∈ ϖ ^ n • A₀ ↔ r ∈ ϖ ^ (n - 1) • A₀`, so the defining set of `ϖ * r` is
   `a⁻¹ • S r` (`zpow_sub_one₀`, `neg_sub`); `Real.sInf_smul_of_nonneg (inv_nonneg.2 _)`, `smul_eq_mul`.""",
 '`Set.mem_smul_set`, `smul_neg`, `smul_add`, `zpow_add`, `zpow_add₀`, `zpow_sub_one₀`, `Real.sInf_smul_of_nonneg`, `smul_eq_mul`.',
 '[JN] Definition 2.1.1 (`jn.txt:476`): "(2) `|r + s| ≤ max(|r|, |s|)`; (3) `|rs| ≤ |r||s|`"; Remark 2.1.3(1): "`ϖ` is a multiplicative pseudo-uniformizer"; decomposition L11.4.',
 'No `T2Space` anywhere in this ticket: the inequalities hold for the seminorm. `gaugeNorm_neg` holds for any subring and unit.')
cleanup('CLEANUP-ALL-2','','T038','Before milestone M2 (T039). Sweep every file with finished tickets; do not touch declarations that are still `sorry`.')
ticket('T039','The gauge norm is a ring norm inducing the topology','GaugeNorm.lean','CLEANUP-ALL-2','no','lemmas + def fields',
 'L11.5–L11.6',
 ['hasBasis_nhds_zero_gaugeNorm','gaugeNorm_eq_zero_iff','exists_gaugeNorm_eq_zpow','gaugeNorm_one','gaugeNorm_unit','gaugeRingNorm'],
 """1. `hasBasis_nhds_zero_gaugeNorm`: `hbasis.to_hasBasis`. Given `n : ℕ`, take `ε := a ^ (-(n : ℤ))`:
   `N r < ε → N r ≤ ε → r ∈ ϖ ^ n • A₀` (workhorse; `zpow_natCast`, `Units.val_pow_eq_pow_val`). Given `ε > 0`, pick
   `n : ℕ` with `(a⁻¹) ^ n < ε` (`exists_pow_lt_of_lt_one`); `r ∈ ϖ ^ n • A₀ → N r ≤ a ^ (-(n : ℤ)) < ε`.
2. `gaugeNorm_eq_zero_iff` (`T2Space`). `⇐`: `0 ∈ ϖ ^ n • A₀` for all `n`, so `N 0 ≤ a ^ (-n)` for all `n`. `⇒`: if
   `r ≠ 0`, `{r}ᶜ` is a neighbourhood of `0` (`isOpen_compl_singleton`), so contains some `ϖ ^ n • A₀`; but
   `N r = 0 ≤ a ^ (-n)` puts `r` in it.
3. `exists_gaugeNorm_eq_zpow`: T037's value lemma and step 2.
4. `gaugeNorm_one` (`Nontrivial`): `N 1 ≤ 1` by `gaugeNorm_le_one_iff` and `one_mem`. If `N 1 < 1`, then
   `N 1 = a ^ k` with `k ≤ -1` (step 3 with `one_ne_zero`; `zpow_lt_one_iff_right₀`), so `1 ∈ ϖ • A₀`, i.e.
   `ϖ⁻¹ ∈ A₀`; then `1 = ϖ ^ n • (ϖ⁻¹) ^ n ∈ ϖ ^ n • A₀` for every `n`, so `N 1 = 0`, so `1 = 0` by step 2 — absurd.
5. `gaugeNorm_unit`: T038 `gaugeNorm_unit_mul` at `r = 1`, step 4, `mul_one`.
6. Fields of `gaugeRingNorm`: `map_zero'` from step 2; `add_le'` from T038 and `max_le_add_of_nonneg`; `neg'`, `mul_le'`
   from T038; `eq_zero_of_map_eq_zero'` from step 2.""",
 '`Filter.HasBasis.to_hasBasis`, `exists_pow_lt_of_lt_one`, `isOpen_compl_singleton`, `zpow_natCast`, `Units.val_pow_eq_pow_val`, `max_le_add_of_nonneg`, `one_mem`, `pow_mem`.',
 '[JN] Remark 2.1.3(1) (`jn.txt:502`), quoted in T037; [RM] §0.4.6 ("inducing the topology of `A`"; "⚠ The Hausdorff hypothesis is necessary: without it the formula gives only a seminorm, with kernel the closure of `0`"); decomposition L11.5–L11.6.',
 '`T2Space` exactly where the seminorm must be a norm; `Nontrivial` exactly for `N 1 = 1`. [JN] omit "Hausdorff" because their Tate rings are complete. `gaugeRingNorm` is a `RingNorm`; turning it into a `NormedRing` instance is left to the caller (a second norm on `A` must not become an instance).',
 milestone=True)
cleanup('CLEANUP-15','GaugeNorm.lean','T039','Final per-file cleanup for `GaugeNorm.lean`.')
# ---------------- G10 Huber ----------------
ticket('T034','Ideal powers are norm balls','Huber.lean','CLEANUP-13, CLEANUP-5','no','lemmas',
 'L10.1–L10.2',
 ['isTopologicallyNilpotent','mem_ideal_pow_iff','ideal_pow_eq_closedBallIdeal','ideal_fg'],
 """1. `isTopologicallyNilpotent`: `IsTopologicallyNilpotent.of_norm_lt_one ϖ.norm_lt_one` (T014).
2. `mem_ideal_pow_iff`: `ideal`, `Ideal.span_singleton_pow`, `Ideal.mem_span_singleton'`. `⇒`: `a = b * ϖ ^ n`,
   `‖a‖ ≤ ‖b‖ * ‖ϖ ^ n‖ ≤ ‖ϖ‖ ^ n` (T015 `norm_pow`). `⇐`: `b := ⟨((ϖ.unit ^ (-(n : ℤ)) : Rˣ) : R) * a, _⟩`, of norm
   `‖ϖ‖ ^ (-n) * ‖a‖ ≤ 1` (T016 `zpow`, `norm_zpow`); `Subtype.ext` and `zpow_neg`, `zpow_natCast`,
   `Units.inv_mul_cancel_left`. At `n = 0` both sides are trivially true — check it is not a special case.
3. `ideal_pow_eq_closedBallIdeal`: `Ideal.ext`; step 2, `mem_closedBallIdeal`, `NNReal.coe_pow`, `coe_nnnorm`.
4. `ideal_fg`: `Submodule.fg_span_singleton _`.""",
 '`Ideal.span_singleton_pow`, `Ideal.mem_span_singleton\'`, `Submodule.fg_span_singleton`, `NNReal.coe_pow`, `coe_nnnorm`, `zpow_neg`, `zpow_natCast`; T014, T015, T016, T007.',
 '[RM] §0.4.5 ("the ideal powers are the norm balls, `ϖⁿ R⁰ = {r ∈ R⁰ | ‖r‖ ≤ ‖ϖ‖ ^ n}`"); [Wed] Def 6.1(ii) (`wedhorn.txt:2059`): "`I` is a finitely generated ideal of `A₀`"; [JN] Remark 2.1.3(1): "`ϖ` is a topologically nilpotent unit"; [SRC] `00_TateRings.mem_ideal_pow`; decomposition L10.1–L10.2.',
 'Stated in Mathlib vocabulary (erratum E7); `NormedCommRing` + `NormOneClass` + `IsUltrametricDist`, as `R⁰` must be a subring with ideals.')
cleanup('CLEANUP-ALL-1','','T034','Before milestone M1 (T035). Sweep every file with finished tickets; do not touch declarations that are still `sorry`.')
ticket('T035','The unit ball is a ring of definition','Huber.lean','CLEANUP-ALL-1','no','theorems',
 'L10.3–L10.6',
 ['isAdic_ideal','exists_pow_mul_mem_unitClosedBall','hasBasis_nhds_zero_smul_unitClosedBall','isPowerBounded_of_mem_unitClosedBall'],
 """1. `isAdic_ideal`: `isAdic_iff` (the `IsTopologicalRing ↥(unitClosedBall R)` instance is Mathlib's subring instance).
   (i) openness: rewrite by T034 `ideal_pow_eq_closedBallIdeal`, then T007 `isOpen_closedBallIdeal (pow_pos _ n)`.
   (ii) cofinality: `Metric.mem_nhds_iff` gives `ε`; `exists_pow_lt_of_lt_one` gives `n` with `‖ϖ‖ ^ n < ε`; an
   element of `ϖ.ideal ^ n` has norm `≤ ‖ϖ‖ ^ n < ε` (T034), so lies in the ball (`mem_ball_zero_iff`,
   the subtype norm is the ambient norm, by `rfl`; cf. `AddSubgroupClass.coe_norm`).
2. `exists_pow_mul_mem_unitClosedBall`: `‖ϖ ^ n * a‖ = ‖ϖ‖ ^ n * ‖a‖` (T015 `norm_pow_mul`). `a = 0`: `n := 0`.
   Otherwise `exists_pow_lt_of_lt_one (inv_pos.2 (norm_pos_iff.2 ha))` and `mul_inv_le_iff₀`.
3. `hasBasis_nhds_zero_smul_unitClosedBall`: first `ϖ ^ n • (R⁰ : Set R) = Metric.closedBall 0 (‖ϖ‖ ^ n)`
   (`Set.ext`, `Set.mem_smul_set`, `smul_eq_mul`; `⇒` by `norm_pow_mul`; `⇐` with `r = ϖ ^ n * (ϖ⁻¹ ^ n * r)` and T016).
   Then `Metric.nhds_basis_closedBall_pow ϖ.norm_pos ϖ.norm_lt_one` rewritten along that identity.
4. `isPowerBounded_of_mem_unitClosedBall`: `PowerBounded.isPowerBounded_of_norm_le_one (mem_unitClosedBall.1 ha)` (T013).""",
 '`isAdic_iff`, `Metric.mem_nhds_iff`, `exists_pow_lt_of_lt_one`, `mem_ball_zero_iff`, `Metric.nhds_basis_closedBall_pow`, `Set.mem_smul_set`, `smul_eq_mul`; T007, T013, T015, T016, T034.',
 '[JN] Remark 2.1.3(1) (`jn.txt:500`): "The underlying topological ring is a Tate ring in the language of Huber; the unit ball `R₀` is a ring of definition and `ϖ` is a topologically nilpotent unit"; [Wed] Def 6.1(ii), Def 6.10, Prop 6.14 (`wedhorn.txt:2059, 2176`); [Buz07] `buzzard.txt:158`: "the ideals of `A₀` generated by `ρⁿ` … form a basis of open neighbourhoods of zero"; [RM] §0.4.5; decomposition L10.3–L10.6.',
 '**Seam (E7)**: with T006 (`isOpen_unitClosedBall`), T034 (`ideal_fg`, `isTopologicallyNilpotent`) these are the fields of Tau Ceti\'s pair of definition plus the Tate condition, in Mathlib vocabulary. `hasBasis_…` is stated in exactly the hypothesis shape of `GaugeNorm.lean`.',
 milestone=True)
ticket('T036','The round trip: gauge norm of `(R⁰, ϖ)` is the rescaled norm','Huber.lean','T035, CLEANUP-12, CLEANUP-15','no','theorem',
 'L10.7',
 ['gaugeNorm_unitClosedBall'],
 """Both sides are `sInf` of a set of reals; show the two sets are equal and finish with `congrArg sInf`.
1. For `n : ℤ`: `r ∈ ((ϖ.unit ^ n : Rˣ) : R) • (R⁰ : Set R) ↔ ‖r‖ ≤ ‖ϖ‖ ^ n` — the `ℤ`-version of T035 step 3, by
   T016 `zpow`/`norm_zpow` (`⇒`: `‖ϖ ^ n * b‖ = ‖ϖ‖ ^ n * ‖b‖ ≤ ‖ϖ‖ ^ n`; `⇐`: `b := ϖ ^ (-n) * r`).
2. `(‖ϖ‖⁻¹) ^ (-n) = ‖ϖ‖ ^ n` (`inv_zpow'`, `neg_neg`).
3. `Subring.gaugeNorm` and `Real.zpowCeil` unfold (`rfl`/`unfold`) to `sInf {y | ∃ n, y = _ ∧ _}`; `Set.ext` with steps
   1–2. Only the two *definitions* are used — no lemma of `GaugeNorm.lean` or `Rescale.lean`.""",
 '`Set.mem_smul_set`, `smul_eq_mul`, `inv_zpow\'`, `neg_neg`, `zpow_neg`, `Units.mul_inv_cancel_left`; T016.',
 '[JN] Remark 2.1.3(1) (`jn.txt:500–502`), both directions, read against [RM] §0.3.3 and [JN] Lemma 2.1.7; decomposition L10.7 (**planner\'s addition**: the precise sense in which the two bridges are mutually inverse).',
 'Equality with the *rescaled* norm `zpowCeil ‖ϖ‖ ‖r‖`, not the original norm (false in `ℂ_p`, T042). At `r = 0` both sides are `0`. Depends on CLEANUP-12 and CLEANUP-15 only so that both definitions are final.')
cleanup('CLEANUP-14','Huber.lean','T036','Final per-file cleanup for `Huber.lean`.')
# ---------------- G12 Examples ----------------
ticket('T040','Examples over `ℚ_p`','Examples.lean','CLEANUP-13','yes (with G10)','examples',
 'L12.1–L12.4',
 ['unitClosedBall_padic','ideal_padic_eq_openUnitBallIdeal','nonempty_residueRing_padic_equiv_zmod','norm_zpow_mul_mem_Ioc_iff'],
 """1. `unitClosedBall_padic`: `Subring.ext fun x ↦ _`; `mem_unitClosedBall` against the carrier `{x | ‖x‖ ≤ 1}` of
   `PadicInt.subring p` (`Iff.rfl` after unfolding).
2. `ideal_padic_eq_openUnitBallIdeal`: T032 `ideal_eq_openUnitBallIdeal`. The pseudo-uniformiser coerces to
   `algebraMap ℚ_[p] ℚ_[p] p = p` (`coe_ofNormedAlgebra`, `Algebra.algebraMap_self`/`rfl`). For `r ≠ 0`:
   `‖r‖ = p ^ (-r.valuation)` (`Padic.norm_eq_zpow_neg_valuation`) `= ‖p‖ ^ r.valuation` (`Padic.norm_p`, `inv_zpow'`).
3. `nonempty_residueRing_padic_equiv_zmod`: transport along step 1 to `ℤ_[p]`; the composite
   `unitClosedBall ℚ_[p] →+* ZMod p` through `PadicInt.toZMod` is surjective (`ZMod.ringHom_surjective`) with kernel
   the open unit ball (`PadicInt.ker_toZMod`, `PadicInt.norm_lt_one_iff_dvd`, `PadicInt.maximalIdeal_eq_span_p`);
   `RingHom.quotientKerEquivOfSurjective`, `Ideal.quotEquivOfEq`.
4. `norm_zpow_mul_mem_Ioc_iff`: `norm_mul`, `norm_zpow`, `Padic.norm_p`, `Padic.norm_eq_zpow_neg_valuation hx`:
   `‖p ^ n * x‖ = (p : ℝ) ^ (-(n + v))`; `Set.mem_Ioc`; `zpow_lt_zpow_iff_right₀`, `zpow_le_one_iff_right₀`
   (base `(p : ℝ) > 1`), `omega`.""",
 '`PadicInt.subring`, `Padic.norm_eq_zpow_neg_valuation`, `Padic.norm_p`, `inv_zpow\'`, `PadicInt.toZMod`, `PadicInt.ker_toZMod`, `ZMod.ringHom_surjective`, `RingHom.quotientKerEquivOfSurjective`, `Ideal.quotEquivOfEq`, `zpow_lt_zpow_iff_right₀`, `zpow_le_one_iff_right₀`.',
 '[RM] Layer 0 Examples ("`ℚ_p` … with `R⁰`", "the shells `‖ϖ‖ < ‖ϖⁿ x‖ ≤ 1` in `ℚ_p` with `ϖ = p`"); decomposition L12.1–L12.4.',
 'Concrete instances only; the hypotheses `hc₀`, `hc₁` are kept as arguments so that the statement names the pseudo-uniformiser `ofNormedAlgebra ℚ_[p] hc₀ hc₁`.')
ticket('T041','Examples over `ℤ_p`: the non-example and the Neumann series','Examples.lean','T040','no','examples',
 'L12.5',
 ['not_isTate_padicInt','norm_tsum_pow_padicInt','norm_tsum_pow_padicInt_sub_one'],
 """1. `not_isTate_padicInt`: `rintro ⟨⟨ϖ⟩⟩`; `ϖ.unit.isUnit` and `PadicInt.isUnit_iff` give `‖(ϖ : ℤ_[p])‖ = 1`,
   contradicting `ϖ.norm_lt_one`.
2. `‖(p : ℤ_[p])‖ < 1`: `PadicInt.norm_p`, `inv_lt_one_of_one_lt₀`, `Nat.one_lt_cast`, `hp.out.one_lt`.
3. `norm_tsum_pow_padicInt`: T010 `norm_tsum_geometric` with step 2.
4. `norm_tsum_pow_padicInt_sub_one`: T010 `norm_tsum_geometric_sub_one`, then `PadicInt.norm_p`.""",
 '`PadicInt.isUnit_iff`, `PadicInt.norm_p`, `inv_lt_one_of_one_lt₀`, `Nat.one_lt_cast`; T010.',
 '[RM] §0.4.7 ("A non-example: `ℤ_[p]`, whose norm has no unit of norm less than `1`"); acceptance example ("`‖∑\' n, pⁿ‖ = 1` in `ℤ_p`"); decomposition L12.5.',
 'Concrete instances; needs `CompleteSpace ℤ_[p]`, `IsUltrametricDist ℤ_[p]`, `NormOneClass ℤ_[p]` — all in Mathlib.')
ticket('T042','Examples over `ℂ_p`: the value group is not discrete','Examples.lean','T041, CLEANUP-12','no','examples',
 'L12.6',
 ['exists_norm_p_lt_norm_lt_one_padicComplex','exists_zpowCeil_norm_ne_padicComplex','ideal_padicComplex_ne_openUnitBallIdeal'],
 """1. `obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (p : ℂ_[p]) two_pos`, so `‖x‖ ^ 2 = ‖(p : ℂ_[p])‖` (`norm_pow`).
   `‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ =: t ∈ (0, 1)`: `(p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] p` (`map_natCast`),
   `norm_algebraMap'`, `Padic.norm_p`. From `‖x‖ ^ 2 = t`: `t < ‖x‖` (else `‖x‖ ^ 2 ≤ t ^ 2 < t`) and `‖x‖ < 1` (else
   `‖x‖ ^ 2 ≥ 1 > t`); `pow_le_pow_left₀`, `nlinarith`.
2. `exists_zpowCeil_norm_ne_padicComplex`: the same `x`. `Real.zpowCeil t ‖x‖ = t ^ n` for some `n` (T029); if it
   equalled `‖x‖` then `t ^ 1 < t ^ n < t ^ 0`, i.e. `0 < n < 1` (`zpow_lt_zpow_iff_right_of_lt_one₀`), `omega`.
3. `ideal_padicComplex_ne_openUnitBallIdeal`: `⟨x, _⟩ : unitClosedBall ℂ_[p]` lies in `openUnitBallIdeal` but not in
   the ideal, by T032 `mem_ideal_iff` and `coe_ofNormedAlgebra`, `norm_algebraMap'`; `fun h ↦ _` with `h ▸`/`SetLike.ext_iff`.""",
 '`IsAlgClosed.exists_pow_nat_eq`, `norm_pow`, `map_natCast`, `norm_algebraMap\'`, `Padic.norm_p`, `pow_le_pow_left₀`, `zpow_lt_zpow_iff_right_of_lt_one₀`; T029, T032.',
 '[RM] Layer 0 Examples ("the rescaled norm on `ℂ_p` with `π = p` … is not the original norm"); decomposition L12.6. This is the counterexample behind errata E3 and the value hypotheses of T031–T033.',
 'Concrete; uses `NormedAlgebra ℚ_[p] ℂ_[p]` and `IsAlgClosed ℂ_[p]` from `Mathlib.NumberTheory.Padics.Complex`.')
cleanup('CLEANUP-16','Examples.lean','T042')
ticket('T043','Counterexample: `ℤ` with the discrete topology','Examples.lean','CLEANUP-16, CLEANUP-5','no','examples',
 'L12.7',
 ['isPowerBounded_int','norm_two_int','not_neBot_nhdsNE_zero_int'],
 """1. `isPowerBounded_int`: unfold `IsPowerBounded`, `TopologicalRing.IsBounded`. Given `U ∈ 𝓝 0` take `V := {0}`:
   `(isOpen_discrete _).mem_nhds rfl`; `{0} * S ⊆ {0}` (`Set.zero_mul_subset`, with `Set.singleton_zero`) and
   `{0} ⊆ U` by `mem_of_mem_nhds`.
2. `norm_two_int`: `Int.norm_eq_abs`; `norm_num`.
3. `not_neBot_nhdsNE_zero_int`: `discreteTopology_iff_nhds_ne.1 inferInstance 0` gives `𝓝[≠] 0 = ⊥`; `Filter.not_neBot`.""",
 '`isOpen_discrete`, `Set.zero_mul_subset`, `mem_of_mem_nhds`, `Int.norm_eq_abs`, `discreteTopology_iff_nhds_ne`, `Filter.not_neBot`.',
 '[RM] §0.2.2 ("over `ℤ` with the discrete topology every element is power-bounded while `‖2‖ = 2`"); decomposition L12.7.',
 'Shows `NeBot (𝓝[≠] 0)` cannot be dropped from T013\'s converse.')
ticket('T044','Counterexample: the `ℓ¹` norm on `ℝ[X]/(X² − X)`','Examples.lean','T043','no','instance fields + examples',
 'L12.8',
 ['addGroupNorm','RE:^theorem norm_mul_le \\(x y : L1Pair\\)','oneSubTwoX_sq','norm_oneSubTwoX','isPowerBounded_oneSubTwoX'],
 """Coordinates: `a + bX ↦ (u, v) = (a, a + b)`, so multiplication is componentwise and `‖(u, v)‖ = |u| + |v − u|`.
1. Fields of `addGroupNorm`. `map_zero'`: `simp`. `add_le'`: `(x + y).2 − (x + y).1 = (x.2 − x.1) + (y.2 − y.1)`
   (`Prod.fst_add`, `Prod.snd_add`, `ring`), then `abs_add` twice and `linarith`. `neg'`: `abs_neg` after
   `-x.2 − -x.1 = -(x.2 − x.1)`. `eq_zero_of_map_eq_zero'`: both summands vanish (`add_eq_zero_iff_of_nonneg`,
   `abs_eq_zero`), so `x.1 = 0`, `x.2 = x.1`; `Prod.ext`.
2. `norm_mul_le`: with `a := x.1`, `b := x.2 − x.1`, `a' := y.1`, `b' := y.2 − y.1`:
   `x.2 * y.2 − x.1 * y.1 = a * b' + b * a' + b * b'`, so
   `‖x * y‖ = |a a'| + |a b' + b a' + b b'| ≤ (|a| + |b|) (|a'| + |b'|)` by `abs_add_three`, `abs_mul`, and expanding.
3. `oneSubTwoX_sq`: `Prod.ext` + `norm_num` (`(1, −1)² = (1, 1) = 1`).
4. `norm_oneSubTwoX`: `norm_def`; `norm_num` (`|1| + |−1 − 1| = 3`).
5. `isPowerBounded_oneSubTwoX`: T012 `PowerBounded.isPowerBounded_of_norm_pow_le (C := 3)`. For `n = 2k` the power is
   `1` with `‖1‖ = 1`; for `n = 2k + 1` it is `oneSubTwoX` (`pow_mul`, step 3, `one_pow`); `Nat.even_or_odd'`.""",
 '`abs_add`, `abs_neg`, `abs_mul`, `abs_add_three`, `abs_eq_zero`, `add_eq_zero_iff_of_nonneg`, `Prod.ext`, `pow_mul`, `Nat.even_or_odd\'`; T012.',
 '[RM] §0.2.2 ("the `ℓ¹` norm on `ℝ[X]/(X² − X)` … the element `1 − 2X` squares to `1` and has norm `3`"); decomposition L12.8 (arithmetic verified by hand).',
 'Shows that submultiplicativity does not suffice in T013: `NormMulClass` cannot be weakened to a `NormedRing`. Realised on `ℝ × ℝ` to avoid a quotient of `ℝ[X]`.')
cleanup('CLEANUP-17','Examples.lean','T044','Final per-file cleanup for `Examples.lean`.')
# ---------------- chain root + final ----------------
T.append(dict(id='T045',raw="""### [T045] Add Layer 0 to the Tau Ceti chain root
- **Status**: open · **File**: `PhD/TauCeti.lean` · **Depends on**: CLEANUP-2, CLEANUP-4, CLEANUP-5, CLEANUP-6, CLEANUP-7, CLEANUP-9, CLEANUP-10, CLEANUP-12, CLEANUP-13, CLEANUP-14, CLEANUP-15, CLEANUP-17 · **Parallel**: no · **Type**: build gate

#### Statement
Append (append-only — a parallel board also edits this file; re-read it immediately before editing) the two leaf
modules, which import the other ten:
```lean
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Examples
import PhD.TauCeti.Code.PadicFunctionalAnalysis.NormComparison
```
#### Proof sketch
1. `grep -rn "sorry" PhD/TauCeti/Code/PadicFunctionalAnalysis/` returns nothing.
2. `lake build PhD.TauCeti` passes (never `lake build PhD`). No `import PhD.Main` anywhere in the folder.
3. `#print axioms` on the two milestones (`NormedRing.PseudoUniformizer.isAdic_ideal`, `Subring.gaugeRingNorm`) and on
   `NormedRing.PseudoUniformizer.gaugeNorm_unitClosedBall`: `propext`, `Classical.choice`, `Quot.sound` only.
4. `lake exe runLinter` on each of the twelve modules: no findings.
#### Mathlib lemmas needed
None.
#### Sources
Plan, "Build protocol"; memory `tauceti-newton-polygons` (chain layout, CI gate).
#### Generality decision
Not applicable.
"""))
cleanup('CLEANUP-FINAL','','T045','Final sweep of the whole folder: naming, docstrings, import minimality (`lake exe shake`), module docstrings list the final declaration names, the README provenance table of the roadmap can be pointed at these files.')
