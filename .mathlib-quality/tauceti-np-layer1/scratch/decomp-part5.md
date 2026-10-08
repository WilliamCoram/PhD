
---

## Result R9 — extensions and completions (§1.3.6, §1.5.1–§1.5.3, `Extension.lean`)

### Plain-English proof (source: [RM] §1.3.6, §1.5.1–§1.5.3; [BGR] 3.2.4/2–3, 3.1.3, 1.5.1; [Gou20] 6.3–6.4, 6.8.7; [Kob84] III §2–§4)

**Restriction (§1.5.1).** For any normed `K`-algebra field `L`, `‖algebraMap K L x‖ = ‖x‖`
(Mathlib `norm_algebraMap'`), so `normAddVal L (algebraMap x) = −log ‖x‖ = normAddVal K x` for
`x ≠ 0`, and both are `⊤` at `0`. (Ultrametricity of `L` is Mathlib's `IsUltrametricDist.of_normedAlgebra`;
[BGR] 3.2.4/2 identifies the norm of an algebraic `L` over complete `K` with the spectral norm.)
**Ramification (§1.3.6).** Let `K`, `L` be discretely valued, `π` a uniformiser of `K`. In `L`,
`v_L (algebraMap π) = g_L ^ d` for some integer `d`, and `d > 0` since `‖algebraMap π‖ = ‖π‖ < 1`
and `g_L < 1`; `e := d` is the ramification index ([Gou20] 6.4.3: `v_p(K×) = (1/e)ℤ`, [BGR] 3.1.3).
For `x ∈ K` with `normAddValZ K x = k`, `‖x‖ = ‖π‖ ^ k` (L6.12), hence `‖algebraMap x‖ =
‖algebraMap π‖ ^ k`, i.e. `v_L (algebraMap x) = g_L ^ (e k)`, so `normAddValZ L (algebraMap x) =
e k` — [Kob84]'s `m = e · ord_p x`. Also `algebraMap π` is a normalising element of `L` (L5.3), and
for `y ∈ L` with `normAddValZ L y = d`, `(v_L y)^e = g_L^{de} = (v_L (algebraMap π))^d`, so
`normAddValQ L (algebraMap π) y = d / e`: `normAddValZ L = e · normAddValQ L (algebraMap π)`.
**Inheritance (§1.5.2).** For `K` complete and `L/K` algebraic, [BGR] 3.2.4/3: the minimal
polynomial `Xⁿ + ⋯ + a₀` of `x` has `|x|^n = |a₀|` (Mathlib: `‖x‖ = spectralNorm x =
‖a₀‖^{1/n}`). If `K` is commensurable at `π` and `x ≠ 0`, then `a₀ ≠ 0` and `|a₀|^k = |π|^m` for
some `k > 0`, so `|x|^{nk} = |algebraMap π|^m`: `L` is commensurable at `algebraMap π`. The
witnesses of an `x ∈ K` are witnesses of `algebraMap x` (same norms), so by the workhorse
`normAddValQ L (algebraMap π) (algebraMap x) = normAddValQ K π x`.
**Completion (§1.5.3).** In a valued field, every value of the completion is a value of the
field (Mathlib `Valued.exists_coe_eq_v`; [Gou20] Lemma 3.2.10/Prop. 6.8.7, [Kob84] III §4), and
`v (π : K̂) = v π`; so the commensurability witnesses of `K` serve for `K̂`.

### Shared quotes

> **Q9.1** [RM] §1.5.1: "For `L/K` an algebraic extension of a complete ultrametric normed field,
> normed by `spectralNorm.normedField`, prove `IsUltrametricDist L` and that the spectral norm
> extends the norm of `K`. Prove that `normAddVal L` restricts to `normAddVal K`."

> **Q9.2** [RM] §1.5.2: "**Commensurability is inherited.** If `NormedField.valuation` on `K` is
> `IsCommensurable` at `π`, so is the valuation of `L` at `algebraMap K L π`, and `normAddValQ L π`
> restricts to `normAddValQ K π`. The proof is from the definition of the spectral norm as a
> spectral value: `spectralNorm x ^ (n - i) = ‖aᵢ‖` for the index `i` realising the maximum over
> the coefficients of the minimal polynomial, so every value of `L` is commensurable with a value
> of `K`." (Route taken: the `i = 0` form `‖x‖ ^ n = ‖a₀‖`, which is Mathlib's
> `spectralNorm_eq_norm_coeff_zero_rpow` and [BGR] 3.2.4/3; same conclusion.)

> **Q9.3** [RM] §1.5.3: "**Completion preserves the value group.** For a rank-one valued field, the
> value group of the completion is the value group of the field, so `IsCommensurable` at `π`
> passes to the completion, and `normAddValQ` of the completion restricts to `normAddValQ` of the
> field."

> **Q9.4** [RM] §1.3.6: "**Finite extensions.** For `L/K` a finite extension of a complete discretely
> valued field, with `L` discretely valued under the spectral norm and ramification index
> `e(L/K)` — both cited from the local-fields-and-ramification roadmap — prove
> `normAddValZ L x = e(L/K) · normAddValZ K x` for `x ∈ K`, and identify `normAddValZ L` with
> `e(L/K)` times the `ℚ`-valued valuation of §1.4 normalised at a uniformiser of `K`."
> (Deviation D2 of `plan.md`: discreteness of `L` is a hypothesis and `e` is defined by
> `normAddValZ L (algebraMap K L π) = e`.)

> **Q9.5** [BGR] 3.2.4 Prop. 3, p. 140: "Let `K` be complete and let `q = X^m + a₁X^{m−1} + ⋯ + a_m
> ∈ K[X]` be irreducible. Then `σ(q) = |a_m|^{1/m}`; i.e., `|a_μ| ≤ |a_m|^{μ/m}` for all
> `μ = 1, …, m`." Proof: "Since `q` is the minimal polynomial of `θ₁, …, θ_m` over `K`, we have
> `|θ_μ| = σ(q)` for all `μ` by definition of the spectral norm. Since the spectral norm is a
> valuation on `L` by Theorem 2, the equation `a_m = (−1)^m ∏ θ_μ` yields `|a_m| = ∏ |θ_μ| =
> σ(q)^m`."

> **Q9.6** [BGR] 3.2.4 Thm 2, pp. 139–140: "Let `K` be complete with respect to the given valuation
> `| |`, and let `L` be an algebraic extension of `K`. Then the spectral norm on `L` is a valuation,
> and each power-multiplicative `K`-algebra norm on `L` coincides with this valuation. In
> particular, the spectral valuation is the unique valuation on `L` extending the valuation `| |`
> from `K`."

> **Q9.7** [Gou20] Def. 6.4.3, p. 193: "Let K/ℚ_p be a finite extension, and let e = e(K/ℚ_p) be
> the unique positive integer (dividing n = [K : ℚ_p]) defined by v_p(K×) = (1/e)ℤ. We call e the
> ramification index of K over ℚ_p." [BGR] 3.1.3 Prop. 2, p. 131: "For each valued ring `B`
> containing a valued subring `A` such that `|A − {0}|` is a group, we have `e(B/A) f(B/A) ≤
> rk_A B`."

> **Q9.8** [Gou20] p. 221 (PDFPAGE 224): "Recall that whenever we have a convergent sequence
> x_n → x ≠ 0 in a non-archimedean field, there exists an N such that |x_n| = |x| for n ≥ N (this
> is Lemma 3.2.10 …). This means that the set of possible absolute values in ℂ_p is exactly the
> same as in ℚ̄_p." [BGR] 1.5.1, p. 41: "The completion `(Â, | |^)` of a valued ring (resp. valued
> field) is a valued ring (resp. valued field)."

> **Q9.9** [Kob84] III §2, p. 61 (PDFPAGE 74): "We conclude that the norm of α equals the norm of
> each of its conjugates. But then the norm of N_{ℚ_p(α)/ℚ_p}(α), which is in ℚ_p, equals … =
> ‖α‖ⁿ. Thus ‖α‖ = |N_{ℚ_p(α)/ℚ_p}(α)|_p^{1/n}. So, concretely speaking, to find the p-adic norm of
> α, look at the monic irreducible polynomial satisfied by α. If it has degree n and constant term
> a_n, then the p-adic norm of α is the nth root of |a_n|_p."

### Leaves

- **L9.1** (leaf, Mathlib) `Extension.lean · Valued.isCommensurable_completion`. Source Q9.3, Q9.8.
  D: `constructor`; `val_pos`, `val_lt_one`: `Valued.valuedCompletion_apply π ▸ hπ.val_pos` etc.;
  `exists_zpow_eq x hx`: `obtain ⟨r, hr⟩ := Valued.exists_coe_eq_v x` (with `Valued.v x =
  extensionValuation x` by `rfl`), `hr : v x = v r`; `v r ≠ 0` from `hx`; `obtain ⟨m, n, hn, e⟩ :=
  hπ.exists_zpow_eq r this`; `⟨m, n, hn, by rw [hr, valuedCompletion_apply, e]⟩`.
  Attacks: [1] a value of the completion not attained on `K` would break this — Mathlib's lemma
  says there is none (nonarchimedean locally-constant norms, Q9.8) ✓; [2] `x = 0`: excluded by
  `hx` ✓; `x = (π : K̂)` ✓; [3] `Valued K Γ₀` for a *field* `K` is what `valuedCompletion` needs;
  no rank-one hypothesis needed — [RM]'s "rank-one valued field" is more than required ✓;
  [5] `Valued.exists_coe_eq_v`, `valuedCompletion_apply` ✓; the instance `Valued (Completion K) Γ₀`
  elaborates in the skeleton ✓. SURVIVED.
- **L9.2** (leaf, Mathlib) `Extension.lean · NormedField.normAddVal_algebraMap`. Source Q9.1 ("prove
  that `normAddVal L` restricts to `normAddVal K`"). D: `rcases eq_or_ne x 0 with rfl | hx`; zero:
  `map_zero`, `normAddVal_zero` twice; nonzero: `normAddVal_apply_of_ne_zero L (by simpa using hx)`,
  `normAddVal_apply_of_ne_zero K hx`, `norm_algebraMap'`.
  Attacks: [3] no completeness or algebraicity is needed (Q9.1 assumes both; the lemma holds for
  every normed `K`-algebra field — `norm_algebraMap'` only needs `NormOneClass L`) ✓;
  [2] `x = 1` ✓; [5] `norm_algebraMap'`, `(algebraMap K L).injective`/`map_ne_zero` ✓. SURVIVED.
- **L9.3** (leaf, project) `Extension.lean · NormedField.exists_normAddValZ_algebraMap_eq` — `e > 0`
  with `normAddValZ L (algebraMap π) = e`. Source Q9.4, Q9.7. D: `algebraMap π ≠ 0`; `d` from
  `WithTop.ne_top_iff_exists` (L6.11); `(addValZ_eq_iff _ _ d).mp` gives `v_L (algebraMap π) =
  ↑(generator ^ d)`; `v_L (algebraMap π) < 1` (`valuation_apply`, `norm_algebraMap'`, `hπ.val_lt_one`
  via `valuation_apply` on `K`); `generator < 1` (`generator_lt_one`); hence `0 < d`
  (`zpow_lt_one_iff_right_of_lt_one₀` on `Γ₀ˣ`-values coerced, or `Units.val_lt_val`); `⟨d.toNat,
  by omega, by rw [Int.toNat_of_nonneg hd.le]; exact hd⟩`.
  Attacks: [1] `e = 0` would mean `v_L (algebraMap π) = 1`, contradicting `‖π‖ < 1` ✓; [2] `L = K`:
  `e = 1` ✓; [3] both discreteness instances are used (`normAddValZ L`, `generator`) ✓; [5]
  `zpow_lt_one_iff_right_of_lt_one₀`, `Int.toNat_of_nonneg` — verified in the ticket name check.
  SURVIVED.
- **L9.4** (leaf, project) `Extension.lean · NormedField.normAddValZ_algebraMap` — **M4**, the
  ramification formula. Source Q9.4, [Kob84] Q5.4 ("`m = e · ord_p x`"), Q9.7. D: `rcases eq_or_ne
  x 0`; zero: both `⊤` (`WithTop.map_top`); nonzero: `k` with `normAddValZ K x = k`
  (`ne_top_iff_exists`), `‖x‖ = ‖π‖ ^ k` (L6.12), so `‖algebraMap x‖ = ‖algebraMap π‖ ^ k`
  (`norm_algebraMap'` twice); from `he` and `addValZ_eq_iff` on `L`: `v_L (algebraMap π) =
  ↑(generator_L ^ e)`; so `v_L (algebraMap x) = ↑(generator_L ^ (e * k))` (`valuation_apply`,
  `← NNReal.coe_inj`, `zpow_mul`, `Units.val_zpow_eq_zpow_val`); conclude `(addValZ_eq_iff _ _
  (e * k)).mpr`, `WithTop.map_coe`.
  Attacks: [1] without `he` the statement has no `e`; with `he` the integer `e` is forced
  (L9.3), so no inconsistency ✓; [2] `x = π`: `e * 1 = e` ✓ (`he` itself); `x = 1`: `0` ✓; [3] no
  finiteness, no completeness, no algebraicity: the argument only uses `‖algebraMap x‖ = ‖x‖` ✓
  (more general than Q9.4, which is for finite extensions); [4] Q9.4 "normAddValZ L x = e(L/K) ·
  normAddValZ K x for x ∈ K" ✓; [5] `zpow_mul`, `WithTop.map_coe` ✓. SURVIVED.
- **L9.5** (leaf, project) `Extension.lean · NormedField.isCommensurable_algebraMap_of_isRankOneDiscrete`.
  Source Q4.1 + Q9.4 (the normalising element of `L` used in the identification). D:
  `IsRankOneDiscrete.isCommensurable_of_lt_one _ h0 h1` (L5.3) with `h0 : v_L (algebraMap π) ≠ 0`
  (`map_ne_zero`, `hπ.ne_zero`) and `h1 : v_L (algebraMap π) < 1` (`valuation_apply`,
  `norm_algebraMap'`, `hπ.val_lt_one`).
  Attacks: [2] `L = K` ✓; [5] L5.3 ✓; [3] only discreteness of `L` and `0 < ‖π‖ < 1` enter ✓.
  SURVIVED.
- **L9.6** (leaf, project) `Extension.lean · NormedField.map_intCast_normAddValZ_eq_map_normAddValQ`
  — `Int.cast ∘ normAddValZ L = e · normAddValQ L (algebraMap π)`. Source Q9.4 (second sentence).
  D: `0 < e` from `he` as in L9.3; `rcases eq_or_ne y 0` (zero: both `⊤`); `d` with `normAddValZ L
  y = d`; `v_L y = ↑(g_L ^ d)` and `v_L (algebraMap π) = ↑(g_L ^ e)` (`addValZ_eq_iff`); so
  `v_L y ^ e = v_L (algebraMap π) ^ d` (`zpow_mul`, `mul_comm`); `addValQ_eq_of_zpow _ _ (v_L y ≠ 0)
  he_pos this : normAddValQ … y = ↑(d / e)`; finish with `WithTop.map_coe`, `WithTop.coe_inj`,
  `mul_div_cancel₀` (`(e : ℚ) ≠ 0`).
  Attacks: [1] for `e ≤ 0` the workhorse would not apply — but `he` forces `e > 0` (L9.3's
  argument, repeated inside) ✓; [2] `y = algebraMap π`: `e = e · 1` ✓; `y = 1`: `0 = e · 0` ✓;
  [3] the `IsCommensurable` instance is a hypothesis although derivable (L9.5) — `Prop`-class,
  all instances equal ✓; [5] `mul_div_cancel₀`, `WithTop.coe_inj` ✓. SURVIVED.
- **L9.7** (leaf, Mathlib) `Extension.lean · NormedField.norm_pow_natDegree_minpoly` — `‖x‖ ^ n =
  ‖a₀‖`. Source Q9.5 (BGR 3.2.4/3), Q9.9. D: `rw [NormedAlgebra.norm_eq_spectralNorm K x,
  spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow, one_div, Real.rpow_inv_natCast_pow (norm_nonneg
  _) (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x)).ne']`.
  Attacks: [1] for `K` not complete the norm of `L` need not be the spectral norm (two different
  extensions of a valuation) — `[CompleteSpace K]` is used by `NormedAlgebra.norm_eq_spectralNorm`
  ✓ (this is the D1 repair); [2] `x = 0`: `minpoly = X`, `n = 1`, `0 = 0` ✓; `x ∈ K`: `minpoly = X −
  x`, `‖x‖ = ‖−x‖` ✓; [3] `IsUltrametricDist K` is a hypothesis of Mathlib's lemma; `IsUltrametricDist
  L` is an unused section instance (cleanup may `omit` it) ✓; [4] Q9.5 is exactly `σ(q) =
  |a_m|^{1/m}` for the minimal polynomial; the roadmap's `i`-th coefficient form (Q9.2) is a
  different route to the same inheritance statement — recorded, not a drift of the *leaf* ✓;
  [5] `spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow`, `NormedAlgebra.norm_eq_spectralNorm`,
  `Real.rpow_inv_natCast_pow`, `minpoly.natDegree_pos` elaborate (`names_pre.lean`; the last two
  verified in the ticket name check). SURVIVED.
- **L9.8** (leaf, project) `Extension.lean · NormedField.isCommensurable_algebraMap` (instance) —
  **inheritance**. Source Q9.2, Q9.5, Q9.9. D: `constructor`; `val_pos`/`val_lt_one` via
  `valuation_apply`, `norm_algebraMap'`, `hπ.val_pos`/`val_lt_one`; `exists_zpow_eq x hx`: `x ≠ 0`;
  `a₀ := (minpoly K x).coeff 0 ≠ 0` (`minpoly.coeff_zero_ne_zero (Algebra.IsIntegral.isIntegral x)
  hx`); `⟨m, k, hk, e⟩ := hπ.exists_zpow_eq a₀ (by simpa using this)`; `n := natDegree`, `hn : 0 <
  n`; from L9.7, `‖x‖₊ ^ n = ‖a₀‖₊` (`NNReal.coe_inj`, `coe_pow`); then `‖x‖₊ ^ ((n : ℤ) * k) =
  ‖a₀‖₊ ^ k = ‖π‖₊ ^ m = ‖algebraMap π‖₊ ^ m` (`zpow_mul`, `zpow_natCast`, `nnnorm_algebraMap'`);
  witnesses `⟨m, n * k, mul_pos (Nat.cast_pos.mpr hn) hk, …⟩`.
  Attacks: [1] counterexample to the *unfixed* statement (no completeness): see D1 — with
  `[CompleteSpace K]` the Mathlib identification holds ✓; algebraicity: for transcendental `L`
  (e.g. `K(T)` with `‖T‖ = p^{√2}`, completed) the conclusion fails, and `[Algebra.IsAlgebraic K L]`
  is used through `minpoly`/L9.7 ✓; [2] `L = K` ✓; `x = algebraMap π`: `minpoly = X − π`, `a₀ = −π`,
  witnesses `(m, k) = (1, 1)`, `n = 1` ✓; [3] every hypothesis is used ✓; [4] Q9.2 verbatim ("so is
  the valuation of `L` at `algebraMap K L π`") ✓; [5] `minpoly.coeff_zero_ne_zero`,
  `nnnorm_algebraMap'` — verified in the ticket name check. SURVIVED.
- **L9.9** (leaf, project) `Extension.lean · NormedField.normAddValQ_algebraMap` — restriction of
  `normAddValQ`. Source Q9.2 ("restricts to `normAddValQ K π`"). D: `rcases eq_or_ne x 0` (zero:
  both `⊤`); `⟨m, n, hn, e⟩ := (IsCommensurable at K).exists_zpow_eq x (by simpa using hx)`; `e' :
  v_L (algebraMap x) ^ n = v_L (algebraMap π) ^ m` by `valuation_apply`, `nnnorm_algebraMap'`;
  `rw [normAddValQ, normAddValQ, addValQ_eq_of_zpow _ _ _ hn e', addValQ_eq_of_zpow _ _ _ hn e]`.
  Attacks: [2] `x = π`: `1 = 1` ✓; [5] L4.13 ✓; [3] completeness/algebraicity are needed only to
  *state* it (the instance on `L`) ✓. SURVIVED.

### Internal node R9 ([6])

Three independent sub-results (restriction, ramification, inheritance) plus the completion
lemma; the only composition is L9.6 = L9.4's technique + L4.13, attacked above. SURVIVED.

---

## Result R10 — the algebraic closure of `ℚ_p`, and `ℂ_p` (§1.5.4–§1.5.5, `PadicComplex.lean`)

### Plain-English proof (source: [RM] §1.5.4–§1.5.5; [Kob84] III §3–§4; [Gou20] 6.8.6–6.8.7)

`ℚ_p` is complete and commensurable at `p` (L7.9), so every algebraic ultrametric normed
`ℚ_p`-algebra field is commensurable at `p` (L9.8 with `algebraMap p = p`) — in particular
`PadicAlgCl p` ([Kob84] III §3: `|α|_p = |a_n|_p^{1/n}`, a rational power of `p`). `ℂ_[p]` is the
completion of `PadicAlgCl p`; Mathlib's `Valued.v` on `ℂ_[p]` is the extended valuation and equals
`‖·‖₊` (through `norm_eq_norm`, `RankOne.hom_eq_embedding`), so L9.1 transports commensurability
at `p` to `ℂ_[p]` ([Gou20] 6.8.7: "the image of ℂ_p× under v_p is ℚ"). Hence `normAddValQ ℂ_[p] p`
exists with `normAddValQ p = 1`; on `x ∈ ℚ_p` with `x.valuation = k`, `‖x‖ = p^{−k} = ‖p‖^k` so the
workhorse gives `k`, i.e. `Padic.addValuation x`; `‖x‖ = ‖p‖^q = p^{−q}` (L6.21). Every rational
`q = a/b` is attained: `ℂ_p` is algebraically closed, so `z^b = p^a` has a solution ([Kob84] III §4:
"let `p^r` denote any root of `x^b − p^a`"), with `normAddValQ z = a/b`; and no other values than
rationals and `⊤` occur, by the type.

### Shared quotes

> **Q10.1** [RM] §1.5.4: "**The algebraic closure of `ℚ_p`, and `ℂ_p`.** Prove `IsCommensurable` at
> `p` for `PadicAlgCl p` and for `ℂ_[p]`, so that `normAddValQ ℂ_[p] p : AddValuation ℂ_[p]
> (WithTop ℚ)` is defined with `normAddValQ ℂ_[p] p p = 1`, restricts to `Padic.addValuation` on
> `ℚ_p`, and satisfies `‖x‖ = p ^ (-(normAddValQ ℂ_[p] p x))`."

> **Q10.2** [RM] §1.5.5: "Prove the value group of `ℂ_[p]` is exactly `p^ℚ`: every rational occurs
> as a valuation, and nothing else does."

> **Q10.3** [Kob84] III §4, p. 72 (PDFPAGE 85): "Finally, an arbitrary nonzero x ∈ Ω can be written
> as a fractional power of p times an element x₁ ∈ Ω of absolute value 1. Namely, if ord_p x = r =
> a/b (see Exercise 1 below), then let p^r denote any root of x^b − p^a = 0." Exercise 1, p. 73:
> "Prove that the possible values of | |_p on ℚ̄_p is the set of all rational powers of p (in the
> positive real numbers). What about on Ω? … What is the set of all possible values of ord_p on
> Ω?"

> **Q10.4** [Gou20] Prop. 6.8.7, p. 221 (PDFPAGE 224): "If x ∈ ℂ_p, x ≠ 0, then there exists a
> rational number v ∈ ℚ such that |x| = p^{−v}. In other words, the p-adic valuation v_p extends to
> ℂ_p, and the image of ℂ_p× under v_p is ℚ."

> **Q10.5** [Mathlib] `PadicComplex.valued : Valued ℂ_[p] ℝ≥0 := Valued.valuedCompletion`,
> `PadicComplex.norm_eq_norm (x : ℂ_[p]) : ‖x‖ = Valued.v.norm x`, `PadicComplex.RankOne.hom_eq_embedding`,
> `PadicComplex.norm_extends' (x : ℚ_[p]) : ‖(x : ℂ_[p])‖ = ‖x‖`, `PadicComplex.coe_natCast`,
> `PadicComplex.isAlgClosed`; `PadicAlgCl.valued := NormedField.toValued`, `PadicAlgCl.valuation_def :
> Valued.v x = ‖x‖₊` (`rfl`).

### Leaves

- **L10.1** (leaf, project) `PadicComplex.lean · NormedField.isCommensurable_natCast_prime`
  (instance). Source Q10.1 (first half) via Q9.2. D: `have := isCommensurable_algebraMap (K :=
  ℚ_[p]) (L := L) (p : ℚ_[p])` (L9.8, instances `Padic.isCommensurable_p`, `CompleteSpace ℚ_[p]`);
  `rwa [map_natCast] at this`.
  Attacks: [3] `CompleteSpace ℚ_[p]` is a Mathlib instance ✓; `[Algebra.IsAlgebraic ℚ_[p] L]` is
  necessary (D1 counterexample) ✓; [2] `L = ℚ_[p]` ✓; [5] `map_natCast` ✓. SURVIVED.
- **L10.2** (leaf, project) `PadicComplex.lean · PadicAlgCl.isCommensurable_p`. Source Q10.1. D:
  `inferInstance` (L10.1; `PadicAlgCl.normedAlgebra`, `PadicAlgCl.isAlgebraic`,
  `PadicAlgCl.nontriviallyNormedField`, `PadicAlgCl.isUltrametricDist`).
  Attacks: [5] the four instances exist in `Mathlib/NumberTheory/Padics/Complex.lean` (lines
  59–122) ✓; [2] n/a. SURVIVED.
- **L10.3** (leaf, Mathlib) `PadicComplex.lean · PadicComplex.valuation_eq_nnnorm` — `Valued.v x =
  ‖x‖₊`. Source Q10.5 (the seam). D: `rw [← NNReal.coe_inj, coe_nnnorm, norm_eq_norm x,
  Valuation.norm_def, RankOne.hom_eq_embedding, Valuation.embedding_restrict]`.
  Attacks: [1] the `Valued` structure on `ℂ_[p]` could a priori differ from `NormedField.toValued`;
  Mathlib proves `norm_eq_norm` precisely to close this, and `hom = embedding` makes `Valued.v.norm x
  = (Valued.v x : ℝ)` ✓; [2] `x = 0` ✓; [5] names ✓ (`names_pre.lean`). SURVIVED.
- **L10.4** (leaf, project) `PadicComplex.lean · PadicComplex.normedField_valuation_eq`. D:
  `Valuation.ext fun x ↦ by rw [valuation_apply, valuation_eq_nnnorm]`. SURVIVED ([5] L10.3 ✓).
- **L10.5** (leaf, project) `PadicComplex.lean · PadicComplex.isCommensurable_p` (instance) — **ℂ_p
  is commensurable at `p`**. Source Q10.1, Q10.4, Q9.8. D: `have h₀ : (Valued.v : Valuation
  (PadicAlgCl p) ℝ≥0).IsCommensurable (p : PadicAlgCl p) := PadicAlgCl.isCommensurable_p`
  (`Valued.v = NormedField.valuation` by `PadicAlgCl.valuation_def`/`rfl`); `have h₁ :=
  Valued.isCommensurable_completion (K := PadicAlgCl p) (p : PadicAlgCl p)` (L9.1); `rw
  [normedField_valuation_eq]`; `simpa [PadicComplex.coe_natCast] using h₁` (the element
  `((p : PadicAlgCl p) : ℂ_[p]) = (p : ℂ_[p])`).
  Attacks: [1] `ℂ_p` is not algebraic over `ℚ_p`, so L9.8 does not apply directly — the route is
  the completion lemma, as [RM] §1.5.3 prescribes ✓; [2] n/a; [3] no new hypothesis ✓;
  [4] Q10.1 "for `ℂ_[p]`" ✓; [5] `PadicComplex.coe_natCast`, `valuation_extends` ✓; the
  `UniformSpace.Completion (PadicAlgCl p)` of L9.1 is `ℂ_[p]` by definition (`abbrev PadicComplex`)
  ✓. SURVIVED.
- **L10.6** (leaf, project) `PadicComplex.lean · PadicComplex.normAddValQ_p` — `normAddValQ ℂ_[p] p p
  = 1`. Source Q10.1. D: `normAddValQ_self _ _` (L6.19). SURVIVED.
- **L10.7** (leaf, project) `PadicComplex.lean · PadicComplex.normAddValQ_algebraMap_padic` —
  restriction to `ℚ_p` is `Padic.addValuation`. Source Q10.1 ("restricts to `Padic.addValuation`
  on `ℚ_p`"). D: `rcases eq_or_ne x 0` (zero: `map_zero`, `AddValuation.map_zero`, `WithTop.map_top`);
  `k := x.valuation`; `Padic.addValuation.apply hx`, `WithTop.map_coe`; `normAddValQ_eq_of_zpow`-form:
  `addValQ_eq_of_zpow _ _ (v (algebraMap x) ≠ 0) one_pos` with `v (algebraMap x) ^ 1 = v p ^ k`:
  `‖algebraMap x‖₊ = ‖x‖₊ = ‖p‖₊ ^ k` (`norm_extends'`/`norm_algebraMap'`, `Padic.nnnorm_p_zpow_valuation`,
  `nnnorm_natCast`-style `‖(p : ℂ_[p])‖₊ = ‖(p : ℚ_[p])‖₊` via `PadicComplex.nnnorm_extends'`);
  `norm_num` (`k / 1 = k`).
  Attacks: [2] `x = p`: `1 = ↑1` ✓ (L10.6); `x = 1`: `0` ✓; [5] `Padic.addValuation.apply`,
  `PadicComplex.nnnorm_extends'` ✓. SURVIVED.
- **L10.8** (leaf, project) `PadicComplex.lean · PadicComplex.norm_eq_rpow_neg_normAddValQ` — `‖x‖
  = p^{−q}`. Source Q10.1, Q10.4. D: `rw [norm_eq_norm_rpow_normAddValQ _ _ hq]` (L6.21); `‖(p :
  ℂ_[p])‖ = (p : ℝ)⁻¹` (`norm_extends'`, `Padic.norm_p`, `map_natCast`); `Real.inv_rpow (by
  positivity)`, `← Real.rpow_neg (by positivity)`.
  Attacks: [2] `q = 1`: `p⁻¹` ✓; [5] `Real.inv_rpow`, `Real.rpow_neg` ✓. SURVIVED.
- **L10.9** (leaf, project) `PadicComplex.lean · PadicComplex.exists_normAddValQ_eq` — every
  rational occurs. Source Q10.2, Q10.3. D: `a := q.num`, `b := q.den`, `hb : 0 < b := q.den_pos`;
  `⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((p : ℂ_[p]) ^ a) hb` (`z ^ b = p ^ a`); `z ≠ 0`
  (`pow_ne_zero`-contrapositive: `p ^ a ≠ 0` as `(p : ℂ_[p]) ≠ 0`); `v z ^ (b : ℤ) = v p ^ a`
  (`map_pow`, `map_zpow₀`, `zpow_natCast`, `hz`); `addValQ_eq_of_zpow _ _ hz0 (by exact_mod_cast hb)
  this : normAddValQ z = ↑(a / b)`; `Rat.num_div_den q`.
  Attacks: [1] `ℂ_p` algebraically closed is Mathlib's `PadicComplex.isAlgClosed` ✓; [2] `q = 0`:
  `z ^ 1 = p ^ 0 = 1`, `z = 1`, value `0` ✓; `q = 1`: `z = p` ✓; negative `q` ✓ (zpow); [5]
  `IsAlgClosed.exists_pow_nat_eq`, `Rat.num_div_den`, `Rat.den_pos` — verified in the ticket name
  check. SURVIVED.
- **L10.10** (leaf, project) `PadicComplex.lean · PadicComplex.range_normAddValQ` — **M5**,
  `range = insert ⊤ (range (↑))`. Source Q10.2 ("every rational occurs … and nothing else does").
  D: `Set.ext fun y ↦ ?_`; `→`: `⟨x, rfl⟩`; `rcases eq_or_ne x 0`: `⊤` (`normAddValQ_zero`), else
  `WithTop.ne_top_iff_exists` (L6.18) gives `q` with `↑q = normAddValQ x`; `←`: `y = ⊤`: `⟨0,
  normAddValQ_zero _ _⟩`; `y = ↑q`: L10.9.
  Attacks: [2] both clauses exercised ✓; [3] none; [5] `Set.mem_insert_iff`, `Set.mem_range` ✓.
  SURVIVED.

### Internal node R10 ([6])

The chain `ℚ_p → PadicAlgCl p → ℂ_p` uses L9.8 then L9.1 with the seam L10.3/L10.4 between
`Valued.v` and `NormedField.valuation`; L10.6–L10.10 are R6 at `K = ℂ_[p]`, `π = p`. SURVIVED.

---

## Result R11 — the roadmap's examples (`Examples.lean`)

### Plain-English proof (source: [RM] Layer 1 Examples; [Kob84] I §2; [Gou20] Problems 242–244)

`normAddValZ p = 1` is L6.13 at the uniformiser `p`; `normAddValZ (1/p²) = −2` is `Padic.addValuation`
at `(p²)⁻¹` through L7.11 (Mathlib's `valuation_inv`, `valuation_pow`, `valuation_p`);
`normAddVal ℚ_[p] = log p · normAddValZ` is L6.16 with `−log ‖p‖ = log p`. In any algebraic
ultrametric normed `ℚ_p`-algebra field `L`, `s² = p` gives `‖s‖² = ‖p‖`, so the workhorse read off
norms gives `normAddValQ L p s = 1/2`; if `L` is discretely valued with `normAddValZ L s = 1`,
multiplicativity gives `normAddValZ L p = 2·1 = 2`. In `ℂ_p`, `x³ = p` gives `normAddValQ x = 1/3`.
For Laurent series, `addValZ (X ^ n) = n · addValZ X = n`.

### Shared quote

> **Q11.1** [RM] Layer 1, Examples: "`ℚ_p`: `normAddValZ p = 1`, `normAddValZ (1/p²) = -2`,
> `‖x‖ = p ^ (-v x)`, and `normAddVal ℚ_[p]` is `log p` times `normAddValZ`. `ℚ_p(√p)`:
> `normAddValZ` of the extension gives `√p ↦ 1` and `p ↦ 2`, while `normAddValQ` normalised at `p`
> gives `√p ↦ 1/2`. `ℂ_p` at `π = p`: `p^{1/3} ↦ 1/3`. `𝔽_q⸨t⸩` at `t`: `normAddValZ` is the order of
> vanishing at `t`."

### Leaves

- **L11.1** (leaf, project) `Examples.lean · NormedField.normAddValZ_padic_p`. D:
  `normAddValZ_isUniformizer _ Padic.isUniformizer_p` (L6.13, L7.8). SURVIVED ([5] ✓).
- **L11.2** (leaf, project) `Examples.lean · NormedField.normAddValZ_padic_inv_p_sq` — `= −2`. D:
  `rw [normAddValZ_padic_apply, Padic.addValuation.apply (by positivity-style: inv_ne_zero
  (pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero))), Padic.valuation_inv, Padic.valuation_pow,
  Padic.valuation_p]`; `norm_num`.
  Attacks: [2] n/a (a computation); [5] `Padic.valuation_inv`, `Padic.valuation_pow` elaborate
  (`names_pre.lean`) ✓; [4] Q11.1 "`normAddValZ (1/p²) = -2`" ✓. SURVIVED.
- **L11.3** (leaf, project) `Examples.lean · NormedField.normAddVal_padic` — `log p` times
  `normAddValZ`. D: `normAddVal_eq_map_normAddValZ ℚ_[p] Padic.isUniformizer_p x` (L6.16);
  `congr`/`funext`: `−Real.log ‖(p : ℚ_[p])‖ = Real.log p` by `Padic.norm_p`, `Real.log_inv`,
  `neg_neg`.
  Attacks: [2] `x = p`: `log p = 1 · log p` ✓; [5] `Real.log_inv` ✓. SURVIVED.
- **L11.4** (leaf, project) `Examples.lean · NormedField.normAddValQ_of_sq_eq_prime` — `1/2`. D:
  `normAddValQ_eq_of_pow_eq_pow L p (s ≠ 0) two_pos (m := 1)` with `‖s‖ ^ 2 = ‖s ^ 2‖ = ‖(p : L)‖ =
  ‖p‖ ^ 1` (`norm_pow`, `hs`, `pow_one`); `s ≠ 0` since `s ^ 2 = p ≠ 0` (`(p : L) = algebraMap ℚ_[p] L
  p` by `map_natCast`, `map_ne_zero`, `Nat.cast_ne_zero`); `norm_num`.
  Attacks: [2] `L = ℚ_[p](√p)` is the intended instance; the statement holds in any `L` with
  such an `s` ✓; [3] the instance `isCommensurable_natCast_prime` supplies commensurability ✓;
  [5] `norm_pow` ✓. SURVIVED.
- **L11.5** (leaf, project) `Examples.lean · NormedField.normAddValZ_prime_of_sq_eq_prime` —
  `normAddValZ L p = 2` from `normAddValZ L s = 1`. D: `rw [← hs, AddValuation.map_pow, h1,
  two_nsmul, one_add_one_eq_two]`.
  Attacks: [3] without `h1` the conclusion is false (e.g. an unramified `L` with `s ∉ L` cannot
  occur, but `s` a uniformiser of a ramified `L` with `normAddValZ L s = 1` is what Q11.1 means
  by "`√p ↦ 1`") ✓; [2] n/a; [5] `two_nsmul`, `one_add_one_eq_two` ✓. SURVIVED.
- **L11.6** (leaf, project) `Examples.lean · NormedField.normAddValQ_padicComplex_of_pow_three` —
  `1/3`. D: as L11.4 with `n = 3`, `norm_pow`, `norm_extends'`-free since `‖x ^ 3‖ = ‖(p : ℂ_[p])‖`
  directly; `x ≠ 0` from `(p : ℂ_[p]) ≠ 0` (`Nat.cast_ne_zero`, `CharZero ℂ_[p]`).
  Attacks: [2] ✓; [5] `PadicComplex.charZero` ✓. SURVIVED.
- **L11.7** (leaf, project) `Examples.lean · LaurentSeries.addValZ_X_pow` — `n`. D: `rw
  [AddValuation.map_pow, addValZ_X, nsmul_one]`? — `n • (1 : WithTop ℤ) = ((n : ℤ) : WithTop ℤ)`:
  `nsmul_eq_mul`, `mul_one`, `Nat.cast`-coherence (`WithTop.coe_natCast`), spelled out in the
  ticket.
  Attacks: [2] `n = 0`: `addValZ 1 = 0` ✓; [5] `AddValuation.map_pow` ✓. SURVIVED.

---

## Confidence gate (Step 5)

1. **Every leaf discharged**: 144 declarations; each leaf above names its Mathlib lemmas (verified
   by elaboration) or the project leaf it reduces to. No API gap is open: the only new
   mathematical content beyond [SRC] (L2.6, L4.19, L5.3, L8.1–L8.7, L9.1–L9.9, L10.1–L10.10, the
   examples) decomposes to Mathlib lemmas named above.
2. **Skeleton compiles**: `lake build PhD.TauCeti.Code.NewtonPolygons.AddVal.Examples`, 2884 jobs,
   `sorry` warnings only; `scratch/signatures.txt` has 143 elaborated signatures, 0 errors.
3. **Verbatim quotes + Lean ↔ source match**: every leaf cites a shared quote Q*.* (verbatim from
   [RM]/[Kob84]/[Gou20]/[BGR]/[PR]/[Mathlib]) and states the match in its D/attack lines.
4. **Adversarial pass**: every leaf has an attacks block with ≥ 3 categories; every internal node
   has a composition attack; one defect (D1) found and repaired.
5. **Prior-B2 log**: consulted (table above); no name match; the dropped-variable shape caught D1.
6. **Mirrors the source**: the roadmap's clause structure is the tree (R1 = §1.1, R2–R4 = §1.4 with
   its group-theoretic substrate, R5 = §1.3.1–3, R6 = §1.2.2–3/§1.3.4/§1.4.6, R7–R8 = §1.3.5,
   R9 = §1.3.6/§1.5.1–3, R10 = §1.5.4–5, R11 = Examples); where the roadmap defers to a source
   ([Kob84], [Gou20], [BGR]) the quotes are from that source. Sizing: every leaf is a one-paragraph
   argument in its source and a ≤ 15-line Lean proof in [SRC] where ported; the tickets' sketches
   are grounded in those.
7. **Single-conclusion**: checked above (only shared-witness existentials).

No REVIEW-PENDING leaves (the ChatGPT MCP server was unavailable; no step needed it — every
source gap was closed by [Kob84]/[Gou20]/[BGR]).

## Feasibility

The layer is a port of a sorry-free development ([SRC], §1.1–§1.4 and `ℚ_p`) with the [PR] names,
plus five new pieces, each discharged from named Mathlib lemmas: the uniqueness statement §1.4.4
(L2.6/L4.19, elementary), discreteness/uniformiser/order for Laurent series (L8.1–L8.7, from
Mathlib's `LaurentSeries` valuation API), the ramification formula §1.3.6 (L9.3–L9.6, from norm
extension and the generator characterisation), inheritance of commensurability §1.5.2 (L9.7–L9.9,
from Mathlib's `NormedAlgebra.norm_eq_spectralNorm` and `spectralNorm_eq_norm_coeff_zero_rpow`) and
`ℂ_p` (L9.1 + L10.*, from `Valued.exists_coe_eq_v` and `IsAlgClosed.exists_pow_nat_eq`). The
recorded deviations D1–D6 of `plan.md` are statement-level and visible to the roadmap's reader.
Expected size: 52 proof tickets, none longer than a working session.
