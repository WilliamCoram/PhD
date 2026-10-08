
# ---------------------------------------------------------------- Affinoid/PowerBounded.lean
t(id='T047', title='The subring `Å = {|f|_sup ≤ 1}` and its ideal `Ǎ = {|f|_sup < 1}` (BGR 6.2.3/1–2, 1.2.5/2, 1.2.5/7)', file=APB,
  deps='T003', par='yes (with T020–T046)', typ='defs+lemmas', leaves='L8.1–L8.4',
  decls=[(APB,'powerBounded'),(APB,'topologicallyNilpotent'),(APB,'topologicallyNilpotent_isRadical'),(APB,'algebraMap_mem_powerBounded')],
  sketch="""`powerBounded`: `mul_mem'`: `|fg| ≤ |f||g| ≤ 1` (`mul_le_one'`); `one_mem'`: `supSeminorm_one_le`; `add_mem'`:
`add_le_max` + `max_le`; `zero_mem'`: `supSeminorm_zero`; `neg_mem'`: `supSeminorm_neg`. `topologicallyNilpotent`:
`add_mem'`: `max_lt`; `zero_mem'`: `0 < 1`; `smul_mem'`: `|c • f| = |c f| ≤ |c| |f| < 1` (`mul_lt_one_of_nonneg_of_lt_one_right`).
`isRadical`: `Ideal.IsRadical` = `∀ f n, f^n ∈ I → f ∈ I`-type (`Ideal.isRadical_iff_pow_one_lt`? use
`Ideal.IsRadical` unfolding to `I.radical ≤ I`, `Ideal.mem_radical_iff`): `|f^n|_sup = |f|^n < 1` with `n ≠ 0` gives
`|f| < 1` (`pow_lt_one_iff_of_nonneg`). `algebraMap_mem`: `|algebraMap c|_sup = |c • 1| = ‖c‖ |1| ≤ ‖c‖ ≤ 1`
(`Algebra.algebraMap_eq_smul_one`, `supSeminorm_smul`, `supSeminorm_one_le`).""",
  mathlib="""`Subring`, `Ideal` structure fields, `mul_le_one'`, `max_lt`, `mul_lt_one_of_nonneg_of_lt_one_right`, `Ideal.IsRadical`,
`Ideal.mem_radical_iff`, `pow_lt_one_iff_of_nonneg`, `Algebra.algebraMap_eq_smul_one`.""",
  sources="""BGR 6.2.3/1–2 and 6.2.3/4 (`bgr-6.2-6.3.1.md`): "`Ã = {f ∈ A; |f|_sup ≤ 1}/{f ∈ A; |f|_sup < 1}`"; BGR 1.2.5/2
(`bgr-3.7.md:157`): "The set `Å` is a subring of `A` and `Ǎ` is an ideal in `Å`"; BGR 1.2.5/7 (`bgr-1.3-1.5.md`): "The rings
`Ã` and `~A` are reduced".""",
  gen="""Defined for any `[HasSupSeminorm K A]` (no norm, no affinoid hypothesis): roadmap §2.3.1 "`Å` form a subring independent
of the norm".""")

t(id='T048', title='Power-bounded ⇔ `|f|_sup ≤ 1` (BGR 6.2.3/1; Bosch 1.4/16) — first half of M3', file=APB,
  deps='T009, T024, T046, T047', par='no', typ='theorem', leaves='L8.5–L8.6',
  decls=[(APB,'isPowerBounded_iff_supSeminorm_le_one'),(APB,'isPowerBounded_iff_mem_powerBounded')],
  sketch="""`→`: T024 `IsPowerBounded.supSeminorm_le_one` (instance from `hA.hasSupSeminorm`). `←` (BGR's proof): presentation
`α : Tₙ →ₐ[K] A` surjective (finite: `RingHom.Finite.of_surjective`), continuous (Layer 1 `hA.continuous_presentation`),
so `∃ C, ∀ g, ‖α g‖ ≤ C ‖g‖` (`ContinuousLinearMap.exists_bound`/Layer 1 `exists_forall_norm_le_mul_of_continuous`). T046
gives monic `q ∈ Tₙ[X]` with `q.eval₂ α f = 0` and `σ(q) = |f|_sup ≤ 1`, so every coefficient has `|t_i|_sup = ‖t_i‖ ≤ 1`
(T009 `coeff_le_pow`, `supSeminorm_eq_norm`). Induction as in T027: `f^j = ∑_{i<n} α (c_i) f^i` with `‖c_i‖ ≤ 1`
(the coefficients stay in the unit ball of `Tₙ`: `norm_add_le_max`/ultrametric, `norm_mul_le`, `NormOneClass`), hence
`‖f^j‖ ≤ max_i ‖α c_i‖ ‖f^i‖ ≤ C max_{i<n} ‖f^i‖` for all `j`: `isPowerBounded_of_norm_pow_le`. `iff_mem`: rewrite with
`mem_powerBounded`.""",
  mathlib="""`PowerBounded.isPowerBounded_of_norm_pow_le`, `RingHom.Finite.of_surjective`, `IsUltrametricDist.norm_add_le_max`,
`norm_mul_le`, `IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty`; Layer 1 `IsAffinoidAlgebra.continuous_presentation`,
`MvPowerSeries.Restricted.exists_forall_norm_le_mul_of_continuous`.""",
  sources="""BGR 6.2.3/1 and proof (`bgr-6.2-6.3.1.md`): "We have only to show that `f` is power-bounded if `|f|_sup ≤ 1`. Choose
a finite homomorphism `φ: T_d → A` (for example, an epimorphism). Then due to Proposition 6.2.2/4, there is an integral
equation … We have `t₁, …, tₙ ∈ T̊_d` if `|f|_sup ≤ 1`. Induction on `ν` gives then `f^{n+ν} ∈ Σ φ(T̊_d) f^i`. Since
`φ(T̊_d)` is bounded in `A`, we see that `Σ φ(T̊_d) f^i` is bounded."; Bosch 1.4/16.""",
  gen="""Any complete `K`-algebra norm on the affinoid `A` (roadmap convention 3); no domain hypothesis (BGR's direct proof,
unlike the 3.8.2/6 route).""")

t(id='T049', title='Topologically nilpotent ⇔ `|f|_sup < 1` ⇔ `|f(x)| < 1` for all `x` (BGR 6.2.3/2; Bosch 1.4/17)', file=APB,
  deps='T042, T043, T048', par='no', typ='lemmas', leaves='L8.7–L8.9',
  decls=[(APB,'isTopologicallyNilpotent_iff_supSeminorm_lt_one'),(APB,'isTopologicallyNilpotent_iff_forall_evalNorm_lt_one'),
         (APB,'isTopologicallyNilpotent_iff_mem_topologicallyNilpotent')],
  sketch="""`iff_supSeminorm_lt_one`: `→`: `‖f^n‖ → 0` gives `‖f^m‖ < 1` for some `m ≥ 1`, and `|f|_sup^m = |f^m|_sup ≤ ‖f^m‖ < 1`
so `|f|_sup < 1` (`pow_lt_one_iff_of_nonneg`). `←`: if `|f|_sup = 0` then `f` is nilpotent (T044) hence topologically
nilpotent (`IsNilpotent.isTopologicallyNilpotent`?/eventually `0`). Else T043: `c, m` with `|c • f^m|_sup = 1`;
`‖c‖ > 1` since `|f|_sup^m < 1` (`‖c‖ = 1/|f|_sup^m`); `c • f^m` is power-bounded (T048), so `‖(c • f^m)^k‖ ≤ M`,
i.e. `‖f^{mk}‖ ≤ M ‖c‖^{-k} → 0`: `f^m` is topologically nilpotent, hence `f` (BGR 1.2.5/7 argument as in T027:
`n = mq + s`). `iff_forall_evalNorm_lt_one`: `|f|_sup < 1 ↔ ∀ x, |f(x)| < 1` by M2 (T042: the sup is attained; `←`
needs `[Nontrivial A]`) and `evalNorm_le_supSeminorm`. `iff_mem`: rewrite `mem_topologicallyNilpotent`.""",
  mathlib="""`pow_lt_one_iff_of_nonneg`, `tendsto_pow_atTop_nhds_zero_of_lt_one`, `Metric.tendsto_atTop`, `norm_smul`, `norm_pow`,
`IsTopologicallyNilpotent` (Mathlib: `Tendsto (fun n ↦ x ^ n) atTop (𝓝 0)`), `Nat.div_add_mod`, `squeeze_zero`.""",
  sources="""BGR 6.2.3/2 and proof (`bgr-6.2-6.3.1.md`): "Statements (ii) and (iii) are equivalent due to the Maximum Modulus
Principle. Furthermore, statement (i) implies statement (iii), since any Banach norm on `A` dominates `| |_sup` and since
`| |_sup` is power-multiplicative. In order to verify the opposite direction, assume `|f|_sup < 1`. Then there exist a
constant `c ∈ k`, `|c| > 1`, and an integer `m > 0` such that `|cf^m|_sup ≤ 1` … We have `cf^m ∈ Å` by Proposition 1.
Therefore `f^m ∈ c⁻¹Å ⊂ Ǎ`, and we see that `f^m` and hence also `f` are topologically nilpotent."; Bosch 1.4/17.""",
  gen="""Three single-conclusion lemmas (BGR's (i)⇔(ii)⇔(iii) split per the statement-splitting rule).""")

t(id='T050', title='M3 — the spectral radius formula `|f|_sup = inf ‖fⁱ‖^{1/i}` (BGR 6.2.3/3)', file=APB, deps='T024, T043, T048',
  par='no', typ='theorem', leaves='L8.10', milestone='M3 ([RM] §2.3.1 + §2.3.3, with T048)', decls=[(APB,'supSeminorm_eq_smoothingFun')],
  sketch="""`≤`: T024 `supSeminorm_le_smoothingFun`. `≥` (indirect, BGR): suppose `|f|_sup < μ'(f) := smoothingFun f`. If
`|f|_sup = 0`: `f` nilpotent (T044), so `f^N = 0` and `μ'(f) ≤ ‖f^N‖^{1/N} = 0` (`smoothingFun_le`), contradiction.
Else T043: `c, m` with `|c • f^m|_sup = 1`; `g := c • f^m` has `μ'(g) = ‖c‖ μ'(f)^m`?? — `smoothingFun` is
power-multiplicative (`isPowMul_smoothingFun`) and `c • ·` is multiplicative for the norm (`norm_smul`), so
`μ'(c • f^m) = ‖c‖ μ'(f)^m` (`smoothingFun_of_map_mul_eq_mul`/`smoothingFun_apply_of_map_mul_eq_mul` for the constant
`algebraMap c`, which is norm-multiplicative in a `NormedAlgebra` + `NormOneClass`: `norm_algebraMap'`), while
`|g|_sup = ‖c‖ |f|_sup^m = 1`; hence `μ'(g) > 1 = |g|_sup`, so `‖g^i‖ ≥ μ'(g)^i → ∞` (`smoothingFun_le`:
`μ'(g) ≤ ‖g^i‖^{1/i}`; `tendsto_pow_atTop_atTop_of_one_lt`), i.e. `g` is not power-bounded
(`IsPowerBounded.exists_norm_pow_le`), contradicting T048 (`|g|_sup ≤ 1`).""",
  mathlib="""`smoothingFun_le`, `isPowMul_smoothingFun`, `smoothingFun_apply_of_map_mul_eq_mul`, `norm_algebraMap'`, `norm_smul`,
`tendsto_pow_atTop_atTop_of_one_lt`, `PowerBounded.IsPowerBounded.exists_norm_pow_le`; T044 for nilpotents.""",
  sources="""BGR 6.2.3/3 and proof (`bgr-6.2-6.3.1.md`): "Define `|f|' := inf |f^i|^{1/i} … it follows from Corollary 3.8.2/2
that `|f|_sup ≤ |f|'` … Assume that `|f|_sup < |f|'` for some `f ∈ A`. Proposition 6.2.1/4 (ii) allows us to assume
`|f|_sup = 1`, and hence `|f|' > 1`. This implies `|f^i| ≥ |f|'^i → ∞`, and therefore `f` cannot be power-bounded,
in contradiction to Proposition 1."; [RM] §2.3.3 ("the right-hand side is Mathlib's `smoothingSeminorm`").""",
  gen="""Any complete `K`-algebra norm on the affinoid `A`; `smoothingFun (SeminormedRing.toRingSeminorm A)` is Mathlib's
`inf_i ‖fⁱ‖^{1/i}`.""")

t(id='T051', title='`|·|_sup` is 1-Lipschitz; `Å` is open and closed; `Ǎ` is open (§2.4.3)', file=APB, deps='T003, T038',
  par='yes (with T052)', typ='lemmas', leaves='L8.11–L8.14',
  decls=[(APB,'lipschitzWith_supSeminorm'),(APB,'isClosed_powerBounded'),(APB,'isOpen_powerBounded'),(APB,'isOpen_setOf_supSeminorm_lt_one')],
  sketch="""`lipschitzWith`: `LipschitzWith.of_dist_le_mul`/`LipschitzWith.of_le_add`: `|f|_sup ≤ max (|f-g|_sup) (|g|_sup) ≤
|f - g|_sup + |g|_sup ≤ ‖f - g‖ + |g|_sup` (nonarchimedean, `f = (f - g) + g`, Layer 0 `supSeminorm_le_norm`) and symmetric;
`Real.dist_eq`, `abs_sub_le_iff`. `isClosed`: `{f | |f|_sup ≤ 1} = (supSeminorm K) ⁻¹' Iic 1`, closed by continuity
(`LipschitzWith.continuous`, `isClosed_Iic`). `isOpen_setOf_lt`: preimage of `Iio 1`. `isOpen_powerBounded`:
`Metric.ball 0 1 ⊆ Å` (`|f|_sup ≤ ‖f‖ < 1`), so `Å` (an `AddSubgroup`: `(powerBounded K A).toAddSubgroup`) contains a
neighbourhood of `0`, hence is open (`AddSubgroup.isOpen_of_mem_nhds`).""",
  mathlib="""`LipschitzWith.of_le_add`, `LipschitzWith.continuous`, `isClosed_Iic`, `isOpen_Iio`, `IsClosed.preimage`,
`AddSubgroup.isOpen_of_mem_nhds`, `Metric.ball_mem_nhds`, `Subring.toAddSubgroup`.""",
  sources="""[RM] §2.4.3 ("`Å` is the unit ball of a norm defining the topology … `Ǎ` is its open unit ball"); BGR 1.2.5/2
(`bgr-3.7.md:157`): "The subring `Å` is open and closed, `Ǎ` is open" (for a power-multiplicative norm; here through
`|·|_sup ≤ ‖·‖`).""",
  gen="""No reducedness needed (only `|·|_sup ≤ ‖·‖`); stated for any complete `K`-algebra norm on an affinoid `A`.""")

t(id='T052', title='Uniformity in norm form: `Å` bounded ⇔ `|·|_sup` equivalent to the norm; bounded `Å` forces reduced (§2.3.5)',
  file=APB, deps='T043, T044, T048', par='no', typ='lemmas', leaves='L8.15–L8.16',
  decls=[(APB,'exists_norm_le_mul_supSeminorm_iff_isBounded_powerBounded'),(APB,'isReduced_of_isBounded_powerBounded')],
  sketch="""`→`: `‖f‖ ≤ C |f|_sup ≤ C` on `Å`: PFA `TopologicalRing.isBounded_of_forall_norm_le`. `←` (BGR p. 181): PFA
`IsBounded.exists_norm_le_of_normedAlgebra` gives `M` with `‖g‖ ≤ M` on `Å`; `c : K` with `1 < ‖c‖`
(`NontriviallyNormedField.exists_one_lt_norm`). For `f` with `|f|_sup ≠ 0`: choose `m : ℤ` with `‖c‖^(m-1) < |f|_sup ≤ ‖c‖^m`
(`exists_mem_Ioc_zpow` for `‖c‖ > 1`, `|f|_sup > 0`); `g := c^(-m) • f` has `|g|_sup = ‖c‖^(-m) |f|_sup ≤ 1`
(`supSeminorm_smul`, `norm_zpow`), so `g ∈ Å`, `‖g‖ ≤ M`, and `‖f‖ = ‖c‖^m ‖g‖ ≤ M ‖c‖^m < M ‖c‖ |f|_sup`:
`C := M * ‖c‖`. For `|f|_sup = 0`: `c^(-m) • f ∈ Å` for every `m`, so `‖f‖ ≤ M ‖c‖^m` for all `m`, letting `m → -∞`
(`‖c‖^m → 0`: `tendsto_zpow_atTop_zero`/`zpow` with `1/‖c‖ < 1`) gives `f = 0`, so `‖f‖ = 0 ≤ C * 0`.
`isReduced_of…`: a nilpotent `f` has `|f|_sup = 0` (T044 `→` direction, no reducedness), so `‖f‖ ≤ C * 0 = 0`.""",
  mathlib="""`TopologicalRing.isBounded_of_forall_norm_le`, `TopologicalRing.IsBounded.exists_norm_le_of_normedAlgebra` (PFA),
`NontriviallyNormedField.exists_one_lt_norm`, `exists_mem_Ioc_zpow`, `norm_zpow`, `zpow_neg`, `tendsto_zpow_atTop_zero`,
`isReduced_iff`, `IsNilpotent`.""",
  sources="""BGR 3.8.3/6, end of proof (`bgr-3.8-proofs.md`): "Choose an element `c ∈ k` with `|c| > 1`. We claim that
`|f| ≤ |c| |f|_sup` for all `f ∈ A` … there exists an `m ∈ ℤ` such that `|c|^{m−1} < |f|_sup ≤ |c|^m`. Then
`|c^{−m}f|_sup ≤ 1` and `|c|^m < |c| |f|_sup`. Set `g := c^{−m}f` so that `g ∈ Å` … `|f| = |c^m g| ≤ |c|^m ≤ |c| |f|_sup`";
[RM] §2.3.5 ("`Å` is bounded in `A` exactly when `|·|_sup` is equivalent to the norm of `A`").""",
  gen="""The `IsUniform` bridge to the adic-spaces roadmap is a seam ticket for later (plan §7); here the norm form.
No `CharZero`.""")
