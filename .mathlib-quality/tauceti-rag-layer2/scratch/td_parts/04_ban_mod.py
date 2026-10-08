
# ---------------------------------------------------------------- SupSeminorm/Banach.lean
t(id='T023', title='Continuity into a Banach algebra on which `|·|_sup` is a norm; all complete norms equivalent (BGR 3.8.2/3–4)',
  file=BAN, deps='T004, T005', par='yes (with T020–T022, T028)', typ='lemmas', leaves='L4.1–L4.3',
  decls=[(BAN,'MaximalSpectrum.isClosed_asIdeal'),(BAN,'AlgHom.continuous_of_supSeminorm_eq_zero_imp'),
         (BAN,'AlgEquiv.exists_forall_norm_le_mul_of_supSeminorm_eq_zero_imp')],
  sketch="""`isClosed_asIdeal`: `Ideal.IsMaximal.isClosed` (needs `HasSummableGeomSeries A`: instance from
`[NormedRing A] [CompleteSpace A]`). `continuous_of…`: Layer 1
`AlgHom.continuous_of_forall_isClosed_of_finiteDimensional φ {𝔪 | 𝔪.IsMaximal}` with: `hB` closed by the first
lemma; `hA`: `𝔪.comap φ` is maximal (T005 `isMaximal_comap_of_isAlgebraic` with `x := ⟨𝔪, h⟩`, the class gives
algebraicity) hence closed in the Banach algebra `B` (`Ideal.IsMaximal.isClosed` again); `hfin` from the
hypothesis; `hinf`: `sInf {𝔪 | IsMaximal} = jacobson ⊥` (`Ideal.jacobson` is `sInf` of maximals ⊇ `⊥`,
`Ideal.jacobson_bot`-style unfolding) `= ⊥` because `f ∈ jacobson ⊥ ↔ |f|_sup = 0` (T004) `→ f = 0` (`hA`).
`exists_forall_norm_le_mul…`: `e.symm : B →ₐ[K] A` is continuous by the previous lemma (hypotheses on `A`);
then `e = (e.symm)⁻¹` is continuous by the open mapping theorem for the continuous linear bijection
`e.symm.toLinearMap` (`LinearEquiv.continuous_symm`/`ContinuousLinearEquiv.ofBijective`), and a continuous
linear map is bounded (`ContinuousLinearMap.exists_bound`/`LinearMap.continuous_iff_isBoundedLinearMap`).
Layer 1's `AlgEquiv.exists_forall_norm_le_mul_of_isNoetherianRing` is the template.""",
  mathlib="""`Ideal.IsMaximal.isClosed`, `HasSummableGeomSeries`, `Ideal.jacobson`, `Ideal.sInf_eq_bot`?, `LinearEquiv.continuous_symm`,
`ContinuousLinearMap.exists_bound`, `AlgEquiv.toLinearEquiv`; Layer 1 `AlgHom.continuous_of_forall_isClosed_of_finiteDimensional`,
`AlgEquiv.exists_forall_norm_le_mul_of_isNoetherianRing` (template).""",
  sources="""BGR 3.8.2/3 and proof (`bgr-3.8-proofs.md`): "`φ⁻¹(x) ∈ Max_k B` … Then by Lemma 3.8.1/9, we may finish the proof
by using the Closed Graph Theorem (in almost literally the same way as in the proof of Proposition 3.7.5/1)";
BGR 3.8.2/4: "all complete `k`-algebra norms on `A` are equivalent".""",
  gen="""BGR take `|·|_sup` a norm on `A` with `A` Banach and `Max_k A` the algebraic points; we add the finiteness of the
residue fields (`hfin`) because Layer 1's closed-graph lemma asks for `FiniteDimensional K (B ⧸ 𝔟)` (BGR 3.7.5/1 uses
"`A/𝔟` finite-dimensional" too). Affinoid algebras satisfy it.""")

t(id='T024', title='`|f|_sup ≤ inf ‖fⁱ‖^{1/i}`; power-bounded elements have `|f|_sup ≤ 1`', file=BAN, deps='T003',
  par='yes (with T020–T023, T028)', typ='lemmas', leaves='L4.4–L4.6',
  decls=[(BAN,'supSeminorm_le_norm_pow_rpow'),(BAN,'supSeminorm_le_smoothingFun'),(BAN,'IsPowerBounded.supSeminorm_le_one')],
  sketch="""`supSeminorm_le_norm_pow_rpow`: `|f|_sup = |f^i|_sup^(1/i) ≤ ‖f^i‖^(1/i)` by `supSeminorm_pow` (`i ≠ 0`),
Layer 0 `supSeminorm_le_norm`, `Real.rpow_le_rpow`, `Real.pow_rpow_inv_natCast`. `supSeminorm_le_smoothingFun`:
`smoothingFun μ f = ⨅ n : ℕ+, μ (f^n) ^ (1/n)` (unfold the `abbrev`), `μ = SeminormedRing.toRingSeminorm A` is the
norm; `le_ciInf` (`ℕ+` nonempty) with the first lemma. `IsPowerBounded.supSeminorm_le_one`: by
`IsPowerBounded.exists_norm_pow_le K` (PFA) get `C` with `‖f^n‖ ≤ C`; then `|f|_sup^n ≤ C` for all `n ≥ 1`, so
`|f|_sup ≤ 1` (`pow_le_one`-contrapositive: if `|f|_sup > 1` then `|f|_sup^n → ∞`, `tendsto_pow_atTop_atTop_of_one_lt`;
or `Real.le_one_of_pow_le`-style: `|f|_sup ≤ C^(1/n) → 1`).""",
  mathlib="""`smoothingFun`, `le_ciInf`, `Real.rpow_le_rpow`, `Real.pow_rpow_inv_natCast`, `tendsto_pow_atTop_atTop_of_one_lt`,
`PowerBounded.IsPowerBounded.exists_norm_pow_le`, `SeminormedRing.toRingSeminorm`.""",
  sources="""BGR 3.8.2/5, proof (`bgr-3.8-proofs.md`): "From Corollary 2 one deduces immediately that `|f|_sup ≤ |f|_r`";
BGR 6.2.3 intro (`bgr-6.2-6.3.1.md`): "all power-bounded elements `f ∈ A` must satisfy `|f|_sup ≤ 1`, since
`| |_sup` is power-multiplicative".""",
  gen="""Any Banach `K`-algebra with `HasSupSeminorm`; `IsPowerBounded` is PFA's topological notion (needs
`NontriviallyNormedField K` for the norm bound).""")

t(id='T025', title='The smoothing seminorm of a root is bounded by the spectral value of its equation (BGR 3.1.2/1 for `|·|_r`)',
  file=BAN, deps='none', par='yes (with T020–T024, T028)', typ='lemma', leaves='L4.7',
  decls=[(BAN,'smoothingFun_le_of_eval₂_eq_zero')],
  sketch="""`μ' := smoothingSeminorm μ hμ1 hna` with `μ := SeminormedRing.toRingSeminorm A`, `hμ1 : μ 1 ≤ 1`
(`NormOneClass`), `hna : IsNonarchimedean μ` (`IsUltrametricDist.isNonarchimedean_norm`); `μ'` is a `RingSeminorm`
(submultiplicative), power-multiplicative (`isPowMul_smoothingFun hμ1`), nonarchimedean
(`isNonarchimedean_smoothingFun`), with `μ' ≤ μ` (`smoothingFun_le_self`) and `μ' f = smoothingFun μ f`
(`smoothingSeminorm_apply`-level `rfl`). Then repeat T010's argument for `μ'` in place of `|·|_sup`:
`f^n = -∑_{i<n} φ(b_i) f^i`, `μ'(f)^n = μ'(f^n) ≤ max_i μ'(φ b_i) μ'(f)^i ≤ max_i ‖φ b_i‖ μ'(f)^i`, pick the
maximising `i`, divide: `μ'(f) ≤ ‖φ b_i‖^(1/(n-i)) ≤ ⨆ j : Fin n, ‖φ (coeff j)‖^(1/(n-j))` (`le_ciSup`, finite
family). Trivial `A`/`n = 0`: `μ' f = 0` (norm `0`) and the `iSup` over `Fin 0` is `0`.""",
  mathlib="""`smoothingSeminorm`, `isPowMul_smoothingFun`, `isNonarchimedean_smoothingFun`, `smoothingFun_le_self`,
`IsUltrametricDist.isNonarchimedean_norm`, `RingSeminorm.mul_le'`?, `Finset.exists_max_image`, `le_ciSup`,
`Real.iSup_of_isEmpty`.""",
  sources="""BGR 3.8.2/5, proof (`bgr-3.8-proofs.md`): "Since `| |_r` is a power-multiplicative semi-norm on `A`, one can
apply Proposition 3.1.2/1 to `A/ker | |_r` (viewed as a normed algebra over itself), and one gets
`|f|_r ≤ max |φ(b_i)|_r^{1/i} ≤ max |φ(b_i)|^{1/i}`".""",
  gen="""Stated for any ring hom `φ : B →+* A` (no `K`) and the norm's smoothing seminorm; the bound is phrased with the
coefficient norms `‖φ (coeff n)‖` in the `supSpectralValueTerms` shape.""")

t(id='T026', title='BGR 3.8.2/5: `|f|_sup = inf ‖fⁱ‖^{1/i}` along a continuous integral monomorphism', file=BAN,
  deps='T019, T024, T025', par='no', typ='theorem', leaves='L4.8',
  decls=[(BAN,'supSeminorm_eq_smoothingFun_of_isIntegral')],
  sketch="""`≤`: T024. `≥`: with `q := minpoly B f`, T025 gives `μ'(f) ≤ max_i ‖algebraMap (coeff i)‖^(1/(n-i)) ≤
max_i (C |coeff i|_sup)^(1/(n-i))` (`hC`, `Real.rpow_le_rpow`) `≤ C' max_i |coeff i|_sup^(1/(n-i)) = C' σ(q)
= C' |f|_sup` (M1), where `C' := max 1 C` handles `C^(1/j) ≤ C'` for `j ≥ 1` (`Real.rpow_le_self_of_one_le`-type:
`C^(1/j) ≤ max 1 C` since `1/j ≤ 1`). So `μ'(f) ≤ C' |f|_sup` for ALL `f`; apply to `f^m`: `μ'(f)^m ≤ C' |f|_sup^m`
(both power-multiplicative), take `m`-th roots and let `m → ∞` (`C'^(1/m) → 1`: `tendsto_rpow_div`-style,
`Real.tendsto_rpow_div_one`? use `le_of_tendsto` with `Filter.Tendsto (fun m ↦ C'^(1/m)) atTop (𝓝 1)` from
`tendsto_const_rpow_inv`?? — concretely `Real.rpow_natCast`-free: if `μ'(f) > |f|_sup` then `(μ'(f)/|f|_sup)^m ≤ C'`
for all `m` with ratio `> 1`, contradiction with `tendsto_pow_atTop_atTop_of_one_lt`; the case `|f|_sup = 0`
forces `μ'(f)^m ≤ 0`, so `μ'(f) = 0`). This is BGR's "This implies `|f|_r ≤ |f|_sup`, since both `| |_r` and
`| |_sup` are power-multiplicative" (= BGR 1.3.1/2, the contraction argument of T001-type).""",
  mathlib="""`isPowMul_smoothingFun`, `tendsto_pow_atTop_atTop_of_one_lt`, `Real.rpow_le_rpow`, `Real.mul_rpow`,
`Real.rpow_le_rpow_left_iff`, `div_pow`, `le_max_right`.""",
  sources="""BGR 3.8.2/5 and proof (`bgr-3.8-proofs.md`): "Because `φ` is continuous, there is a real constant `C > 1` such
that `|φ(b)| ≤ C|b|_sup` for all `b ∈ B`, and a fortiori `|φ(b)|^{1/i} ≤ C|b|_sup^{1/i}` … we have shown that
`|f|_r ≤ C max |b_i|_sup^{1/i} = C|f|_sup`. This implies `|f|_r ≤ |f|_sup`, since both `| |_r` and `| |_sup`
are power-multiplicative."; BGR 1.3.1/2 (`bgr-1.3-1.5.md`).""",
  gen="""Hypotheses of 3.8.1/7 (D8: `A` a domain) plus `A` Banach and the continuity bound `hC`; BGR's "`φ` continuous
if `B` is provided with the topology induced by `| |_sup`" is exactly `‖algebraMap b‖ ≤ C |b|_sup`.""")

t(id='T027', title='BGR 3.8.2/6: power-bounded ⇔ `|f|_sup ≤ 1`, topologically nilpotent ⇔ `|f|_sup < 1`', file=BAN,
  deps='T024, T026', par='no', typ='lemmas', leaves='L4.9–L4.10',
  decls=[(BAN,'isPowerBounded_of_supSeminorm_le_one_of_isIntegral'),(BAN,'isTopologicallyNilpotent_iff_supSeminorm_lt_one_of_isIntegral')],
  sketch="""`isPowerBounded_of…`: `q := minpoly B f`, `n := natDegree q ≥ 1`; by M1, `|f|_sup ≤ 1` gives `|coeff i|_sup ≤ 1`
for every `i < n` (T009 `coeff_le_pow` with `σ(q) ≤ 1`). Let `R := Subring.closure (range (algebraMap ∘ coeff))`
… simpler: show by induction on `j` that `f^j ∈ N := Submodule.span (Subring.closure {coeff i}) {f^i | i < n}`-free
version: prove `∀ j, ∃ c : Fin n → B, (∀ i, |c i|_sup ≤ 1) ∧ f^j = ∑ i, algebraMap (c i) * f^i` by induction
(`f^{j+1} = ∑ c_i f^{i+1}`; `f^n = -∑ b_i f^i` replaces the top term; the new coefficients are
`c_{i-1} - c_{n-1} b_i`, still of `|·|_sup ≤ 1` by `supSeminorm_add_le_max`, `supSeminorm_mul_le`, `supSeminorm_neg`).
Then `‖f^j‖ ≤ max_i ‖algebraMap (c i)‖ ‖f^i‖ ≤ C · max_i ‖f^i‖` (`hC`, `IsUltrametricDist` sum bound
`IsUltrametricDist.norm_sum_le_of_forall_le`?, `norm_mul_le`), a bound independent of `j`:
`isPowerBounded_of_norm_pow_le` (PFA). `isTopologicallyNilpotent_iff…`: (a) ⇔ (b) `inf ‖fⁱ‖^{1/i} < 1`:
`→`: `‖f^n‖ → 0` so some `‖f^m‖ < 1`, hence `smoothingFun ≤ ‖f^m‖^{1/m} < 1` (`smoothingFun_le`, `Real.rpow_lt_one`);
`←`: some `‖f^m‖^{1/m} < 1` (`ciInf_lt_iff`/`exists_lt_of_ciInf_lt`), so `r := ‖f^m‖ < 1` and `f^m` is
topologically nilpotent (`IsTopologicallyNilpotent.of_norm_lt_one`, PFA), hence `f` is (BGR 1.2.5/7 argument:
`‖f^{mq+s}‖ ≤ ‖f^m‖^q max_{s<m} ‖f^s‖ → 0`; write `n = m*q + s` by `Nat.div_add_mod`, `norm_mul_le`,
`squeeze_zero`). (b) ⇔ (c) by T026.""",
  mathlib="""`PowerBounded.isPowerBounded_of_norm_pow_le`, `IsTopologicallyNilpotent.of_norm_lt_one`, `smoothingFun_le`,
`exists_lt_of_ciInf_lt`, `Real.rpow_lt_one`, `Nat.div_add_mod`, `squeeze_zero`, `tendsto_pow_atTop_nhds_zero_of_lt_one`,
`IsUltrametricDist.norm_sum_le_of_forall_le`?/`exists_norm_finsetSum_le_of_nonempty`.""",
  sources="""BGR 3.8.2/6 and proof (`bgr-3.8-proofs.md`): "(c') implies (a'): … from (c') we get `|b_i|_sup ≤ 1` … Since `φ` is
continuous, `R := φ(P)[φ(b₁), …, φ(bₙ)]` is bounded under `| |`. From the integral equation for `f`, one easily
derives `f^j ∈ Σ_{i=0}^{n−1} R f^i` for all `j ∈ ℕ` (use induction on `j`). Hence `f` is power-bounded"; "it is
easily seen that an element `f` is topologically nilpotent in `A` if and only if `inf |f^i|^{1/i} < 1`".""",
  gen="""Under the hypotheses of 3.8.2/5 (`A` a domain, D8). The affinoid versions (6.2.3/1–2) are proved
separately in `Affinoid/PowerBounded.lean` without domain hypotheses (BGR's direct proofs).""")

# ---------------------------------------------------------------- BanachAlgebra/Module.lean
t(id='T028', title='Nakayama for the unit ball and open mapping for finitely generated submodules of `Aⁿ`', file=MOD,
  deps='none', par='yes (with T001–T027)', typ='lemmas', leaves='L5.1–L5.2',
  decls=[(MOD,'Submodule.forall_mem_of_forall_exists_eq_add_sum_smul_of_norm_lt_one'),(MOD,'Submodule.exists_forall_exists_eq_sum_smul_norm_le')],
  sketch="""Both are the module versions of Layer 1 `BanachAlgebra/Noetherian.lean`, whose proofs port with `*` replaced
by `•`. Nakayama: work in the `unitClosedBall A`-module `Fin n → unitClosedBall A`?? — Layer 1's trick: view the
`Fin m` vectors `x i` as generating the `Å := unitClosedBall A`-submodule `M := span Å (range x)` of the
`Å`-module `Fin n → A` (restrict scalars: `(Fin n → A)` is an `Å`-module via `Subring` coercion,
`Module.compHom`/`Subring.module`); the hypothesis says `M ≤ N' + 𝔞 • M` with `𝔞 := openUnitBallIdeal A`
(`Ideal.smul`), `N' := N.restrictScalars Å`; `𝔞 ≤ jacobson ⊥` (PFA `openUnitBallIdeal_le_jacobson_bot`), so
`Submodule.le_of_le_smul_of_le_jacobson_bot` (Nakayama, `M` finitely generated) gives `M ≤ N'`. Copy the proof of
`Ideal.forall_mem_of_forall_exists_eq_add_sum_mul_of_norm_lt_one` (Layer 1, lines 44–73) line by line. Open mapping:
the `K`-linear map `π : (Fin m → A) →L[K] N`, `a ↦ ⟨∑ a i • x i, _⟩` is continuous (`ContinuousLinearMap`, finite
sum of continuous smul) and surjective (`hx`), `N` is complete (closed in the Banach space `Fin n → A`:
`IsClosed.completeSpace_coe`), so `ContinuousLinearMap.exists_preimage_norm_le` gives `C` with preimages of norm
`≤ C ‖z‖`; coordinates `‖a i‖ ≤ ‖a‖` (`norm_le_pi_norm`). Copy `Ideal.exists_forall_exists_eq_sum_mul_norm_le`
(Layer 1, lines 77–110).""",
  mathlib="""`Submodule.le_of_le_smul_of_le_jacobson_bot`, `Submodule.restrictScalars`, `Ideal.smul`?,
`ContinuousLinearMap.exists_preimage_norm_le`, `IsClosed.completeSpace_coe`, `norm_le_pi_norm`, `Submodule.span`,
`Submodule.mem_span_range_iff_exists_fun`; PFA `openUnitBallIdeal_le_jacobson_bot`, `unitClosedBall`.""",
  sources="""BGR 3.7.2/2 and its proof (`bgr-3.7.md:39–46`, via 3.7.2/1 and 1.2.4/6 "Let `A` be complete and let `M` be an
`A`-module. Let `N` be a submodule of `M` such that …" — the Nakayama lemma for `Ǎ`); Layer 1's
`BanachAlgebra/Noetherian.lean` (ideal case, the direct template).""",
  gen="""`K` explicit (`include K`): the open mapping theorem needs a nontrivially normed field of scalars (Layer 1 B2
log, T022/T023: "without a nontrivially normed field of scalars Banach open mapping fails"). `A` noetherian
is a section variable, unused in these two lemmas (`omit` at cleanup if the linter asks).""")

t(id='T029', title='BGR 3.7.2/2 (module form): every submodule of `Aⁿ` over a noetherian Banach algebra is closed', file=MOD,
  deps='T028', par='no', typ='theorem', leaves='L5.3',
  decls=[(MOD,'Submodule.isClosed_of_isNoetherianRing_pi')],
  sketch="""Port `Ideal.isClosed_of_fg_closure` and `Ideal.isClosed_of_isNoetherianRing` (Layer 1, lines 114–168):
`N̄ := N.topologicalClosure` is a submodule (`Submodule.topologicalClosure`), finitely generated (noetherian:
`IsNoetherian.noetherian`), say by `x : Fin m → Fin n → A` (`Submodule.fg_iff_exists_fin_generating_family`);
each `x i ∈ N̄` is a limit of elements of `N`, so `x i = y_i + (x i − y_i)` with `y_i ∈ N` and `x i − y_i ∈ N̄`
of norm `< ε`; by the open-mapping lemma (T028, applied to the closed `N̄` with generators `x`) write
`x i − y_i = ∑ c μ • x μ` with `‖c μ‖ ≤ C ‖x i − y_i‖ < 1` for `ε` small; Nakayama (T028) then gives `x i ∈ N`
for all `i`, so `N̄ = span (range x) ≤ N`, i.e. `N` is closed (`Submodule.topologicalClosure_minimal`-free:
`isClosed_of_closure_subset`).""",
  mathlib="""`Submodule.topologicalClosure`, `Submodule.le_topologicalClosure`, `Submodule.isClosed_topologicalClosure`,
`IsNoetherian.noetherian`, `Submodule.fg_iff_exists_fin_generating_family`, `Metric.mem_closure_iff`,
`isClosed_of_closure_subset`; Layer 1 `Ideal.isClosed_of_fg_closure` (template).""",
  sources="""BGR 3.7.2/2 (`bgr-3.7.md:39`): "Let `A` be a `k`-Banach algebra and `M` a complete normed `A`-module. Then `M` is
Noetherian ⇔ … every submodule of `M` is closed" (the direction used: finitely generated submodules of a
complete module over a complete ring are closed, 3.7.2/1).""",
  gen="""`Fin n → A` with the sup norm; `K` explicit. The ideal case is Layer 1's; this is the module case needed by
3.8.3/7 and 6.2.4/1.""")

t(id='T030', title='BGR 3.7.3/1: submodules of complete finite normed modules are closed', file=MOD, deps='T029', par='no',
  typ='lemmas', leaves='L5.4–L5.5',
  decls=[(MOD,'Submodule.isClosed_of_isClosed_comap'),(MOD,'Submodule.isClosed_of_isNoetherianRing_of_finite')],
  sketch="""`isClosed_of_isClosed_comap`: `π.restrictScalars K` is a continuous surjective `K`-linear map between Banach spaces,
hence open (`ContinuousLinearMap.isOpenMap`, from `exists_preimage_norm_le`) and a quotient map
(`IsOpenMap.isQuotientMap`/`IsOpenMap.to_isQuotientMap` with continuity and surjectivity); a set is closed iff its
preimage under a quotient map is closed (`IsQuotientMap.isClosed_preimage`), and `π ⁻¹' N = N.comap π`.
`isClosed_of_isNoetherianRing_of_finite`: `Module.Finite A M` gives `x : Fin n → M` spanning `M`
(`Module.Finite.exists_fin`); `π := Fintype.linearCombination A x : (Fin n → A) →ₗ[A] M` is surjective
(`Fintype.range_linearCombination`, `span = ⊤`) and continuous (finite sum of `fun a ↦ a i • x i`, continuous by
`ContinuousSMul A M` and `continuous_apply`); `N.comap π` is a submodule of `Fin n → A`, closed by T029; conclude
with the first lemma.""",
  mathlib="""`ContinuousLinearMap.isOpenMap`, `IsOpenMap.isQuotientMap`, `IsQuotientMap.isClosed_preimage`, `Submodule.comap`,
`Module.Finite.exists_fin`, `Fintype.linearCombination`, `Fintype.range_linearCombination`, `continuous_finset_sum`,
`Continuous.smul`, `continuous_apply`, `LinearMap.restrictScalars`.""",
  sources="""BGR 3.7.3/1 (`bgr-3.7.md:53`): "Every submodule `M′` of a module `M ∈ 𝔐_A` is closed"; BGR p. 242 (6.2.4/1's proof):
"Viewing `A` as a submodule of the finite `A`-module `A'`, we see by Proposition 3.7.3/1 that `A` is closed in `A'`".""",
  gen="""`M` a Banach `K`-space with a compatible `A`-module structure (`IsScalarTower K A M`, `ContinuousSMul A M`) — BGR's
`𝔐_A` (finite complete normed `A`-modules). `K` explicit.""")
