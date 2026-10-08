
# ---------------------------------------------------------------- Affinoid/Reduction.lean
t(id='T053', title='The reduction `Ã = Å ⧸ Ǎ` is a reduced `K̃`-algebra (BGR 6.2.3/4, 1.2.5/7)', file=RED, deps='T047',
  par='yes (with T054)', typ='defs+instances', leaves='L9.1–L9.4',
  decls=[(RED,'powerBounded.ofUnitClosedBall'),(RED,'powerBounded.ofUnitClosedBall_mem_topologicallyNilpotent'),
         (RED,'Reduction.ofResidueField'),(RED,'Reduction.isReduced')],
  sketch="""`ofUnitClosedBall`: the ring-hom fields are `Subtype.ext` + `map_one/map_mul/map_zero/map_add` of `algebraMap K A`
(the carrier is `algebraMap K A c` with `algebraMap_mem_powerBounded (Subring.norm_le_one c)`).
`…_mem_topologicallyNilpotent`: `|algebraMap c|_sup = ‖c‖ |1|_sup ≤ ‖c‖ < 1` (`mem_openUnitBallIdeal`,
`Algebra.algebraMap_eq_smul_one`, `supSeminorm_smul`, `supSeminorm_one_le`). `Reduction.ofResidueField`:
`IsLocalRing.ResidueField (unitClosedBall K) = unitClosedBall K ⧸ maximalIdeal _` and `maximalIdeal (unitClosedBall K) =
openUnitBallIdeal K` (PFA `NormedRing.maximalIdeal_unitClosedBall`), so `Ideal.Quotient.lift (maximalIdeal _)
((Reduction.mk K A).comp (ofUnitClosedBall K A)) (fun c hc ↦ Ideal.Quotient.eq_zero_iff_mem.2 (… (by rwa
[maximalIdeal_unitClosedBall] at hc)))`. `isReduced`: `Ideal.Quotient.isReduced_iff`?/`Ideal.isRadical_iff_quotient_reduced`:
`IsReduced (R ⧸ I) ↔ I.IsRadical`, with T047 `topologicallyNilpotent_isRadical`.""",
  mathlib="""`IsLocalRing.ResidueField`, `IsLocalRing.residue`, `Ideal.Quotient.lift`, `Ideal.Quotient.eq_zero_iff_mem`,
`Ideal.isRadical_iff_quotient_reduced` (verify name), `RingHom.toAlgebra`; PFA `NormedRing.maximalIdeal_unitClosedBall`,
`mem_openUnitBallIdeal`.""",
  sources="""BGR 6.2.3/4 (`bgr-6.2-6.3.1.md`): "`Ã = {f ∈ A; |f|_sup ≤ 1}/{f ∈ A; |f|_sup < 1}`"; BGR 1.2.5/6–7 (`bgr-1.3-1.5.md`);
[RM] §2.3.4 ("The reduction `Ã := Å ⧸ Ǎ` is a `K̃`-algebra").""",
  gen="""`Reduction K A` is an `abbrev` for the quotient (so the `CommRing` instance is found); the `K̃`-algebra structure
is `(Reduction.ofResidueField K A).toAlgebra` for any `[HasSupSeminorm K A]`.""")

t(id='T054', title='`T̃ₙ ≅ K̃[X₁, …, Xₙ]`: the reduction of the Tate algebra (BGR 6.2.3/4 + 5.1.2)', file=RED, deps='T038, T047',
  par='yes (with T053)', typ='lemma+def', leaves='L9.5–L9.6',
  decls=[(RED,'TateAlgebra.powerBounded_eq_unitClosedBall'),(RED,'TateAlgebra.reductionEquiv')],
  sketch="""`powerBounded_eq_unitClosedBall`: `Subring.ext fun f ↦ by simp [mem_powerBounded, Subring.mem_unitClosedBall,
supSeminorm_eq_norm]` (Layer 0). `reductionEquiv`: `e : powerBounded K (Tₙ) ≃+* unitClosedBall (Tₙ)` from the subring
equality (`RingEquiv.subringCongr`); under `e`, `topologicallyNilpotent K (Tₙ)` maps onto `openUnitBallIdeal (Tₙ)`
(`mem_topologicallyNilpotent` is `|f|_sup < 1 ↔ ‖f‖ < 1 = mem_openUnitBallIdeal`); `Ideal.quotientEquiv _ _ e (by ext; simp …)`
gives `Reduction K (Tₙ) ≃+* unitClosedBall (Tₙ) ⧸ openUnitBallIdeal _`, then compose with Layer 0
`MvPowerSeries.Restricted.reductionEquiv : … ≃+* MvPolynomial (Fin n) (ResidueField (unitClosedBall K))`.""",
  mathlib="""`RingEquiv.subringCongr`, `Ideal.quotientEquiv`, `Ideal.map`, `RingEquiv.trans`, `Subring.ext`; Layer 0
`MvPowerSeries.Restricted.reductionEquiv`, `supSeminorm_eq_norm`; PFA `mem_openUnitBallIdeal`, `Subring.mem_unitClosedBall`.""",
  sources="""[RM] §2.3.4 ("for `Tₙ` it is `K̃[X]` (§0.1.2)"); BGR 5.1.2 (Layer 0 `TateAlgebra/Reduction.lean`, "`T̃ₙ = k̃[X₁, …, Xₙ]`");
BGR 6.2.3/4 (`bgr-6.2-6.3.1.md`).""",
  gen="""`TateAlgebra K n` with the Gauss norm; the instance `Affinoid.TateAlgebra.instHasSupSeminorm` is used.""")

t(id='T055', title='`|·|_sup` is a valuation iff `A` is reduced and `Ã` is a domain (BGR 6.2.3/5, via 1.5.3/1)', file=RED,
  deps='T043, T044, T053', par='no', typ='lemmas', leaves='L9.7–L9.9',
  decls=[(RED,'supSeminorm_mul_of_isReduced_of_isDomain_reduction'),(RED,'isReduced_of_isValuation'),(RED,'isDomain_reduction_of_isValuation')],
  sketch="""`supSeminorm_mul…` (BGR 1.5.3/1's proof): by contradiction suppose `|fg| < |f||g|`; then `f, g ≠ 0` and `|f|, |g| ≠ 0`
(else both sides `0`; `|f| = 0 → f = 0` in the reduced `A`, T044). T043: `c_i, s_i ≥ 1` with `|c_i • f_i^{s_i}|_sup = 1`
(`f_1 := f`, `f_2 := g`); WLOG `s_2 ≥ s_1` (symmetric). `u := c_1 • f^{s_1}`, `v := c_2 • g^{s_2}` lie in `Å ∖ Ǎ`
(`|u| = 1`). `|u v|_sup = ‖c_1‖ ‖c_2‖ |f^{s_1} g^{s_2}|_sup ≤ ‖c_1‖‖c_2‖ |fg|^{s_1} |g|^{s_2 − s_1} < ‖c_1‖‖c_2‖ |f|^{s_1}
|g|^{s_2} = |u| |v| = 1` (`supSeminorm_smul`, `supSeminorm_mul_le`, `supSeminorm_pow`, strict `mul_lt_mul`), so
`u v ∈ Ǎ`, i.e. `τ(u) τ(v) = 0` in the domain `Ã` with `τ(u), τ(v) ≠ 0` (`Ideal.Quotient.eq_zero_iff_mem`,
`|u| = 1 ≮ 1`): contradiction with `mul_eq_zero`/`NoZeroDivisors`. `isReduced_of_isValuation`: nilpotent `f` has
`|f|_sup = 0` (T044 or power-multiplicativity) so `f = 0`. `isDomain_reduction_of_isValuation`:
`Ideal.Quotient.isDomain_iff_prime`: `Ǎ` is prime: `Ǎ ≠ ⊤` since `1 ∉ Ǎ` (`|1|_sup = 1`, `Nontrivial A`); `u v ∈ Ǎ →
|u||v| = |uv| < 1 → |u| < 1 ∨ |v| < 1` (`mul_lt_one_iff`-style with `|u|, |v| ≤ 1`).""",
  mathlib="""`Ideal.Quotient.isDomain_iff_prime`, `Ideal.IsPrime`, `Ideal.Quotient.eq_zero_iff_mem`, `mul_eq_zero`, `mul_lt_mul''`,
`pow_le_pow_left`, `isReduced_iff`, `IsNilpotent`.""",
  sources="""BGR 6.2.3/5 (`bgr-6.2-6.3.1.md`): "The supremum semi-norm is a valuation on `A` if and only if `A` is reduced and `Ã`
is an integral domain" ("using Propositions 1.5.3/1, 6.2.1/4, and the above Proposition 4"); BGR 1.5.3/1 and proof
(`bgr-1.3-1.5.md`): "Assume there are elements `a₁, a₂ ∈ A` such that `|a₁a₂| < |a₁| |a₂|` … `(m₁a₁^{s₁})(m₂a₂^{s₂}) ∈ A˅`.
However, this is in contradiction with the fact that, by condition (ii), the ideal `A˅` is prime in `A°`"; BGR 1.5.1
(`bgr-1.3-1.5.md`): "A valued ring is an integral domain. The ideal `Ǎ` is prime in `Å`; hence `Ã` is also an integral
domain".""",
  gen="""BGR's iff split into three single-conclusion lemmas; "valuation" = multiplicative + `|f|_sup = 0 → f = 0`
(BGR 1.5.1/1 (a) and (c)). No norm on `A` is needed.""")

# ---------------------------------------------------------------- Affinoid/FunctionAlgebra.lean
t(id='T056', title='BGR 6.2.4/1 for affinoid domains (`[CharZero K]`)', file=AFA, deps='T037, T038', par='yes (with T057)',
  typ='theorem', leaves='L10.1', decls=[(AFA,'isBanachFunctionAlgebra_of_isDomain')],
  sketch="""Noether normalisation `φ : TateAlgebra K d →ₐ[K] A` finite injective (Layer 1); `letI := φ.toAlgebra`, tower,
`Module.Finite` (`hfin`), `FaithfulSMul` (`hinj`); `hcont : Continuous (algebraMap _ A)` = Layer 1
`AlgHom.continuous_of_isAffinoidAlgebra' (tateAlgebra d) hA φ`. Apply T037 `IsBanachFunctionAlgebra.of_finite_domain` with
`B := TateAlgebra K d`: `NormMulClass` (Layer 0), `IsDomain`, `IsIntegrallyClosed` (Rueckert), `IsNoetherianRing`
(Layer 1), `HasSupSeminorm` (T038), `hBsup := supSeminorm_eq_norm` (Layer 0), `hws := Affinoid.TateAlgebra.isWeaklyStable_fractionRing K d`
(Layer 0, `[CharZero K]`; its statement is exactly the `letI := IsFractionRing.normedField …; IsWeaklyStable …` form).""",
  mathlib="""`RingHom.toAlgebra`, `IsScalarTower.of_algebraMap_eq`, `faithfulSMul_iff_algebraMap_injective`, `Module.Finite` from
`RingHom.Finite`; Layer 0 `Affinoid.TateAlgebra.isWeaklyStable_fractionRing`; Layer 1 `exists_finite_injective`,
`AlgHom.continuous_of_isAffinoidAlgebra'`, `isNoetherianRing`.""",
  sources="""BGR 6.2.4/1, proof (`bgr-6.2-6.3.1.md`): "Let us first consider the case, where `A` is an integral domain. Choose a
finite normalization monomorphism `φ: T_d → A` for a suitable `d ≥ 0`. Then `φ` is torsion-free, and the assertion
follows immediately from Theorem 3.8.3/7, because the field of fractions `Q(T_d)` is weakly stable (Theorem 5.3.1/1)."
""",
  gen="""`[CharZero K]` (plan D2) and `A : Type u` with `K : Type u` (D12).""")

t(id='T057', title='The diagonal map `A → ∏ A ⧸ 𝔭ᵢ`: continuous scalar action, closed range, open-mapping bound', file=AFA,
  deps='T030', par='yes (with T056)', typ='lemmas', leaves='L10.2–L10.4',
  decls=[(AFA,'continuousSMul_pi_quotient'),(AFA,'isClosed_range_pi_quotient_mk'),(AFA,'exists_norm_le_mul_norm_pi_quotient_mk')],
  sketch="""Instances: `Ideal.Quotient.normedCommRing (𝔭 i)` (closed ideals: Layer 1 `hA.isClosed_ideal`), `Pi.normedCommRing`,
`Ideal.Quotient.normedAlgebra`, `Pi.normedAlgebra`, `Pi.completeSpace` (each quotient complete:
`QuotientAddGroup.completeSpace`/`Submodule.Quotient.completeSpace` for closed subgroups of a complete group).
`continuousSMul`: `a • x = fun i ↦ mk a * x i` (`Pi.smul_apply`, `Submodule.Quotient.mk_smul`/`Ideal.Quotient.mk_smul`?
— for `A ⧸ I` as an `A`-module, `a • mk b = mk (a * b)`); continuity from `continuous_pi`, `Continuous.mul`,
`Ideal.Quotient.continuous_mk`-type (`continuous_quot_mk`). `isClosed_range`: the range of `RingHom.pi (mk ∘ 𝔭)` is the
image of the `A`-submodule `⊤` under the `A`-linear map `LinearMap.pi (fun i ↦ (𝔭 i).mkQ)`, a submodule of the finite
`A`-module `∀ i, A ⧸ 𝔭 i` (`Module.Finite.pi`, each quotient finite: `Module.Finite.quotient`), so closed by T030
`Submodule.isClosed_of_isNoetherianRing_of_finite K` (`IsNoetherianRing A` from Layer 1; `NormedSpace K (Pi)`,
`IsScalarTower K A (Pi)` instances: `Pi.isScalarTower`). `exists_norm_le…`: the `K`-linear map `π : A →L[K] ∀ i, A ⧸ 𝔭 i`
is continuous, injective (`h`: kernel `= ⨅ 𝔭 i = ⊥`, `LinearMap.ker_pi`/`Submodule.iInf`), with closed range; open mapping
onto the range (`ContinuousLinearMap.exists_preimage_norm_le`) gives `‖f‖ ≤ C ‖π f‖` (uniqueness of the preimage).""",
  mathlib="""`Ideal.Quotient.normedCommRing`, `Ideal.Quotient.normedAlgebra`, `Pi.normedCommRing`, `Pi.normedAlgebra`, `Pi.completeSpace`,
`QuotientAddGroup.completeSpace`, `continuous_pi`, `continuous_quot_mk`, `LinearMap.pi`, `Submodule.mkQ`, `Module.Finite.pi`,
`Module.Finite.quotient`, `LinearMap.ker_pi`, `Submodule.ker_mkQ`, `ContinuousLinearMap.exists_preimage_norm_le`,
`IsClosed.completeSpace_coe`; Layer 1 `IsAffinoidAlgebra.isClosed_ideal`, `isNoetherianRing`.""",
  sources="""BGR 6.2.4/1, proof (`bgr-6.2-6.3.1.md`): "the canonical homomorphism `π: A → A' := ⊕ A/𝔭_i` is injective … Provide
`A'` with the maximum norm … Then `A'` is complete under `| |` … Viewing `A` as a submodule of the finite `A`-module
`A'`, we see by Proposition 3.7.3/1 that `A` is closed in `A'`."
""",
  gen="""Stated for an arbitrary finite family of ideals `𝔭 : ι → Ideal A` (the minimal primes are the instance); the
`haveI` for closedness is part of the statements so that the quotient normed-ring instances exist.""")

t(id='T058', title='M4 — REDUCED AFFINOID ALGEBRAS ARE BANACH FUNCTION ALGEBRAS (BGR 6.2.4/1)', file=AFA, deps='T006, T056, T057',
  par='no', typ='theorem', leaves='L10.5', milestone='M4 ([RM] §2.4.1, BGR 6.2.4/1)', decls=[(AFA,'isBanachFunctionAlgebra_of_isReduced')],
  sketch="""`ι := hfin.toFinset` with `hfin := minimalPrimes.finite_of_isNoetherianRing A` (a `Fintype` via `Finset`-subtype),
`𝔭 i := (i : Ideal A)`. `⨅ i, 𝔭 i = sInf (minimalPrimes A) = (⊥).radical = nilradical A = ⊥` (`Ideal.sInf_minimalPrimes`,
`nilradical_eq_zero` for reduced). T057 gives `C₀` with `‖f‖ ≤ C₀ ‖π f‖`. For each `i`, `A ⧸ 𝔭 i` is an affinoid domain
(`hA.quotient`, `Ideal.Quotient.isDomain` from `IsPrime`) with the residue norm, so T056 gives `C_i` with
`‖mk f‖ ≤ C_i |mk f|_sup ≤ C_i |f|_sup` (T006 `supSeminorm_mk_le`). `‖π f‖ = ⨆ i, ‖mk_i f‖ ≤ (max_i C_i) |f|_sup`
(`pi_norm_le_iff_of_nonneg`, `Finset.sup'`/`Finset.le_sup'`). `C := C₀ * max_i C_i` (use `Finset.sup' _ nonempty` when
`ι` nonempty, else `A` is trivial and any `C` works).""",
  mathlib="""`minimalPrimes.finite_of_isNoetherianRing`, `Ideal.sInf_minimalPrimes`, `nilradical_eq_zero`, `Ideal.Quotient.isDomain`,
`pi_norm_le_iff_of_nonneg`, `Finset.sup'`, `Finset.le_sup'`, `Set.Finite.toFinset`, `Fintype` on a finset coerced to type.""",
  sources="""BGR 6.2.4/1 (`bgr-6.2-6.3.1.md`): "Every reduced `k`-affinoid algebra `A` is a Banach function algebra; i.e., `| |_sup`
is a complete norm on `A`. It is equivalent to every other complete `k`-algebra norm on `A`." and its proof ("due to
Lemma 6.2.1/3, the norm `| |` induces the supremum norm on `A`"); [RM] §2.4.1.""",
  gen="""`[CharZero K]` (D2), `A : Type u` (D12), any complete `K`-algebra norm on `A`; the conclusion is the norm inequality
(D3).""")

t(id='T059', title='Consequences of M4: `Å` is bounded for reduced `A`; continuous maps out of reduced `A` are `|·|_sup`-bounded (§2.3.5, §2.4.3)',
  file=AFA, deps='T052, T058', par='no', typ='lemmas', leaves='L10.6–L10.7',
  decls=[(AFA,'isBounded_powerBounded_of_isReduced'),(AFA,'exists_norm_map_le_mul_supSeminorm')],
  sketch="""`isBounded_powerBounded_of_isReduced`: `(hA.exists_norm_le_mul_supSeminorm_iff_isBounded_powerBounded).1
(hA.isBanachFunctionAlgebra_of_isReduced)` (T052, T058). `exists_norm_map_le…`: `hφ` gives `C₁` with `‖φ f‖ ≤ C₁ ‖f‖`
(Layer 1 `exists_forall_norm_le_mul_of_continuous` or `ContinuousLinearMap.exists_bound` on `φ.toLinearMap`), M4 gives
`C₂`; `C := C₁ * C₂`.""",
  mathlib="""`ContinuousLinearMap.exists_bound`, `AlgHom.toLinearMap`, `LinearMap.mkContinuous`; Layer 1
`MvPowerSeries.Restricted.exists_forall_norm_le_mul_of_continuous`.""",
  sources="""[RM] §2.3.5 ("deduce from §2.4.1 that a reduced affinoid algebra is uniform") and §2.4.3; BGR 6.2.4/1 ("It is
equivalent to every other complete `k`-algebra norm on `A`").""",
  gen="""`[CharZero K]` inherited from M4; the `IsUniform` seam (plan §7) is left for the adic roadmap.""")
