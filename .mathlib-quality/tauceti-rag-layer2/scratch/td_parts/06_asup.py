
# ---------------------------------------------------------------- Affinoid/SupSeminorm.lean
t(id='T038', title='Affinoid algebras have a supremum seminorm (BGR 6.2.1/1); `|f|_sup ≤ ‖g‖` through a presentation', file=ASUP,
  deps='T005', par='yes (with T020–T037)', typ='lemmas+instance', leaves='L7.1–L7.3',
  decls=[(ASUP,'hasSupSeminorm'),(ASUP,'supSeminorm_le_norm_of_eq')],
  sketch="""`hasSupSeminorm`: `isAlgebraic`: Layer 1 `finiteDimensional_quotient_of_isMaximal hA x.asIdeal` gives
`FiniteDimensional K (A ⧸ x)`, hence `Algebra.IsAlgebraic` (`Algebra.IsAlgebraic.of_finite`). `bddAbove`: take a
presentation `⟨n, α, hα⟩ := hA`; for `f` choose `g` with `α g = f`; for every `x`, `evalNorm K x f = evalNorm K x (α g)
= evalNorm K (comapPoint α x) g` (T005, the point `x` is algebraic by the first part — note `comapPoint` needs
`HasSupSeminorm K A`, so use the underlying `isMaximal_comap_of_isAlgebraic` + `evalNorm_comapPoint`'s proof shape, or
first build the instance with the bound through `evalNorm_eq_norm_algHom`-free reasoning: `evalNorm K x (α g) =
evalNorm K ⟨comap α x, _⟩ g ≤ ‖g‖` (Layer 0 `evalNorm_le_norm` on the Banach algebra `Tₙ`)). `supSeminorm_le_norm_of_eq`:
`supSeminorm K f = supSeminorm K (α g) ≤ supSeminorm K g ≤ ‖g‖` (T005 + Layer 0 `supSeminorm_le_norm`), with the
instances from `hA.hasSupSeminorm` and `Affinoid.TateAlgebra.instHasSupSeminorm`.""",
  mathlib="""`Algebra.IsAlgebraic.of_finite`; Layer 1 `IsAffinoidAlgebra.finiteDimensional_quotient_of_isMaximal`; Layer 0
`Affinoid.evalNorm_le_norm`, `Affinoid.supSeminorm_le_norm`, `Affinoid.bddAbove_range_evalNorm`.""",
  sources="""BGR 6.2.1 p. 236 (`bgr-6.2-6.3.1.md`): "According to Corollary 6.1.2/3, all maximal ideals in a `k`-affinoid
algebra `A` are `k`-algebraic … because `A` is a `k`-Banach algebra, Corollary 3.8.2/2 yields that `| |_sup` is
finite; more precisely, `|f|_sup ≤ |f|_α` for all `f ∈ A` and all epimorphisms `α: Tₙ → A`".""",
  gen="""`hasSupSeminorm` is a theorem (its hypothesis `hA` is a Prop, not a class); the Tate-algebra instance is
derived from it. No norm on `A` is needed.""")

t(id='T039', title='Integral monomorphisms of affinoid algebras are isometries (BGR 6.2.2/1)', file=ASUP, deps='T014, T038',
  par='yes (with T040)', typ='lemma', leaves='L7.4', decls=[(ASUP,'supSeminorm_map_eq_of_isIntegral')],
  sketch="""`letI := φ.toAlgebra`; `IsScalarTower K B A` (`IsScalarTower.of_algebraMap_eq fun k ↦ (φ.commutes k).symm`);
`Algebra.IsIntegral B A := ⟨hint⟩` (`RingHom.IsIntegral` ↔ `Algebra.IsIntegral` under `toAlgebra`:
`Algebra.IsIntegral.mk`/`RingHom.IsIntegral`); `FaithfulSMul B A` from `hinj` (`faithfulSMul_iff_algebraMap_injective`);
`haveI := hA.hasSupSeminorm; haveI := hB.hasSupSeminorm`; `exact supSeminorm_algebraMap_eq K b` (T014). The contraction
half of 6.2.2/1 is `Affinoid.supSeminorm_map_le` (T005).""",
  mathlib="""`RingHom.toAlgebra`, `IsScalarTower.of_algebraMap_eq`, `faithfulSMul_iff_algebraMap_injective`, `RingHom.IsIntegral`,
`Algebra.IsIntegral`.""",
  sources="""BGR 6.2.2/1 (`bgr-6.2-6.3.1.md`): "Every homomorphism of `k`-affinoid algebras `φ: B → A` is a contraction with
respect to the supremum semi-norm. If `φ` is an integral monomorphism, it is an isometry." (from 3.8.1/4 and 3.8.1/6).""",
  gen="""Affinoid wrapper of T014 with `φ.toRingHom.IsIntegral` (BGR: integral, not finite).""")

t(id='T040', title='`|f|_sup = σ(minpoly_{T_d} f)` and `|φ(t) f|_sup = ‖t‖ |f|_sup` for affinoid domains over `T_d` (BGR 6.2.2/2)',
  file=ASUP, deps='T019, T020, T038', par='yes (with T039)', typ='lemmas', leaves='L7.5–L7.6',
  decls=[(ASUP,'supSeminorm_eq_supSpectralValue_minpoly_tateAlgebra'),(ASUP,'supSeminorm_algebraMap_tateAlgebra_mul')],
  sketch="""Instances for M1 with `B := TateAlgebra K d`: `IsDomain` (Layer 0 `Restricted.instIsDomain`), `IsIntegrallyClosed`
(Layer 0 `TateAlgebra/Rueckert.lean`, line 68), `HasSupSeminorm` (T038 instance), `Module.IsTorsionFree (TateAlgebra K d) A`
from `[IsDomain A] [FaithfulSMul _ A]` (T033's lemma, `Module.isTorsionFree_of_faithfulSMul_of_isDomain`, but it is
stated for finite `A` — for integral `A` reprove inline: `b • a = algebraMap b * a = 0`, domain). Then
`supSeminorm_eq_supSpectralValue_minpoly K f` (T019) and `supSeminorm_algebraMap_mul K (hB := …) t f` (T020) with
`hB : ∀ t t', |t t'|_sup = |t|_sup |t'|_sup` from Layer 0 `supSeminorm_eq_norm` + `NormMulClass` (`norm_mul`), and
`‖t‖ = supSeminorm K t` to rewrite the conclusion.""",
  mathlib="""`norm_mul` (`NormMulClass`); Layer 0 `MvPowerSeries.Restricted.supSeminorm_eq_norm`, `Restricted.instIsDomain`,
the `IsIntegrallyClosed (TateAlgebra K n)` instance of `TateAlgebra/Rueckert.lean`.""",
  sources="""BGR 6.2.2/2 (`bgr-6.2-6.3.1.md`): "Let `φ: T_d → A` be an integral torsion-free monomorphism into some `k`-affinoid
algebra `A`. Then `| |_sup` is a faithful `T_d`-algebra norm on `A` (i.e., `|φ(t) f|_sup = |t| |f|_sup` …). If
`fⁿ + φ(t₁) fⁿ⁻¹ + ⋯ + φ(tₙ) = 0` is the integral equation of minimal degree for `f` over `T_d`, then one has
`|f|_sup = max |t_i|^{1/i}`" ("Since `T_d` is a valued integrally closed domain, we can derive from Proposition
3.8.1/7 (a) and (d)").""",
  gen="""For `A` a domain (D8: BGR say "torsion-free"); stated with `[Algebra (TateAlgebra K d) A] [IsScalarTower …]
[Algebra.IsIntegral …] [FaithfulSMul …]` (the consumer applies Noether normalisation and `letI := φ.toAlgebra`).""")

t(id='T041', title='The maximum modulus principle for affinoid domains (BGR 6.2.1/4 (i), special case)', file=ASUP,
  deps='T021, T040', par='no', typ='theorem', leaves='L7.7', decls=[(ASUP,'exists_evalNorm_eq_supSeminorm_of_isDomain')],
  sketch="""Noether normalisation (Layer 1 `hA.exists_finite_injective`): `φ : TateAlgebra K d →ₐ[K] A` finite injective.
`letI := φ.toAlgebra`, tower, `Algebra.IsIntegral` (finite ⇒ integral: `RingHom.Finite.to_isIntegral`),
`FaithfulSMul`, torsion-free (T033 lemma), `HasSupSeminorm` both (T038). Apply T021 `exists_evalNorm_eq_supSeminorm_of_forall_exists K`
with `hB : ∀ t, ∃ y, evalNorm K y t = supSeminorm K t`: Layer 0 `exists_evalNorm_eq_norm t` gives `y` with
`evalNorm K y t = ‖t‖ = supSeminorm K t` (`supSeminorm_eq_norm`).""",
  mathlib="""`RingHom.Finite.to_isIntegral`; Layer 1 `IsAffinoidAlgebra.exists_finite_injective`; Layer 0
`MvPowerSeries.Restricted.exists_evalNorm_eq_norm`, `supSeminorm_eq_norm`.""",
  sources="""BGR 6.2.1/4, proof (`bgr-6.2-6.3.1.md`): "Let us first consider the special case, where `A` is an integral domain.
Applying the Noether Normalization Lemma (Corollary 6.1.2/2), we find a finite monomorphism `φ: T_d → A` … Since `T_d`
is integrally closed (Theorem 5.2.6/2) and since the Maximum Modulus Principle holds for `T_d` (Corollary 5.1.4/6),
assertions (i) and (ii) follow from Proposition 3.8.1/7."; Bosch 1.4/14 (`bosch-lectures.txt`).""",
  gen="""`[IsDomain A]`; no norm on `A`.""")

t(id='T042', title='M2 — THE MAXIMUM MODULUS PRINCIPLE (BGR 6.2.1/4 (i); Bosch 1.4/14)', file=ASUP, deps='T007, T041', par='no',
  typ='theorem', leaves='L7.8', milestone='M2 ([RM] §2.2.1)', decls=[(ASUP,'exists_evalNorm_eq_supSeminorm')],
  sketch="""`haveI := hA.hasSupSeminorm`, `IsNoetherianRing A` (Layer 1). T007: `𝔭 ∈ minimalPrimes A` with
`supSeminorm K (mk 𝔭 f) = supSeminorm K f`. `A ⧸ 𝔭` is an affinoid domain (`hA.quotient 𝔭`, `Ideal.Quotient.isDomain`
with `𝔭.IsPrime` from `Ideal.minimalPrimes_isPrime`/`minimalPrimes` ⊆ primes); T041 gives `x̄ : MaximalSpectrum (A ⧸ 𝔭)`
with `evalNorm K x̄ (mk f) = supSeminorm K (mk f)`. Lift: `x := comapPoint (Ideal.Quotient.mkₐ K 𝔭) x̄` (T005; the
instance on `A ⧸ 𝔭` is `HasSupSeminorm.quotient`), `evalNorm K x f = evalNorm K x̄ (mk f)` (`evalNorm_comapPoint`).
Chain the equalities.""",
  mathlib="""`Ideal.Quotient.isDomain`, `Ideal.minimalPrimes_isPrime`?/`minimalPrimes` membership → `IsPrime`
(`Ideal.minimalPrimes.isPrime`), `Ideal.Quotient.mkₐ`.""",
  sources="""BGR 6.2.1/4, proof (`bgr-6.2-6.3.1.md`): "Now let `A` be arbitrary. Denote by `𝔭₁, …, 𝔭_r` the minimal prime
ideals in `A`. By what we have just seen, assertions (i) and (ii) are true for the algebras `A/𝔭_i` … Thus by
Lemma 3, they must also be true for `A`."; Bosch 1.4, Prop. 14 (`bosch-lectures.txt`, "maximum modulus").""",
  gen="""`[Nontrivial A]` (the zero ring has no points); no norm on `A`.""")

t(id='T043', title='The value group: `|f|_sup^m ∈ ‖K‖` uniformly, and `|c f^m|_sup = 1` (BGR 6.2.1/4 (ii), 3.8.1/8)', file=ASUP,
  deps='T007, T022, T040', par='yes (with T044, T045)', typ='lemmas', leaves='L7.9–L7.11',
  decls=[(ASUP,'exists_forall_pow_supSeminorm_mem_range_norm_of_isDomain'),(ASUP,'exists_forall_exists_smul_pow_supSeminorm_eq_one'),
         (ASUP,'exists_smul_pow_supSeminorm_eq_one')],
  sketch="""Domain case: Noether normalisation as in T041; `n := Module.finrank (FractionRing (TateAlgebra K d)) (FractionRing A)`
(finite by Layer 1 `FractionRing.finiteDimensional_of_finite`), and `natDegree (minpoly (TateAlgebra K d) f) ≤ n` by
`minpoly.natDegree_le` over the fraction field plus `minpoly.isIntegrallyClosed_eq_field_fractions'` (degree preserved
by `map`); `hB : ∀ t, supSeminorm K t ∈ range ‖·‖`: `supSeminorm_eq_norm` + Layer 0 `norm_mem_range_norm`
(`exists_norm_coeff_eq`: the Gauss norm is a coefficient norm). T022 gives `m := n!`. General case: `𝔭 ↦ m_𝔭` for the
finitely many minimal primes (`minimalPrimes.finite_of_isNoetherianRing`), `m := ∏ m_𝔭` (`Finset.prod` over
`hfin.toFinset`, `≠ 0` as a product of nonzeros); for `f` with `|f|_sup ≠ 0`: T007 gives `𝔭` with
`|mk 𝔭 f|_sup = |f|_sup`, and `|f|_sup^m = (|mk f|_sup^{m_𝔭})^{m/m_𝔭} = ‖d‖^{m/m_𝔭} = ‖d^{m/m_𝔭}‖ =: ‖d'‖`
(`Finset.dvd_prod_of_mem`, `pow_mul`); `d' ≠ 0` since `|f|_sup ≠ 0`; `c := d'⁻¹`: `|c • f^m|_sup = ‖c‖ |f|_sup^m = 1`
(`supSeminorm_smul`, `supSeminorm_pow`, `norm_inv`). Trivial `A`: `m := 1`, vacuous. `exists_smul_pow…`: specialise.""",
  mathlib="""`minpoly.natDegree_le`, `Module.finrank`, `Finset.prod_ne_zero_iff`, `Finset.dvd_prod_of_mem`, `pow_mul`, `norm_inv`,
`norm_pow`, `inv_mul_cancel₀`; Layer 0 `MvPowerSeries.Restricted.norm_mem_range_norm`/`exists_norm_coeff_eq`; Layer 1
`FractionRing.finiteDimensional_of_finite`.""",
  sources="""BGR 6.2.1/4 (ii) and proof (`bgr-6.2-6.3.1.md`): "For all `f ∈ A` such that `|f|_sup ≠ 0`, there are `c ∈ k` and
`m ∈ ℕ` such that `|cf^m|_sup = 1`" ("assertions (i) and (ii) follow from Proposition 3.8.1/7" and "Thus by Lemma 3,
they must also be true for `A`"); BGR 3.8.1/8 (`bgr-3.8-proofs.md`); [RM] §2.2.2 for the uniform `m`; Bosch 1.4/15.""",
  gen="""Three statements: the domain-case uniform exponent, the uniform exponent for every affinoid algebra (plan D6:
`m = ∏ (n_𝔭)!`), and the pointwise BGR form. BGR's "`|A|_sup ⊂ |k_a|`" is implied and not stated separately.""")

t(id='T044', title='`|f|_sup = 0` iff `f` is nilpotent; `|·|_sup` is a norm iff `A` is reduced (BGR 6.2.1/4 (iii))', file=ASUP,
  deps='T004, T038', par='yes (with T043, T045)', typ='lemmas', leaves='L7.12–L7.14',
  decls=[(ASUP,'supSeminorm_eq_zero_iff_isNilpotent'),(ASUP,'eq_zero_of_supSeminorm_eq_zero'),(ASUP,'isReduced_of_forall_supSeminorm_eq_zero_imp')],
  sketch="""`haveI := hA.hasSupSeminorm`. T004: `supSeminorm K f = 0 ↔ f ∈ jacobson ⊥`. Affinoid algebras are Jacobson (Layer 1
`hA.isJacobsonRing`): `jacobson ⊥ = radical ⊥ = nilradical A`: `Ideal.radical_bot`?-free: `(IsJacobsonRing.out
(radical ⊥).radical_isRadical : jacobson (radical ⊥) = radical ⊥)` and `jacobson ⊥ ≤ jacobson (radical ⊥)`
(`Ideal.jacobson_mono bot_le`) with `radical ⊥ ≤ jacobson ⊥` (`Ideal.radical_le_jacobson`), so `jacobson ⊥ = radical ⊥
= nilradical A` (`nilradical_eq_radical_bot`?—`nilradical` is defined as `(⊥ : Ideal R).radical`, `rfl`), and
`mem_nilradical : f ∈ nilradical A ↔ IsNilpotent f`. `eq_zero_of…`: `IsNilpotent f → f = 0` in a reduced ring
(`IsReduced.eq_zero`/`IsNilpotent.eq_zero`). `isReduced_of…`: `⟨fun f hf ↦ h f ((iff).2 hf)⟩` (`isReduced_iff`).""",
  mathlib="""`IsJacobsonRing.out`, `Ideal.radical_isRadical`?/`Ideal.IsRadical`, `Ideal.jacobson_mono`, `Ideal.radical_le_jacobson`,
`nilradical`, `mem_nilradical`, `IsNilpotent.eq_zero`, `isReduced_iff`; Layer 1 `IsAffinoidAlgebra.isJacobsonRing`.""",
  sources="""BGR 6.2.1/4 (iii) and proof (`bgr-6.2-6.3.1.md`): "An element `f ∈ A` is nilpotent if and only if `| |_sup = 0`. In
particular, `| |_sup` is a norm on `A` if and only if `A` is reduced." / "it follows that `| |_sup` is a norm on
`red A = A/rad A`, since `rad A = ⋂ 𝔭_i`"; the Remark after 6.2.1/5: "assertion (iii) … is equivalent to the fact that
each `Tₙ` is a Jacobson ring" (our route).""",
  gen="""Three single-conclusion statements (statement-splitting rule); the Jacobson route replaces BGR's minimal-primes
route (BGR's own Remark records the equivalence).""")

t(id='T045', title='Homomorphisms of Banach algebras into reduced affinoid algebras are continuous (BGR 6.2.1/5)', file=ASUP,
  deps='T023, T038, T044', par='yes (with T043, T044)', typ='theorem', leaves='L7.15',
  decls=[(ASUP,'_root_.AlgHom.continuous_of_isReduced_of_isAffinoidAlgebra')],
  sketch="""`haveI := hA.hasSupSeminorm`; `AlgHom.continuous_of_supSeminorm_eq_zero_imp (hfin := fun x ↦
hA.finiteDimensional_quotient_of_isMaximal x.asIdeal) (hA := fun f hf ↦ hA.eq_zero_of_supSeminorm_eq_zero hf) φ` (T023, T044).""",
  mathlib="""Layer 1 `IsAffinoidAlgebra.finiteDimensional_quotient_of_isMaximal`.""",
  sources="""BGR 6.2.1/5 (`bgr-6.2-6.3.1.md`): "If `A` is a reduced `k`-affinoid algebra, then each homomorphism of a (not
necessarily Noetherian) `k`-Banach algebra into `A` is continuous." ("Combining assertion (iii) of the above
proposition with the assertion of Proposition 3.8.2/3").""",
  gen="""`B` any Banach `K`-algebra (no ultrametric/noetherian hypothesis on `B`); `A` affinoid with any complete norm,
reduced.""")

t(id='T046', title='Integral equations compute `|f|_sup` (BGR 6.2.2/4; Bosch 1.4/13), domain case then general', file=ASUP,
  deps='T007, T010, T011, T040, T044', par='no', typ='lemmas', leaves='L7.16–L7.17',
  decls=[(ASUP,'exists_monic_eval₂_eq_zero_supSeminorm_eq_supSpectralValue_of_isDomain'),(ASUP,'exists_monic_eval₂_eq_zero_supSeminorm_eq_supSpectralValue')],
  sketch="""Domain case: `A` nontrivial; Layer 1 `hB.exists_finite_injective_comp φ hfin` gives `ψ : TateAlgebra K d →ₐ[K] B` with
`φ ∘ ψ` finite and injective. With `letI := (φ.comp ψ).toAlgebra` and T040, `p := minpoly (TateAlgebra K d) f` has
`|f|_sup = σ(p)`; `q := p.map ψ` is monic (`Monic.map`), `q.eval₂ φ f = p.eval₂ (φ ∘ ψ) f = aeval f p = 0`
(`Polynomial.eval₂_map`, `minpoly.aeval`), and `σ(q) ≤ σ(p)` (T011 `supSpectralValue_map_le ψ`, instances T038) while
`|f|_sup ≤ σ(q)` (T010), so `|f|_sup = σ(q)`. General case: `haveI := hA.hasSupSeminorm`; minimal primes `𝔭_i`
(finite, nonempty); for each, `A ⧸ 𝔭_i` is an affinoid domain and `φ_i := (mkₐ K 𝔭_i).comp φ` is finite
(`RingHom.Finite.comp` with the surjection), so the domain case gives `q_i` monic with `q_i.eval₂ φ_i (mk f) = 0`,
i.e. `q_i.eval₂ φ f ∈ 𝔭_i` (`Ideal.Quotient.eq_zero_iff_mem`, `Polynomial.hom_eval₂`), and `|mk f|_sup = σ(q_i)`.
`q* := ∏ q_i` (`Finset.prod` over the finite set), `q*.eval₂ φ f ∈ ⋂ 𝔭_i = nilradical A` (`Polynomial.eval₂_prod`?/
`Polynomial.eval₂_finset_prod`, `Ideal.mul_mem_left`, `Ideal.sInf_minimalPrimes` + `Ideal.radical_bot`… `sInf (minimalPrimes A)
= (⊥).radical = nilradical A`), so some `e` with `(q*.eval₂ φ f)^e = 0` (`mem_nilradical`, `IsNilpotent`); `q := q*^e`
(monic, `eval₂_pow`). `σ(q) ≤ σ(q*) ≤ max_i σ(q_i) = max_i |mk f|_sup = |f|_sup` (T011 `pow_le`, `prod_le_of_forall_le`
with `C := |f|_sup` and `σ(q_i) = |mk 𝔭_i f|_sup ≤ |f|_sup` by T006), and `|f|_sup ≤ σ(q)` by T010.""",
  mathlib="""`Polynomial.Monic.map`, `Polynomial.eval₂_map`, `Polynomial.hom_eval₂`, `Polynomial.eval₂_finset_prod`,
`Polynomial.eval₂_pow`, `Polynomial.monic_prod_of_monic`, `Monic.pow`, `Ideal.Quotient.eq_zero_iff_mem`, `Ideal.sInf_minimalPrimes`,
`mem_nilradical`, `RingHom.Finite.comp`, `RingHom.Finite.of_surjective`; Layer 1 `IsAffinoidAlgebra.exists_finite_injective_comp`.""",
  sources="""BGR 6.2.2/4 and proof (`bgr-6.2-6.3.1.md`): "Theorem 6.1.2/1 provides us with a homomorphism `ψ: T_d → B` such that
`φ ∘ ψ … is an integral monomorphism … we have `|f|_sup = σ(p)` … Consider the polynomial `q ∈ B[X]` obtained from
`p` by replacing all its coefficients by their `ψ`-images in `B`. Clearly, `q(f) = p(f) = 0`, and `|f|_sup = σ(p) ≥
σ(q)`"; "If one defines `q* := ∏ q_i`, one gets a monic polynomial in `B[X]` such that `q*(f) ∈ ⋂ 𝔭_i = rad A`. Then
there is an exponent `e` … Setting `q := q*^e` … Proposition 1.5.4/1 gives us `σ(q) ≤ max σ(q_i) = max |π_i(f)|_sup =
|f|_sup`"; Bosch 1.4/13.""",
  gen="""`φ` finite (plan D10) instead of BGR's integral; `A` nontrivial in the general statement (BGR implicit).""")
