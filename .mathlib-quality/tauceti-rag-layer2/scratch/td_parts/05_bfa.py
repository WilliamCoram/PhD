
# ---------------------------------------------------------------- SupSeminorm/FunctionAlgebra.lean
t(id='T031', title='Banach function algebras: `|·|_sup` is a norm and is the only power-multiplicative complete norm (BGR 3.8.3/1–3)',
  file=BFA, deps='T003', par='yes (with T020–T030)', typ='lemmas', leaves='L6.1–L6.2',
  decls=[(BFA,'IsBanachFunctionAlgebra.eq_zero_of_supSeminorm_eq_zero'),(BFA,'IsBanachFunctionAlgebra.norm_eq_supSeminorm_of_isPowMul')],
  sketch="""`eq_zero_of…`: `‖f‖ ≤ C * 0 = 0` so `f = 0` (`norm_eq_zero`). `norm_eq_supSeminorm_of_isPowMul` (BGR 1.3.1/3):
`|f|_sup ≤ ‖f‖` (Layer 0) and `‖f‖^n = ‖f^n‖ ≤ C |f^n|_sup = C |f|_sup^n` for `n ≥ 1` (`hpm`, `supSeminorm_pow`),
so `‖f‖ ≤ C^(1/n) |f|_sup → |f|_sup` as `n → ∞` (as in T026: contradiction with `tendsto_pow_atTop_atTop_of_one_lt`
if `‖f‖ > |f|_sup`, after dividing; `|f|_sup = 0` forces `‖f‖ = 0`).""",
  mathlib="""`norm_eq_zero`, `IsPowMul`, `tendsto_pow_atTop_atTop_of_one_lt`, `div_pow`, `norm_nonneg`.""",
  sources="""BGR 3.8.3/1–3 (`bgr-3.8-proofs.md`): "A `k`-algebra `A` is called a Banach function algebra if `| |_sup` is a
complete norm on `A`"; "A `k`-Banach algebra `A` is a Banach function algebra if and only if `| |_sup` is equivalent
to the given norm on `A`"; "`| |_sup` is the only power-multiplicative complete `k`-algebra norm on `A`" (proof via
1.3.1/3, `bgr-1.3-1.5.md`).""",
  gen="""`IsBanachFunctionAlgebra K A := ∃ C, ∀ f, ‖f‖ ≤ C * supSeminorm K f` for a Banach `K`-algebra `A` is BGR 3.8.3/2's
characterisation (plan D3: no type synonym carrying `|·|_sup` as a `NormedRing` structure).""")

t(id='T032', title='Closed subalgebras and finite subalgebras of Banach function algebras (BGR 3.8.3/4–5)', file=BFA,
  deps='T005, T023, T030, T031', par='yes (with T033)', typ='lemmas', leaves='L6.3–L6.4',
  decls=[(BFA,'IsBanachFunctionAlgebra.of_isClosed_range'),(BFA,'IsBanachFunctionAlgebra.of_finite_injective')],
  sketch="""`of_isClosed_range`: `φ.toLinearMap.restrictScalars K`-free: `φ` is a continuous injective `K`-linear map
`B → A` with closed (hence complete) range; the open mapping theorem onto the range
(`ContinuousLinearEquiv.ofBijective` for `B ≃ range φ`, or `ContinuousLinearMap.exists_preimage_norm_le` for the
surjection `B → range φ`) gives `‖b‖ ≤ C₁ ‖φ b‖`; then `‖φ b‖ ≤ C₂ |φ b|_sup` (`hA`) and `|φ b|_sup ≤ |b|_sup`
(T005): `‖b‖ ≤ C₁ C₂ |b|_sup`. `of_finite_injective`: let `letI := φ.toAlgebra`; `Module.Finite B A` from
`hfin`; `IsScalarTower K B A` (`IsScalarTower.of_algebraMap_eq`, `φ.commutes`); `ContinuousSMul B A`
(`b • a = φ b * a`, `hφ.mul continuous_snd`… via `ContinuousSMul.mk` + `continuous_smul` unfolding
`Algebra.smul_def`); then T030 `Submodule.isClosed_of_isNoetherianRing_of_finite K (LinearMap.range
(Algebra.linearMap B A))` shows `range φ` closed; conclude with `of_isClosed_range`.""",
  mathlib="""`ContinuousLinearMap.exists_preimage_norm_le`, `IsClosed.completeSpace_coe`, `LinearMap.range`, `Algebra.linearMap`,
`RingHom.Finite`, `Module.Finite`, `IsScalarTower.of_algebraMap_eq`, `ContinuousSMul`, `Algebra.smul_def`,
`RingHom.toAlgebra`.""",
  sources="""BGR 3.8.3/4 and proof (`bgr-3.8-proofs.md`): "Applying Corollary 3.8.2/2, we see that the new norm dominates the
supremum semi-norm on `B` … by Lemma 3.8.1/4, the monomorphism `φ` is a contraction … Putting these inequalities
together"; BGR 3.8.3/5 and proof: "Since `B` is a Noetherian `k`-Banach algebra, all `B`-submodules of `A` are closed
(see Proposition 3.7.2/2); in particular, `φ(B)` is closed in `A`."
""",
  gen="""Both for Banach `B` with its own norm and continuous `φ` (BGR transport the norm along `φ`; with a given
complete norm on `B` the open mapping theorem supplies the comparison). Not used by the milestones; cheap
corollaries BGR state.""")

t(id='T033', title='Torsion-freeness of a finite domain extension; a basis of `Q(A)` over `Q(B)` with a universal denominator',
  file=BFA, deps='none', par='yes (with T020–T032)', typ='lemmas', leaves='L6.5–L6.6',
  decls=[(BFA,'Module.isTorsionFree_of_faithfulSMul_of_isDomain'),(BFA,'exists_basis_universalDenominator')],
  sketch="""`isTorsionFree`: `Module.IsTorsionFree B A` unfolds to `∀ b ≠ 0, Injective (b • ·)`/no zero smul divisors
(check the current definition: `Module.IsTorsionFree R M : ∀ {r : R} {m : M}, r • m = 0 → r = 0 ∨ m = 0`?);
`b • a = algebraMap b * a = 0` in the domain `A` gives `algebraMap b = 0` (so `b = 0` by `FaithfulSMul.algebraMap_injective`)
or `a = 0`. `exists_basis_universalDenominator`: `L := FractionRing A` is finite-dimensional over
`F := FractionRing B` (Layer 1 `FractionRing.finiteDimensional_of_finite B A` with the `Algebra F L` instance
`FractionRing.liftAlgebra`? — Layer 1 states it with `[Algebra (FractionRing R) (FractionRing S)]
[IsScalarTower R (FractionRing R) (FractionRing S)]` as hypotheses: supply `FractionRing.liftAlgebra` and
`FractionRing.isScalarTower_liftAlgebra`). Take a basis `v` of `L` over `F` (`Module.Basis.ofVectorSpace`),
`n := finrank`; clear denominators: each `v i = algebraMap (a i) / algebraMap (s i)` with `s i ∈ nonZeroDivisors A`
(`IsFractionRing.div_surjective`/`IsLocalization.mk'_surjective`); replacing `v i` by `s i • v i` keeps linear
independence over `F` (scaling by units), so WLOG `v i = algebraMap A L (a i)` with `a i ∈ A`; `LinearIndependent B a`
follows from linear independence over `F` by restricting scalars (`LinearIndependent.restrict_scalars`-type with
`algebraMap B F` injective). Universal denominator: `A` is a finite `B`-module with generators `g j`
(`Module.Finite.exists_fin`); each `algebraMap A L (g j) = ∑ (β_ij / d_ij) v i` with `β_ij ∈ B`, `d_ij ∈ B∖0`
(`IsLocalization.exist_integer_multiples_of_finset`-style: `IsLocalization.exist_integer_multiples` on the finite
set of coordinates gives ONE `b ∈ nonZeroDivisors B` with `b • coord ∈ B` for all); take `b := ∏ d_ij` (or the
witness of `exist_integer_multiples` over the finite family of all coordinates of all `g j`); for general
`f = ∑ c_j g_j` (`c_j ∈ B`), `b • f = ∑ c_j (b • g_j) ∈ ∑ B a_i` with `B`-coefficients, and the identity
`b • f = ∑ β_i • a_i` in `L` descends to `A` (`IsFractionRing.injective A L`).""",
  mathlib="""`Module.IsTorsionFree`, `FaithfulSMul.algebraMap_injective`, `Module.Basis.ofVectorSpace`, `FractionRing.liftAlgebra`,
`FractionRing.isScalarTower_liftAlgebra`, `IsFractionRing.div_surjective`, `IsLocalization.mk'_surjective`,
`IsLocalization.exist_integer_multiples`, `IsLocalization.IsInteger`, `LinearIndependent.map'`/`restrict_scalars`,
`Module.Finite.exists_fin`, `IsFractionRing.injective`; Layer 1 `FractionRing.finiteDimensional_of_finite`.""",
  sources="""BGR 3.8.3/7, proof (`bgr-3.8-proofs.md`): "Let `a₁, …, aₙ` be a `Q(B)`-basis of `Q(A)`. Because `φ` is finite, there is a
universal denominator `b ∈ B − {0}` such that `A ⊂ A' := Σ B a_i/b ⊂ Q(A)`"; BGR 3.8.1/7 preliminaries: "Since `A`
is torsion-free over `B`, we have a commutative diagram of inclusions `B ⊂ A`, `Q(B) ⊂ Q(A)`".""",
  gen="""Pure algebra (`K` unused, dropped): `B`, `A` domains, `A` finite over `B`, `FaithfulSMul B A`. `n` is left
existential (it equals `finrank (FractionRing B) (FractionRing A)`).""")

t(id='T034', title='The coordinate map `A → Bⁿ`: injective, closed range, and `‖f‖ ≤ C ‖θ f‖` (closed graph + open mapping)',
  file=BFA, deps='T029, T033', par='no', typ='lemmas', leaves='L6.7–L6.8',
  decls=[(BFA,'exists_coordinateMap'),(BFA,'exists_norm_le_mul_norm_coordinateMap')],
  sketch="""`exists_coordinateMap`: define `θ f := Classical.choose (hA f)`; uniqueness of the coefficients from
`LinearIndependent B a` (`LinearIndependent.eq_coords_of_eq`/`linearIndependent_iff'`: `∑ (β - β') i • a i = 0 →
β = β'`) makes `θ` additive and `B`-linear (`b' • f` has coefficients `b' • θ f` by uniqueness); injective: `θ f = 0 →
b • f = 0 → f = 0` (torsion-free, T033); `range θ` is a `B`-submodule (`LinearMap.range θ`) of `Fin n → B`, closed
by T029 (`Submodule.isClosed_of_isNoetherianRing_pi K`, `B` noetherian Banach). `exists_norm_le_mul_norm…`:
`θ' := θ.restrictScalars K` (K-linear: `k • f = algebraMap K B k • f` by `IsScalarTower`); closed graph
(`LinearMap.continuous_of_isClosed_graph`): if `(f_k, θ f_k) → (f, v)` then `b • f_k → b • f` (`continuous_const_smul`)
and `∑ θ f_k i • a i = ∑ algebraMap (θ f_k i) * a i → ∑ algebraMap (v i) * a i` (`hcont`, `continuous_finset_sum`),
so `b • f = ∑ v i • a i` and `θ f = v` by uniqueness: the graph is sequentially closed hence closed (metric). Then
`θ'` is a continuous injective `K`-linear map with closed range; open mapping (`ContinuousLinearMap.exists_preimage_norm_le`
on `A → range θ'`, a Banach space) gives `‖f‖ ≤ C ‖θ f‖`.""",
  mathlib="""`linearIndependent_iff'`, `LinearMap.range`, `LinearMap.continuous_of_isClosed_graph`, `isClosed_of_closure_subset`,
`IsSeqClosed.isClosed`, `continuous_const_smul`, `continuous_finset_sum`, `Algebra.smul_def`,
`ContinuousLinearMap.exists_preimage_norm_le`, `IsClosed.completeSpace_coe`, `LinearMap.restrictScalars`;
`Submodule.isClosed_of_isNoetherianRing_pi` (T029).""",
  sources="""BGR 3.8.3/7, proof (`bgr-3.8-proofs.md`): "we get a complete finite (and hence Noetherian) `B`-module if we restrict
`| |_sp` to `A'`. By Proposition 3.7.2/2, the `B`-submodule `A` of `A'` is closed with respect to the restriction of
`| |_sp`. Because `A'` is complete, `A` is complete and hence a `k`-Banach algebra"; the comparison with the given
norm is BGR 3.8.2/4 ("all complete `k`-algebra norms on `A` are equivalent", here through the closed graph
theorem as in 3.8.2/3's proof).""",
  gen="""`K` explicit (`variable (K) in include K in`): the closed-graph and open-mapping steps need the field of scalars
(Layer 1 B2 precedent). `hcont : Continuous (algebraMap B A)` replaces BGR's construction of the topology of `A`
from `A'` (with a given norm on `A` the continuity is needed to compare, see plan §5.5).""")

t(id='T035', title='The spectral norm of `Q(A)` over `Q(B)` restricts to `|·|_sup` on `A` (BGR 3.8.3/7, "`|f|_sup = |f|_sp`")',
  file=BFA, deps='T019, T009', par='yes (with T034, T036)', typ='lemma', leaves='L6.9',
  decls=[(BFA,'spectralNorm_fractionRing_eq_supSeminorm')],
  sketch="""`letI := IsFractionRing.normedField B (FractionRing B)` (needs `NormMulClass B`, Layer 0). For `f : A`, `y := algebraMap A
(FractionRing A) f` is integral over `B` (`IsIntegral.algebraMap`-type: `f` integral since `Module.Finite B A`,
`Algebra.IsIntegral.isIntegral f`, then map along `A → FractionRing A`: `IsIntegral.map`). `minpoly (FractionRing B) y =
(minpoly B y).map (algebraMap B (FractionRing B))` (`minpoly.isIntegrallyClosed_eq_field_fractions'` with `R := B`,
`K := FractionRing B`, `S := FractionRing A`, the scalar tower instance given) and `minpoly B y = minpoly B f`
(`minpoly.algHom_eq` for the injective `IsScalarTower.toAlgHom B A (FractionRing A)`). `spectralNorm (FractionRing B) _ y
= spectralValue (minpoly _ y)`; its terms are `‖algebraMap (coeff i)‖^(1/(d-i))` with `‖algebraMap B (FractionRing B) b‖
= ‖b‖` (Layer 0 `IsFractionRing.normAbsoluteValue_algebraMap`, `natDegree_map`, `coeff_map`), `= |coeff i|_sup^(1/(d-i))`
(`hBsup`), i.e. `spectralValue = supSpectralValue K (minpoly B f)` termwise (T009 `supSpectralValue_eq_spectralValue`-style
`congrArg iSup`), `= supSeminorm K f` by M1 (T019: `A` domain, integral over `B` (finite), torsion-free (T033),
`HasSupSeminorm` on both).""",
  mathlib="""`IsFractionRing.normedField` (Layer 0), `IsFractionRing.normAbsoluteValue_algebraMap` (Layer 0),
`minpoly.isIntegrallyClosed_eq_field_fractions'`, `minpoly.algHom_eq`, `IsIntegral.map`, `Algebra.IsIntegral.isIntegral`,
`Module.Finite` → `Algebra.IsIntegral` (`Algebra.IsIntegral.of_finite`), `spectralNorm`, `spectralValueTerms`,
`Polynomial.coeff_map`, `Polynomial.natDegree_map_eq_of_injective`.""",
  sources="""BGR 3.8.3/7, proof end (`bgr-3.8-proofs.md`): "From Proposition 3.8.1/7 (a), we derive `|f|_sup = |f|_sp` for all
`f ∈ A`"; BGR Remark after 3.8.1/9: "The spectral norm on `Q(A)` considered as a `Q(B)`-algebra yields — if
restricted to `A` — the supremum norm on `A` considered as a `k`-algebra".""",
  gen="""`B` a valued (`NormMulClass`) domain with `|·|_sup = ‖·‖` (BGR: "`B` is a valued integrally closed Noetherian
`k`-Banach algebra"); the `Algebra (FractionRing B) (FractionRing A)` instance and the tower are hypotheses
(instantiate with `FractionRing.liftAlgebra`).""")

t(id='T036', title='Weak stability bounds the coordinates by `|·|_sup`', file=BFA, deps='T033, T035', par='no', typ='lemma',
  leaves='L6.10', decls=[(BFA,'exists_norm_coordinateMap_le_mul_supSeminorm')],
  sketch="""`F := FractionRing B` (normed by `IsFractionRing.normedField`, ultrametric by Layer 0 `IsFractionRing.isUltrametricDist`),
`L := FractionRing A` with `Algebra F L` (`FractionRing.liftAlgebra`), finite-dimensional (Layer 1). The family
`algebraMap A L ∘ a` is linearly independent over `F` (from `LinearIndependent B a` by clearing denominators:
`LinearIndependent.localization`-type / `linearIndependent_iff'` with `IsLocalization.exist_integer_multiples`) and
spans `L`: every `y ∈ L` is `(algebraMap f)/(algebraMap g)` with `f ∈ A`, `g ∈ A∖0`… — spanning is NOT needed: extend
to a basis `v` of `L` (`LinearIndependent.extend`/`Basis.extend`) whose first `n` vectors are the `a i`; the
coordinate functionals `ψ i := v.coord i : L →ₗ[F] F`. Weak stability `hws` gives `C_i` with `‖ψ i z‖ ≤ C_i *
spectralNorm F L z`. For `f : A`: `algebraMap (b • f) = ∑ algebraMap (θ f i) • a i`, so `ψ i (algebraMap (b • f))
= algebraMap B F (θ f i)` for `i < n` (and `0` beyond), hence `‖θ f i‖ = ‖ψ i (algebraMap (b•f))‖ ≤ C_i
spectralNorm F L (algebraMap (b • f)) = C_i ‖b‖ spectralNorm F L (algebraMap f)` (the spectral norm is
`F`-multiplicative: `spectralNorm_smul`/`spectralAlgNorm` with `‖algebraMap b‖ = ‖b‖`) `= C_i ‖b‖ |f|_sup` (T035).
`C := ‖b‖ * max_i C_i` (`Finset.sup'`), and `‖θ f‖ = max_i ‖θ f i‖` (`pi_norm_le_iff_of_nonneg`).""",
  mathlib="""`IsWeaklyStable` (Layer 0: `∀ L [Field L] [Algebra K L] [FiniteDimensional K L] (φ : L →ₗ[K] K), ∃ C, ∀ y, ‖φ y‖ ≤ C *
spectralNorm K L y`), `Module.Basis.extend`, `Module.Basis.coord`, `LinearIndependent.localization`?,
`spectralNorm_smul`, `pi_norm_le_iff_of_nonneg`, `Finset.sup'`, `Finset.le_sup'`; Layer 0 `IsFractionRing.isUltrametricDist`.""",
  sources="""BGR 3.8.3/7, proof (`bgr-3.8-proofs.md`): "Since `Q(B)` is weakly stable, all these extensions are weakly
`Q(B)`-cartesian under their spectral norm. Then `Q(A)`, provided with its spectral norm, is weakly `Q(B)`-cartesian
(use Theorem 3.2.2/2). Let `a₁, …, aₙ` be a `Q(B)`-basis of `Q(A)` … Since `| |_sp` induces the `Q(B)`-product
topology on `Q(A)`"; the definition of weak stability (`bgr-4-and-3.8.3.7.md` / Layer 0 `WeaklyStable.lean`):
"weakly cartesian = the coordinate functionals are bounded by the spectral norm".""",
  gen="""Universe: `A` and `B` in one universe `u` (plan D12). `A` is a domain so `Q(A)` is a field and `IsWeaklyStable`
applies directly (BGR's Dedekind decomposition for reduced `A` is D1).""")

t(id='T037', title='BGR 3.8.3/7 (domain case): a finite domain over a weakly-stable valued Banach function algebra is one', file=BFA,
  deps='T034, T036', par='no', typ='theorem', leaves='L6.11', decls=[(BFA,'IsBanachFunctionAlgebra.of_finite_domain')],
  sketch="""Assemble: T033 gives `n, a, b`; T034 gives `θ` and `‖f‖ ≤ C₁ ‖θ f‖`; T036 gives `‖θ f‖ ≤ C₂ |f|_sup`
(instances: `HasSupSeminorm K A` from T013 `of_isIntegral` over `B`; `Algebra (FractionRing B) (FractionRing A)` and
the tower via `FractionRing.liftAlgebra`/`FractionRing.isScalarTower_liftAlgebra`, `Module.IsTorsionFree` from T033).
`⟨C₁ * C₂, fun f ↦ by nlinarith/calc⟩`.""",
  mathlib="""`FractionRing.liftAlgebra`, `FractionRing.isScalarTower_liftAlgebra`, `mul_assoc`, `mul_le_mul_of_nonneg_left`.""",
  sources="""BGR 3.8.3/7 (`bgr-3.8-proofs.md`), statement and proof; the domain restriction is plan D1.""",
  gen="""`B` valued (`NormMulClass`), integrally closed, noetherian, Banach with `|·|_sup = ‖·‖` and `HasSupSeminorm`,
weakly stable fraction field; `A` a domain, finite over `B` with injective continuous structure map, any complete
`K`-algebra norm. Conclusion: `‖f‖ ≤ C |f|_sup` (= Banach function algebra, D3).""")
