
# ---------------------------------------------------------------- Affinoid/SupExamples.lean
t(id='T065', title='Examples in `Tₙ`: `|Xᵢ|_sup = 1`, `|m|_sup = ‖m‖`, `X` power-bounded, `c • X` topologically nilpotent', file=EX,
  deps='T003, T038, T048, T049', par='yes (with T066–T069)', typ='lemmas', leaves='L12.1–L12.4',
  decls=[(EX,'supSeminorm_X'),(EX,'supSeminorm_natCast'),(EX,'isPowerBounded_X'),(EX,'isTopologicallyNilpotent_smul_X')],
  sketch="""`supSeminorm_X`: `supSeminorm_eq_norm` (Layer 0) + `Affinoid.TateAlgebra.norm_X` (Layer 1 `TateAlgebra/Examples.lean`).
`supSeminorm_natCast`: `(m : Tₙ) = algebraMap K _ (m : K)` (`map_natCast`), `supSeminorm_algebraMap` (`Nontrivial Tₙ`).
`isPowerBounded_X`: Layer 1 `MvPowerSeries.Restricted.isPowerBounded_X` (Affinoid/Extend.lean) or T048 with `supSeminorm_X`.
`isTopologicallyNilpotent_smul_X`: T049 (`|c • X|_sup = ‖c‖ < 1`) or directly `‖(c • X)^n‖ = ‖c‖^n → 0`.""",
  mathlib="""`map_natCast`, `norm_smul`, `norm_pow`; Layer 1 `Affinoid.TateAlgebra.norm_X`, `MvPowerSeries.Restricted.isPowerBounded_X`.""",
  sources="""[RM] Examples ("`|X|_sup = 1` and `|p|_sup = p⁻¹` in `ℚ_p⟨X⟩` … `X` is power-bounded and `pX` is topologically nilpotent in
`K⟨X⟩`").""",
  gen="""Over any `K`; the `ℚ_p` instances follow by specialisation (`‖(p : ℚ_p)‖ = p⁻¹` is Mathlib `padicNormE.norm_p`).""")

t(id='T066', title='Examples in quotients of `K⟨X⟩`: `(X − a)`, `(X²)`, `(X² − a)`', file=EX, deps='T016, T017, T044, T052', par='yes (with T065, T067–T069)',
  typ='lemmas', leaves='L12.5–L12.9',
  decls=[(EX,'supSeminorm_mk_X_span_X_sub_C'),(EX,'supSeminorm_mk_X_span_X_sq'),(EX,'norm_mk_X_span_X_sq'),
         (EX,'not_isBounded_powerBounded_span_X_sq'),(EX,'supSeminorm_mk_X_span_X_sq_sub_C')],
  sketch="""`(X − a)`: Layer 1 `Affinoid/Examples.lean` has `ker_aeval_eq_span (ha : ‖a‖ ≤ 1) : RingHom.ker (eval at a) = span {X − C a}`
and `nonempty_algEquiv_quotient_X_sub`: the quotient is `≃ₐ[K] K` with `mk X ↦ a`; the unique point of `K` gives
`supSeminorm K (mk X) = ‖a‖` (T015 `supSeminorm_eq_spectralNorm` on `K`, transported along the `AlgEquiv` by
`supSeminorm_map_le` both ways, `spectralNorm_extends`). `(X²)`: `(mk X)^2 = mk (X^2) = 0` so `mk X` is nilpotent and
`|mk X|_sup = 0` (T044 with `tateAlgebra_quotient`). `norm_mk_X_span_X_sq`: the residue norm of `mk X` is
`inf_{g} ‖X + g X²‖` (Layer 1 `exists_norm_quotient_mk_eq`/`norm_quotient_mk_le`); `‖X + g X²‖ ≥ ‖coeff₁(X + gX²)‖ = 1`
(`norm_coeff_le`, the `X`-coefficient of `g X²` is `0`), and `‖X‖ = 1`: use `Ideal.Quotient.norm_mk_eq_norm_of_forall_le`
(Layer 1 NormedQuotient: `(∀ a ∈ I, ‖f‖ ≤ ‖f - a‖) → ‖mk f‖ = ‖f‖`). `not_isBounded…`: `isReduced_of_isBounded_powerBounded`
(T052) would make `T₁ ⧸ (X²)` reduced, but `mk X` is a nonzero nilpotent (`mk X ≠ 0` since `X ∉ span {X²}`: degree/coefficient
argument, e.g. by the residue norm `1 ≠ 0` from the previous lemma). `(X² − a)`: Layer 1 `isAffinoidAlgebra_quotient_X_sq_sub`
and (for `‖a‖ < 1`) `finrank_quotient_X_sq_sub`; in general `T₁ ⧸ (X² − C a) ≃ₐ[K] AdjoinRoot (X² − C a : K[X])` by
Weierstrass division (Layer 0 `TateAlgebra/Distinguished.lean`/`Finiteness.lean`: `X² − a` is `X`-distinguished of degree 2 for
`‖a‖ ≤ 1`; or Layer 1's `exists_algEquiv_quotient_X_norm_eq`-type lemma — check `Affinoid/Examples.lean` lines 56–130 for the
exact available statements). Then T016/T017 on `AdjoinRoot (X² − C a)` over `L := K`: `sup = supSpectralValue K (X² − C a) =
‖a‖^(1/2)` (the only nonzero term: coefficient `-a` at index `0`, exponent `1/2`, `supSeminorm_neg`, `supSeminorm_algebraMap`).""",
  mathlib="""`Ideal.Quotient.eq_zero_iff_mem`, `Ideal.mem_span_singleton`, `IsNilpotent`, `spectralNorm_extends`, `Real.rpow_natCast`;
Layer 1 `Affinoid.Examples.ker_aeval_eq_span`, `nonempty_algEquiv_quotient_X_sub`, `isAffinoidAlgebra_quotient_X_sq_sub`,
`exists_norm_quotient_mk_eq`, `Ideal.Quotient.norm_mk_eq_norm_of_forall_le`; Layer 0 Weierstrass division
(`TateAlgebra/Distinguished.lean`, `TateAlgebra/Finiteness.lean`).""",
  sources="""[RM] Examples ("`|X|_sup = |a|` in `K⟨X⟩/(X − a)`; the nilpotent `ε` in `K⟨X⟩/(X²)` has `|ε|_sup = 0` and residue norm `1`;
in `K⟨X⟩/(X² − p)` the element `X` has `|X|_sup = p^{−1/2} ∉ |K^×|`; … `K⟨X⟩/(X²)` is not uniform").""",
  gen="""`a` with `‖a‖ ≤ 1` (the ideals must be proper and `X`-distinguished); the "`∉ |ℚ_p^×|`" remark is not formalised
(it is immediate from `‖a‖^{1/2}` with `‖p‖ = p⁻¹`).""")

t(id='T067', title='The annulus algebra `K⟨X, Y⟩/(XY − c)`: `|f₁|_sup = |f₂|_sup = 1`, `|f₁f₂|_sup = ‖c‖` (BGR 6.2.3, example)', file=EX,
  deps='T002, T038', par='yes (with T065, T066, T068, T069)', typ='lemmas', leaves='L12.10–L12.13',
  decls=[(EX,'supSeminorm_mk_X_annulus'),(EX,'supSeminorm_mk_Y_annulus'),(EX,'supSeminorm_mk_X_mul_Y_annulus'),(EX,'not_forall_supSeminorm_mul_annulus')],
  sketch="""Points: the evaluation `ev₁ : T₂ →ₐ[K] K` at `(1, c)` (Layer 1 `extendAlgHom (Algebra.ofId K K) _ ![1, c] _` with
`‖1‖, ‖c‖ ≤ 1`; `extendAlgHom_X`) kills `XY − C c` (`1 · c − c = 0`), so it factors through `A := T₂ ⧸ annulusIdeal c`
(`Ideal.Quotient.liftₐ`), giving `ψ₁ : A →ₐ[K] K` with `ψ₁ (mk X) = 1`; its kernel is a maximal ideal `x₁` (Layer 0
`isMaximal_ker_of_isAlgebraic`) with `evalNorm K x₁ (mk X) = ‖ψ₁ (mk X)‖ = 1` (Layer 0 `evalNorm_eq_norm_algHom` with `L := K`).
Hence `|mk X|_sup ≥ 1`; and `≤ 1` by T038 `supSeminorm_le_norm_of_eq` with `‖X‖ = 1`. Symmetric for `Y` at `(c, 1)`.
`mk X * mk Y = mk (X Y) = mk (C c) = algebraMap K A c` (`XY − C c ∈ annulusIdeal`, `Ideal.Quotient.eq`), and
`|algebraMap c|_sup = ‖c‖` needs `Nontrivial A`, i.e. `annulusIdeal c ≠ ⊤`: `XY − C c` is not a unit of `T₂` (Layer 0
`isUnit_iff_norm_coeff_lt`: a unit has a dominant constant term; here `‖coeff_{XY}‖ = 1 ≥ ‖c‖`), so `span ≠ ⊤`
(`Ideal.span_singleton_eq_top`). `not_forall…`: `1 * 1 = 1 ≠ ‖c‖` when `‖c‖ < 1`.""",
  mathlib="""`Ideal.Quotient.liftₐ`, `Ideal.Quotient.eq`, `Ideal.mem_span_singleton_self`, `Ideal.span_singleton_eq_top`, `isUnit_iff_exists`;
Layer 1 `MvPowerSeries.Restricted.extendAlgHom`, `extendAlgHom_X`; Layer 0 `Affinoid.isMaximal_ker_of_isAlgebraic`,
`Affinoid.evalNorm_eq_norm_algHom`, `MvPowerSeries.Restricted.isUnit_iff_norm_coeff_lt`.""",
  sources="""BGR 6.2.3, the example after 6.2.3/5 (`bgr-6.2-6.3.1.md`): "The ideals `(X − 1, Y − c)` and `(X − c, Y − 1)` are maximal
ideals in `k⟨X, Y⟩` containing the ideal `(XY − c)` … Since `f₁(x₁) = 1 = f₂(x₂)`, we see that `|f₁|_sup = 1 = |f₂|_sup`.
However `|f₁f₂|_sup = |c|_sup = |c| < 1`. Consequently, `| |_sup` cannot be a valuation on `A`."
""",
  gen="""Our points are kernels of evaluation maps (no need to show `(X − 1, Y − c)` is maximal in `T₂`); that `A` is a domain
is plan D4 (not formalised).""")

t(id='T068', title='BGR 6.3.1 Example 2: `T₁ → K × K`, `X ↦ (c, 0)` is surjective but its reduction is not', file=EX,
  deps='T038, T044, T060', par='yes (with T065–T067, T069)', typ='lemmas+def', leaves='L12.14–L12.18',
  decls=[(EX,'isAffinoidAlgebra_prod'),(EX,'prodHom'),(EX,'prodHom_X'),(EX,'surjective_prodHom'),(EX,'not_surjective_reductionMap_prodHom')],
  sketch="""Instances on `K × K`: `Prod.normedCommRing`, `Prod.normedAlgebra`, `Prod.completeSpace`, PFA `Prod.instIsUltrametricDist`,
`Prod.normOneClass`. `prodHom`'s field: `‖(c, 0)‖ = max ‖c‖ 0 ≤ 1` (`Prod.norm_def`). `prodHom_X`: `extendAlgHom_X`.
`isAffinoidAlgebra_prod`: `IsAffinoidAlgebra.of_surjective (tateAlgebra 1) (prodHom K (c := 1) …)`-free: use the map with
`c := 1` (`‖1‖ ≤ 1`) and `surjective_prodHom` for `c = 1`, so first prove surjectivity for any `c ≠ 0`: `(1, 0) = φ (c⁻¹ • X)`
(`map_smul`, `prodHom_X`, `Prod.smul_mk`) and `(0, 1) = φ 1 - φ (c⁻¹ • X)`; `(u, v) = u • (1,0) + v • (0,1)` (`Prod.ext`).
`not_surjective_reductionMap…`: suppose `φ̃` surjective. The element `τ(1, 0) ∈ Reduction K (K × K)` (`(1,0) ∈ Å`:
`|(1,0)|_sup ≤ ‖(1,0)‖ = 1`) has a preimage `τ(g)`, `g ∈ T̊₁`; write `g = C g₀ + X h` (`Layer 0: coefficient extraction`:
`g - C (coeff 0 g)` is divisible by `X` in `T₁`: `MvPowerSeries.Restricted` shift… — alternative route avoiding division:
`|φ g - algebraMap (g₀)|_sup < 1` where `g₀ := coeff 0 g`: since `φ g = (g(c), g(0)) = (Σ gₙ cⁿ, g₀)` (`extendAlgHom_apply`:
`φ g = ∑ gₙ (c,0)ⁿ` as a convergent sum), `φ g - (g₀, g₀) = (Σ_{n≥1} gₙ cⁿ, 0)` has norm `≤ max_{n≥1} ‖gₙ‖ ‖c‖ⁿ ≤ ‖c‖ < 1`
(`‖gₙ‖ ≤ 1`); so `τ(φ̊ g) = τ(algebraMap g₀ · 1)`, i.e. `φ̃(τ g) ∈ range (Reduction.ofResidueField)`; but `τ(1, 0)` is not
in that range: `(1, 0) - (a, a) ∈ Ǎ` would give `‖(1 - a, -a)‖ < 1`, i.e. `‖1 - a‖ < 1` and `‖a‖ < 1`, contradicting
`‖1‖ = 1 ≤ max` (`IsUltrametricDist.norm_add_le_max`). (`|·|_sup` on `K × K` is `‖·‖`: two points, residue fields `K`;
prove `supSeminorm K (u, v) = max ‖u‖ ‖v‖` via the two projections as `AlgHom`s to `K` and Layer 0 `evalNorm_eq_norm_algHom`,
plus `supSeminorm_le_norm`.)""",
  mathlib="""`Prod.normedCommRing`, `Prod.normedAlgebra`, `Prod.norm_def`, `Prod.normOneClass`, `Prod.ext`, `Prod.smul_mk`, `map_smul`,
`IsUltrametricDist.norm_add_le_max`; PFA `Prod.instIsUltrametricDist`; Layer 1 `extendAlgHom`, `extendAlgHom_X`,
`extendAlgHom_apply` (the sum formula), `IsAffinoidAlgebra.of_surjective`; Layer 0 `evalNorm_eq_norm_algHom`.""",
  sources="""BGR 6.3.1 Example 2 (`bgr-6.2-6.3.1.md`): "Set `B := T₁ = k⟨X⟩` and `A := k ⊕ k` (ring-theoretic normed direct sum of
two copies of `k`). Choose a constant `c ∈ k`, `0 < |c| < 1`, and consider the homomorphism `φ: B → A`, `X ↦ (c, 0)`. It
is easily verified that `φ` is surjective. However `φ̃: k̃[X] → k̃ ⊕ k̃` cannot be surjective, since `|φ(X)|_sup = |c| < 1`
and hence `φ̃(X) = 0`."
""",
  gen="""`K × K` with the sup norm is BGR's "ring-theoretic normed direct sum"; `0 < ‖c‖ < 1` split into `hc0` (surjectivity)
and `hc : ‖c‖ < 1` (non-surjectivity of the reduction).""")

t(id='T069', title='BGR 6.3.1 Example 1 (hypothesis form, plan D5): finite extensions are affinoid, `K̃ → L̃` is injective, `K → L` is not surjective',
  file=EX, deps='T038, T061', par='yes (with T065–T068)', typ='lemmas', leaves='L12.19–L12.21',
  decls=[(EX,'isAffinoidAlgebra_of_finiteDimensional'),(EX,'injective_reductionMap_ofId'),(EX,'not_surjective_algebraMap_of_one_lt_finrank')],
  sketch="""`isAffinoidAlgebra_of_finiteDimensional`: `letI := spectralNorm.normedField K L; letI := spectralNorm.normedAlgebra K L`
(Layer 0 pattern; `IsUltrametricDist L`, `CompleteSpace L` by `spectralNorm.completeSpace`); a `K`-basis `v` of `L`
(`Module.finBasis`), scaled into the unit ball (`c • v i` with `‖c • v i‖ ≤ 1`, `NontriviallyNormedField.exists_norm_lt`-type
scaling, Layer 1 `exists_forall_norm_smul_le_one`); `extendAlgHom (Algebra.ofId K L) _ (scaled basis) _ : Tₙ →ₐ[K] L` is
surjective (its range is a `K`-subspace containing a basis: `Submodule.span_eq_top`), so `IsAffinoidAlgebra.of_surjective
(tateAlgebra n)`. `injective_reductionMap_ofId`: T061 `injective_reductionMap_iff_isometry` with `|algebraMap c|_sup = ‖c‖ =
|c|_sup` (`supSeminorm_algebraMap`, T015 on the fields `K` and `L`: `supSeminorm K c = spectralNorm K K c = ‖c‖`).
`not_surjective_algebraMap…`: a surjective `algebraMap K L` makes `L` one-dimensional (`finrank_eq_one_iff_of_nonzero'`/
`Module.finrank_le_one_iff`), contradicting `1 < finrank`.""",
  mathlib="""`spectralNorm.normedField`, `spectralNorm.normedAlgebra`, `spectralNorm.completeSpace`, `Module.finBasis`, `Submodule.span_eq_top`?,
`Module.finrank_le_one_iff`, `Algebra.ofId`; Layer 1 `extendAlgHom`, `exists_forall_norm_smul_le_one`, `IsAffinoidAlgebra.of_surjective`.""",
  sources="""BGR 6.3.1 Example 1 (`bgr-6.2-6.3.1.md`): "viewing `k` and `K` as `k`-affinoid algebras, the injection `φ: k ↪ K` is a
homomorphism of `k`-affinoid algebras which is not surjective. However, the residue homomorphism `φ̃: k̃ → K̃` is bijective,
since `f(K/k) = 1`."; plan D5 for the hypothesis form.""",
  gen="""Bijectivity of `φ̃` under "residue degree `1`" is not stated (it would need the identification `Reduction K L ≃+* L̃`);
injectivity holds unconditionally (an isometry), non-surjectivity of `φ` for `[L : K] > 1`.""")

t(id='T070', title='Chain-root gate: import `Affinoid.SupExamples` into `PhD/TauCeti.lean`, full build, lint, axioms', file='PhD/TauCeti.lean',
  deps='T001–T069, all CLEANUP-* of the twelve files', par='no', typ='gate', leaves='—',
  decls=[], statement_override="""-- PhD/TauCeti.lean: add
import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.SupExamples
-- then: ~/.elan/bin/lake build PhD.TauCeti   (no warnings, no sorries)
--       lake exe runLinter on each of the twelve Layer 2 modules
--       python3 .mathlib-quality/tauceti-rag-layer2/scratch/axioms.py on M1–M5""",
  sketch="""1. Add the import line (alphabetical position after `Affinoid.Examples`). 2. `lake build PhD.TauCeti` must report no
`sorry` and no warnings. 3. `lake exe runLinter PhD.TauCeti.Code.RigidAnalyticGeometry.<Module>` for the twelve modules.
4. `#print axioms` on `Affinoid.supSeminorm_eq_supSpectralValue_minpoly`, `IsAffinoidAlgebra.exists_evalNorm_eq_supSeminorm`,
`IsAffinoidAlgebra.isPowerBounded_iff_supSeminorm_le_one`, `IsAffinoidAlgebra.supSeminorm_eq_smoothingFun`,
`IsAffinoidAlgebra.isBanachFunctionAlgebra_of_isReduced`, `IsAffinoidAlgebra.isStrictMap_of_isometry` — standard only.
5. Never `import PhD.Main.*` (grep the twelve files).""",
  mathlib="""—""", sources="""[RM] Layer 2 dependencies; `tauceti-rag-layer1` gate ticket T064 (precedent).""",
  gen="""The chain root imports only the leaf file (it transitively imports the whole layer).""")
