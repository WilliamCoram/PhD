
# ---------------------------------------------------------------- SupSeminorm/Integral.lean
t(id='T012', title='Going up for maximal ideals along an integral map; residue fields stay algebraic',
  file=INT, deps='none', par='yes (with T001–T011, T028)', typ='lemmas', leaves='L3.1–L3.3',
  decls=[(INT,'exists_comap_algebraMap_eq'),(INT,'isMaximal_comap_algebraMap_of_isIntegral'),
         (INT,'isAlgebraic_quotient_of_isAlgebraic_quotient_comap')],
  sketch="""`exists_comap_algebraMap_eq`: `Ideal.exists_ideal_over_maximal_of_isIntegral y.asIdeal` with
`RingHom.ker (algebraMap B A) ≤ y.asIdeal` from `RingHom.ker_eq_bot_iff_eq_zero`/`FaithfulSMul`
(`(FaithfulSMul.algebraMap_injective B A)`, `RingHom.injective_iff_ker_eq_bot`), giving `Q` maximal with
`comap Q = y`; package `⟨Q, hQ⟩`. `isMaximal_comap_algebraMap_of_isIntegral`:
`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal x.asIdeal`. `isAlgebraic_quotient…`: with
`letI := Ideal.Quotient.algebraQuotientOfLEComap le_rfl : Algebra (B ⧸ comap) (A ⧸ x)` and
`Algebra.IsIntegral.quotient : Algebra.IsIntegral (B ⧸ comap) (A ⧸ x)`, the tower `K → B ⧸ comap → A ⧸ x`
is a scalar tower (`IsScalarTower.of_algebraMap_eq`, both maps are induced by `algebraMap`), so
`Algebra.IsAlgebraic.trans` (integral ⇒ algebraic: `Algebra.IsIntegral.isAlgebraic`) gives
`Algebra.IsAlgebraic K (A ⧸ x)`.""",
  mathlib="""`Ideal.exists_ideal_over_maximal_of_isIntegral`, `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`,
`FaithfulSMul.algebraMap_injective`, `Ideal.Quotient.algebraQuotientOfLEComap`, `Algebra.IsIntegral.quotient`,
`Algebra.IsIntegral.isAlgebraic`, `Algebra.IsAlgebraic.trans`, `IsScalarTower.of_algebraMap_eq`.""",
  sources="""BGR 3.8.1/6 (a), proof (`bgr-3.8.md:76–84`): "Since `φ` is integral and injective, there is a maximal
ideal `x` of `A` lying over `y`, i.e., `φ⁻¹(x) = y`. Now `φ` induces an integral monomorphism from `B/y`
into `A/x`. The field `B/y` is an algebraic extension of `k` by our assumption, and `A/x` is integral
over `B/y`. Therefore `A/x` is an algebraic extension of `k`."
""",
  gen="""Pure commutative algebra over `[Algebra B A] [IsScalarTower K B A]`; `K` is only needed for the third
lemma. `FaithfulSMul B A` is Mathlib's spelling of "monomorphism".""")

t(id='T013', title='Finiteness of `|·|_sup` transfers along integral maps (BGR 3.8.1/6 (c))', file=INT,
  deps='T003, T005, T006, T010, T012', par='yes (with T011, T028)', typ='lemmas', leaves='L3.4–L3.5',
  decls=[(INT,'HasSupSeminorm.of_isIntegral'),(INT,'HasSupSeminorm.of_isIntegral_of_faithfulSMul')],
  sketch="""`of_isIntegral`: `isAlgebraic`: T012 (`comap x` is maximal with algebraic residue field by the class on `B`,
packaged as the point `⟨comap x, _⟩`). `bddAbove`: for `f`, take an integral equation `q := minpoly`-free:
`Algebra.IsIntegral.isIntegral f` gives monic `q ∈ B[X]` with `aeval f q = 0`; the POINTWISE bound
`evalNorm K x f ≤ max_i |q.coeff i (comap x)|^{1/(n-i)} ≤ max_i |q.coeff i|_sup^{1/(n-i)}` — proved as
in T010 but at the single point `x` with the pointwise seminorm properties of T001 (`evalNorm_pow`,
`evalNorm_add_le_max`, `evalNorm_mul_le`, `evalNorm_comapPoint`-style equality
`evalNorm K x (algebraMap B A b) = evalNorm K ⟨comap x, _⟩ b` from T005's `evalNorm_comapPoint` applied to
`IsScalarTower.toAlgHom K B A`), then `evalNorm_le_supSeminorm` on `B`. Package the bound as
`BddAbove`. (Do NOT use `supSeminorm_le_supSpectralValue_of_eval₂_eq_zero`: it needs the class on `A`,
which is what is being constructed; factor the pointwise argument out of T010 as a private lemma if
convenient.) `of_isIntegral_of_faithfulSMul`: `isAlgebraic` for `y`: pick `x` over `y` (T012),
`B ⧸ y ≃ₐ[K] (image in A ⧸ x)` via the injective map `B ⧸ comap x → A ⧸ x`, and a subalgebra of an
algebraic extension is algebraic (`Algebra.IsAlgebraic.of_injective`/`AlgHom.isAlgebraic_of_injective`?
verify: `Algebra.IsAlgebraic.of_injective (f : B' →ₐ[K] A') (hf : Injective f)`). `bddAbove`: `|b(y)| =
|algebraMap b (x)| ≤ supSeminorm K (algebraMap B A b)`.""",
  mathlib="""`Algebra.IsIntegral.isIntegral`, `IsIntegral` (monic `p` with `eval₂ = 0`), `IsScalarTower.toAlgHom`,
`Algebra.IsAlgebraic.of_injective` (verify name), `Ideal.quotientMap`, `Ideal.quotientMap_injective`.""",
  sources="""BGR 3.8.1/6 (c) and proof (`bgr-3.8.md:68–90`): "`| |_sup` is finite on `A` if and only if it is finite
on `B`" / "If `g(Max_k B)` is bounded for all `g ∈ B`, then `f(Max_k A)` is also bounded for all `f ∈ A`
due to (b). The converse is true due to (a)."; 3.8.1/6 (b)'s proof: "Due to Proposition 3.1.2/1, this
equation implies `|f(x)| ≤ max |b_i(φ⁻¹(x))|^{1/i} ≤ max |b_i|_sup^{1/i}`".""",
  gen="""The two directions are separate theorems (not instances: `B` cannot be inferred). The first needs no
injectivity; the second needs `FaithfulSMul B A`.""")

t(id='T014', title='An integral monomorphism is an isometry; `|f|_sup = sup_y |f mod yA|_sup` (BGR 3.8.1/6 (a))',
  file=INT, deps='T005, T006, T012, T013', par='yes (with T011, T028)', typ='lemmas', leaves='L3.6–L3.7',
  decls=[(INT,'supSeminorm_algebraMap_eq'),(INT,'supSeminorm_le_of_forall_supSeminorm_mk_map_le')],
  sketch="""`supSeminorm_algebraMap_eq`: `≤` is `supSeminorm_map_le (IsScalarTower.toAlgHom K B A)` (T005). `≥`:
`supSeminorm_le_of_forall (supSeminorm_nonneg _ _)`: for `y`, pick `x` over `y` (T012); then
`evalNorm K y b = evalNorm K x (algebraMap b)` (`evalNorm_comapPoint` with `comapPoint _ x = y` by
`MaximalSpectrum.ext`/`Subtype.ext` on `asIdeal`) `≤ supSeminorm K (algebraMap b)`.
`supSeminorm_le_of_forall_supSeminorm_mk_map_le`: `supSeminorm_le_of_forall hC`: for `x`, let
`y := comapPoint (IsScalarTower.toAlgHom K B A) x`; `y.asIdeal.map (algebraMap B A) ≤ x.asIdeal`
(`Ideal.map_comap_le`), so `evalNorm K x f ≤ supSeminorm K (mk _ f)` (T006 `evalNorm_le_supSeminorm_mk`)
`≤ C`.""",
  mathlib="""`Ideal.map_comap_le`, `MaximalSpectrum.ext`, `IsScalarTower.toAlgHom`, `IsScalarTower.coe_toAlgHom'`.""",
  sources="""BGR 3.8.1/6 (a), proof (`bgr-3.8.md:76–84`): "the map `x ↦ φ⁻¹(x)` from `Max_k A` to `Max_k B` is surjective.
Therefore, one has equality in the formula (*) occurring in the proof of Lemma 4, and so `φ` is an
isometry"; BGR p. 172 (`bgr-3.8-proofs.md`): "Since each `y ∈ Max_k B` is contained in some ideal
`x ∈ Max_k A`, we see that `|f|_sup = sup_{y ∈ Max_k B} |f_y|_sup`".""",
  gen="""`supSeminorm_le_of_forall_supSeminorm_mk_map_le` needs no integrality (every `x` lies over `comap x`); it is
stated in the Isometry section for convenience — drop the unused `[Algebra.IsIntegral B A]` with `omit` if the
linter asks.""")

t(id='T015', title='Fields: `|·|_sup` is the spectral norm, and `HasSupSeminorm.of_field`', file=INT,
  deps='T002, T005', par='yes (with T011, T013, T028)', typ='lemmas', leaves='L3.8–L3.9',
  decls=[(INT,'supSeminorm_eq_spectralNorm'),(INT,'HasSupSeminorm.of_field')],
  sketch="""A field `L` has exactly one maximal ideal, `⊥` (`Ideal.bot_isMaximal`, `Ideal.eq_bot_or_top`). Let
`x₀ : MaximalSpectrum L := ⟨⊥, Ideal.bot_isMaximal⟩`; every `x` equals `x₀` (`Subsingleton`-style:
`MaximalSpectrum.ext` + `x.isMaximal.ne_top` + `eq_bot_or_top`). `evalNorm K x₀ b = spectralNorm K L b`:
`L ⧸ ⊥ ≃ₐ[K] L` (`(RingEquiv.quotientBot L)` upgraded to an `AlgEquiv`, or `Ideal.quotientKerAlgEquivOfSurjective`
for `AlgHom.id`), and `minpoly.algHom_eq` along the injective map gives `minpoly K (mk ⊥ b) = minpoly K b`.
Then `supSeminorm K b = ⨆ x, evalNorm K x b = evalNorm K x₀ b` (`ciSup_const` after rewriting the family
as constant, via `Unique (MaximalSpectrum L)`). `of_field`: `isAlgebraic` by transport along the same
equivalence; `bddAbove` by the constant family.""",
  mathlib="""`Ideal.bot_isMaximal`, `Ideal.eq_bot_or_top`, `RingEquiv.quotientBot`, `Ideal.quotientKerAlgEquivOfSurjective`,
`minpoly.algHom_eq`, `ciSup_const`, `Unique`.""",
  sources="""BGR 3.8.1/2 (`bgr-3.8.md:38–40`): "if `A` is an algebraic extension of `k`, this definition obviously yields the
spectral norm on `A`".""",
  gen="""`[NontriviallyNormedField K] [CompleteSpace K]` come from the section (the Fibre section needs them for the
splitting-field norms); these two lemmas need only `[NormedField K]` — `omit` the extra instances at
cleanup if the linter reports them unused.""")

t(id='T016', title='Fibre upper bound: `|X(x)| ≤ σ(q)` at every point of `L[X] ⧸ (q)`', file=INT,
  deps='T001, T009, T015', par='yes (with T013, T014, T028)', typ='lemma', leaves='L3.10',
  decls=[(INT,'evalNorm_root_le_supSpectralValue')],
  sketch="""Let `x : MaximalSpectrum (AdjoinRoot q)` and `E := AdjoinRoot q ⧸ x.asIdeal`, a field, algebraic over `K`
(class) and over `L` (`Algebra L E` through `AdjoinRoot.of`; `IsScalarTower K L E`). Give `L` and `E` their
spectral norms over `K`: `letI := spectralNorm.normedField K L`, `letI := spectralNorm.normedAlgebra' K L E`
(Mathlib: `[NormedField E] [NormedAlgebra K E] [Algebra E L]`… check the direction of
`spectralNorm.normedAlgebra'`: it makes `L` a normed `E`-algebra when `K → E → L`; here use it with
`(E := L) (L := E)` names swapped). The class of `X` in `E` is a root of `q.map (algebraMap L E)`
(`AdjoinRoot.eval₂_root`/`AdjoinRoot.aeval_eq`, `Ideal.Quotient.mk` is a ring hom). Mathlib's
`norm_root_le_spectralValue (f := spectralAlgNorm L E)` — with base field `L` (normed by the `K`-spectral
norm; its `L`-spectral norm on `E` coincides with the `K`-spectral norm by `spectralNorm.eq_of_tower`, so
`IsPowMul`/`IsNonarchimedean` hold) — gives `‖root‖_E ≤ spectralValue (q)` where `spectralValue` is for the
norm on `L`, which is `supSpectralValue K q` by T009 `supSpectralValue_eq_spectralValue` and T015
`supSeminorm_eq_spectralNorm`. Finally `evalNorm K x (root q) = spectralNorm K E (mk (root q))`
(definition, `Ideal.Quotient.field`) `= ‖mk (root q)‖_E` (`NormedAlgebra.norm_eq_spectralNorm`/`rfl` for
the spectral-norm instance).""",
  mathlib="""`spectralNorm.normedField`, `spectralNorm.normedAlgebra'`, `spectralNorm.eq_of_tower`, `norm_root_le_spectralValue`,
`spectralAlgNorm`, `spectralAlgNorm_isPowMul`, `isNonarchimedean_spectralNorm`, `AdjoinRoot.of`,
`AdjoinRoot.aeval_eq`, `AdjoinRoot.eval₂_root`, `NormedAlgebra.norm_eq_spectralNorm`, `Ideal.Quotient.field`.""",
  sources="""BGR 3.8.1/6 (b), proof (`bgr-3.8.md:85–90`): "Due to Proposition 3.1.2/1, this equation implies
`|f(x)| ≤ max |b_i(φ⁻¹(x))|^{1/i}`"; BGR p. 172 (`bgr-3.8-proofs.md`): "denote by `| |_ν` the spectral norm
on `(B/y)[X]/(q_ν)` over `B/y` (which equals the spectral norm over `k` by Proposition 3.2.2/4)".""",
  gen="""Stated over an arbitrary field `L` algebraic over `K` (BGR: `L = B/y` with `y ∈ Max_k B`), with the
`HasSupSeminorm K (AdjoinRoot q)` instance as an explicit hypothesis (provided by T013 at the use site).""")

t(id='T017', title='THE FIBRE COMPUTATION: `σ(q)` is attained at a point of `L[X] ⧸ (q)` (BGR p. 172)', file=INT,
  deps='T015, T016', par='no', typ='lemma', leaves='L3.11',
  decls=[(INT,'exists_evalNorm_root_eq_supSpectralValue')],
  sketch="""Let `E := q.SplittingField` over `L` (`Polynomial.SplittingField`, with `Algebra L E`, `IsScalarTower K L E`
through `Polynomial.SplittingField.algebra'`; `E` is finite over `L` hence algebraic over `K`:
`Algebra.IsAlgebraic.trans`). Spectral norms over `K` on `L` and `E` as in T016. `q.map (algebraMap L E)`
splits: `q.map _ = ∏_{a ∈ roots} (X − C a)` (`Splits.eq_prod_roots_of_monic`, `SplittingField.splits`).
Mathlib `max_norm_root_eq_spectralValue (K := L) (L := E) (f := spectralAlgNorm L E)` (power-multiplicative,
nonarchimedean, `f 1 = 1`; `mapAlg L E q = ∏ (X - C a)`) gives `(⨆ a, if a ∈ roots then ‖a‖ else 0) =
spectralValue q = supSpectralValue K q` (T009, T015). The roots form a nonempty finite multiset (`natDegree > 0`,
`Multiset.card_roots'`/`Polynomial.natDegree_eq_card_roots` for split polynomials), so some root `a₀` attains
`‖a₀‖ = σ(q)` (`Finset.exists_max_image` on `roots.toFinset`). Now `AdjoinRoot.liftAlgHom`-style evaluation
`ev : AdjoinRoot q →ₐ[L] E`, `root q ↦ a₀` (`AdjoinRoot.liftAlgHom (Algebra.ofId L E) a₀ (by simpa using
root)`; restrict scalars to `K`); its kernel is a maximal ideal `x` (Layer 0 `isMaximal_ker_of_isAlgebraic`
for `ev.restrictScalars K` into the algebraic field `E`), and Layer 0 `evalNorm_eq_norm_algHom` (with `L := E`
normed by the spectral norm — `NormedAlgebra K E`, `Algebra.IsAlgebraic K E`) gives
`evalNorm K x (root q) = ‖ev (root q)‖ = ‖a₀‖ = σ(q)`.""",
  mathlib="""`Polynomial.SplittingField`, `Polynomial.SplittingField.splits`, `Polynomial.SplittingField.algebra'`,
`Splits.eq_prod_roots_of_monic`, `max_norm_root_eq_spectralValue`, `mapAlg`, `Polynomial.natDegree_eq_card_roots`,
`Finset.exists_max_image`, `AdjoinRoot.liftAlgHom`, `AlgHom.restrictScalars`; Layer 0
`Affinoid.isMaximal_ker_of_isAlgebraic`, `Affinoid.evalNorm_eq_norm_algHom`, and the Layer 0 pattern in
`TateAlgebra/MaxModulus.lean` (`letI := spectralNorm.normedField K E; letI := spectralNorm.normedAlgebra K E;
haveI : IsUltrametricDist E := …; haveI := spectralNorm.completeSpace K E`).""",
  sources="""BGR p. 172 (`bgr-3.8-proofs.md`, proof of 3.8.1/7 (a)): "`red (A/yA) = (B/y)[X]/(q₁ ⋯ q_r) = ⊕ (B/y)[X]/(q_ν)`.
Provide `B/y` with the spectral norm over `k` … Then if `f̄_ν` is the residue class of `f̄_y` in
`(B/y)[X]/(q_ν)`, we have by Corollary 3.2.1/6 `|f̄_y|_sup = max_ν |f̄_ν|_ν = max_ν σ(q_ν) = σ(q_y)`"; BGR 1.5.4
"if a monic polynomial splits into linear factors, then its spectral value is the norm of its largest root"
(Mathlib's docstring of `spectralValue`).""",
  gen="""Formulated on `AdjoinRoot q` for a monic `q ∈ L[X]` of positive degree over a field `L` algebraic over `K`:
BGR's `A/yA = (B/y)[X]/(q_y)` is this with `L = B/y`. Our route goes through ONE splitting field and the
evaluation at a maximal root instead of BGR's prime factorisation `q_y = ∏ q_ν^{n_ν}` and the reduced ring
`⊕ (B/y)[X]/(q_ν)` (the point over the factor `q_ν` of the root `a₀` is the kernel of `ev`); both facts
BGR invoke (3.2.1/6, 3.2.2/4) are replaced by Mathlib's `max_norm_root_eq_spectralValue`.""")

t(id='T018', title='`σ(minpoly_B f) ≤ |f|_sup`: the lower bound of BGR 3.8.1/7 (a)', file=INT,
  deps='T006, T009, T011, T014, T017', par='no', typ='lemma', leaves='L3.12',
  decls=[(INT,'supSpectralValue_minpoly_le_supSpectralValue')],
  sketch="""Let `q := minpoly B f` (monic: `minpoly.monic (Algebra.IsIntegral.isIntegral f)`, positive degree:
`minpoly.natDegree_pos`). Step 1 (BGR: "we may assume `A = B[f]`"): let `A' := Algebra.adjoin B {f}`; `A'` is
integral over `B`, `A` is integral over `A'` (`Algebra.IsIntegral.tower_top`), and `A' → A` is injective, so
`supSeminorm K (f : A') = supSeminorm K f` by T014 `supSeminorm_algebraMap_eq` (with `HasSupSeminorm K A'` from
T013 `of_isIntegral_of_faithfulSMul` applied to `A' ↪ A`, or from `of_isIntegral` over `B`). So it suffices
to prove the bound on `A'`. Step 2: `AdjoinRoot q ≃ₐ[B] A'`: `AdjoinRoot.equiv'`/`Algebra.adjoin.powerBasis'`
… the cleanest is `minpoly.equivAdjoin`-type for integrally closed `B` — Mathlib: `AdjoinRoot.equiv' q
(Algebra.adjoin.powerBasis' hf)` with the `minpoly` identification `minpoly_powerBasis_gen_of_monic`; or
avoid the equivalence: the surjection `AdjoinRoot.liftAlgHom q f : AdjoinRoot q →ₐ[B] A'` is injective
because its kernel is `span {q}` (`minpoly.ker_eval`, `AdjoinRoot.mk_eq_zero`), hence an isomorphism
(`AlgEquiv.ofBijective`). Transport the seminorm along it (`supSeminorm_map_le` both ways, or
`evalNorm`-level equality through `comapPoint`): `supSeminorm K (root q) = supSeminorm K (f : A')`.
Step 3 (the fibre over `y`): for `y : MaximalSpectrum B`, `AdjoinRoot q ⧸ (y.asIdeal.map (of q)) ≃ₐ[B]
AdjoinRoot (q.map (mk y))` (`AdjoinRoot.quotEquivQuotMap q y.asIdeal`, then `AdjoinRoot` of the mapped
polynomial over the field `L := B ⧸ y`); by T006/T014, `supSeminorm K (root q) ≥ supSeminorm K (mk _ (root q))
= supSeminorm K (root q̄)` (transport along the equivalence; the class on `AdjoinRoot q̄` from T013 over `L`
with T015) `= σ(q̄)` where `≥` is T017's attained point (and `≤` T016; equality is not needed, only `≥`).
Step 4: `σ(q̄) ≥ |b_i(y)|^{1/i}` for each coefficient (T009 `terms_le`, `q̄.coeff i = mk y (q.coeff i)`,
`Monic.natDegree_map`, and `supSeminorm K (mk y b) = evalNorm K y b` by T015 on the field `L` + T006), so
`|f|_sup ≥ sup_y max_i |b_i(y)|^{1/i} = max_i |b_i|_sup^{1/i} = σ(q)`: for each `i`,
`|b_i|_sup = ⨆ y, |b_i(y)|` (definition), take `rpow` (monotone, `Real.iSup_rpow`-free: show
`|b_i(y)|^{1/i} ≤ |f|_sup` for all `y`, hence `|b_i|_sup^{1/i} ≤ |f|_sup` by `Real.rpow_le_rpow` after
`ciSup_le` on `|b_i(y)| ≤ |f|_sup^i`), then `supSpectralValue_le_of_forall`.""",
  mathlib="""`minpoly.monic`, `minpoly.natDegree_pos`, `minpoly.ker_eval`, `AdjoinRoot.liftAlgHom`, `AdjoinRoot.mk_eq_zero`,
`AlgEquiv.ofBijective`, `Algebra.adjoin`, `Algebra.IsIntegral.tower_top`, `AdjoinRoot.quotEquivQuotMap`,
`Polynomial.coeff_map`, `Polynomial.Monic.natDegree_map`, `Real.rpow_le_rpow`, `ciSup_le`,
`Real.rpow_natCast`.""",
  sources="""BGR 3.8.1/7, proof Ad (a) (`bgr-3.8-proofs.md`): "We may assume that `B` is a subalgebra of `A` and that
`A = B[f]` … `A = B[f] ≅ B[X]/(q)` … `|f|_sup = sup_{y ∈ Max_k B} |f_y|_sup = sup_y |f̄_y|_sup` … `A/yA =
(B/y)[X]/(q_y)` … `|f̄_y|_sup = σ(q_y)`. Therefore `|f|_sup = sup_y σ(q_y) = sup_y max_i |b_i(y)|^{1/i}
= max_i |b_i|_sup^{1/i}`"; the preliminaries pp. 171–172 for `B[X]/(q) ≅ B[f]` ("`ker τ` is generated by `q`",
= `minpoly.ker_eval`).""",
  gen="""`A` a domain (plan D8), `B` an integrally closed domain, `[Algebra.IsIntegral B A] [Module.IsTorsionFree B A]`,
both with `HasSupSeminorm`; `[CompleteSpace K]` through the fibre computation. Only the `≥` half of the
fibre identity is used here; T010 gives `≤` globally.""")

t(id='T019', title='M1 — BGR 3.8.1/7 (a): `|f|_sup = σ(minpoly_B f)`', file=INT, deps='T010, T018', par='no',
  typ='theorem', leaves='L3.13', milestone='M1 ([RM] §2.1.4, BGR 3.8.1/7 (a))',
  decls=[(INT,'supSeminorm_eq_supSpectralValue_minpoly')],
  sketch="""`le_antisymm (supSeminorm_le_supSpectralValue_of_eval₂_eq_zero K (IsScalarTower.toAlgHom K B A)
(minpoly.monic _) (by simpa [Polynomial.aeval_def] using minpoly.aeval B f)) (supSpectralValue_minpoly_le_supSeminorm K f)`.
Then `#print axioms` (standard) and record in `tickets.md`.""",
  mathlib="""`minpoly.aeval`, `Polynomial.aeval_def`, `IsScalarTower.toAlgHom`.""",
  sources="""BGR 3.8.1/7 (a) (`bgr-3.8-proofs.md`): "`|f|_sup = max_{1≤i≤n} |b_i|_sup^{1/i}` for `f ∈ A`, where
`fⁿ + φ(b₁) fⁿ⁻¹ + ⋯ + φ(bₙ) = 0` is the (unique) integral equation of minimal degree for `f` over `φ(B)`".""",
  gen="""As T018.""")

t(id='T020', title='`minpoly (b • f)` is the scaled polynomial; `|φ(b) f|_sup = |b|_sup |f|_sup` (BGR 3.8.1/7 (d))',
  file=INT, deps='T019', par='yes (with T021, T022, T023, T028)', typ='lemmas', leaves='L3.14–L3.15',
  decls=[(INT,'minpoly_algebraMap_mul_eq_scaleRoots'),(INT,'supSeminorm_algebraMap_mul')],
  sketch="""`minpoly_algebraMap_mul_eq_scaleRoots`: `p := (minpoly B f).scaleRoots b` is monic (`monic_scaleRoots_iff`),
has `b•f` as a root (`scaleRoots_aeval_eq_zero (minpoly.aeval B f)`, `Algebra.smul_def`), and
`natDegree p = natDegree (minpoly B f)` (`natDegree_scaleRoots`). `minpoly B (b•f) ∣ p`
(`minpoly.isIntegrallyClosed_dvd`, needs `IsIntegral B (b • f)`: product of integrals) and
`natDegree (minpoly B (b•f)) ≥ natDegree (minpoly B f)`: both equal the degrees over `Q(B)`
(`minpoly.isIntegrallyClosed_eq_field_fractions'` + `natDegree_map`), and over the field `Q(B)` the
elements `f` and `b•f` (with `b ≠ 0` a unit of `Q(B)`) generate the same intermediate field, so
`minpoly.natDegree_eq_finrank`-style equality (`IntermediateField.adjoin_simple_eq`? easier: apply the
same divisibility argument symmetrically: `f = b⁻¹ • (b•f)` in `Q(A)`, so `minpoly_{Q(B)} f ∣
(minpoly_{Q(B)} (b•f)).scaleRoots b⁻¹`, giving `deg f ≤ deg (b•f)`). Monic divisor of a monic polynomial
of the same degree: `Polynomial.eq_of_monic_of_dvd_of_natDegree_le`. `supSeminorm_algebraMap_mul`: `b = 0`
trivial (`supSeminorm_zero`, `zero_mul`); else by M1 twice and the scaled polynomial:
`σ(q.scaleRoots b)`'s terms are `|b^{n-i} b_i|_sup^{1/(n-i)} = |b|_sup |b_i|_sup^{1/(n-i)}` using `hB` for
`|b^{n-i} b_i| = |b|^{n-i} |b_i|` and `Real.mul_rpow`; so `σ(q.scaleRoots b) = |b|_sup σ(q)`
(`Real.mul_iSup_of_nonneg`).""",
  mathlib="""`Polynomial.scaleRoots`, `monic_scaleRoots_iff`, `scaleRoots_aeval_eq_zero`, `natDegree_scaleRoots`,
`coeff_scaleRoots`, `minpoly.isIntegrallyClosed_dvd`, `minpoly.isIntegrallyClosed_eq_field_fractions'`,
`Polynomial.eq_of_monic_of_dvd_of_natDegree_le`, `IsIntegral.mul`, `Real.mul_rpow`, `Real.mul_iSup_of_nonneg`.""",
  sources="""BGR 3.8.1/7, proof Ad (d) (`bgr-3.8-proofs.md`): "`f` is of degree `n` over the fraction field `Q(B)`, and so
is any product `bf` where `b ∈ B − {0}`. Therefore `(bf)ⁿ + bb₁(bf)ⁿ⁻¹ + ⋯ + bⁿbₙ = 0` is the integral
equation of minimal degree for any such product `bf` … `|bf|_sup = max |b^i b_i|_sup^{1/i} = |b|_sup
max |b_i|_sup^{1/i} = |b|_sup |f|_sup`".""",
  gen="""Only the "if" direction of (d) (the "only if" is 3.8.1/6 (a), T014). `hB` is BGR's "`| |_sup` is
multiplicative on `B`" (for `T_d`: the Gauss norm is multiplicative, Layer 0 `NormMulClass`).""")

t(id='T021', title='The maximum modulus principle and the norm property transfer along integral maps (BGR 3.8.1/7 (b), (c))',
  file=INT, deps='T009, T017, T019', par='yes (with T020, T022, T023, T028)', typ='lemmas', leaves='L3.16–L3.17',
  decls=[(INT,'exists_evalNorm_eq_supSeminorm_of_forall_exists'),(INT,'eq_zero_of_supSeminorm_eq_zero')],
  sketch="""(b): `q := minpoly B f`; if `|f|_sup = 0` any point works (`A` is a domain so nontrivial; take any `x`,
`evalNorm_nonneg` + `evalNorm_le_supSeminorm`). Else `σ(q) = |f|_sup ≠ 0` is attained at a coefficient index
`i` (T009 `exists_supSpectralValue_eq`); by `hB` pick `y` with `|b_i(y)| = |b_i|_sup`. Then `σ(q̄_y) ≥
|b_i(y)|^{1/(n-i)} = σ(q)` (T009 on `L = B ⧸ y` as in T018 step 4), and `≤` by T011 `map_le`-style
(coefficientwise `|b(y)| ≤ |b|_sup`); so `σ(q̄_y) = |f|_sup`. T017 gives a point `x̄` of `AdjoinRoot q̄_y` with
`evalNorm x̄ (root q̄_y) = σ(q̄_y)`; transport to a point of `A ⧸ yA`-side: through the equivalences of T018
(steps 2–3) the point `x̄` corresponds to a maximal ideal `x` of `A'` = `B[f]` over `y`, and then to a maximal
ideal of `A` lying over it (T012 going up, `A` integral over `A'`), with `evalNorm K x f = evalNorm x̄ (root)`
(`evalNorm_comapPoint`/`evalNorm_eq_norm_algHom` along the composite). (c): `f ≠ 0`, `q := minpoly B f` has some
coefficient `b_i ≠ 0` with `i < n` (else `q = Xⁿ`, so `fⁿ = 0`, `f = 0` in the domain `A`), `|b_i|_sup ≠ 0` by `hB`,
so `|f|_sup = σ(q) ≥ |b_i|_sup^{1/(n-i)} > 0` (M1 + `terms_le` + `Real.rpow_pos_of_pos`).""",
  mathlib="""`Real.rpow_pos_of_pos`, `Polynomial.ext_iff`, `pow_eq_zero_iff`, `minpoly.natDegree_pos`, `Finset.exists_max_image`.""",
  sources="""BGR 3.8.1/7, proof Ad (b) and Ad (c) (`bgr-3.8-proofs.md`): "there is a `y ∈ Max_k B` such that
`|f̄_y|_sup = σ(q_y) = |f|_sup`. Since `A/yA` contains only finitely many maximal ideals, there must exist an
`x ∈ Max_k A` such that `|f̄_y|_sup = |f(x)|`" / "Because `A` is reduced, there exists an index `m` … `b_m ≠ 0`
… `|f|_sup ≥ |b_m|_sup^{1/m} > 0`".""",
  gen="""(b) is stated in the `∀ b, ∃ y, …` form (the hypothesis "the maximum modulus principle holds for `B`"), (c) in
the `∀ b, |b|_sup = 0 → b = 0` form, both for `A` a domain (D8); the converses are T014/T013.""")

t(id='T022', title='A uniform power of `|f|_sup` lies in `‖K‖` (BGR 3.8.1/8, the form 6.2.1/4 (ii) needs)', file=INT,
  deps='T009, T019', par='yes (with T020, T021, T023, T028)', typ='lemma', leaves='L3.18',
  decls=[(INT,'supSeminorm_pow_factorial_mem_range_norm')],
  sketch="""`q := minpoly B f`, `d := natDegree q ≥ 1`, `d ≤ n`. By M1 and T009 `exists_supSpectralValue_eq`,
`|f|_sup = |b_i|_sup ^ (1/(d-i))` for some `i < d`; set `j := d - i ∈ [1, n]`, so `|f|_sup ^ j = |b_i|_sup`
(`Real.rpow_inv_natCast_pow`, nonneg) `= ‖c‖` for some `c : K` (`hB`). Since `j ∣ n!` (`Nat.dvd_factorial`),
`|f|_sup ^ n! = (|f|_sup ^ j) ^ (n!/j) = ‖c‖ ^ (n!/j) = ‖c ^ (n!/j)‖` (`norm_pow`), i.e. `∈ Set.range ‖·‖`.""",
  mathlib="""`Nat.dvd_factorial`, `Nat.div_mul_cancel`, `pow_mul`, `norm_pow`, `Real.rpow_inv_natCast_pow`, `Set.mem_range`.""",
  sources="""BGR 3.8.1/8, proof (`bgr-3.8-proofs.md`): "According to assertion (a) of the preceding proposition,
`|f|_sup ∈ |k_a|` for all `f ∈ A`. Hence there are an element `d ∈ k` and an integer `m` such that
`|d|^{1/m} = |f|_sup`"; the uniform exponent is [RM] §2.2.2 ("State the uniform version: `m` may be chosen to
depend only on `A`"), with `|T_d|_sup = |K|` replacing BGR's `|k_a|`.""",
  gen="""Hypotheses: `|B|_sup ⊆ ‖K‖` (true for `T_d`: Gauss norms are coefficient norms) and a degree bound
`∀ f, natDegree (minpoly B f) ≤ n` (supplied in `Affinoid/SupSeminorm.lean` from
`FractionRing.finiteDimensional_of_finite` + `minpoly.natDegree_le`). Exponent `n!` (any common multiple
of `1..n` would do).""")
