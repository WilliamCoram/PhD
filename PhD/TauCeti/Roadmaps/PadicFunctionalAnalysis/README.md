# Roadmap: p-adic functional analysis

This roadmap develops the functional analysis of nonarchimedean Banach modules and the analysis of
functions on `ℤ_p`: ultrametric summability, Banach modules over nonarchimedean rings and over
Banach–Tate rings, bounded operators and the open mapping theorem, the model space `c₀(I, R)` with
its orthonormal bases, continuous and locally analytic functions on `ℤ_p` with the Mahler and Amice
bases, the `p`-adic exponential, logarithm and binomial series, and the continuous characters of
`ℤ_p^×` — weight space — together with the Iwasawa algebra that parametrises them and the ring
`Λ^{>1/p}` of functions on its boundary annulus. Three results are the headline milestones.

```text
every Banach space over a discretely valued field is orthonormalisable after an equivalent norm       [Serre]
C(ℤ_p, E) ≅ c₀(ℕ, E) by the Mahler basis (x choose n),  and  LA_h(ℤ_p, E) ≅ c₀(ℕ, E) by the Amice
basis ⌊n/pʰ⌋!·(x choose n)                                                                         [Mahler, Amice]
Hom_cts(ℤ_p^×, R^×) ≅ Hom(Δ, R^×) × {r topologically nilpotent},  Λ = ℤ_p⟦ℤ_p^×⟧ ≅ ℤ_p[Δ]⟦T⟧,  and
Λ^{>1/p}[1/T] is a Banach–Tate ring with T as pseudo-uniformiser                                    [Iwasawa, Amice; LWX]
```

The first three layers are functional analysis with no `p` in sight: they are stated for a
nonarchimedean normed ring `R`, or for a Banach–Tate ring — a complete nonarchimedean normed ring
with a multiplicative unit of norm less than `1` — and everything in them should be usable by
anyone working with Banach modules over such a ring. The point of the generality is that the
coefficient ring of a family of `p`-adic automorphic forms is not a field: it is `Λ^{>1/p}[1/T]` or an
affinoid algebra, and the field case is recovered by the bridge lemma of §0.4, not assumed. The
remaining layers are the analysis on `ℤ_p`: Mahler's theorem is in Mathlib and is the floor on which
Layer 3 stands; Amice's theorem is the arithmetic core of Layer 4; and Layer 5 reads the characters
of `ℤ_p^×` through the analysis of Layer 4, so that "the character `κ` is analytic on the discs
`a + pʰℤ_p`" is a theorem with a computable threshold rather than a definition.

## Scope

The roadmap includes the following material.

- Sums in complete ultrametric groups: summability of null families, the bound `‖∑' f‖ ≤ sup ‖f i‖`,
  the strict and unique-dominant-term forms, double sums and Cauchy products.
- Nonarchimedean normed rings: the unit ball and its ideal of topologically nilpotent elements,
  power-bounded elements, the Neumann series; Banach modules over such rings and their
  constructions; norm rescaling; Banach–Tate rings in the normed sense, the pseudo-uniformiser
  valuation, the bridge from Banach algebras over nontrivially normed fields, the bridge to and from
  Huber's topological Tate rings, and the comparison of equivalent norms.
- Bounded linear maps over Banach–Tate rings: the operator norm on `M →L[R] N`, boundedness versus
  continuity, completeness, the quantitative open mapping theorem, the closed graph theorem,
  Banach–Steinhaus, invertibility by Neumann series, finite-dimensional spaces over a complete
  field, and finitely generated modules over Noetherian Banach–Tate rings.
- The model space `c₀(I, R)` as Mathlib's `C₀(I, R)` for a discrete `I`: its universal property,
  reindexing and block decompositions; orthogonal, `t`-orthogonal and orthonormal families and
  bases; orthonormalisable and potentially orthonormalisable modules and property (Pr); Serre's
  theorem in its ring form (residue-module freeness) and its field form; Banach spaces of countable
  type; the dual of `c₀`; matrices of bounded operators between model spaces and coordinate
  truncations; the unitriangular-perturbation criterion for a matrix to define an isometric
  automorphism.
- Continuous functions on a profinite space with values in a Banach module, the density of locally
  constant functions, the Mahler basis of `C(ℤ_p, E)` (Mathlib) with the Mahler coefficients of
  monomials, translates, locally constant functions and characters, the Mahler basis on the cosets
  of `pʰℤ_p`, the van der Put basis, and measures on `ℤ_p` with the Amice transform of a measure.
- The Tate algebra `R⟨X⟩` as the model space, evaluation and substitution of restricted series, the
  identity theorem; analytic functions on the discs `a + pʰℤ_p`, the spaces `LA_h(ℤ_p, E)` presented
  by their Taylor coefficients on the discs, their inclusions, locally polynomial functions, Amice's
  theorem and the Mahler-coefficient characterisation of local analyticity; the exponential,
  logarithm, power and binomial series over a Banach `ℚ_p`-algebra with their sharp convergence
  discs and functional equations; continuous characters of `ℤ_p` and the level of their analyticity;
  locally analytic distributions on `ℤ_p` and the Amice transform.
- Continuous characters of `ℤ_p^×` with values in a complete ultrametric normed `ℤ_p`-algebra:
  the decomposition `ℤ_p^× = Δ × (1 + qℤ_p)`, the `T`-coordinate of a character, the classical
  characters `x ↦ xᵏψ(x)`, the level of analyticity of a character and the expansion of
  `z ↦ κ(cz + d)` as a restricted power series; the Iwasawa algebra `Λ = ℤ_p⟦ℤ_p^×⟧` as the completed
  group algebra, as `ℤ_p[Δ]⟦T⟧` and as the algebra of measures, with its universal character and its
  universal property; the ring `Λ^{>1/p} = ℤ_p⟦T, pT⁻¹⟧` of the boundary annulus, its specialisations
  at the points `p⁻¹ < ‖T₀‖ < 1`, and the Banach–Tate ring `Λ^{>1/p}[1/T]`.

The roadmap does not include the following.

- ⚠ **Compact operators.** Finite-rank and completely continuous operators, the row-decay
  (compactoid) criterion, Fredholm determinants `det(1 − Tu)`, Riesz theory and slope
  decompositions are the compact-operators roadmap. This roadmap ends at the matrix of a bounded
  operator on the model space (§2.6); the first compactness-flavoured notion — uniform decay of the
  rows of that matrix — belongs to the other roadmap, which consumes §§0–2 and §4.3 (the inclusions
  `LA_h ⊂ LA_{h+1}` are diagonal with entries tending to zero) as inputs.
- ⚠ **Tate rings as topological rings, restricted power series as rings, and Weierstrass theory.**
  Huber rings, Tate rings, pairs of definition, the power-bounded subring `A°`, the ring structure
  of `A⟨X₁, …, Xₙ⟩`, Weierstrass division and preparation and the Noetherian theory of Tate algebras
  are the adic-spaces roadmap (Layer 0 and §0.5), already partly in Tau Ceti under
  `TauCeti/RingTheory/Huber/`. This roadmap defines the *normed* notion of a Banach–Tate ring and
  proves the bridge in both directions (§0.4); it sees `R⟨X⟩` only as a Banach `R`-module (§4.1).
- ⚠ **Newton polygons, radii of convergence and zeros of power series.** The Newton-polygons
  roadmap; §4.1 cites its Weierstrass preparation for the identity theorem.
- The structure theory of local fields — the unit filtration, the Teichmüller section, and the
  logarithm as an isomorphism of the deep principal units onto an ideal — is the
  local-fields-and-ramification roadmap (Layer 1). §4.5 constructs the exponential and logarithm
  over an arbitrary Banach `ℚ_p`-algebra and records that on a local field they are that roadmap's
  maps; §5.1 cites that roadmap for `ℤ_p^× = μ_{p−1} × (1 + pℤ_p)` at odd `p`.
- The completed group algebra `ℤ_p⟦Γ⟧` of a general profinite group and its identification with
  `ℤ_p⟦T⟧` for procyclic `Γ` are the profinite-and-pro-`p`-groups roadmap (Layer 9). §5.3 cites it
  for the definition of `Λ` and adds the `Δ`-factor, the measures, and the universal character.
- Locally convex spaces, Fréchet spaces, spherical completeness and the Hahn–Banach theorem,
  reflexivity, nuclear spaces, and the general duality theory of Schneider's book; the only duality
  statement here is the dual of `c₀`.
- Locally analytic representations of `p`-adic groups, locally analytic vectors, and distribution
  algebras of `p`-adic Lie groups other than `ℤ_p` and `ℤ_p^×`; the rigid-analytic weight space and
  its affinoid subdomains; `p`-adic `L`-functions and the measures attached to Dirichlet characters;
  the Iwasawa main conjecture.
- The weight-`κ` action on the Tate algebra, overconvergent automorphic forms and Hecke operators,
  which consume §5.5 and are the overconvergent-forms roadmap; the Mahler calculus of Liu–Wan–Xiao
  (§3 of their paper) and the halo estimate, which consume §5.6 and are the spectral-halo roadmap.

Layers 0–2 belong under `TauCeti/Analysis/Normed/`, mirroring Mathlib's directories: the sums in
`TauCeti/Analysis/Normed/Group/Ultra/`, the rings, modules and Banach–Tate rings in
`TauCeti/Analysis/Normed/Ring/Ultra/` and `TauCeti/Analysis/Normed/Module/Ultra/`, the operators in
`TauCeti/Analysis/Normed/Operator/Ultra/`, and the model space and its bases in
`TauCeti/Analysis/Normed/Module/Ultra/ModelSpace/`. Layers 3–5 belong under
`TauCeti/NumberTheory/Padics/`: `Mahler/`, `LocallyAnalytic/`, `ExpLog/` and `WeightSpace/`.

## Conventions and coordination with Mathlib

The following Mathlib material and pull requests are relevant to this roadmap.

- `Mathlib/NumberTheory/Padics/MahlerBasis.lean` proves Mahler's theorem,
  `PadicInt.mahlerEquiv E : C(ℤ_[p], E) ≃ₗᵢ[ℤ_[p]] C₀(ℕ, E)`, for every complete ultrametric normed
  `ℤ_[p]`-module `E`. Layer 3 stands on it and never redefines the Mahler basis.
- `Mathlib/NumberTheory/Padics/AddChar.lean` proves `PadicInt.continuousAddCharEquiv`: continuous
  additive characters `ℤ_[p] → R` of a complete ultrametric normed `ℤ_[p]`-algebra `R` correspond to
  topologically nilpotent elements of `R`, by `κ ↦ κ 1 − 1`. This is the `ℤ_p`-part of the
  parametrisation of weight space (§5.2), and §4.6 identifies the character attached to `r` with
  the binomial series `x ↦ (1 + r)ˣ`.
- `Mathlib/NumberTheory/Padics/Measure/` defines `AbstractMeasure X R E`, the space `D(X, R)` of
  `R`-valued measures on `X` as continuous linear functionals on `C(X, R)`, with Dirac measures,
  pushforward and product measures, and names the Iwasawa algebra as its motivation. §3.4 builds the
  Amice transform on that type and nowhere else.
- `Mathlib/Topology/Algebra/InfiniteSum/Nonarchimedean.lean` proves that a family in a complete
  nonarchimedean group is summable exactly when it tends to `0` cofinitely, and that products of
  sums distribute; `Mathlib/Analysis/Normed/Group/Ultra.lean` makes an ultrametric normed group a
  `NonarchimedeanAddGroup`, so both apply to `IsUltrametricDist` spaces.
- mathlib4#40013 defines bounded subsets and power-bounded elements of topological rings; the
  adic-spaces roadmap coordinates with it and Tau Ceti's `TauCeti.Huber.IsPowerBounded` is shaped as
  it is. §0.2 uses that vocabulary for the norm characterisations.
- mathlib4#43578 and mathlib4#43580 (`WithZero.negLog`, `Valuation.addVal`) are the additive
  valuations of the Newton-polygons roadmap; §0.4 relates the pseudo-uniformiser valuation `v_ϖ` to
  them and does not build them.

The Tau Ceti API should agree with the final Mathlib API. ⚠ **None of these is a blocker, and
nothing in this roadmap waits on Mathlib.**

These conventions are binding. Several of them are corrections to the obvious first design, and the
reasons are given because an implementor who does not know them will reintroduce the problem.

1. **Mathlib's vocabulary for "nonarchimedean".** A nonarchimedean normed ring is
   `[NormedRing R] [IsUltrametricDist R]`, with `[NormOneClass R]` whenever `‖1‖ = 1` is needed and
   `[CompleteSpace R]` for "Banach"; a normed module over it is
   `[NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [IsUltrametricDist M]`, and a Banach
   module adds `[CompleteSpace M]`. A multiplicative norm is `NormMulClass` on a ring and
   `NormSMulClass` on a module. There is no class `BanachModule`, no class `NonarchimedeanNormedRing`,
   and no predicate wrapping the strong triangle inequality: `IsUltrametricDist` is the instance
   Mathlib uses, `IsUltrametricDist.norm_add_le_max` is the inequality, and every statement is made
   in these terms. A nonarchimedean normed field is `[NontriviallyNormedField K] [IsUltrametricDist K]`.

2. **Banach–Tate rings are a Prop class with the pseudo-uniformiser as separate data.** Following
   Johansson–Newton, a normed ring is *Tate* when it has a multiplicative unit `ϖ` (`‖ϖ x‖ = ‖ϖ‖‖x‖`
   for all `x`) of norm less than `1`, a *multiplicative pseudo-uniformiser*; a Banach–Tate ring is
   a complete one. The class `NormedRing.IsTate R : Prop` records existence; the structure
   `PseudoUniformizer R` carries a chosen `ϖ` for the statements that need the element (its
   valuation `v_ϖ`, the shells `‖ϖ‖ < ‖ϖⁿ x‖ ≤ 1`, the constants of the open mapping theorem). Do
   not make `IsTate` carry data, and do not state theorems about `IsTate` rings that secretly depend
   on a choice.

   ⚠ The name is chosen against Mathlib's and Tau Ceti's `IsTateRing`, which is Huber's *topological*
   notion (a Huber ring with a topologically nilpotent unit, `TauCeti.Huber.IsTateRing`). The two
   are different objects: a norm is data, a topology is not, and a Tate ring has many norms. §0.4
   proves that a Tate normed ring is a Tate ring, and that a Tate ring with a chosen ring of
   definition and topologically nilpotent unit admits a norm making it a Tate normed ring; nothing
   identifies the two classes.

3. **The model space is Mathlib's `C₀`.** The model space `c₀(I, R)` of families `I → R` tending to
   `0` cofinitely, with the sup norm, is `C₀(I, R)` for `I` carrying the discrete topology
   (`[TopologicalSpace I] [DiscreteTopology I]`), and no new type is introduced for it. Statements
   are made for an arbitrary discrete `I`; the index sets that occur downstream — `ℕ`, `ℤ`,
   `ZMod n`, `Fin n`, and their finite products — carry discrete instances in Mathlib. The
   instances `C₀` lacks (`IsUltrametricDist`, and `Module R` with `IsBoundedSMul R` for a normed
   *ring* `R`) are milestones of §2.1, added to `C₀` for a discrete domain, not to a synonym.

4. **Orthonormalisability is defined by isometry to the model space.** `IsONable R M` is the
   existence of an `R`-linear isometric isomorphism `M ≃ₗᵢ[R] C₀(I, R)` for some `I`, and
   `IsPotentiallyONable R M` the existence of a continuous linear equivalence, as Johansson–Newton
   define them; `HasPr R M` is "a direct summand of a potentially orthonormalisable module". The
   basis-language notions — an orthonormal family, an orthonormal basis — are predicates on a family
   `e : I → M`, and "`M` is ON-able iff it has an orthonormal basis" is a theorem (§2.2.3). The
   reason for the order is that an isometry to `C₀` is what every later construction uses (the
   matrix of an operator, base change, block decompositions), and a basis is then the image of the
   canonical one; a structure carrying a basis as data would have to be transported along every
   isometry.

5. **Orthonormal means norm one and the sup-norm identity, orthogonal allows scaling.** A family
   `e : I → M` is *orthogonal* if `‖∑ aᵢ eᵢ‖ = max ‖aᵢ eᵢ‖` for every finitely supported `a`, and
   *orthonormal* if moreover `‖eᵢ‖ = 1` for all `i`; for `0 < t ≤ 1` it is *`t`-orthogonal* if
   `‖∑ aᵢ eᵢ‖ ≥ t · max ‖aᵢ eᵢ‖`. A family is a *basis* of the given kind if in addition the closed
   span is `M`; equivalently, every `x` has a unique expansion `x = ∑ aᵢ eᵢ` with `aᵢ eᵢ → 0`
   cofinitely. These are Schneider's and Colmez's definitions; Bellaïche's "orthonormal basis"
   (unique expansion with `‖x‖ = sup ‖aᵢ‖`) is the orthonormal case and the equivalence is proved.

6. **The operator norm is Mathlib's formula, stated at the generality that proves it.** The norm on
   `M →L[R] N` is `sInf {c | 0 ≤ c ∧ ∀ x, ‖u x‖ ≤ c * ‖x‖}`, literally the formula of
   `ContinuousLinearMap.opNorm`, which Mathlib states for field scalars only. Layer 1 states the
   definition and its order-theoretic lemmas for a semiring of scalars, and the lemmas that need
   scaling (`‖u x‖ ≤ ‖u‖ * ‖x‖` for merely continuous `u`, completeness, the open mapping theorem)
   for Banach–Tate rings. ⚠ The instance is `scoped`, so that for a field `R` Mathlib's instance is
   the only global one, and the theorem that the two norms agree on the nose is a milestone
   (§1.1.6); a global instance would create a diamond with `ContinuousLinearMap.hasOpNorm`.

7. **Matrices of operators between model spaces: rows are coordinates, columns are images.** For
   `u : C₀(J, R) →L[R] C₀(I, R)` the matrix coefficient `matrixCoeff u i j` is the `i`-th coordinate
   of `u (single j 1)`, so that column `j` is the image of the `j`-th basis vector — a family tending
   to `0` cofinitely in `i` — and `‖u‖ = sup_{i,j} ‖matrixCoeff u i j‖`. Composition is the matrix
   product, with the sum over the middle index convergent. The compact-operators roadmap's criterion
   is then that the row suprema `sup_j ‖matrixCoeff u i j‖` tend to `0` cofinitely in `i`; Buzzard
   and Bellaïche write the transpose (their `aᵢⱼ` is the coefficient of `fⱼ` in `φ(eᵢ)`), and the
   orientation is fixed here so that no statement has to say which.

8. **Discretely valued, uniformiser, and the normalisation of the norm.** "Discretely valued" for a
   nonarchimedean normed field `K` means `(NormedField.valuation K).IsRankOneDiscrete`, and a
   uniformiser is a `Valuation.IsUniformizer`, exactly as in Layer 1 of the Newton-polygons roadmap.
   In Layers 4 and 5 the coefficient field or algebra is a normed `ℚ_p`-algebra
   (`[NormedAlgebra ℚ_[p] A]`), which pins `‖p‖ = p⁻¹`, so that a radius such as `p^{-1/(p-1)}` is
   a literal real number and not "the norm of `p` to the power `1/(p−1)`"; for a field, this says the
   norm extends the `p`-adic norm. The value `q` is `p` for odd `p` and `4` for `p = 2`, as in
   Liu–Wan–Xiao's Notation 2.1, and every statement of Layer 5 is made for all primes with this `q`.

9. **Locally analytic functions are presented by their Taylor coefficients.** The space
   `LA_h(ℤ_p, E)` of functions analytic on every disc `a + pʰℤ_p` is *defined* as the disc model
   `C₀(ZMod (p ^ h) × ℕ, E)` — for each residue `a`, the Taylor coefficients at the centre `a` of
   the expansion in the coordinate `w` with `x = a + pʰ w` — together with the evaluation map into
   `C(ℤ_[p], E)`; "`f` is analytic of level `h`" is the predicate that `f` lies in the image. The
   norm is the maximum over the discs of the sup norm of the coefficients (Colmez's `v_{LA_h}`).

   The reason: the Taylor coefficients of an `E`-valued function are **not** determined by the
   function for a bad `E`. Over `E = 𝔽_p` with the trivial norm — a complete ultrametric normed
   `ℤ_p`-module — the series `Xᵖ − X` vanishes identically on `ℤ_p`, so a space of *functions* with
   a coefficient-defined norm is ill defined. Evaluation is injective when `E` admits a jointly
   injective family of bounded `ℤ_p`-linear maps to complete nonarchimedean fields (§4.1.6), which
   covers every field, every potentially orthonormalisable Banach space over a field, and
   `Λ^{>1/p}`; under that hypothesis the disc model and the space of functions are identified, and
   that identification is a theorem, not a definition. ⚠ The norm of `LA_h` is not the sup norm on
   `ℤ_p`: `xᵖ − x` has sup norm `p⁻¹` on `ℤ_p` and coefficient norm `1`.

10. **Weight space is a set of characters, parametrised by a topologically nilpotent element.** For
    a complete ultrametric normed `ℤ_p`-algebra `R`, the weight space is
    `𝒲(R) := (ℤ_[p]ˣ →ₜ* Rˣ)`, the continuous characters. Its coordinate is
    `T_κ := κ γ − 1` where `γ := exp q ∈ 1 + qℤ_p` is the topological generator with `log γ = q`,
    and `𝒲(R) ≅ Hom(Δ, Rˣ) × {r : IsTopologicallyNilpotent r}` is a theorem (§5.2.2). The
    generator is Liu–Wan–Xiao's; Washington's `γ = 1 + q` gives another coordinate, and the change of
    coordinate is a milestone (§5.2.5), so that either convention can be read off. No rigid-analytic
    space is attached to `𝒲`; the "open unit disc" is the set `{r : ‖r‖ < 1}` of a field.

11. **The Iwasawa algebra is the completed group algebra, and the halo ring is a ring of Laurent
    coefficient streams.** `Λ := completedGroupAlgebra p ℤ_[p]ˣ` in the sense of the
    profinite-and-pro-`p`-groups roadmap, and `Λ ≅ ℤ_p[Δ]⟦T⟧` with `T = [γ] − 1` is a theorem, not
    the definition. The ring `Λ^{>1/p}` is defined component-wise as the ring of formal Laurent series
    `∑_{m ∈ ℤ} dₘ Tᵐ` with `dₘ ∈ ℤ_p` and `v_p(dₘ) ≥ max(0, −m)`, with the convolution product and the
    gauge norm `‖d‖ = sup_m ‖dₘ‖ p^{−m}`; that it is the `p`-adic completion of `Λ[pT⁻¹]` is a
    theorem (§5.6.3). The reason for the concrete definition is that every statement Liu–Wan–Xiao
    make about `Λ^{>1/p}` is a coefficient estimate, and the completion would have to be unwound to
    the coefficients in every proof.

12. **Names.** The Banach–Tate class is `NormedRing.IsTate`, the element `PseudoUniformizer R` with
    `PseudoUniformizer.val` for `v_ϖ`. Orthonormalisability lives in the `IsONable`,
    `IsPotentiallyONable`, `HasPr` predicates and the `IsOrthogonalFamily`, `IsOrthonormalFamily`,
    `IsOrthonormalBasis` predicates on families; the matrix coefficient is `matrixCoeff` and the
    coordinate truncation `truncation`. The `p`-adic objects live in the `PadicInt` namespace next
    to Mathlib's Mahler basis (`PadicInt.mahler`): `PadicInt.amice h n` for the Amice basis,
    `PadicInt.LocallyAnalytic h E` for the disc model, `PadicInt.padicExp`, `PadicInt.padicLog`,
    `PadicInt.binomialSeries`; the characters in `PadicInt.WeightSpace`, the Iwasawa algebra in
    `IwasawaAlgebra`, the halo ring as `IwasawaAlgebra.Halo p` and its localisation
    `IwasawaAlgebra.HaloTate p`. Nothing from this roadmap is placed in the root namespace.

## Existing Mathlib used by the roadmap

- `IsUltrametricDist`, with `IsUltrametricDist.norm_add_le_max`, the `nnnorm` variants,
  `IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty`, and the instances for subtypes, finite
  products, `ℚ_[p]`, `ℤ_[p]`, `PadicAlgCl p`, `ℂ_[p]`, and `Valued.toNormedField`.
  `IsUltrametricDist.nonarchimedeanAddGroup` makes an ultrametric normed group a
  `NonarchimedeanAddGroup`. ⚠ There is no `IsUltrametricDist` instance on `C₀(α, β)`, on
  `C(α, β)` for compact `α`, or on `BoundedContinuousFunction`; §2.1 and §3.1 add them.
- `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`,
  `NonarchimedeanAddGroup.cauchySeq_sum_of_tendsto_cofinite_zero`, `HasSum.mul_of_nonarchimedean`,
  `Summable.mul_of_nonarchimedean` and `tsum_mul_tsum_of_nonarchimedean`. ⚠ Mathlib has no bound
  `‖∑' i, f i‖ ≤ ⨆ i, ‖f i‖` for ultrametric norms; §0.1 supplies it.
- `IsBoundedSMul`, `NormSMulClass`, `NormMulClass`, `NormOneClass`; `NormedAlgebra`; `NormedSpace`
  (defined over a `NormedField` only, which is why modules over rings are phrased with
  `IsBoundedSMul`).
- `IsTopologicallyNilpotent` and `topologicalNilradical`; `Units.oneSub` (the Neumann series
  `(1 − t)⁻¹` for `‖t‖ < 1` in a complete normed ring, `Mathlib/Analysis/SpecificLimits/Normed.lean`),
  `Units.isOpen`, `NormedRing.inverse_add`. Power-boundedness is `TauCeti.Huber.IsPowerBounded`,
  shaped as mathlib4#40013.
- `ContinuousLinearMap.opNorm` and its API for `NontriviallyNormedField` scalars;
  `ContinuousLinearMap.exists_preimage_norm_le` and `ContinuousLinearMap.isOpenMap` (the open
  mapping theorem over a field, `Mathlib/Analysis/Normed/Operator/Banach.lean`); `banach_steinhaus`;
  `LinearMap.continuous_of_finiteDimensional`, `FiniteDimensional.complete`,
  `LinearMap.exists_antilipschitzWith` and `ContinuousLinearMap.isOpen_injective` over a complete
  nontrivially normed field. ⚠ All of these take a field of scalars; the ring versions are Layer 1.
- `ZeroAtInftyContinuousMap` (`C₀(α, β)`), with `NormedAddCommGroup`, `NormedSpace 𝕜`,
  `CompleteSpace`, the `Module R` instance for `[ContinuousConstSMul R β]`, and
  `ContinuousMap.liftZeroAtInfty : C(α, β) ≃ C₀(α, β)` for compact `α`; `lp` for `ℓ^∞`;
  `BoundedContinuousFunction`; `ContinuousMap` with its `NormedRing` and `NormedAlgebra` instances
  for a compact domain; `LocallyConstant` and `LocallyConstant.toContinuousMap`. ⚠ Mathlib has no
  density theorem for locally constant functions in `C(X, E)` for profinite `X`; §3.1 supplies it.
- `PadicInt.compactSpace`, `PadicInt.totallyBounded_univ`, `Padic.instProperSpace`;
  `IsUltrametricDist → TotallySeparatedSpace`, so `ℤ_[p]` is profinite; `PadicInt.toZModPow` and
  `PadicInt.ker_toZModPow`; `PadicInt.isUnit_iff`; `Padic.addValuation`;
  `sub_one_mul_padicValNat_factorial` (Legendre's formula) and `padicValNat_factorial_le`.
- `Ring.choose`, `Ring.multichoose`, the `BinomialRing` API and `IsAddTorsionFree ℤ_[p]`; `fwdDiff`
  (`Δ_[h]`), `fwdDiff_iter_eq_sum_shift` and `shift_eq_sum_fwdDiff_iter`.
- `PadicInt.mahler`, `PadicInt.mahlerTerm`, `PadicInt.mahlerSeries`, `PadicInt.hasSum_mahler`,
  `PadicInt.fwdDiff_tendsto_zero`, `PadicInt.mahlerEquiv` and
  `IsUltrametricDist.norm_fwdDiff_iter_apply_le`.
- `AbstractMeasure X R E` and `D(X, R)`, `AbstractMeasure.dirac`, `AbstractMeasure.map`,
  `AbstractMeasure.prodMk`, `AbstractMeasure.toCLMEquiv`, and the weak and strong topologies of
  `Mathlib/NumberTheory/Padics/Measure/Topology.lean`.
- `PadicInt.addChar_of_value_at_one`, `PadicInt.continuousAddCharEquiv` and
  `PadicInt.continuousAddCharEquiv_of_norm_mul`; `ContinuousMonoidHom` with the notation `→ₜ*`.
- `PowerSeries.IsRestricted c f` and `MvPowerSeries.IsRestricted`, `MvPowerSeries.gaussNorm`,
  `MvPowerSeries.HasGaussNorm`, `Polynomial.gaussNorm`; ⚠ Mathlib has the *predicate* "restricted",
  not the ring `R⟨X⟩`; the ring is `TauCeti.RingTheory.Huber.Restricted.PowerSeries` (adic-spaces
  roadmap §0.5), and §4.1 identifies it with `C₀(ℕ, R)` as a Banach module.
- `PowerSeries` with its product topology (`Mathlib/RingTheory/PowerSeries/PiTopology.lean`), which
  on `ℤ_[p]⟦T⟧` is the `(p, T)`-adic topology; `MonoidAlgebra`.
- `PadicAlgCl p`, `ℂ_[p]` and `𝓞_ℂ_[p]`; `spectralNorm`; `hensels_lemma`.
- `TauCeti.Huber.IsTateRing`, `TauCeti.Huber.IsPseudoUniformizer`, `TauCeti.Huber.PairOfDefinition`,
  `TauCeti.Huber.powerBoundedSubring`, `TauCeti.Huber.topologicallyNilpotentIdeal`, Henkel's open
  mapping theorem `TauCeti.HasZeroSequenceOfUnits.isOpenMap` with its Tate-ring instances, and
  `TauCeti.Huber.isUnit_one_sub_of_isTopologicallyNilpotent_entries` (Tau Ceti, adic-spaces
  roadmap Layer 0). Layer 0 bridges to the first two, Layer 1 derives its quantitative open mapping
  theorem from the fourth, and §1.5 uses the last.

⚠ Mathlib has **no** orthonormal basis in the nonarchimedean sense (`OrthonormalBasis` is the
inner-product notion and unrelated), **no** operator norm over a normed ring, **no** open mapping
theorem over a ring, **no** locally analytic function, **no** exponential or logarithm with a
`p`-adic convergence disc (`NormedSpace.exp` is defined, but its convergence results are stated for
`RCLike` fields), **no** Amice transform, **no** Iwasawa algebra beyond the docstring of
`AbstractMeasure`, and **no** weight space. `WittVector.teichmuller` is the Witt-vector Teichmüller
map and is not the section `μ_{p−1} → ℤ_p^×` of §5.1.

---

## Layer 0: ultrametric sums and nonarchimedean Banach modules

No `p`, and no field. `R` is a nonarchimedean normed ring — `[NormedRing R] [IsUltrametricDist R]`,
with `[NormOneClass R]` and `[CompleteSpace R]` where stated — and `M`, `N` are normed `R`-modules in
the sense of convention 1. Everything here is the bookkeeping that the later layers use on every
page, stated once.

### 0.1 Sums in complete ultrametric groups

`E` is a complete ultrametric normed additive group.

1. Record Mathlib's criterion in the form the later layers use: a family `f : ι → E` is summable if
   and only if `f → 0` along the cofinite filter (`NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`),
   and such a family has bounded norms (`BddAbove (Set.range (‖f ·‖))`).
2. **The ultrametric bound.** For `f → 0` cofinitely, `‖∑' i, f i‖ ≤ ⨆ i, ‖f i‖`, and the supremum
   is attained when some `f i ≠ 0`. State the `nnnorm` form as well.
3. **The strict bound and the unique dominant term.** If `‖f i‖ < B` for every `i` and `f → 0`
   cofinitely, then `‖∑' f‖ < B`; if `‖f i₀‖ > ‖f i‖` for every `i ≠ i₀`, then `‖∑' f‖ = ‖f i₀‖`.
   The second is the engine of every "leading term" argument in the later layers (the Gauss norm of
   a product, the sharpness of an estimate at a halo point).
4. **Double sums.** For `f : ι × κ → E` tending to `0` cofinitely, both iterated sums exist and
   equal `∑' p, f p`; and for `f : ι → E`, `g : κ → E` and a bilinear continuous map with
   `‖b x y‖ ≤ ‖x‖ ‖y‖`, the family `b (f i) (g j)` tends to `0` cofinitely and its sum is
   `b (∑' f) (∑' g)`. Mathlib's `tsum_mul_tsum_of_nonarchimedean` is the case of a ring, and the
   module form is what the matrix product of §2.6 needs.
5. The sum is continuous and `1`-Lipschitz in the sup norm: for `f, g → 0` cofinitely,
   `‖∑' f − ∑' g‖ ≤ ⨆ i, ‖f i − g i‖`; and a null family of null families sums to a null family.

### 0.2 Nonarchimedean normed rings

`R` is a nonarchimedean normed ring with `‖1‖ = 1`.

1. The closed unit ball `R⁰ := {r | ‖r‖ ≤ 1}` is a subring, the open unit ball
   `R⁰⁰ := {r | ‖r‖ < 1}` is an ideal of `R⁰`, and `R⁰⁰` is contained in the topological nilradical
   of `R⁰`. Every element of `R⁰` is power-bounded and every element of `R⁰⁰` is topologically
   nilpotent (`TauCeti.Huber.IsPowerBounded`, `IsTopologicallyNilpotent`).
2. **The converses need a multiplicative norm.** If the norm is multiplicative (`NormMulClass R`)
   and `0` is not isolated, then an element is power-bounded if and only if `‖r‖ ≤ 1` and
   topologically nilpotent if and only if `‖r‖ < 1`; so `R⁰ = R°` and `R⁰⁰ = R°°` in the notation
   of the adic-spaces roadmap. Record the two counterexamples: over `ℤ` with the discrete topology
   every element is power-bounded while `‖2‖ = 2`, and in `ℝ[X]/(X² − X)` with the `ℓ¹` norm the
   element `1 − 2X` squares to `1` and has norm `3`.
3. **The Neumann series.** If `R` is complete and `‖x‖ < 1`, then `1 − x` is a unit with inverse
   `∑' n, x ^ n`, `‖(1 − x)⁻¹‖ = 1` and `‖(1 − x)⁻¹ − 1‖ = ‖x‖`; Mathlib's `Units.oneSub` is the
   unit, and the ultrametric equalities are new. Deduce that the units of `R⁰` are exactly the
   elements of `R⁰` whose image in `R⁰/R⁰⁰` is a unit, and that `R⁰⁰` is the unique maximal ideal of
   `R⁰` when the norm is multiplicative.
4. A *multiplicative element* is an `a` with `‖a x‖ = ‖a‖ ‖x‖` for all `x`. Products and powers of
   multiplicative elements are multiplicative; a unit `u` is multiplicative if and only if
   `‖u⁻¹‖ = ‖u‖⁻¹`; and for a multiplicative unit `u` and any normed `R`-module `M`,
   `‖u • m‖ = ‖u‖ ‖m‖`.

### 0.3 Banach modules over nonarchimedean rings

1. **Constructions.** `R` itself; a closed submodule with the restricted norm; the quotient by a
   closed submodule with the quotient norm `‖x + N‖ = inf ‖x + n‖`, which is again ultrametric and
   complete; finite products with the max norm; `C₀(I, M)` for a discrete `I` and `C(X, M)` for a
   compact `X` (§2.1, §3.1). Each is a Banach `R`-module when its inputs are.
2. **Equivalent norms.** Two norms on `M` are *bounded-equivalent* if each is bounded by a constant
   times the other; bounded-equivalent norms have the same bounded maps and the same Cauchy
   sequences. Prove that over a Tate normed ring (§0.4) equivalence of norms (same topology) already
   implies a power comparison, in the form of Johansson–Newton's Lemmas 2.1.6 and 2.1.7: if two norms
   on `R` inducing the same topology have multiplicative pseudo-uniformisers `ϖ` and `π`, then
   `‖a‖_ϖ ≤ C₁` when `‖a‖_π < 1` and `‖a‖_ϖ ≤ C₂ ‖a‖_π ^ s` when `‖a‖_π ≥ 1`; and if `ϖ` is
   multiplicative for both, `C₁ ‖a‖₁ ^ s ≤ ‖a‖₂ ≤ C₂ ‖a‖₁ ^ s` with `s` determined by
   `‖ϖ‖₂ = ‖ϖ‖₁ ^ s`. ⚠ The published statement of Lemma 2.1.6 is incorrect; the form above is the
   corrected one of arXiv:1604.07739v4.
3. **Rescaling to a discrete value set.** Let `π` be a multiplicative unit of `R` with
   `0 < ‖π‖ < 1`. Define the rescaled norm `‖m‖' := inf {‖π‖ ^ n | n : ℤ, ‖m‖ ≤ ‖π‖ ^ n}` on any
   normed `R`-module `M`; prove it is a norm taking values in `‖π‖ ^ ℤ ∪ {0}`, ultrametric, with
   `‖π‖ ‖m‖' < ‖m‖ ≤ ‖m‖'`, hence bounded-equivalent to the original, complete when the original is,
   and with `‖π • m‖' = ‖π‖ ‖m‖'`. This is Serre's first step and Bellaïche's Theorem II.1.13's
   only analytic input.
4. **Residue modules.** For `π` as above, `M⁰ := {m | ‖m‖ ≤ 1}` is an `R⁰`-submodule and
   `M̃ := M⁰ / π M⁰` is a module over `R̃ := R⁰ / π R⁰`. Prove that if the norm of `M` takes values in
   `‖π‖ ^ ℤ ∪ {0}` then `π M⁰ = {m | ‖m‖ < 1}`, so that `M̃` is the reduction of the unit ball modulo
   its open ball. This is the module Serre's theorem (§2.3) tests for freeness.

### 0.4 Banach–Tate rings

1. Define `PseudoUniformizer R`: a unit `ϖ` of `R` that is multiplicative with `‖ϖ‖ < 1`; and the
   Prop class `NormedRing.IsTate R`, the existence of one (convention 2). A Tate normed ring is
   nontrivial, and `‖ϖ⁻¹‖ = ‖ϖ‖⁻¹`.
2. **The scaling trick.** For `ϖ : PseudoUniformizer R` and `m ≠ 0` in a normed `R`-module, there
   is a unique `n : ℤ` with `‖ϖ‖ < ‖ϖ ^ n • m‖ ≤ 1`. This replaces every use of a ground field: it
   is how `ρ`-scaling in Buzzard and `ϖ`-scaling in Johansson–Newton are performed, and Layer 1 is
   built on it.
3. **The valuation `v_ϖ`.** Define `PseudoUniformizer.val ϖ : R → WithTop ℝ` by
   `val ϖ r = −log ‖r‖ / log ‖ϖ⁻¹‖`, with `val ϖ 0 = ⊤`, so that `val ϖ ϖ = 1`. It is order-reversing
   in the norm, `val ϖ (r * s) ≥ val ϖ r + val ϖ s` with equality when the norm is multiplicative,
   `val ϖ (r + s) ≥ min`, and `‖r‖ = ‖ϖ‖ ^ (val ϖ r)`. ⚠ It is **not** an `AddValuation` unless the
   norm is multiplicative, and no bundled structure is introduced for it. When `R` is an ultrametric
   normed field, `val ϖ` is the real additive valuation `normAddVal` of the Newton-polygons roadmap
   (§1.2) rescaled by `−log ‖ϖ‖`; state this seam so that the two developments do not fork.
4. **The bridge from Banach algebras.** A normed algebra over a nontrivially normed field
   (`[NormedAlgebra K R] [NormOneClass R]`) is a Tate normed ring, with `ϖ = λ • 1` for any scalar
   `0 < ‖λ‖ < 1`. In particular every nonarchimedean nontrivially normed field is Banach–Tate, and
   every result of Layers 1–2 stated over a Banach–Tate ring specialises to Buzzard's and
   Bellaïche's field-based statements along this instance.
5. **The bridge to Huber's Tate rings.** A Tate normed ring is a Tate ring in Huber's sense: its
   unit ball `R⁰` and the ideal `(ϖ)` form a pair of definition, `ϖ` is a topologically nilpotent
   unit, and the ideal powers are the norm balls, `ϖⁿ R⁰ = {r ∈ R⁰ | ‖r‖ ≤ ‖ϖ‖ ^ n}`, so that the
   `(ϖ)`-adic topology of `R⁰` is the norm topology. State it as an instance of
   `TauCeti.Huber.IsTateRing` and of `TauCeti.Huber.IsPseudoUniformizer` for `ϖ`.
6. **The bridge back.** If `A` is a Hausdorff Tate ring with a ring of definition `A₀` and a
   topologically nilpotent unit `ϖ ∈ A₀`, then for any real `a > 1` the function
   `‖r‖ := inf {a ^ (−n) | n : ℤ, r ∈ ϖ ^ n A₀}` is an ultrametric submultiplicative norm with
   `‖1‖ = 1` inducing the topology of `A`, whose unit ball is `A₀` and for which `ϖ` is a
   multiplicative pseudo-uniformiser (Johansson–Newton, Remark 2.1.3(1)). ⚠ The Hausdorff hypothesis
   is necessary: without it the formula gives only a seminorm, with kernel the closure of `0`.
7. **Examples.** A nonarchimedean nontrivially normed field with any nonzero element of norm less
   than `1`; `R⟨X⟩` over a Tate normed ring `R` with `ϖ ↦ ϖ` (§4.1); the ring `Λ^{>1/p}[1/T]` with
   `ϖ = T` (§5.6). A non-example: `ℤ_[p]`, whose norm has no unit of norm less than `1`; this is
   the example the adic-spaces roadmap gives of a Huber ring that is not Tate.

### Examples

`ℚ_p`, `ℂ_p`, and `ℤ_p` as normed rings, with `R⁰`, `R⁰⁰`, and the residue ring in each case; the
Neumann inverse of `1 − p` in `ℤ_p`; the shells `‖ϖ‖ < ‖ϖⁿ x‖ ≤ 1` in `ℚ_p` with `ϖ = p`; the
rescaled norm on `ℂ_p` with `π = p`, which takes values in `p^ℤ` and is not the original norm; the
Tate normed ring `ℚ_p⟨X⟩` and its pair of definition `(ℤ_p⟨X⟩, (p))`.

### Dependencies

Mathlib; the adic-spaces roadmap for the Huber-side vocabulary of §0.4.5–6 (already in Tau Ceti).

---

## Layer 1: bounded linear maps

`R` is a Tate normed ring with a chosen `ϖ : PseudoUniformizer R` where scaling is used, and `M`,
`N` are normed `R`-modules, Banach where stated.

### 1.1 The operator norm

1. Define the operator norm on `M →L[R] N` by Mathlib's formula
   `‖u‖ = sInf {c | 0 ≤ c ∧ ∀ x, ‖u x‖ ≤ c * ‖x‖}` as a scoped instance (convention 6), for a
   semiring `R` and seminormed modules, and prove the lemmas that need nothing more: `‖u‖ ≥ 0`,
   `‖0‖ = 0`, `‖−u‖ = ‖u‖`, `‖u‖ ≤ C` from a uniform bound `∀ x, ‖u x‖ ≤ C ‖x‖`, and
   `‖u x‖ ≤ ‖u‖ ‖x‖` for any `u` admitting some uniform bound.
2. Over a Tate normed ring, a linear map is continuous if and only if it is bounded, if and only
   if it is bounded on the unit ball (by the scaling trick); hence `‖u x‖ ≤ ‖u‖ ‖x‖` for every
   `u : M →L[R] N`, and `‖u‖ = sup_{‖x‖ ≤ 1} ‖u x‖`. ⚠ Over a general normed ring continuity does not
   imply boundedness: the identity map from `ℤ_p` with the norm `‖x‖²` (a normed `ℤ_p`-module) to
   `ℤ_p` with its norm is continuous and unbounded. The Tate hypothesis is exactly what is needed.
3. The operator norm is a complete ultrametric norm on `M →L[R] N` when `N` is complete; it is
   submultiplicative under composition, `‖1‖ ≤ 1` with equality when `M ≠ 0`, and it makes
   `M →L[R] M` a nonarchimedean Banach ring; `‖a • u‖ ≤ ‖a‖ ‖u‖`, with equality for multiplicative
   `a`.
4. **Ultrametric estimates for sums of operators.** For a family `uᵢ` of operators tending to `0`
   cofinitely in norm, `∑' uᵢ` converges in operator norm and pointwise, and
   `‖∑' uᵢ‖ ≤ sup ‖uᵢ‖`.
5. **Neumann series in the endomorphism ring.** If `M` is complete and `‖1 − u‖ < 1`, then `u` is
   invertible in `M →L[R] M` with `‖u⁻¹‖ = 1`; the units of `M →L[R] M` are open. This is
   `Units.oneSub` applied to the Banach ring of clause 3, and it is recorded because the field case
   is used constantly and the ring case is what the compact-operators roadmap needs.
6. **Agreement with Mathlib.** When `R` is a nontrivially normed field and `M`, `N` are normed
   spaces, the scoped norm equals `ContinuousLinearMap.opNorm` on the nose, and every lemma of
   clauses 1–5 is either Mathlib's or reduces to it.

### 1.2 The open mapping theorem and its companions

`R` is Banach–Tate and `M`, `N` are Banach `R`-modules.

1. **The quantitative open mapping theorem.** A surjective `u : M →L[R] N` admits a constant
   `C > 0` such that every `n : N` has a preimage `m` with `‖m‖ ≤ C ‖n‖`. Derive it from Tau Ceti's
   topological open mapping theorem over a Tate ring (`TauCeti.HasZeroSequenceOfUnits.isOpenMap`,
   Henkel's theorem, whose hypotheses `CompleteSpace`, `NonarchimedeanAddGroup` and `T0Space` are
   supplied by the Banach hypotheses here): openness gives a ball `B_N(0, ε) ⊆ u (B_M(0, 1))`, and
   the scaling trick turns `ε` into `C`. This is Huber's Lemma 2.4(i) as Johansson–Newton cite it,
   and Bellaïche's proof of his Lemma 3.1.12 is its first use.
2. A bijective `u : M →L[R] N` is a continuous linear equivalence, and a continuous linear map
   with closed range is strict: the induced map `M / ker u → range u` is a continuous linear
   equivalence, and the quotient norm and the subspace norm are bounded-equivalent.
3. **The closed graph theorem.** A linear map `M → N` with closed graph is continuous.
4. **Banach–Steinhaus.** A family `uᵢ : M →L[R] N` that is pointwise bounded is uniformly bounded:
   `sup_i ‖uᵢ‖ < ∞`. The proof is the Baire category argument with the scaling trick in place of
   scalar division. Deduce that a pointwise limit of continuous linear maps from a Banach module is
   continuous.
5. **Bounded maps out of a finite free module.** Every `R`-linear map `R ^ n → M` is continuous,
   with norm the maximum of the norms of the images of the basis vectors.

### 1.3 Finite-dimensional spaces over a complete field

`K` is a complete nonarchimedean nontrivially normed field. Record, for the later layers, Mathlib's
theorems that every linear map out of a finite-dimensional normed `K`-space is continuous, that every
finite-dimensional normed `K`-space is complete and all its norms are equivalent, and that a
finite-dimensional subspace is closed; add that the sup norm on `K ^ n` is ultrametric, and that a
finite-dimensional space with an ultrametric norm has an orthogonal basis when `K` is discretely
valued and a `t`-orthogonal basis for every `t < 1` in general (the finite case of §2.4).

### 1.4 Finitely generated modules over Noetherian Banach–Tate rings

`R` is a Noetherian Banach–Tate ring.

1. Cite the adic-spaces roadmap for: every ideal of `R` is closed; every finitely generated
   `R`-module carries a unique complete topology making it a topological `R`-module, and every
   `R`-linear map between finitely generated modules is continuous and strict (Bosch–Güntzer–Remmert
   §3.7.2–3.7.3, transported to Banach–Tate rings by Johansson–Newton). Prove here their normed
   reading: any two Banach norms on a finitely generated module are bounded-equivalent, and a
   Banach norm exists (the quotient norm from `R ^ n`).
2. **Closedness of finitely generated submodules.** Every submodule of a module-finite Banach
   `R`-module is closed (Fresnel–van der Put, Lemma 1.2.3; Kedlaya's transcription): the closure of
   a submodule is finitely generated, the quotient map from a free module is open, and a geometric
   density iteration finishes. The matrix input — `1 − B` is a unit for a matrix `B` with
   topologically nilpotent entries — is `TauCeti.Huber.isUnit_one_sub_of_isTopologicallyNilpotent_entries`.
3. ⚠ **Not every finitely generated submodule of a Banach module is closed.** Record a
   counterexample over a non-Noetherian Banach–Tate ring, and state the closedness of finitely
   generated submodules of the model space `C₀(I, R)` over Noetherian `R` as a milestone of §2.6,
   where the truncations that prove it live. Bellaïche's book assumes this closedness outright
   (his Hypothesis 3.1.8) to avoid Noetherianity; Ludwig's Remark 2.25 observes that it is all that
   is ever used.

### Examples

The operator norm of coordinate evaluation `C₀(I, R) → R` is `1`; multiplication by `a` on `R` has
norm `‖a‖` when `a` is multiplicative and can be smaller otherwise; the open mapping constant for
the quotient map `R ² → R`, `(x, y) ↦ x + ϖ y`; a continuous bijection of Banach `ℚ_p`-spaces whose
inverse has norm `p`; the diagonal operator `diag(dₙ)` on `C₀(ℕ, R)` with `‖dₙ‖ ≤ 1` and its
invertibility when the `dₙ` are multiplicative units of norm `1`.

### Dependencies

Layer 0; Mathlib's field-scalar theorems for §1.1.6 and §1.3; the adic-spaces roadmap for §1.4.1
and for Henkel's theorem in §1.2.1 (both already in Tau Ceti).

---

## Layer 2: the model space and orthonormal bases

`R` is a nonarchimedean Banach ring with `‖1‖ = 1`; `I`, `J` are discrete topological types
(convention 3). Banach–Tate is assumed where the operator norm of Layer 1 is used.

### 2.1 The model space `C₀(I, R)`

1. Add to `C₀(I, E)`, for a discrete `I` and an ultrametric normed group `E`, the instances
   Mathlib lacks: `IsUltrametricDist`, and for a normed ring `R` with bounded action on `E`,
   `Module R C₀(I, E)` with `IsBoundedSMul R C₀(I, E)` (and `NormSMulClass` when `E` has it). Prove
   the sup-norm formula `‖f‖ = ⨆ i, ‖f i‖`, that the supremum is attained when `f ≠ 0`, that
   `f → 0` cofinitely, and that `C₀(I, E)` is complete when `E` is.
2. The coordinate vectors `single i r`, the coordinate functionals `eval i : C₀(I, R) →L[R] R` of
   norm `1`, and the expansion `f = ∑' i, f i • single i 1`, convergent in norm; finitely supported
   families are dense.
3. **The universal property.** For a Banach `R`-module `M`, bounded families `I → M` correspond to
   continuous linear maps `C₀(I, R) →L[R] M` by `m ↦ (f ↦ ∑' i, f i • m i)`, with
   `‖u‖ = sup ‖m i‖` (Buzzard §2). In particular the dual of `C₀(I, R)` is `ℓ^∞(I, R)` (§2.5).
4. **Reindexing and blocks.** A bijection `I ≃ J` induces an isometry `C₀(I, R) ≃ₗᵢ[R] C₀(J, R)`;
   `C₀(I ⊕ J, R) ≃ₗᵢ C₀(I, R) × C₀(J, R)` with the max norm; `C₀(I × J, R) ≃ₗᵢ C₀(I, C₀(J, R))`;
   and for a finite `σ`, `C₀(σ × I, R) ≃ₗᵢ (σ → C₀(I, R))`, the block decomposition that the
   compact-operators and overconvergent-forms roadmaps use to assemble operators from `σ × σ`
   matrices of operators.
5. **Functoriality in the ring.** A bounded ring homomorphism `φ : R → S` induces
   `C₀(I, R) → C₀(I, S)` of norm at most the bound of `φ`, an isometry when `φ` is, and compatible
   with `single`, `eval`, and reindexing.

### 2.2 Orthogonal and orthonormal families

Fix a Banach `R`-module `M` and a family `e : I → M`.

1. Define `IsOrthogonalFamily e`, `IsOrthonormalFamily e`, and `IsTOrthogonalFamily t e` for
   `0 < t ≤ 1` (convention 5), and prove: orthonormal implies orthogonal implies `t`-orthogonal;
   an orthogonal family with nonzero members is linearly independent; the scaled family `aᵢ • eᵢ`
   of an orthogonal family is orthogonal; and for an orthonormal family the map
   `C₀(I, R) → M`, `a ↦ ∑' aᵢ • eᵢ` is an isometric embedding.
2. Define `IsOrthonormalBasis e`: an orthonormal family whose closed span is `M`. Prove the
   equivalent formulations: every `x` has a unique expansion `x = ∑' aᵢ • eᵢ` with `a → 0`
   cofinitely, and then `‖x‖ = sup ‖aᵢ‖` (Bellaïche's Definition II.1.5, Colmez's Définition 1.1.3);
   and the expansion coefficients are continuous linear functionals.
3. **`IsONable` and bases.** `IsONable R M ↔ ∃ (I : Type) (e : I → M), IsOrthonormalBasis e`, and an
   isometry `M ≃ₗᵢ C₀(I, R)` corresponds to the basis `i ↦ e⁻¹ (single i 1)`. State
   `IsPotentiallyONable` and `HasPr` and the implications `IsONable → IsPotentiallyONable → HasPr`;
   prove that `C₀(I, R)` is ON-able with the canonical basis, that all three notions are stable under
   reindexing, finite products, `C₀(J, −)`, and bounded-equivalent norms (potentially ON-able and
   (Pr) only), and that a closed direct summand of a potentially ON-able module has (Pr).
4. **The lifting characterisation of (Pr).** A Banach module `P` has property (Pr) if and only if
   every continuous surjection `M → N` of Banach modules and every continuous map `P → N` admit a
   continuous lift `P → M` (Bellaïche, Exercise II.1.19); a finitely generated module with (Pr) is
   projective (Bellaïche, Proposition II.1.20).
5. **Orthogonal complements and projections.** For an orthonormal basis `e` and a subset `S ⊆ I`,
   the closed span of `e|_S` is a closed direct summand with the projection `π_S` of norm at most
   `1`, and `M ≅ C₀(S, R) × C₀(I ∖ S, R)`.

### 2.3 Serre's theorem

Let `R` be Banach–Tate with a pseudo-uniformiser `π` whose norm is the largest norm less than `1`,
so that `‖R ∖ {0}‖ = ‖π‖ ^ ℤ` (Bellaïche's Hypothesis II.1.11), and write `R̃ := R⁰ / π R⁰`.

1. **Residue-basis lifting.** Let `M` be a Banach `R`-module whose norm takes values in
   `‖π‖ ^ ℤ ∪ {0}`, and `e : I → M⁰`. Then `e` is an orthonormal basis of `M` if and only if the
   reductions `ẽᵢ` form a basis of the `R̃`-module `M̃ = M⁰ / π M⁰` (Bellaïche, Lemma II.1.12;
   Colmez, Proposition 1.1.5). The "if" direction is the successive `π`-adic approximation
   `m = ∑ aᵢ eᵢ + π m₁`, iterated, with the coefficients converging by completeness of `R`; the
   "only if" direction is the reduction of the sup-norm identity.
2. **Serre's theorem, ring form.** Under the same hypotheses, `M` is orthonormalisable if and only
   if `M̃` is a free `R̃`-module; and every Banach `R`-module is potentially orthonormalisable as soon
   as `R̃` has the property that all its modules are free — in particular when `R̃` is a field.
3. **Serre's theorem, field form.** Every Banach space over a discretely valued nonarchimedean
   field `K` is potentially orthonormalisable, and it is orthonormalisable on the nose if and only
   if its norm takes values in `‖K‖` (Serre, §1, Proposition 1; Schneider, Proposition 10.1 and
   Remark 10.2; Bellaïche, Theorem II.1.13). The equivalent norm is the rescaled norm of §0.3.3 at a
   uniformiser, and the index set is a basis of the residue vector space `M̃`.
4. **The index is an invariant.** `C₀(I, K)` and `C₀(J, K)` are topologically isomorphic if and
   only if `I` and `J` have the same cardinality (Schneider, Lemma 10.3).
5. ⚠ The discreteness hypothesis cannot be dropped for orthonormal bases on the nose: for odd `p`,
   `ℂ_p` itself with the norm `2‖·‖` has no orthonormal basis, since `‖ℂ_p‖ = p^ℚ` does not contain
   `1/2`; the potential statement is §2.4.

### 2.4 Banach spaces of countable type

`K` is a complete nonarchimedean nontrivially normed field, not assumed discretely valued.

1. A `K`-Banach space with a dense subspace of countably infinite dimension is topologically
   isomorphic to `C₀(ℕ, K)` (Schneider, Proposition 10.4); the proof constructs, for each `t < 1`,
   a `t`-orthogonal sequence spanning a dense subspace, by the inductive distance argument, and the
   scaled sequence is a potential orthonormal basis. Hence such a space is potentially
   orthonormalisable over any `K`.
2. A `K`-Banach space of countable type has a `t`-orthogonal basis for every `0 < t < 1`, and an
   orthogonal basis when `K` is discretely valued (van Rooij; Perez-Garcia–Schikhof). Record that
   over a non-discretely-valued `K` a `1`-orthogonal basis need not exist.
3. A closed subspace of a space of countable type is of countable type and is complemented by a
   closed subspace; a quotient of a space of countable type is of countable type.

### 2.5 The dual of the model space

1. For a Banach–Tate ring `R`, the continuous dual of `C₀(I, R)` is `ℓ^∞(I, R)` (bounded families,
   sup norm) isometrically, by the universal property §2.1.3: a functional is determined by its
   values on the coordinate vectors, and `‖λ‖ = sup ‖λ (single i 1)‖`. State it as an isometry of
   Banach `R`-modules `(C₀(I, R) →L[R] R) ≃ₗᵢ[R] lp (fun _ : I ↦ R) ∞`, using Mathlib's `lp`.
2. The pairing `ℓ^∞(I, R) × C₀(I, R) → R`, `⟨λ, f⟩ = ∑' λᵢ fᵢ`, is continuous with
   `‖⟨λ, f⟩‖ ≤ ‖λ‖ ‖f‖`, and the evaluation `C₀ → (C₀)'' = (ℓ^∞)'` is an isometric embedding.
   ⚠ It is not surjective: `C₀(ℕ, K)` is not reflexive, and nothing about reflexivity is in scope.
3. For an orthonormalisable `M` with basis `e`, the dual is identified with bounded families
   indexed by the basis, and the transpose of `u : M →L[R] N` between orthonormalisable modules has
   the transposed matrix (§2.6).

### 2.6 Matrices of bounded operators

`R` is Banach–Tate.

1. **Matrix coefficients.** For `u : C₀(J, R) →L[R] C₀(I, R)` define `matrixCoeff u i j` as in
   convention 7 and prove: each column tends to `0` cofinitely, `‖u‖ = sup_{i,j} ‖matrixCoeff u i j‖`,
   and `(u f) i = ∑' j, matrixCoeff u i j * f j`. Conversely a matrix `a : I → J → R` whose columns
   tend to `0` cofinitely and whose entries are bounded is the matrix of a unique bounded operator,
   of norm `sup ‖a i j‖` (Buzzard §2; Bellaïche §II.1.3). The matrix of a composite is the matrix
   product, with the middle sum convergent by §0.1.4.
2. **Diagonal and permutation operators.** The diagonal operator of a bounded family `d : I → R`
   has norm `sup ‖dᵢ‖`; it is an isometric automorphism when every `dᵢ` is a multiplicative unit of
   norm `1`, and injective with dense range when every `dᵢ` is a non-zero-divisor, which is the case
   of `diag(⌊n/pʰ⌋!)` in §4.4. The permutation operator of `σ : I ≃ I` is an isometric automorphism.
3. **Coordinate truncations.** For a finite `S ⊆ I`, the truncation `π_S : C₀(I, R) →L[R] C₀(I, R)`
   (restriction of coordinates to `S`) has norm at most `1`, has range the finite free module on
   `S`, and `π_S ∘ u → u` pointwise along the filter of finite subsets for every bounded `u` into
   `C₀(I, R)`; the compact-operators roadmap will characterise the `u` for which the convergence is
   in operator norm.
4. **Approximation of finitely generated closed submodules.** If `P ⊆ C₀(I, R)` is a finitely
   generated closed submodule, then for every `ε > 0` there is a finite `S` with
   `‖π_S p − p‖ ≤ ε ‖p‖` for all `p ∈ P` (Bellaïche, Lemma 3.1.12). The proof is the open mapping
   theorem applied to a surjection `R ^ r → P`, which is why closedness is a hypothesis. ⚠ Without
   closedness the statement is false; record the counterexample.
5. **Closedness over Noetherian rings.** If `R` is Noetherian, some truncation is injective on any
   finitely generated submodule of `C₀(I, R)`, and every finitely generated submodule of `C₀(I, R)`
   is closed (Buzzard, Lemma 2.3; Ludwig, Lemma 2.26). This discharges the hypothesis of clause 4
   over Noetherian bases and is the statement §1.4.3 defers to here.
6. **Base change of matrices.** For a bounded ring homomorphism `φ : R → S`, the operator
   `C₀(J, S) → C₀(I, S)` with matrix `φ (matrixCoeff u i j)` exists, is `φ`-semilinearly compatible
   with `u`, and has norm at most `‖φ‖ ‖u‖`; a bicontinuous ring isomorphism transports bounded
   operators (Johansson–Newton, Proposition 2.1.8, the part that does not mention compactness).

### 2.7 The unitriangular-perturbation criterion

`R` is a nonarchimedean Banach ring with `‖1‖ = 1`, and `q < 1`.

1. A matrix `a : ℕ → ℕ → R` is a *unitriangular perturbation of level `q`* if all entries have
   norm at most `1`, every diagonal entry is a multiplicative unit of norm `1`, every entry
   strictly below the diagonal (`i > j`) has norm at most `q`, and every column is finitely
   supported. Prove that such a matrix is the matrix of a bounded operator `T` of `C₀(ℕ, R)`, that
   `T` is an isometry (`‖T f‖ = ‖f‖`, by the largest-index argument: the largest index at which
   `‖fⱼ‖` is attained contributes a term that no other term can cancel), and that `T` is surjective
   (successive approximation with contraction factor `q`), hence an isometric automorphism.
2. State the criterion for a family: if `e : ℕ → M` is a family in an orthonormalisable Banach
   module whose matrix in an orthonormal basis, after a reindexing by a bijection of `ℕ`, is a
   unitriangular perturbation, then `e` is an orthonormal basis. This is the form in which Amice's
   theorem (§4.4) is proved.
3. Record the relation to Colmez's Proposition 1.1.5: over a discretely valued field the criterion
   follows from §2.3.1 by reduction modulo the uniformiser, since a triangular matrix with unit
   diagonal is invertible over the residue field; the criterion above needs no discreteness and no
   residue field, and this is why the statement is made over any nonarchimedean Banach ring.

### Examples

`C₀(ℕ, ℚ_p)` with its canonical basis and its dual `ℓ^∞(ℕ, ℚ_p)`; the Banach space `C(ℤ_p, ℚ_p)` is
orthonormalisable (Layer 3 exhibits the basis, this layer only knows it from Serre's theorem);
`ℂ_p` with the norm `2‖·‖` (`p` odd) is potentially but not literally orthonormalisable; a finite-dimensional
`ℂ_p`-space with a norm whose values are not in `p^ℚ`; the matrix of the shift on `C₀(ℕ, R)`; the
unitriangular perturbation `1 + N` with `N` strictly lower triangular of norm `q`, and a matrix with
entries in `ℤ_p`, unit diagonal, and lower entries in `pℤ_p`.

### Dependencies

Layers 0 and 1; Mathlib's `C₀` and `lp`.

---

## Layer 3: continuous functions on `ℤ_p` and measures

`E` is a complete ultrametric normed `ℤ_[p]`-module — `[NormedAddCommGroup E] [Module ℤ_[p] E]
[IsBoundedSMul ℤ_[p] E] [IsUltrametricDist E] [CompleteSpace E]`, Mathlib's hypotheses for
`PadicInt.mahlerEquiv` — and `R` is a complete ultrametric normed `ℤ_[p]`-algebra when a ring is
needed. Nothing in this layer is specific to `ℤ_p` until §3.2, and §3.1 is stated for a profinite
space `X`.

### 3.1 Continuous functions on a profinite space

1. For `X` compact and `E` an ultrametric normed group, `C(X, E)` with the sup norm is ultrametric,
   complete when `E` is, and a Banach `R`-module when `E` is; `C(X, R)` is a nonarchimedean Banach
   ring. Add the missing `IsUltrametricDist` instances (convention 1) and record that
   `ContinuousMap.liftZeroAtInfty` is an isometry `C(X, E) ≃ C₀(X, E)`.
2. **Locally constant functions are dense.** For `X` profinite (compact, Hausdorff, totally
   disconnected) and `E` a metric space, `LocallyConstant X E` is dense in `C(X, E)`: a continuous
   function is uniformly continuous, hence constant on the pieces of a clopen partition. `ℤ_[p]` is
   profinite by `PadicInt.compactSpace` and `IsUltrametricDist → TotallySeparatedSpace`.
3. **Clopen decompositions.** For a finite clopen partition `X = ⊔ Xₐ`, restriction is an isometry
   `C(X, E) ≃ₗᵢ (a → C(Xₐ, E))` with the max norm. For `X = ℤ_p` and the partition into the discs
   `a + pʰℤ_p`, `a ∈ ZMod (p ^ h)`, this is the *disc decomposition*, and each disc is identified
   with `ℤ_p` by `w ↦ a + pʰ w`, with `a` the natural representative in `[0, pʰ)`.
4. Translation `f ↦ f (· + a)`, dilation `f ↦ f (p ·)`, and multiplication by a continuous scalar
   function are bounded operators of norm at most `1`; restriction to `ℤ_p^×` and extension by zero
   from `ℤ_p^×` are norm-decreasing.

### 3.2 Mahler's theorem and the Mahler coefficients

1. Record Mathlib's theorem in the vocabulary of Layer 2: the Mahler basis
   `PadicInt.mahler n = (x ↦ (x choose n))` is an orthonormal basis of `C(ℤ_[p], E)` in the sense of
   §2.2 (with coefficients acting through `ℤ_[p]`), the coefficients are the iterated forward
   differences `aₙ(f) = Δ^n f (0)`, and `mahlerEquiv E : C(ℤ_[p], E) ≃ₗᵢ[ℤ_[p]] C₀(ℕ, E)`. In
   particular `C(ℤ_[p], K)` is orthonormalisable for every complete nonarchimedean field `K ⊇ ℚ_p`.
2. **Mahler coefficients of monomials.** `aₘ (x ↦ x ^ k) = m! · S(k, m)` with `S` the Stirling
   numbers of the second kind: finitely supported, integral, and given by Newton's forward-difference
   formula `x ^ k = ∑_m (x choose m) · Δ^m (n ↦ n ^ k) (0)` on `ℕ`, hence on `ℤ_p` by density.
   Deduce the Mahler coefficients of a polynomial function, and that polynomial functions are the
   finitely supported Mahler expansions with coefficients in the image of the monomials.
3. **Translates and products.** `aₙ (f (· + a)) = ∑_{k ≥ n} (a choose (k − n)) aₖ(f)` (Vandermonde),
   `aₙ (x ↦ (1 + t) ^ x) = tⁿ` for a topologically nilpotent `t` (the Mahler expansion of a
   continuous character, §4.6), and the product formula for the Mahler coefficients of `f · g`
   over a ring.
4. **The Mahler basis on the discs.** Composing Mahler's theorem with the disc decomposition
   §3.1.3, the functions `1_{a + pʰℤ_p}(x) · ((x − a)/pʰ choose n)` for `a ∈ ZMod (p ^ h)`, `n ∈ ℕ`
   form an orthonormal basis of `C(ℤ_[p], E)`, giving `C(ℤ_[p], E) ≃ₗᵢ C₀(ZMod (p ^ h) × ℕ, E)`;
   restricted to the units, the discs with `p ∤ a` give an orthonormal basis of `C(ℤ_[p]ˣ, E)`.
   ⚠ This is a *Mahler* disc model; it is not the Taylor disc model of §4.3, and the two are
   related by Amice's theorem.

### 3.3 The van der Put basis

1. For `i ∈ ℕ` let `ℓ(i)` be the number of `p`-adic digits of `i` (`ℓ(0) = 0`, and `pˡ⁻¹ ≤ i < pˡ`
   for `ℓ(i) = ℓ ≥ 1`), and `eᵢ := 1_{i + p^{ℓ(i)} ℤ_p}`, the characteristic function of the ball
   of radius `p^{−ℓ(i)}` about `i`. Prove that `(eᵢ)` is an orthonormal basis of `C(ℤ_[p], E)`
   (Colmez, Proposition 1.3.2 and Définition 1.3.3, the "base d'ondelettes"; van der Put), with
   coefficients `b₀(f) = f 0` and `bᵢ(f) = f i − f i₋` for `i ≥ 1`, where `i₋` is `i` with its
   leading digit removed.
2. The locally constant functions are exactly the finitely supported van der Put expansions, and
   the functions constant on the cosets of `pʰℤ_p` are the span of `eᵢ` for `i < pʰ`; this is
   the second proof of §3.1.2 for `ℤ_p`.
3. Relate the two bases: the change of basis between the Mahler and van der Put bases is
   triangular with integral entries, and the Mahler coefficients of `1_{a + pʰℤ_p}` are computed
   by `1_{a + pʰℤ_p} (x) = p^{−h} ∑_{ζ^{pʰ} = 1} ζ^{x − a}` over a field containing the `pʰ`-th roots
   of unity (Colmez §1.3.2).

### 3.4 Measures and the Amice transform of a measure

`R` is a complete ultrametric normed `ℤ_[p]`-algebra with `‖1‖ = 1`, and `D(ℤ_[p], R)` is Mathlib's
`AbstractMeasure ℤ_[p] R R`, the continuous `R`-linear functionals on `C(ℤ_[p], R)`, with the operator
norm. ⚠ The statements below are about *bounded* functionals: continuity implies boundedness when
`R` is Tate (§1.1.2), and also when `R` is the unit ball of a Banach–Tate ring whose norm takes
values in `‖ϖ‖ ^ ℤ` — `ℤ_p`, `𝒪_K`, `Λ^{>1/p}` — because then `‖f‖ ≤ ‖ϖ‖ ^ k` means `f = ϖ ^ k g` with
`‖g‖ ≤ 1`; prove both, and state the norm formulas for bounded functionals.

1. **The Mahler dual.** `μ ↦ (μ (mahler n))_n` is an isometric isomorphism of `D(ℤ_[p], R)` onto
   `ℓ^∞(ℕ, R)` (§2.5 along `mahlerEquiv`), so a measure is a bounded sequence and
   `‖μ‖ = sup ‖μ (mahler n)‖`.
2. **The Amice transform.** Define `amiceTransform μ := ∑ₙ μ (mahler n) • Tⁿ ∈ R⟦T⟧`, a power
   series with bounded coefficients, and prove it is injective and `R`-linear, that
   `amiceTransform (dirac a) = ∑ (a choose n) Tⁿ = (1 + T) ^ a`, and that for a topologically
   nilpotent `t` the integral of the character `x ↦ (1 + t) ^ x` against `μ` is the value
   `∑ μ (mahler n) tⁿ` of the transform at `t` (Colmez, Lemme II.2.1 in the measure case).
3. **Convolution.** Define the convolution `μ * ν` as the pushforward of `prodMk μ ν` along
   addition `ℤ_[p] × ℤ_[p] → ℤ_[p]`, prove it makes `D(ℤ_[p], R)` a commutative Banach `R`-algebra with
   unit `dirac 0` and `‖μ * ν‖ ≤ ‖μ‖ ‖ν‖`, and that the Amice transform is a ring homomorphism into
   `R⟦T⟧` (Vandermonde again: the Mahler coefficients of `(x, y) ↦ ((x + y) choose n)`).
4. **The integral case.** For `R = ℤ_[p]` the Amice transform is an isomorphism of rings
   `D(ℤ_[p], ℤ_[p]) ≅ ℤ_[p]⟦T⟧` (every bounded sequence of `ℤ_p`-valued coefficients occurs). This
   is the measure-theoretic face of the Iwasawa algebra of `ℤ_p`; §5.3 identifies it with the
   completed group algebra along `dirac a ↦ [a]` and `T ↦ [1] − 1`. For `R = K` a field, the image
   is the bounded power series `𝒪_K⟦T⟧ ⊗ K`.
5. Pushforward along the multiplication maps and along `x ↦ x + a`, `x ↦ p x`, restriction to
   `ℤ_p^×`, and the action of `ℤ_p^×` on `D(ℤ_[p], R)` by `(a · μ)(f) = μ (f (a ·))`; the effect of
   each on the Amice transform (`(1 + T) ^ a` times, the substitution `T ↦ (1 + T) ^ p − 1`, and the
   projector `1_{ℤ_p^×}`).

### Examples

The Mahler coefficients of `1`, `x`, `x²` and `x ↦ (1 + p) ^ x`, of the
locally constant function `1_{pℤ_p}` over `ℚ_p(ζ_p)`, and of `x ↦ x ^ p − x` (finitely supported,
of sup norm `p⁻¹`); the van der Put coefficients of `x ↦ x` (`bᵢ = p^{ℓ(i) − 1}` for `i ≥ 1`) and of
`1_{1 + pℤ_p}`; the Amice transform of `dirac 1` and of the Haar-type functional
`f ↦ ∑_{a < pʰ} f a`, with its convolution square.

### Dependencies

Layers 0 and 2; Mathlib's Mahler basis and `AbstractMeasure`.

---

## Layer 4: analytic and locally analytic functions on `ℤ_p`

`E` is as in Layer 3; `K` is a complete nonarchimedean nontrivially normed field with
`[NormedAlgebra ℚ_[p] K]`, so `‖p‖ = p⁻¹`; and `A` is a nonarchimedean Banach `ℚ_p`-algebra
(`[NormedCommRing A] [NormedAlgebra ℚ_[p] A] [IsUltrametricDist A] [CompleteSpace A]`).

### 4.1 Restricted power series as functions

`R` is a nonarchimedean Banach ring with `‖1‖ = 1`.

1. **The Tate algebra is the model space.** The series restricted at radius `1`
   (`PowerSeries.IsRestricted 1`), which the adic-spaces roadmap makes into the ring `R⟨X⟩`, form a
   Banach `R`-module for the Gauss norm at radius `1`, and the coefficient map is an isometry
   `R⟨X⟩ ≃ₗᵢ[R] C₀(ℕ, R)`: the monomials `Xⁿ` are an orthonormal basis. Nothing about the ring
   structure is proved here; the adic-spaces roadmap owns it.
2. For a radius `c > 0`, the series restricted at `c` form a Banach `R`-module for the Gauss norm
   at `c`, isometric to `C₀(ℕ, R)` when `c = ‖u‖` for a multiplicative unit `u` (by `X ↦ u X`), and
   in general a potentially orthonormalisable module when `R` is Tate.
3. **Evaluation.** For `f` restricted at `c` and `x` in a Banach `R`-algebra with `‖x‖ ≤ c`, the
   series `∑ (coeff n f) xⁿ` converges, `‖f x‖ ≤ gaussNorm c f`, and evaluation at `x` is a
   continuous ring homomorphism; evaluation at the points of `R⁰` gives a bounded `R`-linear map
   `R⟨X⟩ → C(R⁰, R)` of norm `1`.
4. **Substitution.** For `g` restricted at radius `1` with `coeff 0 g = 0` and `gaussNorm 1 g ≤ 1`,
   the formal composite `f ∘ g` of `f ∈ R⟨X⟩` is restricted at radius `1`, has Gauss norm at most
   that of `f`, and evaluates to the composite of the evaluations. In general, `f ∘ g` is
   restricted at radius `1` whenever `f` is restricted at some radius `c ≥ gaussNorm 1 g`, with
   `gaussNorm 1 (f ∘ g) ≤ gaussNorm c f`. This is the tool that transports
   analyticity along the analytic bijections `w ↦ a + pʰ w` and `z ↦ log(1 + p ʰ z)/pʰ` of the
   later sections.
5. **The identity theorem.** For `K` a complete nonarchimedean nontrivially normed field, a series
   `f ∈ K⟨X⟩` vanishing on an infinite subset of the closed unit disc of `K` is zero. This is
   Strassmann's theorem, obtained from the Newton-polygons roadmap's Weierstrass preparation (§3.1):
   `f = P · u` with `P` a polynomial and `u` a unit of `K⟨X⟩`, so the zeros of `f` in the closed disc
   are the roots of `P`. In particular a series vanishing on `ℤ_p ⊆ K` is zero.
6. **The identity theorem for module-valued series.** If `E` admits a family of bounded
   `ℤ_[p]`-linear maps `λⱼ : E → Kⱼ` to complete nonarchimedean fields that is jointly injective,
   then a series in `C₀(ℕ, E)` vanishing on `ℤ_p` (as an `E`-valued function) is zero. The
   hypothesis holds for every field, every potentially orthonormalisable Banach space over a field
   (coordinate functionals), and every ring of coefficient streams such as `Λ^{>1/p}` (coefficient
   maps). ⚠ It cannot be dropped: over `E = 𝔽_p` with the trivial norm, `Xᵖ − X` vanishes on `ℤ_p`
   (convention 9).

### 4.2 Analytic functions on a disc

1. A function `f : ℤ_p → E` is *analytic on the disc `a + pʰℤ_p`* if there is `c ∈ C₀(ℕ, E)` with
   `f (a + pʰ w) = ∑ cₖ • wᵏ` for all `w ∈ ℤ_p`. Prove that this is independent of the centre: if
   `a' ∈ a + pʰℤ_p` then `f` is analytic on the disc about `a'` with coefficients given by the
   re-expansion `w ↦ w + (a' − a)/pʰ` (a substitution as in §4.1.4 with `ℤ_p`-integral
   coefficients), and the sup norm of the coefficients is the same (Colmez, Proposition 1.4.3).
2. Analytic functions on a disc are continuous, closed under sums, products (when `E` is a ring),
   `ℤ_p`-scalars, and composition with analytic bijections of the disc; polynomial functions and
   restrictions of series in `K⟨X⟩` are analytic on every disc.
3. The coefficients of a function analytic on a disc are unique under the hypothesis of §4.1.6;
   the function `x ↦ (x ^ p − x) mod p` shows they are not unique in general.

### 4.3 Locally analytic functions of level `h`

1. Define the disc model `LocallyAnalytic h E := C₀(ZMod (p ^ h) × ℕ, E)` (convention 9), with the
   evaluation `eval h : LocallyAnalytic h E →L[ℤ_[p]] C(ℤ_[p], E)` sending the coefficient family
   `(cₐ,ₖ)` to the function equal to `∑ₖ cₐ,ₖ • wᵏ` at `a + pʰ w`; prove `‖eval h c‖ ≤ ‖c‖` and
   that the image is exactly the functions analytic on every disc `a + pʰℤ_p`. Under the hypothesis
   of §4.1.6, `eval h` is injective, so `LocallyAnalytic h E` *is* the space of level-`h` locally
   analytic functions with the norm `‖f‖_h = max_a sup_k ‖cₐ,ₖ(f)‖`; state every later result for
   the disc model, and its function form under that hypothesis.
2. **The inclusions.** `LocallyAnalytic h E → LocallyAnalytic (h + 1) E`, re-expanding the series on
   `a + pʰℤ_p` on each of its `p` sub-discs `a + pʰ b + pʰ⁺¹ ℤ_p`, is injective, of norm at most `1`,
   compatible with evaluation, and in the disc models its matrix is the binomial re-centring: with
   `w = b + p w'` on the sub-disc `a + pʰ b + pʰ⁺¹ ℤ_p` (`0 ≤ b < p`), the coefficient `j` there is
   `∑_{k ≥ j} (k choose j) · b^{k − j} · p^{j} · cₐ,ₖ`, so the entry from `(a, k)` to `(a + pʰ b, j)` is
   `(k choose j) b^{k − j} p^{j}`, every column is finitely supported, and the entries with `j`
   fixed are bounded by `p^{−j}` in norm.
3. **The locally analytic functions.** `LA(ℤ_p, E) := ⋃_h eval h (LocallyAnalytic h E)` as a
   submodule of `C(ℤ_[p], E)`; no topology is put on the union. Prove that a function is locally
   analytic if and only if it is analytic on a neighbourhood of every point, and that `LA` is a
   subring when `E` is a ring, stable under composition with locally analytic maps `ℤ_p → ℤ_p`.
4. **Locally polynomial functions.** For `k ∈ ℕ`, define `LP_{h, ≤ k}(ℤ_p, E)` as the coefficient
   families supported on `{(a, j) | j ≤ k}`: the functions that are polynomial of degree at most
   `k` on each disc `a + pʰℤ_p`. It is a free module of rank `pʰ (k + 1)`, closed in
   `LocallyAnalytic h E`, with the basis `1_{a + pʰℤ_p} · (x − a)ʲ`; the inclusion
   `LP_{h, ≤ k} → LP_{h + 1, ≤ k}` is the block-diagonal map of clause 2 restricted to degrees
   `≤ k`. These are the spaces `Ind^{alg}` of Liu–Wan–Xiao (2.3), and the classicality statements
   of the spectral-halo roadmap are about them.

### 4.4 Amice's theorem

1. **The Amice basis.** `PadicInt.amice h n := (⌊n / pʰ⌋)! • mahler n`, the function
   `x ↦ ⌊n/pʰ⌋! · (x choose n)` (Colmez's `gₙ`). Prove the integrality and reduction lemma
   (Colmez, Lemme 1.4.9): for a residue `a` and the polynomial `gₙ,ₐ(w) := gₙ(a + pʰ w)`, the
   coefficients of `gₙ,ₐ` lie in `ℤ_p`; and writing `n = (m(n) + 1) pʰ − i(n)` with `1 ≤ i(n) ≤ pʰ`,
   the reduction of `gₙ,ₐ` modulo `p` vanishes when `a` lies beyond the disc index `i(n)`, has degree
   `m(n)` on the disc `i(n)`, and degree less than `m(n)` on the earlier discs, in Colmez's ordering
   of the discs by the centres `−j`. State the same with the natural representatives
   `a ∈ [0, pʰ)` and the reversal of each block of `pʰ` consecutive indices, which is the ordering
   in which the matrix below is unitriangular.
2. **Amice's theorem.** The map `C₀(ℕ, E) → LocallyAnalytic h E` sending `(bₙ)` to the disc
   coefficients of `∑ bₙ • amice h n` is an isometric isomorphism of Banach `ℤ_[p]`-modules
   (`K`-linear when `E` is a `K`-Banach space): the Amice basis is an orthonormal basis of
   `LA_h(ℤ_p, E)` (Amice; Colmez, Théorème 1.4.7; Liu–Wan–Xiao §2.16). The proof is §2.7 applied
   to the matrix of clause 1 in the disc model, reindexed by the block reversal; nothing beyond the
   unitriangular-perturbation criterion and Lemme 1.4.9 is needed, and no residue field.
3. **Mahler coefficients of locally analytic functions.** The Amice coordinate `bₙ` and the Mahler
   coefficient `aₙ` of `f ∈ LA_h` are related by `aₙ(f) = ⌊n/pʰ⌋! • bₙ(f)`. Hence, for `E` a
   `K`-Banach space: `f ∈ C(ℤ_[p], E)` is analytic of level `h` if and only if
   `aₙ(f) / ⌊n/pʰ⌋! → 0`, and then `‖f‖_h = sup ‖aₙ(f) / ⌊n/pʰ⌋!‖`; and `f` is locally analytic if and
   only if `liminf v_p(aₙ(f)) / n > 0` (Colmez, Corollaire 1.4.8), where by Legendre's formula
   `v_p(⌊n/pʰ⌋!) = (⌊n/pʰ⌋ − s_p(⌊n/pʰ⌋)) / (p − 1)`.
4. **The inclusions in the Amice bases.** In the Amice bases of levels `h` and `h + 1`, the
   inclusion §4.3.2 is the diagonal operator with entries `⌊n/pʰ⌋! / ⌊n/pʰ⁺¹⌋! ∈ ℤ_p`, whose norms
   tend to `0` (their valuations grow like `n / pʰ⁺¹`); and in the Amice basis of level `h` and the
   Mahler basis, `eval h` is the diagonal operator `diag(⌊n/pʰ⌋!)`. Both are statements about
   diagonal operators (§2.6.2); the compact-operators roadmap reads the first as complete
   continuity of the inclusion.
5. The level-`0` case: `amice 0 n = n! • mahler n = x (x − 1) ⋯ (x − n + 1)`, the Colmez basis of
   the Tate algebra, and Amice's theorem at level `0` says the monomial and Colmez coordinates of
   `K⟨X⟩` differ by the unitriangular matrix of Stirling numbers, so `diag(n!)` conjugates the
   Colmez basis into the Mahler basis.

### 4.5 The exponential, logarithm and binomial series

Over a nonarchimedean Banach `ℚ_p`-algebra `A`, so `‖p‖ = p⁻¹`; the radius `r_p := p^{−1/(p − 1)}`.

1. **Convergence discs.** `padicExp x := ∑ xⁿ / n!` converges for `‖x‖ < r_p` and diverges at
   every `x` of a field with `‖x‖ ≥ r_p`; `padicLog (1 + x) := ∑ (−1)ⁿ⁺¹ xⁿ / n` converges for
   `‖x‖ < 1`. Both are restricted power series on every closed sub-disc of their discs. The input is
   Legendre's formula in the form `v_p(n!) ≤ (n − 1)/(p − 1)` with equality only at powers of `p`.
2. **Norms.** `‖padicExp x − 1‖ = ‖x‖` for `‖x‖ < r_p`; for `‖x‖ < 1`,
   `‖padicLog (1 + x)‖ ≤ max_n ‖xⁿ / n‖` (a maximum, the terms tending to `0`), and
   `‖padicLog (1 + x)‖ = ‖x‖` on the disc `‖x‖ < r_p`.
3. **Functional equations.** `padicExp (x + y) = padicExp x * padicExp y` on the disc,
   `padicLog ((1 + x) (1 + y)) = padicLog (1 + x) + padicLog (1 + y)` for `‖x‖, ‖y‖ < 1`,
   `padicLog (padicExp x) = x` for `‖x‖ < r_p`, and `padicExp (padicLog u) = u` for `‖u − 1‖ < r_p`.
   Hence `padicExp` is an isomorphism of topological groups from the additive disc `‖x‖ < r_p` onto
   the multiplicative disc `‖u − 1‖ < r_p`, with inverse `padicLog`; in particular, whenever
   `‖p ^ h‖ < r_p` — that is, `h ≥ 1` for odd `p` and `h ≥ 2` for `p = 2`, so that `p ^ h ∈ qℤ_p` —
   `z ↦ padicExp (p ^ h z)` is a bijection of `ℤ_p` onto `1 + p ^ h ℤ_p` given by a restricted series
   with `ℤ_p`-integral coefficients, and so is its inverse `u ↦ padicLog u / p ^ h`.
4. ⚠ **The logarithm is not injective on the open unit disc.** Over a field, its kernel on
   `‖u − 1‖ < 1` is the group of `p`-power roots of unity; record `padicLog ζ_p = 0`. The
   injectivity statement is on the disc `‖u − 1‖ < r_p` only.
5. **The binomial series.** For `s ∈ A` and `x` with `‖x‖ < 1`, `binomialSeries s x := ∑ (s choose n) xⁿ`
   with `(s choose n) = s (s − 1) ⋯ (s − n + 1) / n!`. Prove: for `s` in the image of `ℤ_p` the
   coefficients are integral and the series converges for all `‖x‖ < 1` (⚠ not for every `‖s‖ ≤ 1`:
   over `ℚ_p(√p)` the coefficient `(√p choose p)` has norm `√p`); for arbitrary `s` it
   converges when `‖x‖ < r_p` and `‖s‖ ‖x‖ < r_p`, and on that disc
   `binomialSeries s x = padicExp (s * padicLog (1 + x))`; `(1 + x) ^ (s + t) = (1 + x) ^ s (1 + x) ^ t`
   and `((1 + x) ^ s) ^ t = (1 + x) ^ (s t)` on the joint disc; and for `s = n ∈ ℕ` it is
   `(1 + x) ^ n`. The identity with the exponential is proved by the identity theorem in the
   exponent (§4.1.5): both sides are, for fixed `x`, restricted series in `s` agreeing at every
   natural number.
6. **Powers of one-units and the `p`-th-power contraction.** For `‖x‖ < 1` and `s ∈ ℤ_p`,
   `(1 + x) ^ s` is the limit of `(1 + x) ^ sₙ` along natural numbers `sₙ → s`; and
   `‖(1 + x) ^ p − 1‖ ≤ max (‖p‖ ‖x‖, ‖x‖ ^ p)`, so `(1 + x) ^ (p ^ h) − 1 → 0` as `h → ∞` and for
   every `‖x‖ < 1` there is `h` with `‖(1 + x) ^ (p ^ h) − 1‖ < r_p`. The binomial power identity
   `(1 + x) ^ (p ^ h u) = ((1 + x) ^ (p ^ h)) ^ u` for `u ∈ ℤ_p` holds by continuity and density.
7. **The local-field seam.** For `A = K` a local field, `padicLog` on `1 + 𝔪_K` and `padicExp` on
   the deep units are the maps of the local-fields-and-ramification roadmap (Layer 1), and the
   group isomorphism `U(K, i) ≃ 𝔪_K^i` there is clause 3 at `‖p‖^{i/e} < r_p`; the Teichmüller
   section and the decomposition `𝒪_K^× ≃ μ_{q − 1} × U(K, 1)` are cited from there, not re-proved.

### 4.6 Characters of `ℤ_p` and their analyticity

1. For a topologically nilpotent `r` in a complete ultrametric normed `ℤ_[p]`-algebra `R`,
   Mathlib's continuous additive character `addChar_of_value_at_one r`, `x ↦ (1 + r) ^ x`, is the
   Mahler series with coefficients `rⁿ` (§3.2.3); when `R` is a `ℚ_p`-algebra and `‖r‖ < 1` it is the
   binomial series, `(1 + r) ^ x = binomialSeries (x : R) r` for `x ∈ ℤ_p`, and
   `(1 + r) ^ x = padicExp (x * padicLog (1 + r))` when `‖r‖ < r_p`.
2. **The analyticity level of a character.** For `K` a field and `‖r‖ < 1`, the character
   `x ↦ (1 + r) ^ x` is analytic of level `h` if and only if `‖(1 + r) ^ (p ^ h) − 1‖ < r_p`, if and
   only if `‖r‖ < p^{−1/(pʰ (p − 1))}`; the first form is the disc formula
   `(1 + r) ^ (a + pʰ w) = (1 + r) ^ a · padicExp (w · padicLog ((1 + r) ^ (pʰ)))`, and the second is
   Amice's criterion §4.4.3 applied to the Mahler coefficients `rⁿ`. Every continuous character of
   `ℤ_p` is locally analytic, of level `h` for every `h` beyond a threshold.
3. For a Banach `ℚ_p`-algebra `A` and `‖r‖ < r_p` in `A`, the character `x ↦ (1 + r) ^ x` extends to
   the analytic function `z ↦ padicExp (z * padicLog (1 + r))` on the closed unit disc of any
   Banach `A`-algebra, with values in the unit ball; this is the extension formula of §5.4.

### 4.7 Locally analytic distributions and the Amice transform

`K` is a field, `E = K`.

1. Define `D(ℤ_p, K)` as the linear functionals on `LA(ℤ_p, K)` that are bounded on every
   `LA_h(ℤ_p, K)` — equivalently the inverse limit of the duals `LA_h(ℤ_p, K)'`, each of which is
   `ℓ^∞(ℕ, K)` in the Amice coordinates by §2.5 — and the Amice transform
   `amiceTransform μ := ∑ μ (mahler n) Tⁿ ∈ K⟦T⟧`.
2. **Amice's theorem for distributions.** The Amice transform is a bijection from `D(ℤ_p, K)` onto
   the power series converging on the open unit disc, `{∑ bₙ Tⁿ | ∀ ρ < 1, ‖bₙ‖ ρⁿ → 0}`, i.e.
   the series restricted at every radius `ρ < 1` (Amice; Colmez, Théorème II.2.2; Schneider–Teitelbaum
   §2); measures (§3.4) are the distributions bounded on `C(ℤ_p, K)`, and correspond to the bounded
   series. The proof is §4.4.3: `μ` is bounded on `LA_h` if and only if the sequence
   `‖μ (mahler n)‖ · ‖⌊n/pʰ⌋!‖⁻¹` is bounded, and Legendre's formula turns the union over `h` into
   convergence on every disc of radius `ρ < 1`.
3. Convolution of distributions and the ring isomorphism with the algebra of series on the open
   disc; the Dirac distribution, the action of `ℤ_p^×`, and the integral of a locally analytic
   character `x ↦ (1 + z) ^ x` (`‖z‖ < 1`) against a distribution as the value of the transform at
   `z` (Colmez, Lemme II.2.1).

### Examples

Over `ℚ_p`: the Mahler and Amice coordinates of `x ↦ xᵏ`, of `1_{a + pℤ_p}`, of `x ↦ (1 + p) ^ x`
(level `0` for `p` odd, level `1` for `p = 2`), of `x ↦ ζ_p ^ x` (locally constant, level `1`, not
level `0`), and of `x ↦ (1 + p^{1/2}) ^ x` over `ℚ_p(√p)` (level `1`, by both criteria of §4.6.2);
`padicExp p`, `padicLog (1 + p)`, `padicLog ζ_p = 0`; `(1 + p) ^ (1/2)` as a binomial series;
the Amice transform of `dirac a` and of the derivative functional `f ↦ (d/dx) f (0)` on locally
analytic functions, which is `∑ (−1)ⁿ⁺¹ Tⁿ / n = log (1 + T)`, converging on the open disc but not
bounded.

### Dependencies

Layers 0–3; the adic-spaces roadmap for the ring `R⟨X⟩` (§4.1.1); the Newton-polygons roadmap for
Weierstrass preparation (§4.1.5); the local-fields-and-ramification roadmap for §4.5.7.

---

## Layer 5: characters of `ℤ_p^×`, the Iwasawa algebra, weight space and the halo

`q := p` for odd `p` and `q := 4` for `p = 2`; `Δ := (ZMod q)ˣ`. `R` is a complete ultrametric
normed `ℤ_[p]`-algebra with `‖1‖ = 1`; `K` and `A` are as in Layer 4; `r_p = p^{−1/(p − 1)}`.

### 5.1 The structure of `ℤ_p^×`

1. The reduction `ℤ_[p]ˣ → Δ` is split by the Teichmüller section `ω : Δ → ℤ_[p]ˣ`, `ω(δ) = lim δ̃^{pⁿ}`
   for any lift `δ̃`, a multiplicative map with `ω(δ) ≡ δ mod q`; hence `ℤ_[p]ˣ ≅ Δ × (1 + qℤ_p)`
   as topological groups, `x = ω(x̄) · ⟨x⟩`, with `⟨x⟩ ∈ 1 + qℤ_p`. For odd `p` this is the
   local-fields-and-ramification roadmap's `𝒪_K^× ≃ μ_{q − 1} × U(K, 1)` at `K = ℚ_p`, cited; the
   case `p = 2`, where `Δ = {±1}` and `1 + 4ℤ_2` is the torsion-free part, is proved here.
2. **The generator.** `γ := padicExp q ∈ 1 + qℤ_p`, the element with `padicLog γ = q`; the map
   `ℤ_p → 1 + qℤ_p`, `z ↦ γ ^ z = padicExp (q z)`, is an isomorphism of topological groups with
   inverse `u ↦ padicLog u / q` (§4.5.3 at `‖q‖ < r_p`). Every element of `1 + p ^ h ℤ_p` with
   `‖p ^ h‖ < r_p` is `padicExp (p ^ h z)` for a unique `z ∈ ℤ_p`.
3. Define `ℓ⟨x⟩ := padicLog ⟨x⟩ / q ∈ ℤ_p` for `x ∈ ℤ_[p]ˣ`; it is a continuous homomorphism
   `ℤ_[p]ˣ → ℤ_p` with kernel `ω(Δ)`, and `⟨x⟩ = γ ^ ℓ⟨x⟩`.

### 5.2 Continuous characters and the `T`-coordinate

1. Define `PadicInt.WeightSpace R := (ℤ_[p]ˣ →ₜ* Rˣ)`, the continuous characters (convention 10),
   and for `κ` in it the `T`-coordinate `T_κ := κ γ − 1 ∈ R`. Prove `T_κ` is topologically
   nilpotent (`(κ γ) ^ (p ^ n) = κ (γ ^ (p ^ n)) → κ 1 = 1`, and `u ^ (pⁿ) → 1` forces `u − 1`
   topologically nilpotent in an ultrametric `ℤ_p`-algebra), so `‖T_κ‖ < 1` when the norm is
   multiplicative.
2. **The parametrisation.** `κ ↦ (κ ∘ ω, T_κ)` is a bijection
   `WeightSpace R ≃ (Δ →* Rˣ) × {r : R // IsTopologicallyNilpotent r}`, with inverse
   `(η, r) ↦ (x ↦ η(x̄) · (1 + r) ^ ℓ⟨x⟩)`; this is Mathlib's `continuousAddCharEquiv` transported
   along `z ↦ γ ^ z` on the `1 + qℤ_p` factor, and the finite-group part on `Δ`. For a field `K`,
   `WeightSpace K ≅ (Δ →* Kˣ) × {T : ‖T‖ < 1}`: the weight space over `K` is `|Δ|` copies of the
   open unit disc, `p − 1` copies for odd `p` and `2` for `p = 2`.
3. **Classical characters.** For `k ∈ ℕ` and a character `ψ` of finite order of `ℤ_[p]ˣ`, define
   the classical character `(k, ψ) : x ↦ x ^ k ψ(x)`; `ψ` has *conductor* `p ^ m` when it factors
   through `(ZMod (p ^ m))ˣ` and not through `(ZMod (p ^ (m − 1)))ˣ`. Compute the coordinate: for
   odd `p`, `v_p (T_{(k,ψ)}) ≥ 1` when `m ≤ 1` and `v_p (T_{(k,ψ)}) = 1 / (p ^ (m − 2) (p − 1))` when
   `m ≥ 2`; for `p = 2`, `v_2 ≥ 1` when `m ≤ 3` and `= 1 / 2 ^ (m − 3)` when `m ≥ 4` (Liu–Wan–Xiao,
   §2.1). Since `1 / (p ^ (m − 2)(p − 1)) < 1` exactly when `m ≥ 3`, or `m = 2` and `p ≥ 3`, the
   classical characters with `‖T‖ > p⁻¹` are those of conductor at least `p ^ 2` for odd `p` and at
   least `2 ^ 4` for `p = 2`.
4. **Characters of the units of a bigger ring.** For a complete ultrametric normed `ℤ_p`-algebra
   `R`, `𝒪_K`-valued characters, and the identification `(ℤ_[p]ˣ →ₜ* 𝒪_Kˣ) = (ℤ_[p]ˣ →ₜ* Kˣ)` (a
   continuous character has compact image, hence lands in the units of the unit ball).
5. **Change of generator.** For any topological generator `γ'` of `1 + qℤ_p`, the coordinate
   `T'_κ := κ γ' − 1` satisfies `1 + T'_κ = (1 + T_κ) ^ ℓ⟨γ'⟩` with `ℓ⟨γ'⟩ ∈ ℤ_p^×`, so the two
   coordinates are related by the binomial series and each is a function of the other; the case
   `γ' = 1 + q` is Washington's coordinate.

### 5.3 The Iwasawa algebra

1. Define `IwasawaAlgebra p := completedGroupAlgebra p ℤ_[p]ˣ` in the sense of the
   profinite-and-pro-`p`-groups roadmap (Layer 9) — the limit of `ℤ_p[ℤ_p^× / (1 + pⁿℤ_p)]` —
   with its compact topology, and the *universal character* `[·] : ℤ_[p]ˣ →ₜ* Λˣ`, `a ↦ [a]`, the
   image of the group element (Liu–Wan–Xiao, Notation 2.1).
2. **The structure theorem.** `Λ ≅ MonoidAlgebra ℤ_[p] Δ ⊗ ℤ_[p]⟦T⟧ ≅ (MonoidAlgebra ℤ_[p] Δ)⟦T⟧`,
   topologically, with `[ω(δ)] ↦ δ` and `[γ] ↦ 1 + T`: the completed group algebra of a product
   `Δ × Γ'` with `Δ` finite is `ℤ_p[Δ] ⊗ ℤ_p⟦Γ'⟧`, and `ℤ_p⟦Γ'⟧ ≅ ℤ_p⟦T⟧` for the procyclic
   `Γ' = 1 + qℤ_p` is the profinite-and-pro-`p`-groups roadmap's identification (Iwasawa; Serre;
   Washington, Theorem 7.1). Under it, `[a] = ω(ā) · (1 + T) ^ ℓ⟨a⟩` with
   `(1 + T) ^ s = ∑ (s choose n) Tⁿ ∈ ℤ_p⟦T⟧` for `s ∈ ℤ_p`, and the maximal ideals of `Λ` are the
   ideals `𝔪_Λ = (p, T)` of the components: for odd `p`, `ℤ_p[Δ] ≅ ∏_{η : Δ → μ_{p−1}} ℤ_p` and
   `Λ ≅ ∏_η ℤ_p⟦T⟧` is a product of `p − 1` local rings, while for `p = 2` the ring `ℤ_2[C₂]⟦T⟧` is
   local.
3. **The universal property.** For a complete ultrametric normed `ℤ_[p]`-algebra `R`, composition
   with `[·]` is a bijection from continuous `ℤ_[p]`-algebra homomorphisms `Λ → R` onto
   `WeightSpace R`; the inverse sends `κ` to the *specialisation* `ψ_κ`, given on `ℤ_p[Δ]⟦T⟧` by
   `δ ↦ κ(ω δ)` and `∑ cₙ Tⁿ ↦ ∑ cₙ T_κⁿ` (convergent since `T_κ` is topologically nilpotent). This
   is the second sentence of Liu–Wan–Xiao's Notation 2.1, and with §5.2.2 it says that the points of
   `Λ` in `R` are the weights.
4. **Measures.** `Λ ≅ D(ℤ_[p]ˣ, ℤ_[p])` as topological rings, with `[a] ↦ dirac a` and convolution
   as the product: the continuous functionals on `C(ℤ_[p]ˣ, ℤ_[p])` are the compatible families of
   functionals on the finite quotients. On the `1 + qℤ_p` factor this is §3.4.4 pulled back along
   `z ↦ γ ^ z`, and the two identifications of `ℤ_p⟦T⟧` — as `ℤ_p⟦1 + qℤ_p⟧` and as measures on
   `ℤ_p` — agree, both sending `T` to `[γ] − 1 = dirac 1 − dirac 0`.
5. **Integration.** The pairing `Λ × C(ℤ_[p]ˣ, ℤ_p) → ℤ_p`, `⟨λ, f⟩ := λ(f)` through clause 4, with
   `⟨[a], f⟩ = f a`, and its extension `⟨λ, f⟩_R ∈ R` for `f ∈ C(ℤ_[p]ˣ, R)`, continuous in both
   arguments; a weight `κ` integrates to `⟨λ, κ⟩_R = ψ_κ(λ)`, the specialisation of clause 3.

### 5.4 The analyticity level of a character

1. Define `IsAnalyticOfLevel h κ` for `κ : WeightSpace K` (with `h ≥ v_p q`, i.e. `‖p ^ h‖ < r_p`):
   `κ`, as a function on `ℤ_[p]ˣ ⊆ ℤ_[p]`, is analytic on every disc `a + p ^ h ℤ_p` with `p ∤ a`
   (§4.2), equivalently its restriction to each coset `a (1 + p ^ h ℤ_p)` lies in the image of the
   level-`h` disc model.
2. **The criterion.** `κ` is analytic of level `h` if and only if `‖κ (padicExp (p ^ h)) − 1‖ < r_p`,
   if and only if `‖T_κ‖ < p^{−q / (p ^ h (p − 1))}`. The first equivalence is the disc formula
   `κ (a · padicExp (p ^ h z)) = κ a · padicExp (z · padicLog (κ (padicExp (p ^ h))))` for `z ∈ ℤ_p`,
   with `z ↦ padicExp (p ^ h z)` an analytic bijection of `ℤ_p` onto `1 + p ^ h ℤ_p` with
   `ℤ_p`-integral coefficients in both directions (§4.5.3, §4.1.4), together with §4.6.2 at level
   `0`; the second is §4.6.2's criterion for the character `z ↦ (1 + T_κ) ^ z` at level
   `h − v_p q`, since `κ (padicExp (p ^ h)) = (1 + T_κ) ^ (p ^ (h − v_p q))`. Liu–Wan–Xiao's
   "`m`-locally analytic" (§2.1) is level `h = m` in the second form, and the "`v(T) > q/(pᵐ(p−1))`"
   there is the second inequality.
3. **Every character has a level.** For every `κ : WeightSpace K` there is `h` with `κ` analytic
   of level `h` (§4.5.6: `(1 + T_κ) ^ (p ^ n) − 1 → 0`), and then of every higher level; a classical
   character `(k, ψ)` of conductor `p ^ m` is analytic of level `max (m, v_p q)`, by the valuations
   of §5.2.3.
4. **The extension to a rigid neighbourhood.** For `κ` analytic of level `h` with values in a Banach
   `ℚ_p`-algebra `A` (`κ : ℤ_[p]ˣ →ₜ* Aˣ` with `‖κ (padicExp (p ^ h)) − 1‖ < r_p`), and any
   nonarchimedean Banach `A`-algebra `B` with unit ball `B⁰`, define `κ̃` on the group
   `ℤ_p^× · (1 + p ^ h B⁰)` by `κ̃ (a · x) := κ a · padicExp (padicLog x · padicLog (κ (padicExp (p ^ h))) / p ^ h)`
   and prove it is a well-defined multiplicative extension of `κ`, continuous, with values in the
   units of `B⁰` (Liu–Wan–Xiao, §2.1, the display defining `κ`). This is the device by which a
   character of `ℤ_p^×` is evaluated at `cz + d`.

### 5.5 The expansion of `z ↦ κ (cz + d)`

`κ : WeightSpace K` analytic of level `h`, `c ∈ K` with `‖c‖ ≤ ‖p ^ h‖`, and `d ∈ 𝒪_K^×` with
`d ∈ ℤ_p^× · (1 + p ^ h 𝒪_K)`.

1. The function `z ↦ κ̃ (c z + d)` on the closed unit disc of `K` is given by a restricted power
   series `expansion κ c d ∈ K⟨z⟩` with all coefficients of norm at most `1` and constant term
   `κ̃ d`: apply §5.4.4 with `B = K⟨z⟩` to the element `c z + d = d (1 + (c/d) z)`.
2. **Geometric decay.** Let `T'_h := κ (padicExp (p ^ h)) − 1`. For every real `r ≥ 1` with
   `r ‖c‖ < r_p` and `r ‖c‖ ‖T'_h‖ < ‖p ^ h‖ r_p`, the series `expansion κ c d` is restricted at
   radius `r`, so its `m`-th coefficient has norm at most `r^{−m}`. The level-`h` criterion is
   exactly the statement that some `r > 1` works, so the coefficients decay geometrically. The
   proof composes `padicExp (· · padicLog (1 + T'_h))`, convergent on `‖y‖ < r_p / ‖T'_h‖`, with
   `y = padicLog (1 + (c/d) z) / p ^ h`, of norm at most `r ‖c‖ / ‖p ^ h‖` on `‖z‖ ≤ r`.
3. **The cocycle.** For `g, g'` in the monoid of matrices `(a b; c d)` over `ℤ_p` with
   `p ^ h ∣ c`, `d ∈ ℤ_p^×` and nonzero determinant, and the Möbius series `w_g(z) = (az + b)/(cz + d)`,
   the expansions satisfy `expansion (g g') = expansion g · (expansion g' ∘ w_g)` as elements of
   `K⟨z⟩`, by the identity theorem §4.1.5 applied to the pointwise identity
   `κ̃ ((c'' z + d'')) = κ̃ (c z + d) · κ̃ (c' w_g(z) + d')` on `ℤ_p`. This is the automorphy-factor
   cocycle `j(gg', z) = j(g, z) j(g', gz)` combined with multiplicativity of `κ`, and it is the
   statement the overconvergent-forms roadmap needs in order to make the weight-`κ` action of
   Jacobs's Definition 1.27 an action.
4. **Algebraic weights.** For `κ = (x ↦ x ^ k)`, the expansion is the polynomial `(d + c z) ^ k`,
   and the cocycle is the classical one; for `κ = (k, ψ)` the expansion is `ψ(d) · (d + c z) ^ k`
   once `p ^ h` is a multiple of the conductor.

### 5.6 The halo ring `Λ^{>1/p}` and the Banach–Tate ring `Λ^{>1/p}[1/T]`

One component at a time: `T` is the coordinate of `ℤ_p⟦T⟧ ⊆ Λ`, and the `Δ`-factor is restored in
clause 6.

1. **Definition.** `IwasawaAlgebra.Halo p` is the set of functions `d : ℤ → ℤ_[p]` with
   `‖d m‖ ≤ p ^ (min 0 m)`, i.e. `v_p (dₘ) ≥ max (0, −m)`, thought of as `∑_{m ∈ ℤ} dₘ Tᵐ`
   (convention 11). Prove that the convolution `(d * e)ₖ = ∑' i, dᵢ e_{k − i}` converges, that
   `Halo p` is a commutative `ℤ_[p]`-algebra with `1 = δ₀` and `T = δ₁`, that the *gauge norm*
   `‖d‖ := ⨆ m, ‖dₘ‖ · p ^ (−m)` is an ultrametric submultiplicative norm with `‖1‖ = 1` taking
   values in `[0, 1]`, that `Halo p` is complete, that the constants embed isometrically, and that
   `‖T * d‖ = p⁻¹ ‖d‖` on the nose (multiplication by `T` is the coefficient shift).
2. **Divisibility by `T` is a norm bound.** `T ^ k ∣ d ↔ ‖d‖ ≤ p ^ (−k)`; `𝔪_Λ · Halo p = (T)`,
   i.e. `p ∈ T · Halo p` (Liu–Wan–Xiao, Lemma 3.15: `p = pT⁻¹ · T`); and for `a ≥ 0` and `b ∈ ℤ`
   with `a + b ≥ 0`, `𝔪_Λ ^ a · T ^ b · Halo p = T ^ (a + b) · Halo p` inside `Halo p [1/T]`
   (their (3.16.3)).
3. **The universal property.** `Halo p` is the `p`-adic completion of `Λ[pT⁻¹] ⊆ Λ[1/T]`: the
   natural map `ℤ_[p]⟦T, U⟧ / (T U − p) → Halo p`, `U ↦ pT⁻¹`, is an isomorphism, and a
   `ℤ_[p]`-algebra homomorphism out of `Halo p` into a `p`-adically complete algebra is determined
   by the images of `T` and `pT⁻¹`. This is the sense in which `Halo p` is Liu–Wan–Xiao's
   `Λ⟦pT⁻¹⟧`.
4. **Specialisation at a halo point.** For `T₀ ∈ K` with `p⁻¹ < ‖T₀‖ < 1`, the series
   `∑_{m ∈ ℤ} dₘ T₀ᵐ` converges and defines a continuous ring homomorphism
   `specialize T₀ : Halo p → 𝒪_K` with `‖specialize T₀ (T ^ k · d)‖ ≤ ‖T₀‖ ^ k`. ⚠ The annulus is
   open at both ends and the lower bound cannot be relaxed: at `‖T₀‖ = p⁻¹` the terms `dₘ T₀ᵐ` with
   `m → −∞` are bounded by `1` and need not tend to `0`. The specialisations at all `T₀` are
   jointly injective, which is how §4.1.6 applies to `Halo p`-valued series.
5. **The Banach–Tate ring.** `IwasawaAlgebra.HaloTate p := Halo p [1/T]`, realised as the streams
   `d : ℤ → ℤ_[p]` with `‖d m‖ ≤ p ^ (min 0 (m + k))` for some `k`, with the gauge norm extended by
   the same formula. Prove it is complete, that its unit ball is `Halo p`, that `T` is a unit with
   `‖T ^ n * d‖ = p ^ (−n) ‖d‖` for all `n ∈ ℤ`, hence a multiplicative pseudo-uniformiser, so that
   `HaloTate p` is a Banach–Tate ring (§0.4) and every element is `T ^ (−k)` times an element of
   `Halo p`. Its pseudo-uniformiser valuation is `v_T (d) = min_m (m + v_p (dₘ))`, the `T`-adic order
   weighted by the `p`-adic valuations of the coefficients. It is the coefficient ring over which the
   spectral-halo roadmap runs Riesz theory.
6. **The `Δ`-factor and the universal character.** The full halo ring is
   `MonoidAlgebra ℤ_[p] Δ ⊗ Halo p`, a product of copies of `Halo p` for odd `p`; `Λ` maps into it,
   `[a] ↦ ω(ā) · (1 + T) ^ ℓ⟨a⟩` with `(1 + T) ^ s = ∑ (s choose n) Tⁿ` for `s ∈ ℤ_p` (§4.5.5 with
   integral coefficients), and the specialisation at a halo point `T₀` sends `[a]` to the character
   `κ_{T₀} : a ↦ ω(ā) (1 + T₀) ^ ℓ⟨a⟩`, a point of `WeightSpace 𝒪_K` with `T_{κ_{T₀}} = T₀`.
   By §5.4.3 there is a level `h` at which `κ_{T₀}` is analytic; by §5.4.2 the level is
   `h ≥ v_p q` with `‖T₀‖ < p^{−q / (p ^ h (p − 1))}`, and the level-`h` expansion data of §5.5 exist
   at every halo point. Liu–Wan–Xiao's Definition 2.13 chooses such an `h` for the affinoid
   `‖T‖ ≤ r`; here the choice is made point by point and no affinoid is needed.

### Examples

`ℤ_3^× = {±1} × (1 + 3ℤ_3)` with `γ = exp 3`; `ℤ_2^× = {±1} × (1 + 4ℤ_2)` with `γ = exp 4`; the
coordinates `T_{(k, 1)} = γ ^ k − 1` and `T_{(0, ψ)} = ζ_{pᵐ⁻¹} − 1` for `ψ` of conductor `p ^ m`,
`m ≥ 2`; the specialisation of `Λ` at `x ↦ x ^ k`; the element `pT⁻¹` of `Halo p` and its norm `1`;
`‖T‖ = p⁻¹` and `‖p‖ = p⁻¹` in `Halo p`; the specialisation of `∑_{m < 0} p ^ (−m) T ^ m` at a
point with `‖T₀‖ = p^{−1/2}` (a point of the halo) versus its non-convergence at `‖T₀‖ = p⁻¹`; the
level of `κ_{T₀}` for `‖T₀‖ = 3^{−1/2}` at `p = 3`: level `1` requires `‖T₀‖ < 3^{−q/(p(p−1))} = 3^{−1/2}`,
so this `T₀` needs level `2`.

### Dependencies

Layers 3 and 4; the profinite-and-pro-`p`-groups roadmap for the completed group algebra (§5.3);
the local-fields-and-ramification roadmap for §5.1.1 at odd `p`.

---

## Dependency graph

```text
Layer 0  →  Layer 1  →  Layer 2  →  Layer 3  →  Layer 4  →  Layer 5
                            ↘                       ↗
                              ————————————————————
```

Layers 0–2 are linear and independent of `p`. Layer 3 uses Layer 2 (the model space, its dual, and
the ON-basis vocabulary) and Mathlib's Mahler theorem. Layer 4 uses Layers 2 and 3 (§4.1 and §4.4
are Layer 2 applied to `K⟨X⟩` and to the disc model; §4.4.3 and §4.7 are Layer 3's Mahler
coefficients); Layer 5 uses Layer 4 throughout and §3.4 for the measures. The adic-spaces roadmap
is cited at §0.4.5–6, §1.2.1, §1.4.1 and §4.1.1; the Newton-polygons roadmap at §0.4.3 and §4.1.5;
the local-fields-and-ramification roadmap at §4.5.7 and §5.1.1; the profinite-and-pro-`p`-groups
roadmap at §5.3.

## Acceptance examples

The following should be proved alongside the general theory, and they are the things a reviewer
should check are present.

- `‖∑' n, pⁿ‖ = 1` in `ℤ_p` with the dominant term `n = 0`, and `‖∑' n, pⁿ⁺¹ xₙ‖ < 1` for any null
  family `xₙ` of `ℤ_p`.
- `ℚ_p⟨X⟩` is a Tate normed ring with pseudo-uniformiser `p`, its unit ball is `ℤ_p⟨X⟩`, and it is
  a Tate ring in Huber's sense with pair of definition `(ℤ_p⟨X⟩, (p))`.
- The quotient map `ℚ_p ² → ℚ_p`, `(x, y) ↦ x + p y`, admits preimages of norm at most `‖n‖`, and
  the open mapping constant is `1`.
- `C(ℤ_p, ℚ_p)` is orthonormalisable, by Mahler's basis (§3.2) and, independently, by Serre's
  theorem (§2.3) since `ℚ_p` is discretely valued and the sup norm takes values in `p^ℤ`.
- `ℂ_p` with the norm `2 ‖·‖`, for odd `p`, is potentially but not literally orthonormalisable.
- The matrix of the shift `(fₙ) ↦ (f_{n+1})` on `C₀(ℕ, ℚ_p)` has entries `matrixCoeff i j = [j = i + 1]`,
  columns of norm `1`, and row suprema `1`, so the shift is bounded of norm `1` and its row suprema
  do not tend to `0`.
- The matrix with unit diagonal and entries `p` below it is a unitriangular perturbation of level
  `p⁻¹`, hence an isometric automorphism of `C₀(ℕ, ℚ_p)`.
- The Mahler coefficients of `x ↦ x²` are `(0, 1, 2, 0, 0, …)`, of `x ↦ (1 + p) ^ x` are `pⁿ`, and
  of `x ↦ x ^ p − x` are finitely supported with sup norm `1`, while the function has sup norm
  `p⁻¹` on `ℤ_p`.
- `1_{1 + pℤ_p}` has van der Put expansion `e₁` and Mahler expansion computed over `ℚ_p(ζ_p)`.
- The Amice transform of `dirac 1` is `1 + T`, of `dirac a` is `(1 + T) ^ a`, and
  `D(ℤ_p, ℤ_p) ≅ ℤ_p⟦T⟧` sends convolution to multiplication.
- `x ↦ ζ_p ^ x` is analytic of level `1` and not of level `0`; `x ↦ (1 + p) ^ x` is analytic of level
  `0` for odd `p`; both criteria of §4.6.2 agree on them.
- `amice h n = ⌊n/pʰ⌋! · (x choose n)` has `ℤ_p`-integral Taylor coefficients on every disc
  `a + pʰℤ_p`, and the Amice basis at level `0` is `x (x − 1) ⋯ (x − n + 1)`.
- `padicExp` converges at `p` and `padicLog` at `1 + p`, `padicLog (padicExp p) = p`,
  `padicLog ζ_p = 0`, and `(1 + p) ^ (1/2)` computed by the binomial series squares to `1 + p`.
- `ℤ_3^× = {±1} × (1 + 3ℤ_3)`, `γ = padicExp 3`, and the character `x ↦ x ^ k` has coordinate
  `T = padicExp (3k) − 1` of valuation `1 + v_3(k)`.
- For `p = 3`, `T₀` with `‖T₀‖ = 3^{−1/2}` is a halo point, `κ_{T₀}` is analytic of level `2` and
  not of level `1`, and the expansion of `z ↦ κ_{T₀}(9 z + 1)` is restricted at some radius
  `r > 1`.
- `‖T‖ = ‖p‖ = 3⁻¹` and `‖pT⁻¹‖ = 1` in `Halo 3`; `HaloTate 3` is Banach–Tate with
  `‖T ^ n d‖ = 3^{−n} ‖d‖` for all `n ∈ ℤ`; `∑_{m < 0} p ^ (−m) T ^ m` specialises at
  `‖T₀‖ = 3^{−1/2}` and not at `‖T₀‖ = 3⁻¹`.

## Beyond this roadmap

⚠ **This section is a roadmap-for-a-roadmap. Do not attempt any of it here.** It records what this
roadmap is for, so that the conventions above are chosen with the sequels in mind.

The Banach–Tate rings, model spaces and matrices of Layers 0–2 are the setting in which
Serre's, Buzzard's, Bellaïche's and Johansson–Newton's theory of completely continuous operators
and their Fredholm determinants `det(1 − Tu)` lives; that theory, its Riesz decompositions and its
slope factorisations are the compact-operators roadmap. The characters, their expansions
`κ(cz + d)` (§5.5) and the Tate algebra as the model space (§4.1) are the setting of Jacobs's
weight-`κ` action on `K⟨z⟩` and of Buzzard's overconvergent automorphic forms, the
overconvergent-forms roadmap. The halo ring, its specialisations, the disc models at every level
and Amice's theorem (§4.4, §5.6) are what Liu–Wan–Xiao's halo estimate and its spectral consequences
consume, the spectral-halo roadmap. What those roadmaps ask of this one is that Layers 0–2 hold over
a Banach–Tate ring and not only over a field, that the disc model of `LA_h` be literally
`C₀(ZMod (p ^ h) × ℕ, E)` so that block operators can be built on it, and that the level of a
character be a theorem with the threshold of §5.4.2. All three are what is specified above.

Further afield: the Amice transform of distributions on `ℤ_p` is the first case of
Schneider–Teitelbaum's Fourier theory for `𝒪_K`, and the locally analytic functions on `ℤ_p` are the
first case of locally analytic vectors of `p`-adic Lie groups (Emerton); the measures of §3.4 and
the specialisations of §5.3 are the vocabulary of `p`-adic `L`-functions; and Hahn–Banach over
spherically complete fields, of which a Lean formalisation outside Mathlib exists (Yuan,
arXiv:2601.21734), would extend §2.5 from `C₀` to arbitrary Banach spaces.

## References

- J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*, Publ. Math.
  IHÉS 12 (1962), 69–85 — [Serre]. §1 (Lemme 1, Proposition 1) is the source of §2.3: the rescaling
  of the norm and the orthonormal basis lifted from a basis of the residue space.
- P. Schneider, *Nonarchimedean Functional Analysis*, Springer Monographs (2002); the lecture-notes
  version `https://ivv5hpp.uni-muenster.de/u/pschnei/publ/lectnotes/nfa.pdf` — [Sch]. §3
  (normed vector spaces, `c₀(X)` and `ℓ^∞(X)`), Proposition 4.13 (finite-dimensional spaces),
  Proposition 6.15 (Banach–Steinhaus), Propositions 8.5–8.6 and Corollary 8.7 (closed graph, open
  mapping), Proposition 10.1 and Remark 10.2 (Serre's theorem over a discretely valued field),
  Lemma 10.3 (the index of `c₀(X)` is an invariant), Proposition 10.4 (countable type).
- S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261 (1984) — [BGR].
  §2.1.8 (bounded and continuous linear maps), §3.7.2–3.7.3 (closed ideals and the canonical
  topology on finite modules over Noetherian Banach algebras), keyed in BGR's own numbering.
- K. Buzzard, *Eigenvarieties*, in *L-functions and Galois representations*, LMS Lecture Notes 320
  (2007), §2 — [Buz07]. Proposition 2.1 (open mapping theorem, finite Banach modules), Lemma 2.2,
  the definitions of ONable modules and of `c_A(I)` with its universal property, Lemma 2.3 (finitely
  generated submodules of `c_A(I)`), and the matrix calculus on p. 65.
- J. Bellaïche, *The Eigenbook*, Pathways in Mathematics, Birkhäuser (2021), §3.1, and the draft
  Chapter II §II.1 — [Bel]. Definitions II.1.5–II.1.6 and Example II.1.7 (orthonormal bases,
  potentially orthonormalisable modules), Lemma II.1.8 / published Lemma 3.1.12 (truncations
  approximate closed finitely generated submodules) and Hypothesis 3.1.8, Hypothesis II.1.11,
  Lemma II.1.12 and Theorem II.1.13 (Serre's theorem in ring form), Exercise II.1.19 and
  Proposition II.1.20 (property (Pr)).
- C. Johansson, J. Newton, *Extended eigenvarieties for overconvergent cohomology*, Algebra &
  Number Theory 13 (2019); arXiv:1604.07739v4, §2.1 — [JN]. Definition 2.1.2 (Tate normed rings,
  Banach–Tate rings, multiplicative pseudo-uniformisers, `v_ϖ`), Remark 2.1.3 (the bridge to Huber's
  Tate rings), Definition 2.1.4 (Banach modules, boundedness), Definition 2.1.5 (`c_R(I)`, ON-able,
  property (Pr)), Lemmas 2.1.6–2.1.7 (comparison of equivalent norms; the corrected statement),
  Proposition 2.1.8.
- R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217 (1994),
  Lemma 2.4(i) — the open mapping theorem for Tate rings; and L. Henkel, *An Open Mapping Theorem
  for rings which have a zero sequence of units*, arXiv:1407.5647, the form implemented in Tau Ceti.
- J. Fresnel, M. van der Put, *Rigid Analytic Geometry and Its Applications*, Progress in Math. 218
  (2004), Lemma 1.2.3 — closedness of submodules of finite Banach modules over Noetherian Banach
  algebras; and J. Ludwig, *Spectral theory and the eigenvariety machine*, arXiv:2407.18073,
  Remark 2.25 and Lemma 2.26.
- A. C. M. van Rooij, *Non-Archimedean Functional Analysis*, Dekker (1978), and C. Perez-Garcia,
  W. H. Schikhof, *Locally Convex Spaces over Non-Archimedean Valued Fields*, Cambridge Studies 119
  (2010), Chapter 2 — `t`-orthogonal bases and spaces of countable type.
- K. Mahler, *An interpolation series for continuous functions of a p-adic variable*, J. reine
  angew. Math. 199 (1958), 23–34 — Mahler's theorem; and W. H. Schikhof, *Ultrametric Calculus*,
  Cambridge Studies 4 (1984), the sections "Mahler's base" and "van der Put's base".
- Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180 — the orthonormal
  basis `⌊n/pʰ⌋!·(x choose n)` of the locally analytic functions and the transform of distributions.
- P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), 13–59 — [Col10]. The
  primary source for Layers 3 and 4: Définition 1.1.3 and Proposition 1.1.5 (orthonormal bases,
  Serre's theorem), Théorème 1.2.3 and Corollaire 1.2.4 (Mahler), Proposition 1.3.2 and
  Définition 1.3.3 (the van der Put "base d'ondelettes"), §I.4 (analytic functions on a disc,
  `LA_h`, Remarque 1.4.4, Lemme 1.4.5), Théorème 1.4.7 (Amice), Corollaire 1.4.8, Lemme 1.4.9,
  §II.2 (distributions and the Amice transform, Lemme II.2.1, Théorème II.2.2), §II.3 (measures).
- P. Schneider, J. Teitelbaum, *p-adic Fourier theory*, Doc. Math. 6 (2001), 447–481, §2 — the
  Amice transform as the `ℤ_p` case of Fourier theory.
- N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, 2nd ed., GTM 58 (1984),
  Ch. IV §§1–2 — the convergence discs of `exp`, `log` and the binomial series; and A. M. Robert,
  *A Course in p-adic Analysis*, GTM 198 (2000), Ch. 4 §2 (Mahler expansions) and Ch. 5 §4
  (the exponential and logarithm).
- L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83 (1997), Theorem 7.1
  (`ℤ_p⟦Γ⟧ ≅ ℤ_p⟦T⟧`) and §12.2 (measures and power series) — the Iwasawa algebra and the Amice
  transform of measures, with the generator `1 + p`.
- R. Liu, D. Wan, L. Xiao, *The eigencurve over the boundary of weight space*, Duke Math. J. 166
  (2017); arXiv:1412.2584v4 — [LWX]. Notation 2.1 (the universal character, `T`-coordinate, weight
  space), §2.1 (`m`-locally analytic characters, their extension, the classical characters and their
  coordinates), (2.3.4) and §2.16 (the disc model and Colmez's basis), Definition 2.13, Lemma 3.15
  and (3.16.3) (the ring `Λ^{>1/p}`).
- D. Jacobs, *Slopes of Compact Hecke Operators*, PhD thesis, Imperial College (2003), Definition
  1.27 — the weight-`κ` action that §5.5 serves.

⚠ **Orientation and normalisation.** [Col10] normalises `v_p(p) = 1` and works with valuations;
[JN] and [Buz07] work with norms; this roadmap works with norms normalised by `‖p‖ = p⁻¹`
(convention 8), so that Colmez's `v_p(x) > 1/(p−1)` reads `‖x‖ < r_p`. [Col10] centres the discs at
`−j`, `1 ≤ j ≤ pʰ`; the disc model uses the natural representatives `0 ≤ a < pʰ`, and the
unitriangular ordering of §4.4.1 is the block reversal that reconciles the two. [LWX] index
analyticity by `m` with discs `a + q⁻¹ pᵐ ℤ_p`; the level `h` of §4.3 is the exponent of the disc
radius, so `h = m − v_p(q)` in the disc statements and `h = m` in the criterion of §5.4.2 as they
state it. When transcribing a statement, check the convention against §5.4.2 rather than assuming
it.

## Existing Lean work

The principal source of existing code is `github.com/WilliamCoram/PhD` (Apache-2.0), at commit
`747bb77` (2026-09-12): the directory `PhD/Main/TateFredholm/` for Layers 0–2 (the Banach–Tate
setting, the operator norm and open mapping theorem, the model space, Serre's theorem, matrices
and truncations, the unitriangular criterion), the files `PhD/Main/ForMathlib/Analysis/Normed/Ring/`
and `PhD/Main/ForMathlib/Topology/Algebra/` for §0.2, the files `PhD/Main/LWX/{00_Colmez, 00_HaloRing,
00_PadicExpLog, 01_AmiceValuation, 01_Binomial, 01_HaloTate, 01_UnitsLog, 04_IntegralModel,
05_Specialize, 06_HaloWeight, 07_PowSubOne, 08_AmiceBasis, 08_HaloWeightH, 09_DiscModel}.lean` for
Layers 3–5, and `PhD/Main/QMF/Weight/{00_Series, 04_Char, 06_Algebraic}.lean` for §5.5. It is the
only formalisation of this material known to us apart from Mathlib's Mahler basis, `AbstractMeasure`
and `AddChar` files (D. Loeffler), which Layer 3 builds on, and Yuan's spherical-completeness
development (arXiv:2601.21734), which is outside this roadmap's scope.

The existing material in those directories is by William Coram, who has agreed to its integration
into Tau Ceti. ⚠ The wider repository also contains files by other authors, derived from the FLT
project and from Mathlib; those are not migration sources for this roadmap, and the provenance of
anything copied must be checked file-by-file rather than directory-by-directory. The three blueprint
files `PhD/Main/Test/bad/CompactOperators{,Bellaiche,JohanssonNewton}.lean` carry 32–44 direct
`sorry`s each and are source documentation, not migration sources; the `ONBasis` structure in the
Bellaïche file is the basis-language formulation of §2.2.2.

Two separate audits are recorded below, for the reason the adic-spaces roadmap gives: a declaration
with no direct `sorry` is not the same as a theorem whose dependency cone is axiom-clean. The direct
column is a file-level `grep` count, which over-counts (comments match) and sees no cross-file
dependence. At the pin above, every file listed has a direct count of **0**. The transitive column
must be regenerated at migration by a `#print axioms` gate on the capstones in Tau Ceti CI; the
source project reports every directory listed clean on `propext`, `Classical.choice` and
`Quot.sound`, and that claim is to be re-verified, not carried over.

| Roadmap section | Existing source | Direct status at the pin | Transitive status | Roadmap status |
|---|---|---|---|---|
| §0.1 ultrametric sums | `TateFredholm/00_Tate.lean` (`summable_of_tendsto_cofinite`, `norm_tsum_le_iSup`), `LWX/05_Sharpness.lean` (`norm_tsum_lt_of_forall_lt`, `norm_tsum_eq_of_forall_lt`) | no direct `sorry` | audit required | present; the summability criterion is now Mathlib's and is to be deleted in favour of it |
| §0.2 normed rings | `ForMathlib/Analysis/Normed/Ring/{PowerBounded,TopologicallyNilpotent,Ultra,NormMulUnit,NegLogNorm}.lean`, `ForMathlib/Topology/Algebra/{Bounded,PowerBounded,TopologicallyNilpotent}.lean` | no direct `sorry` | audit required | present; restate against `TauCeti.Huber.IsPowerBounded` |
| §0.3 Banach modules | `TateFredholm/00_Tate.lean`, `01_OperatorNorm.lean` (scaling), `08_BaseChange.lean` (`norm_le_pow_of_equiv`, `norm_comparison_of_common_uniformizer`, `Rescaled`) | no direct `sorry` | audit required | present except quotient norms and §0.3.4, which are new |
| §0.4 Banach–Tate rings | `TateFredholm/00_Tate.lean` (`IsTate`, `PseudoUniformizer`, `val`, `isTate_of_normedAlgebra`), `HandClean/00_TateRings.lean` (the bridge to `IsTateRing`), `01_AddVal.lean` (the seam with `normAddVal`) | no direct `sorry` | audit required | present; the bridge back (§0.4.6) is new (`Test/TateConverse.md` records the design) |
| §1.1 operator norm | `TateFredholm/01_OperatorNorm.lean`, `Test/OpNormMathlibPR.{lean,md}` | no direct `sorry` | audit required | present, as a scoped instance; the agreement theorem §1.1.6 is new |
| §1.2 open mapping and companions | `TateFredholm/01_OperatorNorm.lean` (`exists_preimage_norm_le`, `exists_inverse_of_norm_id_sub_lt_one`) | no direct `sorry` | audit required | present for the open mapping theorem, by a direct Baire argument; derive from Tau Ceti's Henkel form; closed graph and Banach–Steinhaus are new |
| §1.4 Noetherian bases | `TateFredholm/05_Noetherian.lean` (`isClosed_of_finite`, `exists_truncation_injOn`, `isClosed_of_fg`) | no direct `sorry` | audit required | present; §2.6.5 is `isClosed_of_fg` |
| §2.1 model space | `TateFredholm/03_ModelSpace.lean` (`cSpace`, `single`, `evalCLM`, `hasSum_single`), `04_TateAlgebra.lean` (`reindex`), `06_BlockOp.lean`, `08_BlockMap.lean` (blocks) | no direct `sorry` | audit required | present on a synonym `Ix I`; restate on `C₀` with `DiscreteTopology` (convention 3) |
| §2.2 orthonormal families | `TateFredholm/03_ModelSpace.lean` (`IsONable`, `IsPotentiallyONable`, `HasPr`), `06_Pr.lean` (`HasPr.exists_lift`, `HasPr.projective`), `Test/bad/CompactOperatorsBellaiche.lean` (`ONBasis`) | no direct `sorry` (the `Test/bad` file: 44) | audit required | partial; the family predicates and `t`-orthogonality are new |
| §2.3 Serre's theorem | `TateFredholm/07_Residue.lean`, `08_BaseChange.lean` (`isPotentiallyONable_of_uniformizer`) | no direct `sorry` | audit required | present in the field form; the ring form §2.3.2 and Lemma 10.3 are new |
| §2.4 countable type | — | — | — | new |
| §2.5 the dual | — | — | — | new |
| §2.6 matrices and truncations | `TateFredholm/04_Matrix.lean` (`matrixCoeff`, `tendsto_matrixCoeff_column`, `norm_eq_iSup_matrixCoeff`, `exists_coeffEquiv`, `truncation`, `exists_truncation_near`), `08_BaseChange.lean` (`charPowerSeries_map_equiv`'s matrix part) | no direct `sorry` | audit required | present; check the orientation against convention 7 |
| §2.7 unitriangular criterion | `TateFredholm/06_Unitriangular.lean`; `LWX/00_Colmez.lean`, `08_AmiceBasis.lean` (diagonal operators) | no direct `sorry` | audit required | present over a field; restate over a Banach ring |
| §3.1 continuous functions | `LWX/04_IntegralModel.lean` (`CFun`) | no direct `sorry` | audit required | partial; density of locally constant functions and the disc decomposition are new |
| §3.2 Mahler coefficients | Mathlib; `LWX/00_Colmez.lean` (`mahlerCoeffPow`, `pow_eq_sum_choose_mul_mahlerCoeffPow`, `fwdDiff_iter_evalAt_natCast`), `02_TiltedDegree.lean` (`Δ̃` of `mahler`, Leibniz), `04_IntegralModel.lean` (`mahlerON`, `mahlerCoeffs`) | no direct `sorry` | audit required | present for monomials and series; translates, products and the disc Mahler basis are new |
| §3.3 van der Put basis | — | — | — | new |
| §3.4 measures and the Amice transform | Mathlib (`AbstractMeasure`, `AddChar`) | — | — | new |
| §4.1 restricted series as functions | `TateFredholm/04_TateAlgebra.lean` (`restrictedEquivCSpace`, `isONable_restricted`), `00_Compose.lean` (`compAn`), `QMF/Weight/04_Char.lean` (`evalAt`, `evalAt_eq_zero_iff_of_forall`, `evalAt_compAn`), `LWX/01_Binomial.lean` (`eq_zero_of_forall_tsum_natCast_eq_zero`) | no direct `sorry` | audit required | present; the module-valued identity theorem §4.1.6 is new |
| §4.2–4.3 discs and `LA_h` | `LWX/08_AmiceBasis.lean` (`discCoord`, `discEval`, `discToMahler`), `09_DiscModel.lean` (the disc parametrisation), `10_DiscForms.lean` | no direct `sorry` | audit required | present as the disc model only; the function-side predicate, the inclusions and `LP_{h,≤k}` are new |
| §4.4 Amice's theorem | `LWX/01_AmiceValuation.lean` (`discPoly`, the three coefficient facts), `08_AmiceBasis.lean` (`colmezDiscEquiv`, `discToMahler_apply_eq_fwdDiff`), `00_Colmez.lean` (`colmezEquiv`, level `0`) | no direct `sorry` | audit required | present over a field; restate module-valued, with §4.4.3–4 new |
| §4.5 exp, log, binomial | `LWX/00_PadicExpLog.lean` (odd `p`, the joint disc `‖x‖² < ‖p‖`), `01_Binomial.lean`, `01_UnitsLog.lean` (`teichmuller`, `qlog`), `07_PowSubOne.lean`, `JacobsSlash/1_PadicAnalytic.lean` (`p = 3`) | no direct `sorry` | audit required | present for odd `p` on a smaller disc; the sharp radius `r_p`, `p = 2`, and the local-field seam are new |
| §4.6 characters of `ℤ_p` | Mathlib (`AddChar`); `LWX/07_PowSubOne.lean`, `08_HaloWeightH.lean` | no direct `sorry` | audit required | partial; the level criterion in both forms is new |
| §4.7 distributions | — | — | — | new |
| §5.1 structure of `ℤ_p^×` | `LWX/01_UnitsLog.lean` (`teichmuller`, `oneUnitPart`, `qlog`) | no direct `sorry` | audit required | present for odd `p` |
| §5.2 weight space | Mathlib (`AddChar`); `LWX/05_Specialize.lean`, `06_HaloWeight.lean` | no direct `sorry` | audit required | partial; the parametrisation and the classical coordinates are new |
| §5.3 Iwasawa algebra | `LWX/04_IntegralModel.lean` (`univChar` into `HaloInt`, `oneAddTPow`) | no direct `sorry` | audit required | the universal character is present into `Λ^{>1/p}`; `Λ` itself, its structure theorem and measures are new |
| §5.4 analyticity level | `LWX/06_HaloWeight.lean`, `08_HaloWeightH.lean` (`haloWeightH`, `specialize_univChar_eq_padicExp`), `07_PowSubOne.lean` (`exists_sq_norm_pow_prime_pow_sub_one_lt`) | no direct `sorry` | audit required | present at halo points with the sufficient criterion; the sharp criterion is new |
| §5.5 expansions `κ(cz+d)` | `QMF/Weight/04_Char.lean` (`ExpansionData`, `AnalyticWeight`, `col_eq_of_mem`), `06_Algebraic.lean`, `LWX/06_HaloWeight.lean` (`haloCol`, `haloExpansion`), `08_HaloWeightH.lean` (`haloColH`, `norm_coeff_haloColH_le`) | no direct `sorry` | audit required | present as data-carrying `ExpansionData` at halo points and algebraic weights; the general theorem §5.5.1–2 is new |
| §5.6 the halo ring | `LWX/00_HaloRing.lean` (`HaloInt`, `norm_T_mul`, `norm_le_zpow_iff`), `01_HaloTate.lean` (`HaloTate`, `instIsTate`), `05_Specialize.lean` (`specializeHom`) | no direct `sorry` | audit required | present without the `Δ`-factor; §5.6.3 and §5.6.6 are new |

⚠ **Do not treat the existing file layout as prescriptive.** The source development is organised
around the compact-operator theory it was written for: the model space is a synonym `Ix I` with the
discrete topology rather than `C₀` on a discrete type, the operator norm is a scoped instance whose
agreement with Mathlib's is not stated, the exponential and logarithm are proved on the joint disc
`‖x‖² < ‖p‖` for odd `p` only, `LA_h` exists only as the disc model `c(ZMod (p^h) × ℕ, K)` over a
field, the halo ring omits the `Δ`-factor, and the analyticity of the halo character is proved by a
sufficient condition rather than the criterion of §5.4.2. The migration is expected to restate the
theory at the generality specified above — Banach–Tate rings, module-valued function spaces, all
primes with `q` — not to port the layout.
