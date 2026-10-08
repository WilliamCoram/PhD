# Roadmap: rigid analytic geometry

This roadmap develops Tate's rigid analytic geometry over a complete nonarchimedean field `K`,
following Bosch–Güntzer–Remmert's *Non-Archimedean Analysis* Parts B and C: affinoid algebras and
their spectra, affinoid subdomains, Tate's acyclicity theorem, Grothendieck topologies and sheaves,
rigid analytic varieties, coherent modules, and the analytification of algebraic varieties. Five
results are the headline milestones.

```text
Noether normalisation:   every nonzero affinoid algebra is a finite extension of some Tate algebra T_d
Maximum modulus:         every affinoid function attains its supremum at a point of the spectrum
Gerritzen–Grauert:       every affinoid subdomain is a finite union of rational subdomains
Tate's acyclicity:       every finite affinoid covering is acyclic for the structure presheaf
Kiehl:                   coherent modules on an affinoid variety are the finite modules over its algebra
```

and a sixth, the bridge to the adic-spaces roadmap:

```text
the maximal spectrum of an affinoid algebra is the set of classical points of its adic spectrum,
rational subdomains are the rational subsets, and the two Čech complexes of a rational covering agree.
```

The first layers are commutative algebra and Banach-algebra theory: the Tate algebras beyond what
the adic-spaces roadmap builds of them, affinoid algebras with their presentations and residue
norms, and the supremum seminorm. The middle layers are the local geometry: affinoid varieties as
maximal spectra, the Nullstellensatz, affinoid subdomains and their classification, and Tate's
theorem. The last layers are the global theory: G-topologies, sheaves, rigid varieties by gluing,
coherent modules, the GAGA functor, and the comparison with Huber's adic spectra, which is where
this roadmap meets the adic-spaces roadmap and lets each side use the other's theorems.

## Scope

The roadmap includes the following material.

- The Tate algebras `Tₙ = K⟨X₁, …, Xₙ⟩` beyond the adic-spaces roadmap's slice: the Gauss norm as
  the supremum norm, the reduction `T̃ₙ = K̃[X₁, …, Xₙ]`, the Weierstrass finiteness theorem and
  distinguished charts, Rückert's applications (unique factorisation, normality, the Jacobson
  property, Krull dimension `n`), strict closedness of ideals, and the weak stability of the fraction
  field with its consequence that `Tₙ` is Japanese.
- Affinoid algebras as quotients of Tate algebras: presentations, residue norms, the Banach-algebra
  structure, the universal property of `A⟨X₁, …, Xₘ⟩`, affinoid tensor products, quotients and
  finite extensions of the ground field, Noether normalisation, finiteness of residue fields,
  continuity of all homomorphisms and uniqueness of the Banach topology, the generalised rings of
  fractions `A⟨f, g⁻¹⟩` and `A⟨f/g⟩`, and the algebras of convergent series on polydiscs of
  arbitrary polyradius.
- The supremum seminorm: the maximum modulus principle, the value group, the characterisation of
  nilpotent, power-bounded and topologically nilpotent elements, the spectral-radius formula, the
  reduction `Ã`, the theorem that reduced affinoid algebras are Banach function algebras, and the
  isometry criterion through the reduction.
- Affinoid varieties: the maximal spectrum `Sp A`, its points through finite extensions of `K`,
  the Nullstellensatz, affinoid subsets and their irreducible decomposition, affinoid maps and the
  category of affinoid varieties, closed immersions and finite maps, fibre products, and the
  canonical topology.
- Affinoid subdomains: the universal property, Weierstrass, Laurent and rational domains with their
  algebras, transitivity, intersections and preimages, the openness theorem, germs and stalks,
  flatness of the restriction maps, locally closed, closed and open immersions, Runge immersions,
  and the Gerritzen–Grauert theorem.
- Čech cohomology of presheaves on a covering, refinements and the comparison theorem, and Tate's
  acyclicity theorem for finite affinoid coverings, including its module form and its corollaries:
  the sheaf property of `𝒪_X`, the gluing of morphisms, and the characterisation of affinoid
  subdomains as open immersions.
- Grothendieck topologies on a set, their enhancing procedures and pasting, the weak and strong
  G-topologies on an affinoid variety, sheaves and sheafification on G-topological spaces and the
  extension of sheaves from the weak to the strong G-topology.
- Rigid analytic varieties as locally G-ringed spaces: affinoid varieties as such spaces, pasting
  of varieties and of morphisms, open subspaces, the basic examples (affine and projective space,
  the open disc, annuli), fibre products, and extension of the ground field.
- Coherent modules: associated modules on affinoid varieties, `𝔘`-coherence, Kiehl's theorem,
  finite morphisms, coherent ideals and closed analytic subvarieties, the identification of Čech
  cohomology with sheaf cohomology for coverings acyclic on all intersections, and the vanishing
  of higher cohomology of coherent modules on affinoid varieties.
- Separated, quasi-compact, quasi-separated and proper morphisms: their definitions, their
  behaviour under base change and fibre products, and the separatedness of affinoid varieties.
- The GAGA functor: the analytification of a `K`-scheme locally of finite type, its universal
  property, its points, and its functoriality.
- The comparison with adic spaces: the classical points of `Spa(A, A°)`, the correspondence of
  rational subdomains with rational subsets and of their coordinate rings, the covering criterion,
  the agreement of the Čech complexes, and the fully faithful functor from rigid varieties to adic
  spaces over `Spa(K, K°)`.

The roadmap does not include the following.

- ⚠ **Huber rings, Tate rings, restricted power series as topological rings, and Weierstrass
  division and preparation in `Tₙ`.** These are Layer 0 and §0.5 of the adic-spaces roadmap; Layer
  0 here starts where that roadmap stops and takes them as its floor (convention 2). The
  noetherianity of `Tₙ` is in both roadmaps: Layer 0 here proves it through Rückert's theory
  (§0.3.2), which gives factoriality, the Jacobson property and the dimension at the same time. The same applies to the valuation spectrum, continuous valuations, the adic
  spectrum `Spa(A, A⁺)`, rational subsets, rational localisation `A⟨T/s⟩`, the structure presheaf of
  an adic spectrum and the strongly noetherian form of Tate acyclicity (its Layers 1–4), and to
  adic spaces and their gluing (its Layer 5). Layer 8 consumes all of that and never rebuilds it.
- ⚠ **The reduction theory of affinoid algebras and varieties beyond the reduction map**: the
  finiteness of the reduction functor and of `A ↦ Å` (BGR 6.3.2–6.3.5, 6.4), the reduction of
  affinoid varieties (BGR 7.1.5) and affinoid subdomains and reduction (BGR 7.2.6). These are the
  algebraic entry to formal models and belong with a formal-and-rigid-geometry roadmap, together
  with Raynaud's theory of formal models and admissible blowing-ups.
- The direct image theorem of Kiehl, the theorem on formal functions, and the GAGA comparison
  theorems of Köpf (BGR 9.6.3; Bosch's *Lectures* 1.16–1.17). Properness is defined here and its
  elementary properties are proved; the finiteness of higher direct images is not.
- Tate's elliptic curves and Mumford curves as rigid varieties (BGR 9.7). The point-level Tate curve
  is in the elliptic-curves roadmap; its uniformisation as a quotient of a rigid analytic torus is
  a separate development.
- Berkovich spaces, dagger (overconvergent) spaces, étale and rigid cohomology, and the
  completed tensor product of general Banach modules. The affinoid tensor product `B₁ ⊗̂_A B₂` is
  built here by presentations (§1.1.5) and nothing more general is; the adic-spaces roadmap names a
  separate roadmap for completed tensor products and fibre products of adic spaces.
- Eigenvarieties and spectral varieties over affinoid weight spaces, and the rigid-analytic
  weight space itself. The compact-operators and overconvergent-forms roadmaps leave these to the
  rigid or adic geometry; they are the first consumers of this roadmap and are recorded in
  *Beyond this roadmap*.
- The general `p`-adic functional analysis of Banach modules, orthonormal bases and compact
  operators (the `p`-adic-functional-analysis and compact-operators roadmaps). Layer 1 cites the
  former for the Banach-module facts about finite modules over noetherian Banach algebras.

The algebra of Layers 0–2 belongs under `TauCeti/RingTheory/Affinoid/`, mirroring the adic
roadmap's `TauCeti/RingTheory/Huber/`. The G-topologies of §6.1–6.2 are reusable topology and
belong under `TauCeti/Topology/GTopology/`; Čech cohomology of presheaves on a site, where it goes
beyond Mathlib, under `TauCeti/CategoryTheory/Sites/Cech/`. Everything geometric — affinoid
varieties, subdomains, rigid varieties, coherent modules, analytification and the comparison with
adic spaces — belongs under `TauCeti/AlgebraicGeometry/Rigid/`.

## Conventions and coordination with Mathlib

The following Mathlib pull requests are relevant to this roadmap.

- mathlib4#26089 (merged) made restricted power series a ring, and mathlib4#39583 (merged) aligned
  the univariate definition with the multivariate one; `MvPowerSeries.IsRestricted.subring` and
  `PowerSeries.IsRestricted.subring` are the result, and `Tₙ` is the former at the unit polyradius.
- mathlib4#42867 makes restricted multivariate power series a type of their own, and mathlib4#42871
  extends the multivariate Gauss-norm API. Either may change the shape of the Tate algebra that
  Layer 0 consumes; the Newton-polygons roadmap coordinates with the same two pull requests.
- mathlib4#40013 defines bounded subsets of topological rings and power-bounded elements; the
  adic-spaces roadmap coordinates with it, and Tau Ceti's `TauCeti.Huber.IsPowerBounded` is
  shaped as it is. §2.3 is stated with that vocabulary.
- mathlib4#38009, #42312, #42314 and #42315 (valuation spectrum, Huber rings, continuous valuations,
  an initial `Spa`) are the adic-spaces roadmap's; Layer 8 consumes whatever shape they settle on
  through that roadmap, not directly.

The Tau Ceti API should agree with the final Mathlib API. ⚠ **None of these is a blocker, and
nothing in this roadmap waits on Mathlib.** Where a pull request is open, the object is built here
named and shaped as the pull request names and shapes it, so that if it lands the Tau Ceti copy is
deleted in favour of an import.

Numbered references of the form `BGR 6.1.2/3` are to Bosch–Güntzer–Remmert, section and statement
number; references of the form `Bosch 1.6/9` are to Bosch's *Lectures on Formal and Rigid Geometry*
(see the References), whose Part 1 follows the same route with shorter proofs and is the second
source for every statement of Layers 1–7.

These conventions are binding. Several of them are corrections to the obvious first design, and the
reasons are given because an implementor who does not know them will reintroduce the problem.

1. **The ground field is complete, nonarchimedean and nontrivially valued, and nothing else.**
   `K` carries `[NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]`. It is not
   assumed discretely valued, algebraically closed, or of any characteristic, and its value group
   `|K^×|` may be dense. Every statement that needs a radius in `√|K^×|` or `|K^×|` says so in its
   hypotheses (BGR 7.2.3, 9.1.4/5). The algebraic closure `K_a` enters only through *finite*
   extensions of `K`, each normed by Mathlib's `spectralNorm`, which is the unique extension of the
   norm of `K` (BGR 3.2.4/2); no completion of `K_a` is used anywhere in Layers 0–8.

2. **The Tate algebra is Mathlib's ring of restricted power series.** `Tₙ` is the `K`-subalgebra
   `MvPowerSeries.IsRestricted.subring (fun _ : Fin n ↦ 1)` of `MvPowerSeries (Fin n) K`, normed
   by Mathlib's `MvPowerSeries.gaussNorm norm (fun _ ↦ 1)`. In code it is the type of
   mathlib4#42867, `MvPowerSeries.Restricted K (1 : Fin n → ℝ)` — the subring as a type, with its
   Gauss-norm `NormedCommRing` — under the name `Affinoid.TateAlgebra K n`; statements that do not
   use `Fin n` are made for `MvPowerSeries.Restricted K (1 : σ → ℝ)`, and statements that hold at
   every polyradius are made there. The floor — the normed ring and its completeness, the iteration
   isomorphism, the criterion for units, Weierstrass division and preparation — is the
   adic-spaces roadmap's §0.5 mathematically, and the one-variable case at every radius is also
   the Newton-polygons roadmap's §3.1; an implementation that does not have that code builds the
   floor as mathlib4#42867 shapes it (the rule above). Layer 0 adds what those roadmaps do not ask
   for. The topology is the Gauss-norm topology; the adic-spaces roadmap's weighted restricted
   series carry the same topology, and the identification is a theorem of its §0.5, not a
   convention here.

   ⚠ The distinguished variable is `X 0`, the one Mathlib's `MvPowerSeries.finSuccEquiv` splits
   off. BGR and Bosch distinguish the last variable `Xₙ`; their `Xₙ` is this roadmap's `X 0`, and
   their chart `Xᵢ ↦ Xᵢ + Xₙ^{αᵢ}` is `X (i+1) ↦ X (i+1) + X 0 ^ αᵢ`. The text below keeps the
   sources' notation. Only one file should touch the iteration isomorphism (it restates the floor
   at the unit polyradius: the coefficients of a series in `X 0`, the polynomials in `X 0`, and
   division and preparation); the polyradius `Fin.tail 1` that the isomorphism produces is
   definitionally, not syntactically, the unit polyradius, and unification across it is slow.

3. **An affinoid algebra is a `Prop` on a `K`-algebra, and carries no topology.** `IsAffinoidAlgebra
   K A` says that some `Tₙ` surjects onto `A` as a `K`-algebra (BGR 6.1.1/1). The *affinoid
   topology* is the quotient topology of any presentation; that it does not depend on the
   presentation is BGR 6.1.3/1, that every `K`-algebra homomorphism between affinoid algebras is
   continuous is the same theorem, and that every `K`-Banach-algebra topology on an affinoid algebra
   is the affinoid topology is BGR 6.1.3/2. Consequently a theorem whose statement needs a norm
   takes `[NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]` together with
   `IsAffinoidAlgebra K A`, and is proved for every such norm at once. There is no data-carrying
   class recording a chosen residue norm.

   The reason: residue norms are not canonical — two presentations give equivalent but different
   norms — while the topology and every notion defined from it (power-boundedness, topological
   nilpotence, completeness of ideals) are. A data class would hide a choice and produce
   non-defeq instances on `A⟨f/g⟩` from its two presentations (BGR 6.1.4/2 and 6.1.4/4).

4. **Points are maximal ideals, and values are spectral norms on residue fields.** `Sp A` is
   Mathlib's `MaximalSpectrum A`. For `x ∈ Sp A` the residue field `A ⧸ x` is a finite extension
   of `K` (BGR 6.1.2/3), and `|f(x)|` is the spectral norm of the residue class of `f`, Mathlib's
   `spectralNorm K (A ⧸ x)`, spelled `spectralValue (minpoly K (mk f))` — its definition — so that
   no `Field` instance on the quotient has to be chosen. At a maximal ideal where the residue class
   of `f` is not algebraic over `K` this value is `0`; that happens only outside affinoid algebras
   and is BGR's convention of taking the supremum over `Max_K A` (3.8.1/1–2). No embedding of a residue field into an algebraic closure is chosen:
   `f(x)` itself is only defined up to `Gal(K_a/K)` (BGR 7.1.1), and the roadmap never uses it,
   only `|f(x)|`. The unit ball `Bⁿ(K_a)` appears once, in §3.1, as a description of `Sp Tₙ`.

5. **The supremum seminorm is a supremum over the maximal spectrum.** `|f|_sup = ⨆ x : Sp A,
   |f(x)|`, a real `iSup` (finite by BGR 3.8.2/2, zero on the zero algebra). It is not defined as
   the spectral radius `inf ‖fⁱ‖^{1/i}` and not as a supremum over `Bⁿ(K_a)`; both are theorems
   (BGR 6.2.3/3; §3.1).

6. **An affinoid subdomain is the data of its representing algebra.** `AffinoidSubdomain X` for
   `X = Sp A` bundles an affinoid algebra `A'`, a `K`-algebra map `A → A'`, the subset `U ⊆ Sp A`
   it lands in, and the universal property of BGR 7.2.2/2 (every affinoid map into `X` with image
   in `U` factors uniquely through `Sp A'`). The subset is derived, the algebra is data, and the
   uniqueness of the algebra up to unique isomorphism is a theorem. The special subdomains are
   constructed with their explicit algebras: the Weierstrass domain `X(f)` with `A⟨X⟩/(Xᵢ − fᵢ)`,
   the Laurent domain `X(f, g⁻¹)` with `A⟨X, Y⟩/(Xᵢ − fᵢ, gⱼYⱼ − 1)` (BGR 6.1.4/2), and the
   rational domain `X(f/g)` with `A⟨X⟩/(gXᵢ − fᵢ)` (BGR 6.1.4/4).

   ⚠ The rational domain's algebra is **the same ring** as the adic-spaces roadmap's completed
   rational localisation `A⟨T/s⟩` with `T = {f₁, …, fₘ, g}` and `s = g`: Tau Ceti's
   `TauCeti.Huber.PairOfDefinition.rationalQuotientRingEquiv` is precisely the isomorphism
   `A⟨X₁, …, Xₖ⟩ ⧸ (tᵢ − s Xᵢ) ≃ A⟨T/s⟩`. The quotient presentation is the definition here, the
   completed-localisation presentation is a theorem of §4.2, and Layer 8 rests on it. Do not build
   a third model.

7. **The coordinate rings of a covering are the data of the covering.** A finite affinoid covering
   of `Sp A` is a finite family of affinoid subdomains (convention 6) whose subsets cover; the Čech
   complex is formed from their algebras and the algebras of their finite intersections (BGR
   7.2.2/5, 7.2.3/7), with the restriction maps given by the universal property. Čech complexes are
   Mathlib's `cechComplexFunctor` on the poset of affinoid subdomains, which has finite products
   (intersections) by §4.3; the alternating complex is the auxiliary object of BGR 8.1.3 and the
   two have the same cohomology.

8. **A G-topology is a site on a poset of subsets, and sheaves are Mathlib's.** A G-topology on a
   set `X` (BGR 9.1.1/1) is a predicate `IsAdmissibleOpen : Set X → Prop` closed under binary
   intersection together with a predicate on families of admissible opens (the admissible
   coverings) satisfying BGR's four axioms; it induces a `Coverage` on the preorder category of
   admissible opens, hence a `GrothendieckTopology`, and a sheaf on a G-topological space *is*
   Mathlib's `Sheaf` for that topology. The sheaf condition in BGR's form — the equaliser diagram
   for every admissible covering — is the theorem `Presieve.isSheaf_coverage`, not a second
   definition. Mathlib's `Opens.grothendieckTopology` and `Opens.pretopology` are the model: a
   topological space is a G-topological space in which every open set and every open covering is
   admissible, and that embedding is a theorem of §6.1.

   The reason: the whole of Mathlib's sheaf theory — sheafification, cohomology, dense subsites,
   points — is available only for Mathlib's `Sheaf`, and a bespoke sheaf condition on
   G-topological spaces would have to reprove all of it.

9. **Rigid varieties are locally G-ringed spaces, and affinoid varieties are a full subcategory.**
   Following BGR 9.3.1, a locally G-ringed `K`-space is a G-topological space with a sheaf of
   `K`-algebras whose stalks — filtered colimits over the admissible opens containing a point — are
   local rings; a rigid variety is one satisfying the completeness conditions `(G0)`, `(G1)`, `(G2)`
   of BGR 9.1.2 with an admissible covering by affinoid varieties. The functor from affinoid
   varieties to locally G-ringed spaces is fully faithful (BGR 9.3.1/1) and respects open
   immersions (BGR 9.3.1/3). No functor-of-points or Berkovich-style definition is used, and the
   strong G-topology of an affinoid variety is the one its locally G-ringed space carries.

10. **Tate's theorem is proved once, for Laurent coverings, and once only.** The reductions from
    affinoid to rational to Laurent coverings (BGR 8.2.2) are theorems of Layer 5; the exactness of
    the two-piece Laurent sequence `0 → A → A⟨f⟩ × A⟨f⁻¹⟩ → A⟨f, f⁻¹⟩ → 0` (BGR 8.2.3) is the
    adic-spaces roadmap's Lemma 8.33 (Wedhorn), already in Tau Ceti as
    `TauCeti.ValuationSpectrum.laurentCover_exact`, transported along the identification of
    convention 6; it is not re-proved on the rigid side. ⚠ That transport is the only place where
    the affinoid algebra `A` is asked to be a strongly noetherian Tate ring; it is one (§1.2.6 and
    the adic-spaces roadmap's §0.5), and the hypothesis is discharged there, not carried through
    Layer 5.

11. **Coherence is the `𝔘`-coherence of BGR 9.4.3.** An `𝒪_X`-module on a rigid variety is coherent
    when, for some admissible affinoid covering `𝔘`, its restriction to each member is associated
    to a finite module over the member's algebra; that this holds for every admissible affinoid
    covering is Kiehl's theorem (BGR 9.4.3; Bosch 1.14/4–5), and the kernel-of-finite-type
    characterisation (Bosch 1.14/2(iii)) is a theorem. No general "coherent ringed space"
    machinery is developed.

12. **The comparison with adic spaces goes through the classical points.** For an affinoid algebra
    `A` the adic data are the Huber pair `(A, A°)` with the affinoid topology; the classical point
    of `x ∈ Sp A` is the valuation `f ↦ |f(x)|` of convention 4, a continuous rank-one valuation
    with support `x`, at most one on `A°`. Rational subdomains and rational subsets share their
    presentation `(f₁, …, fₘ, g)`, and a finite family of them covers `Sp A` exactly when it covers
    `Spa(A, A°)` (§8.2). Everything in Layer 8 is stated through these three correspondences, and
    nothing in Layers 0–7 depends on Layer 8.

13. **Names.** The algebra lives in the `Affinoid` namespace: `Affinoid.TateAlgebra K n`,
    `IsAffinoidAlgebra K A`, `Affinoid.evalNorm`, `Affinoid.supSeminorm`, `Affinoid.reduction`.
    The geometry lives in `Rigid`: `Rigid.Sp`, `Rigid.AffinoidSubdomain`, `Rigid.weierstrassDomain`,
    `Rigid.laurentDomain`, `Rigid.rationalDomain`, `Rigid.LocallyGRingedSpace`, `Rigid.IsVariety`,
    `Rigid.IsCoherent`, `Rigid.analytification`, `Rigid.toAdic`. G-topologies are `GTopology X`
    with `GTopology.Opens`, `GTopology.coverage`, `GTopology.grothendieckTopology`. Nothing from this
    roadmap is placed in the root namespace except `GTopology`.

## Existing Mathlib and Tau Ceti used by the roadmap

The roadmap uses the following Mathlib material.

- `MvPowerSeries.IsRestricted`, `MvPowerSeries.IsRestricted.subring`, `PowerSeries.IsRestricted`
  and `PowerSeries.IsRestricted.subring`; `MvPowerSeries.gaussNorm`, `MvPowerSeries.HasGaussNorm`,
  `MvPowerSeries.gaussNorm_mul_eq_mul` (multiplicativity given a dominant pair of indices),
  `PowerSeries.gaussNorm` and `Polynomial.gaussNorm`. ⚠ Mathlib has the Gauss norm as a bare
  function; the `NormedRing` instance on the subring, its completeness and the attainment of the
  norm at a dominant index are the `p`-adic-functional-analysis roadmap's §4.1 for one variable
  and Layer 0 here in general.
- `MvPowerSeries.finSuccEquiv`, the isomorphism `MvPowerSeries (Fin (n+1)) R ≃ PowerSeries
  (MvPowerSeries (Fin n) R)`, which is how `Tₙ = T_{n−1}⟨Xₙ⟩` is read (adic-spaces roadmap §0.5.5).
- The unbundled norm files `Mathlib/Analysis/Normed/Unbundled/`: `RingSeminorm`, `RingNorm`,
  `AlgebraNorm`, `MulAlgebraNorm`; `seminormFromBounded` (BGR 1.2.1/2), `smoothingSeminorm` (BGR
  1.3.2/1), `seminormFromConst` (BGR 1.3.2/2), `eq_of_powMul_faithful` (BGR 3.1.5/1),
  `Basis.norm` and the existence of power-multiplicative extensions (BGR 3.2.1/3),
  `spectralNorm`, `spectralAlgNorm`, `spectralMulAlgNorm`, `spectralNorm_unique` and
  `spectralNorm.normedField` (BGR 3.2.1/2 and 3.2.4/2). These are BGR Part A as far as it exists in
  Lean; Layer 2 cites them for the spectral norm on residue fields and for the `inf ‖fⁱ‖^{1/i}`
  construction.
- `IsUltrametricDist`, `NontriviallyNormedField`, `IsNonarchimedean`, `norm_add_le_max`;
  `NormedAlgebra`, `NormedCommRing`, `CompleteSpace`; `Ideal.Quotient.normedCommRing` (the quotient
  norm by a closed ideal, which is BGR's residue norm) and `Ideal.Quotient.normedAlgebra`;
  `UniformSpace.Completion` with its `NormedRing` instance.
- `IsTopologicallyNilpotent`; `Bornology.IsBounded` for power-boundedness of a normed-ring element
  through `Set.range (fun k ↦ f ^ k)` (coordinated with mathlib4#40013 as the adic-spaces roadmap
  does).
- `ContinuousLinearMap.isOpenMap` and `LinearMap.continuous_of_isClosed_graph` (Banach's open
  mapping and closed graph theorems over a nontrivially normed field), and
  `Mathlib/Topology/Algebra/Module/FiniteDimension.lean` (every linear map out of a
  finite-dimensional Hausdorff topological vector space over a complete field is continuous),
  which is the input to BGR 3.7.5/2 and hence to §1.3.
- `MaximalSpectrum` with `MaximalSpectrum.toPrimeSpectrum`, its Zariski topology, and
  `PrimeSpectrum.zeroLocus`, `PrimeSpectrum.vanishingIdeal`; `IsJacobsonRing`,
  `isJacobsonRing_quotient`, `MvPolynomial.isJacobsonRing` and
  `finite_of_finite_type_of_isJacobsonRing`; `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`
  (going up); `Ideal.finite_minimalPrimes_of_isNoetherianRing`; `Ideal.iInf_pow_eq_bot_of_isLocalRing`
  (Krull's intersection theorem); `Algebra.IsIntegral.finite`; `RingHom.Finite`; `Module.Flat`
  and `Module.FaithfullyFlat`. ⚠ `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical` is the
  Nullstellensatz for polynomials over an **algebraically closed** field and is not the input to
  §3.2, whose Nullstellensatz is the Jacobson property of `Tₙ` read on `Max Tₙ`.
- `Mathlib/RingTheory/NoetherNormalization.lean` (Nagata's proof for finitely generated algebras
  over a field). ⚠ It is not the affinoid theorem: Noether normalisation for `Tₙ` (BGR 6.1.2/1)
  runs on Weierstrass polynomials and the Weierstrass finiteness theorem, and §1.2 proves it. The
  shape of the two statements — a finite injective map from a polynomial, respectively Tate,
  algebra in `d` variables — is aligned deliberately.
- `IsIntegralClosure.finite` and `IsIntegralClosure.isNoetherianRing`: finiteness of the integral
  closure in a finite **separable** extension of the fraction field of an integrally closed
  noetherian domain. ⚠ The Japanese property of `Tₙ` (BGR 5.3.1/3) is stated for all finite
  extensions, inseparable ones included, and is proved in §0.4 through weak stability; Mathlib's
  theorem covers the separable case only.
- Sites and sheaves: `CategoryTheory.GrothendieckTopology`, `Pretopology`, `Coverage` with
  `Coverage.toGrothendieck` and `Presieve.isSheaf_coverage`, `Sheaf`, `Presheaf.IsSheaf`,
  `Opens.grothendieckTopology` and `Opens.pretopology` (the topological-space model),
  `Functor.IsCoverDense`, `Functor.IsDenseSubsite` and the resulting equivalence of sheaf
  categories, `HasSheafify` and `presheafToSheaf`, `GrothendieckTopology.Point` with its fibre
  functors, and `CategoryTheory.cechComplexFunctor` (the Čech complex of a presheaf with values in
  a preadditive category with products, for a family of objects in a category with finite
  products). ⚠ Mathlib's `Sheaf.H` defines sheaf cohomology on a site as `Ext` from the constant
  sheaf, with functoriality and a Mayer–Vietoris sequence, but **no** comparison with Čech
  cohomology; §7.4 builds that comparison. ⚠ There is no Čech cohomology of a presheaf on a
  G-topological *space* and no stalk for a site of subsets; §6.1 and §6.3 build them on top of the
  site vocabulary.
- `CategoryTheory.GlueData`, `TopCat.GlueData` and `AlgebraicGeometry.Scheme.GlueData`, which are the
  models for the pasting of G-topological spaces and of rigid varieties; `SheafedSpace` and
  `LocallyRingedSpace`, which are the models for locally G-ringed spaces but are **not** reused:
  their underlying object is a topological space.
- `AlgebraicGeometry.Scheme`, `Spec`, `ΓSpec.adjunction`, `LocallyOfFiniteType`, `IsSeparated`,
  `IsProper`, `IsFinite`, `IsClosedImmersion` and `Scheme.OpenCover`, consumed by §8.1.
- `PadicComplex` (`ℂ_[p]`) with `IsAlgClosed` and `IsUltrametricDist`, `Valuation`,
  `ValuativeRel` and `Valuation.Compatible`, consumed by the acceptance examples and by Layer 8.

The roadmap uses the following Tau Ceti material, all of it the adic-spaces roadmap's. ⚠ It is
cited by that roadmap's section numbers, so that the dependency is on the specification; the
declaration names below are the ones at the pin recorded in *Existing Lean work* and may move.

- Huber rings, Tate rings and pairs: `TauCeti.Huber.PairOfDefinition`, `IsHuberRing`, `IsTateRing`,
  `IsPseudoUniformizer`, `IsBounded`, `IsPowerBounded`, `powerBoundedSubring`,
  `topologicallyNilpotentIdeal`, `IsRingOfIntegralElements`, `Pair`, `Pair.Hom`, `IsUniform`,
  `IsStablyUniform`, `isPowerBounded_iff_norm_le_one` and `IsUniform.of_normedDivisionRing` (adic
  §0.1–0.2).
- Restricted power series as topological rings: `restrictedMvPowerSeriesSubring`,
  `restrictedMvPowerSeriesCompletion`, `restrictedMvPowerSeriesCompletionOneEquiv` (the one-variable
  Huber model is Mathlib's restricted series), `IsStronglyNoetherian`, `IsTopologicallyFiniteType`,
  `flat_restrictedMvPowerSeriesSubring`, `faithfullyFlat_restrictedMvPowerSeriesSubring`, and the
  one-variable Weierstrass theory `TauCeti.PowerSeries.IsDistinguished`, `gaussValuation`,
  `IsDistinguished.existsUnique_mul_add_eq`, `IsDistinguished.existsUnique_isUnit_isMonicOfDegree_mul_eq`,
  `isPrincipalIdealRing_isRestricted_subring`, `isNoetherianRing_isRestricted_subring`,
  `exists_isMonicOfDegree_span_singleton_eq`, `isUnit_iff_isDistinguished_zero` (adic §0.5).
- Rational localisation and its presentations: `TauCeti.Huber.PairOfDefinition.toCompletionLoc`,
  `rationalQuotientRingEquiv`, `laurentQuotientRingEquiv`, `completedPlusSubring` (adic §3.1), and
  `LinearMap.isStrictMap_of_module_finite`, `TauCeti.HasZeroSequenceOfUnits.isOpenMap` (adic §0.6).
- Adic spectra: `TauCeti.ValuationSpectrum.spa`, `rationalSubset`, `spaRationalFamily`,
  `isBasis_spaRationalOpens`, `spaComap`, `spaComapLoc`, `spaCompletedLocalizationHomeomorph`,
  `closedPolydisc`, `evalAtHom`, `classicalPoint`, `gaussPoint`, `closedDiscGaussValuation`,
  `IsAnalyticPoint`, `cont`, `IsContinuous`, the `SpectralSpace` instance on `spa`,
  `span_eq_top_iff_spa_eq_biUnion_rationalSubset` (Wedhorn 7.53),
  `exists_span_eq_top_forall_rationalSubset_subset_of_isTateRing` (Wedhorn 7.54),
  `isUnit_iff_forall_mem_spa_notMem_supp` (Wedhorn 7.52), `existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset`
  (Wedhorn 8.1), `presentationLimitPresheaf`, `rationalSubsetLimitPresheaf`,
  `isSheaf_iff_isSheafFor_rationalCover`, `faithfullyFlat_pi_toCompletionLoc` (Wedhorn 8.32),
  `laurentCover_injective`, `laurentCover_exact`, `laurentCover_surjective` (Wedhorn 8.33),
  `TauCeti.Huber.IsSheafyRing`, `IsStablySheafyRing`, `TauCeti.PreAdicSpace`,
  `TauCeti.AffinoidPreAdicSpace` (adic §§2–4).
- `TauCeti.TopCommRingCat.isSheaf_of_isSheaf_forget` and the complete-separated subcategory
  `TauCeti.TopCommRingCat.IsCompleteSeparated` (adic §3.2), `TauCeti.IsProConstructible` (adic §1.3).

⚠ Mathlib has **no** affinoid algebra, no supremum seminorm, no maximal-spectrum-valued points with
norms, no G-topology, no rigid analytic variety, no Gerritzen–Grauert theorem, no Tate acyclicity
in the classical form, no Kiehl theorem, and no analytification functor. Tau Ceti has none of these
either: its `AlgebraicGeometry/AdicSpace/` is Huber's theory, whose affinoid objects are Huber
pairs, and its only classical-geometry objects are the closed polydisc with its classical points
and Gauss points (`closedPolydisc`, `classicalPoint`, `gaussPoint`). This roadmap is where the
classical theory is built.

---

## Layer 0: the Tate algebras beyond the adic-spaces roadmap

References: BGR 5.1, 5.2.3–5.2.4, 5.2.6–5.2.7, 5.3.1, 3.5, 3.8; Bosch 1.2–1.3.

`Tₙ` is Mathlib's subring of restricted power series at the unit polyradius (convention 2). The
floor is the adic-spaces roadmap's §0.5 and mathlib4#42867: the ring structure and the Gauss-norm
`NormedCommRing`, its completeness, the iteration isomorphism `Tₙ ≅ T_{n−1}⟨Xₙ⟩` (through
`MvPowerSeries.finSuccEquiv`), the criterion for units, and Weierstrass division and preparation by
an `Xₙ`-distinguished series (BGR 5.2.1/2, 5.2.2/1). The `p`-adic-functional-analysis roadmap's
§4.1 supplies the one-variable Banach structure, and the Newton-polygons roadmap's §§2–3 the
Gauss-norm dictionary at every radius in one variable. This layer is everything else BGR's Chapter
5 asks of `Tₙ` that the later layers consume — **including** the substitution and evaluation
homomorphisms (§0.1.3) and the noetherianity of `Tₙ` (§0.3.2), which it proves itself.

**Status (2026-10-02).** Layer 0 is implemented in this repository in
`PhD/TauCeti/Code/RigidAnalyticGeometry/` (with `PadicFunctionalAnalysis/Orthonormal.lean`), from the
ticket board `.mathlib-quality/tauceti-rag-layer0/`: every declaration is proved, `lake build
PhD.TauCeti` passes, and the milestone theorems (`supSeminorm_eq_norm`; the `IsNoetherianRing`,
`UniqueFactorizationMonoid` and `IsJacobsonRing` instances and `ringKrullDim_eq`; `isClosed_ideal`,
`exists_forall_norm_sub_le_ideal`, `norm_quotient_mk_mem_range_norm`; `isWeaklyStable_fractionRing`,
`isJapaneseRing`) depend only on `propext`, `Classical.choice` and `Quot.sound`. The floor
(mathlib4#42867) is a copy of the user's `PhD/Main/ForMathlib` development in `Restricted/`, not an
import. §0.4 is done in characteristic zero only; the characteristic-`p` case (BGR 5.3.1/2 with
b-separable modules) is not on that board.

### 0.1 The Gauss norm, the reduction, and the maximum modulus principle on `Tₙ`

1. The Gauss norm `|f| = max_ν |a_ν|` is a complete, multiplicative, nonarchimedean `K`-algebra norm
   on `Tₙ` with `|Tₙ| = |K|` and `|Tₙ ∖ {0}| ⊆ |K^×|` (BGR 5.1.1–5.1.2); `K[X₁, …, Xₙ]` is dense.
   Multiplicativity is Mathlib's `MvPowerSeries.gaussNorm_mul_eq_mul` once a dominant pair of
   indices is produced, and the existence of that pair is the attainment theorem: for `f ≠ 0`
   there is a largest index in the lexicographic order at which `|a_ν|` attains `|f|`.
2. Define the power-bounded subring `T̊ₙ = {|f| ≤ 1}` and the ideal `Ťₙ = {|f| < 1}` of it, and
   prove that they are the power-bounded and the topologically nilpotent elements of `Tₙ` in the
   sense of mathlib4#40013 (coefficientwise criteria). Construct the reduction `T̊ₙ → K̃[X₁, …, Xₙ]`,
   coefficientwise reduction to the residue field `K̃`, prove it is a surjective ring homomorphism
   with kernel `Ťₙ`, so that `T̃ₙ := T̊ₙ/Ťₙ ≅ K̃[X₁, …, Xₙ]` (BGR 5.1.2), and prove the going-up and
   -down statements of BGR 5.1.3: a unit of `T̊ₙ` reduces to a unit, an element of `T̊ₙ` whose
   reduction is a unit is a unit, and an element of `T̊ₙ` whose reduction is nonzero has Gauss norm
   one.
3. **Evaluation and maximum modulus for `Tₙ`** (BGR 5.1.3/5, 5.1.4). For a complete nonarchimedean
   Banach `K`-algebra `B` and a tuple of its unit ball, construct the evaluation homomorphism
   `Tₙ → B`, `f ↦ f(x)`: a contractive `K`-algebra homomorphism, the unique continuous one with the
   given values on the variables; `B` a complete extension field gives evaluation at a point, `B` a
   Tate algebra gives the substitution homomorphisms. Prove that evaluation commutes with the
   reduction (the commutative square of BGR 5.1.4). Then, for every `f ∈ Tₙ`, there is a maximal
   ideal `x ∈ Max Tₙ` with `|f(x)| = |f|`, where `|f(x)|` is the spectral norm of the residue class
   of `f` in `Tₙ ⧸ x` (convention 4), and with `Tₙ ⧸ x` finite over `K` — the point is constructed
   with a finite residue field, so nothing from Layer 1 is needed. Prove it by reduction: scale `f`
   to Gauss norm one; its reduction is a nonzero polynomial of degree less than `m` in each
   variable, for some `m` with `|m| = 1`; the `m`-th roots of unity in the splitting field `K'` of
   `X^m − 1` have norm one and pairwise differences of norm one, so they give `m` residue classes,
   and the reduced polynomial does not vanish at some point with coordinates among them
   (combinatorial Nullstellensatz); evaluate there. This is BGR's proof with Lemma 3.4.1/4 (the
   residue field of `K_a`) replaced by its content for the one polynomial `X^m − 1`, as BGR's
   remark after 5.1.4/3 permits. ⚠ The residue field `K̃` may be finite, so the point is in general
   not `K`-rational: the extension is unavoidable and is why convention 4 measures points by
   residue fields.
4. Prove `|f(x)| ≤ ‖f‖` for every maximal ideal of a Banach `K`-algebra (BGR 3.8.2/1–2; the unit
   argument of Bosch 1.2/12 proves it without residue norms), and deduce that the Gauss norm is
   the supremum norm: `|f| = sup_{x ∈ Max Tₙ} |f(x)|`, that `Tₙ` is a
   Banach function algebra in the sense of BGR 3.8.3, and that the set of `x` with `|f(x)| = |f|` is
   nonempty and Zariski-dense when `f ≠ 0`. Prove that `Tₙ` is an integral domain (from
   multiplicativity).

### 0.2 Weierstrass polynomials, the finiteness theorem, and distinguished charts

1. Define Weierstrass polynomials (BGR 5.2.3/1): `ω ∈ T_{n−1}[Xₙ]` monic of Gauss norm one,
   equivalently monic with all coefficients of Gauss norm `≤ 1`. ⚠ Not "non-leading coefficients
   of norm `< 1`": `Xₙ − 1` is `Xₙ`-distinguished of order one and is its own Weierstrass
   polynomial. Prove that monic factors of a Weierstrass polynomial are Weierstrass polynomials
   (BGR 5.2.3/2), that `ω` of degree `s` is `Xₙ`-distinguished of order `s` as a series, and
   that an `Xₙ`-distinguished series of order `s` is a unit times a Weierstrass polynomial of
   degree `s`, the Weierstrass polynomial being unique (BGR 5.2.2/1, from the floor's preparation
   theorem, restated here on Weierstrass polynomials).
2. **Weierstrass finiteness theorem** (BGR 5.2.3/4). For `ω` a Weierstrass polynomial of degree `s`,
   `Tₙ ⧸ (ω)` is a free `T_{n−1}`-module with basis `1, Xₙ, …, Xₙ^{s−1}`, and for `f`
   `Xₙ`-distinguished of order `s` the inclusion `T_{n−1} → Tₙ ⧸ (f)` is finite. Prove it from
   Weierstrass division. State the module version: for a finite `Tₙ`-module `M` killed by `ω`,
   `M` is a finite `T_{n−1}`-module.
3. **Distinguished charts** (BGR 5.2.4; Bosch 1.2/7). For `f ∈ Tₙ ∖ {0}` there is a `K`-algebra
   automorphism `σ` of `Tₙ`, `Xᵢ ↦ Xᵢ + Xₙ^{αᵢ}` for `i < n` and `Xₙ ↦ Xₙ`, with `σ(f)`
   `Xₙ`-distinguished of some order `s`. Construct `σ` as a continuous automorphism from the
   evaluation homomorphisms of §0.1.3, with inverse `Xᵢ ↦ Xᵢ − Xₙ^{αᵢ}`; it is an isometry
   because it and its inverse are contractive. Prove that
   `α = (tⁿ⁻¹, …, t)` works as soon as `t` exceeds every exponent occurring in a monomial of `f` of
   maximal Gauss norm, and that one `σ` works for finitely many series at once (Bosch 1.2/7). The
   polynomial statement behind it — over a field, this shear makes the leading coefficient of a
   nonzero polynomial in the distinguished variable a unit — is proved first, on the reduction. The
   relative form of Bosch 1.8/13, over an affinoid base, needs affinoid algebras and `Sp A` and is
   stated in §4.6, where it is consumed.

### 0.3 Ideals of `Tₙ`: Rückert's applications

1. Every ideal of `Tₙ` is closed and **strictly closed** (BGR 5.2.7/2, 5.2.7/8; Bosch 1.3/7–9): for
   `𝔞 ⊆ Tₙ` and `f ∈ Tₙ` the distance `inf_{a ∈ 𝔞} |f − a|` is attained, `𝔞` has generators of norm
   one in which every `f ∈ 𝔞` has coefficients of norm `≤ |f|`, and the residue norm of `Tₙ ⧸ 𝔞`
   takes values in `|K|`. Prove them together by Bosch's route: bald subrings of the unit ball of
   `K` (Bosch 1.3/2–3: the subring generated by a zero sequence is bald), the lifting of
   orthonormal bases from the reduction (Bosch 1.3/6), and an orthonormal basis of `Tₙ` adapted to
   the ideal. ⚠ BGR's own proof of 5.2.7/7 is an induction through cartesian modules over `Q(Tₙ)`
   (Part A, Chapter 2) and is not the route; and closedness is not available by citation from the
   adic-spaces or functional-analysis roadmaps without their code.
2. `Tₙ` is a unique factorisation domain and integrally closed in its fraction field
   (BGR 5.2.6/2), by induction on `n` through the finiteness theorem and distinguished charts.
   Organise items 2–4 through BGR's abstract Rückert overrings (5.2.5/1–4): `Tₙ` is Rückert over
   `T_{n−1}` for the family of Weierstrass polynomials, and a Rückert overring inherits
   noetherianity, factoriality and (given a vanishing Jacobson radical, BGR 5.1.3/3) the Jacobson
   property. This proves the noetherianity of `Tₙ` (BGR 5.2.6/1) as well.
3. `Tₙ` is a Jacobson ring (BGR 5.2.6/3; Bosch 1.2/15): every prime ideal is an intersection of
   maximal ideals. ⚠ This is the Nullstellensatz of §3.2 in algebraic clothing and is the reason
   the Nullstellensatz for affinoid algebras does not need an algebraically closed field.
4. The Krull dimension of `Tₙ` is `n` (BGR 6.1.2, Remark): `dim Tₙ ≥ n` from the chain
   `0 ⊂ (X₁) ⊂ … ⊂ (X₁, …, Xₙ)`, and `≤ n` by integral descent: a prime that is not minimal
   contains, after an automorphism, a Weierstrass polynomial `ω`, and `Tₙ ⧸ (ω)` is finite over
   `T_{n−1}` (Bosch 1.2/10; an integral map does not raise the dimension). ⚠ BGR's argument for
   `≤ n` uses 7.1.1/3, which is §3.1 and rests on Noether normalisation; it is not needed.
5. Finite `Tₙ`-modules (BGR 5.2.7): prove that a submodule `N` of a finite free module `Tₙˢ` with
   the maximum norm is closed and strictly closed, with generators of norm one in which every
   `x ∈ N` has coefficients of norm `≤ |x|` (Bosch 1.3/10; BGR 5.2.7/1 with the bound `ρ = 1`, and
   5.2.7/7), so that the residue norm of a finite module presented as `Tₙˢ ⧸ N` takes values in
   `|K|`. Item 1 is the case `s = 1`. The unique complete topology of a finite module and the
   continuity of linear maps are the `p`-adic-functional-analysis roadmap's §1.4 and are cited
   where a later layer needs them.

### 0.4 Weak stability of `Q(Tₙ)` and the Japanese property

This is the deepest Part A dependency of the roadmap, and it is consumed by exactly two results:
§1.2.5 (affinoid domains are Japanese) and §2.4.1 (reduced affinoid algebras are Banach function
algebras). Both are needed by Layer 8 (uniformity of reduced affinoid algebras) and the first by
§7.1 (finite morphisms), so neither can be left out.

1. Define weakly stable valued fields (BGR 3.5.2/1): `K` is weakly stable when every finite
   extension `L`, with its spectral norm, is weakly `K`-cartesian, that is (BGR 2.3.1/3, 2.3.2/1)
   every `K`-linear functional on `L` is bounded for the spectral norm. Prove that perfect fields
   and complete fields are weakly stable (BGR 3.5.1/3–4, 3.5.2), the first through the trace being
   a contraction for the spectral norm (BGR 3.2.3/2) and the criterion "bounded functionals that
   separate points are all functionals" (BGR 2.3.1/2). Define Japanese rings (BGR 4.3/1) and prove
   Dedekind's criterion: a noetherian integrally closed domain with perfect fraction field is
   Japanese (BGR 4.2/1, 4.3/2). These settle characteristic zero. In characteristic `p` the route,
   checked against the source, is BGR 5.3.1/2 with 3.5.3/1–2 (weak stability through `K^{p⁻¹}`),
   4.1/3–4 (tame modules) and 4.4/2 (the third criterion for Japaneseness), and it consumes Part
   A's b-separable modules (2.2.5–2.2.6) and spaces of countable type (2.6–2.7.1). ⚠ BGR 3.5.4/1
   is about discrete valuation rings and is not what 5.3.1 uses.
2. **`Q(Tₙ)` is weakly stable** for the multiplicative extension of the Gauss norm (BGR 5.3.1/1):
   immediate from item 1 in characteristic zero; in characteristic `p` by BGR 5.3.1/2
   (`Tₙ^{p⁻¹} = K^{p⁻¹}⟨Y⟩`, and every `Tₙ`-submodule of finite rank in it is b-separable).
3. **`Tₙ` is Japanese** (BGR 5.3.1/3): for every finite extension `L` of `Q(Tₙ)` the integral
   closure of `Tₙ` in `L` is a finite `Tₙ`-module. Separable extensions are Mathlib's
   `IsIntegralClosure.finite` given §0.3.2; the inseparable case is the content and comes from
   §0.4.1–0.4.2. Record the counterexample that motivates the hypothesis: a nonarchimedean field
   that is not weakly stable has a Tate algebra that is not Japanese is **not** claimed; only the
   positive statement is in scope.

### Examples

`T₀ = K`; `T₁` with `|X|` and the Gauss norm of `1 + pX` over `ℚ_p`; the reduction of
`p + X + pX²` is `X`; the variable `X₁` of `T₂`, which is `X₂`-distinguished of no order, and the
automorphism `X₁ ↦ X₁ + X₂` making it `X₂`-distinguished of order one; the
Weierstrass polynomial `X₂² − pX₁X₂ − p` over `T₁ = ℚ_p⟨X₁⟩` with `T₂/(ω)` free of rank `2`;
the maximal ideal of a `K`-rational point of the unit ball (its generators `Xᵢ − aᵢ` are §3.1) and
a maximal ideal of `T₁` whose residue field is a quadratic extension, `(X² − p)` over `ℚ_p`.

### Dependencies

Mathlib; the floor of convention 2 (the adic-spaces roadmap §0.5, or mathlib4#42867); the
`p`-adic-functional-analysis roadmap §0.2 (unit balls, power-bounded elements) and §2.2
(orthonormal families and bases, for §0.3.1); the Newton-polygons roadmap §§2.3 and 3.1 for the
one-variable Gauss norm at every radius. The characteristic-`p` half of §0.4 additionally needs
the `p`-adic-functional-analysis roadmap's §2.2 and §2.4 (orthogonal bases over fields, spaces of
countable type) and is planned separately.

---

## Layer 1: affinoid algebras

References: BGR 6.1; Bosch 1.4.

**Status (2026-10-06).** Layer 1 is implemented in this repository in
`PhD/TauCeti/Code/RigidAnalyticGeometry/` (`NormedQuotient.lean`, `Restricted/Sum.lean`,
`Affinoid/*.lean`, `BanachAlgebra/*.lean`; `Restricted/Algebra.lean`, `TateAlgebra/Eval.lean` and
`PadicFunctionalAnalysis/PowerBounded.lean` were generalised in place), from the ticket board
`.mathlib-quality/tauceti-rag-layer1/`: every declaration is proved, `lake build PhD.TauCeti` passes,
and the milestone theorems (Noether normalisation `IsAffinoidAlgebra.exists_finite_injective`, the
continuity theorem `AlgHom.continuous_of_isAffinoidAlgebra`, the tensor-product universal property
`Affinoid.isAffinoidTensorProduct_tensorQuotient`, and the fraction universal properties
`Affinoid.isGeneralisedFractions_toFractions` and `Affinoid.isRationalFractions_toRational`) depend only
on `propext`, `Classical.choice` and `Quot.sound`. The plan's deviations (V1–V7) and errata (E1–E6)
are recorded in `plan.md`, not applied here: §1.4.2's completion model, §1.4.3–1.4.4, the "only if"
of §1.5.2 and characteristic-`p` Japaneseness are not on that board. Hypotheses dropped by the
skeleton (section variables, and `[CompleteSpace K]` for the open-disc example of §1.5) were restored
in place during the run and are logged in the board's `b2_log.jsonl`.

### 1.1 The category of affinoid algebras

1. Define `IsAffinoidAlgebra K A` (convention 3) and the affinoid topology on `A` as the quotient
   topology of a presentation `α : Tₙ ↠ A`. Define a residue norm as the quotient norm of a
   presentation, which is Mathlib's `Ideal.Quotient.normedCommRing` for the closed ideal `ker α`
   (§0.3.1); prove it is a complete `K`-algebra norm taking values in `|K|` (BGR 6.1.1, with
   strict closedness).
2. Prove that affinoid algebras are noetherian (from §0.3 and the adic-spaces roadmap), Jacobson
   (BGR 5.2.6/3 and `isJacobsonRing_quotient`), and that quotients of affinoid algebras by ideals
   are affinoid (BGR 6.1.1): the affinoid topology of `A ⧸ 𝔞` is the quotient topology.
3. **The universal property of `A⟨X₁, …, Xₘ⟩`** (BGR 6.1.1/4; Bosch 1.4/18). Define
   `A⟨X₁, …, Xₘ⟩` for a `K`-Banach algebra `A` as the restricted series over `A` at the unit
   polyradius (Mathlib's subring over the normed ring `A`) and prove: for `A` affinoid,
   `A⟨X₁, …, Xₘ⟩ ≅ (A ⊗̂_K Tₘ)` is affinoid, `A⟨X⟩⟨Y⟩ ≅ A⟨X, Y⟩`; and for a continuous
   homomorphism `φ : A → B` into a `K`-Banach algebra and power-bounded `b₁, …, bₘ ∈ B` there is a
   unique continuous `A`-algebra homomorphism `A⟨X⟩ → B` with `Xᵢ ↦ bᵢ`. Define affinoid
   generating systems of `B` over `A` (BGR 7.2.5; Bosch 1.8/7) and prove that `B` is affinoid over
   `K` exactly when it has one over `K`.
4. Prove that a `K`-algebra homomorphism between affinoid algebras is uniquely determined by its
   values on an affinoid generating system (BGR 6.1.1/4), and that the category of affinoid
   algebras has all finite colimits of the following kinds, with their universal properties:
   quotients, and the affinoid tensor product of item 5.
5. **The affinoid tensor product** (BGR 6.1.1/10–11). For affinoid `A`-algebras `B₁ = A⟨X⟩/𝔟₁` and
   `B₂ = A⟨Y⟩/𝔟₂`, define `B₁ ⊗̂_A B₂ := A⟨X, Y⟩/(𝔟₁, 𝔟₂)` and prove it is affinoid, independent
   of the presentations up to canonical isomorphism, and the pushout of `B₁ ← A → B₂` in the
   category of affinoid algebras; prove that `B₁ ⊗̂_A B₂` receives the algebraic tensor product
   `B₁ ⊗_A B₂` with dense image, and that if `A → B₁` is surjective so is `B₂ → B₁ ⊗̂_A B₂`
   (BGR 6.1.1/11). ⚠ This is a construction by presentations, and the only completed tensor
   product in the roadmap; the universal property among all `K`-Banach algebras is not claimed.
6. Extension of the ground field: for a finite extension `K'/K` with its spectral norm,
   `A ⊗̂_K K' := A ⊗_K K'` (already complete) is a `K'`-affinoid algebra and `Tₙ(K) ⊗_K K' = Tₙ(K')`
   (BGR 6.1.1; the complete case for an arbitrary complete extension is §6.6).

### 1.2 Noether normalisation and its consequences

1. **Noether normalisation** (BGR 6.1.2/1–2; Bosch 1.2/10 and 1.4/2). For a surjection
   `α : Tₙ ↠ A` with `A ≠ 0` there is a `K`-algebra map `Td → Tₙ`, `d ≤ n`, such that the composite
   `Td → A` is finite and injective; in particular every nonzero affinoid algebra is a finite
   extension of some `Td`. Prove it by induction on `n` through a distinguished chart (§0.2.3) and
   the Weierstrass finiteness theorem (§0.2.2), exactly as BGR does.
2. Finite homomorphisms: for `φ : B → A` finite and `A` an integral domain, `A` is torsion-free
   over `B/ker φ` (used in §2.2); the composite of finite maps is finite; `Tₙ ↠ A` makes `A` a
   finite `Td`-module for the `d` of item 1.
3. The integer `d` is the Krull dimension of `A` (BGR 6.1.2, Remark): `dim A = dim Td = d`.
4. **Residue fields are finite** (BGR 6.1.2/3; Bosch 1.2/11 and 1.4/3): for an ideal `𝔮` of `A`
   whose radical is maximal, `A ⧸ 𝔮` is a finite-dimensional `K`-vector space. In particular every
   maximal ideal of `A` has residue field a finite extension of `K`, and the preimage of a maximal
   ideal under a `K`-algebra map of affinoid algebras is maximal. ⚠ This is what makes
   `MaximalSpectrum` functorial on affinoid algebras (§3.3); Mathlib's `finite_of_finite_type_of_isJacobsonRing`
   does the same for finitely generated algebras and is not applicable to `A`.
5. Affinoid domains are Japanese (BGR 6.1.2/4), from §0.4.3 and item 1.

### 1.3 Continuity of homomorphisms and uniqueness of the topology

1. Prove the two inputs to BGR 3.7.5/2 for an affinoid algebra `B`: for every maximal ideal `𝔪`
   and every `ν`, `B ⧸ 𝔪^ν` is finite-dimensional over `K` (§1.2.4), and the intersection of all
   `𝔪^ν` is zero (Krull's intersection theorem in the localisations, Mathlib's
   `Ideal.iInf_pow_eq_bot_of_isLocalRing`, together with the Jacobson property).
2. **Every `K`-algebra homomorphism from a noetherian `K`-Banach algebra into an affinoid algebra
   is continuous** (BGR 6.1.3/1), hence every homomorphism between affinoid algebras is continuous
   for any residue norms (Bosch 1.4/19). Prove it along Bosch 1.4/18: the map is continuous into
   each finite-dimensional `B ⧸ 𝔪^ν` by Mathlib's finite-dimensional continuity theorem, and the
   `𝔪^ν` separate `B`. ⚠ The general BGR 3.7.5/2 is stated for a noetherian Banach algebra as
   source; the version needed in this roadmap only ever has an affinoid source, and the general
   statement is proved as stated so that the `p`-adic-functional-analysis roadmap's Banach algebras
   can use it.
3. **Uniqueness of the Banach topology** (BGR 6.1.3/2): every `K`-Banach algebra topology on an
   affinoid algebra is the affinoid topology, so any two complete `K`-algebra norms on `A` are
   equivalent (`∃ C, ‖·‖₁ ≤ C ‖·‖₂` and conversely). Deduce that an affinoid algebra has a unique
   structure of Banach `K`-algebra up to equivalence of norms, and that the notions of
   power-bounded, topologically nilpotent, bounded and closed are the same for all residue norms.
4. Contractive renorming (BGR 6.1.3/3): for `φ : B → A` between affinoid algebras the norm on `A`
   can be replaced by an equivalent one for which `φ` is contractive, making `A` a normed
   `B`-algebra; the proof uses an affinoid generating system over `B` and the Gauss norm of
   `B⟨X⟩`.

### 1.4 Generalised rings of fractions

1. For `f₁, …, fₘ, g₁, …, gₙ ∈ A` define `A⟨f, g⁻¹⟩ := A⟨X, Y⟩/(Xᵢ − fᵢ, gⱼYⱼ − 1)` and prove the
   universal property of BGR 6.1.4/1: for a continuous `K`-algebra map `φ : A → B` into a `K`-Banach
   algebra with each `φ(gⱼ)` a unit and each `φ(fᵢ)`, `φ(gⱼ)⁻¹` power-bounded, there is a unique
   continuous factorisation through `A⟨f, g⁻¹⟩`. Prove associativity
   `A⟨f, g⁻¹⟩⟨f', g'⁻¹⟩ ≅ A⟨f, f', g⁻¹, g'⁻¹⟩` (BGR 6.1.4/2) and that `A⟨h⁻¹⟩` for a unit `h` agrees
   with `A⟨h⁻¹⟩` as a generalised fraction.
2. For `f₁, …, fₘ, g ∈ A` generating the unit ideal, define `A⟨f/g⟩ := A⟨X⟩/(gXᵢ − fᵢ)` and prove
   the universal property of BGR 6.1.4/3: `g` becomes a unit, the `fᵢ/g` are power-bounded, and
   every continuous `φ : A → B` with `φ(g)` a unit and `φ(fᵢ)/φ(g)` power-bounded factors uniquely.
   Prove that the natural map `A[g⁻¹] → A⟨f/g⟩` has dense image and that `A⟨f/g⟩` is the
   completion of `A[g⁻¹]` for the seminorm `|b| = inf max |b_ν|` over representations
   `b = ∑ b_ν (f/g)^ν` (BGR 6.1.4, the description preceding 6.1.4/3), so that the two models of
   BGR 6.1.4/4 are isometric.
3. **Identification with the adic-spaces roadmap.** Prove that `A⟨f/g⟩` is the adic-spaces
   roadmap's completed rational localisation `A⟨T/s⟩` for `T = {f₁, …, fₘ, g}` and `s = g`, as
   topological `A`-algebras, and that the universal properties correspond (Tau Ceti:
   `rationalQuotientRingEquiv`); likewise `A⟨f, g⁻¹⟩` for `T = {f₁, …, fₘ, 1}` and
   `s = ∏ gⱼ` after the change of presentation of BGR 7.2.4/1. This is convention 6's theorem.
4. Prove that `A → A⟨f/g⟩` and `A → A⟨f, g⁻¹⟩` are flat (BGR 7.3.2; Bosch 1.7/5, in the form
   proved by the adic-spaces roadmap's §4.1 step 3 for strongly noetherian Tate rings; cite and
   transport along item 3).

### 1.5 Convergent power series on polydiscs of arbitrary polyradius

1. For `ρ ∈ (0, ∞)ⁿ` define `T_{n,ρ}` as Mathlib's `MvPowerSeries.IsRestricted.subring ρ` with the
   Gauss norm `|f|_ρ = max |a_ν| ρ^ν`, and prove it is a `K`-Banach algebra containing `K[X]` as a
   dense subalgebra and that `|·|_ρ` is multiplicative (BGR 6.1.5/1–2). The Newton-polygons
   roadmap's §2.3 and the `p`-adic-functional-analysis roadmap's §4.1 own the one-variable case;
   this item is the several-variable statement.
2. Prove that `T_{n,ρ}` is affinoid when every `ρᵢ` lies in `√|K^×|`: choose `r` and `cᵢ ∈ K` with
   `ρᵢ^r = |cᵢ|` and `cᵢ' ∈ K` with `|cᵢ'| ≥ ρᵢ`; rescaling `Xᵢ = cᵢ' Zᵢ` identifies `T_{n,ρ}` with
   the Weierstrass domain algebra `Tₙ⟨(cᵢ'^r cᵢ⁻¹) Zᵢ^r⟩` of the unit polydisc (§1.4.1 and BGR
   7.2.3), and `|·|_ρ` is then the supremum norm (BGR 6.1.5/5). ⚠ For `ρᵢ ∉ √|K^×|` the algebra
   `T_{n,ρ}` is **not** affinoid and is not a `K`-affinoid algebra of any kind (BGR 6.1.5, the
   remark after 6.1.5/5); record the example of a series convergent on the open disc of radius `ρ`
   but not in `T_{1,ρ}` (BGR 6.1.5).

### Examples

`K⟨X⟩/(X² − p)` and `K⟨X⟩/(X − a)` for `|a| ≤ 1`; `K⟨X⟩/(pX − 1) = 0`; `A⟨f⟩` for `f = X` in
`A = K⟨X⟩` is `A` itself; `K⟨X, Y⟩/(XY − 1) = K⟨X, X⁻¹⟩`; Noether normalisation of
`K⟨X, Y⟩/(Y² − X³)` by `T₁ = K⟨X⟩`; the two presentations `K⟨X⟩ ⧸ (X)` and `K` of the same
affinoid algebra, with their residue norms equal; `ℚ_p⟨X⟩ ⊗_{ℚ_p} ℚ_p(√p) = ℚ_p(√p)⟨X⟩`.

### Dependencies

Layer 0; the adic-spaces roadmap §0.5 and §§3.1, 4.1; the `p`-adic-functional-analysis roadmap §1.4.

---

## Layer 2: the supremum seminorm and the reduction

References: BGR 3.8, 6.2, 6.3.1; Bosch 1.4.

**Status (2026-10-06).** Layer 2 is implemented in this repository in
`PhD/TauCeti/Code/RigidAnalyticGeometry/` (`SupSeminorm/{Seminorm, SpectralValue, Integral, Banach,
FunctionAlgebra}.lean`, `BanachAlgebra/Module.lean`, `Affinoid/{SupSeminorm, PowerBounded, Reduction,
FunctionAlgebra, ReductionFunctor, SupExamples}.lean`; the Layer 0 file `SupSeminorm.lean` gained
`isUnit_aeval_of_norm_lt_spectralValue`, `evalNorm_map_le_norm` and `supSeminorm_map_le_norm`), from the
ticket board `.mathlib-quality/tauceti-rag-layer2/`: every declaration is proved, `lake build PhD.TauCeti`
passes with the chain root importing `Affinoid.SupExamples`, and the milestone theorems
(`Affinoid.supSeminorm_eq_supSpectralValue_minpoly` for BGR 3.8.1/7 (a), the maximum modulus principle
`IsAffinoidAlgebra.exists_evalNorm_eq_supSeminorm`, `IsAffinoidAlgebra.isPowerBounded_iff_supSeminorm_le_one`
with the spectral radius formula `IsAffinoidAlgebra.supSeminorm_eq_smoothingFun`,
`IsAffinoidAlgebra.isBanachFunctionAlgebra_of_isReduced` for BGR 6.2.4/1, and
`IsAffinoidAlgebra.isStrictMap_of_isometry` for BGR 6.3.1/6) depend only on `propext`,
`Classical.choice` and `Quot.sound`. The plan's deviations (`plan.md` §8, D1–D12) are recorded there,
not applied here: BGR 3.8.3/7 and 3.8.1/7 are stated for `A` a domain; §2.4.1 and its consequences carry
`[CharZero K]`; "`|·|_sup` is a complete norm" is the norm inequality `‖f‖ ≤ C |f|_sup`; BGR 6.2.2/4 is
stated for finite homomorphisms; the claim that `K⟨X, Y⟩/(XY − c)` is a domain, `ℚ₂(√2)` for BGR 6.3.1
Example 1, "`Q(T₁)` is not complete" and the `IsUniform` bridge of §2.3.5 are not on the board.
Hypotheses that the linter found unused were dropped as generalisations (for instance `[Nontrivial A]` in
BGR 6.2.2/4, `[IsReduced A]` in the "if" half of BGR 6.2.3/5, now
`IsAffinoidAlgebra.supSeminorm_mul_of_isDomain_reduction`, and the affinoid hypothesis on the target of
`isStrictMap_of_isometry`), and the statement of BGR 6.3.1 Example 1 gained the instance `HasSupSeminorm K K`
that the reduction functor needs on its source.

### 2.1 The supremum seminorm of a Banach function algebra

Stated for a `K`-Banach algebra `B` all of whose maximal ideals have residue fields finite over `K`
(BGR calls them `K`-algebraic), so that every affinoid algebra is an instance by §1.2.4.

1. Define `|f(x)|` for `x ∈ Max B` through the spectral norm of `B ⧸ x` (convention 4) and
   `|f|_sup := ⨆_x |f(x)|` (convention 5). Prove `|f|_sup ≤ ‖f‖` for every complete `K`-algebra
   norm (BGR 3.8.2/2), so the supremum is finite, and that `|·|_sup` is a power-multiplicative
   `K`-algebra seminorm (BGR 3.8.1/3, 6.2.1/1): submultiplicative, nonarchimedean,
   `|cf|_sup = |c||f|_sup`, `|fⁿ|_sup = |f|_sup^n`.
2. Prove `|f|_sup = max_i |π_i(f)|_sup` over the minimal primes `𝔭_i` of a noetherian `B`
   (BGR 3.8.1/5, 6.2.1/3), and `|f|_sup = |red f|_sup` for the reduction modulo the nilradical.
3. Prove the contraction and isometry statements (BGR 3.8.1/4, 3.8.1/6, 6.2.2/1): every `K`-algebra
   homomorphism of such algebras is a contraction for `|·|_sup`, and an integral injective one is an
   isometry.
4. Prove BGR 3.8.1/7 for an integral, torsion-free, injective homomorphism `Td → A` (and more
   generally from a valued, integrally closed domain): `|·|_sup` is a faithful `Td`-algebra norm on
   `A`, and if `fⁿ + t₁fⁿ⁻¹ + ⋯ + tₙ = 0` is the integral equation of minimal degree then
   `|f|_sup = max_i |tᵢ|^{1/i}` (BGR 6.2.2/2; Bosch 1.4/12). Prove the inequality `|f|_sup ≤ σ(q)`
   for any monic `q` with `q(f) = 0` (BGR 6.2.2/3), with `σ(q) = max |bᵢ|_sup^{1/i}` the spectral
   value, which is Mathlib's `spectralValue` of `q` for the seminorm `|·|_sup`.

### 2.2 The maximum modulus principle and the value group

1. **Maximum modulus** (BGR 6.2.1/4(i); Bosch 1.4/14). For `A ≠ 0` affinoid and `f ∈ A` there is
   `x ∈ Sp A` with `|f(x)| = |f|_sup`. Prove it for domains by Noether normalisation and §2.1.4,
   reducing to the maximum modulus principle on `Td` (§0.1.3), and in general through the minimal
   primes (§2.1.2).
2. For `|f|_sup ≠ 0` there are `c ∈ K` and `m ≥ 1` with `|cf^m|_sup = 1` (BGR 6.2.1/4(ii); Bosch
   1.4/15); hence `|A|_sup ⊆ |K_a| = √|K^×| ∪ {0}`. State the uniform version: `m` may be chosen to
   depend only on `A`.
3. **Integral equations compute the seminorm** (BGR 6.2.2/4; Bosch 1.4/13). For `φ : B → A`
   integral between affinoid algebras and `f ∈ A` there is a monic `q ∈ B[X]` with `q(f) = 0` and
   `|f|_sup = σ(q)`.
4. `|f|_sup = 0` exactly when `f` is nilpotent; `|·|_sup` is a norm exactly when `A` is reduced
   (BGR 6.2.1/4(iii)); and every homomorphism from a `K`-Banach algebra into a reduced affinoid
   algebra is continuous (BGR 6.2.1/5) — no noetherianity on the source.

### 2.3 Power-bounded and topologically nilpotent elements

`A` affinoid with any complete `K`-algebra norm (convention 3).

1. `f` is power-bounded (`Bornology.IsBounded (Set.range (f ^ ·))`) exactly when `|f|_sup ≤ 1`,
   exactly when `f` satisfies an integral equation with coefficients of norm `≤ 1` for a residue
   norm (BGR 6.2.3/1; Bosch 1.4/16). Hence the power-bounded elements `Å` form a subring
   independent of the norm, and `Å = {|f|_sup ≤ 1}`.
2. `f` is topologically nilpotent exactly when `|f(x)| < 1` for every `x`, exactly when
   `|f|_sup < 1` (BGR 6.2.3/2; Bosch 1.4/17). Hence `Ǎ := {|f|_sup < 1}` is the ideal of
   topologically nilpotent elements of `Å`.
3. **Spectral radius** (BGR 6.2.3/3): `|f|_sup = inf_i ‖fⁱ‖^{1/i}` for every complete `K`-algebra
   norm; the right-hand side is Mathlib's `smoothingSeminorm`, and the theorem identifies it with
   `|·|_sup`.
4. The reduction `Ã := Å ⧸ Ǎ` (BGR 6.2.3/4) is a `K̃`-algebra; for `Tₙ` it is `K̃[X]` (§0.1.2).
   Prove that `|·|_sup` is a valuation on `A` exactly when `A` is reduced and `Ã` is a domain
   (BGR 6.2.3/5), and record the counterexample `K⟨X, Y⟩/(XY − c)`, `0 < |c| < 1`: a domain on
   which `|·|_sup` is not multiplicative (BGR 6.2.3, the example after 6.2.3/5).
5. **Uniformity.** Prove that `Å` is bounded in `A` exactly when `|·|_sup` is equivalent to the
   norm of `A`, and deduce from §2.4.1 that a reduced affinoid algebra is uniform in the sense of
   the adic-spaces roadmap's §4.2 (`TauCeti.Huber.IsUniform`); conversely a uniform affinoid algebra
   is reduced (adic §4.2, `IsUniform.isReduced`). ⚠ This is the input Layer 8 needs to apply the
   Buzzard–Verberkmoes criterion on the adic side, and it is the reason §2.4 is in scope.

### 2.4 Reduced affinoid algebras are Banach function algebras

1. **BGR 6.2.4/1.** For a reduced affinoid algebra `A`, `|·|_sup` is a complete norm equivalent to
   every complete `K`-algebra norm on `A`. Prove it as BGR does: for a domain, by Noether
   normalisation `Td ↪ A` and the Banach-function-algebra theorem BGR 3.8.3/7 (stated and proved in
   §2.4.2) applied with the weak stability of `Q(Td)` (§0.4.2); in general, embed `A` into
   `⊕ A ⧸ 𝔭ᵢ` over the minimal primes with the maximum norm, use §2.1.2 to see that the induced
   norm is `|·|_sup`, and use the closedness of `A` in the finite `A`-module `⊕ A ⧸ 𝔭ᵢ`
   (`p`-adic-functional-analysis §1.4.2). Equivalence of norms is then §1.3.3.
2. **BGR 3.8.3/7**, stated and proved in the generality BGR gives it: for a noetherian `K`-Banach
   algebra `B` that is an integrally closed domain, whose supremum seminorm is a valuation and whose
   fraction field is weakly stable, and for `A` a finite torsion-free `B`-algebra which is reduced,
   `|·|_sup` on `A` is a complete norm equivalent to the Banach norm. The torsion-free finite
   module structure and the spectral norm of the fraction-field extension are the inputs.
3. Deduce for reduced `A` that `Å` is the unit ball of a norm defining the topology, that `Ǎ` is its
   open unit ball, and that `A ↦ Å` is functorial for all `K`-algebra homomorphisms (BGR 6.3,
   introduction).

### 2.5 The reduction functor on homomorphisms

1. Every homomorphism `φ : B → A` of affinoid algebras maps `B̊` to `Å` and `B̌` to `Ǎ`, inducing
   `φ̃ : B̃ → Ã` (BGR 6.3, introduction; from §2.3.1–2.3.2). Prove functoriality.
2. Define strict homomorphisms (the image of an open set is open in the image) and prove BGR
   6.3.1/4–5: for `φ` strict, `ker φ̃ = rad(τ(ker φ̊))`; and if `φ` is strict with `ker φ ⊆ rad B`
   then `φ̃` is injective.
3. **BGR 6.3.1/6.** For `B` reduced, the following are equivalent: `φ` is injective and strict;
   `φ` is an isometry for `|·|_sup`; `φ̃` is injective. Record that no criterion relates
   surjectivity of `φ` and of `φ̃` (BGR 6.3.1, the two examples after 6.3.1/6).

### Examples

`|X|_sup = 1` and `|p|_sup = p⁻¹` in `ℚ_p⟨X⟩`; `|X|_sup = |a|` in `K⟨X⟩/(X − a)`; the nilpotent `ε` in
`K⟨X⟩/(X²)` has `|ε|_sup = 0` and residue norm `1`; in `K⟨X⟩/(X² − p)` the element `X` has
`|X|_sup = p^{−1/2} ∉ |K^×|`; `X` is power-bounded and `pX` is topologically nilpotent in `K⟨X⟩`;
the domain `K⟨X, Y⟩/(XY − c)` whose supremum seminorm is not multiplicative; `K⟨X⟩/(X²)` is not
uniform; `Q(T₁)` is not complete for the Gauss norm.

### Dependencies

Layers 0–1; Mathlib's spectral norm and smoothing seminorm; the adic-spaces roadmap §4.2 for
`IsUniform`; the `p`-adic-functional-analysis roadmap §1.4.

---

## Layer 3: affinoid varieties

References: BGR 7.1, 7.2.1; Bosch 1.5.

### 3.1 The maximal spectrum of a Tate algebra

1. Define `Sp A := MaximalSpectrum A` for an affinoid algebra `A`, the residue field `κ(x) = A ⧸ x`
   with its spectral norm, and `|f(x)|` (convention 4). Prove `|f(x)| = 0 ↔ f ∈ x` and
   `|(fg)(x)| = |f(x)||g(x)|`, `|(f + g)(x)| ≤ max`, `|c(x)| = |c|` for `c ∈ K`.
2. **Points of `Sp Tₙ`** (BGR 7.1.1/1). For a finite extension `K'/K` and `a ∈ Bⁿ(K')` (the closed
   unit polydisc of `K'`), evaluation `f ↦ f(a)` is a continuous `K`-algebra map `Tₙ → K'` whose
   kernel `𝔪_a` is maximal; the map `Bⁿ(K_a) → Max Tₙ`, `a ↦ 𝔪_a`, is surjective with finite
   fibres, and `𝔪_a = 𝔪_b` exactly when `a` and `b` are conjugate over `K`. State it without the
   algebraic closure: every maximal ideal is `𝔪_a` for some finite `K'` and `a ∈ Bⁿ(K')`, and two
   such points give the same ideal exactly when there is a `K`-isomorphism `K(a) ≅ K(b)` carrying
   `a` to `b`. Prove `|f(𝔪_a)| = |f(a)|`.
3. Every maximal ideal of `Tₙ` is generated by `n` elements (BGR 7.1.1/3): the minimal polynomials
   of the coordinates of a point generate `𝔪_a` after a triangular change of generators. (BGR
   deduces `dim Tₙ ≤ n` from this; §0.3.4 has already proved it, by integral descent.)
4. Connect with Tau Ceti: the classical points `TauCeti.ValuationSpectrum.classicalPoint` of the
   closed polydisc are the points `𝔪_a` with `a ∈ Bⁿ(K)` read as valuations `f ↦ |f(a)|`; this is
   the first instance of §8.1.

### 3.2 Affinoid subsets and the Nullstellensatz

1. For `F ⊆ A` define `V(F) = {x ∈ Sp A : F ⊆ x}` and for `E ⊆ Sp A` the ideal
   `id(E) = ⋂_{x ∈ E} x`; these are Mathlib's `PrimeSpectrum.zeroLocus` and `vanishingIdeal` read on
   `MaximalSpectrum` through `toPrimeSpectrum`. Prove `V(F) = V(𝔞) = V(rad 𝔞)` for the ideal `𝔞`
   generated by `F`, that every `V(F)` is `V(f₁, …, f_r)` for finitely many `fᵢ` (BGR 7.1.2/1),
   and `V(id(V(F))) = V(F)` (BGR 7.1.2/2).
2. **Nullstellensatz** (BGR 7.1.2/3; Bosch 1.5/4): `id(V(𝔞)) = rad 𝔞`, from the Jacobson property
   (§0.3.3 and §1.1.2). Deduce the bijection between radical ideals of `A` and affinoid subsets
   of `Sp A` (BGR 7.1.2/4), and that functions without a common zero generate the unit ideal
   (BGR 7.1.2/5; Bosch 1.5/6). ⚠ The last item is the hypothesis of every rational domain and the
   bridge to Wedhorn's Corollary 7.53 in §8.2.
3. The calculus of `V` and `id` (BGR 7.1.2/6), irreducibility `↔` `id(Y)` prime (BGR 7.1.2/7), and
   the unique minimal decomposition of an affinoid subset into irreducible ones (BGR 7.1.2/8), from
   noetherianity. Define the Zariski topology on `Sp A` as Mathlib's `MaximalSpectrum.zariskiTopology`
   and prove its closed sets are the affinoid subsets.
4. Closed subspaces (BGR 7.1.3): for an ideal `𝔞 ⊆ A`, `Sp(A ⧸ 𝔞) → Sp A` is injective with image
   `V(𝔞)`, and every affinoid variety is a closed subvariety of some `Sp Tₙ`.

### 3.3 Affinoid maps and the category of affinoid varieties

1. For a `K`-algebra homomorphism `σ : B → A` of affinoid algebras define `Sp σ : Sp A → Sp B`,
   `x ↦ σ⁻¹(x)`, well defined by §1.2.4, and prove `|g(Sp σ (x))| = |σ(g)(x)|`
   (BGR 7.1.4; Bosch 1.5/6). Prove that `Sp` is a fully faithful contravariant functor: affinoid
   maps `Sp A → Sp B` are by definition the maps `Sp σ`, and `σ ↦ Sp σ` is injective (the
   Nullstellensatz, through the Jacobson property). Define the category of affinoid varieties as
   the opposite of the category of affinoid algebras (BGR 7.1.4).
2. Define closed immersions (`σ` surjective) and finite maps (`A` a finite `B`-module); prove that
   a closed immersion is injective with image an affinoid subset (BGR 7.1.4/3), and that finite
   maps have finite fibres and are surjective when injective on algebras (going up).
3. **Fibre products** (BGR 7.1.4/4): `Sp B₁ ×_{Sp A} Sp B₂ = Sp (B₁ ⊗̂_A B₂)` with the affinoid
   tensor product of §1.1.5, and the universal property in the category of affinoid varieties.
   Prove that the underlying set of the fibre product is **not** the fibre product of the
   underlying sets, with the example `Sp(K' ⊗_K K')` for a non-trivial finite extension `K'`.
4. Noether normalisation geometrically: every nonempty affinoid variety admits a finite surjective
   map onto some unit ball `𝔹^d = Sp Td` (BGR 7.1.4, the remark after 7.1.4/3).

### 3.4 The canonical topology

1. Define the canonical topology on `Sp A` as the topology generated by the sets
   `X(f; ε) = {|f(x)| ≤ ε}` for `f ∈ A`, `ε > 0` (BGR 7.2.1; Bosch 1.5/1), and prove it is
   generated by the `X(f) = X(f; 1)` alone (Bosch 1.5/2, using `|A|_sup ⊆ √|K^×|`).
2. Prove Bosch 1.5/3: for `|f(x)| = ε > 0` there is `g ∈ A` with `g(x) = 0` and `|f(y)| = ε` for all
   `y ∈ X(g)`; deduce that `{f ≠ 0}`, `{|f| ≤ ε}`, `{|f| = ε}`, `{|f| ≥ ε}` are open
   (Bosch 1.5/4) and that the sets `X(f₁, …, f_r)` with `fᵢ ∈ 𝔪_x` form a neighbourhood basis of
   `x` (Bosch 1.5/5).
3. Affinoid maps are continuous for the canonical topologies (Bosch 1.5/6), the Zariski topology is
   coarser than the canonical topology, and `Sp A` is totally disconnected and Hausdorff for the
   canonical topology; `Sp Tₙ` is compact exactly when `K` is locally compact and `n = 0`, and in
   general is not compact (the unit disc over `ℂ_p` is not).

### Examples

`Sp K⟨X⟩` is the closed unit disc: its points for `K = ℚ_p` include the `ℚ_p`-rational points, the
points of residue degree two such as `𝔪 = (X² − p)`, and no point of the form `|X| = p^{−1/3}`
unless `K` is enlarged; `Sp K⟨X, Y⟩/(XY − c)` is the annulus `|c| ≤ |X| ≤ 1`; `V(X) ⊆ Sp K⟨X⟩` is a
single point; the Nullstellensatz for `𝔞 = (X²)`; the finite map `Sp K⟨X⟩ → Sp K⟨Y⟩`, `Y ↦ X²`,
has fibres of size one or two; the canonical topology on `Sp ℚ_p⟨X⟩` restricted to `ℤ_p` is the
`p`-adic topology.

### Dependencies

Layers 1–2; Mathlib's `MaximalSpectrum`, `PrimeSpectrum` zero loci, and Jacobson rings.

---

## Layer 4: affinoid subdomains and the Gerritzen–Grauert theorem

References: BGR 7.2.2–7.2.5, 7.3; Bosch 1.6–1.8.

### 4.1 The universal property

1. Define `AffinoidSubdomain X` (convention 6; BGR 7.2.2/2; Bosch 1.6/9). Prove Bosch 1.6/10
   (BGR 7.2.2): the map `Sp A' → Sp A` is injective with image exactly `U`, `A ⧸ 𝔪_{ι(x)}^n ≅ A' ⧸ 𝔪_x^n`
   for all `n`, and `𝔪_x = 𝔪_{ι(x)} A'`. Prove that the representing algebra is unique up to unique
   isomorphism over `A`, so that `𝒪_X(U)` is well defined, and that `U` is an affinoid variety with
   `Sp 𝒪_X(U) ≅ U` as sets.
2. **Transitivity** (BGR 7.2.2/3; Bosch 1.6/12): an affinoid subdomain of an affinoid subdomain of
   `X` is an affinoid subdomain of `X`.
3. **Preimages** (BGR 7.2.2/4; Bosch 1.6/13): for an affinoid map `φ : Y → X` and `X' ⊆ X` an
   affinoid subdomain, `φ⁻¹(X')` is an affinoid subdomain of `Y` with algebra
   `𝒪_X(X') ⊗̂_A B`, and `φ` restricts to an affinoid map `φ⁻¹(X') → X'`.
4. **Intersections** (BGR 7.2.2/5 and 7.2.3/7; Bosch 1.6/14): the intersection of two affinoid
   subdomains is an affinoid subdomain, with algebra `𝒪_X(U) ⊗̂_A 𝒪_X(V)`; the restriction of an
   affinoid covering to an affinoid subdomain is an affinoid covering (BGR 8.2.2/1). Hence the
   affinoid subdomains of `X` form a poset with finite intersections, which is the index category
   of convention 7.

### 4.2 Weierstrass, Laurent and rational domains

1. Define `X(f) = {|fᵢ(x)| ≤ 1}`, `X(f, g⁻¹) = {|fᵢ(x)| ≤ 1, |gⱼ(x)| ≥ 1}` and, for `f₁, …, fₘ, g`
   without common zero, `X(f/g) = {|fᵢ(x)| ≤ |g(x)|}` (BGR 7.2.3; Bosch 1.6/7); prove all three are
   open for the canonical topology and that the Weierstrass domains form a basis of it
   (Bosch 1.6/8).
2. **They are affinoid subdomains** (BGR 7.2.3; Bosch 1.6/11), represented by `A⟨f⟩`,
   `A⟨f, g⁻¹⟩` and `A⟨f/g⟩` of §1.4, with the universal property verified through the universal
   properties of §1.4 and the characterisation of power-boundedness by `|·|_sup` (§2.3.1). Prove
   that the three classes are stable under intersection (Bosch 1.6/14) and that Weierstrass
   domains are Laurent and Laurent domains are rational (Bosch 1.6/15).
3. **Rational domains are Weierstrass in a Laurent domain** (BGR 7.2.4/1; Bosch 1.6/16): for
   `U = X(f/g)` there is `ε ∈ |K^×|` such that `X' = X(εg⁻¹)` satisfies `U ⊆ X'`, `U` is a Weierstrass
   domain in `X'`, and `U ∩ X(ε⁻¹g) = ∅`. Prove transitivity for Weierstrass and for rational
   domains (BGR 7.2.4; Bosch 1.6/17), and record that it **fails** for Laurent domains, with BGR's
   example of a rational domain in the unit disc that is not Laurent (BGR 7.2.4, the example after
   7.2.4/1) and of the Laurent domain `X(X⁻¹)` that is not Weierstrass.
4. Scaled domains: for `ε ∈ √|K^×|` the sets `X(ε⁻¹f)`, `X(ε⁻¹f, δg⁻¹)` and `X(ε⁻¹ f/g)` are
   Weierstrass, Laurent and rational domains (BGR 7.2.3, end), by `ε^r = |c|`.
5. Identification with the adic-spaces roadmap's rational subsets: under §1.4.3 the rational domain
   `X(f/g)` has the same presentation data as the rational subset `R(T/s)` of `Spa(A, A°)`; the
   point-set comparison is §8.1.

### 4.3 The openness theorem

1. Prove Bosch 1.6/18 (BGR 7.2.5): for `φ : Y → X` affinoid and `x ∈ X` with
   `A ⧸ 𝔪_x → B ⧸ 𝔪_x B` surjective (resp. `A ⧸ 𝔪_x^n ≅ B ⧸ 𝔪_x^n B` for all `n`) there is a
   special affinoid subdomain `X' ∋ x` over which `φ` is a closed immersion (resp. an isomorphism).
   The proof is BGR's: an affinoid generating system of `B` over `A` (§1.1.3), approximation of the
   generators by elements of `A` modulo `𝔪_x`, and the universal property of `A⟨X⟩`.
2. **Openness theorem** (BGR 7.2.5; Bosch 1.6/19): every affinoid subdomain is open for the
   canonical topology, and the canonical topology of `X` restricts to that of the subdomain.

### 4.4 Germs, stalks and flatness

1. Define the presheaf `𝒪_X` on the poset of affinoid subdomains, `U ↦ 𝒪_X(U)`, with restriction
   maps from the universal property (BGR 7.3.2), and the stalk `𝒪_{X,x} = colim_{U ∋ x} 𝒪_X(U)`.
   Prove `𝒪_{X,x}` is local with maximal ideal `𝔪_x 𝒪_{X,x}` and residue field `κ(x)`
   (BGR 7.3.2/1; Bosch 1.7/1).
2. Prove Bosch 1.7/2 (BGR 7.3.2): `A_{𝔪_x} → 𝒪_{X,x}` is injective and induces an isomorphism of
   `𝔪_x`-adic completions, through the ideal-adic topologies of BGR 7.3.1 (Corollaries 7.3.1/8–9,
   stated and proved for noetherian local rings). Deduce: a function is zero if all its germs are
   (Bosch 1.7/3); the restriction maps of an affinoid covering are jointly injective
   (Bosch 1.7/4); `𝒪_{X,x}` is noetherian (Bosch 1.7/6).
3. **Flatness** (BGR 7.3.2; Bosch 1.7/5): for an affinoid subdomain `Sp A' ⊆ Sp A` the map
   `A → A'` is flat. Prove it from item 2 and the local flatness criterion, or transport the
   adic-spaces roadmap's flatness of rational localisations (§1.4.4) through Gerritzen–Grauert for
   the rational case and the local criterion in general; record which route is taken.
4. Reducedness and normality are local: `A` reduced (resp. normal) iff all `𝒪_{X,x}` are
   (BGR 7.3.2/8–9), and pass to affinoid subdomains (BGR 7.3.2/10); the Japanese property of
   §1.2.5 and the excellence-free argument BGR gives are what is used.

### 4.5 Immersions

1. Define closed immersions (surjective on algebras), locally closed immersions (injective, with
   surjective stalk maps) and open immersions (injective, with bijective stalk maps) of affinoid
   varieties (BGR 7.3.3; Bosch 1.8/1). Prove: inclusions of affinoid subdomains are open
   immersions (BGR 7.3.3/1); compositions of immersions of each type are of the same type
   (BGR 7.3.3/2); immersions restrict to preimages of affinoid subdomains (BGR 7.3.3/3;
   Bosch 1.8/2).
2. A locally closed immersion whose algebra map is finite is a closed immersion (Bosch 1.8/3), and
   an open and closed immersion defines a Weierstrass domain (Bosch 1.8/4).
3. **Runge immersions** (BGR 7.3.4; Bosch 1.8/5–8): a closed immersion into a Weierstrass domain;
   `σ : A → A'` corresponds to a Runge immersion iff `σ(A)` is dense in `A'` iff `σ(A)` contains an
   affinoid generating system of `A'` over `A` (Bosch 1.8/7), with the approximation lemma Bosch
   1.8/8 for generating systems; Runge immersions restrict to affinoid subdomains (Bosch 1.8/6).

### 4.6 The Gerritzen–Grauert theorem

1. Weierstrass theory over an affinoid algebra (BGR 7.3.4–7.3.5; Bosch 1.8/13–15): distinguishedness
   of `f ∈ A⟨ζ⟩` at a point `x ∈ Sp A`, the chart lemma of §0.2.3 in its relative form (Bosch
   1.8/13: for `f ∈ A⟨ζ⟩` whose coefficients have no common zero on `Sp A`, some automorphism of
   the type of §0.2.3 makes `f` `ζₙ`-distinguished of order `≤ s` at every point), the lemma
   that `{x : f is ζₙ-distinguished of order exactly s at x}` is a rational subdomain (Bosch 1.8/14),
   and the finiteness of `A⟨ζ₁, …, ζ_{n−1}⟩ → A⟨ζ⟩/(f)` for `f` of order exactly `s` at every
   point (Bosch 1.8/15).
2. **Main theorem for locally closed immersions** (BGR 7.3.5; Bosch 1.8/10). For a locally closed
   immersion `φ : X' → X` of affinoid varieties there is a finite covering of `X` by rational
   subdomains `Xᵢ` such that each `φ⁻¹(Xᵢ) → Xᵢ` is a Runge immersion. Prove it by induction on
   the number of affinoid generators along Bosch 1.8, using items 1 and §4.5.
3. **Corollaries** (BGR 7.3.5/2–3; Bosch 1.8/11–12): for an open immersion the `φ⁻¹(Xᵢ)` are
   Weierstrass domains in `Xᵢ`; every affinoid subdomain `X' ⊆ X` admits a finite covering of `X`
   by rational subdomains `Xᵢ` with `Xᵢ ∩ X'` Weierstrass in `Xᵢ`; hence **every affinoid
   subdomain is a finite union of rational subdomains** (BGR 7.3.5/3; Bosch 1.6/20). Record that a
   finite union of affinoid subdomains need not be an affinoid subdomain (Bosch, remark after
   1.6/20).

### Examples

In `X = Sp K⟨X⟩`: `X(X⁻¹) = {|X| = 1}` is Laurent and not Weierstrass; `X(c⁻¹X)` for `|c| < 1` is
the disc of radius `|c|`; the annulus `X(cX⁻¹, X)`; the rational domain `X(X/c) ∪`-type example of
BGR 7.2.4 that is not Laurent; the covering `{|X| ≤ |c|} ∪ {|X| ≥ |c|}` is a Laurent covering; the
stalk `𝒪_{X,0}` is the ring of power series convergent on some disc about `0`, strictly larger than
`K⟨X⟩_{(X)}` and strictly smaller than `K⟦X⟧`; Gerritzen–Grauert for `U = X(X⁻¹) ∪ X(c⁻¹X)` in the
disc, which is affinoid only when the two pieces are suitably related.

### Dependencies

Layers 1–3; the adic-spaces roadmap §§3.1 and 4.1 for the flatness transport of §4.4.3.

---

## Layer 5: Čech cohomology and Tate's acyclicity theorem

References: BGR 8.1, 8.2; Bosch 1.9.

### 5.1 Čech cohomology of a presheaf on a covering

Stated for a presheaf `F` of abelian groups (or `R`-modules) on a poset with finite meets — the
affinoid subdomains of `X` (§4.1.4), the admissible opens of a G-topological space (§6.1) — and a
finite family `𝔘 = (Uᵢ)` in it.

1. Define the Čech complex `C^•(𝔘, F)` as Mathlib's `cechComplexFunctor` applied to the family and
   the presheaf, the alternating complex `C^•_a(𝔘, F)` of BGR 8.1.3, and the augmentation
   `F(X) → C^0(𝔘, F)`; prove the two complexes have the same cohomology (Bosch 1.9/8) and that the
   alternating complex vanishes in degrees `≥ |𝔘|` (Bosch 1.9/9). Define `H^q(𝔘, F)`, and
   `F`-acyclicity of `𝔘`: exactness of the augmented complex.
2. Refinements: a refinement `τ : 𝔙 → 𝔘` induces `H^q(𝔘, F) → H^q(𝔙, F)` independent of `τ`
   (BGR 8.1.3), and mutual refinements induce inverse isomorphisms (BGR 8.1.3/4).
3. **The comparison theorem** (BGR 8.1.4/2–4). If all restrictions `𝔘|_{V_{j₀…j_q}}` and
   `𝔙|_{U_{i₀…i_p}}` are `F`-acyclic then `H^r(𝔘, F) ≅ H^r(𝔙, F)` through the double complex, and
   `𝔘` is `F`-acyclic iff `𝔙` is; in particular for `𝔙` a refinement of `𝔘` with `𝔙|_{U_{i₀…i_p}}`
   acyclic for all `p`, acyclicity of `𝔘` and `𝔙` are equivalent (BGR 8.1.4/3), and the product
   covering `𝔘 × 𝔙` is acyclic iff `𝔘` is, when `𝔙|_{U_{i₀…i_p}}` are (BGR 8.1.4/4). Prove the
   sheaf-property versions first (Bosch 1.9/2–3), then the cohomological ones.
4. Define `𝔘`-sheaves (Bosch 1.9, the definition before 1.9/1): `F` satisfies the sheaf condition
   for `𝔘|_U` on every affinoid subdomain `U`. Prove that `F` is a `𝔘`-sheaf for every Laurent
   covering implies `F` is a `𝔙`-sheaf for every affinoid covering `𝔙` (Bosch 1.9/7), from items
   2–3 and §5.2.

### 5.2 Reductions: affinoid, rational, Laurent coverings

1. Define rational coverings `{X(f₁/fᵢ, …, fₙ/fᵢ)}ᵢ` generated by `f₁, …, fₙ` without common zero,
   and Laurent coverings `{X(f₁^{±1}, …, fₙ^{±1})}` generated by `f₁, …, fₙ` (BGR 8.2.2); prove
   they are affinoid coverings and restrict to coverings of the same type on affinoid subdomains
   (BGR 8.2.2/1).
2. **Every affinoid covering has a rational refinement** (BGR 8.2.2/2; Bosch 1.9/4), from
   Gerritzen–Grauert (§4.6.3) and the product construction of BGR's proof.
3. **Every rational covering is refined, over a Laurent covering, by rational coverings generated
   by units** (Bosch 1.9/5), and **every rational covering generated by units is refined by a
   Laurent covering** (Bosch 1.9/6; BGR 8.2.2); the latter is the covering generated by the
   quotients `fᵢ/fⱼ`.
4. Assemble Bosch 1.9/7: acyclicity (or the sheaf property) for all Laurent coverings implies it
   for all affinoid coverings.

### 5.3 The Laurent case and Tate's theorem

1. **Two-piece Laurent coverings.** For `f ∈ A` the sequence
   `0 → A → A⟨f⟩ × A⟨f⁻¹⟩ → A⟨f, f⁻¹⟩ → 0` is exact (BGR 8.2.3; Bosch 1.9, the diagram after 1.9/7).
   Obtain it from the adic-spaces roadmap's Wedhorn 8.33 (`laurentCover_injective`, `_exact`,
   `_surjective`) transported along §1.4.3 (convention 10), after proving that an affinoid
   algebra with its affinoid topology is a complete Hausdorff strongly noetherian Tate ring: Tate
   because `K` has a pseudouniformiser, strongly noetherian because `A⟨X₁, …, Xₖ⟩` is affinoid
   (§1.1.3) hence noetherian (§1.1.2). ⚠ Record the shape of Wedhorn's cover: its pieces are the
   rational subsets `{|f| ≤ 1}` and `{|f| ≥ 1}` of `Spa(A, A°)`, whose coordinate rings are the
   algebras `A⟨f⟩` and `A⟨f⁻¹⟩` of §1.4.1 by the identification; nothing about points is needed
   here.
2. Laurent coverings generated by several functions are products of two-piece ones; conclude by
   §5.1.3 (BGR 8.1.4/4) that every Laurent covering is `𝒪_X`-acyclic, for `𝒪_X` restricted to any
   affinoid subdomain.
3. **Tate's acyclicity theorem** (BGR 8.2.1/1; Bosch 1.9/1 and 1.9/10): every finite affinoid
   covering of an affinoid variety is `𝒪_X`-acyclic. Assemble §5.1.4, §5.2 and items 1–2.
4. **The module version** (Bosch 1.9/11; BGR 8.2.1): for an `A`-module `M`, the presheaf
   `U ↦ M ⊗_A 𝒪_X(U)` is acyclic for every finite affinoid covering. Prove it for free modules by
   additivity and in general by a presentation `0 → M' → F → M → 0`, the flatness of §4.4.3 and
   the vanishing of the Čech complex in high degrees (Bosch's descending induction).

### 5.4 Consequences

1. `𝒪_X` has the sheaf property for affinoid coverings (BGR 8.2.1/2): restriction is jointly
   injective and compatible families glue uniquely.
2. Affinoid maps glue (BGR 8.2.1/3): maps `Uᵢ → Y` agreeing on overlaps come from a unique map
   `X → Y`, and two maps agreeing on each `Uᵢ` are equal.
3. **Affinoid subdomains are exactly the open immersions** (BGR 8.2.1/4): for an affinoid map
   `φ : U → X`, `U` is an affinoid subdomain of `X` via `φ` iff `φ` is an open immersion; a
   surjective open immersion is an isomorphism. Uses §4.6.3 and item 2.
4. Record the non-example (BGR 8.2.1, end): on a positive-dimensional affinoid variety there are
   infinite coverings by affinoid subdomains that are not acyclic — for a domain `A` with a point
   `x₀`, the covering by a small disc about `x₀` and infinitely many pieces of its complement — which
   is why coverings must be finite and why Layer 6 restricts admissible coverings.

### Examples

The Laurent covering `{|X| ≤ 1} ∪ {|X| ≥ 1}` of `Sp K⟨X, X⁻¹⟩`-type annuli; the standard covering
of the unit disc `{|X| ≤ |c|} ∪ {|X| ≥ |c|}` with the explicit exact sequence
`0 → K⟨X⟩ → K⟨c⁻¹X⟩ × K⟨X, cX⁻¹⟩ → K⟨c⁻¹X, cX⁻¹⟩ → 0`; the rational covering of the disc generated
by `X, c`; a function on the unit disc defined piecewise on `|X| ≤ |c|` and `|X| ≥ |c|` agreeing on
`|X| = |c|` is a single restricted series; the non-admissible covering of the disc by `{|X| < 1}`
and `{|X| = 1}`, for which the zero cochain `(1, 0)` does not glue.

### Dependencies

Layers 1–4; the adic-spaces roadmap §4.1 (Wedhorn 8.33) and §0.5 (strong noetherianity) through
§5.3.1; Mathlib's `cechComplexFunctor`.

---

## Layer 6: G-topologies, sheaves, and rigid analytic varieties

References: BGR 9.1, 9.2, 9.3; Bosch 1.10–1.12.

### 6.1 G-topological spaces

1. Define `GTopology X` (convention 8; BGR 9.1.1/1) by BGR's four axioms: (i) `U ∩ V` is
   admissible for `U, V` admissible; (ii) every admissible covering is a covering of an admissible
   open by admissible opens; (iii) the trivial covering `{U}` of an admissible open is admissible;
   (iv) admissible coverings are stable under restriction to admissible open subsets and under
   composition. State them exactly so, and define continuous maps of G-topological spaces (preimages of admissible opens and coverings are
   admissible), finer and weaker G-topologies, the induced G-topology along a map, and bases
   (BGR 9.1.1).
2. Define `GTopology.Opens`, the preorder of admissible opens, the coverage whose covering families
   are the admissible coverings, the generated Grothendieck topology, and prove that a presheaf on
   `Opens` is a sheaf for it exactly when it satisfies the equaliser condition for every admissible
   covering (Mathlib's `Presieve.isSheaf_coverage`). Prove that a topological space with all open
   sets and open coverings is a G-topological space whose Grothendieck topology is Mathlib's
   `Opens.grothendieckTopology`.
3. **Enhancing** (BGR 9.1.2): define slightly finer G-topologies (BGR 9.1.2/1), the completeness
   conditions `(G0)`: `∅` and `X` admissible; `(G1)`: a subset `V ⊆ U` of an admissible open with
   `V ∩ Uᵢ` admissible for all members of an admissible covering of `U` is admissible; `(G2)`: a
   covering of an admissible open by admissible opens which has an admissible refinement is
   admissible. Prove BGR 9.1.2/5: every G-topology `𝔗` has a unique finest G-topology slightly finer
   than it, satisfying `(G1)` and `(G2)`, and `(G0)` if `𝔗` does; construct it as BGR 9.1.2/2–4 do,
   through coverings compatible with `𝔗`.
4. **Pasting** (BGR 9.1.3; Bosch 1.10/10–11): on a set `X` covered by `Xᵢ` with G-topologies
   satisfying `(G0)`–`(G2)` and compatible on overlaps, there is a unique G-topology on `X`
   satisfying `(G0)`–`(G2)` inducing the given ones and making `(Xᵢ)` admissible; admissible opens
   and coverings are detected on the `Xᵢ` (Bosch 1.10/10). Model the construction on Mathlib's
   `TopCat.GlueData`.

### 6.2 The weak and strong G-topologies on an affinoid variety

1. Define the weak G-topology on `Sp A` (BGR 9.1.4; Bosch 1.10/3): admissible opens are the affinoid
   subdomains, admissible coverings the finite affinoid coverings. Prove it is a G-topology, that
   affinoid maps are continuous for it (BGR 9.1.4), and that `𝒪_X` is a sheaf for it (Tate, §5.4.1).
2. Define the strong G-topology (BGR 9.1.4; Bosch 1.10/4): `U` is admissible open when it has a
   covering by affinoid subdomains `Uᵢ` such that for every affinoid map `φ : Z → X` with image in
   `U` the covering `(φ⁻¹(Uᵢ))` of `Z` has a finite affinoid refinement; a covering of such a `U`
   by such sets is admissible when every such `φ` sees a finite affinoid refinement. Prove it is the
   finest G-topology slightly finer than the weak one (BGR 9.1.4, via 9.1.2/5), satisfies
   `(G0)`–`(G2)` (Bosch 1.10/5), that affinoid maps are continuous for it (Bosch 1.10/6), and that
   it restricts to the strong G-topology of an affinoid subdomain (BGR 9.1.4/3).
3. **Zariski-open subsets are admissible** (BGR 9.1.4/5–7; Bosch 1.10/7–9): the complement of
   `V(f₁, …, f_r)` is admissible open, covered admissibly by the `X(ε⁻¹ f_j^{-1})`-type pieces, and
   every Zariski covering is admissible; the proof uses the maximum modulus principle and the lemma
   BGR 9.1.4/6 on constants `α < 1 < β`. Deduce BGR 9.1.4/8: connectedness for the Zariski, weak and
   strong G-topologies coincide, and an affinoid variety is connected iff its algebra has no
   non-trivial idempotent.
4. Record the non-admissible covering of the unit disc by `{|X| < 1}` and `{|X| = 1}` and the
   admissible open `{|X| < 1}` with its admissible covering by the discs `{|X| ≤ |c|}` (the open
   disc is admissible open but not quasi-compact).

### 6.3 Sheaves on G-topological spaces

1. Presheaves and sheaves on a G-topological space with values in a category with products are
   Mathlib's, through §6.1.2 (BGR 9.2.1). Define the stalk at a point as the filtered colimit over
   the admissible opens containing it (for the strong G-topology on an affinoid variety, this is the
   stalk of §4.4.1 by cofinality of affinoid subdomains), and prove it is Mathlib's fibre functor of
   the point of the site given by `x` (`GrothendieckTopology.Point`).
2. **Sheafification** (BGR 9.2.2/3–4; Bosch 1.11/2): `F⁺ = Ȟ⁰(·, F)` is separated; `F⁺⁺` is a sheaf
   and `F → F⁺⁺` is a sheafification. Prove it is Mathlib's sheafification (`presheafToSheaf`) for
   the Grothendieck topology of §6.1.2, so that images and quotients of sheaves are Mathlib's.
3. **Extension of sheaves** (BGR 9.2.3/1; Bosch 1.11/3): for `𝔗'` slightly finer than `𝔗`, every
   `𝔗`-sheaf extends uniquely to a `𝔗'`-sheaf; prove it as an instance of Mathlib's dense-subsite
   equivalence (`Functor.IsDenseSubsite`) for the inclusion of `𝔗`-opens into `𝔗'`-opens, and
   deduce that `𝒪_X` extends uniquely from the weak to the strong G-topology of an affinoid variety
   (BGR 9.2.3; Bosch 1.11/4).

### 6.4 Locally G-ringed spaces and rigid varieties

1. Define locally G-ringed `K`-spaces and their morphisms (convention 9; BGR 9.3.1; Bosch 1.12/1):
   a G-topological space with a sheaf of `K`-algebras whose stalks are local rings; a morphism is a
   continuous map with a map of sheaves `𝒪_Y → φ_* 𝒪_X` that is local on stalks. Define open
   subspaces (restriction to an admissible open with the induced G-topology, which is a G-topology
   satisfying `(G0)`–`(G2)` if the ambient one does).
2. **Affinoid varieties as locally G-ringed spaces.** Attach to `Sp A` the strong G-topology and
   the extended sheaf `𝒪_X` of §6.3.3; prove the stalks are local (§4.4.1) and that affinoid maps
   induce morphisms (BGR 9.3.1, the construction before 9.3.1/1). Prove **full faithfulness**
   (BGR 9.3.1/1–2; Bosch 1.12/2–3): affinoid maps `X → Y` correspond bijectively to morphisms of
   locally G-ringed `K`-spaces, and the functor respects open immersions: `U` is an affinoid
   subdomain of `X` iff `(U, 𝒪_U)` is an open subspace of `(X, 𝒪_X)` (BGR 9.3.1/3). From here on
   an affinoid variety is any locally G-ringed space isomorphic to such a one.
3. **Rigid analytic varieties** (BGR 9.3.1; Bosch 1.12/4): locally G-ringed `K`-spaces whose
   G-topology satisfies `(G0)`–`(G2)` and which admit an admissible covering by open subspaces that
   are affinoid varieties. Morphisms are morphisms of locally G-ringed `K`-spaces. Prove: open
   subspaces of rigid varieties are rigid varieties; the affinoid open subspaces form a basis;
   `Hom(X, Sp B) ≅ Hom_K(B, 𝒪_X(X))` for every rigid variety `X` (Bosch 1.12/7).
4. **Pasting** (BGR 9.3.2; Bosch 1.12/5): given rigid varieties `Xᵢ`, open subspaces `Xᵢⱼ ⊆ Xᵢ` and
   isomorphisms `φᵢⱼ : Xᵢⱼ ≅ Xⱼᵢ` satisfying the cocycle condition, there is a rigid variety `X`
   with an admissible covering by copies of the `Xᵢ` glued along the `φᵢⱼ`, unique up to unique
   isomorphism; build it on Mathlib's `GlueData` with the G-topology of §6.1.4 and the sheaf by
   §6.3.3. Prove the pasting of morphisms (BGR 9.3.3; Bosch 1.12/6).
5. **Fibre products** (BGR 9.3.5; Bosch 1.12/8): the category of rigid varieties has fibre products,
   affinoid-locally `Sp(B₁ ⊗̂_A B₂)` (§3.3.3), glued by item 4; the underlying set is not the
   set-theoretic fibre product in general (§3.3.3).
6. Extension of the ground field (BGR 9.3.6): for a complete extension `K'/K` (a complete
   nonarchimedean field containing `K` isometrically), `A ⊗̂_K K'` is `K'`-affinoid and `X ↦ X ⊗̂_K K'`
   is a functor on rigid varieties compatible with admissible coverings; the finite case is
   §1.1.6. ⚠ `A ⊗̂_K K'` here is the completion of `A ⊗_K K'` for the tensor seminorm, a
   construction specific to a base field and not the general completed tensor product.

### 6.5 Basic examples

Construct, as rigid varieties with their admissible coverings (BGR 9.3.4; Bosch 1.12 and 1.13):
the closed polydisc `𝔹ⁿ = Sp Tₙ`; the open unit disc as the union of `Sp K⟨c⁻¹X⟩` over `|c| < 1`,
not affinoid because not quasi-compact (compare the adic-spaces roadmap's §5.4); the affine
`n`-space `𝔸^{n,rig}` as the union of the polydiscs of radii `|c|^{−i}`; projective space
`ℙ^{n,rig}` by pasting `n + 1` copies of `𝔸^{n,rig}`, admissibly covered by `n + 1` polydiscs;
annuli and the punctured disc; the rigid analytic torus `𝔾_m^{rig}`; and the Zariski-open subsets
of an affinoid variety as open subspaces (§6.2.3).

### Examples

The G-topology of the unit disc: the admissible opens include every affinoid subdomain, every
Zariski open, the open disc and every `{|X − a| < r}`; the covering of the disc by the
`{|X − a| ≤ |c|}` for `a` running over a set of representatives of `K̃` is admissible when `K̃` is
finite and not when it is infinite; the sheaf `𝒪` on `{|X| < 1}` has global sections the power
series convergent on the open disc, which is not an affinoid algebra; `ℙ^{1,rig} = 𝔹¹ ∪ 𝔹¹` glued
along `{|X| = 1}`; `𝒪(ℙ^{1,rig}) = K`.

### Dependencies

Layers 3–5; Mathlib's sites, sheafification, dense subsites, points and `GlueData`.

---

## Layer 7: coherent modules, closed subvarieties, separated and proper morphisms

References: BGR 9.4, 9.5, 9.6.1–9.6.2; Bosch 1.14–1.16.

### 7.1 Associated modules and Kiehl's theorem

1. For `X = Sp A` and an `A`-module `M` define the presheaf `M ⊗_A 𝒪_X` on affinoid subdomains and
   prove it is a sheaf for the weak G-topology (§5.3.4), extend it to the strong G-topology (§6.3.3),
   and prove `(M ⊗_A 𝒪_X)|_{X'} = (M ⊗_A A') ⊗_{A'} 𝒪_{X'}` for affinoid subdomains (BGR 9.4.2).
   Prove BGR 9.4.2/1 (Bosch 1.14/1): `M ↦ M ⊗_A 𝒪_X` is fully faithful, exact, and commutes with
   kernels, images, cokernels and tensor products, using the flatness of §4.4.3.
2. Define `𝒪_X`-modules on a rigid variety, modules of finite type and of finite presentation, and
   coherent modules (Bosch 1.14/2), and `𝔘`-coherent modules for an admissible affinoid covering
   `𝔘` (BGR 9.4.3; convention 11). Prove restriction exactness (BGR 9.4.1/1): a short exact
   sequence of `𝔘`-coherent modules restricts to a short exact sequence on every affinoid subdomain
   contained in a member of `𝔘`.
3. **Kiehl's theorem** (BGR 9.4.3; Bosch 1.14/4): on an affinoid variety `X = Sp A`, an `𝒪_X`-module
   is coherent (for some admissible affinoid covering) iff it is associated to a finite `A`-module.
   Prove it as BGR and Bosch do: reduce to Laurent coverings by §5.2 and the comparison theorem
   (§5.1.3), then to a two-piece Laurent covering by induction; prove `H¹(𝔘, F) = 0` for
   `𝔘`-coherent `F` by the estimate of BGR 9.4.3 (Bosch 1.14/6: the surjectivity of
   `M₁ × M₂ → M₁₂` by the approximation argument with constants `α, β, ε`), and conclude by
   Bosch 1.14/7 (the `𝔪_x`-adic separation and Nakayama argument) that `F` is associated to
   `F(X)`, which is finite. Deduce that coherence is independent of the admissible affinoid
   covering (Bosch 1.14/5).
4. Finite morphisms (BGR 9.4.4): a morphism `φ : X → Y` of rigid varieties is finite when `Y` has an
   admissible affinoid covering over which `φ` is a finite affinoid map; prove the condition is
   independent of the covering (by Kiehl's theorem applied to `φ_* 𝒪_X`) and that finite morphisms
   are stable under base change and composition.

### 7.2 Coherent ideals and closed analytic subvarieties

1. Coherent ideals (BGR 9.5.1): an `𝒪_X`-ideal is coherent iff it is `𝔘`-coherent for an admissible
   affinoid covering; the nilradical of `𝒪_X` is coherent, and `X` is reduced iff its affinoid
   pieces are (BGR 9.5.1 and §4.4.4).
2. Analytic subsets (BGR 9.5.2): a subset `Y ⊆ X` is analytic iff `Y ∩ U` is Zariski-closed in
   every affinoid open `U`; it carries the coherent ideal `id(Y)` and is admissible-locally the
   zero set of finitely many functions. Prove that analytic subsets are closed for the strong
   G-topology in the sense that their complements are admissible open (§6.2.3).
3. **Closed immersions** (BGR 9.5.3; Bosch 1.16/1): for a coherent ideal `𝔍` the ringed space
   `(V(𝔍), 𝒪_X/𝔍)` is a rigid variety and `V(𝔍) → X` is a closed immersion; conversely a morphism is
   a closed immersion iff it is so over an admissible affinoid covering of the target, and the
   condition is independent of the covering (Kiehl). Prove that closed immersions are injective
   with analytic image, stable under base change and composition, and that `X` is a closed
   subvariety of some `𝔹ⁿ` affinoid-locally.

### 7.3 Separated, quasi-compact and proper morphisms

1. Define quasi-compact rigid varieties (a finite admissible affinoid covering) and quasi-compact
   morphisms; prove affinoid varieties are quasi-compact and finite unions of affinoid opens are
   (Bosch 1.16/2).
2. Define separated and quasi-separated morphisms through the diagonal `X → X ×_Y X` (BGR 9.6.1;
   Bosch 1.16/2): closed immersion, respectively quasi-compact. Prove: affinoid maps are separated
   (Bosch 1.16/3); for `φ : X → Y` separated (resp. quasi-separated) with `Y` affinoid, the
   intersection of two affinoid opens of `X` is affinoid (resp. quasi-compact) (Bosch 1.16/4);
   separatedness is stable under base change, composition and fibre products; the diagonal is
   always a locally closed immersion; and the criterion BGR 9.6.1/3 and 9.6.1/7 (Bosch 1.16/5):
   separated iff quasi-separated with the diagonal's image an analytic subset.
3. Relative compactness (BGR 9.6.2; Bosch 1.16/6): for `X` over an affinoid `Y`, `U ⋐_Y U'` for
   affinoid opens `U ⊆ U'` when some affinoid generating system of `𝒪_X(U')` over `𝒪_Y(Y)` has
   `|fᵢ| < 1` on `U`, equivalently `U ⊆ U'(ε⁻¹f)` for some `ε < 1` in `√|K^×|`. Prove the
   stability properties Bosch 1.16/7 (products, fibre products, intersections under
   separatedness).
4. **Proper morphisms** (BGR 9.6.2; Bosch 1.16/8): separated, with an admissible affinoid covering
   `(Yᵢ)` of `Y` and, over each `Yᵢ`, two finite admissible affinoid coverings `(Xᵢⱼ)`, `(X'ᵢⱼ)` of
   `φ⁻¹(Yᵢ)` with `Xᵢⱼ ⋐_{Yᵢ} X'ᵢⱼ`. Prove that proper morphisms are quasi-compact, stable under
   base change and under fibre products over `Y`, and that finite morphisms are proper. ⚠ The
   composite of proper morphisms being proper is not asked for (Bosch 1.16, the remark after 1.16/8:
   it is difficult in this generality and is a theorem of the formal-model theory), and nothing
   here depends on it.

### 7.4 Čech and sheaf cohomology on rigid varieties

1. Define the Čech cohomology `Ȟ^q(X, F) = colim_𝔘 H^q(𝔘, F)` over admissible coverings (BGR
   9.2.2; Bosch 1.15) and the canonical maps `Ȟ^q(X, F) → H^q(X, F)` to Mathlib's sheaf cohomology
   `Sheaf.H` of the site of §6.1.2; prove they are isomorphisms for `q = 0, 1` and injective for
   `q = 2` (Bosch 1.15, the remarks before 1.15/5).
2. **Leray's theorem on a site** (Bosch 1.15/5; Stacks 03F7): for an admissible covering `𝔘` and
   a sheaf `F` with `H^q(U, F) = 0` for `q > 0` on every finite intersection `U` of members of `𝔘`,
   the map `H^q(𝔘, F) → H^q(X, F)` is an isomorphism. ⚠ This is new for Mathlib's `Sheaf.H`; prove
   it by dimension shifting with injective sheaves, whose Čech cohomology on every covering
   vanishes, or by the Čech-to-derived spectral sequence if that is built first; state which.
3. **Cartan's criterion** (Bosch 1.15/6; BGR 9.2.2): for a system `𝔖` of admissible opens stable
   under intersection, cofinal among refinements, and with `Ȟ^q(U, F) = 0` for `q > 0` and
   `U ∈ 𝔖`, the maps `Ȟ^q(X, F) → H^q(X, F)` are isomorphisms for all `q`.
4. **Theorem B for affinoid varieties** (Bosch 1.15/7; BGR 9.2.2): `H^q(X, 𝒪_X) = 0` and
   `H^q(X, M ⊗_A 𝒪_X) = 0` for `q > 0`, `X` affinoid, `M` any `A`-module, from Tate's theorem and
   items 2–3 with `𝔖` the affinoid subdomains.

### Examples

`𝒪(𝔹¹)`-modules associated to `K⟨X⟩/(X)`, to `K⟨X⟩²`, and to the ideal `(X)`; the skyscraper at a
point as a coherent module; the structure sheaf of the open disc is not associated to a finite
module over any affinoid algebra; the closed subvariety `V(XY − c)` of `𝔹²`; the diagonal of
`ℙ^{1,rig}`; the open disc is not quasi-compact; the inclusion of the disc of radius `|c|` into the
unit disc is relatively compact; `ℙ^{n,rig}` is proper and `𝔸^{n,rig}` is not; `H¹(ℙ^{1,rig}, 𝒪) = 0`
by the two-disc covering.

### Dependencies

Layers 4–6; Mathlib's `Sheaf.H` and sheafification; the adic-spaces roadmap for nothing new.

---

## Layer 8: the GAGA functor and the comparison with adic spaces

References: Bosch 1.13 (analytification; BGR 9.3.4 has the examples only); Huber [Hu2] §4, [Hu3]
(1.1.11); Wedhorn §§7.4–7.6 and Example 7.57.

### 8.1 Analytification

1. **The affine case** (Bosch 1.13/1–3). For `Z = Spec C` with `C = K[ζ₁, …, ζₙ]/𝔞` of finite type
   over `K`, define `Z^{rig}` as the union of the affinoid varieties `Sp(T_n^{(i)}/𝔞 T_n^{(i)})`,
   `T_n^{(i)} = K⟨c^i ζ⟩` for a fixed `|c| > 1`, glued along the inclusions; prove the inclusions
   `Max T_n^{(i)} ⊆ Max T_n^{(i+1)}` with union `Max K[ζ]` (Bosch 1.13/1), that `Z^{rig}` is
   independent of `c` and of the presentation, and that it comes with a morphism of locally
   G-ringed spaces `ι : Z^{rig} → Z` (`Z` with its Zariski topology, Mathlib's `Scheme`) such that
   morphisms of locally G-ringed spaces `Y → Z` from a rigid variety correspond to `K`-algebra maps
   `C → 𝒪_Y(Y)` (Bosch 1.13/2), through Mathlib's `ΓSpec.adjunction` on the scheme side. Deduce the
   universal property: every morphism `Y → Z` from a rigid variety factors uniquely through `ι`.
2. **The general case** (Bosch 1.13/4–5): every `K`-scheme locally of finite type
   (`LocallyOfFiniteType (Z ⟶ Spec K)`) has an analytification, built by pasting the affine ones
   over an affine open cover, with the universal property; analytification is a functor from
   `K`-schemes locally of finite type to rigid varieties, and it is **not** fully faithful (record
   Bosch's remark). Prove: the points of `Z^{rig}` are the closed points of `Z`, with the same
   residue fields; `ι` is injective on points, continuous for the Zariski topology, and flat on
   stalks (`𝒪_{Z,z} → 𝒪_{Z^{rig},z}` induces an isomorphism on completions, from §4.4.2);
   analytification commutes with fibre products, open and closed immersions, and preserves
   separatedness and finiteness.
3. Identify `(𝔸ⁿ_K)^{rig} = 𝔸^{n,rig}` and `(ℙⁿ_K)^{rig} = ℙ^{n,rig}` with the constructions of
   §6.5, and prove `Z^{rig}` is quasi-compact when `Z` is proper over `K`, through Chow's lemma or
   directly for projective `Z` (the proper case of Köpf's theorem is out of scope; quasi-compactness
   is all that is claimed).

### 8.2 Affinoid varieties inside adic spectra

1. **The affinoid algebra as a Huber pair.** For `A` affinoid with its affinoid topology, prove
   that `A` is a complete Hausdorff Tate ring with ring of definition the unit ball of a residue
   norm and pseudouniformiser any `c ∈ K` with `0 < |c| < 1` (adic §0.2; `p`-adic-functional-analysis
   §0.4.5 is the normed form), that `A°` (`TauCeti.Huber.powerBoundedSubring`) is `Å` of §2.3.1, that
   `(A, A°)` is a Huber pair, and that `A` is strongly noetherian (§5.3.1). Prove that `A` is
   uniform iff reduced (§2.3.5), hence stably uniform when reduced since rational localisations of
   reduced affinoid algebras are reduced (§4.4.4 and §4.2.2), which is the Buzzard–Verberkmoes
   hypothesis of the adic-spaces roadmap's §4.2.
2. **Classical points.** For `x ∈ Sp A` define `v_x : A → ℝ≥0`, `f ↦ |f(x)|`, prove it is a
   continuous rank-one valuation with support `x`, at most one on `A°`, hence a point of
   `Spa(A, A°)` (Tau Ceti's `spa (powerBoundedSubring A)`), and that `x ↦ v_x` is injective. For
   `A = Tₙ` prove it agrees with `TauCeti.ValuationSpectrum.classicalPoint` at `K`-rational points
   and that the Gauss point `gaussPoint` is not classical (Tau Ceti's `gaussPoint_ne_classicalPoint`),
   so the map is not surjective (Wedhorn, Example 7.57: the five kinds of points of the unit disc,
   of which the classical ones are the first).
3. Characterise the image: a point of `Spa(A, A°)` is classical iff its support is a maximal ideal
   iff it has rank one with residue field finite over `K` (Wedhorn 7.57 for the disc; in general
   from §1.2.4 and the uniqueness of the extension of the valuation of `K` to a finite extension).
4. **Rational subdomains and rational subsets.** For `f₁, …, fₘ, g ∈ A` generating the unit ideal,
   the preimage of the rational subset `R({f, g}/g) ⊆ Spa(A, A°)` under `x ↦ v_x` is the rational
   domain `X(f/g) ⊆ Sp A`; the coordinate rings agree (§1.4.3); and the classical points of
   `Spa(A⟨f/g⟩, A⟨f/g⟩°)` are the classical points of `Spa(A, A°)` lying in `R(T/s)` (Tau Ceti's
   `spaCompletedLocalizationHomeomorph` composed with item 2). Prove the same for Weierstrass and
   Laurent domains through their rational presentations (§4.2.3).
5. **The covering criterion.** A finite family of rational domains `X(f^{(i)}/g^{(i)})` covers
   `Sp A` iff the corresponding rational subsets cover `Spa(A, A°)`. Prove: for a standard rational
   covering generated by `f₁, …, fₙ`, both sides are equivalent to `(f₁, …, fₙ) = A` — on the rigid
   side by the Nullstellensatz (§3.2.2; BGR 7.1.2/5), on the adic side by Wedhorn's Corollary 7.53
   (`span_eq_top_iff_spa_eq_biUnion_rationalSubset`); for a general finite rational family, refine
   it on the rigid side by a standard rational covering (BGR 8.2.2/2, whose refinement is built from
   the presentation data and covers `Spa(A, A°)` as well), and use that `Sp A` is a subset of
   `Spa(A, A°)` for the converse. Extend to finite affinoid coverings through Gerritzen–Grauert.
6. **The Čech complexes agree.** For a finite rational covering, the Čech complex of `𝒪_X` of §5.1
   is the Čech complex of the adic-spaces roadmap's structure presheaf on the corresponding rational
   cover of `Spa(A, A°)`, compatibly with the identifications of items 4–5; hence Tate acyclicity
   on either side gives it on the other for rational coverings, and the adic-spaces roadmap's
   all-degrees Čech exactness (its §4.1, Wedhorn 8.28) is equivalent for affinoid `A` to §5.3.3
   restricted to rational coverings. Record both directions; §5.3 uses only the two-piece Laurent
   case in the direction adic → rigid.
7. The G-topology and the adic topology: an admissible open of the strong G-topology on `Sp A`
   is the trace on `Sp A` of an open subset of `Spa(A, A°)`, admissible coverings correspond to
   open coverings, and `𝒪_X(U)` is the adic structure presheaf's value on the corresponding open
   (Huber [Hu2] §4; Wedhorn §8.1 for the presheaf). Prove it for admissible opens that are finite
   unions of rational domains and deduce the general case from the definition of the strong
   G-topology.

### 8.3 The functor from rigid varieties to adic spaces

1. For an affinoid variety `X = Sp A` define `r(X) = Spa(A, A°)` with the adic-spaces roadmap's
   structure presheaf (its §3.3, which is a sheaf by §8.2.1 and its §4.1 or §4.2), an affinoid adic
   space over `Spa(K, K°)` (its §5); prove that affinoid maps induce morphisms of adic spaces, that
   `r` is fully faithful on affinoid varieties (Wedhorn's Lemma 8.1 in Tau Ceti,
   `existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset`, and §1.3.2), and that it
   carries affinoid subdomains to open affinoid subspaces (§8.2.4 and §4.6.3).
2. Extend `r` to rigid varieties by pasting (§6.4.4 and the adic-spaces roadmap's §5.3): prove the
   G-topology of `X` and the topology of `r(X)` correspond as in §8.2.7, that `r` is a functor into
   adic spaces over `Spa(K, K°)`, and that it is **fully faithful** (Huber [Hu2] §4; [Hu3] (1.1.11)).
   The essential image is not characterised here; [Hu3] (1.1.11) states it.
3. Prove that `r` carries the open disc to the adic open disc of the adic-spaces roadmap's §5.4,
   `𝔸^{n,rig}` and `ℙ^{n,rig}` to the adic affine and projective spaces, and fibre products to fibre
   products whenever the adic side has them (it is not asked to construct them: the adic-spaces
   roadmap excludes fibre products of adic spaces, and this item is stated for the affinoid case
   only, where `Spa(B₁ ⊗̂_A B₂, ·)` is the fibre product by the universal property).

### Examples

`Sp ℚ_p⟨X⟩` inside `Spa(ℚ_p⟨X⟩, ℤ_p⟨X⟩)`: the classical point at `a ∈ ℤ_p` and the Gauss point
`η_1`; the rational domain `{|X| ≤ |p|}` and the rational subset `R({X, p}/p)` with coordinate ring
`ℚ_p⟨X, X/p⟩ ≅ ℚ_p⟨Y⟩`; the standard covering generated by `X, p` covers both spectra; the
analytification of `𝔸¹_{ℚ_p}` and its adic image; `(Spec ℚ_p[X]/(X² + 1))^{rig}` is one point with
residue field `ℚ_p(i)` when `−1` is not a square in `ℚ_p` (`p ≡ 3 mod 4`) and two `ℚ_p`-rational
points when it is (`p ≡ 1 mod 4`).

### Dependencies

Layers 1–7; the adic-spaces roadmap Layers 0–5 (§§0.2, 0.5, 2.1–2.4, 3.1–3.3, 4.1–4.2, 5.1–5.4);
Mathlib's schemes.

---

## Dependency graph

```text
Layer 0 → Layer 1 → Layer 2 → Layer 3 → Layer 4 → Layer 5 → Layer 6 → Layer 7
                                                                    ↘
                                                        Layer 8 (uses Layers 1–7 and the adic-spaces roadmap)
```

Layer 0 depends on the floor of convention 2 (the adic-spaces roadmap's §0.5, or mathlib4#42867)
and on the `p`-adic-functional-analysis roadmap's §0.2 and §2.2; the characteristic-`p` half of its
§0.4 also on that roadmap's §2.4. Layer 5 depends on the adic-spaces roadmap's §4.1 at exactly one point, §5.3.1.
Layer 8 depends on the adic-spaces roadmap's Layers 0–5 throughout and on nothing after Layer 7
here. The Newton-polygons roadmap is cited for the one-variable Gauss norm at every radius (§0.1,
§1.5). No layer depends on Layer 8.

## Acceptance examples

The following should be proved alongside the general theory, and they are the things a reviewer
should check are present. All are over `K = ℚ_p` unless stated.

- `|1 + pX| = 1` and `|p + X²|_sup = 1` in `T₁`, attained at `x = 𝔪_0`; the reduction of
  `p + X + pX²` is `X`; and `T̃₂ = 𝔽_p[X₁, X₂]`.
- Noether normalisation of `K⟨X, Y⟩/(Y² − X³)` by `K⟨X⟩` and of `K⟨X, Y⟩/(XY − p)` by `K⟨X + Y⟩`
  after the chart `X ↦ X + Y^t`; `dim K⟨X, Y⟩/(XY − p) = 1`.
- The residue field of the maximal ideal `(X² − p)` of `T₁` is `ℚ_p(√p)`, and `|X(x)| = p^{−1/2}`.
- `K⟨X⟩/(X²)`: `ε` has supremum seminorm `0` and residue norm `1`; the algebra is not reduced, not
  uniform, and its supremum seminorm is not a norm.
- `K⟨X, Y⟩/(XY − c)` with `0 < |c| < 1` is a domain whose supremum seminorm is not multiplicative:
  `|X|_sup = |Y|_sup = 1` and `|XY|_sup = |c|`.
- In `𝔹¹ = Sp K⟨X⟩`: `{|X| = 1}` is Laurent and not Weierstrass; `{|X| ≤ |c|}` is Weierstrass;
  BGR's rational domain that is not Laurent; the Gerritzen–Grauert decomposition of an explicit
  affinoid subdomain that is not rational.
- The Laurent covering `{|X| ≤ |c|} ∪ {|X| ≥ |c|}` of `𝔹¹`: the explicit exact sequence
  `0 → K⟨X⟩ → K⟨c⁻¹X⟩ × K⟨X, cX⁻¹⟩ → K⟨c⁻¹X, cX⁻¹⟩ → 0`, and its agreement with Tau Ceti's
  `laurentCover_exact` for `f = c⁻¹X`.
- The covering of `𝔹¹` by `{|X| < 1}` and `{|X| = 1}` is not admissible and not acyclic.
- `ℙ^{1,rig}`: glued from two discs, admissibly covered by them, with `𝒪(ℙ^{1,rig}) = K` and
  `H¹(ℙ^{1,rig}, 𝒪) = 0`; `(ℙ¹_K)^{rig} = ℙ^{1,rig}`; `𝔸^{1,rig}` is not quasi-compact.
- The classical points of `Spa(ℚ_p⟨X⟩, ℤ_p⟨X⟩)` are the points of `Sp ℚ_p⟨X⟩`, the Gauss point is
  not one of them, and the rational subset `R({X, p}/p)` meets the classical points in
  `{|X| ≤ |p|}`.
- The standard rational covering generated by `X, p` covers `Sp ℚ_p⟨X⟩` and `Spa(ℚ_p⟨X⟩, ℤ_p⟨X⟩)`;
  the family `{X(X/p)}` alone covers neither.

## Beyond this roadmap

⚠ **This section is a roadmap-for-a-roadmap. Do not attempt any of it here.** It records what this
roadmap is for, so that the conventions above are chosen with the sequel in mind.

The direct image theorem of Kiehl (coherence of `R^qφ_*F` for proper `φ`), the theorem on formal
functions and the GAGA comparison theorems (BGR 9.6.3; Bosch 1.16–1.17) rest on the theorem of
Schwarz on completely continuous perturbations of surjections between Banach modules over an
affinoid algebra (Bosch 1.17/3–4), which is the compact-operators roadmap's §0.1 and §3 in the
affinoid setting; a roadmap for them would consume Layers 6–7 here and that roadmap. Formal models,
Raynaud's generic fibre, admissible blowing-ups and the reduction theory of BGR 6.3–6.4, 7.1.5 and
7.2.6 are a formal-and-rigid-geometry roadmap, whose rigid side is this one. Berkovich spaces and
the Shilov boundary, dagger spaces, and étale cohomology of rigid varieties each want this roadmap's
affinoid algebras and Layer 8's comparison as their starting point.

Closest to home, the spectral variety `{det(1 − T·U) = 0} ⊆ 𝒲 × 𝔸¹` of the compact-operators and
overconvergent-forms roadmaps, the rigid-analytic weight space with its affinoid subdomains, and the
eigencurve glued from finite-slope pieces (Buzzard's *Eigenvarieties* §§4–5, Coleman–Mazur,
Johansson–Newton §2.3) are rigid varieties over `ℚ_p` built from affinoid algebras over affinoid
subdomains of weight space; the `p`-adic-functional-analysis roadmap's §5.6 halo ring and the
spectral-halo roadmap's `Λ^{>1/p}[1/T]` are the coordinate rings of the relevant admissible opens.
What they ask of this roadmap is that affinoid algebras over an arbitrary complete `K` carry their
supremum seminorm and uniformity (Layer 2), that rational subdomains and finite coverings be
available with Tate acyclicity (Layers 4–5), and that gluing produce rigid varieties with a
comparison to adic spaces (Layers 6 and 8). All of that is specified above.

## References

- S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis. A Systematic Approach to Rigid
  Analytic Geometry*, Grundlehren 261, Springer (1984) — [BGR]. The primary source: Chapter 5 for
  Layer 0 (5.1, 5.2.3–5.2.7, 5.3.1), Chapter 6 for Layers 1–2, Chapter 7 for Layers 3–4, Chapter 8
  for Layer 5, Chapter 9 for Layers 6–8; and Part A as cited (3.5, 3.7.5, 3.8). Statements are
  keyed `section/number`, e.g. `BGR 6.1.2/3`.
- S. Bosch, *Lectures on Formal and Rigid Geometry*, Lecture Notes in Mathematics 2105, Springer
  (2014); the preprint version *State: April 2008*, Münster SFB 478, Heft 378 — [Bosch]. Part 1
  (1.1–1.17) follows BGR's route with shorter proofs and is the second source for Layers 1–7,
  keyed `section/number` to the preprint's numbering, e.g. `Bosch 1.6/9`. ⚠ The published book
  renumbers sections (its Chapter 2–6 are the preprint's 1.1–1.17); check before transcribing.
- J. Tate, *Rigid analytic spaces*, Invent. Math. 12 (1971), 257–289 — the original, for the
  acyclicity theorem and the definition of rigid spaces.
- L. Gerritzen and H. Grauert, *Die Azyklizität der affinoiden Überdeckungen*, in *Global Analysis,
  Papers in Honor of K. Kodaira*, Univ. Tokyo Press (1969), 159–184 — the Gerritzen–Grauert theorem.
- R. Kiehl, *Theorem A und Theorem B in der nichtarchimedischen Funktionentheorie*, Invent. Math. 2
  (1967), 256–273, and *Der Endlichkeitssatz für eigentliche Abbildungen in der nichtarchimedischen
  Funktionentheorie*, Invent. Math. 2 (1967), 191–214 — Kiehl's theorem (§7.1) and the direct image
  theorem (out of scope).
- J. Fresnel and M. van der Put, *Rigid Analytic Geometry and Its Applications*, Progress in
  Mathematics 218, Birkhäuser (2004) — [FvdP]; Chapters 3–4 are a third account of Layers 1–7 and
  the source of several examples.
- B. Conrad, *Several approaches to non-archimedean geometry*, in *p-adic Geometry: Lectures from
  the 2007 Arizona Winter School*, AMS (2008), 9–63 — the comparison of the rigid, Berkovich and
  adic viewpoints, for Layer 8.
- R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217 (1994),
  513–551 — [Hu2], §4: the functor from rigid varieties to adic spaces. R. Huber, *Étale cohomology
  of rigid analytic varieties and adic spaces*, Vieweg (1996) — [Hu3], (1.1.11): its full
  faithfulness and essential image. The keys `[Hu2]`, `[Hu3]` are the adic-spaces roadmap's, which
  are shifted by one against Wedhorn's bibliography; see that roadmap's note.
- T. Wedhorn, *Adic Spaces*, arXiv:1910.05934, v1 — [Wedhorn], §§5–8 as the adic-spaces roadmap
  cites them, and Example 7.57 for the points of the unit disc.
- K. Kedlaya, *Sheaves, shtukas, and the adic Fargues–Fontaine curve* / 18.727 notes
  `https://kskedlaya.org/18.727/tate-acyclic.pdf` — a modern proof of Tate acyclicity, consulted for
  §5.3.
- Stacks Project, Tag 03F7 (Čech cohomology computes cohomology for acyclic coverings) and
  Tag 00OW (Noether normalisation), for §7.4.2 and the shape of §1.2.1.
- M. Temkin, *A new proof of the Gerritzen–Grauert theorem*, Math. Ann. 333 (2005), 261–269 — an
  alternative route to §4.6, by reduction of germs; not the route specified.

⚠ **Two numberings of Bosch.** This roadmap keys Bosch's *Lectures* to the 2008 preprint, whose
Part 1 is "1. Classical Rigid Geometry" with sections 1.1–1.17; the LNM 2105 edition splits it into
chapters. When transcribing from the book, locate the statement by its content, not by the preprint
number.

## Existing Lean work

The principal source of existing code is `github.com/WilliamCoram/PhD` (Apache-2.0), at commit
`7586051` (2026-09-17): the directories `PhD/Main/ForMathlib/RingTheory/MvPowerSeries/Restricted/`
and `PhD/Main/ForMathlib/RingTheory/PowerSeries/Restricted/` for Layer 0 and §1.5, the files
`PhD/Main/ForMathlib/Analysis/Normed/Ring/{PowerBounded,TopologicallyNilpotent}.lean` and
`PhD/Main/ForMathlib/Topology/Algebra/{Bounded,PowerBounded,TopologicallyNilpotent}.lean` for
§2.3, and `PhD/Main/TateFredholm/04_TateAlgebra.lean` for the identification of `K⟨X⟩` with the
model space `c₀(ℕ, K)`. The existing material in those directories is by William Coram, who has
agreed to its integration into Tau Ceti. ⚠ The wider repository also contains files by other
authors, derived from the FLT project and from Mathlib; those are not migration sources for this
roadmap, and the provenance of anything copied must be checked file-by-file rather than
directory-by-directory.

The other formalisations known to us are these. None treats affinoid algebras over a field in BGR's
sense, the supremum seminorm, affinoid subdomains, G-topologies or rigid varieties.

- Tau Ceti itself, at commit `96f3a42` (2026-09-30): the adic-spaces roadmap's Layers 0–4 as
  recorded in its generated `STATUS.md` at `759eb3e` (2026-09-26) — Huber and Tate rings, weighted
  and plain restricted series, the one-variable Weierstrass theory and noetherianity, rational
  localisation with its presentations, `Spa` with its rational basis and spectrality, the structure
  presheaf, Wedhorn 7.52–7.54, 8.1, 8.2, 8.29–8.33, the closed polydisc with its classical and Gauss
  points, uniformity and stable uniformity. This is the material Layers 0, 1, 5 and 8 cite; it is
  consumed, not migrated.
- AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), project `projects/AdicSpaces/`, the
  adic-spaces roadmap's migration source: Wedhorn's theory, including `TateAlgebra.lean`,
  `TateAlgebraTopology.lean`, `MvTateAlgebraTopology.lean`, `AffinoidRings.lean` (Huber's affinoid
  rings, i.e. Huber pairs — not BGR's affinoid algebras) and `TateAcyclicity.lean` (the strongly
  noetherian Laurent-cover statement). Nothing there is a migration source for this roadmap.
- `github.com/leanprover-community/lean-perfectoid-spaces` (Lean 3; Buzzard–Commelin–Massot,
  *Formalising perfectoid spaces*, arXiv:1910.12320): Huber pairs, `Spa`, rational opens and the
  structure presheaf on them. Lean 3, superseded by Tau Ceti's adic chain.
- Mathlib's `Mathlib/Analysis/Normed/Unbundled/` (M. I. de Frutos-Fernández, *Formalizing norm
  extensions and applications to number theory*, ITP 2023): BGR 1.2.1/2, 1.3.2/1–2, 3.1.2/1, 3.1.5/1,
  3.2.1/2–3, 3.2.4/2, consumed by Layer 2.
- Mathlib's `Mathlib/RingTheory/{MvPowerSeries,PowerSeries}/{Restricted,GaussNorm}.lean`
  (W. Coram): the Tate algebra as a subring and the Gauss norm as a function, consumed by Layer 0.

Two separate audits are recorded below, for the reason the adic-spaces roadmap gives: a declaration
with no direct `sorry` is not the same as a theorem whose dependency cone is axiom-clean. The direct
column is a file-level `grep` count, which over-counts (comments match) and sees no cross-file
dependence. At the pin above, every file listed has a direct count of **0**. The transitive column
must be regenerated at migration by a `#print axioms` gate on the capstones in Tau Ceti CI; the
source project reports every directory listed clean on `propext`, `Classical.choice` and
`Quot.sound`, and that claim is to be re-verified, not carried over.

| Roadmap section | Existing source | Direct status at the pin | Transitive status | Roadmap status |
|---|---|---|---|---|
| §0.1.1 Gauss norm as a normed ring, attainment at a dominant index | `MvPowerSeries/Restricted/GaussNorm.lean` (`gaussNormRingNorm`, `exists_achievesGaussNorm_dominant`, `NormMulClass`) | no direct `sorry` | audit required | present, at every polyradius |
| §0.1.2 reduction `T̃ₙ = K̃[X]` | `MvPowerSeries/Restricted/Residue.lean` (`residueRingHom`, `residueEquiv`), `PowerSeries/Restricted/Residue.lean` | no direct `sorry` | audit required | present for the ball ideals of any multiplicatively normed ring; the going up/down statements are new |
| §0.1.2, §2.3.1–2 power-bounded and topologically nilpotent elements | `MvPowerSeries/Restricted/{PowerBounded,PowerBoundedIso,TopologicallyNilpotentIso}.lean`, `Analysis/Normed/Ring/{PowerBounded,TopologicallyNilpotent}.lean`, `Topology/Algebra/{Bounded,PowerBounded,TopologicallyNilpotent}.lean` | no direct `sorry` | audit required | present for `Tₙ` and `T_{n,ρ}` coefficientwise; mathlib4#40013 is the same material |
| §0.1.4 units of `Tₙ` | `MvPowerSeries/Restricted/Units.lean` (`isUnit_iff`) | no direct `sorry` | audit required | present |
| §0.2.1–2 Weierstrass over a Banach algebra | `MvPowerSeries/Restricted/MulWeierstrass.lean`, `PowerSeries/Restricted/{MulDistinguished,MulWeierstrassDivision,MulWeierstrassPrep}.lean` (Martin's `IsMulDistinguished`) | no direct `sorry` | audit required | present as division and preparation by a multiplicatively distinguished series over any complete ultrametric normed ring; the finiteness theorem and charts are new |
| §0.2.1 `Tₙ = T_{n−1}⟨Xₙ⟩` | `MvPowerSeries/Restricted/Iso.lean` (`finSuccEquiv`, `finSuccIsometry`) | no direct `sorry` | audit required | present, as an isometry |
| §1.5 polydiscs of arbitrary polyradius | `MvPowerSeries/Restricted/{Basic,Complete,GaussNorm}.lean` (`Restricted R c`) | no direct `sorry` | audit required | present (`T_{n,ρ}` as a Banach algebra); the affinoid criterion is new |
| §1.1.3, §5.1 `K⟨X⟩` as the model space | `TateFredholm/04_TateAlgebra.lean` (`restrictedEquivCSpace`) | no direct `sorry` | audit required | present; consumed by the `p`-adic-functional-analysis roadmap |
| §0.3–0.4, Layers 1–8 otherwise | — | — | — | new |

⚠ **Do not treat the existing file layout as prescriptive.** The source code is organised around a
type synonym `Restricted R c` for the subring at a polyradius with its own `NormedRing` instance,
and around Martin's multiplicative distinguishedness, which is more general than BGR's over a field;
conventions 2 and 3 keep Mathlib's subring and the field case as the primary objects. The migration
is expected to restate the Gauss-norm and reduction results on Mathlib's `IsRestricted.subring`,
not to port the synonym.
