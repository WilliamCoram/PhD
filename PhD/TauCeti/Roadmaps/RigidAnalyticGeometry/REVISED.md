# Rigid analytic geometry revised roadmap

This roadmap develops the classical algebra of rigid analytic geometry over a complete,
nontrivially valued nonarchimedean field, following Bosch–Güntzer–Remmert (BGR), and connects it
to the geometry supplied by the Tau Ceti adic-space programme. The local implementation owns
Layers 0–2 in full, the general G-topological formalism, and the compatibility results needed
to use that algebra and formalism with the upstream geometry. Affinoid and global geometric
theorems in Layers 3–8 are requirements on the upstream interfaces, rather than a second
independent implementation programme.

The principal algebraic milestones are Noether normalisation, the maximum modulus principle,
the spectral description of power-bounded elements, and the Banach function algebra theorem
for reduced affinoids. The geometric milestones consumed from upstream are
Gerritzen–Grauert, Tate acyclicity, Kiehl's affinoid equivalence and proper mapping theorem,
analytification, proper GAGA, and the rigid–adic comparison.

**Status:** proposed roadmap, 13 October 2026. The original roadmap and its `Suggested.lean`
remain separate historical specifications. [CHANGES.md](CHANGES.md) records the comparison,
including the treatment of issue #18 and the additions in #20. The ownership below is a
proposed division of implementation work; it does not assert that upstream maintainers have
already changed their roadmaps or supplied all the required declarations.

## Scope and ownership

| Layer | Work owned here | Geometry or common infrastructure supplied upstream |
|---|---|---|
| 0 Tate algebras | Gauss norm and reduction, evaluation and maximum modulus, Weierstrass finiteness and charts, Rückert theory, strict closedness, weak stability, Japaneseness | AdicSpaces §0.5 supplies the common restricted-series and Weierstrass foundations; Part II R0.9 consumes the classical results |
| 1 Affinoid algebras | Presentations, finite extensions, Noether normalisation, automatic continuity, quotient and tensor presentations, generalised fractions, arbitrary polyradii | Part II R0.1–R0.3 supplies the general topological-ring and completed-tensor framework; R0.9 consumes the classical algebra |
| 2 Supremum seminorm and reduction | The full BGR algebraic programme, including the finite-reduction and integrality requirements below | Part II R0.4 and R0.9 supply or consume the corresponding general spectral and Huber-ring interfaces |
| 3 Affinoid varieties | Algebra-to-spectrum compatibility and examples | Part II R1.1 and R1.9 |
| 4 Affinoid subdomains | Identification of the explicit fraction algebras with upstream coordinate rings | Part II R1.1, R0.8 and R0.13 |
| 5 Čech theory and acyclicity | Comparison of complexes and transfer to the classical G-site; reusable site lemmas only where missing | Part III R3.1, with the existing AdicSpaces Laurent-cover theory |
| 6 G-topologies and rigid varieties | General G-topologies, enhancement, pasting and sheaf comparison in §§6.1–6.3 | Part II R1.1 and R1.7 supply rigid spaces, gluing and the rigid–adic comparison |
| 7 Coherent modules and proper maps | Classical formulations transported through the specified comparisons | Part III R3.2–R3.6; Part II R0.10–R0.13 and R1.9 |
| 8 Analytification and GAGA | Compatibility statements on sections, cohomology and the algebraic interfaces | Part II R1.3–R1.7 and R1.9; Part III R3.7; Part IV R4.4–R4.5 for site comparisons |

An overlap in mathematical scope is not a request for two proofs. A theorem already proved in
the PhD algebra chain should be integrated once, then exposed through the classical and adic
interfaces by comparison lemmas. General Huber-ring results belong to the adic programme;
their specialisations to classical affinoids are consumed here. The several-variable
polyradius theory and the full BGR weak-stability and Japanese-ring arguments remain local
work even when an adic consumer needs only a smaller consequence.

Formal models, Raynaud's generic fibre, admissible blow-ups and their reduction theory belong
to Part III. Dagger geometry and the étale and pro-étale developments belong to their upstream
roadmaps. Eigenvarieties, weight spaces, spectral varieties, and Tate or Mumford curve
uniformisation are downstream applications. General Banach-module analysis and compact
operators remain in the coordinated functional-analysis roadmaps.

## Mathematical and Lean conventions

1. **Ground field.** Use `[NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]`.
   There is no blanket assumption of characteristic zero, discrete valuation, algebraic
   closedness or spherical completeness. A theorem currently proved only with `[CharZero K]`
   retains that hypothesis until its missing input is supplied. Write
   `√|K×| = {r > 0 : ∃ n ≥ 1, rⁿ ∈ |K×|}` for the divisible closure of the value group.

2. **Tate algebra.** `Tₙ = K⟨X₁,…,Xₙ⟩` is restricted multivariate power series at unit
   polyradius with the Gauss norm. The current implementation uses
   `MvPowerSeries.Restricted K (1 : Fin n → ℝ)` and `Affinoid.TateAlgebra K n`.
   Reuse this carrier and its proved API; transport it to the selected Mathlib or Tau Ceti
   carrier by a canonical topological algebra equivalence where necessary. In the existing
   iteration API the distinguished variable is `X 0`, not BGR's last variable.

3. **Affinoidness and topology.** `IsAffinoidAlgebra K A` is the proposition that a Tate
   algebra admits a surjective `K`-algebra map to `A`. In the current implementation it is a
   definition used through an explicit hypothesis, not the class in the historical skeleton.
   A presentation gives a residue norm; automatic continuity makes the resulting complete
   algebra topology independent of presentation. Keep norm choices separate from affinoidness.
   Statements comparing norms quantify over suitable complete nonarchimedean algebra norms.

4. **Points and values.** Classical points are `MaximalSpectrum A`. For a maximal ideal `x`,
   `|f(x)|` is the unique extension of the norm of `K` to the finite residue field, evaluated
   on the image of `f`. Use the existing spectral-value construction; no embedding in an
   algebraic closure is chosen. Finiteness of residue fields is an algebraic input from §1.2,
   not a dependency on a category of rigid spaces.

5. **Supremum and the zero algebra.** Define `|f|sup = ⨆ x : MaximalSpectrum A, |f(x)|`,
   with value zero on the zero algebra. Boundedness must be established before using real
   supremum lemmas. Maximum attainment requires `A ≠ 0`. Power multiplicativity holds for
   positive powers on every affinoid; the exponent-zero statement requires `A ≠ 0`.
   Never infer a multiplicative norm merely from reducedness or integrality of the ring.

6. **Integral elements and reduction.** `A°` denotes the power-bounded subring,
   `A°°` its ideal of topologically nilpotent elements, and `Ã = A°/A°°`.
   On affinoids these are characterised by `|a|sup ≤ 1` and `|a|sup < 1`.
   The comparison with `Spa(A,A°)` uses the canonical plus ring and includes nonreduced
   affinoids. Uniformity is an additional consequence for reduced affinoids, not a replacement
   for the strongly noetherian route to sheafiness in the nonreduced case.

7. **Fractions and subdomains.** Rational fractions use
   `A⟨f/g⟩ = A⟨T₁,…,Tₘ⟩/(gTᵢ − fᵢ)` with `(f₁,…,fₘ,g) = A`.
   This hypothesis ensures that `g` becomes invertible. Pointwise rational domains include
   `|g(x)| ≠ 0`; it follows from the unit-ideal hypothesis when all numerator inequalities
   hold. Compare quotient and completed-localisation models as topological `A`-algebras,
   compatibly with their structure maps. An arbitrary pair of presentation norms need not
   make the comparison an isometry.

8. **Sites and modules.** A G-topology is a coverage on admissible subsets with the BGR
   axioms. Use Mathlib's Grothendieck topologies, sheaves, module sheaves, sheafification and
   sheaf cohomology. Čech cohomology computes sheaf cohomology only after the appropriate
   acyclicity comparison. A morphism of rigid spaces includes its local map of structure
   sheaves and its `K`-structure. There is one geometric category supplied upstream; the
   classical G-site is related to it by proved comparisons.

9. **Dependencies.** Production algebra modules do not depend on roadmap theorem stubs.
   Respect the repository boundary: `PhD.TauCeti.*` and `PhD.Main.*` never import each other.
   Code under `PhD/Main/` is a provenance source for restatement, not an import path for
   the Tau Ceti chain. Reuse existing Mathlib and Tau Ceti results before adding new ones.

## Current implementation and outstanding algebra

The baseline is PhD commit `eefb3d91f34b27d0bc7822140fa85fecae029884`, with Mathlib
`bbc4475e9e8fd25fbc8e26d636dd8b37be8f105a` and Lean `v4.33.0-rc1`.
The source prefix in this table is `PhD/TauCeti/Code/RigidAnalyticGeometry/`.
“Present” identifies existing source, not a new build or transitive axiom audit.

| Programme | Existing source | Work still required for the full target |
|---|---|---|
| Restricted series and Tate algebra, §§0.1–0.3 | `Restricted/`, `TateAlgebra/{Basic,Reduction,MaxModulus,Distinguished,Finiteness,Chart,Rueckert,StrictlyClosed}.lean`, `Rueckert.lean` | Reuse and audit the existing implementation during upstream integration; supply carrier comparisons |
| Weak stability and Japaneseness, §0.4 | `WeaklyStable.lean`, `Japanese.lean`, `TateAlgebra/Stable.lean` | The Tate fraction-field and Japanese-ring capstones currently require characteristic zero; complete the characteristic-positive argument |
| Affinoid presentations, normalisation and continuity | `Affinoid/{Basic,Noether,Continuity,Extend}.lean`, `BanachAlgebra/{Noetherian,Continuity}.lean`, `NormedQuotient.lean` | Preserve the actual hypotheses and the existing closed-graph proof; provide the finite closed-embedding interface |
| Tensor products and finite scalar extension | `Affinoid/{Tensor,BaseChange}.lean` | Compare the presentation construction with the general completed tensor product; do not confuse the ring-theoretic finite-extension result with a constructed norm on the tensor product |
| Fractions | `Affinoid/Fractions.lean` | Complete the seminorm-completion model and the adic comparison; obtain flatness through that comparison |
| Polyradii | `Affinoid/Polydisc.lean`, `Restricted/{Complete,GaussNorm}.lean` | Finish the converse strict-affinoid criterion and the identification of the weighted Gauss norm with the supremum norm |
| Supremum seminorm and power-boundedness | `SupSeminorm/`, `Affinoid/{SupSeminorm,PowerBounded,Reduction}.lean` | Retain general torsion-free and integral-map formulations not covered by the current domain and finite-map proofs |
| Reduced Banach function algebras | `Affinoid/FunctionAlgebra.lean`, `SupSeminorm/FunctionAlgebra.lean` | Remove the characteristic-zero limitation through §0.4; construct the Huber uniformity comparison; package the equivalent complete norm if needed |
| Reduction functor | `Affinoid/ReductionFunctor.lean` | Supply the finite-map and integral-closure interfaces of §2.6 in the shared vocabulary |
| General G-topology and geometric comparisons | Historical specifications in `Roadmaps/RigidAnalyticGeometry/` | Treat these as targets; the algebra source tree does not establish completion of Layers 3–8 |

The Layer 0–2 work boards record the original build and axiom checks and their scope exceptions:
`.mathlib-quality/tauceti-rag-layer0/plan.md`, `tauceti-rag-layer1/plan.md` and
`tauceti-rag-layer2/plan.md`. Their recorded exceptions remain explicit work below.

## Layer 0 Tate algebra theory

**Owner:** this roadmap. **Sources:** BGR 5.1, 5.2.3–5.2.7, 5.3.1, with the cited Part A
inputs; Bosch's 2008 preprint §§1.2–1.3. The common restricted-series ring, iteration,
Weierstrass division and preparation are the foundation shared with AdicSpaces §0.5 and the
Newton-polygons roadmap. Existing local proofs of that foundation are reused or migrated once.

### 0.1 Gauss norm reduction and maximum modulus

1. Equip `Tₙ` with its complete multiplicative nonarchimedean Gauss norm. Prove attainment
   at a coefficient, the value-group statement, and density of polynomials. Retain the
   general polyradius versions in the restricted-series API.
2. Identify the Gauss closed and open unit balls with the power-bounded and topologically
   nilpotent elements. Construct coefficientwise reduction and the isomorphism
   `T̃ₙ ≃ K̃[X₁,…,Xₙ]`; prove its kernel and surjectivity, the unit-lifting statements,
   and the criterion that nonzero reduction means norm one.
3. Construct continuous evaluation and substitution homomorphisms into complete
   nonarchimedean Banach `K`-algebras, contractive for tuples in the unit ball. Prove
   uniqueness and compatibility with coefficientwise reduction. For each series construct
   a maximal point with finite residue field attaining its Gauss norm; finite extensions
   are essential when the residue field of `K` is finite.
4. Prove `|f(x)| ≤ ‖f‖`, the equality of the Gauss and supremum norms, and the domain
   property of `Tₙ`. Retain the nonempty Zariski-dense maximum locus for nonzero `f`.
   This proof precedes general affinoid normalisation.

### 0.2 Weierstrass polynomials finiteness and charts

1. A Weierstrass polynomial is monic with Gauss norm one. Its nonleading coefficients
   have norm at most one, not necessarily less than one. Prove stability under monic
   factors and the unique preparation of a distinguished series as a unit times such
   a polynomial.
2. For a Weierstrass polynomial of degree `s`, identify `Tₙ/(ω)` as a free
   `Tₙ₋₁`-module on `1,X,…,X^(s−1)`. Deduce finiteness for a distinguished series
   and for finite modules killed by a Weierstrass polynomial.
3. Construct the triangular changes of variables making a nonzero series distinguished;
   prove they are isometric automorphisms, give the exponent bound from the dominant
   monomials, and allow one chart for finitely many series. Keep the relative geometric
   use of these charts in the upstream Gerritzen–Grauert development.

### 0.3 Rückert theory and strict closedness

1. Develop Rückert overrings sufficiently to prove that Tate algebras are noetherian,
   factorial, integrally closed and Jacobson. Reuse the existing abstract and Tate-specific
   implementations. These are algebraic exports to Part II R0.9.
2. Prove `dim Tₙ = n` by the explicit prime chain and finite descent after a distinguished
   chart. Do not require a later geometric dimension theorem for this algebraic input.
3. Prove closedness and strict closedness of ideals: nearest points exist, normalised
   finite generators admit coefficient bounds, and quotient norms take values in `|K|`.
   Use the existing bald-subring and orthonormal-lifting route.
4. Retain the corresponding results for submodules of finite free Tate modules and the
   quotient norms of finite modules. General uniqueness of finite-module topology and
   strictness of maps are shared with the functional-analysis programme.

### 0.4 Weak stability and Japanese rings

1. Develop weak stability of valued fields, weakly cartesian finite extensions, the
   bounded-functional criterion, and the perfect-field and complete-field cases in
   BGR 3.5.1–3.5.2. Retain the Japanese-ring criteria and the separable integral-closure
   finiteness theorem at their algebraic generality.
2. Prove weak stability of `FractionRing Tₙ` with the extended Gauss norm in every
   characteristic. The current characteristic-zero proof is available. The remaining
   characteristic-`p` route uses BGR 5.3.1/2, 3.5.3/1–2, b-separable modules and spaces
   of countable type; these inputs must be supplied with the functional-analysis roadmap.
3. Prove finiteness of the integral closure of `Tₙ` in every finite fraction-field
   extension, including inseparable extensions. Use BGR 4.1/3–4 and 4.4/2 for the
   characteristic-positive step. Do not silently replace a finite extension by a
   separable one or require a discretely valued ground field.

**Exit condition:** the full algebraic package is available on the shared Tate carrier;
the characteristic-free weak-stability and Japanese-ring targets are distinguished from
their already present characteristic-zero specialisations.

## Layer 1 Affinoid algebras

**Owner:** this roadmap. **Sources:** BGR 6.1 and Bosch §1.4. Part II R0.9 consumes this
algebra through the compatibility package below; Part II R0.3 owns the general completed
tensor construction used for comparison.

### 1.1 Presentations quotients and tensor products

1. Define affinoidness by a Tate presentation and construct the complete residue norms
   on quotients by closed ideals. Prove noetherianity, the Jacobson property, closure
   under quotients, closedness of ideals, and compatibility of quotient topologies.
2. Construct `A⟨X₁,…,Xₘ⟩`, prove that it is affinoid when `A` is affinoid, and prove
   the iteration isomorphism. Its universal property uses continuous coefficient maps
   and power-bounded variable images; homomorphisms are determined by affinoid generators.
3. For presentations `B₁ = A⟨X⟩/I` and `B₂ = A⟨Y⟩/J`, construct the presentation
   algebra `A⟨X,Y⟩/(I,J)` and prove its pushout property and independence of presentations.
   Preserve the existing universal property among complete nonarchimedean `K`-Banach
   algebras with continuous maps. Prove density of the algebraic tensor image and the
   stated stability of surjections. This supplies the affinoid tensor product; the
   comparison with a separately constructed completed tensor product is an additional theorem.
4. For a finite normed extension `K'/K`, prove affinoidness of `K' ⊗_K A` and the
   canonical identification on Tate algebras. Supply the compatible complete topology
   before using this as a topological scalar-extension statement. Arbitrary complete
   extensions use the upstream completion construction and the interface in §6.4.

### 1.2 Noether normalisation and finite extensions

1. For `A ≠ 0`, construct a finite injective `K`-algebra map `T_d → A`, with `d` bounded
   by a presentation dimension, using distinguished charts and Weierstrass finiteness.
2. Retain finiteness under composition, the finite extension and integral extension
   formulations needed by BGR, and the torsion-free statements for domain targets.
   Identify `d` with `dim A`.
3. If an ideal has maximal radical, prove that its quotient is finite-dimensional over
   `K`. In particular maximal residue fields are finite, and contraction of a maximal
   ideal along an affinoid homomorphism is maximal. Keep any stronger hypotheses-free
   source formulation already present in the implementation.
4. Deduce that affinoid domains are Japanese. Mark the arbitrary-characteristic
   theorem as dependent on §0.4, rather than widening the current proof by declaration.
5. Supply the algebraic dimension statement needed by Part II R1.9: for an affinoid
   domain, every maximal ideal has height `dim A`. Do not assert equidimensionality
   for every reducible affinoid. The polynomial generation of Tate maximal ideals is
   also an algebraic export, corresponding to original §3.1.3.

### 1.3 Automatic continuity and strictness

1. Retain finiteness of `B/𝔪ⁿ` and the vanishing intersection of maximal-ideal powers
   needed for automatic continuity. The noetherian intersection argument does not
   require a separate Jacobson hypothesis.
2. Prove continuity of every `K`-algebra map from a noetherian Banach algebra to an
   affinoid algebra by the existing BGR closed-graph argument. This avoids a dependency
   on the later supremum-norm theorem.
3. Prove uniqueness of the complete affinoid topology, equivalence of complete algebra
   norms and invariance of boundedness, power-boundedness and topological nilpotence.
   Retain contractive renorming for a given affinoid homomorphism.
4. Supply `isClosedEmbedding_of_finite_injective`: a finite injective homomorphism
   between affinoid algebras with complete algebra norms is a homeomorphism onto its
   closed image. Automatic continuity is a conclusion, not an extra input. This is
   the strictness interface requested for Part II R0.9.

### 1.4 Generalised fractions and rational localisation

1. Define `A⟨f,g⁻¹⟩` by its explicit quotient, and prove its continuous universal
   property, iterated-fraction identities and the special Weierstrass and Laurent cases.
2. Define `A⟨f/g⟩` under the unit-ideal condition; prove invertibility of the denominator,
   power-boundedness of its ratios, the universal property and density of `A[g⁻¹]`.
   The purely algebraic invertibility lemma can be supplied for a nonarchimedean normed
   ring without imposing unnecessary affinoid hypotheses.
3. Complete the seminorm description of the localisation and identify its separated
   completion with the quotient presentation. State isometry only for the specific
   seminorm and quotient norm compared by the construction.
4. Identify these algebras with the completed rational localisations of the adic
   programme, naturally in maps and restrictions. Transport flatness from the applicable
   strongly noetherian theorem. This is a compatibility task; no new construction of
   adic rational localisation is required here.

### 1.5 Arbitrary polyradii

1. For positive `ρ : Fin n → ℝ`, retain `T_{n,ρ}` with the multiplicative weighted
   Gauss norm, completeness and polynomial density. Coordinate the one-variable results
   with the Newton-polygons and functional-analysis roadmaps.
2. Prove strict `K`-affinoidness when every `ρᵢ ∈ √|K×|`. Follow the implemented finite
   monomorphism `Tₙ → T_{n,ρ}`, sending `Xᵢ` to `cᵢ Xᵢ^sᵢ` with
   `ρᵢ^sᵢ |cᵢ| = 1`, and its finite monomial generating set.
3. Complete the converse criterion and, in the strict-affinoid case, identify the
   weighted Gauss norm with the supremum norm. A radius outside the divisible value
   group lies outside the strict-affinoid class used here; this is not a prohibition
   on the broader non-strict affinoid terminology used elsewhere.
4. Retain the example of a series convergent on an open disc but not on its closed
   boundary. Do not identify open-disc functions with one fixed restricted-series algebra.

**Exit condition:** the classical algebraic constructions and continuous universal
properties are proved, and the tensor and localisation comparison tasks are tracked
separately from the existing quotient constructions.

## Layer 2 Supremum seminorm and reduction

**Owner:** this roadmap. **Sources:** BGR 3.8, 6.2 and 6.3, Bosch §1.4. Part II R0.4
owns the general spectral and uniformisation theory; its classical specialisation is
identified with the results here. Part II R0.9 consumes the classical affinoid package.

### 2.1 Spectral values and the supremum seminorm

1. Develop evaluation norms and the supremum seminorm on the stated class of Banach
   algebras with finite maximal residue fields, using the existing `HasSupSeminorm`
   interface. Prove boundedness, scalar compatibility, the ultrametric inequality,
   submultiplicativity and positive-power multiplicativity.
2. Identify the seminorm with the maximum over minimal-prime quotients and show
   invariance under quotienting by the nilradical. Prove contraction under algebra
   homomorphisms and isometry under integral injective maps in the applicable setting.
3. Retain BGR 3.8.1/7 and 6.2.2/2–3: the spectral-value formula from a minimal monic
   equation and the bound from any monic equation. The general torsion-free formulation
   remains a target beyond the existing domain implementation.

### 2.2 Maximum modulus and value groups

1. For each `f` in a nonzero affinoid, prove attainment of `|f|sup` at a maximal point,
   through normalisation and then minimal primes.
2. For `|f|sup ≠ 0`, find `c ∈ K` and `m ≥ 1` with `|cf^m|sup = 1`, including the
   uniform exponent depending only on `A`. Deduce the divisible value-group constraint.
3. For an integral affinoid map `B → A`, obtain a monic equation whose spectral value
   equals `|f|sup`. Preserve the general integral-map target of BGR 6.2.2/4 even though
   the current proof covers finite maps.
4. Identify the kernel with the nilradical. The seminorm separates points exactly
   when `A` is reduced. Retain automatic continuity from an arbitrary Banach source
   into a reduced affinoid target.

### 2.3 Power-boundedness spectral radius and uniformity

1. Prove `a ∈ A° ↔ |a|sup ≤ 1`, the equivalent bounded-powers criterion, and the
   integral-equation criterion for a residue norm.
2. Prove `a ∈ A°° ↔ |a|sup < 1`, including the pointwise criterion; construct `Ã`
   as a `K̃`-algebra.
3. Prove the spectral-radius identity
   `|a|sup = inf_{n ≥ 1} ‖aⁿ‖^(1/n)` and identify it with the existing smoothing API.
4. Retain the criterion that the supremum seminorm is a valuation precisely when
   `A` is reduced and its reduction is a domain. Keep the annulus counterexample to
   multiplicativity for a general affinoid domain.
5. Relate boundedness of `A°` to equivalence with the Banach norm. Supply the actual
   comparison with `TauCeti.Huber.IsUniform` after the carrier and topology bridges.
   The arbitrary-characteristic reduced-affinoid conclusion depends on §2.4.

### 2.4 Reduced affinoids as Banach function algebras

1. Prove BGR 6.2.4/1 for every reduced affinoid: there is `C > 0` with
   `|a|sup ≤ ‖a‖ ≤ C |a|sup`. Reuse the characteristic-zero theorem and extend its
   weak-stability input before removing the characteristic hypothesis.
2. Retain the general reduced, finite torsion-free algebra statement of BGR 3.8.3/7.
   The existing domain theorem and the passage to minimal primes cover important
   consumers but do not exhaust that general statement.
3. If a consumer needs a complete normed carrier with norm exactly `|·|sup`, construct
   it explicitly and prove compatibility with the original topology. The current norm
   inequalities alone should not be described as an already installed second norm instance.
4. Deduce the unit-ball descriptions and functoriality of integral elements, retaining
   the actual hypotheses of the existing reduction strictness results.

### 2.5 Reduction of homomorphisms

1. Construct `φ̃ : B̃ → Ã` from every affinoid homomorphism `φ : B → A` and prove
   identity and composition laws.
2. Retain BGR 6.3.1/4–5 for strict maps, with the kernel and radical statements and
   the injectivity consequence under the stated kernel hypothesis.
3. For reduced source, retain the equivalence between injective strictness, supremum
   isometry and injectivity on reductions (BGR 6.3.1/6). Account for the current
   characteristic-zero restriction where the Banach function theorem is used.
4. Preserve examples separating surjectivity of the algebra map from surjectivity
   on reductions.

### 2.6 Integral elements and finite reductions

These are algebraic requirements from the #20 extension and are part of the shared
classical input to Part II R0.9 and R1.1.

1. For a Tate presentation `π : Tₙ ↠ A`, let `A₀ = π(Tₙ°)`. Prove
   `a ∈ A° ↔ a is integral over A₀` (BGR 6.3.5/1). Include nonreduced `A`.
   No module-finiteness of `A°` over `A₀` is asserted.
2. A finite homomorphism `A → B` induces a finite map `Ã → B̃`, using exactly the
   map induced on power-bounded elements and their topologically nilpotent ideals.
   Deduce finite type of `Ã` over `K̃` from a Tate presentation.
3. Expose the positive-power formula with its zero-algebra convention in the upstream
   vocabulary. These interfaces must agree with the corresponding general spectral
   constructions after transport.

## Layer 3 Affinoid varieties from Part II

**Supplier:** Part II R1.1 and R1.9, using the classical algebra of R0.9.

Consume `Sp A`, its functoriality, the Nullstellensatz, closed subspaces, irreducible
components, finite morphisms, fibre products, and the canonical topology. Identify its
point carrier with `MaximalSpectrum A` and its pointwise values with §2.1. Preserve
nonreduced coordinate algebras even though their maximal-point sets do not detect nilpotents.

The local tasks are to identify sections and pullbacks with the supplied algebra maps,
to identify tensor-product presentations with geometric fibre products, and to supply
the algebraic dimension and polynomial-generation results of §1.2. Geometry must not
be used to prove the normalisation and residue-field facts on which its construction depends.

## Layer 4 Subdomains and Gerritzen–Grauert from Part II

**Supplier:** Part II R1.1, with closed and finite morphisms from R0.8 and R0.13.

The required interface contains the following results.

- Affinoid subdomains carry their representing algebra, structure map and universal
  property. Representing algebras are uniquely isomorphic, compatibly with that map.
- Weierstrass, Laurent and rational domains have the explicit fraction algebras of §1.4;
  their transitivity, intersections and inverse images agree with those presentations.
- Restriction maps are flat. Germs and local rings have the specified infinitesimal
  quotient and completed-local-ring comparisons; these include nonreduced affinoids.
- Open, closed and locally closed immersions, openness results and the required Runge
  statements are supplied on the common geometric category.
- Gerritzen–Grauert gives a finite rational decomposition of an affinoid subdomain,
  with the ambient rational-cover and local Weierstrass/rational descriptions needed
  by the acyclicity and descent proofs.
- For a domain `A` and a nonempty affinoid subdomain `U`, the map `A → 𝒪(U)` is
  injective. For a finite affinoid cover, `A → ∏ᵢ𝒪(Uᵢ)` is faithfully flat.
  Empty members are allowed; the empty family covers only `Sp 0`.
- Standard rational domains for `g₁,…,gᵣ`, with nonzero denominator on each member,
  cover exactly when the `gᵢ` generate the unit ideal.

The local compatibility theorem identifies every coordinate ring and restriction map
with its §1.4 counterpart. The geometric universal properties and decomposition
theorems are implemented once in the supplier programme.

## Layer 5 Čech complexes and acyclicity from Part III

**Supplier:** Part III R3.1, together with the foundational AdicSpaces acyclicity results.

Use the finite-intersection algebras of a covering and Mathlib's Čech constructions.
The comparison must commute with all restrictions and differentials, including the
augmentation from `A`. For the two-piece Laurent cover, fix the differential as
`(u,v) ↦ v|intersection − u|intersection`; changing the sign gives an isomorphic complex
but must be accounted for explicitly.

Consume the Laurent case, refinement lemmas and Tate acyclicity for finite affinoid
coverings. Require the finite-module version with its natural topology, and keep the
classical arbitrary-module exactness requirement separate: an assertion proved only
for finite modules is not automatically an assertion for all modules. Supply the latter
by the appropriate algebraic exactness argument or by an upstream theorem with those
quantifiers. Likewise distinguish exactness from strictness of continuous maps.

Derive the structure sheaf, gluing of morphisms and the classical G-site formulation
through the ring and site comparisons. Retain reusable refinement and acyclic-cover
comparison lemmas locally only where Mathlib and the supplier do not already provide
them. This layer does not redevelop the general sheafy-Tate-pair theory.

## Layer 6 General G-topologies and the rigid space interface

**Owner of §§6.1–6.3:** this roadmap. **Supplier of rigid geometry:** Part II R1.1 and
R1.7. **Sources:** BGR 9.1–9.3 and Bosch §§1.10–1.12.

### 6.1 G-topological spaces

1. Define admissible opens and admissible coverings with BGR's intersection,
   covering, identity, restriction and composition axioms. Define continuous maps,
   refinement of G-topologies, induced structures and bases.
2. Construct the preorder of admissible opens, its coverage and Grothendieck topology.
   Prove that its sheaves are exactly the presheaves satisfying the admissible-cover
   equaliser condition. Recover the ordinary site of a topological space.
3. Develop the completeness conditions G0, G1 and G2 and the enhancement theorem
   for slightly finer G-topologies (BGR 9.1.2). Prove the stated universal property.
4. Prove pasting for compatible complete G-topologies on a covering, with admissible
   opens and coverings detected locally (BGR 9.1.3).

### 6.2 Weak and strong affinoid G-topologies

Apply the general formalism to the supplied affinoid subdomains. The weak basis has
finite affinoid coverings; the strong topology is determined by coverings that admit
finite affinoid refinements after every relevant affinoid test map. Prove the enhancement
description, restriction compatibility, admissibility of Zariski opens and covers, and
the connectedness/idempotent criteria.

Prove that these constructions agree with the rigid G-topology supplied by Part II.
This is the classical presentation of a shared geometry, not a second choice of rigid
spaces. In the unit disc retain the non-admissible covering by the open unit disc
and the unit circle. For an admissible exhaustion of the open disc choose
`|T| ≤ |ϖ|^(1/n)` for `n ≥ 1`, where `0 < |ϖ| < 1`; these radii lie in `√|K×|`
and approach one even over a discretely valued field.

### 6.3 Sheaves sheafification and enhancement

Use Mathlib's sheaves and module sheaves. Construct classical stalks through the
filtered system of admissible neighbourhoods, compare with the point of the site,
and identify the affinoid-germ presentation. Prove the BGR plus-construction
description of sheafification by comparison with Mathlib's sheafification. Prove
extension of sheaves from a G-topology to a slightly finer one through the appropriate
dense-subsite comparison; apply this to extend the structure sheaf from the weak
affinoid basis to the strong G-topology.

### 6.4 Supplied rigid varieties and scalar extension

Consume the category of rigid `K`-spaces, admissible restrictions, gluing, fibre
products, affine and projective space, discs and annuli. Its locally G-ringed-space
description must carry the actual structure sheaf and local morphisms on stalks.

For a complete isometric extension `L/K`, require `A_L = A ⊗̂_K L`, functoriality,
compatibility with affinoid subdomains and gluing under the supplier's stated hypotheses,
and faithful flatness of `A → A_L`. This algebraic scalar-extension requirement
is retained from #20 and coordinated with Part II R0.3 and Part III R3.6. It does
not assume that `L/K` is finite, algebraic, discrete or spherically complete.

## Layer 7 Coherence and proper cohomology from Parts II and III

**Suppliers:** Part III R3.2–R3.6; Part II R0.10–R0.13 and R1.9.

### 7.1 Coherent modules and closed subspaces

Consume exact associated-module functors on the applicable affinoids, Kiehl's
equivalence between finite modules and coherent sheaves, coherent ideals and closed
analytic subspaces, and finite algebras and finite morphisms. Require compatibility
with restriction, tensor products and the identification `Γ(Sp A,𝒪) ≃ A`.
Consume coherent affinoid acyclicity and its Čech-to-sheaf-cohomology comparison.

### 7.2 Morphism classes and the identity principle

Consume separatedness, quasi-compactness, quasi-separatedness, relative compactness
and properness with their base-change and composition properties. Rigid properness
uses Kiehl's finite inner-cover condition on affinoid bases. Apply rigid–adic
properness comparisons only with the hypotheses supplied by Part II R1.7; a
characteristic-free forward implication does not give an unrestricted converse.

Retain the #20 identity-principle requirements through Part II R1.9: on a connected
normal rigid space, a nonempty admissible open is analytically Zariski dense and
restriction of functions is injective; the corresponding restriction for a finite
locally free sheaf is injective. Normality is essential. The vector-bundle conclusion
is not asserted for arbitrary coherent sheaves supported away from the open.

### 7.3 Quasi-Stein spaces

Consume Part III R3.4 for a countable increasing admissible affinoid exhaustion
with dense ring restrictions. Require dense restriction of coherent sections,
generation of each affinoid member by global sections, and Theorem B in positive
degrees. Generation does not mean one finite generating set works on the entire
space. Relative compactness is not part of this quasi-Stein hypothesis.

Retain the relative statement: when inverse images of admissible affinoid opens
are quasi-Stein, higher direct images of coherent sheaves vanish. It is not a
vanishing theorem for every open immersion.

### 7.4 Proper mapping and its cohomological interfaces

Consume Part III R3.6 with the following classical requirements from #20.

1. For a Kiehl-proper morphism and a coherent sheaf, all higher direct images are
   coherent. Over `Sp A`, all cohomology groups are finite `A`-modules; smoothness
   and reducedness are not implicit assumptions.
2. The finite affinoid Čech complexes used for proper cohomology have closed-range
   differentials in their natural Banach-module topologies and compute the specified
   sheaf cohomology. Track strictness separately from algebraic exactness.
3. For an ideal `J ⊆ A`, the canonical map from the `J`-adic completion of
   `Hⁱ(X,F)` to `limₙ Hⁱ(X,F/JⁿF)` is an isomorphism. This is ideal-adic completion,
   not Banach completion.
4. For an affinoid subdomain `Sp B → Sp A`, require the canonical isomorphism
   `B ⊗_A Hⁱ(X,F) ≃ Hⁱ(X_B,F_B)`.
5. Require the same canonical base-change map to be an isomorphism for finite flat
   affinoid maps and for arbitrary complete isometric extensions of the ground field.
   In the latter case the coefficient algebra is `A_L`; cohomology is finite and the
   displayed tensor product with it is algebraic. Do not drop flatness from an
   uncorrected tensor base-change assertion.

All maps send `b ⊗ m` to `b` times the restriction or pullback of `m` and respect
the appropriate functorial and connecting maps. The Banach and compact-operator
inputs to the proper mapping theorem are supplied by their own roadmaps.

## Layer 8 Analytification GAGA and comparison

**Suppliers:** Part II R1.3–R1.7 and R1.9; Part III R3.7; Part IV R4.4–R4.5.

### 8.1 Analytification

Consume analytification of schemes locally of finite type over `K`, with its
universal property, points, products, immersion and finite-map compatibilities,
and local-ring comparisons. Also require relative analytification over `Sp A`
for schemes locally of finite type over `Spec A`, where `A` is `K`-affinoid.
Such schemes need not be locally of finite type over `K`.

Retain exact pullback on module sheaves and preservation of coherence, properness
of analytifications of proper morphisms, and the connectedness and irreducible-component
comparisons of #20. Components carry their reduced induced structures; this does
not replace a nonreduced space by a union of reduced ringed spaces.

### 8.2 Classical points rational domains and the adic functor

Consume Huber's functor with `Sp A ↦ Spa(A,A°)` and the correspondence between
maximal points and classical adic points. Identify rational coordinate algebras
using §1.4, and identify coverings, restrictions, finite-intersection algebras,
sections and Čech complexes. The classical points do not exhaust the adic space;
the Gauss point of the disc remains a required counterexample.

The comparison must be natural in affinoid homomorphisms and compatible with
gluing, fibre products and the supplied morphism classes. Preserve the hypotheses
on quasi-separatedness and properness in the upstream statements. In the inspected
Part II R1.7, converse properness and partial-properness comparisons require discrete
valuation, with the separately stated locally quasi-finite exception. Do not widen
these statements merely to simplify a downstream API.

### 8.3 Proper GAGA

Consume Part III R3.7 for schemes proper over an affinoid base, with:

- the canonical `A`-linear cohomology comparison in every degree;
- the exact, tensor-compatible analytification equivalence on coherent sheaves;
- compatibility of higher direct images with analytification for a proper morphism,
  including a target which is not itself proper.

The degree-zero maps are induced by pullback and adjunction; higher comparisons
extend those maps functorially. An arbitrary equivalence between categories is
insufficient. Proper GAGA is not asserted for nonproper affine space.

### 8.4 Étale and pro-étale comparisons

Part IV R4.4–R4.5 and AdicEtaleGeometry own the site-level comparison programme.
Consume their precise rigid–adic and analytification statements only for a downstream
application that needs them. Do not promote every analytification comparison to an
equivalence of topoi or transfer the entire étale development into this roadmap.

## Compatibility package and dependency order

The first integration package consists of five explicit comparisons.

| Interface | Required comparison |
|---|---|
| Tate algebra | A canonical topological `K`-algebra equivalence between the local restricted-series carrier and the upstream completed Tate algebra, preserving coefficients and variables |
| Affinoidness | Equivalence between the algebraic presentation predicate equipped with its complete affinoid topology and the relevant upstream strictly topologically finite type condition |
| Spectral data | Equality of evaluation norms and supremum seminorms; identification of `A°`, `A°°` and `Ã`, natural in algebra maps |
| Localisation and tensors | Canonical topological algebra equivalences commuting with structure maps, variables, restriction maps and tensor-factor inclusions |
| Sites and cohomology | Agreement of admissible coverings, structure sheaves and associated modules; induced comparisons of Čech complexes and the specified sheaf cohomology |

The algebraic core must precede its geometry consumers. General G-topology is independent
of that geometry; its affinoid application uses supplied subdomains and acyclicity.

```text
Mathlib and common restricted-series / functional-analysis foundations
    → classical algebra, Layers 0 → 1 → 2
    → algebra compatibility → Part II affinoid geometry
    → Part III acyclicity and coherent geometry
    → classical site and cohomology comparisons → applications

Mathlib sites → general G-topology → classical site comparison
Part II + Part III → Part IV site comparisons when required
```

This is a dependency order for the relevant theorem groups, not an instruction to
import entire roadmap files into one another. In particular, if an upstream geometric
proof needs a classical lemma listed in #20, it must either prove it within its own
programme or consume an independently proved common prerequisite. The local
transport of that geometric theorem cannot be used to prove its own prerequisite.
General G-topology shared with a supplier must live below both geometric presentations.

## Upstream availability and import policy

As inspected on 13 October 2026, the three relevant PRs are open drafts:

| Roadmap | PR and inspected commit | Dependency branch |
|---|---|---|
| AdicSpacesPartII | [#817](https://github.com/TauCetiProject/TauCetiRoadmap/pull/817), `b45e54cbcf0c012d7f78b2cf62a716a69fb5ce66` | PR base `main` |
| AdicSpacesPartIII | [#813](https://github.com/TauCetiProject/TauCetiRoadmap/pull/813), `ae824af115b07053c757e5cf5e48f7e50f0ea6af` | PR base `roadmap/adic-spaces-part-ii` |
| AdicSpacesPartIV | [#815](https://github.com/TauCetiProject/TauCetiRoadmap/pull/815), `059fd1582e0ebc00212a3a5fb8447127a6c76b7b` | PR base `roadmap/adic-etale-geometry`; additional stack dependencies apply |

The upstream `Suggested.lean` files contain a mixture of concrete definitions and
theorem signatures with `sorry`; substantial geometric constructions remain README
targets. The issue's original suggestion to import those modules is therefore a
future coordination direction, not evidence that every required declaration or
proof is currently available. Some classical algebra and subdomain signatures are
already present; inspect the exact pinned file rather than assuming all targets
have the same status.

The PhD manifest currently has no Tau Ceti or TauCetiRoadmap dependency. Do not add
nonexistent imports to this documentation revision. For implementation, pin compatible
dependencies, identify actual declarations and hypotheses, and import proved library
modules. `Suggested.lean` is a target specification, not a substitute for a proved
production dependency. A missing interface stays a named requirement here and is
implemented in its agreed owner; it is not replaced by a second geometry or an opaque
axiom. A roadmap PR being merged is distinct from its mathematics being proved.

## Implementation sequence and acceptance

1. **Audit and preserve the existing algebra.** Map each Layer 0–2 target to its
   current declaration and exact hypotheses. Reuse the existing proofs and record
   the gaps in the status table. Keep the historical roadmap and skeleton unchanged.
2. **Finish the independent algebra.** Prioritise the characteristic-positive
   weak-stability and Japanese-ring inputs, the resulting reduced-norm generality,
   the polyradius converse, and the integrality and finite-reduction interfaces.
   Track the general BGR formulations alongside the narrower proved versions.
3. **Build the algebra comparisons.** Reconcile Tate carriers, presentation
   predicates, tensor products, rational localisations and spectral data. Deliver
   the algebra once for Part II R0.9 and its consumers.
4. **Build general G-topology.** Prove enhancement, pasting and sheaf comparison
   independently. Then identify the supplied affinoid site with the classical one.
5. **Consume the geometry in dependency order.** Integrate Part II subdomains and
   comparisons, Part III acyclicity and coherence, then proper mapping and GAGA.
   Keep missing upstream prerequisites visible; Part IV is needed only for the
   site-level consumers in §8.4.

At each implementation milestone, build the actual module and relevant examples,
then check the transitive axioms of its capstone results. Acceptance permits only
`propext`, `Classical.choice` and `Quot.sound`; a file without direct `sorry` is not
by itself an axiom audit. The on-demand root is `lake build PhD.TauCeti`; a build of
`PhD` alone does not exercise this chain. No proof or build completion is claimed
by this documentation proposal.

Required acceptance examples include the following.

- Over `ℚ_p`, `|1+pT| = 1`; `|p+T²|sup = 1`, attained at `T=1`; and the reduction
  of `p+T+pT²` is `T`. The value of `p+T²` at `T=0` is `|p|`, so zero is not a
  maximum point for that polynomial.
- Noether normalisation of `K⟨X,Y⟩/(Y²−X³)` by `K⟨X⟩`; a finite normalisation of
  `K⟨X,Y⟩/(XY−c)` by the sum coordinate; and the expected one-dimensionality.
- The maximal ideal `(T²−p)` over `ℚ_p`, its quadratic residue field and the value
  `|T(x)| = p^(−1/2)`.
- The zero algebra: empty maximal spectrum, zero supremum seminorm, no normalisation
  injection and the positive-power convention. For `K⟨T⟩/(T²)`, a nonzero nilpotent
  has supremum seminorm zero and the structure sheaf retains that nilpotent.
- For `0 < |c| < 1`, the annulus algebra has `|X|sup = |Y|sup = 1` and
  `|XY|sup = |c|`. Its domain assertion remains a separate proof obligation from
  the already present norm computation.
- A polyradius in `√|K×|` but outside `|K×|`, and a positive radius outside
  `√|K×|`, testing the exact strict-affinoid criterion.
- Rational fractions with the unit-ideal hypothesis and a failure without it;
  a standard rational covering; and the two-piece Laurent Čech sequence with
  matching augmentation and differential on both sides of the comparison.
- The non-admissible open-disc/unit-circle covering, the admissible exhaustion
  in §6.2, and the weak-to-strong sheaf extension.
- `ℙ¹` from two affinoid discs, with global functions `K`, vanishing `H¹(𝒪)` and
  the specified analytification comparison. Test proper GAGA on this example and
  preserve the nonproper affine-line counterexample to unrestricted GAGA.
- The classical points and Gauss point of the adic unit disc; the rational subset
  defined by `|T| ≤ |p|`; and agreement of its coordinate ring and restrictions
  with the classical rational domain.

## Sources and provenance

- [PhD issue #18](https://github.com/WilliamCoram/PhD/issues/18) and its
  [update on roadmap signatures](https://github.com/WilliamCoram/PhD/issues/18#issuecomment-6117270006)
  give the proposed division between classical algebra and adic geometry.
- The [original roadmap at the PhD baseline](https://github.com/WilliamCoram/PhD/blob/eefb3d91f34b27d0bc7822140fa85fecae029884/PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md)
  supplies the detailed BGR programme and the #20 interface requirements. Its
  [companion signatures](https://github.com/WilliamCoram/PhD/blob/eefb3d91f34b27d0bc7822140fa85fecae029884/PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/Suggested.lean)
  remain unchanged. Implementation evidence comes from
  [the algebra source at that same commit](https://github.com/WilliamCoram/PhD/tree/eefb3d91f34b27d0bc7822140fa85fecae029884/PhD/TauCeti/Code/RigidAnalyticGeometry).
- The inspected upstream specifications are
  [Part II](https://github.com/TauCetiProject/TauCetiRoadmap/blob/b45e54cbcf0c012d7f78b2cf62a716a69fb5ce66/TauCetiRoadmap/AdicSpacesPartII/README.md),
  [Part III](https://github.com/TauCetiProject/TauCetiRoadmap/blob/ae824af115b07053c757e5cf5e48f7e50f0ea6af/TauCetiRoadmap/AdicSpacesPartIII/README.md), and
  [Part IV](https://github.com/TauCetiProject/TauCetiRoadmap/blob/059fd1582e0ebc00212a3a5fb8447127a6c76b7b/TauCetiRoadmap/AdicSpacesPartIV/README.md).
  Their section labels in this document refer to those commits.
- S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis* (1984), especially
  Chapters 5–6 for the owned algebra and Chapters 7–9 for its geometric interfaces.
  BGR references use section/statement numbering.
- S. Bosch, *Lectures on Formal and Rigid Geometry*, 2008 preprint §§1.1–1.17 and
  published LNM 2105 (2014). Section numbers here follow the preprint; the book
  renumbers them.
- Tate's *Rigid analytic spaces* (1971), Gerritzen–Grauert's affinoid acyclicity
  paper (1969), and Kiehl's two 1967 papers on Theorems A/B and proper direct images
  underpin the geometric requirements. Huber's 1994 comparison paper and 1996 book
  underpin the adic interfaces. The precise source statements and additional Conrad
  references for the #20 requirements are retained in the unchanged original roadmap.

For any future code migration, preserve authorship and check provenance file by file.
The two PhD source chains and historical roadmap declarations are not interchangeable
proof dependencies.
