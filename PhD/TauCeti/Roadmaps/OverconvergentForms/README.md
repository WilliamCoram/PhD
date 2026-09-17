# Roadmap: overconvergent automorphic forms on definite quaternion algebras

This roadmap develops the `p`-adic theory of automorphic forms on a totally definite quaternion
algebra `D` over a totally real field `F`, in the form Buzzard gave it in *Eigenvarieties* §§9–13
and Jacobs in his thesis: the adelic setting and the finiteness of the class set; the locally
analytic weights `κ` and the weight-`κ` action of the wild-level monoid on the Tate algebra; the
Banach spaces `S^D_κ(U) = L(U, A_κ)` of overconvergent forms, with their decomposition over the
class set, their classical subspaces and their property (Pr); the double-coset Hecke operators,
among them the operator `U_𝔭`, which is compact; its Fredholm determinant `det(1 − T·U_𝔭)`, the
finite-slope subspaces it cuts out and the Hecke eigensystems they carry, the slope bound, base
change and families of weights; and the theta operator, Bol's identity and the classicality of
small-slope eigenforms. Three results are the headline milestones.

```text
S^D_κ(U) ≅ ⊕_λ A_κ^{Γ_λ} is a Banach space with property (Pr), and c₀(ι × ℕ, K) at a neat level;
S^D_{k,w}(U) ⊆ S^D_κ(U) Hecke-equivariantly, the classical forms being the polynomial-valued
overconvergent ones                                                        [Buzzard §§9–11; Jacobs]
U_𝔭 is compact on S^D_κ(U) at every locally analytic weight, det(1 − T·U_𝔭) is entire with the
reciprocal U_𝔭-eigenvalues as its zeros, the finite-slope subspaces are finite-dimensional and
Hecke-stable, and the Newton polygon of det(1 − T·U_𝔭) lies above the polygon of unit slopes
⌊n / h(U)⌋ · v(ϖ)                                          [Buzzard Lemma 12.2, §13; Jacobs Ch. 2]
ker θ^{k+1} is the classical subspace, θ^{k+1} ∘ U_𝔭 = ϖ^{k+1} U_𝔭 ∘ θ^{k+1}, and an eigenform of
slope less than k + 1 is classical                                           [Buzzard 2004, Prop. 4]
```

The setting is chosen so that every analytic input is already specified elsewhere: the Banach
modules, the model space `c₀(I, K)`, the locally analytic functions and the characters of `ℤ_p^×`
with their expansions `κ(cz + d)` are the `p`-adic-functional-analysis roadmap; the compactoid
operators, the Fredholm determinant, Riesz theory and the slope bounds are the compact-operators
roadmap; the Newton polygon is the Newton-polygons roadmap. What is new here is the arithmetic
around them — the adelic group `D_f^×`, its compact open subgroups and class sets, the weight
modules and the automorphy cocycle, the double-coset operators and their matrices — and the theorem
that these arithmetic objects satisfy the hypotheses of the analytic ones: `U_𝔭` improves the radius
of convergence, so it is compactoid; the class set is finite, so the model is a finite block sum;
the stabilisers act through finite quotients, so property (Pr) holds. Nothing here uses the
Jacquet–Langlands correspondence, and nothing identifies these forms with Hilbert or elliptic
modular forms: the theory is intrinsic to `D`, which is what makes it formalisable now.

## Scope

The roadmap includes the following material.

- The adelic setting: a totally definite quaternion algebra `D` over a totally real number field
  `F`, split at the places above `p`, with a rigidification `D ⊗ F_v ≅ M₂(F_v)` at each such place;
  the group `D_f^× = (D ⊗_F 𝔸_F^f)^×` with its topology, the compact open subgroups `U₀(𝔫)`, `U₁(𝔫)`
  and the standard levels; the finiteness of the class set `D^× \ D_f^× / U` (Fujisaki's lemma), the
  stabilisers `Γ_λ` and their finite quotients; the local structure at `𝔭 | p`, the wild-level
  monoids `M_t`, the elements `η_𝔭` and the coset decompositions of `U η_𝔭 U`.
- Weight modules: the wild-level monoid in norm form, the Möbius series `(az + b)/(cz + d)` and the
  automorphy factor; locally analytic weights as characters with expansion data; the weight-`κ`
  action on the Tate algebra `K⟨z⟩`, its matrix, its norm, the cocycle and the action laws; the
  scalar twist by a character of the monoid; the algebraic and classical weights, the `F_v`-analytic
  weights and, for `F_v = ℚ_p`, every locally analytic character of `ℤ_p^×`; the classical weight
  modules `L_{n,ν}` and their embedding into the Tate algebra; the several- embedding modules for
  `F ≠ ℚ`.
- The spaces of forms: automorphic functions and the level spaces `L(U, A)` for any Banach module
  `A` with a norm-decreasing action of the wild-level monoid; the decomposition over the class set;
  the norm; `S^D_κ(U; r)` at radius `1` on the Tate algebra and at radius `‖ϖ‖^s` on the disc model,
  with the level–radius trade; the classical spaces `S^D_{k,w}(U)`, their finite dimensionality and
  their Hecke-equivariant inclusion into the overconvergent spaces; neat levels and the block model;
  the averaging projectors and property (Pr) at every level.
- Hecke operators: the double-coset operators `[UηU]` for the Hecke pair `(U, Δ_t)`, the action of
  Mathlib's Hecke ring, the matrix recipe from certificates and the transport to the block model;
  the operators `U_𝔭`, `T_𝔮`, `S_𝔮` and the diamond operators; commutativity for standard levels;
  the radius improvement of `U_𝔭`.
- Compactness and the Fredholm determinant: `U_𝔭` is compactoid at every analytic weight; the
  determinant `det(1 − T·U_𝔭)` at neat and at arbitrary levels, its independence of the
  representatives and certificates, its base change along a homomorphism of coefficient fields;
  eigenforms as reciprocal roots, the Riesz decomposition and the slope-`≤ h` subspaces; the Hecke
  algebra acting on them and its eigensystems; the slope bound by the block polygon; weights in
  families over a Banach–Tate ring and the specialisation of the determinant and of the finite-slope
  decomposition.
- The theta operator on the Tate algebra and on the disc model, Bol's identity, the intertwining
  `θ^{k+1} ∘ U_𝔭 = ϖ^{k+1} U_𝔭 ∘ θ^{k+1}` between classical weights, the identification of
  `ker θ^{k+1}` with the classical subspace, the classicality of small-slope eigenforms, and the
  classical subspace as a finite factor of the Fredholm determinant.

The roadmap does not include the following.

- ⚠ **Jacquet–Langlands, and any comparison with Hilbert or elliptic modular forms.** Buzzard's
  identification `S^D_{k,w}(U) ⊗ ℂ ≅ ` (Hilbert modular forms) and his Theorem 2 of 2004, Jacobs's
  Lemma 1.22 (class number one from the absence of weight-two cusp forms) and the converse half of
  Buzzard's 2004 Proposition 4 (classical eigenforms have slope at most `k + 1`) all pass through
  the correspondence. None of them is used: finiteness is Fujisaki's lemma, class number one is
  Voight's Euclidean argument, and the slope statement about classical forms is not part of this
  roadmap. The automorphic-representations roadmap named by the modular-forms roadmap is where a
  representation-theoretic reformulation would live.
- ⚠ **Eigenvarieties.** The spectral variety `{det(1 − T·U_𝔭) = 0}` over weight space, the links
  between different radii (Buzzard's Lemma 13.1), the admissible covering and the eigenvariety glued
  from the finite-slope pieces (Buzzard §§4–5 and §13, Loeffler §§3.11–3.13, Chenevier) are rigid or
  adic geometry and belong with the adic-spaces roadmap; §4.4 provides the pieces — the Fredholm
  determinant over a Banach–Tate ring of weights and its finite-slope decompositions, specialising
  correctly — and nothing glues them.
- ⚠ **The spectral halo.** The integral model over `Λ^{>1/p}`, the halo estimate on the coefficients
  of `det(1 − T·U_p)`, the Atkin–Lehner operators and the slope symmetries, Jacobs's theorem that
  the slopes of `U_3` at weights near the boundary are `j + ½`, and Liu–Wan–Xiao's Theorems 1.3 and
  1.5 are the spectral-halo roadmap, which consumes this one.
- The classical theory of definite quaternion algebras beyond what the class set needs: the Brandt
  matrices and Eichler's basis problem, mass formulas and class numbers of orders, and the
  arithmetic of orders in general; Gross's algebraic modular forms for a general group compact at
  infinity and Loeffler's theory for a general reductive group. Everything here is for `D^×`.
- The `p`-adic functional analysis, the compact-operator theory and the Newton polygons themselves,
  which are the three roadmaps named above; Hida's ordinary projector `lim U_𝔭^{n!}`; `p`-adic
  `L`-functions and Galois representations attached to eigenforms; overconvergent modular symbols.

The adelic and quaternionic material of Layer 0 belongs under
`TauCeti/NumberTheory/QuaternionAlgebra/` and `TauCeti/NumberTheory/AutomorphicForm/Adelic/`; the
weight modules of Layer 1 under `TauCeti/NumberTheory/AutomorphicForm/Weight/`; the spaces, Hecke
operators and Fredholm theory of Layers 2–4 under `TauCeti/NumberTheory/AutomorphicForm/Definite/`,
mirroring the FLT project's `AutomorphicForm/QuaternionAlgebra/` directory; and the theta operator
of Layer 5 under `TauCeti/NumberTheory/AutomorphicForm/Definite/Theta/`.

## Conventions and coordination with Mathlib

The following Mathlib material is relevant to this roadmap.

- `QuaternionAlgebra R a b c` with the notations `ℍ[R, a, b]` and `ℍ[R]`
  (`Mathlib/Algebra/Quaternion.lean`), the conjugation, norm and the division-ring instance of
  `ℍ[R]` over a linearly ordered field. ⚠ Mathlib has no notion of a quaternion algebra as a central
  simple algebra of dimension `4`, no reduced norm on a central simple algebra, no orders, and no
  splitting theory; Layer 0 works with a division algebra `D` with `[Algebra F D]`,
  `finrank F D = 4` and `Algebra.IsCentral`, carries the rigidification at `p` as data, and takes
  `ℍ[ℚ]` as its running example.
- `NumberField.AdeleRing`, `FiniteAdeleRing (𝓞 F) F` and `NumberField.InfiniteAdeleRing`
  (`Mathlib/NumberTheory/NumberField/AdeleRing.lean`,
  `Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean`), the restricted product
  `RestrictedProduct` (`Mathlib/Topology/Algebra/RestrictedProduct/`) and the module topology
  `IsModuleTopology` (`Mathlib/Topology/Algebra/Module/ModuleTopology.lean`), which put the topology
  on `D ⊗_F 𝔸_F^f`; `IsDedekindDomain.HeightOneSpectrum` for the finite places and `adicCompletion`
  for the completions `F_v`; `NumberField.IsTotallyReal`.
- `HeckeRing` and `HeckeCoset` (`Mathlib/NumberTheory/HeckeRing/Defs.lean`): Shimura's abstract
  Hecke ring of a Hecke triple `(Δ, H₁, H₂)` — a submonoid `Δ` of a group with subgroups `H₁, H₂`
  commensurable in `Δ` — with its convolution product in later files. The pair `(Δ_t, U)` of §0.4 is
  a Hecke triple, and §3.1 makes `HeckeRing Δ_t U ℤ` act on `L(U, A)`. ⚠ The action on forms is not
  in Mathlib, only the ring.
- `DoubleCoset.Quotient`, `Doset.doubleCoset`, `Doset.quotToDoubleCoset` and the coset
  decompositions of `Mathlib/GroupTheory/DoubleCoset.lean`; `Commensurable`, `commensurator`;
  `OpenSubgroup`, `ProfiniteGrp`.
- `SlashAction β G α` and `ModularForm.slash`
  (`Mathlib/NumberTheory/ModularForms/SlashActions.lean`): a right action indexed by a weight `β` on
  a fixed carrier. ⚠ Here the weight parametrises the carrier, so the class is not reused; the right
  actions of this roadmap are `MulOpposite` actions (convention 2), which is Mathlib's own device
  for right actions.
- `MvPolynomial.homogeneousSubmodule` for `Sym^n`; `Polynomial`, `PowerSeries`, `MvPowerSeries` in
  two variables for the generating functions of §1.2; `PadicInt`, `Padic`, `hensels_lemma` for the
  rigidification of `ℍ[ℚ]` at `3`; `ZMod`.
- From the `p`-adic-functional-analysis roadmap, used on every page: the model space `C₀(I, K)` (its
  §2.1), `matrixCoeff` (convention 7 there), orthonormalisability and property (Pr) (§2.2), the Tate
  algebra as the model space and the substitution of restricted series (§4.1), the
  evaluation-injectivity of §4.1.5–6, the disc model of the locally analytic functions (§4.3), the
  exponential, logarithm and binomial series (§4.5), and the characters of `ℤ_p^×` with the level
  criterion and the expansions of `κ(cz + d)` (§§5.4–5.5). From the compact-operators roadmap: the
  compactoid operators, blocks and the restriction-of-radius criterion (§§0.2–0.3), the determinant
  on (Pr) modules (§1.5), base change (§1.7), Riesz theory (§§3.2, 3.4–3.5) and the slope bounds
  (§4.4). From the Newton-polygons roadmap: the polygon and its slopes.
- The FLT project (`github.com/ImperialCollegeLondon/FLT`, Apache-2.0) formalises Fujisaki's lemma,
  `NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset`, and the Haar-character machinery
  it rests on, together with weight-two automorphic forms on `D^×` and their Hecke operators; the
  global-number-fields roadmap consumes Mathlib's adeles and names the adelic-algebraic-groups
  roadmap as the owner of algebraic groups over adeles. Layer 0 states Fujisaki's lemma for `D^×`
  itself and cites FLT as the existing source (see the provenance section for the authorship
  caveat).

The Tau Ceti API should agree with the final Mathlib API. ⚠ **None of these is a blocker, and
nothing in this roadmap waits on Mathlib.** At the pinned Mathlib there is no automorphic form, no
definite quaternion algebra, no class set and no Hecke operator on forms.

These conventions are binding. Several of them are corrections to the obvious first design, and the
reasons are given because an implementor who does not know them will reintroduce the problem.

1. **The coefficient module is abstract; the wild level is a monoid.** The spaces `L(U, A)` are
   defined for an arbitrary Banach `K`-module `A` carrying a norm-decreasing right action of a
   submonoid `Δ ⊆ D_f^×` — Buzzard's "any right `M_t`-module" — and a compact open `U ⊆ Δ`. The
   decomposition over the class set, the Hecke operators, the matrix recipe and property (Pr) are
   proved once in this generality (Layers 2–3), and the weight modules of Layer 1 are instances. The
   monoid, not a group, is essential: the element `η_𝔭` that defines `U_𝔭` acts on `A_κ` but is not
   invertible in `Δ_t`, and the theory of `U_𝔭` is the theory of that non-invertibility.

2. **Right actions, in the sources' form, implemented as `MulOpposite` actions.** The action of `Δ`
   on `A` and on functions is a right action, written `a ∣ δ`, with `(f ∣ u)(g) = f(g u⁻¹) ∣ u_p`
   (Buzzard §9) and the transformation law `f(δ g u) = f(g) ∣ u_p` (Jacobs, Definition 1.30). It is
   implemented as Mathlib's `DistribMulAction Δᵐᵒᵖ A` with `SMulCommClass K Δᵐᵒᵖ A`, which is how
   Mathlib writes right actions, and the double-coset decompositions are into right cosets
   `U η U = ∐_t U x_t`. ⚠ Mathlib's `Module` and `DistribMulAction` are left-handed, and the
   overconvergent-modular-symbols literature (Pollack–Stevens) uses the left-handed monoid `Σ₀(p)`
   with the unit condition on the `a`-entry; the temptation to state the theory left-handed is real,
   and it is resisted because every source, every certificate table and every matrix identity of
   Layers 3–5 is right-handed on the nose. The dictionary to the left-handed form is the adjugate
   `(a b; c d) ↦ (d −b; −c a)`, the level-preserving anti-automorphism of `M₂(𝒪)`; group inversion
   is unavailable on a monoid and transposition sends `𝔭^t | c` to `𝔭^t | b`. Record the dictionary
   as a theorem (§1.1.5) and prove nothing twice.

3. **A weight is a pair of characters together with expansion data, and the expansion is the
   analyticity.** A weight is Buzzard's `κ = (n, v)`, two continuous characters `𝒪_𝔭^× → K^×`, and
   an *expansion datum* for `n` at the level `(Σ, ρ)`: for every `γ ∈ Σ` with lower row `(c, d)`, a
   restricted series `col(c, d) ∈ K⟨z⟩` with `‖coeff_m col(c, d)‖ ≤ ρ^m` which evaluates to
   `n(cz + d)` at the integral points of the closed unit disc. The expansion is carried as data —
   "by `κ(cz + d)` we mean the power series expansion", Jacobs; Buzzard's "thickening" of §8 — and
   its uniqueness on the level is a theorem (§1.2.3), so that two weights with the same characters
   act identically. The reason: over a general complete field `K` there is no "continuous implies
   locally analytic" (that is special to `ℤ_p^×`, the `p`-adic-functional-analysis roadmap's
   §5.4.3), the action and every compactness estimate consume exactly the coefficient bound, and a
   definition through `Classical.choice` would make the matrix of the action uncomputable. The
   domain of the characters is `𝒪_𝔭^×`, not a subgroup of `K^×`, so that a weight base-changes along
   any embedding of `K` (§4.5.1).

4. **The wild level belongs to the weight, not only to the level.** The pair `(Σ, ρ)` — the monoid
   of matrices with `‖c‖ ≤ ρ`, `‖d‖ = 1`, integral entries and nonzero determinant, and the radius
   `ρ` — is a parameter of the weight, and `S^D_κ(U)` requires `U_𝔭 ⊆ Σ` ("`U` of wild level
   `≥ 𝔭^t`", Buzzard; Jacobs's Definition 1.28). Analyticity of `κ` on the disc of radius `‖c‖ ≤ ρ`
   about a unit is a joint condition on `κ` and `ρ`; `A_κ` is a `Σ`-module and `U` must act through
   the same `Σ`; and there is no canonical `Σ` for a `κ` — Jacobs's weight acts through both `Σ₁(3)`
   and `Σ₁(9)` — so the choice is carried explicitly and passed to finer levels by restriction
   (§1.2.5).

5. **The action is defined by its kernel, in Buzzard's normalisation.** `f ∣_κ γ` on
   `K⟨z⟩ = c₀(ℕ, K)` is the operator whose matrix is the coefficient array of the kernel
   `H_γ(x, y) = n(cx + d) · v(det γ) · (1 − w_γ(x) y)^{−1}`, `w_γ = (ax + b)/(cx + d)` — the
   operator "presented by a two-variable series" of the compact-operators roadmap's §0.3.1 — so that
   Jacobs's Proposition 2.6 holds by construction and the compactness of `U_𝔭` is a bound on that
   array. The pointwise formula `(f ∣_κ γ)(z) = n(cz + d) v(det γ) f(w_γ(z))` at the integral points
   of the closed unit disc is a theorem (§1.2.5). The normalisation is Buzzard's (§10, p. 72): the
   algebraic character `n(u) = u^n` gives `Sym^n`, the classical weight `k = n + 2`, and `v(det γ)`
   is the second component of the weight, with `v(ϖ) := 1`. Jacobs's `κ` with his factor
   `(cz + d)^{−2}` is `n = κ · u^{−2}`, and his Definition 1.27 is the case `v = 1`.

6. **Neat levels are a hypothesis on the representatives; property (Pr) is the general case.** The
   block model `S^D_κ(U) ≅ c₀(ι × ℕ, K)` is stated for a family `c : ι → D_f^×` of representatives
   of the class set whose stabilisers `Γ_λ` act trivially on `A_κ`; the general statement is
   `S^D_κ(U) ≅ ∏_λ A_κ^{Γ_λ}` with the averaging projector onto the invariants when `Γ_λ` acts
   through a finite quotient, which makes `S^D_κ(U)` a closed direct summand of the model and gives
   property (Pr). Both determinants are kept: the neat one takes certificates only, and every
   base-change and Riesz statement is stated for it; the (Pr) one is the compact- operators
   roadmap's §1.5.2 and agrees with it at a neat level. The reason: for `F ≠ ℚ` no level is neat —
   `Γ_λ` contains a finite-index subgroup of `𝒪_F^×` — and Buzzard's finite- quotient argument (§10,
   p. 73) is the only route.

7. **Hecke operators are computed from certificates.** A *certificate* for `[UηU]` at the
   representatives `c : ι → D_f^×` is a finite family `x : T → D_f^×` of right-coset representatives
   of `UηU` together with factorisations `c_i · x_t⁻¹ = d(i, t) · c_{σ(i, t)} · u(i, t)` with
   `d(i, t) ∈ D^×` and `u(i, t) ∈ U` (Jacobs, Lemmas 2.4–2.5). Every theorem about the matrix of a
   Hecke operator, its compactness and its determinant is stated for arbitrary certificate data, and
   the existence of certificates is a theorem; the concrete cosets of `U η_𝔭 U` (§0.4.4) and the
   nine factorisations of Jacobs's `U_3` are instances. The reason: everything downstream is a
   computation on the certificate, the statement is then choice-free, and a different certificate
   gives a conjugate block operator (§4.2.2).

8. **No Jacquet–Langlands.** Every statement is about `D` alone. Where a source proves a statement
   of this roadmap through the correspondence, the roadmap says so and gives the intrinsic route:
   Fujisaki for finiteness (§0.3), the Euclidean algorithm of the Hurwitz order for Jacobs's class
   number one (acceptance examples), and the theta argument for the small-slope half of classicality
   (§5.4). The converse slope inequality for classical eigenforms is out of scope, and the
   spectral-halo roadmap records how it is obtained there from an Atkin–Lehner hypothesis.

9. **Norms and slopes.** The coefficient field `K` is a complete nonarchimedean field containing
   `F_v` with `‖p‖ = p^{−1}` (the `p`-adic-functional-analysis roadmap's convention 8), the
   uniformiser `ϖ = ϖ_v` has `‖ϖ‖ = p^{−1/e_v}`, and the slope of an eigenvalue `λ` is `v_p(λ)` read
   through the Newton-polygons roadmap's additive valuation; "slope `< k + 1`" and "`ϖ^{k+1}`" in
   Layer 5 are in this normalisation, in which the classical weight `k + 2` carries `Sym^k`.
   Buzzard's 2004 paper writes the weight as `k` and the operator as `θ^{1−k}`; the dictionary is
   `k_{Buzzard} = k + 2`.

10. **Names.** `DefiniteQuaternion.Dfx F D` for `(D ⊗_F 𝔸_F^f)^×`, `globalUnits` for the image of
    `D^×`, `classSet U`, `RigidificationAt F D v`, `toMatrix F D v`, `levelMonoid` for `Δ_t`,
    `etaAdelic` for `η_𝔭`; `SigmaNorm K ρ` for the norm-form monoid, `LevelBounds`; `ExpansionData`,
    `AnalyticWeight` with fields `n`, `v`, `expansion`, `kappaSlash` for `f ∣_κ γ`, `autFactor`,
    `mobius`; `AutomorphicFunction G Γ A`, `AutomorphicFunction.Level U` for `L(U, A)`, `Forms` for
    `S^D_κ(U)`, `classicalForms`, `polyEmbed`; `heckeOperator`, `heckeUp`, `heckeT`, `heckeS`,
    `diamond`; `evalAtReps`, `heckeBlock`, `heckeBlockOp`, `heckeCharPowerSeries`,
    `heckeCharPowerSeriesPr`, `stabAvg`; `theta`, `bol`. The abstract layer lives in the namespace
    `AutomorphicForm`, the weights in `AnalyticWeight`, the quaternionic instantiation in
    `DefiniteQuaternion`; nothing from this roadmap is placed in the root namespace.

## Existing Mathlib used by the roadmap

- `QuaternionAlgebra`, `Quaternion`, `QuaternionAlgebra.normSq`, `QuaternionAlgebra.star`,
  `Quaternion.instDivisionRing`; `Algebra.IsCentral`, `IsSimpleRing`, `Module.finrank`;
  `NumberField`, `NumberField.RingOfIntegers`, `NumberField.InfinitePlace`,
  `NumberField.InfinitePlace.IsReal`, `NumberField.IsTotallyReal`,
  `IsDedekindDomain.HeightOneSpectrum`, `IsDedekindDomain.HeightOneSpectrum.adicCompletion`,
  `adicCompletionIntegers`, `Valued`, `Valued.toNormedField`, `IsUltrametricDist`.
- `FiniteAdeleRing`, `NumberField.AdeleRing`, `RestrictedProduct`, `IsModuleTopology`,
  `Algebra.TensorProduct`, `Units`, `Units.embedProduct`, `Units.isOpen`; `Subgroup`,
  `OpenSubgroup`, `IsCompact`, `IsOpen`, `LocallyCompactSpace`, `ProfiniteGrp`;
  `DoubleCoset.Quotient`, `Doset.doubleCoset`, `QuotientGroup.rightRel`, `Commensurable`,
  `commensurator`, `IsHeckeTriple`, `HeckeCoset`, `HeckeRing`.
- `Matrix (Fin 2) (Fin 2) K`, `Matrix.det`, `Matrix.adjugate`, `Matrix.adjugate_mul_distrib`,
  `Matrix.GeneralLinearGroup`, `Matrix.SpecialLinearGroup`; `Submonoid`, `Submonoid.comap`,
  `MonoidHom`, `MulOpposite`, `DistribMulAction`, `SMulCommClass`.
- `PowerSeries`, `PowerSeries.IsRestricted`, `MvPowerSeries (Fin 2) K`, `MvPowerSeries.coeff`,
  `Polynomial`, `Polynomial.aeval`, `MvPolynomial.homogeneousSubmodule`, `PowerSeries.derivative`,
  `Nat.descFactorial`; `ZeroAtInftyContinuousMap` (`C₀`), `ContinuousLinearMap`,
  `ContinuousLinearEquiv`, `Module.End`, `Module.End.maxGenEigenspace`, `Module.finrank`,
  `Module.Finite`, `Module.Projective`.
- `PadicInt`, `Padic`, `Padic.addValuation`, `hensels_lemma`, `ZMod`, `Fin`, `Finset.sum`,
  `Fintype.card`; `IsAlgClosed`.
- From the `p`-adic-functional-analysis roadmap: `PseudoUniformizer`, `NormedRing.IsTate`, the
  scoped operator norm, `single`, `matrixCoeff`, `truncation`, `IsONable`, `HasPr`, the disc model
  `PadicInt.LocallyAnalytic h E` and its `eval`, `padicExp`, `padicLog`, `binomialSeries`,
  `PadicInt.WeightSpace`, `IsAnalyticOfLevel`, and the expansion `expansion κ c d` of its §5.5.
- From the compact-operators roadmap: `IsCompactoid`, `rowNorm`, `blockOp`, `blockDiag`,
  `charPowerSeries`, `fredholmDet`, `PowerSeries.evalAt`, `PowerSeries.IsEntire`,
  `exists_rieszProjection`, `exists_rieszDecomposition`, `exists_rieszColemanProjection`,
  `norm_charCoeff_le_pow`, `charPowerSeries_map`, `charPowerSeries_eq_of_diag_intertwine`,
  `charPowerSeries_comm`, `charPowerSeries_eq_mul_of_comm`.
- From the Newton-polygons roadmap: the polygon of a power series and its unit slopes, the polygon
  of a prescribed slope sequence, and the height comparison "lies on or above".

⚠ Mathlib has **no** definite quaternion algebra, **no** order in a quaternion algebra, **no**
reduced norm, **no** Fujisaki lemma, **no** automorphic form on an adelic group, **no** Hecke
operator acting on anything (only the abstract Hecke ring), and **no** weight-`κ` action. The FLT
project has the weight-two case of Layers 0, 2 and 3 for `D^×`; everything with a nontrivial weight
is new.

---

## Layer 0: the adelic setting

`F` is a totally real number field of degree `g`, `p` a prime, `𝔓` the set of places of `F` above
`p`, `𝒪_𝔭` and `F_𝔭` the completions at `𝔭 ∈ 𝔓` with uniformisers `ϖ_𝔭` (Mathlib's `adicCompletion`
at a `HeightOneSpectrum`), `𝒪_p := 𝒪_F ⊗ ℤ_p = ∏_𝔭 𝒪_𝔭` and `F_p = ∏_𝔭 F_𝔭`. `K` is a complete
nonarchimedean field with `‖p‖ = p^{−1}` that splits `F` — the set `I := Hom_ℚ(F, K)` has `g`
elements — and `I = ⊔_𝔭 I_𝔭` with `I_𝔭 = Hom_{ℚ_p}(F_𝔭, K)`, so that every `α ∈ 𝒪_p` has the image
`(i(α))_{i ∈ I} ∈ K^I` (Buzzard §§8–9; his `K ⊇ K₀`). For `F = ℚ` all of this collapses to
`𝔓 = {p}`, `I = {id}`, `𝒪_p = ℤ_p` and `K ⊇ ℚ_p`.

### 0.1 Definite quaternion algebras and rigidifications

1. A *quaternion algebra* over `F` is a central simple `F`-algebra `D` of dimension `4`
   (`[Algebra F D] [Algebra.IsCentral F D] [IsSimpleRing D]`, `finrank F D = 4`); it is a division
   algebra or `M₂(F)`. Define the *reduced norm* `nrd : D → F` and *reduced trace* as the
   determinant and trace of the left-regular representation on any splitting, prove they are
   independent of the splitting, that `nrd` is multiplicative with `nrd(x) = x x̄` for the canonical
   involution, and that `D^× = {x | nrd x ≠ 0}` when `D` is a division algebra. ⚠ Mathlib has
   `QuaternionAlgebra F a b` with `normSq` and `star` (its canonical involution) but no reduced norm
   on an abstract central simple algebra; state the theory for `ℍ[F, a, b]` first, where
   `nrd = normSq`, and for an abstract `D` through a chosen `F`-basis `1, i, j, k` with `i² = a`,
   `j² = b`, `ij = −ji` (every quaternion algebra over a field of characteristic `0` has one —
   Voight, Chapter 2).
2. `D` is *totally definite* if `D ⊗_F F_v` is a division algebra at every real place `v` of `F`,
   i.e. `D ⊗_{F, v} ℝ ≅ ℍ`; define the predicate `IsTotallyDefinite F D` through the real embeddings
   of `F` (Mathlib's `NumberField.InfinitePlace.IsReal`). Prove that `D` is then a division algebra,
   and that `nrd(x) ≫ 0` (totally positive) for every `x ∈ D^×`. The running example is Hamilton's
   `ℍ[ℚ] = (−1, −1 / ℚ)`, definite at the one real place, split at every odd prime and ramified at
   `2` (its discriminant).
3. `D` is *split at `𝔭`* if `D ⊗_F F_𝔭 ≅ M₂(F_𝔭)`. A *rigidification at `𝔭`* is a choice of
   `F_𝔭`-algebra isomorphism `θ_𝔭 : D ⊗_F F_𝔭 ≃ M₂(F_𝔭)` carrying `𝒪_D ⊗ 𝒪_𝔭` onto `M₂(𝒪_𝔭)` for a
   fixed maximal order `𝒪_D` (Buzzard §9: "fix an isomorphism `𝒪_D ⊗ 𝒪_{F_v} = M₂(𝒪_{F_v})`"); carry
   it as data (`RigidificationAt F D 𝔭`). Prove `det (θ_𝔭 x) = nrd x` for `x ∈ D` and that the
   reduced norm of `𝒪_D ⊗ 𝒪_𝔭` lands in `𝒪_𝔭`. For `ℍ[ℚ]` at an odd prime `q`, a rigidification is
   `a + bi + cj + dk ↦ ((a + bν + dξ, bξ − c − dν), (bξ + c − dν, a − bν − dξ))` for `ν, ξ ∈ ℤ_q`
   with `ν² + ξ² = −1` (Jacobs, §1.4), which exists by Hensel's lemma; at `q = 3` take `ν = √−2`,
   `ξ = 1`.
4. **Orders.** An order of `D` is an `𝒪_F`-subalgebra that is a lattice; a maximal order exists
   (Voight, Chapter 10) and is unique up to conjugation when `D` is definite only locally, not
   globally. Define the Hurwitz order `ℤ⟨i, j, (1 + i + j + k)/2⟩ ⊆ ℍ[ℚ]`, prove it is a maximal
   order with exactly `24` units, and prove it is right-Euclidean for the reduced norm (Voight,
   Theorem 11.3.2), so that every right ideal is principal (11.3.4). ⚠ Nothing about orders is in
   Mathlib; only what §0.3 and the acceptance examples consume is specified.

### 0.2 The adelic group

1. Define `D_f := D ⊗_F 𝔸_F^f` with the `𝔸_F^f`-module topology (Mathlib's `IsModuleTopology` for
   the base change of a finite free module), and `D_f^× := (D ⊗_F 𝔸_F^f)^×` with the topology of
   `Units.embedProduct`, so that inversion is continuous. Prove that `D_f` is a locally compact
   totally disconnected topological ring, that `D_f^×` is a locally compact totally disconnected
   group, and that `D^× → D_f^×` is an injective group homomorphism. ⚠ Its image `Γ := D^×` is
   discrete when `F = ℚ` and `D` is definite — `D^× ∩ U₀(1)` is the finite unit group of a definite
   order — but not for a general totally real `F`, where `𝒪_F^×` is infinite and accumulates at `1`;
   what holds in general is that `D^× ∩ c U c^{−1}` contains `F^× ∩ c U c^{−1}` with finite index
   for every compact open `U` (Loeffler, Proposition 3.1.4; Buzzard §9, p. 69: `Γ_λ` "is
   commensurable with `𝒪_F^×`").
2. **Components.** For each finite place `v` the evaluation `𝔸_F^f → F_v` induces `D_f → D ⊗_F F_v`,
   an `F`-algebra homomorphism, continuous; at `𝔭 ∈ 𝔓` compose with the rigidification to get
   `θ_𝔭 : D_f^× →* GL₂(F_𝔭)`, and write `θ_p := (θ_𝔭)_𝔭 : D_f^× →* GL₂(F_p)` and `det θ_p`. The
   `𝔭`-component map is split by the inclusion `ι_𝔭 : GL₂(F_𝔭) → D_f^×` of elements with trivial
   components elsewhere, a group homomorphism with `θ_𝔭 ∘ ι_𝔭 = id` and `θ_𝔮 ∘ ι_𝔭 = 1` for `𝔮 ≠ 𝔭`;
   the image of `ι_𝔭` commutes with every element of trivial `𝔭`-component.
3. **The integral adeles.** `𝒪_D ⊗ ℤ̂ := 𝒪_D ⊗_{𝒪_F} ∏_v 𝒪_v ⊆ D_f`, the closure of `𝒪_D`, is a
   compact open subring, and its unit group `U₀(1) := (𝒪_D ⊗ ℤ̂)^×` is a compact open subgroup of
   `D_f^×`; at a split place with rigidification its `v`-component is `GL₂(𝒪_v)`. The route (Buzzard
   §9; the source development): `𝒪_D ⊗ ℤ̂` is the image of the compact `∏_v 𝒪_v^4` under a
   continuous map, hence compact, and open because `∏ 𝒪_v` is open in `𝔸_F^f`; the unit group of a
   compact multiplicatively closed subset is compact because `Units.embedProduct` is a closed
   embedding.
4. **Norms.** The reduced norm extends to `nrd : D_f^× →* (𝔸_F^f)^×`, with `nrd ∘ ι_𝔭 = det` at `𝔭`;
   the *norm class* `|nrd(g)|_f := ∏_v |nrd(g)_v|_v ∈ ℚ_{>0}` is a continuous character of `D_f^×`
   trivial on `U₀(1)` and on every compact open subgroup. Prove
   `|nrd(g)|_f = ∏_{v ∤ p} |nrd(g)_v|_v · ∏_{𝔭 ∈ 𝔓} |det θ_𝔭(g)|_𝔭`, and, by the product formula,
   `|nrd(γ)|_f = N_{F/ℚ}(nrd γ)^{−1}` for `γ ∈ D^×`; for `F = ℚ` this reads
   `|nrd(γ)|_f · det θ_p(γ) = 1`. This character is the "`|ν(g)|`" of Buzzard's theta operator
   (§5.1.3) and the norm class of the spectral-halo roadmap's Atkin–Lehner data.

### 0.3 Compact open subgroups and the class set

1. **Standard levels.** For an integral ideal `𝔫` of `F` prime to the discriminant of `D`, define
   `U₀(𝔫)`, `U₁(𝔫) ⊆ U₀(1)` as the subgroups whose `v`-components are `((∗ ∗), (0 ∗))` resp.
   `((∗ ∗), (0 1))` modulo `𝔫 𝒪_v` for `v | 𝔫`, through the rigidifications at the split places
   dividing `𝔫`; prove they are compact open, that `U₁(𝔫) ⊴ U₀(𝔫)` with quotient `(𝒪_F / 𝔫)^×` via
   `((a b), (c d)) ↦ d`, and that `U₀(𝔫) ∩ U₀(𝔭^t)` and `U₁(𝔫) ∩ U₀(𝔭^t)` are the levels of
   Buzzard's §§12–13. Every compact open subgroup of `D_f^×` is commensurable with `U₀(1)`, which is
   all that is used.
2. **Fujisaki's lemma.** For a finite-dimensional division algebra `D` over a number field `F`, the
   quotient `D^× \ D_f^×` is compact (Fujisaki; Weil, *Basic Number Theory*; the FLT project's
   `NumberField.FiniteAdeleRing.DivisionAlgebra.units_cocompact`, via the Haar characters of `D_f`
   and a Minkowski-type argument), and hence for every open subgroup `U` the double coset space
   `D^× \ D_f^× / U` is finite (FLT's `finiteDoubleCoset`; Buzzard §9, "Say
   `D_f^× = ∐_{λ=1}^μ D^× τ_λ U`"). ⚠ No definiteness is needed for finiteness; definiteness is what
   makes `D^×` discrete (§0.2.1) and the stabilisers below small.
3. **The class set.** Define `classSet U := D^× \ D_f^× / U` (Mathlib's `DoubleCoset.Quotient`), a
   `Fintype` for `U` open, with class number `h(U)`; a *section* is a family `c : ι → D_f^×`
   bijective onto `classSet U`, and a *complete family* one that meets every double coset. For a
   representative `c_λ` define the *stabiliser* `Γ_λ := c_λ^{−1} D^× c_λ ∩ U` (Buzzard's `Γ_λ`,
   Jacobs's `Γ_i`), a subgroup of `U` isomorphic to `D^× ∩ c_λ U c_λ^{−1}`, which is discrete
   (§0.2.1) and compact, hence **finite**, when `D` is totally definite and `F = ℚ`; for general `F`
   it contains `𝒪_F^× ∩ U` and the quotient `Γ_λ / (Γ_λ ∩ F^×)` is finite (Buzzard §10, p. 73;
   Hida's Lemma 7.1), which is all that §2.6 needs.
4. **Finiteness of coset decompositions.** For `U` compact open and any `η ∈ D_f^×`, the double
   coset `U η U` is compact and open, hence a finite union of right cosets `U x_t` and of left
   cosets `x_t' U`; the number of right cosets is `[U : U ∩ η U η^{−1}]`. Consequently, for a
   submonoid `Δ ⊆ D_f^×` containing `U`, the pair `(Δ, U)` is a Hecke triple in the sense of
   Mathlib's `IsHeckeTriple`, and every `η ∈ Δ` defines an element of `HeckeRing Δ U ℤ`.
5. **Class number one.** `D_f^× = D^× · U₀(1)` for `D = ℍ[ℚ]` with the Hurwitz order: every right
   ideal of a right-Euclidean order is principal (§0.1.4), and the idelic dictionary between right
   ideal classes and `D^× \ D_f^× / U₀(1)` (Voight, Theorem 27.6.8) turns this into the triviality
   of the class set. ⚠ Jacobs (Lemma 1.22) derives this from the absence of weight-two cusp forms
   through Jacquet–Langlands; the route above is the one to formalise (convention 8).

### 0.4 The local structure at `𝔭` and the wild-level monoids

`𝔭 ∈ 𝔓`, `ϖ = ϖ_𝔭`, `𝒪 = 𝒪_𝔭`, `t ≥ 1`.

1. **Iwahori subgroups and the monoids `M_t`.** Define `Iw(𝔭^t) := {γ ∈ GL₂(𝒪) | ϖ^t ∣ c}` and the
   monoid `M_t := {γ ∈ M₂(𝒪) | ϖ^t ∣ c, ϖ ∤ d, det γ ≠ 0}` (Buzzard §9, p. 68: "`M_t` is a monoid
   under multiplication"); `Iw(𝔭^t) ⊆ M_t`, `M_{t+1} ⊆ M_t`, the diagonal matrices `diag(a, d)` with
   `a ≠ 0` and `d` a unit lie in `M_t`, and `η := diag(ϖ, 1) ∈ M_t` is not a unit of `M_t`. In the
   valued form of Mathlib, `ϖ^t ∣ c` is `v(c) ≤ v(ϖ)^t` and `ϖ ∤ d` is `v(d) = 1`; state the
   dictionary with the norm form `‖c‖ ≤ ‖ϖ‖^t`, `‖d‖ = 1` (Layer 1's `SigmaNorm`), which is the form
   the analysis uses.
2. **The coset decomposition of `U η U`.** For `U_𝔭 = Iw(𝔭^t)` — or any subgroup with
   `Iw(𝔭^{t'}) ⊆ U_𝔭 ⊆ Iw(𝔭^t)`, `t' ≥ t`, in particular `U₁`-type subgroups —
   `U_𝔭 η U_𝔭 = ∐_{α ∈ 𝒪/𝔭} U_𝔭 · ((ϖ 0), (α ϖ^t 1))` as right cosets (Buzzard, proof of Lemma 12.1,
   the left-coset form; Jacobs, Lemma 2.3 at `p = 3`, `t = 2`), and correspondingly
   `= ∐_β ((ϖ β), (0 1)) U_𝔭` as left cosets. The representatives are `x_α := η u_α` with
   `u_α := ((1 0), (α ϖ^t 1)) ∈ U_𝔭`, so that `x_α = ((ϖ 0), (α ϖ^t 1))`, `det x_α = ϖ`, and
   `x_α ∈ M_t`.
3. **The element `η_𝔭` and the wild-level monoid.** Define `η_𝔭 := ι_𝔭(η) ∈ D_f^×`, the unit with
   `𝔭`-component `diag(ϖ, 1)` and trivial components elsewhere (`etaAdelic`), and for `t ∈ ℕ_{≥1}^𝔓`
   the monoid `Δ_t := θ_p^{−1}(∏_𝔭 M_{t_𝔭}) ⊆ D_f^×` (Buzzard's "wild level"); a compact open `U`
   *has wild level `≥ 𝔭^t`* if `U ⊆ Δ_t`, i.e. `θ_p(U) ⊆ M_t`. Prove that `η_𝔭 ∈ Δ_t` for every `t`,
   that for `U = U^{(p)} × ∏_𝔭 U_𝔭` with `U_𝔭` as in clause 2 the decomposition
   `U η_𝔭 U = ∐_α U · ι_𝔭(x_α)` holds in `D_f^×` with `θ_𝔭` of the representatives the matrices of
   clause 2 and `det θ_𝔭 = ϖ`, and that every `x` in `U η_𝔭 U` has `‖det θ_𝔭(x)‖ = ‖ϖ‖` and
   `det θ_𝔮(x) ∈ 𝒪_𝔮^×` for `𝔮 ≠ 𝔭`.
4. **Diamond elements and the centre.** For `d ∈ 𝒪^×`, `δ_d := ι_𝔭(diag(1, d))` normalises
   `U₁(𝔭^t)`-type levels and commutes with `η_𝔭`; the scalars `ι_𝔭(u · 1)` for `u ∈ 𝒪^×` lie in
   `Δ_t` and act (Layer 1) through `κ(u, u²)`; `ι_𝔭(ϖ · 1)` does not lie in `Δ_t`.
5. **The Hecke pair.** `(Δ_t, U)` is a Hecke triple for every compact open `U ⊆ Δ_t` (§0.3.4), and
   `U η_𝔭 U`, `U η_𝔮 U` (`𝔮 ∤ p` split, `η_𝔮 := ι_𝔮(diag(ϖ_𝔮, 1))`), `U ϖ_𝔮 U` (the central element)
   and the diamond cosets are elements of `HeckeRing Δ_t U ℤ`.

### 0.5 The running example: `ℍ[ℚ]` at `p = 3`

Fix `D = ℍ[ℚ]`, `𝒪_D` the Hurwitz order, `p = 3`, the rigidification `θ₃` of §0.1.3 with
`ν = √−2 ∈ ℤ_3` (the root that is `≡ 1 mod 3`), and the levels `U₀(1)` and `U₁(9)` (Jacobs,
Definition 1.20: `U₁(9)` has `3`-component `{((a b), (c d)) ∈ GL₂(ℤ_3) | 9 ∣ c, d ≡ 1 mod 9}`).

1. The class set of `U₀(1)` is trivial (§0.3.5).
2. The class set of `U₁(9)` has three elements, with representatives `c_0 = 1`,
   `c_1 = ι_3(diag(5, 2))`, `c_2 = ι_3(diag(7, 4))` (Jacobs, Theorem 2.1): given class number one
   for `U₀(1)`, the class set of `U₁(9)` is the orbit space of the image of the `24` Hurwitz units
   in `GL₂(ℤ/9)` acting on the `72` primitive vectors of `(ℤ/9)²`, a finite computation with three
   orbits, represented by `(1, 0)`, `(5, 0)`, `(7, 0)`.
3. The three stabilisers `Γ_i` are trivial (Jacobs, Lemma 2.2): a Hurwitz unit in
   `c_i U₁(9) c_i^{−1}` reduces to a matrix `≡ ((∗ ∗), (0 1)) mod 9` and only `1` does.
4. `U₁(9) η_3 U₁(9) = ∐_{t ∈ {0,1,2}} U₁(9) · ι_3(((3 0), (9t 1)))` (Jacobs, Lemma 2.3).
5. The nine factorisations `c_i · x_t^{−1} = d(i, t) · c_{σ(i,t)} · u(i, t)` with `d(i, t) ∈ D^×` of
   reduced norm `1/3` (`± h / 3` for `h ∈ {1 + i − j, (−1 + i + 3j + k)/2, −(1 + 3i + j + k)/2}`),
   `σ = ((2, 1, 1), (0, 2, 2), (1, 0, 0))` and `u(i, t) ∈ U₁(9)` (Jacobs, Lemmas 2.4–2.5 and §B.1),
   the certificate of §3.2 for `U_3`.

### Examples

`ℍ[ℚ]` split at every odd prime and ramified at `2` (the Hilbert symbol `(−1, −1)_q`); the Hurwitz
units `±1, ±i, ±j, ±k, (±1 ± i ± j ± k)/2`; `U₀(1)` and `U₁(9)` are compact open;
`D^× \ D_f^× / U₀(1)` is a point and `D^× \ D_f^× / U₁(9)` has three points; `Iw(3^2) η Iw(3^2)`
splits into three right cosets; `diag(3, 1) ∈ M_t` is not a unit of `M_t`;
`|nrd(γ)|_f = nrd(γ)^{−1}` for `γ ∈ ℍ[ℚ]^×`.

### Dependencies

Mathlib's quaternion algebras, adele rings, restricted products, module topologies, Dedekind
domains, `DoubleCoset` and `HeckeRing`; the global-number-fields roadmap for the finite adeles and
the product formula; the FLT project for Fujisaki's lemma and the Haar-character machinery (see the
provenance section).

---

## Layer 1: weights and weight modules

`𝔭 ∈ 𝔓`, `𝒪 = 𝒪_𝔭`, `ϖ = ϖ_𝔭`, `I_𝔭 = Hom_{ℚ_p}(F_𝔭, K)` with `d := |I_𝔭|`, and
`A := K⟨z_i : i ∈ I_𝔭⟩`, the Tate algebra in `d` variables, which is the model space
`c₀(ℕ^{I_𝔭}, K)` with the monomials as orthonormal basis (the `p`-adic-functional-analysis roadmap's
§4.1.1, in several variables). For `γ ∈ M₂(F_𝔭)` and `i ∈ I_𝔭` write `γ_i := i(γ) ∈ M₂(K)`.
Everything in §§1.1–1.3 is at the single place `𝔭`; §1.4 assembles the places. For `F = ℚ`, `d = 1`,
`A = K⟨z⟩` and every multi-index is a natural number.

### 1.1 Level monoids in norm form

1. For `0 ≤ ρ < 1` define
   `SigmaNorm F_𝔭 ρ := {γ ∈ M₂(F_𝔭) | ‖γ_{ij}‖ ≤ 1, ‖c‖ ≤ ρ, ‖d‖ = 1, det γ ≠ 0}`, a submonoid of
   `M₂(F_𝔭)` (the products preserve the three bounds because `‖d‖ = 1` absorbs the cross terms), and
   for a submonoid `Σ ⊆ M₂(F_𝔭)` the predicate `LevelBounds Σ ρ`: its elements satisfy the four
   conditions, i.e. `Σ ⊆ SigmaNorm F_𝔭 ρ`. Prove the valuation dictionary
   `M_t = SigmaNorm F_𝔭 ‖ϖ‖^t` (§0.4.1), so that `Iw(𝔭^t)` and the `U₁`-type groups have level
   bounds `‖ϖ‖^t`.
2. **The determinant bound.** For `γ ∈ SigmaNorm F_𝔭 ρ` and `ρ ≤ σ`, `‖det γ‖ ≤ σ` implies
   `‖a‖ ≤ σ`: `a d = det γ + b c` with `‖d‖ = 1` and `‖b c‖ ≤ ρ ≤ σ`. This is the only property of
   the `U_𝔭`-cosets that the compactness of `U_𝔭` uses (§3.5). The units of `SigmaNorm F_𝔭 ρ` are
   its elements with `‖det‖ = 1`; `η = diag(ϖ, 1)` lies in every `SigmaNorm F_𝔭 ρ` with
   `‖det η‖ = ‖ϖ‖` and is not a unit.
3. **`Σ₁`-type levels.** `{γ ∈ SigmaNorm F_𝔭 ρ | ‖c‖ ≤ ρ², ‖d − 1‖ ≤ ρ}` (Jacobs's `Σ₁(p)`:
   `c ≡ 0 mod p²`, `d ≡ 1 mod p` at `ρ = ‖p‖`) is a submonoid with level bounds `ρ`, and the image
   under `θ_𝔭` of a `U₁(𝔭^{2t})`-type group has `Σ₁`-type bounds at `ρ = ‖ϖ‖^t`. These are the
   levels on which a character defined only on `1 + ϖ^t 𝒪` acts, and the acceptance examples use
   them.
4. **The adjugate dictionary** (convention 2). `adj : ((a b), (c d)) ↦ ((d −b), (−c a))` is an
   anti-automorphism of `M₂(F_𝔭)` (Mathlib's `Matrix.adjugate` with `adjugate_mul_distrib`),
   involutive in dimension `2`, determinant-preserving, and it exchanges `SigmaNorm F_𝔭 ρ` with the
   left-handed monoid `Σ₀(ρ) := {‖a‖ = 1, ‖c‖ ≤ ρ, integral, det ≠ 0}` of Pollack–Stevens. A right
   action of `SigmaNorm` is the same as a left action of `Σ₀` along `adj`, and `adj η` is the
   left-handed `diag(1, ϖ)`. Record the dictionary; every statement of this roadmap is made for the
   right action.

### 1.2 The weight-`κ` action on the Tate algebra

`Σ ⊆ M₂(F_𝔭)` is a submonoid with `LevelBounds Σ ρ`. For `γ ∈ Σ` set `L_γ := (c_i z_i + d_i)_i` and
`N_γ := (a_i z_i + b_i)_i`, families of one-variable polynomials indexed by `I_𝔭`, and the *Möbius
series* `w_γ := (N_{γ,i} · L_{γ,i}^{−1})_i`, where `L_{γ,i}^{−1} = d_i^{−1} ∑_m (−c_i/d_i)^m z_i^m`
is a restricted series with `‖coeff_m‖ ≤ ‖c‖^m` because `‖d‖ = 1 > ‖c‖`.

1. **Möbius composition.** `L_{δγ} = L_γ · (L_δ ∘ w_γ)` and `w_{δγ} = w_δ ∘ w_γ` for `γ, δ ∈ Σ`, as
   identities of restricted series, the substitution being that of the `p`-adic-functional-analysis
   roadmap's §4.1.4 (the coefficients of `w_γ` lie in the unit ball, so `w_γ` maps the closed unit
   polydisc to itself and substitution into a restricted series is restricted). The first identity
   is the automorphy-factor cocycle `j(δγ, z) = j(γ, z) j(δ, γz)` for `j(γ, z) = cz + d`, and
   `det (δγ) = det δ · det γ`.
2. **Expansion data.** For a continuous character `n : 𝒪^× → K^×` an *expansion datum at level
   `(Σ, ρ)`* is a function `col` from the lower rows `(c, d)` of the elements of `Σ` to `A` such
   that
   - `col(c, d)` is restricted at radius `ρ^{−1}` with Gauss norm at most `1` there:
     `‖coeff_m col(c, d)‖ ≤ ρ^{|m|}` for all `m ∈ ℕ^{I_𝔭}` and `‖coeff_m col(c, d)‖ ρ^{−|m|} → 0`
     (for `ρ < 1` the first implies the second; `ρ = 1` is Buzzard's minimal "good `t`");
   - for every `z ∈ 𝒪`, embedded as `(i(z))_i` in the closed unit polydisc of `K^{I_𝔭}`,
     `evalAt (i(z))_i (col(c, d)) = n(c z + d)`, where `c z + d ∈ 𝒪^×` because `‖c‖ < 1 = ‖d‖`. An
     *analytic weight at level `(Σ, ρ)`* is `κ = (n, v, col)`: a character `n` with an expansion
     datum `col` and a second continuous character `v : 𝒪^× → K^×`, extended to the nonzero elements
     of `𝒪` by `v(ϖ^k u) := v(u)` (Buzzard §10, "`v(π_j) = 1`"). This is Buzzard's `κ = (n, v)` with
     the thickening of `n` made explicit (convention 3); no analyticity is required of `v`, which
     enters only through the scalar `v(det γ)`.
3. **Uniqueness of the expansion.** Two expansion data for the same `n` at the same level agree on
   every `(c, d)` occurring in `Σ`, by the **several-variable identity theorem**: a series in
   `K⟨z_i : i ∈ I_𝔭⟩` vanishing at every point `(i(z))_i`, `z ∈ 𝒪`, is zero. Proof: for a
   `ℤ_p`-basis `e_1, …, e_d` of `𝒪` the `d × d` matrix `(i(e_β))_{i, β}` is invertible (linear
   independence of the embeddings), the linear change of variables `K^d → K^{I_𝔭}` it defines is an
   isometry of Tate algebras for a suitable renormalisation, and a series in `d` variables vanishing
   on `ℤ_p^d` vanishes by the one-variable identity theorem (that roadmap's §4.1.5) applied one
   variable at a time with the others fixed in `ℤ_p` (Buzzard, proof of Proposition 8.3: "`𝒪` is
   Zariski-dense in `B_1`"). For `d = 1` this is the one-variable theorem verbatim.
4. **The automorphy factor and the kernel.** Define `j_κ(γ) := v(det γ) • col(c, d) ∈ A`, of Gauss
   norm at most `1` with constant term `v(det γ) n(d)`, and the *kernel*
   `H_γ := j_κ(γ)(x) · ∏_i (1 − w_{γ,i}(x_i) y_i)^{−1} ∈ K⟦x_i, y_i : i ∈ I_𝔭⟧`, whose coefficient
   of `x^m y^r` is the coefficient of `x^m` in `j_κ(γ) · ∏_i w_{γ,i}^{r_i}`. Prove: the coefficients
   of `H_γ` lie in the unit ball; for fixed `r` they tend to `0` in `m` (the columns decay); and the
   **row bound**: if `‖a‖ ≤ σ` with `ρ ≤ σ < 1` then `‖coeff_{(m,r)} H_γ‖ ≤ σ^{|m|}` for all `m, r`,
   since `‖coeff_l w_{γ,i}‖ ≤ σ^l` for `l ≥ 1` (from `‖c‖ ≤ ρ ≤ σ` and `‖a‖ ≤ σ`), products of
   series with this property have it, and `‖coeff_m col‖ ≤ ρ^{|m|} ≤ σ^{|m|}` (Jacobs, Proposition
   2.6 and Lemma 2.7's computation).
5. **The action.** `f ∣_κ γ := ofGenFun (H_γ) f`, the operator on `A = c₀(ℕ^{I_𝔭}, K)` presented by
   the kernel `H_γ` (the compact-operators roadmap's §0.3.1, with `2d` variables):
   `z^r ↦ j_κ(γ) ∏_i w_{γ,i}^{r_i}`, bounded of norm at most `1`, `K`-linear. Prove the pointwise
   formula `(f ∣_κ γ)(z) = j_κ(γ)(z) · f(w_γ(z))` for `z` in the closed unit polydisc (that
   roadmap's §4.1.3–4), and in particular, for a polynomial `f` and `z ∈ 𝒪`,
   `(f ∣_κ γ)(z) = n(c z + d) v(det γ) f((a z + b)/(c z + d))` — Buzzard's definition on points
   (§10, p. 72) and Jacobs's Definition 1.27 with his normalisation absorbed (convention 5).
6. **The cocycle and the action laws.** `j_κ(δγ) = j_κ(γ) · (j_κ(δ) ∘ w_γ)` in `A` for `γ, δ ∈ Σ`:
   both sides are restricted series agreeing at every `z ∈ 𝒪` — by clause 1, the multiplicativity of
   `n` and `v`, and `v(det(δγ)) = v(det δ) v(det γ)` — hence equal by clause 3. Consequently
   `f ∣ 1 = f` and `(f ∣ δ) ∣ γ = f ∣ (δγ)`: the weight action is a right action of `Σ` on `A` by
   operators of norm at most `1` (Jacobs: "It is an easy check that `Σ_α` is a monoid and that `‖_κ`
   is a right action"; here the check is the cocycle), and by clause 3 it depends only on `(n, v)`
   and `γ`, not on the expansion datum. ⚠ The cocycle is the only place a character is analysed; it
   is derived from multiplicativity and evaluation-injectivity, never assumed, and no
   character-specific proof of it is to be written.
7. **Existence of expansion data.** (a) `F_𝔭 = ℚ_p`: a continuous `n : ℤ_p^× → K^×` analytic of
   level `h` (that roadmap's §5.4) has, at every level `t ≥ h` with `Σ = M_t`, the expansion datum
   `col(c, d) := expansion n c d` of its §5.5.1 with `ρ = ‖p‖^{t−h}` (its §5.5.2 at
   `r = ‖p‖^{−(t−h)}`); every continuous character has a level, so every weight has expansion data
   at some level, and geometric decay `ρ ≤ ‖p‖` at every level `t ≥ h + 1`. (b) General `F_𝔭`
   (Buzzard, Proposition 8.3): for every continuous `n : 𝒪^× → K^×` there is `N ≥ 1` such that on
   `1 + ϖ^N 𝒪` one has `n(1 + y) = padicExp (∑_i f_i · i(padicLog (1 + y)))` for constants `f_i ∈ K`
   with `‖ϖ^N f_i‖ < r_p` — the continuous homomorphisms `𝒪 → K` are the `K`-span of the embeddings
   — so that `n` has an expansion datum at every level `t ≥ N` with `ρ = ‖ϖ‖^{t−N}`. Every analytic
   weight of this roadmap arises this way; the algebraic weights (§1.3) have data at every level.
8. **Restriction and twists.** A datum at `(Σ, ρ)` restricts to any `(Σ', ρ')` with `Σ' ⊆ Σ` and
   `ρ ≤ ρ'`, and the action of `Σ'` is the restriction. ⚠ Passing to a smaller `ρ'` at a deeper
   level is not formal: it is clause 7 again at the deeper level. For a character `χ : Σ →* K^×` of
   norm `1` on `Σ`, the twisted action `f ↦ χ(γ) • (f ∣_κ γ)` is again a right action by operators
   of norm at most `1`; `γ ↦ v(det γ)` is such a character, and so is a nebentypus pulled back
   through `d` (§1.3.4).

### 1.3 Algebraic and classical weights

1. **Algebraic weights.** For `n, v ∈ ℤ^{I_𝔭}` define `n(u) := ∏_i i(u)^{n_i}`,
   `v(u) := ∏_i i(u)^{v_i}` and `col(c, d) := ∏_i (i(d) + i(c) z_i)^{n_i}`, a polynomial when every
   `n_i ≥ 0` and otherwise the product of `i(d)^{n_i} (1 + (i(c)/i(d)) z_i)^{n_i}` with the binomial
   series of a negative integer exponent, whose coefficients are integers. This is an expansion
   datum at every level `(SigmaNorm F_𝔭 ρ, ρ)`, `ρ < 1` (Buzzard §11: `r(κ)_j = |π_j|`); the weight
   is `algWeight (n, v)`.
2. **The classical weight modules.** `L_n := ⊗_i Sym^{n_i}`, realised as the polynomials in `A` of
   degree at most `n_i` in each `z_i` (or as `⊗_i K[X_i, Y_i]_{n_i}`, Mathlib's
   `homogeneousSubmodule`, with `z_i = X_i / Y_i`), free of rank `∏ (n_i + 1)`; for every
   `γ ∈ M₂(F_𝔭)` with `det γ ≠ 0` — no level condition — define
   `f ∣_{(n,v)} γ := ∏_i i(det γ)^{v_i} ∏_i (c_i z_i + d_i)^{n_i} · f(w_γ(z))`, a polynomial in
   `L_n`; prove it is a right action of the monoid of nonzero-determinant matrices (Buzzard §9's
   `L_{n,v}`, which "gives an action of `GL₂(F_p)`"), and that in the homogeneous model it is
   `P(X, Y) ↦ det^v P(a X + b Y, c X + d Y)`.
3. **The bridge.** For `γ ∈ Σ`, the action of clause 2 on `L_n ⊆ A` agrees with the weight action of
   `algWeight (n, v)`; hence `L_n` is a `Σ`-stable finite-dimensional subspace of `A`, and it is
   exactly the subspace spanned by the monomials `z^m`, `m ≤ n` (Buzzard §11: "the natural injection
   `L_{n,v} → A_{κ,r}` … is an `M_1`-equivariant inclusion"). The classical weight `(k, w)` of
   Buzzard §9 is `k = n + 2`, `w = v + n + 1`.
4. **Nebentypus and classical shapes.** For a character `ψ` of `𝒪^×` of finite order factoring
   through `(𝒪/𝔭^α)^×` and `n` algebraic, the character `n ψ` has, at every level with
   `‖c‖ ≤ ‖ϖ‖^α`, the expansion datum `col(c, d) = ψ(d) · ∏ (i(d) + i(c) z_i)^{n_i}`, because
   `ψ(c z + d) = ψ(d)` for `z ∈ 𝒪` and `ϖ^α ∣ c`. The weights `(n ψ, v)` are the *classical-shape*
   weights: their automorphy factor is a constant times a polynomial in `c z + d` (Buzzard 2004's
   `(k, ε_p)`; Buzzard §11's `κ(α, β) = ε(α) ∏ α_i^{n_i} β_i^{v_i}`), and Layer 5 is stated for
   them.
5. **Scalars and the weight condition.** The scalar matrix `u · 1`, `u ∈ 𝒪^×`, lies in every `Σ` and
   acts on `A` by the scalar `n(u) v(u²) =: κ(u, u²)`. Consequently, for a subgroup `G ≤ 𝒪_F^×`
   embedded diagonally, `A^G = 0` unless `κ(γ, γ²) = 1` for all `γ ∈ G`. A *weight* in Buzzard's
   sense (§8) is a pair `(n, v)` with `κ(γ, γ²) = 1` for all `γ` in a finite-index subgroup of
   `𝒪_F^×`; for `F = ℚ` this is no condition, but `S^D_κ(U) = 0` whenever `−1 ∈ U` and `n(−1) ≠ 1`
   (§2.3.2).

### 1.4 Several places

1. For the full weight `κ = (n, v)`, `n, v : 𝒪_p^× = ∏_𝔭 𝒪_𝔭^× → K^×`, with expansion data at each
   `𝔭` for `n_𝔭 := n|_{𝒪_𝔭^×}` at level `(Σ_𝔭, ρ_𝔭)`, define
   `A_κ := K⟨z_i : i ∈ I⟩ = c₀(ℕ^I, K) ≅ ⊗̂_𝔭 c₀(ℕ^{I_𝔭}, K)` (that roadmap's §2.1.4) and, for
   `γ = (γ_𝔭)_𝔭 ∈ ∏_𝔭 Σ_𝔭`, the action with kernel `∏_𝔭 H_{γ_𝔭}` — the tensor product of the actions
   at the places, acting on the variables of `I_𝔭` through `γ_𝔭`. Prove it is a right action by
   operators of norm at most `1`, with the row bound `σ^{|m|}` in the total degree over `I` when
   `‖a_𝔭‖ ≤ σ` and `ρ_𝔭 ≤ σ` at every `𝔭`. This is Buzzard's `A_{κ,r}` at `r = 1` (§10) for the
   monoid `M_t`.
2. **The single-place theory.** For a fixed `𝔭` the sub-instance `A = K⟨z_i : i ∈ I_𝔭⟩` with `Σ_𝔮`
   acting trivially for `𝔮 ≠ 𝔭` — the forms of weight `κ` at `𝔭` and of weight two at the other
   places above `p` — has a wild-level condition and a compact operator `U_𝔭` at `𝔭` only. For
   `F = ℚ` there is one place and nothing to choose. Every acceptance example and both consumer
   roadmaps live in this case; the several-place statements of Layers 2–4 follow from the
   single-place ones by the tensor-product formula, and Layer 5 is stated for `F_𝔭 = ℚ_p`.
   (Buzzard's footnote 5: "One can almost certainly develop some of the theory as long as at least
   one place above `p` is split".)

### Examples

`F = ℚ`, `K ⊇ ℚ_p`: the algebraic weight `n(u) = u^k`, `v = 1`, with `col(c, d) = (d + c z)^k` and
kernel `(c x + d)^{k+1} / ((c x + d) − (a x + b) y)`; the matrix of `diag(1, d)`, namely
`z^r ↦ d^{k−r} z^r`; the matrix of `((1 0), (c 1))`; the character
`u ↦ u^s = padicExp (s · padicLog u)` on `1 + p ℤ_p` for `s ∈ ℤ_p`, extended by `n(−1) = 1` —
Jacobs's weight after the normalisation shift — at the `Σ₁`-type level `p² ∣ c`, `d ≡ 1 mod p` with
`ρ = ‖p‖`, whose datum is `col(c, d) = d^s ∑_m (s choose m)(c/d)^m z^m` with
`‖(s choose m) c^m‖ ≤ ‖p‖^{2m} / ‖m!‖ ≤ ‖p‖^m`; its cocycle, derived; a nebentypus `ψ` of conductor
`p` loaded into `u^k ψ(u)` at level `p ∣ c`; the scalar `−1` acting by `(−1)^k`; the adjugate of
`((3 0), (9t 1))`.

### Dependencies

The `p`-adic-functional-analysis roadmap, §§4.1, 4.5, 5.4–5.5, and §2.1.4; the compact-operators
roadmap's §0.3.1 (operators presented by kernels); Layer 0 only for the dictionary with `M_t`.

---

## Layer 2: automorphic functions and the spaces of forms

`G` is a group, `Γ ≤ G` a subgroup, `Δ ⊆ G` a submonoid, and `A` a `K`-Banach space with a right
action of `Δ` by bounded `K`-linear operators of norm at most `1` (convention 2). The quaternionic
case is `G = D_f^×`, `Γ = D^×`, `Δ = Δ_t` and `A = A_κ` with the action pulled back along `θ_p`, and
it is the only case in which finiteness enters; §§2.1–2.2 are group theory.

### 2.1 Automorphic functions and level spaces

1. Define `AutomorphicFunction G Γ A := {φ : G → A | ∀ γ ∈ Γ, ∀ g, φ (γ g) = φ g}`, a `K`-module
   with no continuity imposed, and the right slash `(φ ∣ δ)(g) := φ(g δ^{−1}) ∣ δ` for `δ ∈ Δ`, the
   inverse taken in `G` (Buzzard §9: "`(f|u)(g) := f(gu^{−1}).u_p`"). Prove it is a right action of
   `Δ` on `AutomorphicFunction G Γ A`.
2. For a subgroup `U ≤ G` with `U ⊆ Δ`, define `Level U := {φ | ∀ u ∈ U, φ ∣ u = φ}`, Buzzard's
   `L(U, A)` and Jacobs's `L(U, A)` (Definition 1.30); prove the transformation-law form
   `φ ∈ Level U ↔ ∀ g u, φ (g u) = φ g ∣ u` ("`φ(d g u) = φ(g) ‖_κ u_p`"), that `Level U` is a
   `K`-submodule, that `Level U' ⊇ Level U` for `U' ≤ U`, and the functoriality: a bounded
   `Δ`-equivariant `A → B` induces `Level U → Level U` on the two function spaces, and `L(U, −)` is
   left exact.
3. **Weight two.** For `A = K` with the trivial action, `Level U` is the space of `K`-valued
   functions on `Γ \ G / U` — the weight-two automorphic forms of the FLT project — and every
   statement below specialises to it.

### 2.2 The decomposition over the class set

1. **Evaluation at representatives.** For a family `c : ι → G` meeting every double coset of
   `Γ \ G / U`, the map `φ ↦ (φ (c_λ))_λ` is injective on `Level U`. For a *section* `c` (bijective
   onto the class set) and `Γ_λ := c_λ^{−1} Γ c_λ ∩ U ⊆ U ⊆ Δ`, its image is `∏_λ A^{Γ_λ}`, the
   invariants under the action of `Γ_λ` on `A` (Buzzard §9: "the map `f ↦ (f(τ_λ))` induces an
   isomorphism `L(U, A) → ⊕ A^{Γ_λ}`"; Jacobs, Lemma 1.31): the inverse is `φ(γ c_λ u) := a_λ ∣ u`,
   well defined because `a_λ ∣ w = a_λ` for `w ∈ Γ_λ`.
2. **The norm.** `‖φ‖ := sup_g ‖φ(g)‖ = max_λ ‖φ(c_λ)‖` on `Level U` (Buzzard §10, p. 73: `u` and
   `u^{−1}` are both norm-decreasing, so the action of `U` is isometric); when the class set is
   finite `Level U` is a Banach space, isometric to `∏_λ A^{Γ_λ}` with the max norm, and
   `‖φ ∣ δ‖ ≤ ‖φ‖` for all `δ ∈ Δ`.
3. **The block model.** For `A = c₀(J, K)`, `evalAtReps c : Level U → c₀(ι × J, K)` (the
   `p`-adic-functional-analysis roadmap's §2.1.4 block decomposition) is an isometry onto the closed
   subspace `∏_λ A^{Γ_λ}`; it is bijective if and only if every `Γ_λ` acts trivially on `A`, in
   particular when every `Γ_λ = 1`.

### 2.3 The quaternionic spaces

1. **Definition.** For a weight `κ` with expansion data at level `(M_t, ρ)` (Layer 1; at the places
   of `𝔓`, or at the single place `𝔭` of §1.4.2) and a compact open `U ⊆ D_f^×` of wild level
   `≥ 𝔭^t` (§0.4.3), define `S^D_κ(U) := Level U ⊆ AutomorphicFunction D_f^× D^× A_κ`, Buzzard's
   `S^D_κ(U; 1)` and Jacobs's `L(U, A_κ)`. By §0.3.2 the class set is finite, so
   `S^D_κ(U) ≅ ⊕_λ A_κ^{Γ_λ}` is a `K`-Banach space with the sup norm (§2.2.2). Define the classical
   space `S^D_{k,w}(U) := Level U` for `A = L_{n,v}` (§1.3.2; `k = n + 2`, `w = v + n + 1`),
   Buzzard's Definition in §9, and prove it finite-dimensional of dimension at most
   `h(U) ∏ (n_i + 1)`, with equality when every `Γ_λ` acts trivially (Buzzard §9: "This space is a
   finite-dimensional `K`-vector space").
2. **Vanishing.** If some `γ ∈ 𝒪_F^× ∩ U` has `κ(γ, γ²) ≠ 1` then `S^D_κ(U) = 0` (§1.3.5); for a
   weight in Buzzard's sense there is a finite-index open `U' ⊆ U` with `𝒪_F^× ∩ U'` in the kernel
   of `κ(·, ·²)`, and the spaces at level `U'` are the ones to study. For `F = ℚ` the condition is
   `n(−1) = 1` when `−1 ∈ U`, which is why the running example works at `U₁(9)` (`−1 ∉ U₁(9)`).
3. **Radius `r` and the disc models.** For `s ≥ 0` let `A_{κ,s}` be the disc model of the functions
   analytic on every polydisc of radius `‖ϖ‖^s` about a point of `𝒪` — the
   `p`-adic-functional-analysis roadmap's §4.3.1 for `𝒪_𝔭` in place of `ℤ_p`, indexed by
   `(𝒪/𝔭^s) × ℕ^{I_𝔭}` — with `M_{t+s}` acting by the same formula through the substitution
   `z = α + ϖ^s w` on each disc, and `S^D_κ(U; ‖ϖ‖^s) := Level U` for it: Buzzard's
   `r`-overconvergent forms at `r = ‖ϖ‖^s`. Prove the **level–radius trade**
   `S^D_κ(U ∩ U₀(𝔭^t); ‖ϖ‖^s) ≅ S^D_κ(U ∩ U₀(𝔭^{t+s}); 1)` for `U = U^{(𝔭)} × GL₂(𝒪_𝔭)` (Buzzard,
   Proposition 11.1: `f ↦ h`, `h(g) := f(g · ι_𝔭(diag(ϖ^{−s}, 1))) ∣ diag(ϖ^s, 1)`, and back through
   the disc decomposition), Hecke-equivariant for `U_𝔭` and for the operators away from `𝔭` (his
   Lemma 12.1: `((ϖ 0), (α ϖ^t 1)) diag(ϖ^s, 1) = diag(ϖ^s, 1) ((ϖ 0), (α ϖ^{t+s} 1))`). The
   `m`-locally-analytic spaces `S^{D,†,m}` of the spectral-halo roadmap are the disc-model spaces at
   radius `‖p^m‖`, and the trade is how every statement at radius `1` transfers to them.
4. **The single-place instance.** With `A = K⟨z_i : i ∈ I_𝔭⟩` (§1.4.2), `S^D_κ(U)` is Buzzard's
   space with weight two imposed at the places `𝔮 ≠ 𝔭`; for `F = ℚ` it is his space on the nose.

### 2.4 Classical forms are overconvergent

1. For `κ = algWeight (n, v)` and `U` of wild level `≥ 𝔭`, the equivariant inclusion `L_n ↪ A_κ`
   (§1.3.3) induces an injective isometric `K`-linear map `S^D_{k,w}(U) ↪ S^D_κ(U)` (Buzzard §11:
   "`S^D_{k,w}(U) = L(U, L_{n,v}) ⊆ L(U, A_{κ,r}) = S^D_κ(U; r)`"), Hecke-equivariant (§3.1.5),
   whose image is exactly the forms with values in `L_n`: **classical = polynomial-valued
   overconvergent**, of degree at most `n_i` in `z_i`.
2. **Loading the nebentypus.** Let `U₀ = U^{(p)} × GL₂(𝒪_p)`, `U₁ := U₀ ∩ U₁(𝔭^t) ⊴ U₀ ∩ U₀(𝔭^t)`
   with quotient `(𝒪/𝔭^t)^×` acting on `S^D_{k,w}(U₁)` through the diamond operators (§3.3.4), and
   `ε` a character of `(𝒪/𝔭^t)^×`. Then the `ε`-eigenspace `S^D_{k,w}(U₁)(ε)` maps injectively and
   Hecke-equivariantly into `S^D_{κ_ε}(U₀ ∩ U₀(𝔭^t))` for the classical-shape weight
   `κ_ε = (ε · n, v)` of §1.3.4 (Buzzard §11, pp. 74–75: the map `L_{n,v} → A_{κ_ε}` is equivariant
   for the matrices with `ϖ^t ∣ (d − 1)`, and the two actions of `U₀(𝔭^t)` differ exactly by `ε`).
   This is how classical forms with character at `𝔭` become overconvergent forms of `U₀(𝔭^t)`-level,
   and the image is again the polynomial-valued forms.
3. The classical subspace is `U_𝔭`-stable and finite-dimensional, of dimension `h(U) ∏ (n_i + 1)` at
   a level where every `Γ_λ` acts trivially.

### 2.5 Neat levels and the block model

1. For a section `c : ι → D_f^×` of the class set, `evalAtReps c : S^D_κ(U) → c₀(ι × ℕ^I, K)` is an
   isometry onto `∏_λ A_κ^{Γ_λ}` (§2.2.3), and it is **bijective** when every `Γ_λ` acts trivially
   on `A_κ` — in particular at a *neat* level, where every `Γ_λ = 1` (Jacobs, Lemma 2.2 for `U₁(9)`;
   Liu–Wan–Xiao's Hypothesis 2.10). Then `S^D_κ(U) ≅ c₀(ι × ℕ^I, K)` is orthonormalisable (that
   roadmap's §2.2.3), with the basis of forms supported on one class and equal to a monomial at its
   representative.
2. **Transition between sections.** For two sections `c`, `c'` with `c'_λ = γ_λ c_{π(λ)} u_λ`
   (`γ_λ ∈ D^×`, `u_λ ∈ U`), `evalAtReps c' = T ∘ evalAtReps c` for the block operator `T` with the
   single nonzero block `(· ∣ u_λ)` in row `λ` and column `π(λ)`, an isometric automorphism of
   `c₀(ι × ℕ^I, K)`; this is what makes every construction below independent of the section.

### 2.6 Property (Pr) at every level

1. **Finite quotients.** `Γ_λ` acts on `A_κ` through a finite quotient: `Γ_λ ∩ F^× ⊆ 𝒪_F^× ∩ U` has
   finite index in `Γ_λ` (§0.3.3) and acts by the scalars `κ(γ, γ²)` (§1.3.5), which are `1` on a
   finite-index subgroup `Γ'_λ` for a weight in Buzzard's sense (§2.3.2 after shrinking `U`), so the
   action factors through `Γ_λ / Γ'_λ` (Buzzard §10, p. 73: "the group `Γ_λ` contains, with finite
   index, a subgroup of `𝒪_F^×` of finite index, and hence `Γ_λ` acts on `A_{κ,r}` via a finite
   quotient"). For `F = ℚ` every `Γ_λ` is finite.
2. **The averaging projector.** `e_λ := |Γ_λ / Γ'_λ|^{−1} ∑_{γ ∈ Γ_λ / Γ'_λ} (· ∣ γ)` — `K` has
   characteristic `0` — is a continuous projector of `A_κ` onto `A_κ^{Γ_λ}`, of norm at most
   `‖|Γ_λ/Γ'_λ|‖^{−1}`; hence `A_κ^{Γ_λ}` is a closed direct summand of `c₀(ℕ^I, K)`,
   `stabProj := blockDiag (e_λ)` is a continuous projector of `c₀(ι × ℕ^I, K)` onto the image of
   `evalAtReps`, and **`S^D_κ(U)` has property (Pr)** (that roadmap's §2.2.3; Buzzard p. 73: "Hence
   `S^D_κ(U; r)` is a direct summand of an ONable Banach module and our Fredholm theory applies").
   This is the general case; §2.5 is the case `e_λ = 1`.
3. Over a discretely valued `K`, `S^D_κ(U)` is potentially orthonormalisable (Serre, that roadmap's
   §2.3.3); ⚠ it need not be orthonormalisable on the nose, since the projector `e_λ` need not have
   norm `1`.

### Examples

Weight two: `S^D_2(U) = K^{Γ \ G / U}`, of dimension `h(U)`; for `ℍ[ℚ]`, `S^D_{k+2}(U₁(9))` has
dimension `3(k + 1)` and `S^D_κ(U₁(9)) ≅ c₀(Fin 3 × ℕ, K)` for every weight with expansion data at a
`Σ₁`-type level of `U₁(9)`; `S^D_κ(U₀(1)) = 0` for `n(−1) = −1`; the level–radius trade
`S^D_κ(U₀(3); ‖3‖) ≅ S^D_κ(U₀(9); 1)`; `Γ_λ` for `U = U₀(1)` and `ℍ[ℚ]` is the group of `24` Hurwitz
units, acting on `A_κ` by the norm-one action of §1.2 through `θ_3`, with `e_λ` the average over the
`24` units, so that `S^D_κ(U₀(1)) ≅ A_κ^{𝒪_D^×}`.

### Dependencies

Layers 0–1; the `p`-adic-functional-analysis roadmap's §§2.1–2.3 and §4.3.

---

## Layer 3: Hecke operators

`(Δ, U)` is a Hecke pair as in §0.3.4 — `U ⊆ Δ` a compact open subgroup of the locally profinite
`G = D_f^×` — and `A` is as in Layer 2. The double-coset operators are defined for the abstract
`Level U` and computed for `S^D_κ(U)`.

### 3.1 Double-coset operators

1. For `η ∈ Δ` and a decomposition `U η U = ∐_{t ∈ T} U x_t` into finitely many right cosets
   (§0.3.4), define `[UηU] : Level U → Level U`, `φ ↦ ∑_t φ ∣ x_t` (Buzzard §9, "decompose
   `UηU = ∐_i U x_i` and define `f|[UηU] := ∑_i f|x_i`"; Jacobs, Definition 1.32). Prove that the
   sum lies in `Level U`, that it is independent of the representatives (`x'_t = u_t x_t` with
   `φ ∣ u_t = φ`), that `[UηU]` is `K`-linear of norm at most `1`, that `[U u U] = id` for `u ∈ U`,
   and that `[UηU] = (· ∣ η)` when `η` normalises `U`. More generally define
   `[UηV] : Level U → Level V` for two levels `U, V ⊆ Δ` from `U η V = ∐ U x_t`.
2. **The Hecke ring acts.** The assignment `[UηU] ↦ [UηU]` extends to a ring homomorphism
   `HeckeRing Δ U ℤ → End_K (Level U)` from Mathlib's abstract Hecke ring: the convolution product
   of double cosets corresponds to composition of the operators (Shimura, Chapter 3, §3.1: the
   action of `R(Γ, Δ)` on the `Γ`-invariants of a `Δ`-module). ⚠ Mathlib has the ring and its
   product; the action on `Level U` is new, and it is the statement that turns the commutativity of
   a Hecke ring into the commutativity of operators.
3. **Commutation.** If `U η U = ∐ U x_t`, `U η' U = ∐ U x'_s`, and there is a bijection
   `(t, s) ↦ (s', t')` of `T × T'` with `x_t x'_s ∈ U x'_{s'} x_{t'}` for every pair, then `[UηU]`
   and `[Uη'U]` commute. In particular, for `U = ∏_v U_v` and `η, η'` supported at disjoint sets of
   places, the operators commute.
4. **Functoriality.** A bounded `Δ`-equivariant `A → B` intertwines `[UηU]` on `Level U` for `A` and
   for `B`; in particular the classical inclusion §2.4.1 and the nebentypus loading §2.4.2 are
   Hecke-equivariant.

### 3.2 The matrix recipe

1. **Certificates** (convention 7). For a section `c : ι → G` and representatives `x : T → G` of
   `U η U`, a certificate is `(σ, d, u)` with `σ : ι × T → ι`, `d : ι × T → Γ` and `u : ι × T → U`
   such that `c_i x_t^{−1} = d(i, t) · c_{σ(i,t)} · u(i, t)` for all `(i, t)` (Jacobs, Lemmas
   2.4–2.5: "we decompose `c_i v_t^{−1}` as `d(i,t) c(i,t) u(i,t)`"). Certificates exist for every
   `c` and `x`, since `c_i x_t^{−1}` lies in exactly one double coset.
2. **The recipe.** `([UηU] φ)(c_i) = ∑_t φ(c_{σ(i,t)}) ∣ (u(i, t) x_t)` (Jacobs, pp. 20–21:
   "`(U_p φ)(c_i) = ∑_t φ(c(i,t)) | κ(u(i,t) v_t)_p`"): `φ(c_i x_t^{−1}) = φ(d c_σ u) = φ(c_σ) ∣ u`.
3. **The block matrix.** Define `ε_{ij} := ∑_{t : σ(i,t) = j} (· ∣ (u(i,t) x_t)) : A → A` and the
   block operator `blockOp ε` on `c₀(ι × J, K)` (the compact-operators roadmap's §0.2.6); prove the
   transport `evalAtReps c ∘ [UηU] = blockOp ε ∘ evalAtReps c` (Jacobs, p. 21: "`U_p` can be
   represented as `|I|²` endomorphisms `ε_{i,j}`"). At a neat level `[UηU]` *is* `blockOp ε` under
   the model isomorphism; in general `blockOp ε` preserves the image `∏_λ A^{Γ_λ}` and restricts to
   `[UηU]` on it.
4. **Certificates versus choices.** Two certificates for the same `(c, x)` give the same block
   operator (the recipe is an identity in `φ`); two sections give block operators conjugate by the
   transition operator of §2.5.2; two families of representatives give block operators with the same
   action on the image. All three are theorems, not conventions.

### 3.3 The standard operators on `D`

`U = U^{(p)} × ∏_𝔭 U_𝔭` with `U_𝔭` as in §0.4.2, of wild level `≥ 𝔭^t`.

1. **`U_𝔭`.** `U_𝔭 := [U η_𝔭 U]` for `𝔭 ∈ 𝔓` (Buzzard §12: `U_j = T_{𝔭_j}`, `U_π = ∏_j U_j`;
   Jacobs's `U_p`), with the representatives `ι_𝔭(x_α)`, `α ∈ 𝒪/𝔭`, of §0.4.3:
   `U_𝔭 φ = ∑_α φ ∣ ι_𝔭(x_α)`; and `U_π := ∏_𝔭 U_𝔭`.
2. **`T_𝔮` and `S_𝔮`.** For a finite place `𝔮 ∤ p` at which `D` splits and `U_𝔮 = GL₂(𝒪_𝔮)`:
   `T_𝔮 := [U η_𝔮 U]` and `S_𝔮 := [U ϖ_𝔮 U] = (· ∣ ι_𝔮(ϖ_𝔮))`, independent of the uniformiser
   (Buzzard §12); `S_𝔮` is an isometric automorphism.
3. **Diamond operators.** For `U_𝔭 = U₁`-type inside `U₀`-type and `d ∈ (𝒪/𝔭^t)^×`,
   `⟨d⟩ := (· ∣ δ_d^{−1})` with `δ_d = ι_𝔭(diag(1, d̃))` (§0.4.4), an action of `(𝒪/𝔭^t)^×` on
   `Level U` (Buzzard §11: "`u` act by `f ↦ f|u^{−1}` … the Diamond operators at primes above `p`").
4. **Commutativity.** The `T_𝔮`, `S_𝔮` for all `𝔮 ∤ p 𝔫 disc(D)` commute with one another, with
   every `U_𝔭`, and with the diamond operators; the `U_𝔭` for different `𝔭` commute; `U_𝔭` commutes
   with `⟨d⟩` (Buzzard §12: "A standard argument shows that the endomorphisms `T_v` and `S_v` all
   commute with one another"). The proof: operators supported at disjoint sets of places commute
   (§3.1.3); at a single `𝔮 ∤ p`, the spherical Hecke ring
   `HeckeRing (M₂(𝒪_𝔮) ∖ {det = 0}) GL₂(𝒪_𝔮) ℤ` is commutative, by Gelfand's trick — the transpose
   is an anti-automorphism fixing `GL₂(𝒪_𝔮)` and every double coset, by the elementary-divisor form
   `GL₂(𝒪) diag(ϖ^a, ϖ^b) GL₂(𝒪)` of the double cosets (Shimura, Proposition 3.8 and Theorem 3.24),
   and §3.1.2 transports commutativity to the operators; at `𝔭`, `δ_d` normalises `U` and commutes
   with `η`. ⚠ Nothing else at `𝔭` is claimed to commute with `U_𝔭`.
5. **The Hecke algebra.** `𝕋(U) := ℤ[T_𝔮, S_𝔮 (𝔮 ∤ p 𝔫 disc D), U_𝔭 (𝔭 ∈ 𝔓), ⟨d⟩]`, a commutative
   subring of `End_K (S^D_κ(U))` — Buzzard §13's "set of Hecke operators `T`" together with
   `φ = U_π`.

### 3.4 The radius improvement and the norm

1. Every representative `x = ι_𝔭(x_α)` of `U η_𝔭 U`, and every `u x` with `u ∈ U`, has
   `‖det θ_𝔭(u x)‖ = ‖ϖ‖`, hence `‖a(θ_𝔭(u x))‖ ≤ ‖ϖ‖` (§1.1.2). Consequently the Möbius map of
   `θ_𝔭(u x)` sends the closed unit polydisc into the polydisc of radius `‖ϖ‖` about a point of `𝒪`
   (Buzzard, Lemma 8.1(b)), and `f ↦ f ∣ u x` factors as the restriction `A_κ → A_{κ,1}` (the disc
   model at radius `‖ϖ‖`, compactoid by the `p`-adic-functional-analysis roadmap's §4.4.4 and the
   compact-operators roadmap's §0.3.4) followed by a bounded map `A_{κ,1} → A_κ` (Buzzard, Lemma
   12.2: "`U_π` is the composite of the natural inclusion `S^D_κ(U; r) → S^D_κ(U; r|π|)` and a
   continuous norm-decreasing map"; Buzzard 2004, Lemma 4). This is the restriction-of-radius
   criterion of the compact-operators roadmap's §0.3.3.
2. `‖[UηU]‖ ≤ 1` for every `η ∈ Δ_t` (§3.1.1), in particular `‖U_𝔭‖ ≤ 1`; hence every slope of `U_𝔭`
   is nonnegative (§4.2.3).

### 3.5 Compactness

1. **Row decay of the certificate blocks.** Let `κ` have expansion data at level `(M_t, ρ)` and let
   `η ∈ Δ_t` satisfy `‖det θ_𝔭(η)‖ ≤ σ` at the place `𝔭` of the weight, with `ρ ≤ σ < 1`. Then every
   `u x_t` in a certificate has `‖det θ_𝔭(u x_t)‖ ≤ σ` (units have determinants of norm `1`), so by
   §1.2.4 every block `ε_{ij}` has `‖matrixCoeff ε_{ij} m r‖ ≤ σ^{|m|}` — Jacobs's "`U_p` type"
   hypothesis (his Lemma 2.7: "every entry in `D(1/3) ε_{k,l}` is in `𝒪_3`").
2. **`U_𝔭` is compact** (Buzzard, Lemma 12.2; Jacobs, Lemma 2.7). Under clause 1, `blockOp ε` is
   compactoid on `c₀(ι × ℕ^I, K)` (the compact-operators roadmap's §0.2.6 and §0.2.8), so `[UηU]` is
   compactoid on the orthonormalisable `S^D_κ(U)` at a neat level and completely continuous on the
   (Pr) module `S^D_κ(U)` at every level (its §0.4.2). For `η = η_𝔭`, `σ = ‖ϖ‖`: `U_𝔭` is compact at
   every weight whose expansion data at level `M_t` has `ρ ≤ ‖ϖ‖` — every analytic weight at a deep
   enough level (§1.2.7) — with row decay `‖ϖ‖^{|m|}`; and for every `ρ ≤ 1`, `U_𝔭` is compact by
   §3.4.1, without a rate. `U_π` is compact as a product of commuting compact operators.
3. The operators away from `p` are bounded and not compact in general (`S_𝔮` is an isometric
   automorphism of an infinite-dimensional space), and nothing about their spectrum is claimed.

### Examples

For `ℍ[ℚ]`, `p = 3`, `U = U₁(9)` and the weight `u ↦ u^s` of Layer 1's examples: the block matrix of
`U_3` is `((0 ε₀₁ ε₀₂), (ε₁₀ 0 ε₁₂), (ε₂₀ ε₂₁ 0))` with `ε_{ij}` the operator presented by Jacobs's
generating functions (2.1.4)–(2.1.9) (the misprint in (2.1.6) corrected), each block a single
`(· ∣ u(i,t) x_t)`; `‖det θ_3(x_t)‖ = ‖3‖` and the row decay `‖3‖^m`; the diamond operator
`W = [U₁(9) μ U₁(9)]` for `μ = ι_3(diag(1, 4))`, its three eigenblocks with eigenvalues `1, ω, ω²`
over `ℚ_3(ζ_3)` (Jacobs (2.1.14)), and its commutation with `U_3`; `T_ℓ` for `ℓ ∉ {2, 3}` commuting
with `U_3`; at weight two, `U_𝔭` on `K^{h(U)}` is the matrix with entries `#{t : σ(i, t) = j}`; the
Hecke ring `HeckeRing Δ_2 U₁(9) ℤ` acting on `S^D_κ(U₁(9))`.

### Dependencies

Layers 0–2; Mathlib's `HeckeRing`; the compact-operators roadmap's §§0.2–0.3; the
`p`-adic-functional-analysis roadmap's §4.4.4.

---

## Layer 4: the Fredholm determinant, finite-slope subspaces and families

`κ` has expansion data at level `(M_t, ρ)` with `ρ ≤ ‖ϖ‖`, `U` has wild level `≥ 𝔭^t`, and `U_𝔭` is
the compact operator of §3.5 on `S := S^D_κ(U)`; `c` is a section of the class set and `ε` a
certificate for `U η_𝔭 U`. The compact-operators roadmap is cited by section number throughout.

### 4.1 The determinant `det(1 − T·U_𝔭)`

1. **At a neat level.** Define `heckeCharPowerSeries c ε := charPowerSeries (blockOp ε)` (the
   compact-operators roadmap's §1.2.2), an entire power series with constant term `1` (its §1.3.1),
   and prove it equal to `det(1 − T·U_𝔭)` in the sense of its §1.5.1 on the orthonormalisable `S`.
   Prove it independent of the section and the certificate (Buzzard, Corollary 2.6): two block
   operators from two sections are conjugate by the transition operator of §2.5.2, and its §1.4.2
   applies. Buzzard §13 and Jacobs p. 21 ("we obtain the matrix of `U_p` with respect to the
   topological basis") define the series this way.
2. **At every level.** Define `heckeCharPowerSeriesPr c ε E := charPowerSeries (blockOp ε ∘ E)` for
   any continuous projector `E` of `c₀(ι × ℕ^I, K)` onto the image of `evalAtReps c` — for instance
   `stabProj` of §2.6.2 — and prove it independent of `E` (its §1.4.1: `blockOp ε ∘ E` and
   `blockOp ε ∘ E'` have the same determinant because both compute the determinant of the
   restriction of `blockOp ε` to the image extended by zero), equal to `heckeCharPowerSeries` when
   the level is neat, and equal to the determinant of the compact operator `U_𝔭` on the (Pr) module
   `S` in the sense of its §1.5.2 (Buzzard §2, pp. 18–19: "`det(1 − Xφ) = det(1 − X(φ ⊕ 0))`"). Keep
   both definitions: the neat one takes certificates only, and every base-change and Riesz statement
   below is stated for it; the (Pr) one is the definition for `F ≠ ℚ`.
3. **Eigenforms are reciprocal roots.** For `a ∈ K`, `evalAt a (det(1 − T·U_𝔭)) = 0` if and only if
   `a ≠ 0` and `a^{−1}` is an eigenvalue of `U_𝔭` on `S` (its §3.2.1 through `evalAtReps`, at any
   level with a complete family of representatives).
4. **Multiplicativity.** For a decomposition `S = ⊕_ε S(ε)` into `U_𝔭`-stable closed summands — the
   eigenspaces of a diamond operator or of any operator commuting with `U_𝔭` and diagonalisable with
   finitely many eigenvalues, after base change to a field containing them —
   `det(1 − T·U_𝔭) = ∏_ε det(1 − T·U_𝔭 | S(ε))` (its §1.6.4); Jacobs's factorisation (2.1.14) of
   `det(1 − T·U_3)` along the `W`-eigenblocks is the instance.

### 4.2 Riesz theory and the finite-slope subspaces

1. **The Riesz decomposition on `S`.** For a zero `a` of `det(1 − T·U_𝔭)` of order `h`:
   `S = N(a) ⊕ F(a)` with `N(a) = ker ((1 − a U_𝔭)^h)` of dimension `h`, the generalised eigenspace
   of the eigenvalue `a^{−1}`, and `F(a)` closed and `U_𝔭`-stable with `1 − a U_𝔭` bijective on it
   (its §3.2.2, transported along the model isomorphism at a neat level and along the (Pr)
   presentation in general; over every complete `K`).
2. **Slope subspaces.** For `s ∈ ℝ` let `Q_{≤ s}` be the polynomial factor of `det(1 − T·U_𝔭)`
   carrying the slopes at most `s` (its §4.3.1, through the Newton-polygons roadmap), and define
   `S_{≤ s} := ker (Q_{≤ s}^*(U_𝔭))`, `S_{> s}` its `U_𝔭`-stable closed complement (its §4.3.2):
   `S_{≤ s}` is finite-dimensional of dimension the number of slopes at most `s` counted with
   multiplicity, `S_{≤ s} ⊆ S_{≤ s'}` for `s ≤ s'`, and after base change to an algebraically closed
   field `S_{≤ s}` is the sum of the generalised eigenspaces of `U_𝔭` for the eigenvalues `λ` with
   `v_p(λ) ≤ s`. The *finite-slope forms* are `S^{fs} := ⋃_s S_{≤ s}`, the span of the generalised
   eigenvectors with nonzero eigenvalue; the *ordinary forms* are `S_{≤ 0}`.
3. **Slopes.** Every eigenvalue `λ ≠ 0` of `U_𝔭` has `v_p(λ) ≥ 0` (§3.4.2 and its §4.4.1), and the
   multiset of slopes `v_p(λ)` of the eigenvalues of `U_𝔭` on `S ⊗ ℂ_p`, counted with algebraic
   multiplicity, is the multiset of slopes of the Newton polygon of `det(1 − T·U_𝔭)` (its §4.2.2).

### 4.3 The Hecke algebra on the finite-slope subspaces

1. Every element of `𝕋(U)` commutes with `U_𝔭` (§3.3.4), hence preserves `N(a)`, `S_{≤ s}` and
   `S_{> s}` (its §3.5.1) and acts on the finite-dimensional `S_{≤ s}` by commuting endomorphisms.
2. **Eigensystems.** Over an algebraically closed complete `K`, every nonzero `S_{≤ s}` (and every
   `N(a)`) contains a common generalised eigenvector of `𝕋(U)`: a *finite-slope eigenform* `f` with
   a system of eigenvalues `λ_f : 𝕋(U) → K`, `λ_f(U_𝔭) ≠ 0` (its §3.5.2; Buzzard §5's `φ`-finite
   systems of eigenvalues). The systems of eigenvalues occurring in `S_{≤ s}` are finitely many, and
   every system with `λ(U_𝔭) ≠ 0` occurring in `S` occurs in some `S_{≤ s}`.
3. Forms in `ker U_𝔭` — "infinite slope" — are invisible to the determinant and are not finite-slope
   forms; nothing is claimed about them.

### 4.4 The slope bound

1. In the block model with expansion data of decay `ρ ≤ ‖ϖ‖`,
   `‖matrixCoeff (blockOp ε) (λ, m) (μ, r)‖ ≤ ‖ϖ‖^{|m|}` (§3.5.1), so the compact-operators
   roadmap's §4.4.2 with the weight `w(λ, m) := |m|` on `ι × ℕ^I` gives `‖charCoeff n‖ ≤ ‖ϖ‖^{f(n)}`
   with `f(n) := ∑_{k<n} d_k`, where `d_0 ≤ d_1 ≤ ⋯` enumerates the multiset
   `{|m| : (λ, m) ∈ ι × ℕ^I}` in nondecreasing order — for `|I| = 1`, `d_k = ⌊k / h(U)⌋`. In polygon
   form: the Newton polygon of `det(1 − T·U_𝔭)` lies on or above the polygon with unit slopes
   `d_k · v_p(ϖ)` (Jacobs, Theorem 2.12's lower bound at `t = 3`; Buzzard §13's setting).
2. **What the bound says.** The partial sums of the slopes `s_0 ≤ s_1 ≤ ⋯` of `U_𝔭` satisfy
   `∑_{k<n} s_k ≥ v_p(ϖ) ∑_{k<n} d_k` for every `n`; hence
   `dim S_{≤ s} ≤ max {n | v_p(ϖ) ∑_{k<n} d_k ≤ n s}`, and for `|I| = 1` this is
   `dim S^D_κ(U)_{≤ s} ≤ h(U) · (⌊2s / v_p(ϖ)⌋ + 2)`, a bound uniform in the weight — the
   Gouvêa–Mazur-type finiteness that the eigenvariety machine needs. ⚠ The bound does **not** say
   `s_n ≥ d_n v_p(ϖ)`: a polygon lying above another may have more small slopes (the
   compact-operators roadmap's §4.4 examples).
3. The bound is attained when the rescaled leading minors of the block matrix are units (its
   §4.4.4); at which weights that happens is the spectral-halo roadmap's question (Jacobs, Theorem
   2.12; Liu–Wan–Xiao).

### 4.5 Base change of the coefficient field

1. For an isometric `F_𝔭`-algebra embedding `ι : K ↪ L` of complete fields, a weight `κ` over `K`
   with expansion datum `col` gives the weight `ι ∘ κ` over `L` with datum `map ι ∘ col` (the
   evaluation condition transports because `ι` is continuous and injective on `𝒪`); the actions, the
   certificate blocks and the determinants correspond: `ι_* (f ∣_κ γ) = (ι_* f) ∣_{ι κ} γ`,
   `matrixCoeff (ε_L) = ι ∘ matrixCoeff (ε_K)`, and `det(1 − T·U_𝔭)_L = map ι (det(1 − T·U_𝔭)_K)`
   (the compact-operators roadmap's §1.7.1; Buzzard, Lemma 2.13). Hence the eigenvalues, slopes,
   multiplicities and finite-slope decompositions of `U_𝔭` may be read over `ℂ_p`, and
   `S_{≤ s}(L) = S_{≤ s}(K) ⊗_K L`.
2. ⚠ The embedding `S^D_κ(U) ⊗_K L → S^D_{ικ}(U)` is injective with dense image and is not
   surjective; only the finite-slope parts are base-changed on the nose.

### 4.6 Families of weights

1. **Weights over a Banach–Tate ring.** Let `R` be a Banach–Tate `𝒪_𝔭`-algebra (the
   `p`-adic-functional-analysis roadmap's §0.4; an affinoid algebra `O(X)` or `Λ^{>1/p}[1/T]`) that
   admits a jointly injective family of bounded homomorphisms to complete fields (its §4.1.6). A
   *family of weights over `R`* is `(n, v, col)` with `n, v : 𝒪^× → R^×` continuous and `col` valued
   in `R⟨z_i⟩` satisfying the conditions of §1.2.2 with `R` for `K`. Every statement of Layers 1–3
   holds with `A_{κ,R} := c₀(ℕ^I, R)`: the several-variable identity theorem over `R` (through the
   jointly injective family), the cocycle, the action, the spaces `L(U, A_{κ,R})` as `R`-modules,
   the block model `c₀(ι × ℕ^I, R)` at a neat level, and the compactoid `U_𝔭` with the same row
   bound; hence `det(1 − T·U_𝔭) ∈ R{{T}}`. ⚠ Over a coefficient ring in which `p` is not invertible
   — `Λ^{>1/p}[1/T]` — the averaging projector of §2.6.2 does not exist, and the theory requires a
   **neat** level (every `Γ_λ` acting trivially); this is Liu–Wan–Xiao's Hypothesis 2.10, and it is
   why the spectral-halo roadmap assumes it.
2. **Specialisation.** For a bounded homomorphism `x : R → K` to a complete field, `x ∘ (n, v, col)`
   is a weight over `K`, and `det(1 − T·U_𝔭)` specialises:
   `map x (det(1 − T·U_𝔭)_R) = det(1 − T·U_𝔭)_{x ∘ κ}` (the compact-operators roadmap's §1.7.4); at
   a coprime factorisation `det(1 − T·U_𝔭)_R = Q · S` over `R` the Riesz–Coleman decomposition (its
   §3.4) gives a finite-slope submodule `ker Q^*(U_𝔭)` of `L(U, A_{κ,R})`, projective of rank
   `deg Q`, stable under `𝕋(U)`, whose specialisation at every `x` is the decomposition of the fibre
   (its §3.4.4 and §4.3.5). This is the local content of Buzzard §13's `M_X` and of a slope-`≤ h`
   decomposition in a family; the links between radii (his Lemma 13.1) and the gluing are out of
   scope.
3. **The universal weight over an affinoid.** For an affinoid subdomain `X` of weight space and the
   induced `κ : 𝒪_p^× → O(X)^×` (Buzzard §10), Proposition 8.3 applied over `O(X)` gives expansion
   data at some level: a family in the sense of clause 1. The halo family over `Λ^{>1/p}[1/T]` — the
   universal character of that roadmap's §5.6.6 with the level chosen uniformly on the annulus — is
   the spectral-halo roadmap's integral model.

### Examples

For `ℍ[ℚ]`, `p = 3`, `U₁(9)` and the weight `u ↦ u^s`: `det(1 − T·U_3)` from the block matrix of
Layer 3's example, its independence of the nine factorisations, its base change to `ℚ_3(ζ_3)` and
the factorisation into the three `W`-eigenblocks
`det(1 − T·M_{11}) det(1 − T·M_{22}) det(1 − T·M_{33})` (Jacobs, (2.1.14) and Lemma 1.15); the bound
polygon with unit slopes `⌊k/3⌋`; the Riesz decomposition at a zero and an eigenform with its system
of eigenvalues over `ℂ_3`; at weight two, `det(1 − T·U_𝔭)` is the reversed characteristic polynomial
of the `h(U) × h(U)` matrix of §3's example, with `h(U)` finite slopes; the family
`n_S(u) := padicExp (S · padicLog u)` on `1 + 3 ℤ_3` over `R = K⟨S⟩`, with
`col(c, d) = d^S ∑_m (S choose m) (c/d)^m z^m` at the `Σ₁`-type level of `U₁(9)`, whose
`det(1 − T·U_3) ∈ K⟨S⟩{{T}}` specialises at `S = s` to the determinant at `u ↦ u^s`.

### Dependencies

Layers 1–3; the compact-operators roadmap, §§1.2–1.7, 3.2, 3.4–3.5, 4.2–4.4; the Newton-polygons
roadmap for the polygon; the `p`-adic-functional-analysis roadmap's §0.4, §4.1.6 and §5.6.

---

## Layer 5: the theta operator and classicality

`F_𝔭 = ℚ_p`, so `A = K⟨z⟩` in one variable and `v_p(ϖ) = 1`; `k ∈ ℕ`; `ψ` a character of `ℤ_p^×` of
finite order with conductor dividing `p^α`; `κ := (u ↦ u^k ψ(u), v)` and
`κ' := (u ↦ u^{−k−2} ψ(u), v)` the two classical-shape weights of §1.3.4 (Buzzard 2004's
`(k_B, ε_p)` and `(2 − k_B, ε_p)` with `k_B = k + 2`); `U` has wild level `≥ p^t` with
`t ≥ max(α, 1)`. Everything is at the single place `p` of the sources; the several-variable version
is in "Beyond".

### 5.1 The theta operator

1. Define `θ^r := (d/dz)^r` on `K⟨z⟩`: `z^m ↦ (m)_r z^{m−r}` with `(m)_r = m (m−1) ⋯ (m−r+1)` the
   descending factorial (Mathlib's `Nat.descFactorial`), an integer, so `θ^r` is the operator
   presented by a column-finite matrix with entries in the unit ball (the compact-operators
   roadmap's §0.3.1), bounded of norm at most `1`, with `θ^r ∘ θ^s = θ^{r+s}`. On the disc model at
   level `h` (§2.3.3) it acts blockwise, and `d/dz = p^{−h} d/dw` on the disc `z = a + p^h w`; carry
   the scalar `p^{−hr}` explicitly.
2. `ker θ^{k+1}` is the space `L_k` of polynomials of degree at most `k` — the classical weight
   module (Buzzard 2004, Proposition 4: "The kernel of `θ^{1−k}` is precisely the classical forms")
   — and on the disc model the locally polynomial functions of degree at most `k`, of dimension
   `(k + 1) p^h` (Liu–Wan–Xiao, (3.21.1)). ⚠ `θ^{k+1}` has dense range and is not surjective onto
   `K⟨z⟩`: its matrix is a shift composed with the diagonal `((m + k + 1)_{k+1})_m` whose inverse is
   unbounded, so no exact sequence of Banach spaces is asserted anywhere below.
3. **On forms.** Let `c : D_f^× →* K^×`, `c(g) := |nrd(g)|_f · det θ_p(g)` (§0.2.4). Then `c(γ) = 1`
   for `γ ∈ D^×` (the product formula), `c(u) = det θ_p(u)` for `u` in a compact open `U` (`|nrd|_f`
   is trivial on compact subgroups), `c(η_p) = 1` and `c(η_ℓ) = ℓ^{−1}` for `ℓ ≠ p`. Define
   `(θ^{k+1} φ)(g) := c(g)^{−(k+1)} · θ^{k+1}(φ(g))` (Buzzard 2004, §7:
   "`(θ^{1−k}(f))(g) = (|ν(g)| det(g_p))^{1−k} d^{k−1} f(g) / dz^{k−1}`") and prove, by §5.2.3, that
   it maps `S^D_κ(U)` to `S^D_{κ'}(U)`; for a general tame level the character `|nrd|_f` is the norm
   class of the spectral-halo roadmap's Atkin–Lehner data.

### 5.2 Bol's identity and the equivariance

1. **Bol's identity.** For `γ ∈ M₂(K)` with `d ≠ 0`, writing `N := a z + b`, `L := c z + d` and
   `D := det γ`, and for all `r, j ∈ ℕ`,
   `(d/dz)^r (N^{j+r} L^{−(j+1)}) = D^r · (j + r)_r · N^j L^{−(j+r+1)}` in `K⟦z⟧`, with `L^{−1}` the
   inverse power series (Bol 1949; Buzzard 2004 §7's display
   `(d^{k−1}/dz^{k−1})((cz+d)^{k−2} F((az+b)/(cz+d))) = (ad−bc)^{k−1} (cz+d)^{−k} F^{(k−1)}((az+b)/(cz+d))`
   read on the columns `F = z^{j+r}`). Prove it in this subtraction-free column form by induction on
   `r` with `j` generalised: one derivative produces two terms, the induction hypothesis applies at
   `j` and at `j + 1`, the two descending-factorial recurrences give `(j + r + 1)_{r+1}`, and the
   constant `a L − c N = D` is the cocycle. ⚠ No Leibniz rule and no binomial theorem are needed.
   State also the vanishing `(d/dz)^{k+1} (N^i L^{k−i}) = 0` for `i ≤ k`, the polynomial columns of
   degree `k`.
2. **Column form of the action.** The `i`-th column of `f ∣_κ γ` — the image of `z^i` — is
   `j_κ(γ) · w_γ^i = u_γ · L^k · N^i L^{−i} = u_γ N^i L^{k−i}` for the classical shape
   `j_κ(γ) = u_γ L^k` with the constant `u_γ := ψ(d) v(det γ)`, and the `i`-th column of `∣_{κ'}` is
   `u_γ N^i L^{−k−2−i}`.
3. **Equivariance** (Buzzard 2004, §7). For `γ ∈ M_t`,
   `θ^{k+1} (f ∣_κ γ) = det(γ)^{k+1} · (θ^{k+1} f) ∣_{κ'} γ` for all `f ∈ K⟨z⟩`: column by column
   from clause 1 at `r = k + 1` (columns `i ≥ k + 1`, with `j = i − k − 1`) and the vanishing
   (columns `i ≤ k`), with the same constant `u_γ` on both sides. State the hypothesis on the
   automorphy factors — `j_κ(γ) = u_γ L^k` and `j_{κ'}(γ) = u_γ L^{−k−2}` for one constant `u_γ` —
   rather than on the characters. ⚠ The identity is false if `ψ` is replaced by a character that is
   not constant on the discs `d + c ℤ_p`: for `n = u^3`, `n' = u^1` (two honest weights), `γ` with
   `c ≠ 0` and `f = 1`, the left side is `c ≠ 0` and the right side is `0`, because differentiating
   `n(cz + d)` leaves a term the other side cannot match. This is why the finite part of a
   classical-shape weight is locally constant at the level, and why the equivariance is not stated
   for a general pair of weights.
4. **Intertwining with Hecke operators.** For `η ∈ Δ_t`,
   `θ^{k+1} ∘ [UηU] = |nrd(η)|_f^{−(k+1)} · [UηU] ∘ θ^{k+1}` as maps `S^D_κ(U) → S^D_{κ'}(U)`, from
   clause 3 and `c(g x^{−1}) = c(g) c(x)^{−1}`; in particular
   `θ^{k+1} ∘ U_p = p^{k+1} · U_p ∘ θ^{k+1}`, `θ^{k+1} ∘ T_ℓ = ℓ^{k+1} · T_ℓ ∘ θ^{k+1}` and
   `θ^{k+1} ∘ S_ℓ = ℓ^{2(k+1)} · S_ℓ ∘ θ^{k+1}` (Buzzard 2004:
   "`[UηU] θ^{1−k} = |ν(η)|^{k−1} θ^{1−k} [UηU]`", "`T_l θ^{1−k} = l^{1−k} θ^{1−k} T_l`"). In the
   block model at a neat level, with the same certificate for both weights:
   `θ^{k+1} ∘ blockOp ε_κ = p^{k+1} · blockOp ε_{κ'} ∘ θ^{k+1}`, where `θ^{k+1}` acts on
   `c₀(ι × ℕ, K)` blockwise.

### 5.3 The classical subspace and the determinant identity

1. `ker (θ^{k+1} : S^D_κ(U) → S^D_{κ'}(U))` is the classical subspace: the forms with values in
   `L_k`, i.e. `S^D_{k+2, w}(U)(ψ)` with the nebentypus loaded (§2.4.2) — Buzzard 2004, Proposition
   4's first sentence. It is `U_p`-stable and finite-dimensional, of dimension `h(U) (k + 1)` at a
   neat level and `h(U) (k + 1) p^h` in the disc model at level `h` (Liu–Wan–Xiao (3.21.1)).
2. **The determinant identity.** At a neat level and for classical-shape weights,
   `det(1 − T·U_p | S^D_κ(U)) = charpolyRev (U_p | S^{cl}) · det(1 − p^{k+1} T · U_p | S^D_{κ'}(U))`,
   i.e. the second factor is `rescale (p^{k+1})` of the determinant at weight `κ'`. Proof: on the
   block model `θ^{k+1} = Diag ∘ Shift` with `Shift` the coordinate shift `(λ, m) ↦ (λ, m − k − 1)`
   (killing the classical coordinates), `Diag = diag ((m + k + 1)_{k+1})`, and `Shift` has the
   section `Ins : e_{(λ,m)} ↦ e_{(λ, m + k + 1)}` with `Shift ∘ Ins = 1` and
   `Ins ∘ Shift = 1 − π^{cl}`, the projection off the classical coordinates. The intertwining §5.2.4
   composed with `Ins` gives `Diag ∘ (Shift ∘ U_p ∘ Ins) = (p^{k+1} U'_p) ∘ Diag`, a diagonal
   intertwining by the unit entries `(m + k + 1)_{k+1}` — so `Shift ∘ U_p ∘ Ins` and `p^{k+1} U'_p`
   have the same principal minors (the compact-operators roadmap's §1.4.3, with no inverse of
   `Diag`); then
   `det(1 − T·U_p (1 − π^{cl})) = det(1 − T·(U_p Ins) Shift) = det(1 − T·Shift (U_p Ins))` (its
   §1.4.1) and `det(1 − T·U_p) = charpolyRev (U_p|_{cl}) · det(1 − T·U_p (1 − π^{cl}))` since `U_p`
   preserves the classical coordinates (its §1.6.1). This is the determinant-level content of
   Liu–Wan–Xiao's exact sequence `0 → S^{cl} → S^{D,†}_{(k,ψ)} → S^{D,†}_{(−k−2,ψ)} → 0`
   "equivariant for `U_p` on the first two spaces and `p^{k+1} U_p` on the third" (§3.23, Step III,
   which they cite to Jones's BGG resolution); ⚠ no exactness is asserted (§5.1.2), and none is
   needed.
3. **Consequences for slopes.** The slope multiset of `U_p` on `S^D_κ(U)` is the union of the slope
   multiset on `S^{cl}` — `h(U)(k+1)` slopes — and the slope multiset on `S^D_{κ'}(U)` shifted by
   `k + 1` (the Newton-polygons roadmap's §§5.1–5.2): every non-classical part of the spectrum has
   slope at least `k + 1`.

### 5.4 Classicality

1. **Small slope implies classical** (Buzzard 2004, Proposition 4; the quaternionic form of
   Coleman's theorem). If `f ∈ S^D_κ(U)` is a `U_p`-eigenform with eigenvalue `λ` and
   `v_p(λ) < k + 1`, then `f` is classical: `θ^{k+1} f` is a `U_p`-eigenform on `S^D_{κ'}(U)` with
   eigenvalue `λ p^{−(k+1)}` of negative valuation by §5.2.4, `‖U_p‖ ≤ 1` (§3.4.2) forbids an
   eigenvalue of norm greater than `1`, so `θ^{k+1} f = 0`, and §5.3.1 applies. State the abstract
   lemma behind it — an operator of norm at most `1`, intertwined with another up to a scalar `c`,
   kills every eigenvector whose eigenvalue has norm greater than `‖c‖` — and the generalised form:
   `S^D_κ(U)_{≤ s} = S^D_{k+2,w}(U)(ψ)_{≤ s}` for every `s < k + 1` (from §5.3.3 and the uniqueness
   of the slope decomposition, the compact-operators roadmap's §3.4.2; Loeffler, Theorem 3.9.6 in
   his generality). In words: every form of slope less than `k + 1` is classical, and the
   finite-slope eigensystems of slope less than `k + 1` are exactly the classical ones.
2. ⚠ **The converse is not here.** That a classical eigenform has slope at most `k + 1` is the half
   of Buzzard's Proposition 4 that uses Miyake's Theorem 4.6.17 and Jacquet–Langlands (convention
   8); the spectral-halo roadmap obtains it from an Atkin–Lehner symmetry, and this roadmap claims
   nothing about the slopes of classical forms beyond `≥ 0`.
3. Eigenforms of slope exactly `k + 1` may or may not be classical (Buzzard 2004: "one can find both
   classical and non-classical forms with `v_p(λ) = k − 1`"); nothing is stated about them.

### Examples

`θ^{k+1}` on `K⟨z⟩`, `z^m ↦ (m)_{k+1} z^{m−k−1}`, with kernel the polynomials of degree at most `k`;
Bol's identity at `r = 1`: `(N^{j+1} L^{−(j+1)})' = D (j+1) N^j L^{−(j+2)}`; the counterexample
`n = u^3`, `n' = u^1`, `c ≠ 0`, `f = 1`; for `ℍ[ℚ]` at `U₁(9)` and `κ = (u^k, 1)`:
`θ^{k+1} ∘ U_3 = 3^{k+1} U_3 ∘ θ^{k+1}`, the classical subspace of dimension `3(k+1)`, the identity
`det(1 − T·U_3) = charpolyRev (U_3|_{cl}) · det(1 − 3^{k+1} T·U_3 | S_{κ'})`, and every eigenform of
slope less than `k + 1` classical; at `k = 0` (weight two), `θ = d/dz`, the classical forms are the
functions on the three classes, and every ordinary eigenform is classical.

### Dependencies

Layers 1–4 at the single place `p`; the compact-operators roadmap's §§1.4, 1.6, 3.4 and 4.3; the
Newton-polygons roadmap's §5; Mathlib's `PowerSeries.derivative` and `Nat.descFactorial`.

---

## Dependency graph

```text
Layer 0 ──┐
          ├──→ Layer 2 ──→ Layer 3 ──→ Layer 4 ──→ Layer 5
Layer 1 ──┘                                ↑          ↑
                       compact-operators ──┘──────────┘
```

Layers 0 and 1 are independent: Layer 0 is the arithmetic of `D` and its adeles, Layer 1 the
analysis of the weight action, and neither cites the other except for the dictionary between `M_t`
and `SigmaNorm` (§1.1.1). Layer 2 puts them together; Layer 3 needs Layer 2 and the compactoid
operators of the compact-operators roadmap's Layer 0; Layer 4 needs Layer 3 and that roadmap's
Layers 1–4; Layer 5 needs Layers 1, 3 and 4 and is stated at a single place with `F_𝔭 = ℚ_p`. The
`p`-adic-functional-analysis roadmap is cited on every page of Layers 1–4, the Newton-polygons
roadmap in §§4.2, 4.4 and 5.3, the global-number-fields roadmap and the FLT project in Layer 0, the
adic-spaces roadmap nowhere (the eigenvariety is out of scope). The spectral-halo roadmap is a
consumer and is never a dependency.

## Acceptance examples

The following should be proved alongside the general theory, and they are the things a reviewer
should check are present. `D = ℍ[ℚ]`, `p = 3`, `K ⊇ ℚ_3` unless stated.

- `ℍ[ℚ]` is a totally definite quaternion algebra, split at every odd prime, with the Hurwitz order
  as a maximal order with `24` units; it is right-Euclidean for the reduced norm, so
  `D_f^× = D^× U₀(1)`; the rigidification `θ_3` from `ν = √−2 ≡ 1 mod 3`.
- `U₀(1)` and `U₁(9)` are compact open; the class set of `U₁(9)` is `{c_0, c_1, c_2}` with trivial
  stabilisers; `U₁(9) η_3 U₁(9) = ∐_{t<3} U₁(9) ι_3(((3 0), (9t 1)))`; the nine factorisations
  `c_i x_t^{−1} = d(i,t) c_{σ(i,t)} u(i,t)` with `nrd d(i,t) = 1/3`.
- The algebraic weight `u ↦ u^k` at every level with `ρ = ‖3‖` and `col(c, d) = (d + c z)^k`; the
  weight `u ↦ u^s` on `1 + 3ℤ_3`, `s ∈ ℤ_3`, at the `Σ₁`-type level of `U₁(9)` with `ρ = ‖3‖` and
  the binomial datum; its cocycle derived from multiplicativity; the scalar `−1` acting by `(−1)^k`;
  the nebentypus loading of a character of conductor `3`.
- `S^D_{k+2}(U₁(9))` has dimension `3(k+1)` and embeds Hecke-equivariantly into `S^D_{u^k}(U₁(9))`
  as the polynomial-valued forms; `S^D_κ(U₁(9)) ≅ c₀(Fin 3 × ℕ, K)`; `S^D_κ(U₀(1))` is the
  invariants of the `24` units and vanishes when `n(−1) = −1`; the level–radius trade between
  `U₀(3)` at radius `‖3‖` and `U₀(9)` at radius `1`.
- `U_3` on `S^D_κ(U₁(9))` is the block operator `(ε_{ij})` with zero diagonal blocks and the six
  generating functions (2.1.4)–(2.1.9) of Jacobs, with (2.1.6)'s misprint corrected;
  `‖det θ_3(x_t)‖ = ‖3‖`, row decay `‖3‖^m`, compactoid; the diamond operator `W` at
  `μ = diag(1, 4)` commutes with `U_3` and splits `S^D_κ(U₁(9)) ⊗ ℚ_3(ζ_3)` into three eigenblocks;
  `T_ℓ` for `ℓ ∉ {2, 3}` commutes with `U_3`; the Hecke ring `HeckeRing Δ_2 U₁(9) ℤ` acts.
- `det(1 − T·U_3)` is entire, independent of the certificate, base-changes to `ℚ_3(ζ_3)` where it
  factors as `∏_{j} det(1 − T·M_{jj})` along the `W`-eigenblocks (Jacobs (2.1.14)), and its Newton
  polygon lies on or above the polygon with unit slopes `⌊k/3⌋`; at weight two it is the reversed
  characteristic polynomial of a `3 × 3` matrix.
- A Riesz decomposition of `S^D_κ(U₁(9))` at a zero of `det(1 − T·U_3)`, and a finite-slope
  eigenform over `ℂ_3` with its system of eigenvalues for `𝕋(U₁(9))`.
- The family `n_S(u) = padicExp (S · padicLog u)` over `K⟨S⟩` at the `Σ₁`-type level of `U₁(9)`, its
  `det(1 − T·U_3) ∈ K⟨S⟩{{T}}`, and its specialisation at `S = s`.
- `θ^{k+1}` on `K⟨z⟩` and its kernel; Bol's identity at `r = 1`; the counterexample `n = u^3`,
  `n' = u^1`; `θ^{k+1} ∘ U_3 = 3^{k+1} U_3 ∘ θ^{k+1}` at `U₁(9)`; the determinant identity of §5.3.2
  with the finite factor of degree `3(k+1)`; every eigenform of slope less than `k + 1` is
  classical, and at `k = 0` every ordinary eigenform is classical.

## Beyond this roadmap

⚠ **This section is a roadmap-for-a-roadmap. Do not attempt any of it here.** It records what this
roadmap is for, so that the conventions above are chosen with the sequels in mind.

The spaces `S^D_κ(U)`, the compact `U_𝔭`, the determinant `det(1 − T·U_𝔭)` with its finite-slope
decompositions and their base change, the families of §4.6 and the classicality of §5.4 are the
inputs of two sequels. The spectral-halo roadmap takes the single-place theory for `D/ℚ`, the
integral model of `S^D_κ(U)` over `Λ^{>1/p}` at the universal weight of the boundary annulus,
Liu–Wan–Xiao's Proposition 2.17 (the integral determinant specialises to `det(1 − T·U_p)` at every
halo point), the halo estimate on its coefficients, the Atkin–Lehner operators and the slope
symmetry from which the converse of §5.4.1 and the degrees of Theorem 1.3 follow, and Jacobs's
theorem that the slopes of `U_3` at `U₁(9)` are `j + ½` as its acceptance layer. The eigenvariety —
Buzzard's machine (§§4–5, §13) applied to `M_X = S^D_κ(U)` over affinoids `X` of weight space with
the links of his Lemma 13.1, Loeffler's construction for a general `G`, Chenevier's for `GL_n` — is
rigid or adic geometry over the spectral variety `{det(1 − T·U_𝔭) = 0} ⊆ 𝒲 × 𝔸¹` and belongs with
the adic-spaces roadmap; §4.6 is its local input. What the sequels ask of this roadmap is that the
spaces be defined at every analytic weight over a Banach–Tate ring and not only over a field, that
neat levels be a hypothesis with the block model as its conclusion, and that the classical subspace
be characterised as a kernel with a determinant identity — all of which is what is specified above.

Further afield: the Jacquet–Langlands correspondence and the identification of `S^D_{k,w}(U)` with
Hilbert modular forms (Buzzard §9), which is how the eigenvariety for `D` interpolates classical
eigenforms of `GL₂/F`, and Chenevier's `p`-adic Jacquet–Langlands; the classicality theorem in
several variables and for general reductive groups through the BGG resolution (Loeffler §§2.5–2.6,
Theorem 3.9.6; Jones), and the several-variable theta operators; Hida's ordinary projector
`lim U_𝔭^{n!}` and Hida families; the Galois representations attached to finite-slope eigenforms
(Carayol, Taylor), `p`-adic `L`-functions, and Emerton's completed cohomology, of which `S^{D,†}` is
the locally analytic part (Loeffler §3.10); Gross's algebraic modular forms for a general group
compact at infinity, and the Brandt-matrix computation of `S^D_{k,w}(U)` that the modular-forms
roadmap's trace formula meets through Eichler's basis problem.

## References

- K. Buzzard, *Eigenvarieties*, in *L-functions and Galois representations*, LMS Lecture Notes 320
  (2007), §§8–13 — [Buz07]. §8 (thickenings, Lemma 8.1, Proposition 8.3, weight space), §9 (the
  monoids `M_t`, the modules `L_{n,v}`, `L(U, A)`, the decomposition over the class set, the Hecke
  operators, the classical forms), §10 (`A_{κ,r}`, `S^D_κ(U; r)`, property (Pr), p. 73), §11
  (classical forms are overconvergent, loading the character, Proposition 11.1), §12 (`T_v`, `S_v`,
  `U_π`, Lemmas 12.1–12.2), §13 (the data of the eigenvariety machine, Lemma 13.1).
- K. Buzzard, *On p-adic families of automorphic forms*, in *Modular curves and abelian varieties*,
  Progress in Math. 224 (2004), 23–44 — [Bu04]. Lemma 3 (the compact restriction), Lemma 4 (the
  factorisation of `U_p`), §7 (the theta operator, Bol's identity, the intertwining, Proposition 4).
  Theorem 2 and the second half of Proposition 4 use Jacquet–Langlands and are not used.
- D. Jacobs, *Slopes of Compact Hecke Operators*, PhD thesis, Imperial College (2003) — [Jac03].
  §1.4 (the algebra `ℚ(i, j)`, the rigidifications, `U₀(1)`, `U₁(9)`, Lemma 1.22 — replaced by the
  Euclidean route), §1.5 (Definitions 1.27–1.32), §1.6 (Lemma 1.31, the matrix of `U_p`, pp. 20–21),
  §2.1 (Theorem 2.1, Lemmas 2.2–2.5, Proposition 2.6, Lemma 2.7, the generating functions
  (2.1.4)–(2.1.9), (2.1.14), Theorem 2.12, Corollary 2.16), Appendix B.1.
- D. Loeffler, *Overconvergent algebraic automorphic forms*, Proc. London Math. Soc. 102 (2011),
  193–228 — [Loe11]. §3.1 (Propositions 3.1.1–3.1.4: finiteness, discreteness, compactness at
  infinity), §3.2 (Hecke algebras), Definition 3.3.2 and Proposition 3.3.3 (the spaces `L(W)` and
  their decomposition), Theorem 3.9.6 (classicality of small slope, generalised eigenspaces), §3.10
  (completed cohomology).
- R. Liu, D. Wan, L. Xiao, *The eigencurve over the boundary of weight space*, Duke Math. J. 166
  (2017); arXiv:1412.2584v4 — [LWX]. §§2.3–2.5 (the spaces `S^{D,†,m}`, Hypothesis 2.10, `U_p`),
  Proposition 2.17, (3.21.1), and §3.23 Step III (the exact sequence read here as §5.3.2). Consumed
  by the spectral-halo roadmap; cited here for the disc-model spaces and the determinant identity.
- H. Hida, *On p-adic Hecke algebras for GL₂ over totally real fields*, Ann. of Math. 128 (1988),
  295–384, §2 and Lemma 7.1 — the classical Hilbert-modular side and the finiteness of the `Γ_λ`.
- B. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), 61–93 — the framework of forms on
  groups compact at infinity; cited in "Beyond".
- H. Fujisaki, *On the zeta-function of the simple algebra over the field of rational numbers*, J.
  Fac. Sci. Univ. Tokyo 7 (1958), 567–604; and A. Weil, *Basic Number Theory*, Springer (1967),
  Chapter IV — Fujisaki's lemma. Formalised in the FLT project as
  `NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset` (see the provenance section).
- J. Voight, *Quaternion Algebras*, GTM 288, Springer (2021) — [Voi21]. Chapter 2 (quaternion
  algebras and the reduced norm), Chapter 10 (orders), Theorem 11.3.2 and Corollary 11.3.4 (the
  Hurwitz order is Euclidean and its right ideals are principal), Theorem 27.6.8 (the idelic class
  set), Chapter 41 (Brandt matrices, cited in "Beyond").
- G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton (1971),
  Chapter 3 — [Shi71]. §3.1 (the Hecke ring `R(Γ, Δ)` and its action on `Γ`-invariants), Proposition
  3.8 (commutativity via an anti-automorphism), Theorem 3.24 (elementary divisors); and A. Krieg,
  *Hecke algebras*, Mem. AMS 435 (1990) — the references of Mathlib's `HeckeRing`.
- R. Pollack, G. Stevens, *Overconvergent modular symbols and p-adic L-functions*, Ann. Sci. Éc.
  Norm. Supér. 44 (2011), 1–42 — the left-handed monoid `Σ₀(p)` of convention 2.
- G. Bol, *Invarianten linearer Differentialgleichungen*, Abh. Math. Sem. Univ. Hamburg 16 (1949),
  1–28 — Bol's identity (§5.2.1).
- R. Coleman, *Classical and overconvergent modular forms*, Invent. Math. 124 (1996), 215–241 — the
  theta operator and the classicality of small slope for elliptic modular forms, of which Buzzard
  2004's §7 is the quaternionic transcription; and R. Coleman, *p-adic Banach spaces and families of
  modular forms*, Invent. Math. 127 (1997), 417–479, and R. Coleman, B. Mazur, *The eigencurve*, LMS
  Lecture Notes 254 (1998) — the eigencurve, cited in "Beyond".
- G. Chenevier, *Familles p-adiques de formes automorphes pour GL_n*, J. reine angew. Math. 570
  (2004), 143–217 — cited in "Beyond".
- T. Miyake, *Modular Forms*, Springer (1989), Theorem 4.6.17 — the classical `|a_p|² = p^{k−1}`
  used by the excluded half of Buzzard 2004's Proposition 4.
- The FLT project, `github.com/ImperialCollegeLondon/FLT` (Apache-2.0):
  `FLT/DivisionAlgebra/ Finiteness.lean` (Fujisaki), `FLT/HaarMeasure/` (Haar characters),
  `FLT/AutomorphicForm/ QuaternionAlgebra/` (weight-two forms and their Hecke operators,
  `AbstractHeckeOperator`).

⚠ **Orientation and normalisation.** Weights are Buzzard's pairs `κ = (n, v)` with the action
`n(cz + d) v(det γ) f((az + b)/(cz + d))` (§10, p. 72); Jacobs's character `κ_J` with his
normalisation `κ_J(cz + d)/(cz + d)²` is `n = κ_J · u^{−2}`, so his weight `u ↦ u^t` is
`n(u) = u^{t−2}` here and his `κ = u^{k+2}` is the classical `Sym^k`; Buzzard 2004 indexes the
weight by `k_B = k + 2` and writes `θ^{1−k_B}` for the `θ^{k+1}` of Layer 5; Liu–Wan–Xiao's weight
`(k, ψ)` is `(u^k ψ, 1)`. All actions are right actions (convention 2): `f ∣ γ`, double cosets
decomposed into the cosets `U x_t`, which are *right* cosets in Mathlib's terminology
(`QuotientGroup.rightRel`) and *left* cosets in Buzzard's ("the natural left coset decomposition
`∐_α U₀(π^t) ((π 0), (α π^t 1))`", proof of Lemma 12.1) — the same decomposition under two names;
`η = diag(ϖ, 1)` and the representatives `((ϖ 0), (α ϖ^t 1))`; the left-handed literature has the
unit condition on `a`, `η = diag(1, ϖ)` and the cosets `x_t U`, and the adjugate is the dictionary.
The norm-class character `|nrd(g)|_f` is Buzzard 2004's `|ν(g)|`, with `|nrd(η_ℓ)|_f = ℓ^{−1}`. The
classical weight `(k, w)` of Buzzard §9 is `n = k − 2`, `w = v + n + 1`. When transcribing a
statement, check the handedness against convention 2 and the weight normalisation against convention
5 rather than assuming them.

## Existing Lean work

The principal source of existing code is `github.com/WilliamCoram/PhD` (Apache-2.0), at commit
`747bb77` (2026-09-12): the directory `PhD/Main/QMF/` — the eleven top-level files, `Slash/` (the
right-handed dialect) and `Weight/` (the general weights), thirty-one files and 8 273 lines — for
Layers 0–4, the directory `PhD/Main/JacobsSlash/` (twenty-six files, 14 079 lines, the thesis
instance) for the acceptance examples and §0.5, and the files
`PhD/Main/LWX/{10_DiscForms, 11_Theta, 12_Bol, 12_StepOne, 15_SymPow, 16_ThetaExact}.lean` for
§2.3.3 and Layer 5. The mathematics was complete at commit `1f43221` (2026-09-11); the pin names the
commit at which the tree acquired its present layout. It is, together with the FLT project's
weight-two theory, the only formalisation of this material known to us.

The material in those directories is by William Coram, who has agreed to its integration into Tau
Ceti — with one exception that must be handled file by file. ⚠ The directory
`PhD/Main/QMF/FLTstuff/` (ninety-two files, 15 546 lines) is a vendored port of parts of the FLT
project — the finite adeles and their base change, the Haar-character machinery, and Fujisaki's
lemma — carrying FLT's copyright headers with their authors (K. Buzzard, S. Mercuri, M. Jasper, B.
Wang Peng Jun, M. Crim, Y. Dillies, D. Ledvinka, A. Yang, T. Browning, J. López-Contreras, D.
Loeffler, P. Monticone, R. Van de Velde, and W. Coram; `DivisionAlgebra/Finiteness.lean` is by
Buzzard and Coram). It is a source for §§0.2–0.3 only through the FLT project itself and with its
authors' agreement, as the porting rules require; a migration should take FLT's current versions of
those files rather than this copy, and nothing in it is claimed here as the source development's
own. The three FLT-derived design choices that the source development inherits — the `𝔸_F^f`-module
topology on `D ⊗ 𝔸_F^f` through FLT's right-action instances, the abstract Hecke operator of FLT's
`AbstractHeckeOperator`, and the weight-two space as the case of trivial coefficients — are recorded
in §2.1.3 and §3.1.

Two separate audits are recorded below, for the reason the adic-spaces roadmap gives: a declaration
with no direct `sorry` is not the same as a theorem whose dependency cone is axiom-clean. The direct
column is a file-level `grep` count, which over-counts (comments match) and sees no cross-file
dependence. At the pin above, every file listed has a direct count of **0** (the six matches in
`PhD/Main/JacobsSlash/` and the one in `PhD/Main/LWX/11_Theta.lean` are the word in comments
recording that a former hypothesis was proved). The transitive column must be regenerated at
migration by a `#print axioms` gate on the capstones in Tau Ceti CI; the source project reports
every file listed clean on `propext`, `Classical.choice` and `Quot.sound`, and that claim is to be
re-verified, not carried over.

| Roadmap section | Existing source | Direct status at the pin | Transitive status | Roadmap status |
|---|---|---|---|---|
| §0.1 quaternion algebras, rigidification, orders | `QMF/03_Quaternionic.lean` (`RigidificationAt`, `toMatrix`, `toLocal`), `JacobsSlash/U3/1_Hurwitz.lean` (the Hurwitz order, its norm and units), `U3/1_Setting.lean` (`θ₃`, `ν₃`), `CN1/2_Euclidean.lean` (the Euclidean algorithm) | no direct `sorry` | audit required | partial; the reduced norm on an abstract `D` and totally definite algebras are new |
| §0.2 the adelic group | `QMF/03_Quaternionic.lean` (`Dfx`, `globalUnits`, `unitsIncl`, `evalAlgHom`), `04_Level.lean` (the topology, `isCompact_integralTensor`, `isOpen_integralAdeles`, `continuous_toMatrix`, `toMatrix_det_ne_zero`), `04_UpiElement.lean` (`iotaV`, `etaAdelic`), `LWX/23_QuaternionData.lean` (the norm class as an interface), FLT `Finiteness.lean` (`D_discrete`, `units_cocompact`) | no direct `sorry` | audit required | present; the reduced norm on `D_f^×` and its norm class are new as theorems |
| §0.3 class sets | FLT `finiteDoubleCoset` via `QMF/04_Finiteness.lean` (`finite_classSet`), `04_Level.lean` (Hecke finiteness at compact open levels), `JacobsSlash/U3/2_Level.lean` (`U0`, `U1_9`), `2_LevelTopology.lean`, `3_ClassSet.lean` (Theorem 2.1, Lemma 2.2), `CN1/{3_LocalApprox, 3_AdeleIntegrality, 4_Dictionary}.lean` (class number one) | no direct `sorry` | audit required | present for the example; the standard levels `U₀(𝔫)`, `U₁(𝔫)` and the structure of `Γ_λ` for `F ≠ ℚ` are new |
| §0.4 local structure, wild-level monoids | `QMF/00_Sigma0.lean`, `Slash/01_Sigma0.lean` (`Sigma0'`, `adj`, `eta`), `Weight/04_AdicLevel.lean`, `QMF/04_UpiElement.lean`, `JacobsSlash/U3/3_EtaDecomposition.lean`, `LWX/23_QuaternionData.lean` (the coset decomposition from the Iwahori decomposition, `det = p`) | no direct `sorry` | audit required | present; the bridge to Mathlib's `HeckeRing` is new |
| §0.5 the running example | `JacobsSlash/U3/{1_Hurwitz, 1_Setting, 2_Level, 3_ClassSet, 3_EtaDecomposition, 5_Factorisations}.lean`, `CN1/` | no direct `sorry` | audit required | present |
| §1.1 level monoids | `Weight/00_Series.lean` (`SigmaNorm`, `LevelBounds`), `Weight/04_AdicLevel.lean` (`SigmaOne`, the valuation dictionary), `Slash/01_Sigma0.lean` (the adjugate) | no direct `sorry` | audit required | present |
| §1.2 the weight action | `Weight/00_Series.lean` (`WeightSeries`, `genFun`, `mobius`, `linX`, `numX`), `Weight/03_SlashAction.lean` (`kappaSlash`, `autFactor`, `mobius_mul`, `kappaSlash_one`, `kappaSlash_mul`, `norm_matrixCoeff_kappaSlash_le`, `isCompactoid_kappaSlash_of_norm_det_le`, `twist`), `Weight/04_Char.lean` (`ExpansionData`, `AnalyticWeight`, `col_eq_of_mem`, `evalAt`, `eq_zero_of_forall_evalAt_eq_zero`, `evalAt_compAn`, `toWeightSeries`), `TateFredholm/00_Compose.lean`, `06_WeightGenFun.lean` | no direct `sorry` | audit required | present in one variable with Jacobs's normalisation; the several-variable identity theorem, Buzzard's normalisation and §1.2.7(b) are new; §1.2.7(a) is `LWX/{06_HaloWeight, 08_HaloWeightH}.lean` at halo points |
| §1.3 algebraic and classical weights | `QMF/01_WeightModule.lean`, `Slash/03_WeightModule.lean`, `Weight/06_Algebraic.lean` (`algWeight`, `polyEmbed`, `polyEmbed_slash`, `detTwist`), `LWX/15_SymPow.lean` (`symAct`), `LWX/15_ClassicalPoint.lean` (classical shapes) | no direct `sorry` | audit required | present; the nebentypus loading as a weight is new |
| §1.4 several places | — | — | — | new |
| §2.1–2.2 automorphic functions, the decomposition | `QMF/01_AutomorphicFunction.lean`, `02_Decomposition.lean`, `Slash/03_AutomorphicFunction.lean`, `Slash/04_HeckeMatrix.lean` (`stabilizerAtSlash`, `evalAtRepsSlash`, `bijective_evalAtRepsSlash`) | no direct `sorry` | audit required | present |
| §2.3 the spaces | `Weight/05_Forms.lean` (`Forms`, `levelMonoidOf`, `kappaLevelSlashAction`), `Weight/07_Quaternionic.lean` (`FormsQ`), `QMF/03_Quaternionic.lean` (`Space`), `05_FiniteDimensional.lean`, `LWX/10_DiscForms.lean` (the disc model), `LWX/12_QuaternionicH.lean` | no direct `sorry` | audit required | present; the level–radius trade is new |
| §2.4 classical forms are overconvergent | `Weight/06_Algebraic.lean` (`classicalForms`, `map_classicalForms_le_forms`, `mem_map_classicalForms_iff`, `heckeOperator_mapCoeff_polyEmbed`) | no direct `sorry` | audit required | present; the nebentypus loading is new |
| §2.5 neat levels | `Weight/06_Compact.lean` (`evalAtReps`, `evalAtReps_injective`, `bijective_evalAtReps`, `formsModelEquiv`), `Weight/07_Fredholm.lean` (`transitionOp`) | no direct `sorry` | audit required | present |
| §2.6 property (Pr) | `Weight/08_Pr.lean` (`stabAvg`, `stabProj`, `mem_range_evalAtReps_iff`) | no direct `sorry` | audit required | present for finite stabilisers; the finite-quotient argument for `F ≠ ℚ` is new |
| §3.1 double-coset operators | `QMF/00_HeckeMonoid.lean`, `Slash/03_HeckeMonoid.lean`, `Weight/05_Forms.lean` (`heckeOperator`), `Weight/08_HeckeAlgebra.lean` (`heckeOperatorSlash_comm_of_reps`) | no direct `sorry` | audit required | present; the action of `HeckeRing` is new |
| §3.2 the matrix recipe | `QMF/03_HeckeMatrix.lean`, `Slash/04_HeckeMatrix.lean` (`heckeOperatorSlash_apply_rep`), `Weight/06_Compact.lean` (`heckeBlock`, `heckeBlockOp`, `heckeOperator_apply_rep`, `evalAtReps_heckeOperator`) | no direct `sorry` | audit required | present |
| §3.3 the standard operators | `QMF/04_UpiElement.lean` (`heckeUpi`), `Weight/07_Quaternionic.lean` (`heckeUpiQ`), `JacobsSlash/U3/7_DiamondHecke.lean` (the diamond operator `W`), `LWX/23_QuaternionData.lean` | no direct `sorry` | audit required | present for `U_𝔭` and the example; `T_𝔮`, `S_𝔮` and the commutativity theorem are new (commutativity is a hypothesis in the source) |
| §3.4–3.5 radius improvement, compactness | `Weight/06_Compact.lean` (`norm_det_toMatrix_certificate_le`, `isCompactoid_heckeBlock`, `isCompactoid_heckeBlockOp`), `Weight/07_Quaternionic.lean` (`isCompactoid_heckeBlockOp_etaAdelic'`) | no direct `sorry` | audit required | present by the row-decay route; Buzzard's factorisation §3.4.1 is new |
| §4.1 the determinant | `Weight/07_Fredholm.lean` (`heckeCharPowerSeries`, `evalT_heckeCharPowerSeries_eq_zero_iff`, `heckeCharPowerSeries_eq_of_reps`), `Weight/08_Pr.lean` (`heckeCharPowerSeriesPr`, `heckeCharPowerSeriesPr_eq_of_proj`, `heckeCharPowerSeriesPr_one`, `evalT_heckeCharPowerSeriesPr_eq_zero_iff`), `JacobsSlash/U3/{7_Fredholm, 8_HeckeSlopes}.lean` | no direct `sorry` | audit required | present |
| §4.2 Riesz theory on the forms | `Weight/07_Fredholm.lean` (`exists_riesz_decomposition_forms`) | no direct `sorry` | audit required | present for discretely valued `K`; the slope subspaces are new |
| §4.3 the Hecke algebra | `Weight/08_HeckeAlgebra.lean` (`mapsTo_ker_of_commute`, `exists_common_eigenvector`, `exists_eigensystem_of_riesz`) | no direct `sorry` | audit required | present |
| §4.4 the slope bound | `Weight/08_Slopes.lean` (`norm_matrixCoeff_heckeBlockOp_le`, `norm_charCoeff_heckeCharPowerSeries_le`, `blockSlopes`, `isBelow_newtonPolygon_heckeCharPowerSeries`) | no direct `sorry` | audit required | present; the dimension corollary is new |
| §4.5 base change | `Weight/08_BaseChange.lean` (`matrixCoeff_kappaSlash_map`, `matrixCoeff_heckeBlockOp_map`, `heckeCharPowerSeries_map`), `JacobsSlash/3_BaseChange.lean`, `JacobsSlash/U3/10_Eigenforms.lean` | no direct `sorry` | audit required | present in the form of a supplied second weight; the base change of the weight itself follows from the domain `𝒪^×` |
| §4.6 families | `LWX/{04_IntegralModel, 05_Certificates, 05_Specialize, 06_HaloWeight, 07_Seam, 11_SeamH}.lean` (the halo family and Proposition 2.17) | no direct `sorry` | audit required | the general theory over a Banach–Tate ring is new; the halo instance exists and is the spectral-halo roadmap's |
| §5.1 the theta operator | `LWX/11_Theta.lean` (`thetaOne`, `thetaDisc`, `thetaDisc_apply`, `thetaDisc_eq_zero_iff`, `IsLocPolyDeg`, `finrank_locPolyDegSubmodule`) | no direct `sorry` | audit required | present on the disc model; the normalising character on forms is new |
| §5.2 Bol's identity, equivariance | `LWX/12_Bol.lean` (`bol`, `coeff_iterate_derivative`, `thetaOne_comp_kappaSlash_of_autFactor`, `thetaDisc_comp_discSlash_of_autFactor`, `thetaDisc_comp_discHeckeBlock_of_autFactor`), `LWX/13_AtkinLehnerInst.lean` (`thetaBlock_comp_discHeckeBlockOp_of_autFactor`) | no direct `sorry` | audit required | present on the block model with the automorphy-factor hypotheses; the counterexample is recorded in the source's board files |
| §5.3 the classical subspace, the determinant identity | `LWX/12_StepOne.lean` (the classical subspace of the block model and its dimension), `LWX/16_ThetaExact.lean` (`thetaBlock_eq_diagBlock_comp_shiftBlock`, `isThetaExact_of_isClassicalShape`, `isThetaExact_classicalData`) | no direct `sorry` | audit required | present on the block model at Liu–Wan–Xiao's setting; restate for the spaces |
| §5.4 classicality | `LWX/12_StepOne.lean` (`eq_zero_of_intertwine_of_norm_lt`, `classical_of_slope_lt`) | no direct `sorry` | audit required | present for eigenforms; the generalised form is new |

⚠ **Do not treat the existing file layout as prescriptive.** The source development is organised
around the two applications it was written for, in the order they were needed: a left-handed core
with a right-handed dialect layered on it and seam theorems between them (the roadmap is
right-handed throughout), Jacobs's normalisation of the weight with Buzzard's `v` as a separate
twist, a weight domain that is a subgroup of `K^×` rather than `𝒪_𝔭^×`, one variable at one place,
commutativity of the Hecke operators as a hypothesis, the theta operator on the disc model of the
spectral-halo setting, and the determinant identity of §5.3.2 stated for Liu–Wan–Xiao's certificate
data. The migration is expected to restate the theory at the generality and in the organisation
specified above — Buzzard's normalisation, characters of `𝒪_𝔭^×`, the several variables of §1.4, the
standard operators and their commutativity as theorems, the theta operator on the forms — not to
port the layout.
