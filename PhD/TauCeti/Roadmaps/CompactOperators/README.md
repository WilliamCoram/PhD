# Roadmap: compact operators and Fredholm determinants

This roadmap develops the spectral theory of compact operators on nonarchimedean Banach modules:
finite-rank, completely continuous and compactoid operators; the Fredholm determinant `det(1 − Tu)`
of a compact operator as an entire power series, with its invariances, its multiplicativity and its
behaviour under base change; the ring of entire series with its Euclidean division; the Fredholm
resolvent and Serre's invertibility criterion; Riesz theory — the decomposition of the module at a
zero of the determinant and, over a ring, at a coprime factorisation of it — and the reading of the
Newton polygon of `det(1 − Tu)`: its slopes are the valuations of the eigenvalues of `u`, its
slope-`≤ h` part cuts out a finite projective direct summand, and it lies on or above the polygon
that the rows of the matrix of `u` prescribe. Three results are the headline milestones.

```text
det(1 − Tu) is entire, and 1 − a·u is invertible iff det(1 − Tu)(a) is a unit; over a field the
zeros of det(1 − Tu) are the reciprocals of the nonzero eigenvalues of u, the order of a zero being
the algebraic multiplicity of the eigenvalue                                              [Serre]
det(1 − Tu) = Q·S with Q, S coprime  ⇒  M = ker Q*(u) ⊕ N with ker Q*(u) projective of rank deg Q,
both summands u-stable, det(1 − Tu | ker Q*(u)) = Q and det(1 − Tu | N) = S, over any Banach–Tate
ring and with no Noetherian hypothesis                         [Coleman, Buzzard, Johansson–Newton]
the slopes of det(1 − Tu) are the valuations of the eigenvalues of u with multiplicity, and the
Newton polygon of det(1 − Tu) lies on or above the polygon of the row norms of the matrix of u,
with equality when the rescaled leading minors are units                          [Serre; Jacobs]
```

The setting is that of the `p`-adic-functional-analysis roadmap: a Banach–Tate ring `R` — a complete
nonarchimedean normed ring with a multiplicative unit of norm less than `1` — its Banach modules,
and the model space `c₀(I, R)` with its orthonormal bases. Nothing here assumes a ground field, and
nothing assumes that `R` is Noetherian: the determinant theory is organised around the *compactoid*
operators, those whose matrix has rows tending to zero, for which every statement is proved by
coordinate truncation and a quantitative continuity bound, and the equivalence of "compactoid" with
"limit of finite-rank operators" is a theorem with hypotheses rather than a standing assumption. The
reason for the generality is the same as in that roadmap: the coefficient ring of a family of
`p`-adic automorphic forms is `Λ^{>1/p}[1/T]` or an affinoid algebra, and the field case — Serre's
original theory — is recovered along the bridge lemma of its §0.4, not assumed. The last layer is
where the theory becomes arithmetic: the Newton polygon of `det(1 − Tu)`, read through the
Newton-polygons roadmap, turns the analytic statements into statements about slopes, which is what
the overconvergent-forms and spectral-halo roadmaps consume.

## Scope

The roadmap includes the following material.

- Finite-rank operators, completely continuous operators (operator-norm limits of finite-rank
  operators) and compactoid operators on the model space (matrices whose rows tend to zero): the
  two-sided ideal properties, closure under limits, the truncation criterion, transport along
  reindexings and continuous linear equivalences, restriction to coordinate subspaces, block
  operators on `c₀(σ × I, R)`, diagonal operators, operators presented by two-variable power series
  and by a restriction of radius, the identity criterion for finitely generated modules, and the
  comparison with Mathlib's `IsCompactOperator` and with compactoid sets.
- The Fredholm determinant `det(1 − Tu)` of a compactoid operator: the principal minors and the
  coefficient formula, the ultrametric Hadamard bound, entirety, the Lipschitz continuity of the
  coefficients, agreement with the reversed characteristic polynomial in the finite case, the trace
  property `det(1 − Tuv) = det(1 − Tvu)` and the invariances it yields (conjugation, reindexing,
  diagonal intertwining, transposition, extension by zero), the determinant on orthonormalisable
  modules and on modules with property (Pr), Serre's partition lemma and the block-diagonal and
  finite-factor factorisations, and base change along bounded homomorphisms, bicontinuous
  isomorphisms and specialisations.
- The ring `R{{T}}` of entire power series: evaluation at every point of a Banach algebra, the Hasse
  derivatives, Euclidean division by a polynomial with unit leading coefficient, relative primality,
  good zeros; the Fredholm resolvent; Serre's criterion `1 − a·u` invertible iff `det(1 − Tu)(a)` is
  a unit; the value `det(1 − u)` and its multiplicativity; the nonzero spectrum of a compact
  operator over a field.
- Riesz theory: the projector at a good zero, in the closure of `R[u]`; Serre's decomposition at a
  zero over a field, with the eigenvector theorem and the dimension formula; Coleman's resultant
  `D(B, P)` and the spectral mapping formula `det(1 − T·B(u)) = D(B, det(1 − Tu))`; the
  Riesz–Coleman decomposition for a coprime factorisation `det(1 − Tu) = Q·S` over a Banach–Tate
  ring, with the rank, the determinant identities and the uniqueness of the complement; commuting
  operators and eigensystems.
- Slopes: the Newton polygon of `det(1 − Tu)` and its unbounded slopes; slopes as valuations of
  eigenvalues with multiplicity; the slope factorisation of the determinant and the slope-`≤ h`
  decomposition of the module over a field, and the dominant-index factorisation with the
  slope-`≤ h` decomposition over a Banach–Tate ring; the Hadamard (Hodge) bound on the polygon by
  the row norms, its row-weight, block-weight and two-sided-weight forms, and the exact case of unit
  rescaled minors; finite factors and initial segments of the polygon.

The roadmap does not include the following.

- ⚠ **Banach modules, the operator norm, the model space and its orthonormal bases, the matrix of a
  bounded operator and the coordinate truncations.** These are Layers 0–2 of the
  `p`-adic-functional-analysis roadmap, which stops at the matrix of a bounded operator (its §2.6)
  and at the pointwise convergence of truncations (its §2.6.3); this roadmap starts at the first
  compactness-flavoured notion, the uniform decay of the rows of that matrix, and characterises the
  operators for which the truncations converge in operator norm (§0.2). Serre's theorem on
  orthonormalisability, property (Pr) as a lifting property, and the unitriangular-perturbation
  criterion are that roadmap's (its §§2.2–2.3, 2.7) and are consumed here.
- ⚠ **Newton polygons, Weierstrass factorisation at a vertex, and zeros of power series.** These are
  the Newton-polygons roadmap; Layer 4 reads the polygon of `det(1 − Tu)` through it and proves
  nothing about polygons.
- ⚠ **Restricted power series as rings, Tate rings in Huber's sense, and Weierstrass division.**
  These are the adic-spaces roadmap (Layer 0 and §0.5); §2.2 consumes Weierstrass division at a
  radius by a series whose dominant coefficient is a multiplicative unit, in the form the
  Newton-polygons roadmap's §3.1 records for a field and the adic-spaces roadmap's §0.5 for a Banach
  ring.
- Spectral varieties and the eigenvariety machine: the zero locus of `det(1 − Tu)` over an affinoid
  or adic weight space, its local pieces cut out by slope-`≤ h` decompositions, and the eigenvariety
  glued from them (Buzzard §§4–5, Johansson–Newton §2.3, Coleman–Mazur). This needs the rigid or
  adic geometry of the adic-spaces roadmap, and so does the pointwise (Gelfand-spectrum) form of the
  slope conditions; the norm-level form is here (§4.3).
- Hecke operators, their compactness on spaces of overconvergent automorphic forms, and the Fredholm
  determinant over weight space, which are the overconvergent-forms roadmap; the halo estimate on
  the coefficients of `det(1 − T·U_p)` over `Λ^{>1/p}` and its spectral consequences, which are the
  spectral-halo roadmap. Both consume this roadmap and nothing here mentions a modular form.
- Archimedean spectral theory and archimedean Fredholm determinants: Mathlib's `IsCompactOperator`
  and its Fredholm alternative over `ℝ` and `ℂ`, trace-class and nuclear operators, and
  Grothendieck's Fredholm determinants. §0.5 relates the vocabularies and proves nothing
  archimedean.
- Dwork operators, the rationality of zeta functions, and Wan's theory of nuclear operators over
  `p`-adic rings; locally convex, Fréchet and nuclear spaces and compactoid sets beyond Banach
  spaces.

Layers 0 and 1 belong under `TauCeti/Analysis/Normed/Operator/Ultra/Compact/` and
`TauCeti/Analysis/Normed/Operator/Ultra/Fredholm/`, next to Mathlib's `Analysis/Normed/Operator/`
directory and to the `p`-adic-functional-analysis roadmap's operator files; the finite-dimensional
preliminaries of §1.1 under `TauCeti/LinearAlgebra/Matrix/Charpoly/`, mirroring Mathlib; the entire
series of Layer 2 under `TauCeti/RingTheory/PowerSeries/Entire/`, next to Mathlib's
`RingTheory/PowerSeries/Restricted.lean`; the resolvent and Riesz theory of Layers 2–3 under
`TauCeti/Analysis/Normed/Operator/Ultra/Fredholm/Riesz/`; and Layer 4 under
`TauCeti/NumberTheory/NewtonPolygon/Fredholm/`, next to the Newton-polygons roadmap.

## Conventions and coordination with Mathlib

The following Mathlib material is relevant to this roadmap.

- `Mathlib/Analysis/Normed/Operator/Compact/Basic.lean` defines `IsCompactOperator` — a linear map
  is compact when some neighbourhood of `0` has relatively compact image — over a topological vector
  space, with `isCompactOperator_iff_isCompact_closure_image_ball`, the ideal properties
  `IsCompactOperator.comp_clm` and `.clm_comp`, `isCompactOperator_of_tendsto` and the closedness
  `isClosed_setOfPred_isCompactOperator`; `Compact/FiniteDimension.lean` proves
  `isCompactOperator_id_iff_finiteDimensional`. ⚠ This is the wrong notion over a nonarchimedean
  field that is not locally compact (convention 2), and §0.5 proves exactly when it agrees with the
  notions used here.
- `Mathlib/Analysis/Normed/Operator/Compact/FredholmAlternative.lean` proves, over any
  `NontriviallyNormedField`, that for a compact operator every nonzero point of the spectrum is an
  eigenvalue (`IsCompactOperator.hasEigenvalue_iff_mem_spectrum`), by an antilipschitz argument in
  shells. §0.5 records that it applies to the operators of this roadmap over a locally compact
  field, and §§2.5, 3.2 recover and refine it over every complete nonarchimedean field.
- `Matrix.charpolyRev M = det(1 − X·M)`, with `Matrix.reverse_charpoly` and
  `Matrix.isUnit_charpolyRev_of_isNilpotent` (`Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean`),
  whose docstring already names the infinite-dimensional object of this roadmap; the Sylvester
  identity `Matrix.det_one_sub_mul_comm`; `Matrix.trace_eq_neg_charpoly_coeff`; the universal
  characteristic polynomial `Matrix.charpoly.univ`.
- `Polynomial.resultant` (`Mathlib/RingTheory/Polynomial/Resultant/Basic.lean`) with
  `resultant_eq_prod_roots_sub`, `isUnit_resultant_iff_isCoprime`, `resultant_mul_left` and
  `resultant_map_map`; `Polynomial.reverse` and `Polynomial.reflect`. §3.3 builds Coleman's
  `D(B, P)` on `Polynomial.resultant` and nowhere else.
- `PowerSeries.IsRestricted c f` (`Mathlib/RingTheory/PowerSeries/Restricted.lean`), the predicate
  "restricted at radius `c`", on which the entire series of Layer 2 are built; `PowerSeries.rescale`
  and `PowerSeries.trunc`. ⚠ `PowerSeries.eval₂` and `PowerSeries.aeval`
  (`Mathlib/RingTheory/PowerSeries/Evaluation.lean`) evaluate power series at topologically
  nilpotent elements of a *linearly topologised* complete ring; a normed ring such as `ℚ_p` has no
  basis of ideals at `0`, so they do not apply here, and evaluation is the sum of the
  `p`-adic-functional-analysis roadmap's §4.1.3 (convention 6).
- `spectrum`, `spectrum.subset_closedBall_norm`, `spectrum.isClosed`; `Module.End.HasEigenvalue`,
  `Module.End.maxGenEigenspace`, `Module.End.IsSemisimple` and `LinearMap.charpoly_prodMap`;
  `Submodule.IsTopCompl` (topological complements,
  `Mathlib/Topology/Algebra/Module/Complement.lean`); `Module.Finite`, `Module.Projective`,
  `Module.rankAtStalk`; `IsIdempotentElem`.
- `TauCeti.Huber.isUnit_one_sub_of_isTopologicallyNilpotent_entries` (Tau Ceti, adic-spaces roadmap
  Layer 0), used by the `p`-adic-functional-analysis roadmap's §2.6.5, on which §0.2.9 stands.
- mathlib4#43578 and mathlib4#43580 (`WithZero.negLog`, `Valuation.addVal`) are the additive
  valuations through which the Newton-polygons roadmap, and hence Layer 4, read slopes.

The Tau Ceti API should agree with the final Mathlib API. ⚠ **None of these is a blocker, and
nothing in this roadmap waits on Mathlib.** At the pinned Mathlib there is no nonarchimedean
compact-operator theory, no Fredholm determinant, no entire power series, and no Riesz theory beyond
the archimedean-flavoured Fredholm alternative above.

These conventions are binding. Several of them are corrections to the obvious first design, and the
reasons are given because an implementor who does not know them will reintroduce the problem.

1. **Three notions of compactness, and the one that organises the theory.** `IsFiniteRank u` is "the
   range of `u` lies in a finitely generated submodule"; `IsCompletelyContinuous u` is "`u` is an
   operator-norm limit of finite-rank operators" (Serre's *complètement continu*, Buzzard's and
   Bellaïche's *compact*), a predicate on `M →L[R] N` for any Banach modules; `IsCompactoid u`, for
   `u` between model spaces, is "the row suprema of the matrix of `u` tend to `0` cofinitely". Every
   theorem about the determinant takes `IsCompactoid` as its hypothesis, and
   `IsCompletelyContinuous` enters only through the two bridges of §0.2: compactoid implies
   completely continuous unconditionally, and the converse holds when finitely generated submodules
   of `c₀(I, R)` are closed — over a Noetherian `R`, and over every field.

   The reason is that the converse is false in general and the determinant theory never needs it.
   Bellaïche's truncation lemma (`p`-adic-functional-analysis roadmap §2.6.4) requires closedness,
   which over a non-Noetherian Banach–Tate ring can fail for a finitely generated submodule; Buzzard
   and Johansson–Newton assume `R` Noetherian throughout for this reason alone. Organising the
   theory around row decay removes the hypothesis from every statement about `det(1 − Tu)`, its
   invariances, the resolvent and the Riesz decomposition: no Noetherian hypothesis appears in this
   roadmap.

2. **Mathlib's `IsCompactOperator` is not the notion.** A linear map has Mathlib's property when the
   image of a neighbourhood of `0` is relatively compact. Over a nonarchimedean field that is not
   locally compact this fails for the identity of a one-dimensional space — the unit ball of `ℂ_p`
   is not compact — so no finite-rank operator on a `ℂ_p`-Banach space is `IsCompactOperator`, and
   the notion is useless there; over a locally compact field the two notions agree (§0.5). No
   statement of this roadmap takes `IsCompactOperator` as a hypothesis; the comparison is confined
   to §0.5, where it is a theorem.

3. **Row decay is read on the matrix of the `p`-adic-functional-analysis roadmap, rows being
   coordinates.** `matrixCoeff u i j` is the `i`-th coordinate of `u (single j 1)` (that roadmap's
   convention 7), `rowNorm u i := ⨆ j, ‖matrixCoeff u i j‖`, and compactoid means `rowNorm u i → 0`
   cofinitely in `i`. ⚠ `rowNorm` is a real supremum, and over a normed ring that is not Tate a row
   can be unbounded, in which case the supremum is the junk value `0` and "compactoid" is vacuous
   while a compression of the operator is not; the Banach–Tate hypothesis is therefore standing
   wherever `rowNorm` appears, and over a Tate ring every row is bounded by `‖u‖`.

4. **The determinant is defined by principal minors, and the limit of finite determinants is a
   theorem.** `charCoeff u n := (−1)ⁿ ∑_{|S| = n} det (matrixCoeff u |_{S × S})`, the sum over the
   finite subsets `S` of the index set, and `charPowerSeries u := ∑ₙ charCoeff u n · Tⁿ` — Serre's
   formula. The definition is norm-free and makes sense as a formal sum for any operator; the
   theorems assume `IsCompactoid`, which is what makes the sums converge. The convergence
   `charPowerSeries (π_S ∘ u) → charPowerSeries u` along the finite subsets `S` is then a theorem
   (§1.3.3), not the definition.

   The reason is that every invariance statement becomes a termwise identity of minors: reindexing
   permutes the minors, transposition and diagonal intertwining leave each minor unchanged, and
   Serre's partition lemma is the factorisation of the minors of a block-triangular matrix. A
   definition as a limit would have to carry a compactness hypothesis into each of these and would
   need the Lipschitz bound before the first identity could be stated. The name follows Mathlib's
   `charpolyRev`, whose docstring calls the infinite-dimensional extension the *characteristic power
   series*; Serre's `det(1 − u)`, the value at `T = 1`, is `fredholmDet u`.

5. **The trace property is the primitive invariance.**
   `charPowerSeries (u ∘ v) = charPowerSeries (v ∘ u)` for `u` compactoid and `v` bounded is proved
   first, by truncation, the quantitative Lipschitz bound
   `‖cₙ(u) − cₙ(v)‖ ≤ max(‖u‖, ‖v‖)^{n−1} ‖u − v‖` and the finite Sylvester identity; invariance
   under conjugation by a continuous linear equivalence, independence of the orthonormal basis, and
   the extension of the determinant to modules with property (Pr) are formal corollaries. This is
   Bellaïche's architecture rather than Buzzard's basis-change computation, and the reason is
   Johansson–Newton's Proposition 2.1.8: the ring isomorphisms under which the determinant must be
   invariant are bicontinuous but not bounded, and only the quantitative route reaches them.

6. **Entire series are a predicate on Mathlib's `PowerSeries`, evaluated by summation.**
   `PowerSeries.IsEntire f := ∀ c > 0, PowerSeries.IsRestricted c f`, the subring `R{{T}}` is
   `PowerSeries.entireSubring`, and no new type is introduced. Evaluation of an entire series at a
   point `x` of a Banach `R`-algebra is `evalAt x f := ∑' n, coeff n f * x ^ n`, the sum of the
   `p`-adic-functional-analysis roadmap's §4.1.3 taken at the radius `‖x‖`; the Hasse derivatives
   `Δᵏ f := ∑ₙ (n + k choose k) · coeff (n + k) f · Tⁿ` are defined, since Mathlib has them for
   polynomials only; Euclidean division by a polynomial with unit leading coefficient is obtained
   from Weierstrass division at a radius at which the polynomial is dominant, not proved afresh. ⚠
   Mathlib's `PowerSeries.eval₂` is not the evaluation of this roadmap (it needs a linear topology),
   and `PowerSeries.derivative` is `Δ¹`, not `Δᵏ`.

7. **Riesz theory produces projectors in the closure of `R[u]`, at the ring level.** The
   decomposition theorems are stated as the existence of an idempotent `p` and a witness `w`, both
   operator-norm limits of polynomials in `u`, with `Q*(u) · w = p` and `Q*(u) · (1 − p) = 0`; the
   submodule statements (`M = ker Q*(u) ⊕ range p`, both `u`-stable, the rank of the kernel, the
   determinant identities) are derived. They are proved over a Banach–Tate ring with no Noetherian
   hypothesis, and the field statements — Serre's Proposition 12 — are their specialisation along
   the bridge lemma, with the finite-dimensional summand handled by the equivalence of all norms on
   a finite-dimensional space (`p`-adic-functional-analysis roadmap §1.3), not by a discreteness
   hypothesis on the valuation.

   The reason for the projector form is that every bounded operator commuting with `u` commutes with
   `p` and therefore preserves both summands; this is how the overconvergent-forms roadmap lets a
   Hecke algebra act on a finite-slope subspace, and it is the form of Johansson–Newton's Theorem
   2.2.2. The reason for dropping discreteness is that Serre's proof uses an orthogonal basis of the
   finite-dimensional summand only to compute its determinant, and the determinant is invariant
   under any continuous linear equivalence (convention 5).

8. **Slopes over a field are read through the Newton-polygons roadmap's additive valuation, and over
   a ring through the dominant index at a radius.** Over a nonarchimedean field `K` with an additive
   valuation `(v, e, b)` in the sense of that roadmap's Layer 1, the polygon of `charPowerSeries u`
   is that roadmap's §2.2 applied to the coefficients, so that for `K = ℚ_p` with `v p = 1` the
   slopes are rational numbers and Jacobs's "slopes `j + ½`" is an equality in `ℚ`. Over a
   Banach–Tate ring there is no polygon: the slope-`≤ h` factorisation is stated at the norm level,
   as the factorisation at a *dominant index* `N` at a radius `ρ` (Bellaïche's `N(F, ρ)`), and its
   pointwise form on the Gelfand spectrum is out of scope. The valuation `v_ϖ` of the
   `p`-adic-functional-analysis roadmap's §0.4.3 is the `ℚ`-valued instance of the Newton-polygons
   roadmap's Layer 1 normalised at `ϖ` when `ϖ` is a uniformiser, and that seam, recorded there, is
   the only way the two normalisations meet; nothing here defines a polygon through `v_ϖ`.

9. **Names.** `IsFiniteRank`, `IsCompletelyContinuous`, `IsCompactoid`, `rowNorm`, `minor`,
   `charCoeff`, `charPowerSeries`, `fredholmDet`; `PowerSeries.IsEntire`,
   `PowerSeries.entireSubring`, `PowerSeries.evalAt`, `PowerSeries.hasseDeriv`,
   `PowerSeries.IsEntireCoprime`, `PowerSeries.IsGoodZero`; `resolventCoeff`; `IsRieszProjection`
   and `exists_rieszProjection`, `exists_rieszDecomposition`; `PowerSeries.colemanD` for `D(B, F)`;
   `IsRieszColemanProjection` and `exists_rieszColemanProjection`; `PowerSeries.IsDominantIndex`,
   `Polynomial.IsDominant`, `PowerSeries.IsDominantFactorization`. The compact-operator notions live
   in the namespace of `ContinuousLinearMap`, the series notions in `PowerSeries`, and the
   finite-dimensional facts of §1.1 in `Matrix`; nothing from this roadmap is placed in the root
   namespace.

## Existing Mathlib used by the roadmap

- `IsCompactOperator` and the API listed above; `LocallyCompactSpace`, `ProperSpace`, and the
  `ProperSpace` instances of `ℚ_[p]` and of finite extensions; `TotallyBounded`.
- `ContinuousLinearMap`, `ContinuousLinearEquiv`, `LinearMap.range`, `LinearMap.ker`,
  `Submodule.FG`, `Submodule.span`, `Submodule.IsTopCompl`, `Submodule.projection`; `Module.Finite`,
  `Module.Projective`, `Module.Free`, `Module.finrank`, `Module.rankAtStalk`, `FiniteDimensional`;
  `IsIdempotentElem`; `Polynomial.aeval` on the endomorphism ring.
- `Matrix.det`, `Matrix.det_apply` (the Leibniz expansion), `Matrix.charpoly`, `Matrix.charpolyRev`,
  `Matrix.reverse_charpoly`, `Matrix.det_one_add_mul_comm`, `Matrix.det_one_sub_mul_comm`,
  `Matrix.trace_eq_neg_charpoly_coeff`, `Matrix.charpoly.univ`,
  `Matrix.isUnit_charpolyRev_of_isNilpotent`, `LinearMap.charpoly`, `LinearMap.charpoly_prodMap`,
  `Module.End.IsSemisimple`, `Module.End.IsSemisimple.iSup_eigenspace_eq_top`,
  `Module.End.isSemisimple_of_squarefree_aeval_eq_zero`.
- `Polynomial.resultant` with `resultant_eq_prod_roots_sub`, `isUnit_resultant_iff_isCoprime`,
  `resultant_mul_left`, `resultant_map_map`, `resultant_C_mul_left`; `Polynomial.reverse`,
  `Polynomial.reflect`, `Polynomial.coeff_zero_reverse`, `Polynomial.hasseDeriv`, `IsCoprime` in
  `R[X]`, `Polynomial.roots`, `Polynomial.Splits`.
- `PowerSeries.IsRestricted`, `PowerSeries.isRestricted_iff`, `PowerSeries.rescale`,
  `PowerSeries.trunc`, `PowerSeries.coeff_mul`, `PowerSeries.derivative`, the coercion
  `Polynomial R → PowerSeries R`, `PowerSeries.isUnit_iff_constantCoeff`; `MvPowerSeries` in two
  variables for §0.3.
- `spectrum`, `spectrum.mem_resolventSet_iff`, `spectrum.subset_closedBall_norm`,
  `spectrum.isClosed`, `ContinuousLinearMap.spectrum_eq`, `Module.End.HasEigenvalue`,
  `Module.End.eigenspace`, `Module.End.maxGenEigenspace`; `Units.oneSub` and the Neumann series;
  `IsUltrametricDist`, `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`,
  `Filter.cofinite`, `Filter.Tendsto`.
- From the `p`-adic-functional-analysis roadmap, already specified there and used on every page
  here: the ultrametric bound and the unique dominant term (§0.1.2–3), `PseudoUniformizer` and
  `NormedRing.IsTate` (§0.4), the scoped operator norm and `‖u x‖ ≤ ‖u‖ ‖x‖` (§1.1), the
  quantitative open mapping theorem and the Neumann inverse (§1.2), the equivalence of norms on
  finite-dimensional spaces (§1.3), the model space `C₀(I, R)` with `single`, `eval`, reindexing and
  blocks (§2.1), `IsONable`, `IsPotentiallyONable`, `HasPr` and the lifting property (§2.2),
  `matrixCoeff`, `truncation`, the approximation of closed finitely generated submodules and their
  closedness over Noetherian rings (§2.6), the unitriangular-perturbation criterion (§2.7), and the
  evaluation and substitution of restricted series (§4.1).
- From the Newton-polygons roadmap: the additive valuations `(v, e, b)` (Layer 1), the polygon of a
  power series and its slope data (§2.2, §0.4–0.5), Weierstrass division at a radius (§3.1), the
  factorisation at a vertex and the slope factorisation (§§3.3–3.4), root and zero counts (§§4.1,
  4.3), entire series and their zeros (§§4.4–4.5), and products and initial segments (§§5.1–5.3).
- From Tau Ceti: `TauCeti.Huber.isUnit_one_sub_of_isTopologicallyNilpotent_entries` (through the
  `p`-adic-functional-analysis roadmap's §2.6.5).

⚠ Mathlib has **no** notion of completely continuous or compactoid operator, **no** Fredholm
determinant in any generality, **no** ultrametric Hadamard bound on a determinant, **no**
principal-minors expansion of `det(1 − tA)`, **no** resultant formula
`Res(charpoly A, g) = det g(A)`, **no** entire power series, and **no** Riesz theory beyond the
Fredholm alternative. `LinearMap.charpoly` is defined for finite free modules only; the projective
case of §1.5.4 goes through a free complement.

---

## Layer 0: compact operators

`R` is a Banach–Tate ring in the sense of the `p`-adic-functional-analysis roadmap's §0.4 —
`[NormedCommRing R] [IsUltrametricDist R] [NormOneClass R] [CompleteSpace R] [NormedRing.IsTate R]`
— with a chosen `ϖ : PseudoUniformizer R` where the scaling trick is used; `M`, `N` are Banach
`R`-modules; `I`, `J` are discrete types and `c₀(I, R)` is the model space `C₀(I, R)` of that
roadmap's §2.1, with the operator norm of its §1.1 on `M →L[R] N`. Everything in this layer is about
the operators; nothing about determinants appears before Layer 1.

### 0.1 Finite-rank and completely continuous operators

1. Define `IsFiniteRank u` for `u : M →L[R] N`: the range of `u` is contained in a finitely
   generated submodule of `N`. Prove that finite-rank operators form a two-sided ideal: they are
   closed under sums and scalar multiples, and `f ∘ u` and `u ∘ f` have finite rank when `u` does
   and `f` is bounded. Over a field, `IsFiniteRank u` is "the range of `u` is finite-dimensional".
   The coordinate truncations `π_S ∘ u` of the `p`-adic-functional-analysis roadmap's §2.6.3 have
   finite rank, and so does every bounded operator out of a finite free module (its §1.2.5).
2. Define `IsCompletelyContinuous u`: for every `ε > 0` there is a finite-rank `v` with
   `‖u − v‖ < ε` (Serre, §2; Buzzard §2; Bellaïche, Definition II.1.3; Johansson–Newton, Definition
   2.1.5). Prove the two-sided ideal property `f ∘ u`, `u ∘ f` (Bellaïche, Lemma II.1.4), closure
   under sums and scalar multiples, and closure under operator-norm limits: a limit of completely
   continuous operators is completely continuous. ⚠ The Tate hypothesis is used through
   `‖u x‖ ≤ ‖u‖ ‖x‖` (that roadmap's §1.1.2) in every one of these; over a normed ring that is not
   Tate the operator norm does not control the operator and the ideal property fails.
3. **The identity criterion.** The identity of `M` is completely continuous if and only if `M` is
   finitely generated: if `‖1 − v‖ < 1` with `v` of finite rank, then `v` is invertible by the
   Neumann series (that roadmap's §1.1.5) and its range, which is `M`, is finitely generated. This
   is the nonarchimedean, ring-level form of Mathlib's `isCompactOperator_id_iff_finiteDimensional`,
   and it is the engine of the finiteness statements of §0.4 and §3.1.
4. A completely continuous operator into a finitely generated module has finite rank; the composite
   of two completely continuous operators is completely continuous; and for `M` a direct summand of
   `N` with projection `π` and inclusion `ι`, `u` on `M` is completely continuous if and only if
   `ι ∘ u ∘ π` on `N` is.

### 0.2 Compactoid operators on the model space

`u : c₀(J, R) →L[R] c₀(I, R)`, with matrix `matrixCoeff u i j` (convention 3).

1. Define `rowNorm u i := ⨆ j, ‖matrixCoeff u i j‖` and
   `IsCompactoid u := Tendsto (rowNorm u) cofinite (𝓝 0)`. Prove `rowNorm u i ≤ ‖u‖`, that `rowNorm`
   is `1`-Lipschitz in `u`, and that the family of row norms is a null family whose supremum is
   `‖u‖` (the `p`-adic-functional-analysis roadmap's §2.6.1).
2. **The truncation criterion.** `‖u − π_S ∘ u‖ = sup_{i ∉ S} rowNorm u i` for every finite `S ⊆ I`;
   hence `u` is compactoid if and only if `π_S ∘ u → u` in operator norm along the filter of finite
   subsets of `I` (Bellaïche, Scholium II.1.10, in both directions). This is the statement the
   `p`-adic-functional-analysis roadmap's §2.6.3 defers to here: the truncations converge pointwise
   for every bounded `u`, and in norm exactly for the compactoid ones.
3. Compactoid implies completely continuous, unconditionally (Bellaïche, Proposition II.1.9, the
   direction that needs no hypothesis): `π_S ∘ u` has finite rank and converges to `u`.
4. **The two-sided ideal property.** For `u` compactoid and `v` bounded, `u ∘ v` and `v ∘ u` are
   compactoid: `rowNorm (u ∘ v) i ≤ rowNorm u i · ‖v‖`, and for `v ∘ u` the row `i` of the product
   is `∑_j v_{ij} u_{jk}`, bounded by
   `max(‖v‖ · sup_{j ∉ S} rowNorm u j, max_{j ∈ S} ‖v_{ij}‖ · ‖u‖)` for any finite `S`, and the
   second term tends to `0` in `i` because the columns of `v` do. Compactoid operators are closed
   under sums, scalar multiples and operator-norm limits, and contain the finite-rank operators of
   the form `π_S ∘ u`.
5. **Transport.** Reindexing along `I ≃ I'` and `J ≃ J'` preserves `IsCompactoid`; conjugation by a
   continuous linear automorphism of `c₀(I, R)` preserves it (by clause 4); hence for a continuous
   linear equivalence `e : c₀(I, R) ≃L[R] c₀(I', R)`, `e ∘ u ∘ e⁻¹` is compactoid if and only if `u`
   is. Along a bicontinuous ring isomorphism `R ≃+* S` and along a bounded ring homomorphism
   `ψ : R → S` with `‖ψ r‖ ≤ C ‖r‖`, the operator with matrix `ψ (matrixCoeff u i j)` is compactoid
   when `u` is (Johansson–Newton, Proposition 2.1.8; Bellaïche, Lemma II.1.23).
6. **Restriction, compression and blocks.** For a decidable `P : I → Prop`, the compression of `u`
   to `c₀({i // P i}, R)` (the `P × P` corner of the matrix) is compactoid when `u` is, and so is
   the restriction of `u` to `c₀({i // P i}, R)` when `u` preserves it. For a finite `σ`, an
   operator on `c₀(σ × I, R)` assembled from a `σ × σ` matrix of operators `T a b` on `c₀(I, R)`
   (that roadmap's §2.1.4) is compactoid if and only if every block `T a b` is; state the block
   operator `blockOp T`, its matrix, its composition law
   `blockOp T ∘ blockOp T' = blockOp (T · T')`, the block-diagonal operators `blockDiag f`, and the
   block operators between different fibres `c₀(σ × I, R) → c₀(σ × I', R)` with their composition
   laws, which is how the overconvergent-forms roadmap moves an operator between the disc model and
   the Mahler model of that roadmap's §4.4.
7. **Diagonal and permutation operators.** `diag d` for a bounded family `d : I → R` is compactoid
   if and only if `d → 0` cofinitely; a permutation operator is compactoid if and only if `I` is
   finite; the identity of `c₀(I, R)` is compactoid if and only if `I` is finite, in agreement with
   §0.1.3.
8. **Row-decay criteria.** If `‖matrixCoeff u i j‖ ≤ C · σ ^ (w i)` for all `i, j`, with `0 ≤ σ < 1`
   and a weight `w : I → ℕ` tending to `+∞` cofinitely, then `u` is compactoid (Jacobs, Corollary
   1.10, for `I = ℕ` and `w = id`); state the weights `w (a, k) = k` on `I = ι × ℕ` and `w = id` on
   `ℕ`, which are the two the later roadmaps use.
9. **The converse, under closedness.** If every finitely generated submodule of `c₀(I, R)` is closed
   — in particular over a Noetherian `R` (that roadmap's §2.6.5) and over every field — then a
   completely continuous `u` is compactoid: approximate `u` by a finite-rank `v` with range in a
   closed finitely generated `P`, approximate `P` by a truncation (that roadmap's §2.6.4), and
   compare (Bellaïche, Proposition II.1.9; Buzzard, §2; Johansson–Newton, Definition 2.1.5). Hence
   `IsCompletelyContinuous u ↔ IsCompactoid u` over Noetherian Banach–Tate rings and over fields,
   which is Serre's Proposition 6 in the field case. ⚠ Do not state the equivalence without the
   closedness hypothesis, and do not let any theorem of Layers 1–4 depend on it.

### 0.3 Operators presented by two-variable series and by a restriction of radius

`K` is a complete nonarchimedean nontrivially normed field and `R` a Banach–Tate ring; the model
space is `c₀(ℕ, R)`, identified with the restricted series `R⟨z⟩` by the
`p`-adic-functional-analysis roadmap's §4.1.1, `zʲ ↦ single j 1`.

1. **Kernels.** A two-variable power series `F = ∑ a_{ij} xⁱ yʲ ∈ R⟦x, y⟧` with bounded coefficients
   and columns tending to `0` (`a_{ij} → 0` cofinitely in `i` for each `j`) presents the bounded
   operator `ofGenFun F : c₀(ℕ, R) → c₀(ℕ, R)` with `matrixCoeff (ofGenFun F) i j = a_{ij}`, i.e.
   `zʲ ↦ ∑ᵢ a_{ij} zⁱ` (Jacobs, §1.1). Prove that every bounded operator on `c₀(ℕ, R)` is of this
   form, that composition of operators is the convolution of kernels in the middle variable, that
   the diagonal rescalings `diag (αⁱ)` and `diag (βʲ)` act by `F (x, y) ↦ F (α x, β y)` (Jacobs,
   Proposition 1.3), and that row decay `‖a_{ij}‖ ≤ C ρ ^ i` makes the operator compactoid (§0.2.8).
2. **Substitution operators.** For `g` and `h` in `R⟨z⟩` with `‖g‖ ≤ 1`, `‖h‖ ≤ 1`, the operator
   `f ↦ g · (f ∘ h)` (the substitution of that roadmap's §4.1.4) is bounded of norm at most `1`,
   with kernel `∑ⱼ g(x) h(x)ʲ yʲ = g(x) / (1 − h(x) y)` and matrix `a_{ij} = coeff i (g · hʲ)`.
3. **The restriction-of-radius criterion.** Let `c > 1`. If a bounded operator `u` on `R⟨z⟩` factors
   as `ι ∘ u'` with `u' : R⟨z⟩ → R⟨z⟩_c` bounded into the series restricted at radius `c` (that
   roadmap's §4.1.2) and `ι` the inclusion, then in the monomial basis
   `‖matrixCoeff u i j‖ ≤ ‖u'‖ · c ^ (−i)`, so `u` is compactoid with geometric row decay. In
   particular `f ↦ g · (f ∘ h)` is compactoid whenever `g` and `h` are restricted at some radius
   `c > 1` with `‖h‖_c ≤ 1`, where `‖·‖_c` is the Gauss norm at `c`; and the inclusion
   `R⟨z⟩_c → R⟨z⟩` itself is compactoid. This is the mechanism of Buzzard's Lemma 12.2 and of
   Jacobs's Lemma 2.7 — an operator that "improves the radius" is compact — and it is the only
   compactness argument the overconvergent-forms roadmap needs.
4. **The inclusions of locally analytic functions.** The inclusion `LA_h → LA_{h+1}` of the
   `p`-adic-functional-analysis roadmap's §4.3.2 is compactoid in the disc models, and in the Amice
   bases it is the diagonal operator with entries `⌊n/pʰ⌋! / ⌊n/pʰ⁺¹⌋!` tending to `0` (its §4.4.4),
   compactoid by §0.2.7; and the evaluation `eval h : LA_h → C(ℤ_p, E)` in the Amice and Mahler
   bases is `diag (⌊n/pʰ⌋!)`, whose entries tend to `0` for every `h`, so it is compactoid as well.
   These are the compact inclusions that make the spaces of overconvergent forms of the
   overconvergent-forms roadmap behave like finite-dimensional spaces slope by slope.

### 0.4 Compact operators on orthonormalisable modules and on modules with property (Pr)

1. For `M` potentially orthonormalisable (that roadmap's §2.2.3) and `u : M →L[R] M`, define
   `IsCompactoid u` as: for some continuous linear equivalence `e : M ≃L[R] c₀(I, R)`, the operator
   `e ∘ u ∘ e⁻¹` is compactoid. Prove, by §0.2.5, that this holds for one `e` if and only if it
   holds for every `e`, so that the definition is intrinsic; and that
   `IsCompactoid u → IsCompletelyContinuous u`, with the converse under the closedness hypothesis of
   §0.2.9.
2. For `M` with property (Pr) — a direct summand of a potentially orthonormalisable `N` with
   inclusion `ι` and projection `π` — define `IsCompactoid u` as `IsCompactoid (ι ∘ u ∘ π)`, and
   prove it independent of the choice of `N`, `ι`, `π`: for two presentations, the two extended
   operators are conjugate to each other up to a finite-rank correction on the complement, and
   §0.2.4–5 apply.
3. The ideal properties, closure under limits, and transport of §0.2 hold in this generality, and
   for `M` finitely generated projective every bounded operator is compactoid.
4. **The finiteness germ.** If `M` is a complete Banach `R`-module, `u : M →L[R] M` is completely
   continuous and `1 − u` is nilpotent, then `M` is finitely generated: `1 = u · ∑_{k<n} (1 − u)ᵏ`
   makes the identity completely continuous, and §0.1.3 applies. If moreover `M` has property (Pr),
   then `M` is finitely generated projective (that roadmap's §2.2.4). This is Bellaïche's
   Proposition II.1.21 with its Noetherian hypothesis removed — his proof used only the Neumann
   inverse — and it is the finiteness input of the Riesz decomposition (§3.1).

### 0.5 The relation with Mathlib's compact operators and with compactoid sets

`K` is a complete nonarchimedean nontrivially normed field and `E`, `F` are `K`-Banach spaces.

1. **Compactoid sets.** A subset `A ⊆ F` is *compactoid* if for every `ε > 0` there is a finite set
   `S ⊆ F` with `A ⊆ B(0, ε) + aco S`, where `aco S = {∑_{s ∈ S} a_s s | ‖a_s‖ ≤ 1}` is the
   absolutely convex hull (Gruson; van Rooij; Perez-Garcia–Schikhof). Prove: compactoid sets are
   bounded, closed under finite unions, sums, closures, images under bounded operators and
   absolutely convex hulls of finite sets; every bounded subset of a finite-dimensional space is
   compactoid; and when `K` is locally compact, a subset of a Banach space is compactoid if and only
   if it is totally bounded, i.e. relatively compact.
2. **Projections onto finite-dimensional subspaces.** For every finite-dimensional subspace `D ⊆ E`
   and every `0 < t < 1` there is a projection `P : E →L[K] E` onto `D` with `‖P‖ ≤ t⁻¹` (a
   `t`-orthogonal complement; van Rooij, Chapter 3; Perez-Garcia–Schikhof, Chapter 2), by the
   inductive distance argument of the `p`-adic-functional-analysis roadmap's §2.4.1; over a
   discretely valued or spherically complete `K` one may take `‖P‖ ≤ 1`.
3. **Completely continuous means compactoid image.** `u : E →L[K] F` is completely continuous if and
   only if `u (B(0, 1))` is compactoid. The forward direction is clause 1 applied to a finite-rank
   approximant; the converse takes `S` from the compactoid condition, `D = span S`, `P` from clause
   2, and computes `‖u − P ∘ u‖ ≤ t⁻¹ ε` since `1 − P` has norm at most `t⁻¹` and kills `D`. This is
   the nonarchimedean approximation property: every nonarchimedean Banach space has it, in contrast
   with the archimedean case, and it is why Serre's definition by limits and Gruson's definition by
   compactoid images agree.
4. **The bridge to Mathlib.** If `K` is locally compact, then for `u : E →L[K] F` between Banach
   spaces `IsCompletelyContinuous u ↔ IsCompactOperator u`, by clauses 1 and 3 and Mathlib's
   `isCompactOperator_iff_isCompact_closure_image_ball`. ⚠ Neither direction survives without local
   compactness: the identity of `K = ℂ_p` has finite rank and is not `IsCompactOperator`. Record the
   consequence that Mathlib's Fredholm alternative
   (`IsCompactOperator.hasEigenvalue_iff_mem_spectrum`) applies to every completely continuous
   operator on a Banach space over a local field, and that §2.5 and §3.2 give the same conclusion
   over every complete nonarchimedean field, together with the finiteness of the multiplicities and
   the determinant, which the alternative does not.
5. Over a Banach–Tate ring there is no analogue of clause 4 and none is stated; `IsCompactoid` and
   `IsCompletelyContinuous` are the two notions, related by §0.2.

### Examples

The truncations `π_S` on `c₀(ℕ, ℚ_p)` and the diagonal operator `diag (pⁿ)`, compactoid with row
norms `p^{−n}`; the shift `(fₙ) ↦ (f_{n+1})`, bounded and not compactoid (the `p`-adic-functional-
analysis roadmap's acceptance example: its row suprema are all `1`), hence not completely continuous
since `ℚ_p` is a field; the identity of `c₀(ℕ, ℚ_p)`, not compact, and the identity of `ℚ_p ^ n`,
compact; the rank-one operator `x ↦ (∑ⱼ xⱼ) · (pⁱ)ᵢ` with matrix `a_{ij} = pⁱ`, compactoid; the
identity of `ℂ_p`, of finite rank and not `IsCompactOperator`; the substitution operator `f ↦ f(pz)`
on `ℚ_p⟨z⟩`, compactoid by §0.3.3 with `c = p`, and `f ↦ f(z + 1)`, bounded and not compactoid; a
block operator on `c₀(Fin 2 × ℕ, ℚ_p)` with one compactoid and one non-compactoid block, not
compactoid.

### Dependencies

The `p`-adic-functional-analysis roadmap, Layers 0–2 and §4.1 (all of it, as the floor); Mathlib's
`IsCompactOperator` for §0.5.

---

## Layer 1: the Fredholm determinant

`R` is a Banach–Tate ring, `I` a discrete type, and `u : c₀(I, R) →L[R] c₀(I, R)` with matrix
`a_{ij} = matrixCoeff u i j`. The finite-dimensional facts of §1.1 are stated over an arbitrary
commutative ring, as they are algebra and not analysis.

### 1.1 Finite-dimensional preliminaries: the reversed characteristic polynomial

`A` is a square matrix over a commutative ring `S`, indexed by a finite type `n`, and
`charpolyRev A = det (1 − X·A)` is Mathlib's.

1. **The principal-minors expansion.** `det (1 − X·A) = ∑_{S ⊆ n} (−X) ^ |S| · det (A_{S×S})`, the
   sum over all subsets `S` of the index type of the principal minors; equivalently the coefficient
   of `Xᵏ` in `charpolyRev A` is `(−1)ᵏ` times the sum of the `k × k` principal minors. ⚠ Not in
   Mathlib; it is the identity on which Serre's definition rests and a Mathlib PR candidate. Deduce
   `coeff 1 (charpolyRev A) = −trace A` (Mathlib's `trace_eq_neg_charpoly_coeff` reversed) and
   `natDegree (charpolyRev A) ≤ |n|`.
2. **Sylvester.** `charpolyRev (A * B) = charpolyRev (B * A)` for rectangular `A`, `B` of transposed
   shapes, from Mathlib's `det_one_sub_mul_comm`; `charpolyRev` commutes with ring homomorphisms,
   with conjugation by invertible matrices, and with transposition; and along a factorisation
   `E = P * Q`, `Q * P = 1` of an idempotent `E` with `A * E = E * A = A`,
   `charpolyRev A = charpolyRev (Q * A * P)`. Every idempotent matrix whose range is free admits
   such a factorisation, in particular over a field or a local ring.
3. **Nilpotent and unipotent matrices.** `charpolyRev N = 1` for `N` nilpotent over a reduced ring
   (Mathlib's `isUnit_charpolyRev_of_isNilpotent` gives a unit; the equality is the reduced case),
   and over a field, if `A = E − N` with `E` idempotent, `N` nilpotent and `A E = E A = A`, then
   `charpolyRev A = (1 − X) ^ rank E`. ⚠ Over a non-reduced ring `charpolyRev (1 − N)` need not be
   `(1 − X) ^ |n|`: rank statements in Layer 3 go through the residue fields and degree bounds
   through the localisations, and the two must not be conflated.
4. **The resultant of the characteristic polynomial.** `Res (charpoly A, g) = det (g (A))` for every
   polynomial `g`, over any commutative ring: over an algebraically closed field both sides are
   `∏ g(λ)` over the eigenvalues with multiplicity (Mathlib's `resultant_eq_prod_roots_sub`), and
   the general case is the polynomial identity in the universal matrix `Matrix.charpoly.univ`. ⚠ Not
   in Mathlib; a PR candidate, and the finite input of the spectral mapping formula (§3.3).
5. **Roots of `charpolyRev`.** Over a field, the roots of `charpolyRev A` are the inverses of the
   nonzero roots of `charpoly A` with the same multiplicities, and `charpolyRev A` has degree
   `rank`-many roots when `A` is invertible; if `A * B = c • 1` with `c ≠ 0`, the root multisets of
   `charpoly A` and `charpoly B` correspond under `x ↦ c / x`. These are the finite-dimensional
   facts behind the slope symmetries of the spectral-halo roadmap.
6. **The ultrametric Hadamard bound.** Over a nonarchimedean normed ring with `‖1‖ = 1`,
   `‖det A‖ ≤ ∏ᵢ rᵢ` whenever `‖A i j‖ ≤ rᵢ` for all `j`: each Leibniz monomial is bounded by the
   product, and the ultrametric inequality bounds the sum by the largest term. ⚠ Not in Mathlib.
   State the weighted form `‖det A‖ ≤ σ ^ (∑ᵢ w i)` for `‖A i j‖ ≤ σ ^ (w i)`, `0 ≤ σ ≤ 1`, and the
   two-sided form `‖det A‖ ≤ σ ^ (∑ᵢ w i − ∑ⱼ w' j)` for `‖A i j‖ ≤ σ ^ (w i − w' j)` (truncated
   subtraction, the permutation inequality `∑ᵢ (w i − w' (π i)) ≥ ∑ w − ∑ w'`).

### 1.2 Principal minors and the coefficients

1. Define `minor u S := det (fun i j : S ↦ matrixCoeff u i j)` for a finite `S ⊆ I`. Prove the
   Hadamard bound `‖minor u S‖ ≤ ∏_{i ∈ S} rowNorm u i` (§1.1.6), and that for `u` compactoid the
   family `S ↦ minor u S`, over the subsets of a fixed cardinality `n`, tends to `0` cofinitely: a
   minor of norm at least `ε` needs all its rows among the finitely many rows of norm at least
   `ε / max(‖u‖, 1) ^ (n−1)`. Hence it is summable (the `p`-adic-functional-analysis roadmap's
   §0.1.1).
2. Define `charCoeff u n := (−1) ^ n · ∑' S : {S // |S| = n}, minor u S` and
   `charPowerSeries u := PowerSeries.mk (charCoeff u)` (convention 4); `charCoeff u 0 = 1`, and
   `charCoeff u 1 = −∑' i, matrixCoeff u i i`, the trace, which converges for compactoid `u`. Record
   `charCoeff (a • u) n = a ^ n · charCoeff u n`, i.e.
   `charPowerSeries (a • u) = PowerSeries.rescale a (charPowerSeries u)`, and that
   `charPowerSeries 0 = 1`.
3. **Agreement with the finite case.** If the rows of `u` outside a finite `S` vanish
   (`u = π_S ∘ u`), then `charPowerSeries u = charpolyRev (matrixCoeff u |_{S×S})` by §1.1.1; in
   particular for `I` finite the Fredholm determinant is the reversed characteristic polynomial, and
   for a finite-rank `u` with range in the span of finitely many coordinate vectors it is a
   polynomial of degree at most their number.
4. **The Hadamard bound on the coefficients.** Let `r*` be the decreasing rearrangement of the row
   norms of a compactoid `u` — the null family `rowNorm u` takes each positive value finitely often,
   so `r*_0 ≥ r*_1 ≥ ⋯ → 0` is well defined. Then `‖charCoeff u n‖ ≤ ∏_{k < n} r*_k` (Serre, §5;
   Wan's *Hodge polygon* of a nuclear matrix), since `∏_{i ∈ S} rowNorm u i ≤ ∏_{k < |S|} r*_k` for
   every `S`.

### 1.3 Entirety and continuity

1. **Entirety.** For `u` compactoid, `charPowerSeries u` is restricted at every radius `C > 0`
   (Serre, §5; Bellaïche, Lemma II.1.14): `‖charCoeff u n‖ C ^ n ≤ ∏_{k<n} (C r*_k) → 0` since
   `C r*_k < 1/2` for all but finitely many `k`. So `charPowerSeries u ∈ R{{T}}` (§2.1).
2. **The Lipschitz bound.** For `u`, `v` compactoid and `n ≥ 1`,
   `‖charCoeff u n − charCoeff v n‖ ≤ max(‖u‖, ‖v‖) ^ (n − 1) · ‖u − v‖` (Bellaïche, Lemma II.1.15):
   expand each minor of `u` against the corresponding minor of `v` one row at a time. Hence
   `u ↦ charCoeff u n` is Lipschitz on bounded sets, and `u ↦ charPowerSeries u` is continuous
   coefficientwise for the operator norm.
3. **Truncation limits.** For `u` compactoid, `charPowerSeries (π_S ∘ u) → charPowerSeries u` along
   the finite subsets `S`, coefficientwise by clause 2 and §0.2.2, and in every Gauss norm `‖·‖_C`
   by clause 1, since `π_S ∘ u` and `u` have the same rows on `S` and the tails are uniformly
   bounded by `∏_{k<n} (C r*_k)`. This is the sense in which the determinant is a limit of finite
   determinants, and the tool by which every identity of Layers 1–3 is reduced to finite linear
   algebra: prove it for row-supported operators by §1.2.3 and §1.1, and pass to the limit.
4. **Limits of compactoid operators.** If `uₖ → u` in operator norm with every `uₖ` compactoid, then
   `u` is compactoid (§0.2.4) and `charPowerSeries uₖ → charPowerSeries u` coefficientwise, by
   clause 2; if moreover the row norms of the `uₖ` are dominated by a single null family, the
   convergence holds in every Gauss norm, by the argument of clause 3. State both forms: the first
   is what the Lipschitz bound gives and the second is what limits of truncations and the continuity
   of Coleman's transform (§3.3.3) use.

### 1.4 The trace property and the invariances

1. **The trace property.** For `u : c₀(J, R) →L[R] c₀(I, R)` compactoid and
   `v : c₀(I, R) →L[R] c₀(J, R)` bounded, `charPowerSeries (u ∘ v) = charPowerSeries (v ∘ u)`
   (Bellaïche, Proposition II.1.17; Serre, §5): both composites are compactoid by §0.2.4, the
   identity holds for row-supported `u` by §1.1.2 (Sylvester), and §1.3.2–3 pass to the limit. The
   hypothesis on one factor only is what the later uses need — the other factor is a bounded
   inverse, a change of basis, or a Hecke operator.
2. **Conjugation.** For a continuous linear equivalence `e : c₀(I, R) ≃L[R] c₀(J, R)` and `u`
   compactoid, `charPowerSeries (e ∘ u ∘ e⁻¹) = charPowerSeries u` (Buzzard, Lemma 2.5 and Corollary
   2.6; Bellaïche, Corollary II.1.18), formally from clause 1. Reindexing along `I ≃ J` is the
   special case of a permutation matrix, and is also the termwise identity of minors.
3. **Diagonal intertwining without inverses.** If `d : I → R` has unit values and
   `d i · matrixCoeff v i j = matrixCoeff u i j · d j` for all `i, j`, then `minor v S = minor u S`
   for every `S` (`det (D_S) · det (V_S) = det (U_S) · det (D_S)`, and `det D_S` is a unit), hence
   `charCoeff v = charCoeff u` termwise in the defining sums, with **no** compactness hypothesis and
   no inverse of `diag d` as an operator. This is the form in which "`P` and `P'` are conjugated by
   an infinite diagonal matrix" is used by the spectral-halo roadmap, where the inverse
   `diag (1/n!)` is unbounded.
4. **Transposition.** `minor u S` is invariant under transposition of the matrix; hence if `v` is an
   operator whose matrix is the transpose of the matrix of `u`, and both are compactoid, then
   `charPowerSeries v = charPowerSeries u`. ⚠ The transpose of a bounded matrix need not be the
   matrix of a bounded operator (its columns need not tend to `0`), and a compactoid `u` need not
   have compactoid transpose; both hypotheses are genuine. The spectral-halo roadmap's `U_p` is the
   case where the transpose is the compactoid operator and the determinant of the original is
   defined through it.
5. **Extension by zero.** For `u` compactoid on `c₀(I, R)` and `v` the operator on `c₀(I ⊕ J, R)`
   whose `I × I` corner is `u` and whose other corners vanish,
   `charPowerSeries v = charPowerSeries u` (Buzzard, pp. 72–73; Bellaïche, §II.1.6).
6. **Coboundary twists of block operators.** For a block operator `blockOp T` on `c₀(σ × I, R)` and
   units `φ a`, `ψ a` with `φ a · ψ a = 1`, the twisted operator with blocks `(ψ a · φ b) • T a b`
   has the same Fredholm determinant: it is the conjugate by the block-scalar diagonal `diag (φ)`,
   and clause 1 applies. A twist by a `1`-cocycle on the block indices therefore moves no eigenvalue
   and no slope.

### 1.5 The determinant on orthonormalisable modules and on modules with property (Pr)

1. For `M` potentially orthonormalisable and `u` compactoid on `M` (§0.4.1), define
   `charPowerSeries u := charPowerSeries (e ∘ u ∘ e⁻¹)` for a continuous linear equivalence
   `e : M ≃L[R] c₀(I, R)`, and prove it independent of `e` by §1.4.2. In particular the determinant
   of a compact operator on an orthonormalisable Banach module does not depend on the orthonormal
   basis used to compute its matrix (Serre, Proposition 7; Buzzard, §2), and it is unchanged under
   replacing the norm of `M` by an equivalent one (Johansson–Newton, Proposition 2.1.8).
2. For `M` with property (Pr), `M ⊕ M' ≅ c₀(I, R)`, define
   `charPowerSeries u := charPowerSeries (u ⊕ 0)` and prove it independent of the complement and the
   equivalence by §1.4.5 and §1.4.2 (Buzzard, §2; Bellaïche, §II.1.6). The ideal and transport
   properties of §1.4 hold in this generality.
3. **Finite modules.** For `M` finite free and `u` any endomorphism,
   `charPowerSeries u = charpolyRev (toMatrix u)` in any basis, and
   `charPowerSeries u = (charpoly u).reverse`, Mathlib's `LinearMap.charpoly` reversed. For `M`
   finitely generated projective, `charPowerSeries u` is the reversed characteristic polynomial of
   `u ⊕ 0` on a free complement, a polynomial of degree at most the rank of that complement,
   independent of the complement by §1.1.2.
4. **Restriction to summands.** If `p` is an idempotent of `M →L[R] M` commuting with a compactoid
   `u`, then `u` restricts to compactoid operators on `range p` and on `range (1 − p)`, both of
   which have property (Pr) when `M` does, and
   `charPowerSeries u = charPowerSeries (u |_{range p}) · charPowerSeries (u |_{range (1 − p)})`
   (§1.6.4). This is the form in which the determinant of a Hecke operator on a space of forms is
   computed from a decomposition of that space.

### 1.6 Multiplicativity: partitions, blocks and finite factors

1. **Serre's partition lemma.** If `u` is compactoid on `c₀(I, R)` and preserves `c₀(I', R)` for a
   decidable `I' ⊆ I` — no matrix entry from the `I'`-columns into the `I ∖ I'`-rows — then
   `charPowerSeries u = charPowerSeries u' · charPowerSeries u''`, where `u'` is the restriction to
   `c₀(I', R)` and `u''` the compression to `c₀(I ∖ I', R)` (Serre, Lemme 2; Jacobs, Lemma 1.15):
   the principal minors of a block-triangular matrix factor, and the sums over `S = S' ⊔ S''` split
   accordingly.
2. **Block-diagonal and block-triangular operators.** For a finite `σ` and a compactoid operator on
   `c₀(σ × I, R)` that is block-diagonal (`matrixCoeff u (a, i) (b, j) = 0` for `a ≠ b`),
   `charPowerSeries u = ∏_a charPowerSeries (blockCorner u a)`; for a block-triangular operator with
   respect to a linear order on `σ`, the same product over the diagonal corners, by iterating clause
   1.
3. **Direct sums.** `charPowerSeries (u ⊕ v) = charPowerSeries u · charPowerSeries v` on
   `c₀(I ⊕ J, R)`, and hence on direct sums of modules with property (Pr).
4. **Commuting idempotents.** If `p` is an idempotent commuting with a compactoid `u`, then
   `charPowerSeries u = charPowerSeries (u ∘ (1 − p)) · charPowerSeries (u ∘ p)` (Buzzard, §3;
   Johansson–Newton, proof of Theorem 2.2.2): `u ∘ p` and `u ∘ (1 − p)` are compactoid, they
   commute, their product is zero, and `1 − Tu = (1 − T u p)(1 − T u (1 − p))` is an identity in the
   ring of entire series with operator coefficients, to which §2.4's multiplicativity applies.
5. **Finite factors.** If in clause 4 the range of `u ∘ p` lies in the span of a finite set of `r`
   vectors, then `charPowerSeries (u ∘ p)` is a polynomial of degree at most `r`; if the range of
   `p` is finite free of rank `r` with `u ∘ p` acting by the matrix `A`, then
   `charPowerSeries (u ∘ p) = charpolyRev A`. So a compactoid operator with a finite free `u`-stable
   direct summand `F` has
   `charPowerSeries u = charpolyRev (u |_F) · charPowerSeries (u |_{complement})`, the split that
   reads the slopes of a classical subspace off the whole space (§4.5).

### 1.7 Base change and change of norm

1. **Bounded base change.** For a ring homomorphism `ψ : R → S` of Banach–Tate rings with
   `‖ψ r‖ ≤ C ‖r‖`, the operator `ψ_* u` on `c₀(I, S)` with matrix `ψ (matrixCoeff u i j)` is
   compactoid when `u` is, and `charPowerSeries (ψ_* u) = PowerSeries.map ψ (charPowerSeries u)`,
   coefficientwise `charCoeff (ψ_* u) n = ψ (charCoeff u n)` (Bellaïche, Lemma II.1.23, matrix-wise;
   Buzzard, Corollaries 2.9–2.10). Everything is stated on matrices, through the functoriality of
   `c₀` in the ring (the `p`-adic-functional-analysis roadmap's §2.1.5); ⚠ no completed tensor
   product is defined or used, and the statement `c₀(I, R) ⊗̂_R S = c₀(I, S)` is out of scope.
2. **Bicontinuous ring isomorphisms.** For `e : R ≃+* S` continuous with continuous inverse — which
   over Tate rings is only *power*-equivalent, not bounded (that roadmap's §0.3.2) — `e_* u` is
   compactoid when `u` is and `charPowerSeries (e_* u) = PowerSeries.map e (charPowerSeries u)`
   (Johansson–Newton, Proposition 2.1.8). ⚠ This is a topological statement about summability and is
   not a special case of clause 1.
3. **Equivalent norms.** Replacing the norm of `R` by an equivalent Tate norm, or the norm of the
   module by a bounded-equivalent one, changes neither `IsCompactoid` nor `charPowerSeries`
   (Johansson–Newton, Proposition 2.1.8, the norm-change part, through their Lemmas 2.1.6–2.1.7 as
   recorded in that roadmap's §0.3.2).
4. **Specialisation.** For `A` a Banach–Tate ring and a bounded homomorphism `x : A → K` to a field
   — a point of the family — `charPowerSeries (x_* u) = PowerSeries.map x (charPowerSeries u)`: the
   Fredholm determinant of a family specialises to the Fredholm determinant of the fibre. This is
   how the overconvergent-forms and spectral-halo roadmaps pass from `Λ^{>1/p}[1/T]` or an affinoid
   algebra to a point of weight space; and by §1.7.1 applied to an isometric extension `K → L` of
   fields, the determinant, its zeros and the Riesz theory of Layer 3 may be read in any extension,
   in particular in an algebraic closure.

### Examples

`diag (pⁿ)` on `c₀(ℕ, ℚ_p)`: `charCoeff = (−1)ⁿ p ^ (n(n−1)/2)` and
`charPowerSeries = ∏ (1 − pⁿ T)`, restricted at every radius; the rank-one operator with matrix
`a_{ij} = pⁱ`: every `2 × 2` minor vanishes, the trace is `∑ pⁱ = 1/(1 − p)`, and
`charPowerSeries = 1 − T/(1 − p)`; a `2 × 2` block `[[0, 1], [p, 0]]` extended by zero:
`charPowerSeries = 1 − p T²`; `diag (pⁿ)` conjugated by the unitriangular perturbation `1 + N` of
the `p`-adic-functional-analysis roadmap's §2.7 example, same determinant; the block-diagonal
`diag (pⁿ) ⊕ diag (p ^ (2n))` on `c₀(Fin 2 × ℕ, ℚ_p)`, the product; base change of `diag (pⁿ Xⁿ)`
over `ℚ_p⟨X⟩` along evaluation at `X = x₀`, `‖x₀‖ ≤ 1`, which gives `∏ (1 − pⁿ x₀ⁿ T)`, and along
`X ↦ 0`, which gives `1`.

### Dependencies

Layer 0; Mathlib's `charpolyRev`, `det_one_sub_mul_comm`, `resultant` and `charpoly.univ` for §1.1;
the `p`-adic-functional-analysis roadmap's §0.1 (sums), §2.1.5 (functoriality of `c₀`) and §0.3.2
(norm comparison).

---

## Layer 2: entire series, the resolvent, and the invertibility criterion

`R` is a nonarchimedean Banach ring with `‖1‖ = 1` in §§2.1–2.3, Banach–Tate from §2.4 on; `A` is a
Banach `R`-algebra where points are evaluated.

### 2.1 Entire series and their evaluation

1. Define `PowerSeries.IsEntire f := ∀ c > 0, PowerSeries.IsRestricted c f` — the coefficients
   satisfy `‖aₙ‖ cⁿ → 0` for every `c` — and the subring `R{{T}} := PowerSeries.entireSubring R`
   (Bellaïche, Definition II.1.16; Johansson–Newton, §2.1). Prove that entire series are closed
   under sums, products, scalar multiples, `rescale`, and the substitution `T ↦ Tᵏ`; that
   polynomials are entire; and that a series restricted at every radius `c ≥ c₀` is entire.
2. **Evaluation.** For `f` entire and `x ∈ A`, define `evalAt x f := ∑' n, coeff n f • x ^ n`,
   convergent by the `p`-adic-functional-analysis roadmap's §4.1.3 at the radius `‖x‖`; prove that
   `f ↦ evalAt x f` is a ring homomorphism `R{{T}} → A`, that it agrees with polynomial evaluation
   on polynomials, that `‖evalAt x f‖ ≤ ‖f‖_{‖x‖}` (the Gauss norm at `‖x‖`), that `x ↦ evalAt x f`
   is continuous, and that `evalAt x (rescale a f) = evalAt (a x) f`. For `A = M →L[R] M` this
   evaluates a series at an operator, which §2.4 uses. ⚠ This is not Mathlib's `PowerSeries.eval₂`
   (convention 6); record the agreement on polynomials as the only bridge.
3. **Hasse derivatives.** Define
   `hasseDeriv k f := PowerSeries.mk (fun n ↦ (n + k).choose k * coeff (n + k) f)` (Serre's `Δᵏ`,
   Buzzard's `∆ᵏ` on p. 22; Mathlib's `Polynomial.hasseDeriv` for polynomials), and prove:
   `hasseDeriv 0 = id`, `hasseDeriv 1 = PowerSeries.derivative`, `hasseDeriv k` of an entire series
   is entire, the Leibniz rule
   `hasseDeriv k (f * g) = ∑_{i + j = k} hasseDeriv i f * hasseDeriv j g`, the composition rule
   `hasseDeriv i ∘ hasseDeriv j = (i + j).choose i • hasseDeriv (i + j)`, and the Taylor expansion
   `evalAt (a + t) f = ∑' k, evalAt a (hasseDeriv k f) * t ^ k` for entire `f` and all `a, t ∈ A`,
   which is the identity `f(T + a) = ∑ (Δᵏ f)(a) Tᵏ` in `A{{T}}`.
4. **Gauss norms and convergence in `R{{T}}`.** The Gauss norms `‖f‖_c := sup ‖aₙ‖ cⁿ` for `c > 0`
   (the Newton-polygons roadmap's §2.3) are submultiplicative norms on `R{{T}}`, multiplicative when
   the norm of `R` is (that roadmap's §5.4), and a sequence converges in `R{{T}}` when it converges
   in every `‖·‖_c`; `R{{T}}` is complete for this family of norms, and polynomials are dense.

### 2.2 Euclidean division and relative primality

1. **Dominance of a polynomial at large radius.** For `B ∈ R[T]` with unit leading coefficient there
   is `ρ₀ > 0` such that for every `ρ ≥ ρ₀` the leading coefficient is the dominant one at radius
   `ρ`: `‖bₖ‖ ρᵏ < ‖b_d‖ ρ^d` for `k < d` (Bellaïche, Lemma II.2.5). When the leading coefficient is
   a multiplicative unit, `B` is then Martin-distinguished of order `d` at radius `ρ` in the sense
   of the adic-spaces roadmap's §0.5.
2. **Euclidean division in `R{{T}}`.** For `F` entire and `B` a polynomial whose leading coefficient
   is a multiplicative unit, there are a unique entire `q` and a unique polynomial `r` of degree
   less than `deg B` with `F = B q + r` (Bellaïche, Proposition II.2.8): Weierstrass division at a
   radius `ρ ≥ ρ₀` (the adic-spaces roadmap's §0.5; the Newton-polygons roadmap's §3.1 over a field)
   gives `q_ρ` restricted at `ρ` and `r_ρ` a polynomial, uniqueness of the remainder identifies the
   `r_ρ` and hence the `q_ρ`, and a series restricted at every large radius is entire. Record the
   norm identity `‖F‖_ρ = max(‖B‖_ρ ‖q‖_ρ, ‖r‖_ρ)` at every radius at which `B` is dominant
   (Bellaïche's (II.2.1)), which is the estimate the slope factorisation of §4.3 needs. ⚠ Over a
   field every nonzero leading coefficient is a multiplicative unit; over a ring the
   multiplicativity is a genuine hypothesis and is carried explicitly.
3. **Relative primality.** Define `IsEntireCoprime F G := ∃ a b ∈ R{{T}}, a F + b G = 1`, i.e.
   `(F, G) = R{{T}}` (Johansson–Newton, Definition 2.2.1). Prove symmetry, stability under products
   in either argument, invariance under units of `R{{T}}`, and preservation by ring homomorphisms
   `R → S`. For `B` a polynomial with multiplicatively-unit leading coefficient and `F = B q + r`
   its division, `(B, F)` is coprime in `R{{T}}` if and only if `(B, r)` is coprime in `R{{T}}`
   (Bellaïche, Corollary II.2.9). Over a field `K`, two polynomials are coprime in `K{{T}}` if and
   only if they are coprime in `K[T]` (Mathlib's `IsCoprime`), if and only if they have no common
   root in an algebraic closure; hence a polynomial `B` and an entire `F` are coprime in `K{{T}}` if
   and only if no root of `B` is a zero of `F`. ⚠ Over a ring the polynomial criterion is not
   available and coprimality is carried as a hypothesis, discharged by clause 4.
4. Over a Banach–Tate ring, coprimality of a polynomial `Q` with `Q(0) = 1` and unit leading
   coefficient against an entire `S` is detected by the resultant transform of §3.3.4 and by the
   invertibility of `Q*(u)` for any compactoid `u` with `charPowerSeries u = Q S` (§3.4.2); state
   the pointers, so that the three criteria are proved once each.

### 2.3 Good zeros

1. Define `IsGoodZero F a s`, for `F` entire, `a ∈ R` and `s : ℕ`: `evalAt a (hasseDeriv i F) = 0`
   for all `i < s` and `evalAt a (hasseDeriv s F)` is a unit of `R` (Bellaïche, Definition II.2.11).
   Prove that the order `s` is determined by `F` and `a`, and that for `F` with `F(0) = 1` and
   `s ≥ 1` the point `a` is a unit (Bellaïche, Exercise II.2.12).
2. **Factorisation at a good zero.** If `a` is a good zero of order `s` of an entire `F` with
   `F(0) = 1`, then `F = (1 − a⁻¹ T) ^ s · G` with `G` entire, `G(0) = 1`, and `evalAt a G` a unit
   (Bellaïche, §II.2.3): divide by `(1 − a⁻¹T)^s` (§2.2.2, the leading coefficient being a unit of
   norm `‖a‖^{−s}`, multiplicative when `a` is) and read the vanishing of the remainder off the
   Taylor expansion. Conversely such a factorisation makes `a` a good zero of order `s`.
3. **Leibniz transports good zeros.** If `F = G H` with `a` a good zero of `G` of order `s` and
   `evalAt a H` a unit, then `a` is a good zero of `F` of order `s`; if `a` is a good zero of
   `F = G H` of order `s` and `evalAt a H` is a unit, then it is a good zero of `G` of order `s`.
4. **Over a field every zero is good.** For `K` a field and `F` entire with `F(0) = 1`, every zero
   `a` of `F` has a finite order `s ≥ 1` — the first `k` with `(Δᵏ F)(a) ≠ 0`, which exists because
   the Weierstrass product of the Newton-polygons roadmap's §4.5.2 shows an entire series vanishing
   with all its Hasse derivatives at a point is zero, contradicting `F(0) = 1` — and `a` is a good
   zero of that order; the order is the multiplicity of `a` as a zero of the polynomial factor of
   the Newton-polygons roadmap's §4.3.2.

### 2.4 The Fredholm resolvent

`u` is compactoid on `c₀(I, R)` with `H := charPowerSeries u` and coefficients `cₙ`.

1. Define the resolvent coefficients `resolventCoeff u m := ∑_{k ≤ m} cₖ • u ^ (m − k)` in
   `c₀(I, R) →L[R] c₀(I, R)`, and prove Serre's recursion `v₀ = 1`, `vₘ = cₘ • 1 + u ∘ v_{m−1}`, and
   the identities `(1 − T u) · ∑ vₘ Tᵐ = ∑ vₘ Tᵐ · (1 − T u) = H(T) · 1` in the ring of power series
   with operator coefficients (Serre, §6).
2. **The resolvent is entire.** `‖vₘ‖ Cᵐ → 0` for every `C > 0`: the matrix entries of `vₘ` are sums
   of `(m+1) × (m+1)` minors of the matrix of `u` bordered by a row and a column, and the Hadamard
   bound of §1.2.4 applies (Serre, Proposition 10). Hence `P(a, u) := ∑' m, aᵐ • vₘ` converges in
   operator norm for every `a ∈ R`, and
   `(1 − a • u) ∘ P(a, u) = P(a, u) ∘ (1 − a • u) = evalAt a H • 1`.
3. **Divided evaluations.** The partial sums `Nₛ(a, n) := ∑_{m < n} (m + s).choose s • aᵐ • v_{m+s}`
   of the `s`-th Hasse derivative of the resolvent converge in operator norm, commute with `u`, and
   are operator-norm limits of polynomials in `u`; the limits `Pₛ(a, u)` satisfy the identities
   obtained by applying `Δˢ` to clause 1. These are the operators from which the Riesz projector of
   §3.1 is built.
4. **The determinant value and its multiplicativity.** Define `fredholmDet u := evalAt 1 H`, Serre's
   `det(1 − u)`; then `fredholmDet (a • u) = evalAt a H`, `fredholmDet u = det (1 − A_S)` when the
   rows of `u` are supported on the finite `S` with matrix `A_S`, and for `u`, `v` compactoid,
   `fredholmDet (u + v − u ∘ v) = fredholmDet u · fredholmDet v`, i.e.
   `det ((1 − u)(1 − v)) = det (1 − u) det (1 − v)` (Serre, §5, corollary to Proposition 7): prove
   it for row-supported operators by the finite multiplicativity of `det` and pass to the limit
   along a common sequence of truncations (§1.3.3).

### 2.5 Serre's invertibility criterion and the spectrum

1. **Proposition 11.** For `u` compactoid and `a ∈ R`, `1 − a • u` is invertible in
   `c₀(I, R) →L[R] c₀(I, R)` if and only if `evalAt a H` is a unit of `R`, and then
   `(1 − a • u)⁻¹ = (evalAt a H)⁻¹ • P(a, u)` (Serre, Proposition 11; Buzzard §3). The direction
   "unit ⇒ invertible" is §2.4.2; the direction "invertible ⇒ unit" is the multiplicativity of
   §2.4.4 applied to `(1 − a u)⁻¹ = 1 − w` with `w = −a u (1 − a u)⁻¹` compactoid, giving
   `fredholmDet (a u) · fredholmDet w = 1`.
2. **The dichotomy at a good zero.** If `a` is a good zero of `H` of order `h ≥ 1`, then `1 − a • u`
   has a nonzero kernel: otherwise the resolvent identities force `Pₕ(a, u) = 0` and with it the
   unit `(Δʰ H)(a)`. Over a ring this is the eigenvector statement available before the projector
   exists; §3.1 sharpens it.
3. **The nonzero spectrum over a field.** For `K` a complete nonarchimedean field, `u` compactoid on
   `c₀(I, K)` and `λ ≠ 0`: `λ ∈ spectrum K u` if and only if `evalAt λ⁻¹ H = 0`, if and only if
   `λ⁻¹` is a zero of `det(1 − Tu)`; so the nonzero spectrum is `{a⁻¹ | H(a) = 0}`. By the
   Newton-polygons roadmap's §4.5.1 the zeros of an entire series in a closed disc are finite, so
   the nonzero spectrum is discrete in `K ∖ {0}`, has `0` as its only possible accumulation point,
   and lies in the closed ball of radius `‖u‖` (Mathlib's `spectrum.subset_closedBall_norm`).
   Combined with §3.2.1 every nonzero spectral value is an eigenvalue, which is Mathlib's Fredholm
   alternative in this setting, now over every complete nonarchimedean field and with `det(1 − Tu)`
   as the witness.
4. State clause 3 for a compact operator on any potentially orthonormalisable `K`-Banach space, via
   §1.5, and for modules with property (Pr).

### Examples

`∑ Tⁿ / n!` and `∏ (1 − pⁿ T)` are entire over `ℚ_p`; `∑ Tⁿ` is not; `padicExp` restricted to its
disc is not entire (the `p`-adic-functional-analysis roadmap's §4.5) — the entire series over `ℚ_p`
with a zero of every valuation are the Weierstrass products of the Newton-polygons roadmap's §4.5.2.
Division of `∏ (1 − pⁿ T)` by `1 − T` and by `1 − pT`; `(1 − T, ∏_{n ≥ 1} (1 − pⁿ T))` coprime and
`(1 − pT, ∏_{n ≥ 0} (1 − pⁿ T))` not; `a = p⁻¹` is a good zero of order `1` of `∏ (1 − pⁿ T)` over
`ℚ_p`, and `a = 1` a good zero of order `2` of `(1 − T)² (1 − pT)`; for `u = diag (pⁿ)`, `1 − p⁻¹ u`
is not invertible (`H(p⁻¹) = 0`) while `1 − 2 u` is (`H(2) = ∏ (1 − 2pⁿ)`, a unit of `ℤ_p`);
`spectrum ℚ_p (diag (pⁿ)) = {pⁿ | n} ∪ {0}`; the resolvent coefficients of a diagonal operator.

### Dependencies

Layer 1; the `p`-adic-functional-analysis roadmap's §4.1.3 (evaluation of restricted series) and
§1.1.5 (Neumann series); the adic-spaces roadmap's §0.5 and the Newton-polygons roadmap's §3.1
(Weierstrass division at a radius), §4.5 (zeros of entire series) and §5.4 (Gauss norms).

---

## Layer 3: Riesz theory

`R` is a Banach–Tate ring, `u` a compactoid operator on `c₀(I, R)` with `H = charPowerSeries u`, and
`K` a complete nonarchimedean nontrivially normed field where a field is needed. `Q*` denotes the
reciprocal polynomial `T ^ deg Q · Q(1/T)` (Mathlib's `Polynomial.reverse`), so that
`Q = ∏ (1 − tᵢ T)` has `Q* = ∏ (T − tᵢ)`, and `Q*(u)` is `Polynomial.aeval u Q.reverse`.

### 3.1 The Riesz projector at a good zero

1. **Existence.** If `a` is a good zero of `H` of order `h ≥ 1`, there are `p`, `w` in
   `c₀(I, R) →L[R] c₀(I, R)`, both operator-norm limits of polynomials in `u` (§2.4.3), with
   `p ∘ p = p`, `u ∘ p = p ∘ u`, `u ∘ w = w ∘ u`, `p ∘ w = w ∘ p`, `(1 − a • u) ^ h ∘ (1 − p) = 0`
   and `(1 − a • u) ∘ w = p` (Serre, §7, the construction of `e = ` the projector as a limit of
   divided evaluations of the resolvent; Johansson–Newton, Theorem 2.2.2, "the idempotent projectors
   lie in the closure of `R[u]`"). Package the conclusion as `IsRieszProjection u a h p w`.
2. **The decomposition.** For such `p`: `range (1 − p) = ker ((1 − a • u) ^ h)` and
   `range p = range ((1 − a • u) ^ h)`; `c₀(I, R) = range (1 − p) ⊕ range p` as topological
   complements (`Submodule.IsTopCompl`); both summands are `u`-stable; `1 − a • u` is nilpotent of
   order at most `h` on the first and invertible on the second, with inverse `w`; and `p` is the
   unique idempotent with these properties (`rieszProjection_unique`).
3. **Finiteness.** `ker ((1 − a • u) ^ h)` is finitely generated projective: `a • u` restricts to it
   as a compact operator with `1 − a • u` nilpotent, so §0.4.4 applies, and a closed direct summand
   of `c₀(I, R)` has property (Pr).
4. **Functoriality.** Every bounded operator commuting with `u` commutes with `p` and `w`, hence
   preserves both summands; the projector is compatible with bounded base change (§1.7.1): the
   base-changed `p` is the projector of the base-changed data, since good zeros and the defining
   identities are preserved by ring homomorphisms.
5. **The determinant on the summands.** `H = (1 − a⁻¹T) ^ h · G` with `G` entire and `G(a)` a unit
   (§2.3.2), `charPowerSeries (u |_{range p}) = G`, and
   `charPowerSeries (u |_{ker}) = (1 − a⁻¹T) ^ h`, so that `ker ((1 − a • u) ^ h)` has rank `h` at
   every prime of `R` — these are §3.4 applied to `Q = (1 − a⁻¹T) ^ h`, `S = G`, coprime by §2.2.3–4
   since `G(a)` is a unit.

### 3.2 Serre's decomposition over a field

`u` is compactoid on `c₀(I, K)`, or a compact operator on a potentially orthonormalisable `K`-Banach
space (§1.5.1). ⚠ `K` is any complete nonarchimedean nontrivially normed field: no discreteness of
the valuation is assumed (convention 7).

1. **The eigenvector theorem.** For `a ∈ K`, `evalAt a H = 0` if and only if `a ≠ 0` and `a⁻¹` is an
   eigenvalue of `u`: `H(a) = 0` makes `a` a good zero of some order `h ≥ 1` (§2.3.4), and §3.1.2
   gives `ker (1 − a • u) ≠ 0`; conversely an eigenvector for `a⁻¹` makes `1 − a • u` non-injective,
   so `H(a)` is not a unit by §2.5.1, i.e. `H(a) = 0`. Transport along continuous linear
   equivalences, so that the statement covers every Banach space with a potential orthonormal basis.
2. **Proposition 12.** For a zero `a` of `H` of order `h`: `c₀(I, K) = N ⊕ F` with
   `N = ker ((1 − a • u) ^ h)` of dimension exactly `h`, `F = range ((1 − a • u) ^ h)` closed, both
   `u`-stable, `1 − a • u` bijective on `F`, and `H = (1 − a⁻¹T) ^ h · H'` with `H'` entire and
   `H'(a) ≠ 0` (Serre, Proposition 12; Buzzard, §3). The dimension formula is §1.6.4 applied to the
   projector: `charPowerSeries (u |_N) = (1 − a⁻¹T) ^ dim N` by §1.1.3, since `a • u |_N` is
   unipotent, and comparing orders of vanishing at `a` with
   `H = charPowerSeries (u|_N) · charPowerSeries (u|_F)` and `H_F(a) ≠ 0` gives `dim N = h`. ⚠ The
   source proves the dimension formula for discretely valued `K` by choosing an orthogonal basis of
   `N`; the route above uses only that `N` is finite-dimensional and that its determinant is
   independent of the norm (§1.5.1 and the `p`-adic-functional-analysis roadmap's §1.3), and is to
   be followed instead.
3. **Algebraic multiplicities.** The eigenvalue `a⁻¹` has generalised eigenspace
   `maxGenEigenspace u a⁻¹ = N`, of dimension `h`, so the order of `a` as a zero of `det(1 − Tu)` is
   the algebraic multiplicity of `a⁻¹`; the generalised eigenspaces of distinct nonzero eigenvalues
   are independent, and for finitely many zeros `a₁, …, aₖ` the module splits as
   `N(a₁) ⊕ ⋯ ⊕ N(aₖ) ⊕ F` with `F` closed, `u`-stable, and `1 − aᵢ • u` bijective on `F` for each
   `i` (the product of the commuting projectors).
4. **Reading in an extension.** For an isometric extension `L / K` of complete fields, the
   determinant is unchanged (§1.7.1), and the eigenvalues of `u` in `L` are the reciprocals of the
   zeros of `H` in `L`; over an algebraic closure every slope of §4.2 is realised. The nonzero
   spectrum of §2.5.3 consists of eigenvalues, each of finite algebraic multiplicity, accumulating
   only at `0`.

### 3.3 Coleman's resultant and the spectral mapping formula

1. **The transform on polynomials.** For polynomials `B` and `P` over `R` with `P(0) = 1`, define
   `colemanD B P := Res_X (P*(X), 1 − T · B(X)) ∈ R[T]`, the resultant in the variable `X` of the
   reciprocal polynomial `P*` and of `1 − T B(X)` viewed over `R[T]` (Coleman, §A3; Buzzard, p. 21;
   Bellaïche, §II.2.4), built on Mathlib's `Polynomial.resultant`. Prove that if `P = ∏ (1 − tᵢ T)`
   splits then `colemanD B P = ∏ (1 − B(tᵢ) T)`, that
   `colemanD B (P₁ P₂) = colemanD B P₁ · colemanD B P₂`, that `colemanD B P (0) = 1`, that the
   coefficients of `colemanD B P` are polynomials, for fixed `B`, in the coefficients of `P`
   (Bellaïche, Lemma II.2.13), and that the transform commutes with ring homomorphisms.
2. **The transform on entire series.** For `B` a polynomial and `F` entire with `F(0) = 1`, define
   `colemanD B F` as the coefficientwise limit of `colemanD B (trunc (N + 1) F)`, prove that the
   limit exists, that it is entire (Buzzard's rescaling `Res(Q, P) = Res(u^{−n} Q(uT), P(uT))` on p.
   21, which reduces to bounded coefficients), that it is multiplicative in `F`, that
   `F ↦ colemanD B F` is Lipschitz in the sense of §1.3.2 and continuous in every Gauss norm, and
   that it extends clause 1.
3. **Coprimality through the transform.** For `Q` a polynomial with `Q(0) = 1` and unit leading
   coefficient `v`, set `B_Q := 1 − v⁻¹ Q*` (Bellaïche's `1 − Q*(φ)/Q*(0)`). Then
   `evalAt 1 (colemanD B_Q S)` is a unit if and only if `(Q, S)` is coprime in `R{{T}}` (Bellaïche,
   Lemma II.2.14), and `colemanD B_Q (Q S)` has a good zero of order `deg Q` at `1` when `(Q, S)` is
   coprime (Bellaïche, Proposition II.2.15).
4. **The spectral mapping formula.** For `u` compactoid and `B` a polynomial with `B(0) = 0` (so
   that `B(u)` is compactoid by §0.2.4), `charPowerSeries (B(u)) = colemanD B (charPowerSeries u)`
   (Bellaïche, Proposition II.2.16; Coleman, §A4): for a row-supported `u` this is §1.1.4,
   `Res (charpoly A, g) = det g(A)`, applied to `g = 1 − T B`, and §1.3.3 with clause 2 pass to the
   limit. Record the two instances used later: `B = X ^ k`, for which `charPowerSeries (u ^ k)` is
   the transform of `charPowerSeries u` and, over a field containing the `k`-th roots of unity, the
   zeros of `det(1 − T u ^ k)` are the `k`-th powers of the zeros of `det(1 − Tu)`; and `B = B_Q`,
   which is the engine of §3.4.

### 3.4 The Riesz–Coleman decomposition over a Banach–Tate ring

`Q ∈ R[T]` with `Q(0) = 1` and leading coefficient a unit `v`, `S` entire with `S(0) = 1`,
`charPowerSeries u = Q · S`, and `(Q, S)` coprime in `R{{T}}`. No Noetherian hypothesis on `R`.

1. **The theorem.** There are `p`, `w` in `c₀(I, R) →L[R] c₀(I, R)`, operator-norm limits of
   polynomials in `u`, with `p ∘ p = p`, commuting with `u` and with each other, `Q*(u) ∘ w = p` and
   `Q*(u) ^ deg Q ∘ (1 − p) = 0` (Coleman, Theorem A4.3; Buzzard, Theorem 3.3; Bellaïche, Theorem
   II.2.18; Johansson–Newton, Theorem 2.2.2). Package the conclusion as
   `IsRieszColemanProjection u Q S v p w`. The proof is Bellaïche's: `φ' := B_Q(u)` is compactoid
   with `charPowerSeries φ' = colemanD B_Q (Q S)` (§3.3.4), which has a good zero of order `deg Q`
   at `1` (§3.3.3), and §3.1.1 at `a = 1` for `φ'` gives `p`, `w` — in the closure of
   `R[φ'] ⊆ R[u]`, which is why they commute with `u` and not only with `φ'`.
2. **Refinements.** `Q*(u) ∘ (1 − p) = 0` (zero, not merely nilpotent); `ker Q*(u) = range (1 − p)`;
   `ker Q*(u)` is finitely generated projective of rank `deg Q` at every prime of `R`
   (`Module.rankAtStalk`), hence free of rank `deg Q` over a local ring or a field; `u` is
   invertible on `ker Q*(u)`; `charPowerSeries (u |_{ker Q*(u)}) = Q` and
   `charPowerSeries (u |_{range p}) = S`; `(Q, charPowerSeries u)` is coprime if and only if `Q*(u)`
   is invertible on all of `c₀(I, R)` (Buzzard, Lemma 3.1); and the complement is unique: any pair
   of `u`-stable topological complements on which `Q*(u)` is respectively nilpotent and invertible
   is `(ker Q*(u), range p)`. The rank is computed through the residue fields (§1.1.3's caveat) and
   the degree bound through the localisations.
3. **The matrix realisation.** On the finite piece, `u |_{ker Q*(u)}` is given, after choosing a
   rank factorisation of `1 − p` as in §1.1.2, by a matrix `Ψ` with `charpolyRev Ψ = Q` and
   `Q*(Ψ) = 0`, and every operator commuting with `u` restricts to a matrix commuting with `Ψ`.
4. **Base change.** For a bounded homomorphism `ψ : R → S'` (§1.7.1), the data
   `(ψ_* u, map ψ Q, map ψ S)` satisfy the hypotheses of clause 1, and `ψ_* p` is the projector of
   the base-changed data, by uniqueness; hence the rank of `ker Q*(u)` is `deg Q` in every fibre of
   a family, which is the constancy statement the overconvergent-forms and spectral-halo roadmaps
   use.
5. **Over a field.** For `K` a field, `ker Q*(u)` has dimension `deg Q`, `u |_{ker Q*(u)}` has
   `charpolyRev = Q`, i.e. characteristic polynomial `Q*`, and its eigenvalues in an algebraic
   closure are the reciprocal roots of `Q`; `range p` is closed with
   `charPowerSeries (u|_{range p}) = S`, so the reciprocal roots of `Q` are not eigenvalues of `u`
   on `range p`.

### 3.5 Commuting operators and eigensystems

1. If a bounded operator `t` commutes with `u`, it commutes with the projectors of §3.1 and §3.4,
   preserves `ker Q*(u)` and `range p`, and restricts to an endomorphism of the finitely generated
   projective module `ker Q*(u)`; a commuting family of bounded operators acts on it as a commuting
   family of matrices (§3.4.3).
2. **Common generalised eigenvectors.** Over an algebraically closed complete `K`, a commuting
   family `(tᵢ)` of operators commuting with `u` has, in each nonzero finite-dimensional `u`-stable
   piece `N = ker ((1 − a • u) ^ n)` (§3.2), a common generalised eigenvector: a nonzero `ψ ∈ N` and
   scalars `λᵢ` with `ψ ∈ maxGenEigenspace (tᵢ) λᵢ` for every `i`, obtained by the finite induction
   on commuting endomorphisms of a finite-dimensional space. The assignment `tᵢ ↦ λᵢ` is a system of
   eigenvalues, and the set of such systems on `ker Q*(u)` is finite.
3. Over a Banach–Tate ring, the action of the commuting family on `ker Q*(u)` and its base changes
   (§3.4.4) is what a Hecke algebra acting on a finite-slope subspace is; state the ring-level
   functoriality and leave the arithmetic to the overconvergent-forms roadmap.

### Examples

`diag (pⁿ)` on `c₀(ℕ, ℚ_p)`: at `a = p^{−n}` the projector is the coordinate projection onto `K eₙ`,
`N = K eₙ`, `h = 1`, and `H = (1 − pⁿ T) · ∏_{m ≠ n} (1 − pᵐ T)`; the operator
`[[0, 1], [p, 0]] ⊕ 0` with `H = 1 − p T²`: no zero in `ℚ_p`, two zeros `± p^{−1/2}` in `ℚ_p(√p)`
each of order `1`, eigenvectors `(1, ±√p)`; the rank-one operator with matrix `pⁱ`, eigenvalue
`1/(1 − p)` with eigenvector `(pⁱ)ᵢ` and `H = 1 − T/(1 − p)`; Coleman's transform of `∏ (1 − pⁿ T)`
by `B = X²`, namely `∏ (1 − p^{2n} T)`; the Riesz–Coleman decomposition over `R = ℚ_p⟨X⟩` of
`u = diag (1 + pX, p, p², …)` for `Q = 1 − (1 + pX) T`, whose leading coefficient is a
multiplicative unit of `ℚ_p⟨X⟩` (the Gauss norm is multiplicative), with `ker Q*(u) = R e₀` of rank
`1`, `S = ∏_{n ≥ 1} (1 − pⁿ T)`, and the specialisation at `X = x₀` giving the decomposition of
`diag (1 + p x₀, p, p², …)`; a commuting family: the diagonal operators commuting with `diag (pⁿ)`
and their common eigenvectors `eₙ`.

### Dependencies

Layers 1–2; Mathlib's `Polynomial.resultant`, `Submodule.IsTopCompl`, `Module.rankAtStalk`,
`Module.End.maxGenEigenspace`; the `p`-adic-functional-analysis roadmap's §1.3 (finite-dimensional
spaces) and §2.2.4 (lifting property, projectivity).

---

## Layer 4: slopes

`K` is a complete nonarchimedean nontrivially normed field with an additive valuation `(v, e, b)` in
the sense of the Newton-polygons roadmap's Layer 1, so that `‖x‖ = b ^ (−e (v x))`; `u` is a
compactoid operator on `c₀(I, K)`, or a compact operator on a potentially orthonormalisable
`K`-Banach space through §1.5, with `H := charPowerSeries u`, entire with `H(0) = 1`. §§4.3.3–5 and
§4.4 are stated over a Banach–Tate ring `R` where a ring is named. Slopes are read in `ℝ` through
`e`, and are rational when `Γ = ℚ` and integral when `Γ = ℤ` (that roadmap's convention 2).

### 4.1 The Newton polygon of a Fredholm determinant

1. The Newton polygon of `H` is that roadmap's §2.2 applied to `n ↦ v (charCoeff u n)`; it starts at
   `(0, 0)` because `c₀ = 1`, and because `H` is entire its slopes are unbounded (that roadmap's
   §4.4.4): every slope occurs with finite multiplicity, the sequence of finite unit slopes
   `s₀ ≤ s₁ ≤ ⋯` (its §0.4) is infinite and tends to `+∞` unless `H` is a polynomial, in which case
   it has exactly `deg H` terms. Define `slopes u` as this multiset of finite unit slopes and
   `slopeMultiplicity u s` as the length of the face of slope `s`.
2. **Rescaling.** `charPowerSeries (a • u) = rescale a H`, so the unit slopes of `a • u` are those
   of `u` shifted by `v a`: the polygon is sheared by the line of slope `v a`.
3. **Products.** For a block-diagonal `u` (§1.6.2), or any factorisation `H = H₁ H₂` into entire
   series with unbounded slopes, the polygon of `H` is the Minkowski sum of the polygons of the
   factors and the slope multisets add (that roadmap's §§5.1–5.2); the polygon is invariant under
   conjugation, reindexing and extension of the field along an isometric embedding with compatible
   valuations (§1.7).
4. **What the polygon does not see.** The kernel of `u` and, more generally, the nilpotent part of
   `u` are invisible: a nilpotent finite-rank operator has `H = 1` and no slopes. The polygon
   records the nonzero spectrum only, and the "slope `∞`" is never counted.

### 4.2 Slopes are valuations of eigenvalues

1. **Zeros at a slope.** For a finite unit slope `s` of `H` of multiplicity `l`, `H` has exactly `l`
   zeros of valuation `−s`, counted with multiplicity, in the completion `ℂ_K` of an algebraic
   closure of `K` with the valuation of that roadmap's §1.5 (its §4.3.2, together with the
   Weierstrass factorisation at the vertex ending the face of slope `s`), and every zero of `H` has
   valuation `−s` for some finite unit slope `s` (its §4.3.3).
2. **Serre's slope reading.** Base-changing along `K → ℂ_K` (§1.7.4) and applying §3.2.3, the
   multiset `slopes u` equals the multiset of valuations `v λ` of the nonzero eigenvalues `λ` of `u`
   on `c₀(I, ℂ_K)`, each counted with its algebraic multiplicity (Serre, §7; Buzzard, §3; Jacobs,
   §1.2): a zero `a` of order `h` is the eigenvalue `λ = a⁻¹` of multiplicity `h` and valuation
   `v λ = −v a = s`. State it as an equality of multisets, and the two counting corollaries: the
   number of eigenvalues of valuation at most `h`, with multiplicity, is the number of unit slopes
   at most `h`, that roadmap's `faceRight`-count at `h`; and the number of valuation exactly `h` is
   `slopeMultiplicity u h`.
3. **Existence at a slope.** In particular every finite unit slope `s` is the valuation of an
   eigenvalue: there is `x ≠ 0` with `u x = λ • x` and `‖λ‖ = b ^ (−e s)`. Over an algebraically
   closed complete `K` no extension is needed; over `ℚ_p` the eigenvector may live only over an
   extension, as in the example `1 − p T²` below.
4. **Normalisation.** With `K = ℚ_p` and `v p = 1` (that roadmap's `Γ = ℤ` instance) the slopes of a
   compact operator are rational numbers; with `K = ℂ_p` and the valuation normalised at `p` (its
   `Γ = ℚ` instance) they are the `p`-adic valuations of the eigenvalues, and "the slopes are
   `j + ½`" is an identity in `ℚ`.

### 4.3 Slope factorisations and the slope-`≤ h` decomposition

1. **The slope factorisation over a field.** For every real `h`, `H = Q_{≤h} · S_{>h}` with `Q_{≤h}`
   a polynomial with `Q_{≤h}(0) = 1` whose polygon is the part of the polygon of `H` with slopes at
   most `h` — so `deg Q_{≤h}` is the number of unit slopes at most `h` — and `S_{>h}` entire with
   `S_{>h}(0) = 1` and all slopes greater than `h` (that roadmap's §3.4.2 at the radius `b ^ h`,
   where `S_{>h}` is a unit of the series restricted at that radius). The factors are coprime in
   `K{{T}}` (its §3.4.3 and §2.2.3: no common zero), the factorisation is unique, and `Q_{≤h}`
   divides `Q_{≤h'}` for `h ≤ h'`. Iterating over the distinct slopes, `Q_{≤h}` is the product of
   the pure polynomials `Q_{=s}` of the slopes `s ≤ h` (its §3.4.1), pairwise coprime.
2. **The slope-`≤ h` decomposition over a field.** Applying §3.4 to `(Q_{≤h}, S_{>h})`:
   `c₀(I, K) = M_{≤h} ⊕ M_{>h}` with `M_{≤h} = ker Q_{≤h}*(u)` of dimension `deg Q_{≤h}`, both
   summands closed and `u`-stable, `charpolyRev (u |_{M_{≤h}}) = Q_{≤h}` and
   `charPowerSeries (u |_{M_{>h}}) = S_{>h}`; every eigenvalue of `u` on `M_{≤h}` in `ℂ_K` has
   valuation at most `h` and every eigenvalue on `M_{>h}` has valuation greater than `h`;
   `M_{≤h} ⊆ M_{≤h'}` for `h ≤ h'`; `M_{≤h} = ⊕_{s ≤ h} M_{=s}` with `M_{=s} = ker Q_{=s}*(u)` of
   dimension `slopeMultiplicity u s`; every bounded operator commuting with `u` preserves each piece
   (§3.5); and the decomposition is compatible with extension of the field. This is Coleman's slope
   decomposition (Coleman, Appendix A; Buzzard, Theorem 3.3 and §4; Bellaïche, §II.3;
   Johansson–Newton, Definition 2.2.5 and Theorem 2.2.13 in the field case).
3. **Dominant indices over a ring.** Define `IsDominantIndex ρ F N` for `F ∈ R{{T}}`, `ρ > 0`,
   `N : ℕ`: `‖aₖ‖ ρ ^ k ≤ ‖a_N‖ ρ ^ N` for all `k`, with strict inequality for `k > N` (Bellaïche,
   Definition II.2.3, "`N(F, ρ)`"); and `Polynomial.IsDominant ρ P`: `deg P` is a dominant index of
   `P` at `ρ` and the leading coefficient is a unit (his Definition II.2.4). Prove that every entire
   `F` has a dominant index at every `ρ` (the maximum of `‖aₖ‖ ρᵏ` is attained, at a largest index),
   that dominant indices are nondecreasing in `ρ`, that a polynomial with unit leading coefficient
   is dominant at every large `ρ` (§2.2.1), and that over a field `N` is a dominant index of `F` at
   `ρ = b ^ s` if and only if `(N, v a_N)` is the right endpoint of the face of slope `s` of the
   polygon of `F` (that roadmap's §0.5, supporting lines) — so that over a field clause 1 at `h = s`
   is the factorisation at that vertex.
4. **The vertex factorisation over a ring.** If `F` is entire with `F(0) = 1`, `N` is a dominant
   index of `F` at `ρ`, and the dominant coefficient `a_N` is a multiplicative unit, then
   `F = P · G` with `P` a `ρ`-dominant polynomial of degree `N`, `P(0) = 1`, multiplicative leading
   coefficient, and `G` entire with `G(0) = 1` and dominant index `0` at `ρ`; the factors are
   coprime in `R{{T}}` and the factorisation is unique (Bellaïche, Theorem II.3.6; the norm-level
   form of Johansson–Newton, Definition 2.2.5 and Lemma 2.2.7; the "standard factorisation argument"
   of Liu–Wan–Xiao's Remark 3.25). Two proofs are available and either is acceptable: Bellaïche's
   Newton iteration `P_{l+1} = P_l + X_l`, `Q_{l+1} = Q_l + Y_l`, driven by the division estimate of
   §2.2.2; or Weierstrass preparation — `F` is Martin-distinguished of order `N` at radius `ρ`
   (adic-spaces roadmap §0.5), so `T ^ N` divides by `F` with a polynomial remainder, and
   `P := T ^ N − r` reversed is the monic factor, uniqueness of the division killing the remainder
   of the entire division. For `ρ₁ ≤ ρ₂` with dominant indices `N₁ ≤ N₂`, `P_{N₁}` divides `P_{N₂}`.
5. **The slope-`≤ h` decomposition over a ring.** Combining clause 4 with §3.4 for a compactoid `u`
   over `R` with `H = charPowerSeries u`: at every dominant index `N` at radius `ρ` with
   multiplicative dominant coefficient, `c₀(I, R) = ker P*(u) ⊕ range p` with `ker P*(u)` projective
   of rank `N`, `charPowerSeries (u |_{ker P*(u)}) = P` and `charPowerSeries (u |_{range p}) = G`,
   functorial for commuting operators and compatible with bounded base change (§3.4.4): the
   specialisation at a point `x : R → K` is the Riesz–Coleman decomposition of the fibre along
   `(map x P, map x G)`, and it is the slope-`≤ log_b ρ` decomposition of the fibre whenever `x`
   preserves the dominance of `a_N` — for instance when the specialisation is an isometry on the
   coefficients of `H`. This is the norm-level form of Johansson–Newton's Theorem 2.2.13; ⚠ its
   pointwise form over the Gelfand spectrum of `R`, in which a dominant index is required at every
   multiplicative seminorm, is out of scope and needs the adic-spaces roadmap. The spectral-halo
   roadmap applies clause 5 to the halo `U_p` over `Λ^{>1/p}[1/T]` at the vertices of the halo
   polygon.

### 4.4 Bounds on the polygon from the matrix

1. **The Hadamard (Hodge) bound.** Let `r*` be the decreasing rearrangement of the row norms of `u`
   (§1.2.4). The Newton polygon of `H` lies on or above the convex polygon with heights
   `n ↦ ∑_{k<n} (−log_b r*_k)`, the *Hodge polygon* of the matrix of `u` (Serre, §5; Wan, for
   nuclear matrices): `e (v cₙ) ≥ ∑_{k<n} (−log_b r*_k)` is §1.2.4 read through
   `‖x‖ = b ^ (−e (v x))`, and the right-hand side is convex in `n` because `r*` is nonincreasing.
   In particular every slope of `u` is at least `−log_b r*_0 = −log_b ‖u‖`.
2. **Row weights.** If `‖matrixCoeff u i j‖ ≤ σ ^ (w i)` for all `i, j`, with `0 ≤ σ < 1` and
   `w : I → ℕ`, then `‖minor u S‖ ≤ σ ^ (∑_{i ∈ S} w i)` and `‖charCoeff u n‖ ≤ σ ^ (f n)` for any
   `f : ℕ → ℕ` with `f n ≤ ∑_{i ∈ S} w i` for every `S` of cardinality `n`. The two weights that the
   later roadmaps use: the identity weight on `I = ℕ`, for which the minimum is `n (n − 1) / 2` and
   the polygon of `H` lies on or above the polygon with unit slopes `k · (−log_b σ)`,
   `k = 0, 1, 2, …` (Serre, §5; Jacobs, Theorem 2.12, the bound); and the block weight
   `w (a, k) = k` on `I = ι × ℕ` with `ι` finite, for which the minimum is `∑_{k<n} ⌊k / |ι|⌋` and
   the unit slopes are `⌊k / |ι|⌋ · (−log_b σ)`. State the polygon form through the Newton-polygons
   roadmap's polygon of a convex sequence (its §§0.1–0.2, the polygon of the partial sums of a
   nondecreasing slope sequence) and its height comparison.
3. **Two-sided weights.** If `‖matrixCoeff u i j‖ ≤ σ ^ (w i − w' j)` (truncated subtraction) for
   weights `w`, `w' : I → ℕ` with `w i − w' i → +∞` cofinitely, then the minors of every degree are
   summable — the definition of `charCoeff` makes sense — and `‖charCoeff u n‖ ≤ σ ^ (f n)` for any
   `f` with `f n ≤ ∑_{i ∈ S} w i − ∑_{i ∈ S} w' i` for every `S` of cardinality `n`, by the
   two-sided Hadamard bound of §1.1.6 and the permutation inequality; for `I = ι × ℕ` and weights
   `w (a, k) = g k`, `w' (a, k) = g' k` with `g − g'` nondecreasing, the minimum over `|S| = n` is
   attained on an initial segment of the block enumeration, `∑_{k<n} (g − g') ⌊k / |ι|⌋`. ⚠ No Tate
   hypothesis and no compactness is assumed here: `u` need not be compactoid (its rows need not
   decay), and this is the case of the halo `U_p` of the spectral-halo roadmap, whose coefficients
   `cₙ ∈ T ^ (λ n) Λ^{>1/p}` with `λ n = ∑_{k<n} (⌊k/t⌋ − ⌊k/pt⌋)` are exactly this bound with
   `σ = ‖T‖`; the determinant of that operator is then identified with that of its compactoid
   transpose by §1.4.4.
4. **The exact case.** Let `u` be compactoid on `c₀(ℕ, K)` and `d : ℕ → K` multiplicative nonzero
   elements with `‖d₀‖ > ‖d₁‖ > ⋯`, such that `‖matrixCoeff u i j‖ ≤ ‖d i‖` for all `i, j` and, for
   every `n`, the leading principal minor of the rescaled matrix
   `(d i ⁻¹ · matrixCoeff u i j)_{i, j < n}` has norm `1`. Then `‖charCoeff u n‖ = ∏_{i<n} ‖d i‖`
   for every `n`, and the unit slopes of `H` are exactly `v d₀, v d₁, …`: the term
   `S = {0, …, n − 1}` is the unique dominant term of the sum defining `cₙ`, since
   `∏_{i ∈ S} ‖d i‖ < ∏_{i<n} ‖d i‖` for every other `S` of cardinality `n` (the strict monotonicity
   of `‖d‖`), and the unique-dominant-term principle of the `p`-adic-functional-analysis roadmap's
   §0.1.3 applies. The case `d i = ϖ ^ i` is Jacobs's Theorem 2.12 at an arbitrary `ϖ` with
   `0 < ‖ϖ‖ < 1`: `‖cₙ‖ = ‖ϖ‖ ^ (n(n−1)/2)` and the slopes are `0, v ϖ, 2 v ϖ, …`; the case
   `d i = ϖ ^ (2i+1)` over `ℚ_3(√3)` with `ϖ = √3` gives the slopes `i + ½`. State the additive form
   as well: `v (charCoeff u n) = ∑_{i<n} v (d i)`.
5. **Where the bounds live.** Clauses 1–3 are statements about `‖charCoeff u n‖` and need no
   valuation; clause 4's equality and the polygon forms are stated through `(v, e, b)`. The
   valuation `v_ϖ` of the `p`-adic-functional-analysis roadmap's §0.4.3 reads clause 4 as
   `v_ϖ (charCoeff u n) = n (n − 1) / 2` when `d i = ϖ ^ i`; record that reading once, at the seam
   of convention 8, and nowhere else.

### 4.5 Finite factors and initial segments

1. For a finite free `u`-stable direct summand `F` of rank `r` with `u`-stable complement `N`
   (§1.6.5), `H = charpolyRev (u |_F) · charPowerSeries (u |_N)`, the polygon of `H` is the
   Minkowski sum of the polygon of `charpolyRev (u |_F)` — a polygon with `r` finite slopes — and
   the polygon of `charPowerSeries (u |_N)`, and `slopes u = slopes (u |_F) + slopes (u |_N)` as
   multisets (§4.1.3).
2. **Initial segments.** If every slope of `u |_F` is at most every slope of `u |_N`, then the
   polygon of `H` agrees with the polygon of `charpolyRev (u |_F)` on `[0, r]` (the Newton-polygons
   roadmap's §5.3): the first `r` unit slopes of `u` are the slopes of `u |_F`. Conversely, if for
   some `h` every slope of `u |_F` is at most `h` and every slope of `u |_N` is greater than `h`,
   then `F = M_{≤h}` (§4.3.2 and the uniqueness of the complement in §3.4.2). This is how a
   finite-dimensional `u`-stable subspace — the classical subspace of a space of overconvergent
   forms — supplies an initial segment of the slopes of the whole space, the mechanism of the
   spectral-halo roadmap's touching argument.
3. **The ordinary part.** `M_{≤0}` is the *ordinary* subspace, of dimension the number of unit
   slopes equal to `0`, i.e. of eigenvalues of valuation `0`; when `‖u‖ ≤ 1` there are no negative
   slopes (§4.4.1) and `M_{≤0} = M_{=0}`.

### Examples

Over `ℚ_p` with `v p = 1`: `diag (pⁿ)` has `H = ∏ (1 − pⁿ T)`, unit slopes `0, 1, 2, …`, each of
multiplicity `1`, `M_{≤h}` the span of `e₀, …, e_{⌊h⌋}`, and its rescaled leading minors are `1`, so
§4.4.4 applies with `d i = pⁱ`; `diag (pⁿ) ⊕ diag (p ^ (2n))` has slope multiset
`{0, 0, 1, 2, 2, 3, 4, 4, …}`; `p⁻¹ • diag (pⁿ)` has slopes `−1, 0, 1, …`; the `2 × 2` block
`[[p, 1], [0, p]]` extended by zero has `H = (1 − p T)²` with slopes `1, 1`, while its Hodge polygon
has slopes `0, 1` — the bound of §4.4.1 is strict, and the rescaled leading `1 × 1` minor `p` has
norm `p⁻¹ ≠ 1`, so §4.4.4 does not apply; `[[0, 1], [p, 0]]` extended by zero has `H = 1 − p T²`
with slopes `½, ½`, and its eigenvalues `± √p` live in `ℚ_p(√p)`; over `ℚ_3(√3)` with `ϖ = √3` and
`v 3 = 1`, `diag (ϖ ^ (2i+1))` has slopes `i + ½` exactly, by §4.4.4 with `d i = ϖ ^ (2i+1)`; the
finite factor `diag (p⁻¹) ⊕ diag (pⁿ)_{n ≥ 1}` has the initial segment `{−1}` supplied by the finite
piece; a two-sided-weight matrix `a_{ij} = p ^ max(2i − j, 0)` on `c₀(ℕ, ℚ_p)`, bounded, not
compactoid, with summable minors and `‖cₙ‖ ≤ p ^ (−n(n−1)/2)` by §4.4.3 with `w i = 2i`, `w' j = j`.

### Dependencies

Layers 1–3; the Newton-polygons roadmap throughout (Layer 1 for the valuation, §§0.1–0.5, §2.2,
§§3.3–3.4, §§4.3–4.5, §§5.1–5.3); the adic-spaces roadmap's §0.5 for the Weierstrass route in
§4.3.4; the `p`-adic-functional-analysis roadmap's §0.1.3 (unique dominant term) and §0.4.3 (`v_ϖ`).

---

## Dependency graph

```text
Layer 0  →  Layer 1  →  Layer 2  →  Layer 3  →  Layer 4
```

The layers are linear. Layer 0 stands on Layers 0–2 and §4.1 of the `p`-adic-functional-analysis
roadmap and, in §0.5 only, on Mathlib's `IsCompactOperator`; Layer 1 adds the finite-dimensional
facts of §1.1 on Mathlib's `charpolyRev` and `resultant`; Layer 2 uses Weierstrass division at a
radius from the adic-spaces roadmap's §0.5 (the Newton-polygons roadmap's §3.1 over a field) and the
zeros of entire series from the Newton-polygons roadmap's §4.5; Layer 3 uses Layers 1–2 and
Mathlib's `Submodule.IsTopCompl` and `Module.rankAtStalk`; Layer 4 uses Layers 1–3 and the
Newton-polygons roadmap throughout. The `p`-adic-functional-analysis roadmap is cited on every page;
the adic-spaces roadmap at §2.2.1–2, §4.3.4 and, for the pointwise slope conditions, in the scope;
the overconvergent-forms and spectral-halo roadmaps are consumers and are never cited as
dependencies.

## Acceptance examples

The following should be proved alongside the general theory, and they are the things a reviewer
should check are present. `ℚ_p` carries `v p = 1`.

- `diag (pⁿ)` on `c₀(ℕ, ℚ_p)` is compactoid with `rowNorm = p ^ (−n)`; the shift is bounded and not
  compactoid, hence not completely continuous; the identity of `c₀(ℕ, ℚ_p)` is not completely
  continuous and the identity of `ℚ_p ^ n` is; the identity of `ℂ_p` has finite rank and is not
  `IsCompactOperator`; over `ℚ_p`, `IsCompletelyContinuous ↔ IsCompactOperator` for the operators
  above.
- `f ↦ f(p z)` on `ℚ_p⟨z⟩` is compactoid by the restriction-of-radius criterion, and `f ↦ f(z + 1)`
  is not; the inclusion `LA_1 → LA_2` of locally analytic functions is compactoid.
- `charPowerSeries (diag (pⁿ)) = ∏ (1 − pⁿ T)` with `charCoeff = (−1)ⁿ p ^ (n(n−1)/2)`, entire; the
  rank-one operator with matrix `a_{ij} = pⁱ` has `charPowerSeries = 1 − T/(1 − p)`, trace
  `1/(1 − p)`, and every `2 × 2` minor zero; `[[0, 1], [p, 0]]` extended by zero has
  `charPowerSeries = 1 − p T²` and `[[p, 1], [0, p]]` has `(1 − p T)²`.
- The trace property on `u = diag (pⁿ)`, `v = ` the shift:
  `charPowerSeries (u ∘ v) = charPowerSeries (v ∘ u)`, both equal to `1` (both composites are
  strictly upper triangular, so every principal minor vanishes); the conjugate of `diag (pⁿ)` by the
  unitriangular perturbation of the `p`-adic-functional-analysis roadmap's §2.7 example has the same
  determinant; the coboundary twist of a block operator has the same determinant.
- `diag (pⁿ) ⊕ diag (p ^ (2n))` on `c₀(Fin 2 × ℕ, ℚ_p)` has the product determinant and slope
  multiset `{0, 0, 1, 2, 2, 3, 4, 4, …}`; the partition lemma on a block-triangular `2 × 2` block
  extended by zero.
- Base change: `diag (pⁿ Xⁿ)` over `ℚ_p⟨X⟩` is compactoid with `charPowerSeries = ∏ (1 − pⁿ Xⁿ T)`,
  specialising at `X = x₀`, `‖x₀‖ ≤ 1`, to `∏ (1 − pⁿ x₀ⁿ T)` and at `X = 0` to `1`.
- `∏ (1 − pⁿ T)` and `∑ Tⁿ / n!` are entire over `ℚ_p`, `∑ Tⁿ` is not; Euclidean division of
  `∏ (1 − pⁿ T)` by `1 − T` and by `1 − p T`; `(1 − T, ∏_{n ≥ 1} (1 − pⁿ T))` is coprime in
  `ℚ_p{{T}}` and `(1 − pT, ∏_{n ≥ 0} (1 − pⁿ T))` is not; `p⁻¹` is a good zero of order `1` of
  `∏ (1 − pⁿ T)` and `1` a good zero of order `2` of `(1 − T)² (1 − p T)`.
- Serre's criterion on `u = diag (pⁿ)`: `1 − p⁻¹ u` is not invertible and `1 − 2u` is, with
  `fredholmDet (2 u) = ∏ (1 − 2pⁿ)` a unit of `ℤ_p`; `spectrum ℚ_p (diag (pⁿ)) = {pⁿ | n} ∪ {0}`.
- Riesz theory on `diag (pⁿ)`: at `a = p ^ (−n)` the projector is the coordinate projection, the
  eigenspace is `ℚ_p eₙ`, the order is `1`; on `[[0, 1], [p, 0]] ⊕ 0` the zeros `± p ^ (−1/2)` of
  `1 − p T²` are not in `ℚ_p`, and over `ℚ_p(√p)` each has order `1` with eigenvectors `(1, ±√p)`.
- Coleman's transform of `∏ (1 − pⁿ T)` by `B = X²` is `∏ (1 − p ^ (2n) T)`, and
  `charPowerSeries (diag (pⁿ) ^ 2)` equals it.
- Riesz–Coleman over `ℚ_p⟨X⟩` for `u = diag (1 + pX, p, p², …)` and `Q = 1 − (1 + pX) T`: the
  leading coefficient is a multiplicative unit, `S = ∏_{n ≥ 1} (1 − pⁿ T)`, `(Q, S)` is coprime,
  `ker Q*(u) = ℚ_p⟨X⟩ · e₀` has rank `1`, and the specialisation at `X = x₀` is the decomposition of
  `diag (1 + p x₀, p, p², …)` at its unit-slope eigenvalue.
- Slopes: `diag (pⁿ)` has unit slopes `0, 1, 2, …` with `M_{≤h} = span (e₀, …, e_{⌊h⌋})`, and the
  exact case applies with `d i = pⁱ`; `p⁻¹ • diag (pⁿ)` has slopes `−1, 0, 1, …`; over `ℚ_3(√3)`,
  `diag (√3 ^ (2i+1))` has slopes `i + ½` in `ℚ`; `[[p, 1], [0, p]]` has slopes `1, 1` above its
  Hodge slopes `0, 1`; `[[0, 1], [p, 0]]` has slopes `½, ½` realised by eigenvalues only over
  `ℚ_p(√p)`; the finite factor `diag (p⁻¹) ⊕ diag (pⁿ)_{n ≥ 1}` supplies the initial segment `{−1}`.
- The two-sided matrix `a_{ij} = p ^ max(2i − j, 0)` is bounded, not compactoid, has summable minors
  and `‖charCoeff n‖ ≤ p ^ (−n(n−1)/2)`.

## Beyond this roadmap

⚠ **This section is a roadmap-for-a-roadmap. Do not attempt any of it here.** It records what this
roadmap is for, so that the conventions above are chosen with the sequels in mind.

The compactoid operators, the determinant on modules with property (Pr), the base change of §1.7 and
the slope bounds of §4.4 are the setting in which the overconvergent-forms roadmap proves that `U_p`
is compact on Buzzard's `S^D_κ(U)` at every locally analytic weight, defines `det(1 − T·U_p)` there,
and reads the slopes of the finite-slope eigenforms off it through §4.2–4.3 and the Hecke
eigensystems through §3.5. The two-sided bound of §4.4.3, the transposition and
diagonal-intertwining invariances of §1.4, the ring-level Riesz–Coleman decomposition of §3.4 and
the dominant-index factorisation of §4.3.4–5 are what the spectral-halo roadmap consumes for
Liu–Wan–Xiao's halo estimate over `Λ^{>1/p}[1/T]` and its slope consequences, with the finite-factor
reading of §4.5 as its touching argument. What those roadmaps ask of this one is that the
determinant exist over a Banach–Tate ring that is not a field and not Noetherian, that Riesz theory
come with projectors commuting with everything that commutes with `u`, and that the polygon bounds
be stated for row weights indexed by `ι × ℕ` — all of which is what is specified above.

Further afield: the spectral variety `{det(1 − T u) = 0} ⊆ 𝒲 × 𝔸¹` over an affinoid or adic weight
space, its admissible covering by the pieces where a slope-`≤ h` factorisation exists, and the
eigenvariety machine that glues Hecke algebras over it (Coleman–Mazur; Buzzard §§4–5; Bellaïche;
Johansson–Newton §2.3 and §3; Andreatta–Iovita–Pilloni's *halo spectral*), together with the
pointwise form of the slope conditions on the Gelfand spectrum, are rigid and adic geometry and
belong with the adic-spaces roadmap; the completed tensor product form of base change belongs with
the separate roadmap that the adic-spaces roadmap names for fibre products; Hida's ordinary
projector `lim u^{n!}` is a statement about lattices and belongs with the overconvergent-forms
roadmap; and the Fredholm determinants of Dwork operators, the rationality of zeta functions and
Wan's theory of nuclear operators and Hodge polygons over `p`-adic rings, which are the origin of
§4.4.1, are a roadmap of their own.

## References

- J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*, Publ. Math.
  IHÉS 12 (1962), 69–85 — [Serre]. The source of Layers 0–3 in the field case: §2 (completely
  continuous endomorphisms, Proposition 6, the row-decay criterion), §5 (the Fredholm determinant
  `det(1 − tu)`, Proposition 7 and its corollaries, Lemme 2), §6 (the Fredholm resolvent,
  Proposition 10), §7 (Riesz theory, Propositions 11–12).
- K. Buzzard, *Eigenvarieties*, in *L-functions and Galois representations*, LMS Lecture Notes 320
  (2007), §§2–3 — [Buz07]. Lemma 2.3 (finitely generated submodules over Noetherian rings), Lemma
  2.5 and Corollary 2.6 (independence of the basis), Corollaries 2.9–2.10 (base change), pp. 72–73
  (extension by zero and property (Pr)), §3: p. 21 (`D(B, P)` as a resultant), p. 22 (the divided
  derivatives `∆ˢ`), Lemma 3.1, Proposition 3.2 and Theorem 3.3 (Riesz theory for a coprime
  factorisation), and §4 (the slope-`≤ h` decomposition in families, out of scope).
- J. Bellaïche, *The Eigenbook*, Pathways in Mathematics, Birkhäuser (2021), Chapter 3, and the
  draft Chapter II — [Bel]. Cited by the draft numbering: §II.1 (Definitions II.1.3, II.1.16, Lemmas
  II.1.4, II.1.8, II.1.14, II.1.15, II.1.23, Proposition II.1.9, Scholium II.1.10, Proposition
  II.1.17, Corollary II.1.18, Propositions II.1.20–II.1.21), §II.2 (Definitions II.2.3–II.2.4, Lemma
  II.2.5, Proposition II.2.8, Corollary II.2.9, Definition II.2.11, Exercise II.2.12, Lemmas
  II.2.13–II.2.14, Propositions II.2.15–II.2.16, Theorem II.2.18) and §II.3 (Theorem II.3.6 and the
  iteration (II.3.1)–(II.3.6)); published Hypothesis 3.1.8 and Lemma 3.1.12.
- C. Johansson, J. Newton, *Extended eigenvarieties for overconvergent cohomology*, Algebra & Number
  Theory 13 (2019); arXiv:1604.07739v4, §§2.1–2.3 — [JN]. Definition 2.1.5 (compact operators over
  Banach–Tate rings), Proposition 2.1.8 (invariance under bicontinuous isomorphisms), Definition
  2.2.1 (Fredholm series, relative primality), Theorem 2.2.2 (Riesz theory, with the projectors in
  the closure of `R[u]`), Definition 2.2.5 and Lemma 2.2.7 (slope-`≤ h` factorisations), Theorem
  2.2.13 (slope-`≤ h` decompositions), §2.3 (spectral varieties, out of scope). Every statement
  cited from [JN] is stated here with its Noetherian hypothesis removed.
- R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. 127 (1997),
  417–479, Appendix A — [Col97]. §A2 (compact operators and the characteristic series over Banach
  modules), §A3 (resultants and `D(B, P)`), §A4 (Riesz theory, Theorem A4.3), §A5 (the slope
  decomposition). Banach–Tate rings are exactly Coleman's Banach algebras with `|A^m| ≠ 1`.
- R. Coleman, B. Mazur, *The eigencurve*, in *Galois representations in arithmetic algebraic
  geometry*, LMS Lecture Notes 254 (1998) — the spectral curve, out of scope; cited in "Beyond".
- J. Ludwig, *Spectral theory and the eigenvariety machine*, arXiv:2407.18073 — [Lud24]. Remark 2.25
  and Lemma 2.26 (closedness of finitely generated submodules and where it is used), and the
  exposition of Buzzard's machine.
- L. Gruson, *Théorie de Fredholm p-adique*, Bull. Soc. Math. France 94 (1966), 67–95 — [Gru66]. The
  origin of compactoid operators in the `p`-adic Fredholm theory (§0.5); and L. Gruson, M. van der
  Put, *Banach spaces*, Bull. Soc. Math. France, Mémoire 39–40 (1974), 55–100.
- A. C. M. van Rooij, *Non-Archimedean Functional Analysis*, Dekker (1978), Chapters 3–4 — [vR]; and
  C. Perez-Garcia, W. H. Schikhof, *Locally Convex Spaces over Non-Archimedean Valued Fields*,
  Cambridge Studies 119 (2010), Chapters 2, 3 and 8 — [PGS]. `t`-orthogonal complements, compactoid
  sets, and compactoid (= completely continuous) operators.
- P. Schneider, *Nonarchimedean Functional Analysis*, Springer Monographs (2002) — [Sch]. The
  normed-space background, as in the `p`-adic-functional-analysis roadmap.
- D. Jacobs, *Slopes of Compact Hecke Operators*, PhD thesis, Imperial College (2003), Chapters 1–2
  — [Jac03]. §1.1 (matrices and generating functions, Proposition 1.3), §1.2 (compact operators on
  `c₀(ℕ, K)`, Corollary 1.10), Lemma 1.15 (Serre's partition lemma), Lemma 2.7 (compactness by
  restriction of radius), Theorem 2.12 (the exact slope theorem).
- R. Liu, D. Wan, L. Xiao, *The eigencurve over the boundary of weight space*, Duke Math. J. 166
  (2017); arXiv:1412.2584v4 — [LWX]. Theorem 3.16 (the halo estimate, the two-sided bound of
  §4.4.3), the proof's diagonal conjugation and transposition (§1.4.3–4), and Remark 3.25 (the
  vertex factorisation). Consumed by the spectral-halo roadmap; cited here for the shape of §4.4.3.
- D. Wan, *Dwork's conjecture on unit root zeta functions*, Ann. of Math. 150 (1999), 867–927, and
  *Higher rank case of Dwork's conjecture*, J. Amer. Math. Soc. 13 (2000), 807–852 — [Wan]. Nuclear
  operators, Fredholm determinants over `p`-adic rings, and the Hodge polygon bound (§4.4.1).
- B. Dwork, *On the rationality of the zeta function of an algebraic variety*, Amer. J. Math. 82
  (1960), 631–648 — the origin of `p`-adic Fredholm determinants; cited in "Beyond".
- F. Andreatta, A. Iovita, V. Pilloni, *Le halo spectral*, Ann. Sci. Éc. Norm. Supér. 51 (2018),
  Annexe B — spectral varieties over adic spaces; cited in "Beyond".
- K. S. Kedlaya, *p-adic Differential Equations*, Cambridge Studies 125 (2010), Chapter 2 — Newton
  polygons and the factorisation of power series along them, the argument [LWX] cite for their
  Remark 3.25.
- N. Bourbaki, *Théories spectrales*, Chapitre 3 — the reference of Mathlib's `IsCompactOperator`.

⚠ **Orientation and normalisation.** [Serre] and [Buz07] write `det(1 − tu)`, [Bel] `P_φ(T)`,
[Col97] `det(1 − Tu)`; all agree with `charPowerSeries` here, with constant term `1`. The matrix of
an operator is indexed rows-by-coordinates as in the `p`-adic-functional-analysis roadmap's
convention 7; [Buz07] and [Bel] write the transpose, so their "rows tend to `0`" is the row decay
here after transposition of the letters, and nothing else changes. A zero `a` of `det(1 − Tu)` is
the *reciprocal* of an eigenvalue: the slopes of §4.2 are valuations of eigenvalues `λ = a⁻¹`, i.e.
the negatives of the valuations of the zeros, which is the sign convention of the Newton-polygons
roadmap's §4.1 (slope `m` ↔ roots of valuation `−m`). [Bel]'s draft numbering `II.x.y` corresponds
to the published `3.x.y` where the material was published; the draft §II.2–II.3 has no published
counterpart in Chapter 3 and is cited by the draft alone. [JN]'s Lemma 2.1.6 is cited in its
corrected form (arXiv v4). When transcribing a statement, check the orientation against convention 3
and the sign against §4.2.2 rather than assuming them.

## Existing Lean work

The principal source of existing code is `github.com/WilliamCoram/PhD` (Apache-2.0), at commit
`747bb77` (2026-09-12): the directory `PhD/Main/TateFredholm/` for all five layers — the merged
development of Buzzard's, Bellaïche's and Johansson–Newton's theories over a Banach–Tate ring,
organised around `IsCompactoid` exactly as convention 1 prescribes — together with
`PhD/Main/NewtonPolygons/OfSlopes.lean` (the polygon of a prescribed slope sequence, §4.4.2), the
generic halves of `PhD/Main/JacobsSlash/5_EigenSlopes.lean` (§4.2.3) and
`PhD/Main/QMF/Weight/08_HeckeAlgebra.lean` (§3.5.2), and, as instances of the theory rather than
sources for it, `PhD/Main/QMF/Weight/{06_Compact, 08_Slopes}.lean` and
`PhD/Main/LWX/{04_Halo, 05_TateRiesz}.lean`. It is the only formalisation of this material known to
us; the pin names the commit at which the source tree acquired its present layout, and the
mathematics it records was complete at commit `1f43221` (2026-09-11), the ring-level Riesz theory
having landed on 2026-09-06. The file `PhD/Main/TateFredholm/02_CharpolyPairingZ.lean` postdates the
pin and is not a migration source.

The existing material in those directories is by William Coram, who has agreed to its integration
into Tau Ceti. ⚠ The wider repository also contains files by other authors, derived from the FLT
project and from Mathlib; those are not migration sources for this roadmap, and the provenance of
anything copied must be checked file-by-file rather than directory-by-directory. The three blueprint
files `PhD/Main/Test/bad/CompactOperators{,Bellaiche,JohanssonNewton}.lean` (769, 947 and 803 lines,
with 35, 44 and 32 direct `sorry`s) are source documentation of the three published treatments —
each carries a dictionary against its source and a section on how the sources' hypotheses differ —
and are not migration sources.

Two separate audits are recorded below, for the reason the adic-spaces roadmap gives: a declaration
with no direct `sorry` is not the same as a theorem whose dependency cone is axiom-clean. The direct
column is a file-level `grep` count, which over-counts (comments match) and sees no cross-file
dependence. At the pin above, every file listed has a direct count of **0** (the single match in
`13_FiniteFactor.lean` is the word in a comment). The transitive column must be regenerated at
migration by a `#print axioms` gate on the capstones in Tau Ceti CI; the source project reports
every file listed clean on `propext`, `Classical.choice` and `Quot.sound`, and that claim is to be
re-verified, not carried over.

| Roadmap section | Existing source | Direct status at the pin | Transitive status | Roadmap status |
|---|---|---|---|---|
| §0.1 finite rank, completely continuous | `TateFredholm/02_Compact.lean` (`IsFiniteRank`, `IsCompletelyContinuous`, the ideal lemmas, `isCompletelyContinuous_of_tendsto`) | no direct `sorry` | audit required | present; the identity criterion §0.1.3 is new |
| §0.2 compactoid operators | `TateFredholm/04_Matrix.lean` (`rowNorm`, `IsCompactoid`, `IsCompactoid.isCompletelyContinuous`, `tendsto_truncation_comp`, `.comp_left`, `.comp_right`), `05_Noetherian.lean` (`isCompletelyContinuous_iff_rowNorm`), `06_BlockOp.lean` (`restrictOp`, `reindexOp`, `blockOp`, `isCompactoid_restrictOp`, `isCompactoid_blockOp`), `08_BlockMap.lean`, `08_BaseChange.lean` (`isCompactoid_map_equiv`, `isCompactoid_baseChange`), `05_GenFun.lean` (`isCompactoid_of_row_decay`, `diagOp`) | no direct `sorry` | audit required | present; the iff form of the truncation criterion and the closedness-hypothesis form of §0.2.9 are new |
| §0.3 kernels and radius | `TateFredholm/05_GenFun.lean` (`ofCoeffs`, `ofGenFun`, `diagRescale`), `06_WeightGenFun.lean` (`RowIntAt`), `00_Compose.lean` (`compAn`), `QMF/Weight/06_Compact.lean` (the application) | no direct `sorry` | audit required | partial; the restriction-of-radius criterion §0.3.3 is new in this generality |
| §0.4 ON-able and (Pr) modules | `TateFredholm/03_ModelSpace.lean`, `06_Pr.lean` (`finite_of_one_sub_compact_nilpotent`, `finite_projective_of_one_sub_compact_nilpotent`), `05_Fredholm.lean` (`charPowerSeries_conj`, `charPowerSeries_extendZero`) | no direct `sorry` | audit required | present; the intrinsic definition of `IsCompactoid` on (Pr) modules is new |
| §0.5 Mathlib bridge, compactoid sets | — | — | — | new |
| §1.1 finite-dimensional preliminaries | `TateFredholm/00_Charpoly.lean` (`charpolyRev_map`, `charpolyRev_mul_comm`, `charpolyRev_eq_of_mul_eq`, `exists_mul_eq_of_idempotent`, `charpolyRev_eq_one_sub_pow_rank`), `00_Resultant.lean` (`resultant_charpoly`, `det_aeval_eq_prod_roots`), `01_CharpolyPairing.lean` (`roots_charpolyRev`, `roots_charpoly_of_mul_eq_smul`), `05_Fredholm.lean` (the principal-minors expansion inside `charCoeff_eq_det_coeff`, the Hadamard bound `norm_det_le_of_row_bounds`), `06_Slopes.lean` (`norm_det_le_pow_of_row_bound`), `06_TwoSidedBound.lean` | no direct `sorry` | audit required | present; the expansion and the Hadamard bound are private and are to be made public Mathlib PR candidates |
| §1.2–1.3 minors, coefficients, entirety, continuity | `TateFredholm/05_Fredholm.lean` (`minor`, `summable_minor`, `charCoeff`, `charPowerSeries`, `charPowerSeries_isEntire`, `norm_charCoeff_sub_le`, `charCoeff_eq_det_coeff`), `09_Riesz.lean` (`charCoeff_smul`, `charPowerSeries_smul`) | no direct `sorry` | audit required | present; the decreasing-rearrangement form §1.2.4 is new |
| §1.4 the trace property and invariances | `TateFredholm/05_Fredholm.lean` (`charPowerSeries_comm`, `charPowerSeries_conj`, `charPowerSeries_extendZero`), `06_BlockOp.lean` (`charPowerSeries_reindexOp`, `charPowerSeries_blockOp_twist`), `07_Conjugation.lean` (`charPowerSeries_eq_of_diag_intertwine`), `LWX/05_TateRiesz.lean` (`minor_tateOp`, transposition in the halo instance) | no direct `sorry` | audit required | present; transposition is to be stated generally |
| §1.5 the determinant on (Pr) modules | `TateFredholm/05_Fredholm.lean`, `12_RieszColeman.lean` (`exists_polynomial_charPowerSeries_of_range_le`, `exists_matrix_realisation`) | no direct `sorry` | audit required | present as the transport statements; the definitions on abstract modules are new |
| §1.6 multiplicativity | `TateFredholm/06_BlockOp.lean` (`charPowerSeries_partition`, `charPowerSeries_blockDiag`), `09_Riesz.lean` (`charPowerSeries_blockTriangular`), `12_RieszColeman.lean` (`charPowerSeries_eq_mul_of_comm`), `13_FiniteFactor.lean` (`charPowerSeries_eq_mul_polynomial`) | no direct `sorry` | audit required | present |
| §1.7 base change | `TateFredholm/08_BaseChange.lean` (`charPowerSeries_baseChange`, `charPowerSeries_map_equiv`, `charCoeff_map`) | no direct `sorry` | audit required | present |
| §2.1 entire series | `TateFredholm/09_Riesz.lean` (`PowerSeries.evalT`, `PowerSeries.hasseDeriv`), `10_Entire.lean` (`IsEntire`, `entireSubring`, `hasseDeriv_mul`) | no direct `sorry` | audit required | present; rename `evalT` to `evalAt`, and the Taylor expansion §2.1.3 is new |
| §2.2 Euclidean division, coprimality | `TateFredholm/10_Entire.lean` (`IsEntire.exists_eq_mul_add`, `eq_mul_add_q_unique`, `eq_mul_add_r_unique`, `IsEntireCoprime`, `isEntireCoprime_iff_isCoprime_of_eq_mul_add`), `11_SlopeFactor.lean` (`norm_coeff_r_mul_pow_le_of_eq_mul_add`, `exists_isDominantPoly_of_isUnit_leadingCoeff`) | no direct `sorry` | audit required | present; the field criterion by common zeros is new |
| §2.3 good zeros | `TateFredholm/10_Entire.lean` (`IsGoodZero`, `IsGoodZero.isUnit`, `.mul`, `.of_mul`, `.of_factor`, `.exists_factor`) | no direct `sorry` | audit required | present |
| §2.4 the resolvent, `det(1 − u)` | `TateFredholm/09_Riesz.lean` (`resolventCoeff`, `norm_resolventCoeff_le`, `resolventPartialSum`, `exists_isOpLimit_resolventPartialSum`, `fredholmDet`, `fredholmDet_mul`, `fredholmDet_eq_det_of_rows`) | no direct `sorry` | audit required | present |
| §2.5 Serre's criterion, the spectrum | `TateFredholm/09_Riesz.lean` (`isUnit_one_sub_smul_iff_isUnit_evalT`, `exists_mem_ker_of_hasseDeriv_evalT`) | no direct `sorry` | audit required | present; the reading through Mathlib's `spectrum` is new |
| §3.1 the Riesz projector | `TateFredholm/09_Riesz.lean` (`exists_rieszProjection`, `exists_rieszProjection_isOpLimit`, `IsOpLimitAeval`, `ker_one_sub_smul_pow_of_rieszProjection`, `range_one_sub_smul_pow_of_rieszProjection`, `rieszProjection_unique`) | no direct `sorry` | audit required | present |
| §3.2 Serre's decomposition | `TateFredholm/09_Riesz.lean` (`exists_eigenvector_of_evalT_charPowerSeries_eq_zero`, `evalT_charPowerSeries_eq_zero_iff`, `charPowerSeries_eq_pow_mul_of_riesz`, `finrank_ker_one_sub_smul_pow`, `exists_riesz_decomposition`) | no direct `sorry` | audit required | present for discretely valued fields; restate for every complete field (convention 7) |
| §3.3 Coleman's resultant | `TateFredholm/00_Resultant.lean`, `11_Coleman.lean` (`dPoly`, `bQ`, `dSeries`, `dPoly_mul`, `dSeries_mul`, `norm_coeff_dSeries_sub_le`, `IsEntire.dSeries`, `isUnit_evalT_one_dSeries_bQ_iff`, `isGoodZero_dSeries_bQ`, `charPowerSeries_aeval`) | no direct `sorry` | audit required | present |
| §3.4 Riesz–Coleman | `TateFredholm/12_RieszColeman.lean` (`exists_rieszColemanProjection`, `IsRieszColemanProjection` and its `.finite`, `.projective`, `.rankAtStalk`, `.charPowerSeries_mul_one_sub`, `.charPowerSeries_mul`, `.ker_aeval_reverse`, `.isUnit_mul_one_sub_add`, `.eq_range_of_isTopCompl`, `isEntireCoprime_iff_isUnit_aeval_reverse`) | no direct `sorry` | audit required | present, Noetherian-free; the base-change compatibility §3.4.4 is new |
| §3.5 commuting operators | `QMF/Weight/08_HeckeAlgebra.lean` (`exists_eigensystem_of_riesz`) | no direct `sorry` | audit required | present in an application file, to be restated here |
| §4.1 the polygon of a determinant | `TateFredholm/10_NewtonSlopes.lean` (unbounded slopes via the Newton-polygons roadmap), `NewtonPolygons/OfSlopes.lean` | no direct `sorry` | audit required | partial; the slope multiset and the shear are new |
| §4.2 slopes are valuations of eigenvalues | `TateFredholm/10_NewtonSlopes.lean` (`exists_evalT_zero_of_slope`, `exists_evalT_zero_of_unitSlope`), `JacobsSlash/5_EigenSlopes.lean` (`exists_eigenvector_of_slope_charPowerSeries`) | no direct `sorry` | audit required | present for the existence at a slope; the multiset equality with multiplicities is new |
| §4.3 slope factorisations | `TateFredholm/11_SlopeFactor.lean` (`IsDominantIndex`, `IsDominantPoly`, `IsDominantFactorization`, `exists_isDominantFactorization`, `IsDominantFactorization.isEntireCoprime`), `12_RieszColeman.lean`, `LWX/05_TateRiesz.lean` (the halo instance) | no direct `sorry` | audit required | present over a ring at the norm level; the field-level decomposition through the Newton-polygons roadmap's §3.4 is new as stated |
| §4.4 bounds from the matrix | `TateFredholm/06_Slopes.lean` (`norm_charCoeff_le_pow`, `norm_charCoeff_le_pow_choose_two`, `norm_charCoeff_le_pow_block`, `norm_charCoeff_of_unit_minors`, `val_charCoeff_of_unit_minors`), `06_TwoSidedBound.lean` (`norm_minor_le_pow_sub`, `summable_minor_of_two_sided`, `norm_charCoeff_le_pow_two_sided`, `sum_comp_div_le_sum_monotone`), `QMF/Weight/08_Slopes.lean` (the polygon form) | no direct `sorry` | audit required | present; the Hodge-polygon form §4.4.1 and the general exact case §4.4.4 are new |
| §4.5 finite factors, initial segments | `TateFredholm/13_FiniteFactor.lean`, the Newton-polygons roadmap's §5.3 | no direct `sorry` | audit required | present as the split; the initial-segment reading is new here |

⚠ **Do not treat the existing file layout as prescriptive.** The source development is organised
around the applications it was written for: the model space is a synonym `c(I, R)` on a discrete
index `Ix I` rather than `C₀` on a discrete type, the operator norm is a scoped instance, the
evaluation of series is named `evalT`, Serre's decomposition is proved for discretely valued fields
only, Coleman's transform is named `dSeries`, the polygon bounds are stated over a field in one file
and over a ring in another, the block-operator machinery is split across three files by the order in
which the applications needed it, and the finite-dimensional facts of §1.1 are scattered as private
lemmas. The migration is expected to restate the theory at the generality and in the organisation
specified above — every complete field in Layer 3, the intrinsic definitions on (Pr) modules, the
decreasing-rearrangement and Hodge forms of the bounds — not to port the layout.
