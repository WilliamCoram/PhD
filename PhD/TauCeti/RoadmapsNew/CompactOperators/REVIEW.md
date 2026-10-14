# Compact operators: mathematical review and coordination

This review accompanies the [new roadmap](README.md), preserving the
[original README](../../Roadmaps/CompactOperators/README.md) and
[original prototype](../../Roadmaps/CompactOperators/Suggested.lean). It
incorporates the additions requested in
[PhD PR #24](https://github.com/WilliamCoram/PhD/pull/24), including the
contracts actually used by its two referenced Tau Ceti roadmaps. No remote PR
has been edited and no migration of production proofs is claimed.

## Terminology, field decomposition and Hodge follow-up

Rechecked on 14 October 2026 against the primary sources below. The earlier
PR/source snapshots later in this file record the original review, not a new
audit of the full consumer PRs.

**Compactoid terminology.**
[De Grande–De Kimpe, §§1.1 and 2.1](https://www.numdam.org/item/GAU_1981-1982__9_3_A5_0.pdf)
defines compactoid sets using finite absolutely convex hulls modulo each zero
neighbourhood, and compactoid maps using the image of a zero neighbourhood.
For Banach spaces one may use the unit ball. The field is complete and
nontrivially valued, without a discreteness or spherical-completeness assumption.
[Schikhof, §§2.13 and 2.15, pp. 564 and 566](https://topology.nipissingu.ca/tp/reprints/v24/tp24224.pdf)
uses the same image condition under the name compact operator and identifies
it with norm approximation by finite-rank maps.

Our row criterion agrees with this notion for `K`-linear model-space maps.
The direct proof in §0.5 identifies compactoid subsets of `c₀` with bounded
sets having uniformly small coordinate tails. However, the coefficient ring
matters: identity on `K⟨T⟩` is finite rank over that algebra, but its unit ball
is not compactoid as a `K`-space. This is not a counterexample to the field
equivalence or to a separately specified relative `A°`-span definition.
It does rule out treating relative ring compactness as compactoidness after
restriction to the ground field.

Accordingly the canonical ring/model predicate is now **`IsRowCompact`**.
The prototype and named roadmap interfaces use it throughout. Its raw
definition also requires a global coefficient bound, automatic under the
standing Tate hypotheses, to prevent unbounded real suprema from producing
a vacuous row-decay condition. The field-facing image condition is named
`HasCompactoidImage` in the specification and uses the Banach-space set
predicate specified in §0.5. No broader locally convex compactoid-set library
is proposed here. Consumers of
the former draft name `IsCompactoid`, including
`IsCompactoid.of_tendsto_opNorm_sum_pow`, should migrate to `IsRowCompact`;
any transitional alias must explicitly retain the old ring-relative meaning.
No remote consumer has been renamed by this change.

**Supplier correction after checking other roadmaps.** At PR #854 head
`aa2639b7433a688a21bc314d7e05c453188aeb4b`, neither its README nor its prototype
specifies the literature compactoid-set predicate. Its compactoid references
import our former row-decay terminology, particularly in §4.1. The earlier
claim that its §0.0 supplies compactoid subsets and countable-type factorisation
was incorrect. Section 0.5 now states its small Banach-space prerequisite
explicitly; a locally convex extension would be a future coordination proposal.
The current AdicSpacesPartIII README (PR #813 head
`d31c11188ff22bdd50a1b243b2e4bbd0f0a96cf3`) uses complete continuity and its
strict variant, without a compactoid-set definition. No compactoid terminology
was found in the checked main-branch READMEs for AdicSpaces,
AnalyticToricGeometry, PadicMeasuresIwasawaAlgebras or OperatorTheory, or in
the other local revised roadmaps. Historical local OverconvergentForms and
PadicFunctionalAnalysis occurrences use the old row-decay terminology.

**The old §3.2 is still §3.2, and the claim about its reference was wrong.**
[Serre, §7, Proposition 12, pp. 80–81](https://www.numdam.org/item/PMIHES_1962__12__69_0.pdf#page=13)
already gives the decomposition and dimension equal to the zero multiplicity
for `E=c(I)` without a discrete valuation. His standing assumptions are on
p. 69. The proof invokes §1, Remark 2, p. 71, for finite-dimensional splitting
inside `c(I)`, and that remark explicitly allows nondiscrete valuations.
The original roadmap incorrectly attributed a discrete-valuation restriction
to this argument. The restriction in §1, Proposition 1 concerns replacing
an arbitrary Banach space by `c(I)`; our potentially orthonormalisable
hypothesis supplies that model separately. The revised section retains
the kernel/image formula at the root order and the transport to a chosen model.

An independent modern reference is
[Johansson–Newton, Theorem 2.2.2, p. 10](https://arxiv.org/pdf/1604.07739v4#page=10):
specialise to `R=K` and `Q=(1−a⁻¹T)^h`. The field is Noetherian and the
leading coefficient of `Q` is a unit. Thus its hypotheses give the desired
field statement even with a dense value group. This does not discharge the
separate non-Noetherian ring extension elsewhere in the roadmap.

**Hodge ownership and terminology.** NewtonPolygons already owns the
ordered-weight polygon, convexity, `IsBelow` and the passage from coefficient
inequalities to polygon inequalities (§§0.7, 2.5). No new polygon construction
needs moving. CompactOperators supplies the principal-minor expansion and
its coefficient bounds. The finite-lattice interpretation additionally needs
invariant factors and minima over **all** minors, using linear-algebra lemmas.
[Kedlaya, numerical-analysis notes, §3 and Theorem 16](https://kskedlaya.org/18.787/numerical.pdf#page=5)
is the reference for this Hodge–Newton comparison; translate its origin to
our constant-one Fredholm convention.

Section 4.4 now distinguishes the chosen row lower polygon from the lattice
Hodge polygon. For `[[p,1],[0,p]]` they have slopes `(0,1)` and `(0,2)`,
whereas Newton has slopes `(1,1)`. The row lower bound need not have the same
endpoint, and a Fredholm polynomial alone determines neither a lattice nor
its invariant factors. Finite/zero row support and the effective comparison
domain are explicit. The exact-case examples also now give the correct
normalisations: `ϖ^(2i+1)` has slopes `2i+1` when `v(ϖ)=1`; half-integral
slopes need an element of valuation `1/2` in a suitable complete extension.

**Roadmap references.** The current README now links to
QuaternionicModularForms by its current name. Boundary-weight slope
calculations remain motivation for §4.4, with no planned halo-roadmap
dependency. The original roadmap remains a historical source; its obsolete
consumer names and the erroneous claim about Serre are not copied forward.

## Mathematical corrections

The following changes affect the statements or their proof obligations, rather
than just the organisation of the prose.

| Previous issue | Correction in the new specification |
| --- | --- |
| A bounded operator's row norms were described as a null family | Only row-compact operators have this property; bounded identity on infinite `c₀` has constant row norms one (§0.2) |
| Complete continuity was too easily identified with row decay over arbitrary rings | Preserve the finite-image convention, distinguish finitely generated range, and state the finite-submodule closedness/lifting hypothesis for the converse (§§0.1–0.2) |
| Pseudo-uniformiser data could omit positive norm | The prototype includes `0<‖ϖ‖<1`, as in the revised PFA supplier |
| Independence of a (Pr) presentation was justified by conjugacy up to a finite-rank correction on the complement | Complements need not be finite. Use bounded transition composites for compactness and the cyclic determinant identity for determinants (§§0.4, 1.5) |
| A projection onto any finite-dimensional subspace of any Banach space was asserted over every complete field | This needs extra hypotheses. Factor a compactoid operator image through a countable-type subspace, and approximate there (§0.5) |
| Both directions of the compact-operator comparison were said to fail without local compactness | Topological compactness still implies complete continuity. Identity on `ℂ_p` disproves the reverse direction (§0.5) |
| Analytic transitions were called compact for arbitrary Banach coefficient modules | Restrict the stated consequences to scalar and finite projective coefficients; constants contain the identity of an infinite-dimensional coefficient space (§0.3) |
| `diag(p^i)` had coefficients `(-1)^n p^(n(n−1)/2)` | Divide by `∏_{j=1}^n(1−p^j)`. Already the linear coefficient is `−1/(1−p)`. The old valuation formula remains correct (§1.7) |
| `diag(p^i X^i)` specialised to determinant one at `X=0` | Its index-zero eigenvalue remains one, so the determinant is `1−T` (§1.7) |
| A bounded noncompact `c₀` operator could supposedly have a compact bounded transpose | If both matrices define bounded `c₀` maps and one has row decay, the other does too. Transposed matrices with convergent minor sums need not define bounded operators (§§1.4, 4.4) |
| Finite projective summands could be treated as globally free with a rank-sized matrix | Use free retracts or local matrices. The determinant `1−eT` of identity on `eR`, `R=K×K`, has nonunit leading coefficient and variable rank (§1.5) |
| The p-adic exponential appeared among entire examples | Replace it by `Σp^(n²)T^n`; the exponential has finite radius (§2.1) |
| Entire polynomial division demanded norm-multiplicativity of every leading unit | Normalise by the unit and use monic division; the stronger norm identity is conditional on multiplicativity. This follows the revised restricted-series supplier (§2.2) |
| Good-root factorisation silently needed an extra multiplicativity hypothesis on `a⁻¹` | Unit-leading-coefficient division suffices. The root is a unit because `F(0)=1`, with PR #24's explicit inverse (§2.3) |
| Finite root order depended on a broad entire product theorem | Injectivity of Taylor translation gives finite order for a nonzero series over a field (§2.3) |
| The operator resolvent could be read as a Neumann series | Specify `V_m=Σ_{k≤m}c_k u^(m−k)`; identity on a line has `V=1` (§2.4) |
| An infinite-dimensional Coleman transform allowed arbitrary constant term | Require `B(0)=0`. The prescribed-rank padding identity exhibits the obstruction (§3.3) |
| A common majorant was used as if it proved convergence of the transform | Require a coefficient Cauchy/continuity argument first, then use the majorant for uniform Gauss tails (§3.3) |
| Coprimality of `Q,S` in `H=QS` was conflated with invertibility of `Q*(u)` on the whole space | Whole-space invertibility corresponds to coprimality of `Q,H`; factor coprimality gives invertibility on the complement (§3.4) |
| Statements in Noetherian references were presented as directly proving the full ring generality | Keep the broader row-decay targets, but label them as separate proof obligations and preserve cited source hypotheses (Layer 3 dependencies) |
| An infinite collection of slopes was called a multiset | Use locally finite multiplicities and finite cutoff lists; a Lean `Multiset` is finite (§4.1) |
| Integral coefficient valuations implied integral slopes | Slopes lie in the divisible hull of the value group; `1−pT²` has slope `1/2` twice (§4.2) |
| Root/eigenvalue claims could pass to an incomplete algebraic closure | Use a complete splitting extension (§§3.2, 4.2) |
| A dominant index was requested for every entire series, including zero | Normalised Fredholm series are nonzero. Generic preparation is assigned to restricted series, with exact distinguished hypotheses (§4.3) |
| The Weierstrass polynomial was formed by reversing `T^N` minus the remainder | The monic polynomial is `T^N` minus the remainder itself. Its reciprocal enters later when evaluating the spectral polynomial at `u` (supplier §7.2) |
| Strictly decreasing diagonal bounds alone justified exact Fredholm coefficients in the prototype | Retain row compactness, or require the bounds to tend to zero; strict decrease can have positive limit over a dense value group (§4.4 and prototype) |
| A rank-`r` finite factor always supplied `r` finite slopes | Its determinant degree can be smaller because of zero eigenvalues. To recover rank, or identify the entire summand with a finite-slope piece, require its operator to be invertible (§4.5) |
| `M_(≤0)` always counted exactly valuation-zero eigenvalues | It can contain negative slopes. Identify it with `M_(=0)` only when negative slopes are excluded, for example by `‖u‖≤1` (§4.5) |

For the projection issue, [Schikhof §2.7](https://topology.nipissingu.ca/tp/reprints/v24/tp24224.pdf)
records failure of Hahn–Banach outside the appropriate hypotheses and the
trivial dual of `ℓ∞/c₀` over nonspherically complete fields. A nonzero line
in a Banach space with trivial continuous dual cannot have a continuous
projection. The compactoid-image argument instead uses countably many finite
approximating sets; their closed linear span contains the image and is of
countable type. PFA supplies coordinates in that subspace.

For the transpose issue, split the rows of a row-compact matrix into a finite
head and a uniformly small tail. Existence of a bounded transpose says each
of the finitely many head rows tends to zero in the input index. Taking a
uniform bound over that head proves row decay for the transpose. The concrete
matrix `p^max(2i−j,0)` has bounded coefficients and null columns, but every
row has supremum one. Its transpose has non-null columns and therefore does
not define the alleged bounded map. Two-sided minor estimates remain useful,
but require a separately verified compact realisation for spectral applications.

The primary-source comparison used
[Serre](https://www.numdam.org/item/PMIHES_1962__12__69_0.pdf),
[Coleman Appendix A](https://kundudeb.github.io/1997_Coleman.pdf), and the
[corrected Johansson–Newton v4, §§2.1–2.2](https://arxiv.org/pdf/1604.07739v4).
In particular the latter's (Pr) determinant and Riesz theorems assume
Noetherian coefficients. The new draft requires proof of the stronger
row-compact model-space version, followed by retract transport; it does not
claim that deleting a hypothesis in a citation establishes that extension.

## Disposition of PR #24

The inspected PR adds targets to the old README and prototype rather than
rewriting their earlier statements. This draft integrates them into the
relevant layers and corrects the older statements at the same time.

| Request or family of interfaces | New location and decision |
| --- | --- |
| `isFiniteRank_iff_range_fg`, `IsFiniteRank.isCompletelyContinuous`; ideals, sums and closedness | CompactOperators §§0.1–0.2; retain the explicit Noetherian comparison and the broader finite-image convention |
| Banach modules normed by a lattice | CompactOperators §0.1, using the PFA gauge interface; require a Hausdorff topology for a norm, and use nonzero scalars in the infimum |
| Uniform Fredholm tails under a common null row majorant | CompactOperators §1.2, including `q=0`, empty finite set and small degrees |
| `semiringHasseDeriv`, `_zero`, `_add`, `_smul`, comparison to `hasseDeriv` | RestrictedPowerSeries §2.3; CompactOperators §2.1 consumes it for operator coefficients |
| `divByMonic`, its entirety and quotient/remainder equality; zeros and linear factors | RestrictedPowerSeries §7.2; CompactOperators §2.2 is the public supplier contract for the old references |
| `entireResultant`, remainder invariance, product/evaluation/polynomial comparisons and Bézout identity | RestrictedPowerSeries §7.2; also require the unit/coprimality criterion used in the spectral argument |
| Explicit inverse of a root when `F(0)=1` | RestrictedPowerSeries §7.2; CompactOperators §2.3 adds good orders and their operator use |
| Resolvent identities and explicit root projector | CompactOperators §§2.4–3.1; state the formulas and both projector conventions |
| `colemanDBounded`, degree-bound independence, padding, multiplicativity and comparison with `colemanD` | CompactOperators §3.3; prescribed matrix dimension is part of the input |
| Newton majorants, `colemanMajorant`, decay and coefficient estimates | CompactOperators §3.3; this is the estimate for the spectral transform, not a second Newton polygon construction |
| Entire operator evaluation, compactness for zero constant term | Generic evaluation from RestrictedPowerSeries §2.1; operator-specialised convergence and compact ideal consequence in CompactOperators §3.3 |
| `colemanDEntire`, independent two-parameter convergence, Gauss convergence, entirety, polynomial comparison and product rule | CompactOperators §3.3; an explicit Cauchy estimate is required before applying the tail majorant |
| Entire spectral mapping | CompactOperators §3.3; retain coefficients over nonreduced rings |
| Polynomial invertibility, Riesz–Coleman and projective slope pieces | CompactOperators §§3.4 and 4.3, with normalisation and supplier assumptions spelled out |

The requested semiring Hasse, monic division and resultant names are interface
names, not a requirement to install duplicate definitions in this namespace.
Compatibility aliases or comparison lemmas can preserve consumer code while
its imports change. The canonical implementation should be unique.

### Coverage of the PR's labelled checks

The README is exhaustive about required checks; the Lean file is representative.
Generic series checks are assigned to the series supplier as well as being
identified at their operator-facing interface here.

| PR check | Required location |
| --- | --- |
| `identity_on_infinite_c0` | §0.1 identity criterion |
| `decaying_diagonal` | §§0.1–0.2 |
| `nonzero_nilpotent` | §1.1 |
| `variable_rank_projective` | §1.5 |
| `hasse_characteristic_two` | §2.1; RestrictedPowerSeries §2.3 |
| `monic_quotient_quadratic` | §2.2; RestrictedPowerSeries §7.2 |
| `constant_divisor` | §2.2, `Res(1,F)=1` |
| `linear_evaluation` | §2.2, `Res(T−a,F)=F(a)` |
| `common_factor` | §2.2, positive-degree `Res(Q,Q)=0` |
| `resultant_zero_series` | §2.2; distinguish degree zero from positive degree |
| `resultant_nilpotent_linear` | §2.2, `Res(T²,a+bT)=a²` |
| `root_nonunit_constant` | §2.3, `T` at zero |
| `resolvent_not_neumann` | §2.4, identity on a line |
| `whole_series_product_nonexample` | §1.6, a specified splitting is required |
| `riesz_jordan_root` | §3.1, `u=1+N` |
| `nonzero_constant_padding` | §3.3 and prototype, ranks zero and one |
| `spectralMajorant_coordinate` | §3.3, `β_T(r)=r` |
| `spectralMajorant_zero` | §3.3, `β_0(r)=0` |
| `spectralMajorant_square` | §3.3, `β_(T²)(r)=r²` |
| `entireOperator_zero` | §3.3; require evaluations of `0` and `T` to be `0` and `u` |
| `entireOperator_nilpotent` | §3.3, evaluation on `u²=0` |
| `entireOperator_constant` | §3.3, identity on infinite `c₀` |
| `identity` | §3.3 and prototype, `D(T,F)=F` |
| `zero` | §3.3, `D(0,F)=D(B,1)=1` |
| `nilpotent` | §3.3 and prototype, `F=1−εT²` |
| `nonzero_constant` | §3.3, non-Cauchy linear coefficients of `(1−cT)^N` |
| `wrong_topology` | §3.3, powers of `T` and the unit Gauss norm |

The prose about a zero entire series and the resultant has been made precise:
for a positive-degree monic divisor the resultant is zero, correctly detecting
failure of coprimality; the divisor one gives resultant one. These cases do
not show a defect in the resultant criterion.

## Avoiding overlap with the consuming roadmaps

The refreshed [PR #854](https://github.com/TauCetiProject/TauCetiRoadmap/pull/854)
explicitly imports this operator theory in Layer 4. Its matrix convention is
the transpose of ours: its column bounds are our output-row bounds. Preserve
that conversion in comparison lemmas. Its finite-rank convention is finitely
generated range; the Noetherian comparison in §0.1 is therefore required.
Its `fredholmSeries`, `entireEval f a`, `hasseSeries` and
`polynomialSpectralResultant` correspond respectively to `charPowerSeries`,
`evalAt a f`, the supplier Hasse derivative and `colemanDBounded`.

PR #854 retains its §0.0 locally convex categories and
completed projective tensors; its scalar-extension constructions and its
distribution, manifold and cohomological applications. In its §4.14, the
monic polynomial has **unit constant coefficient**. Divide by that constant
to compare with this roadmap's constant-one convention; multiplication of
the reciprocal operator by a unit preserves invertibility. This does not
justify dropping either unit hypothesis.

The refreshed [PR #813](https://github.com/TauCetiProject/TauCetiRoadmap/pull/813)
imports the **non-strict** completely continuous predicate in R3.6. Its
affinoid lattice model, strictly completely continuous maps, submodule
restriction and coherent cohomology remain there. CompactOperators supplies
the approximation predicate, its elementary calculus and the gauge-norm
comparison. No affinoid presentation or cohomology construction is added here.

The new [RestrictedPowerSeries README](../RestrictedPowerSeries/README.md)
has been extended narrowly at §§2.3 and 7.2 to make the relocated generic
targets explicit, and its coordination record notes the handoff. The PFA
ownership link now points to this new draft. NewtonPolygons already supplies
the scalar factorisation and slope dictionaries; its implementation is not
duplicated here. These are local drafting decisions. External supplier tables
and Lean imports still require coordinated changes, rather than treating the
proposed redistribution as already accepted upstream.

## Format, snapshots and implementation sources

The organisation follows the previously inspected merged
[OperatorTheory #126](https://github.com/TauCetiProject/TauCetiRoadmap/pull/126)
and [GeometricMeasureTheory #828](https://github.com/TauCetiProject/TauCetiRoadmap/pull/828):
a definitive mathematical README, explicit local hypotheses and carrier
choices, dependencies and ownership, required checks and representative
Lean interfaces. The
[contribution guidelines](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/CONTRIBUTING.md)
also call for a separate roadmap directory, topic metadata and honest
attribution. `metadata.toml` uses `math.FA`. Upstream submission should touch
only this roadmap's directory; the supplier amendments need their own
coordinated submissions.

| Source | Inspected revision |
| --- | --- |
| Local PhD baseline | `eefb3d91f34b27d0bc7822140fa85fecae029884` |
| PhD PR #24, open | `5e436da48df001e74206c11119a13f13c423a7fa` |
| TauCetiRoadmap PR #854, open | `84b4aff9523485ea44083ef2f20c4a39fc242270` |
| TauCetiRoadmap PR #813, open | `450961f63d731252ad91fe27764ef08dc90962e7` |
| Merged roadmap comparison snapshot | `97199a4ed890b401e523e38ed11097350518302c` |
| Local Mathlib | `bbc4475e9e8fd25fbc8e26d636dd8b37be8f105a` |
| Lean toolchain | `leanprover/lean4:v4.33.0-rc1` |

Both consumer PRs were read at their current heads on 13 October 2026.
PR #813 has moved since the preceding PFA review; the older review records
its own snapshot and has not been silently repinned. PR #24's diff changes
two files and adds the requested interfaces and checks; no comments were
returned by the inspected PR-comments endpoint.

The independent `PhD/Main/TateFredholm` directory contains candidate sources:
`02_Compact.lean`, `04_Matrix.lean`, `05_Noetherian.lean`, `05_Fredholm.lean`,
`06_Pr.lean`, `06_BlockOp.lean`, `06_TwoSidedBound.lean`, `07_Conjugation.lean`,
`08_BaseChange.lean`, `09_Riesz.lean`, `10_Entire.lean`, `11_Coleman.lean`,
`11_SlopeFactor.lean`, `12_RieszColeman.lean` and `13_FiniteFactor.lean`.
Their layout is provenance, not the proposed destination layout. In particular,
`10_Entire` and the scalar preparation portions should feed the series supplier.
Representative source headers and declarations were inspected, but no complete
transitive axiom audit was performed. The old status table's clean-source
claims are not carried over as a certification of these new statements.

## Validation and attribution

The mathematical review checked the boundary examples above, the PR additions,
the two consumer contracts and the primary-source hypotheses. The Lean prototype
uses mathematical definition bodies with no admitted instances. Its deliberately
admitted theorem targets check types only; production ports must prove them and
audit the capstone axioms. The package does not modify production import chains.

Validation repeated on 14 October 2026 at the recorded pin: `lake env lean
PhD/TauCeti/RoadmapsNew/CompactOperators/Suggested.lean` succeeded with
**21 intentional `sorry` warnings and no errors**. The additional target is the
field comparison between row compactness and complete continuity. All 18
definitions have bodies; there are no standalone instance declarations.
The raw row predicate now includes the boundedness guard described above.
The prototype imports only the specific Mathlib files it uses. Local links,
terminology and whitespace were checked. The follow-up changes only this
package's README, prototype and review; the original roadmap and other
roadmaps are preserved. This is not a
transitive proof audit of the candidate `PhD/Main` sources.

Draft and review prepared with OpenAI Codex assistance. No human or maintainer
approval is claimed. A submission should identify the actual model used and the
human review that has taken place.
