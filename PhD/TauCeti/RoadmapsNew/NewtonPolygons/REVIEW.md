# Newton polygons: revision and mathematical review

Prepared on 13 October 2026 from the [previous roadmap](../../Roadmaps/NewtonPolygons/README.md),
its [Lean prototype](../../Roadmaps/NewtonPolygons/Suggested.lean), the new
[RestrictedPowerSeries roadmap](../RestrictedPowerSeries/README.md), and
[WilliamCoram/PhD PR #22](https://github.com/WilliamCoram/PhD/pull/22).
The revised mathematical specification is [README.md](README.md).
Updated on 14 October 2026 to incorporate the height/slope-data, `ConvexOn`
and Hodge-comparison design discussion below.

This is an author-side, AI-assisted review and redraft. It does not claim
external approval, an audit of every candidate proof, or agreement from other
roadmap authors on changed ownership.

## Incorporation of PR #22

The complete two-file diff of PR #22 was read. It was open at inspection, at
head `7830230e834b85a75f763077e856864bde211112`, based on
`eefb3d91f34b27d0bc7822140fa85fecae029884`.

| Contribution | Location and treatment |
| --- | --- |
| `exists_pow_mul_distinguished_mul_unit` | README §6.3 and the same named theorem in `Suggested.lean`; the valuation-ring carrier, explicit maximal-ideal adic completeness and `π^μ · u · P` order are preserved |
| No finite-residue-field hypothesis | Preserved explicitly; an abstract complete-DVR supplier also supports the coefficient ring used by PadicMeasuresIwasawaAlgebras |
| Minimum coefficient valuation and least attaining index | Real `mu` and `lambda` definitions using Mathlib's native DVR valuation, plus a strengthened preparation signature fixing the exponent and polynomial degree |
| Reducibility of `X²+2X+2` over `ℤ₂[i]` | README §6.5 and a matching valuation-ring Lean example; monicity, degree one and the change of valuation normalisation are required checks |
| Comparison with normed distinguishedness | Corrected in §6.4; the old unqualified equivalence at radius one is false |

The exact PR theorem is a corollary of the stronger abstract-DVR target. Its
short Lean proof only reorganises witnesses and still depends on an admitted
supplier theorem; it is not a completed preparation implementation.

NewtonPolygons remains the supplier of this normalised formal-preparation
contract for [PadicMeasuresIwasawaAlgebras §4.3, PR #780](https://github.com/TauCetiProject/TauCetiRoadmap/pull/780).
General normed series and Banach-ring preparation belong to RestrictedPowerSeries.
Mathlib's existing ideal-adic preparation is used after removing the common
uniformiser power. These allocations preserve the intent of #22.

## Generic geometry and Hodge comparisons

The 14 October revision preserves the greatest convex minorant and separates
its construction from the polygon object. The
[Zulip structural-interface discussion](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Newton.20polygons/with/585588265)
asks that polygons constructed in different ways share the same theory;
[the slope-and-length proposal](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Newton.20polygons/with/585688715)
motivates the second presentation. Both requirements are retained without
bringing F-isocrystal theory into scope.

| Design question | Required interface and location |
| --- | --- |
| Generic geometry versus arithmetic construction | `IsLowerConvexEnvelope` and `lowerConvexEnvelope` in §0.1; polynomial/power-series Newton wrappers in §2.1; `ConvexPolygon` bundles heights and convexity only |
| Slopes and lengths | §0.6 supplies anchored finite and infinite unit-slope data, compressed positive lengths, normalisation and round trips; rational finite data is compatible with the real geometry |
| Convex sequences and `ConvexOn` | Retain `IsConvexSeq` as a predicate on functions; §0.1 requires equivalence with canonical piecewise-affine interpolation on the real finite-domain interval |
| Polygon order | §0.7 gives pointwise `IsBelow`, interpolation compatibility and partial-sum dominance; same-domain/endpoint conditions are separate |
| Hodge lower bounds | §§0.7 and 2.5 construct polygons from specified ordered weights and apply explicit coefficient bounds; CompactOperators §4.4 retains matrix and determinant estimates |

The local implementation already offers parts of these bridges:

- [`ConvexSeq.lean`](../../Code/NewtonPolygons/ConvexSeq.lean) has
  `IsConvexSeq.exists_convexOn` and `isConvexSeq_of_convexOn` for everywhere-finite
  sequences on `ℕ`. The new contract additionally identifies canonical
  interpolation and handles finite domains and shifted half-lines.
- [`OfSlopes.lean`](../../../Main/NewtonPolygons/OfSlopes.lean) constructs a
  polygon from monotone real slopes and identifies its heights with partial
  sums. Finite data, compressed presentations and the reverse conversions are
  explicit roadmap targets.
- [`Basic.lean`](../../../Main/ForMathlib/NumberTheory/NewtonPolygon/Basic.lean)
  supplies the old `IsBelow`. Its extended values and segment records differ
  from this roadmap's outside-`∞` heights, so reuse requires comparison of
  proper domains and honest edges, not equality of arbitrary legacy records.

The mathematical distinctions are recorded next to their uses. Slopes without
an anchor lose translations; raw segment subdivisions prevent literal data
round trips; finite lists do not describe every infinite polygon; and
coefficient contact with a ray is not intrinsic to the geometry. Rational data
is retained for finite arithmetic applications without ruling out irrational
limiting slopes.

A follow-up edge-case audit compared §0.6 with every slope/length/support field
of the older structural definition. Unit widths remove zero-length edge cases;
`Fin d` removes out-of-support slope entries; `d=0` represents a singleton with
no slopes; and infinite unit sequences represent rays without extended lengths.
The generic prototype was tightened from `Preorder Γ` to an ordered additive
group, matching the intended finite-valued slope coefficients. The compressed
presentation explicitly requires positivity of each finite length. The text
and prototype now name the finite/infinite conversions from admissible envelopes
and the fixed-point identity for the envelope of reconstructed heights. Empty,
vertical and genuinely two-sided cases are distinguished; recovery of original
coefficient heights is not asserted.

`ConvexOn` includes convexity of its domain, so it cannot simply be applied to
the natural numbers embedded in the reals. Existence of some convex extension
also does not pick out the polygon between integer points: `x²` differs from
the linear interpolation of `n²`. These are reasons for the canonical bridge,
not reasons to introduce a new sequence carrier.

The Hodge comparison requires additional data. Nondecreasing weights define a
convex cumulative-sum function, and bounds on coefficient valuations then give
`H ≤ NP` by greatestness. A polynomial alone does not recover the usual lattice
Hodge polygon: `diag(p,p)` and `[[p,1],[0,p]]` have the same characteristic and
Fredholm polynomials but Hodge slopes `(1,1)` and `(0,2)`. The finite-lattice
interpretation follows the minor description in
[Kedlaya's numerical notes, §3](https://kskedlaya.org/18.787/numerical.pdf).
The normalisation uses `det(1-TU)`, as distinguished from `det(TI-U)` in
[the Zulip convention discussion](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Newton.20polygons/with/585690331).
Full-rank invariant-factor comparisons have equal endpoints; general row-bound
comparisons need not. Singular operators require their actual finite domain.

A companion clarification in CompactOperators §4.4 points to the shared
ordered-weight and comparison interface. No determinant proof, invariant-factor
implementation or operator compactness result is moved into NewtonPolygons.
The #22 preparation contract and all existing analytic layers are preserved.

## Mathematical findings and corrections

1. **Boundary faces are not boundary counts.** The old Gauss-face prototype
   used a natural-number `faceRight` at every restricted radius. Its ray
   discussion also called the last active coefficient a geometric vertex.
   Consider
   `F=1+Σ_{n≥1}p^⌈√n⌉X^n` and
   `G=1+X+Σ_{n≥2}p^⌈√n⌉X^n`.
   Both are unit-radius restricted with the same horizontal-ray polygon.
   Their greatest active indices are zero and one, so their boundary zero
   counts over `ℂ_p` differ. The revision uses coefficient extrema at every
   restricted radius and geometric face endpoints at interior radii.
   [Lazard §1, (1.11)](https://www.numdam.org/item/PMIHES_1962__14__47_0.pdf)
   explicitly distinguishes these endpoint data from the hull.

2. **Exact counts need splitting.** A complete extension need not contain
   every root: `X²-p` has no roots in `ℚ_p`. The new §4.3 gives exact counts
   in splitting complete extensions and bounds otherwise. The polynomial
   root theorem only needs a splitting normed extension.

3. **Purity allows collinear interior points.** The old §2.4 required equality
   only at endpoints and strict inequality in between. The pure polynomial
   `1+pX+p²X²` disproves that. A break is a change of slope after a segment,
   not the absence of additional coefficients on it.

4. **Finitely many pieces do not force rational ray slopes.** The one-ray
   hull of `⌈n√2⌉` has irrational slope. Rationality now applies to bounded
   segments with actual integral endpoint coefficients, including every
   polynomial segment.

5. **Some-radius convergence does not bound all slopes.** The old §2.2.4
   contradicted the entire example `Σp^(n²)X^n`. The asymptotic-slope theorem
   now treats infinite support, finite support and vertical sequences separately.

6. **The primary radius is intrinsic.** The old radius was a supremum over
   convergence points in a chosen field. For `Σp^⌈n/2⌉X^n`, that supremum in
   `ℚ_p` is one, whereas the coefficient radius is `√p`. The revision makes
   restricted radii primary and retains the pointwise quantity as a comparison
   with an explicit norm-density hypothesis.

7. **Formal and normed preparation degrees differ.** For `p+X+X²`, the first
   unit coefficient is at one and the last at two. Formal preparation has
   degree one; closed-unit-disc preparation has degree two. The comparison
   now holds at radii below one sufficiently close to one, with extra
   conditions for agreement at one. This fixes the old §6.3.1 while keeping
   the preparation target requested by PR #22.

8. **Formal `μ,λ` additivity needs an algebraic proof.** General `O⟦X⟧`
   series need not be restricted at one or entire. The new proof route uses
   coefficient content and order in the residue-field series domain, not
   the global analytic polygon product theorem.

9. **Reversal changes the sign.** The reverse of a monic Eisenstein polynomial
   has slope `+1/d`, not `-1/d`. Dividing by its constant coefficient is the
   operation that preserves the slope while making the constant term one.

10. **The sum bound was false.** For summands `1` and `X²`, the pointwise
    minimum of their polygons is infinite at index one, but the sum's
    polygon is finite there. The new bound uses a common convex minorant.
    A strict Gauss-norm perturbation supplies a valid stability theorem.

11. **Factor uniqueness needs analytic conditions.** In `(1-X)(1-pX)`,
    either factor has degree one and constant term one. At radius one,
    requiring a restricted unit cofactor selects `1-X`. The new uniqueness
    signature includes the full conditions; slope agreement stops strictly
    before the polynomial endpoint.

12. **The old dependency route exceeded the product theorem's hypotheses.**
    It proposed obtaining Gauss multiplicativity for arbitrary restricted
    series from a global polygon product theorem requiring entire factors.
    Gauss multiplicativity is now an existing supplier theorem. Active
    indices add at every common restricted radius; global polygons multiply
    for polynomials and entire series. `(1-X)ΣX^n=1` remains the check
    against an unjustified global extension.

13. **Examples named the wrong factorisation behaviour.** The old Layer 6
    called `1+pX+p³X²` irreducible, although its slopes `1,2` yield two
    linear factors over `ℚ_p`. Conversely `1-X²/p` is irreducible there
    and only splits after an appropriate extension. Both are corrected.

14. **The cited orientation was wrong.** The specified
    [Kedlaya notes](https://kskedlaya.org/18.787/newton-poly.pdf) plot
    `(-i,v(a_i))`. The reference now translates the sign and uses the
    untwisted specialisation explicitly.

15. **Prototype edge cases needed repair.** The old multiset/face theorem
    allowed an arbitrary truncation length, endpoint sentinels could enter
    vertex tests, zero-root multiplicities were not consistently separated,
    and degree-zero division used `natDegree remainder < 0`. The new
    interfaces use finite edges, actual order-to-degree ranges, nonzero-root
    multisets and explicit finite-face/active-index specifications. Division
    itself is supplied by RestrictedPowerSeries, with `Polynomial.degree`.

The vertex walk also handles an unbounded set of slope minimisers, and
collinear contacts are distinguished from vertices. Height rescaling is
written as the explicit equation `w'=(log b/log b')w`. General finite-extension
discreteness has a value-group-index proof target, with a comparison to the
local-field API, rather than an unsupported appeal to a narrower supplier.

## Format and dependency changes

The structure follows the inspected merged
[OperatorTheory #126](https://github.com/TauCetiProject/TauCetiRoadmap/pull/126),
[GeometricMeasureTheory #828](https://github.com/TauCetiProject/TauCetiRoadmap/pull/828),
[AnalyticToricGeometry #281](https://github.com/TauCetiProject/TauCetiRoadmap/pull/281)
and [AdicSpaces #80](https://github.com/TauCetiProject/TauCetiRoadmap/pull/80):
a timeless specification, explicit conventions and suppliers, required layers
with checks, and completion criteria. Status and correction history stay here.

RestrictedPowerSeries supplies the analytic algebra; NewtonPolygons supplies
its slope, root and convergence interpretations and the #22 preparation
contract. LocalFieldsRamification keeps its canonical local-field arithmetic
API. Polynomial products and root multisets precede analytic factorisation,
and formal preparation is usable independently of entire-series theory.

The companion RestrictedPowerSeries boundary records the #22 formal supplier.
These are local draft allocations, not accepted upstream ownership changes.

## Source and implementation record

- PhD base: `eefb3d91f34b27d0bc7822140fa85fecae029884`.
- Local Mathlib: `bbc4475e9e8fd25fbc8e26d636dd8b37be8f105a`;
  Lean: `leanprover/lean4:v4.33.0-rc1`.
- Tau Ceti series foundations: `82808df9eb88cb87958a5adefb955796123eb38e`,
  as surveyed in [RestrictedPowerSeries/COORDINATION.md](../RestrictedPowerSeries/COORDINATION.md).
- TauCetiRoadmap: `97199a4ed890b401e523e38ed11097350518302c`, including
  LocalFieldsRamification's Layer 0 inspected for this revision.
- PhD PR #22: head `7830230e834b85a75f763077e856864bde211112`, open at inspection.
- Mathlib [#43578](https://github.com/leanprover-community/mathlib4/pull/43578)
  and [#43580](https://github.com/leanprover-community/mathlib4/pull/43580)
  were open at inspection. Their additive-valuation interfaces inform the
  design; the roadmap does not require waiting for their merge.

The source survey checked declaration shapes and selected proof status, not
all transitive dependencies. In particular, local `Coeff/Pure.lean` and
`Coeff/SupportValue.lean` contain admitted targets. The old historical
implementation table is not carried over as a current proof-status guarantee.

The new prototype imports only Mathlib, has real definition bodies and installs
no admitted instances. Compilation checks elaboration, not the truth of its
admitted theorem targets. The original roadmap and PR branch are not modified
by this local replacement.

Validation on 14 October 2026 with the pinned local toolchain:
`lake env lean PhD/TauCeti/RoadmapsNew/NewtonPolygons/Suggested.lean`
succeeded with 23 intentional `sorry` warnings and no errors. This includes the
finite/infinite slope data, canonical interpolation targets, polygon order and
coefficient-bound comparison interfaces, the explicit envelope conversion
corollaries, together with the exact preparation
interface requested by PR #22 and its abstract-DVR supplier. The short order and
comparison proofs use the admitted geometric supplier targets; compilation does
not constitute their mathematical implementation. Local links and section
anchors were checked, and the existing valuation, product, root, analytic and
PR #22 preparation sections were compared with the pre-edit files.
The prototype still needs elaboration against the destination roadmap
repository's toolchain when ported.

Any upstream submission should disclose the OpenAI Codex assistance and actual
model used, report the human review actually performed and coordinate supplier
changes with the affected authors. The upstream one-directory-per-roadmap-PR
rule calls for companion ownership revisions in separate PRs. The package
includes `metadata.toml` with topic `math.NT`.
