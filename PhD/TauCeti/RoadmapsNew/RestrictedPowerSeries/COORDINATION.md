# Restricted power series: coordination and drafting record

This is a **local proposal**, prepared on 13 October 2026. The mathematical
specification is [README.md](README.md). The ownership changes below have not
been agreed with the authors or reviewers of the other roadmaps. The subsequent
[NewtonPolygons revision](../NewtonPolygons/README.md) adopts the shared supplier
and incorporates PhD PR #22; its formal-preparation boundary is reflected below.
The original roadmaps remain unchanged.

## Models used for the draft

The structure follows the [contribution guidelines](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/CONTRIBUTING.md)
and the [roadmap-writing checklist](https://github.com/TauCetiProject/TauCetiRoadmap#writing-a-roadmap):
state a reusable mathematical library, reach existing foundations, pin conventions,
give explicit suppliers for prerequisites, keep the README definitive, and use
real definitions with honest admitted target proofs in the Lean prototype.

The following merged roadmaps informed the presentation and scope.

| Merged example | Feature adopted here |
| --- | --- |
| [OperatorTheory, PR #126](https://github.com/TauCetiProject/TauCetiRoadmap/pull/126), merged 8 October 2026 | A common library shared by several consumers, explicit ownership, and dependency-minimal pieces instead of separate application-specific definitions |
| [GeometricMeasureTheory, PR #828](https://github.com/TauCetiProject/TauCetiRoadmap/pull/828), merged 13 October 2026 | A supplier roadmap with pinned conventions, an existing-library floor, required milestones and concrete checks, and a clear boundary with its consumers |
| [AnalyticToricGeometry, PR #281](https://github.com/TauCetiProject/TauCetiRoadmap/pull/281), merged 2 September 2026 | One native mathematical representation, complete prerequisite chains, and explicit completion criteria |
| [AdicSpaces, PR #80](https://github.com/TauCetiProject/TauCetiRoadmap/pull/80), merged 7 August 2026 | The actual topological and weighted series generality to preserve, including non-Tate coefficient rings and module-valued series |

The resulting draft is deliberately substantial: it supplies a common coefficient
and series library, rather than collecting theorems under a new title while leaving
each application to construct its own carrier. Its layers can be implemented
independently once their stated prerequisites are available.

## Proposed ownership changes

The table describes **proposed edits to coordinate**, not the current upstream
ownership. An accepted roadmap remains authoritative until it is revised.

| Existing roadmap or proposal | Targets supplied by the new roadmap | Targets staying with the original roadmap |
| --- | --- | --- |
| [Accepted AdicSpaces](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/AdicSpaces/README.md), §§0.4–0.5 | The restricted and subset-weighted series construction, module series, universal properties, iteration and quotient interfaces, field Weierstrass theory and Tate noetherianity; replaced by references to Layers 0–6 | General boundedness and completion, topological localisation, Huber pairs and strong noetherianness as a property, valuation spectra and geometry |
| [Local NewtonPolygons](../../Roadmaps/NewtonPolygons/README.md), especially §3.1 and §5.4; see the [revised proposal](../NewtonPolygons/README.md) | Arbitrary-radius normed division/preparation, dominant-coefficient and Gauss-norm APIs, and Strassmann via §§2.4 and 4 | Newton functions, polygons, slopes, polygon-specific factorisation and root-counting consequences, and normalised formal DVR preparation for Iwasawa theory |
| [Local PadicFunctionalAnalysis](../../Roadmaps/PadicFunctionalAnalysis/README.md), especially §4.1 | Restricted coefficient modules, the `c₀` comparison, radius norms, evaluation, substitution and the specified function-realisation interface | General nonarchimedean Banach-space/module theory, bases, bounded maps, open mapping and duality |
| [Local CompactOperators](../../Roadmaps/CompactOperators/README.md), especially §§0.3 and 2.1–2.2 | Radius-restriction maps and bounds; entire-series algebra, Hasse derivatives and entire polynomial division | Compactness, determinants, Fredholm resolvents, spectral transforms, Riesz and slope theory |
| [New RigidAnalyticGeometry proposal](../RigidAnalyticGeometry/README.md), §§0.1 and 1.5; see its [review of the revised roadmap and PR #25](../RigidAnalyticGeometry/REVIEW.md) | Tate coefficients, norms, reduction, maximum modulus, Weierstrass theory, distinguished coordinates, finite quotients, noetherian/factorial/Jacobson/dimension results, and Tate finite-module strictness | Weak stability and Japanese applications, general affinoids, affinoid spectral theory, the converse strict-affinoid radius criterion, localisation and classical comparisons; geometric ownership requires the handoffs recorded in that review |
| [Local QuaternionicModularForms](../QuaternionicModularForms/README.md) | Bounded analytic substitutions, re-expansions, differentiation and common radius conditions | Quaternionic coefficient actions, automorphy factors, Hecke actions and classicality |
| [AdicSpaces Part II, PR #817](https://github.com/TauCetiProject/TauCetiRoadmap/pull/817), §R0.9 and the series inputs to §R0.3 | The Tate-algebra portion of classical rigid algebra, supplied by Layer 5; coefficient maps and universal properties supplied by Layer 6 | General classical affinoid algebra, morphisms and analytification; `completed-tensor-restricted-power-series` stays in §R0.3, with this roadmap supplying its series input |
| [AdicSpaces Part III, PR #813](https://github.com/TauCetiProject/TauCetiRoadmap/pull/813), §F0.1 | `restricted-power-series-adic` and its polynomial reductions/noetherian consequence, supplied by §6.3 | The general `adic-completion-noetherian` theorem supplies §6.3; formal schemes, models, coherent sheaves and the geometric uses of complete continuity stay there |
| [AdicSpaces Part IV, PR #815](https://github.com/TauCetiProject/TauCetiRoadmap/pull/815), §F1.1 | Positive-radius Tate algebra, radius inclusions, the native overconvergent series algebra `W_n` and its unit-Gauss-norm completion, supplied by §§1.2, 5.4 and 7.3 | General dagger quotients and fringe topology, weak completions, dagger geometry and cohomology |
| [LocallyAnalyticDistributions, PR #854](https://github.com/TauCetiProject/TauCetiRoadmap/pull/854), Layers 0 and 4 | The restricted-series disc model, its elementary analytic maps, entire-series algebra and general Banach-ring division | Locally analytic function spaces, distributions, functional analysis, Fredholm theory, growth conditions and character spaces |
| [PadicMeasuresIwasawaAlgebras, PR #780](https://github.com/TauCetiProject/TauCetiRoadmap/pull/780) | A shared language for radius conditions and evaluating bounded-coefficient series strictly inside the unit disc | The formal ring `O⟦T⟧`, completed group algebras, measures and Iwasawa invariants; normalised formal DVR preparation is supplied by [NewtonPolygons §6.3](../NewtonPolygons/README.md#63-the-preparation-contract-for-iwasawa-theory), as requested by [PhD PR #22](https://github.com/WilliamCoram/PhD/pull/22), using Mathlib's ideal-adic preparation |

The accepted AdicSpaces roadmap is the most important coordination point: this
proposal would relocate substantial ownership already assigned there. The intended
change is to make those sections consumers of one shared supplier, preserving
their full generality. It is not to remove the existing implementation or fork it.

The local NewtonPolygons roadmap's missing-prerequisite description for Gauss
multiplicativity should be updated: that theorem now exists upstream. Likewise,
references to AdicSpaces §0.5 should not be treated as supplying Martin's full
Banach-ring theorem; the accepted field theorem is weaker. The new §4 supplies
the stronger result explicitly.

The subsequent [p-adic functional-analysis review](../PadicFunctionalAnalysis/REVIEW.md)
checks the broader allocation against [PhD PR #23](https://github.com/WilliamCoram/PhD/pull/23)
and refreshed consumer heads. Its new roadmap supplies the shared Banach-module
theory, analytic stages, bounded and algebraic locally analytic Amice transforms,
and quantitative estimates. PR #854 retains the distribution topologies,
completed tensor construction and geometric Mellin theory; CompactOperators
retains the operator-theoretic conclusions. The review records the precise
handoffs and dependency order. This clarifies the earlier survey below without
changing its historical snapshot identifiers.

The subsequent [compact-operator review](../CompactOperators/REVIEW.md) incorporates
[PhD PR #24](https://github.com/WilliamCoram/PhD/pull/24) and rechecks PRs #854
and #813 at the heads recorded there. RestrictedPowerSeries §§2.3 and 7.2 now
explicitly own the semiring Hasse API, explicit monic entire quotient, generic
monic entire resultant and its Bézout/unit criterion, the inverse of a root of
a normalised entire series, and the normalised entire preparation corollary.
CompactOperators consumes these, retaining Coleman's spectral transform,
resolvents and projectors. PR #854 still cites the older CompactOperators
locations; the supplier links and compatibility names must be updated in a
coordinated change. No external ownership agreement is claimed. The original
survey rows and snapshots above remain historical records.

## Integration with existing code

At the surveyed Tau Ceti commit, several major foundations already exist.
Implementation work should distinguish reuse from new generality.

| Area | Existing upstream floor | Work specified by this roadmap |
| --- | --- | --- |
| Positive polyradii | `MvPowerSeries/TateAlgebra/Basic.lean` gives the native normed construction, completeness, density, norm attainment and multiplicativity with a multiplicative coefficient norm | Extend and connect the API, including module-valued coefficients, radius maps, rescaling and all-polyradius iteration |
| Evaluation | `MvPowerSeries/TateAlgebra/Eval.lean` gives finite-variable evaluation at arbitrary positive polyradii with a contractive coefficient map | Bounded-map variants, analytic substitution with nonzero constants, translation, derivatives and compatibility results |
| Substitution and iteration | `Subst.lean` covers unit-ball polynomial substitutions with zero constant term; `Iterate.lean` covers unit radii | General analytic substitution and isometric iteration at arbitrary positive polyradii |
| Weierstrass theory | `PowerSeries/Weierstrass/Division.lean` and `Preparation.lean` work at arbitrary positive radius with `NormMulClass` coefficients | Replace the global multiplicativity hypothesis by multiplicativity of the distinguished coefficient, and recover the old statements by comparison |
| Topological series | `Huber/Restricted/` and `Huber/WeightedRestrictedSeries/` already give carriers, topology and many maps | Preserve their weighted generality, extend comparisons and connect the normed, completed and adic APIs |
| Normed/topological comparison | `Huber/Restricted/GaussNorm.lean` provides unit-radius ring, algebra and completed comparisons | Coherence with coefficients, evaluation, iteration and the extended structure theory; state extra hypotheses for weighted comparisons |

The local implementation under
`PhD/TauCeti/Code/RigidAnalyticGeometry/Restricted/` is a source for the
multiplicative-unit, Banach-ring Weierstrass and polyradius extensions. The
neighbouring `TateAlgebra/` files are sources for reduction, distinguished charts,
finite quotients, Rückert theory and strict closedness. Audit these declarations
against current upstream definitions and preserve their attribution when porting.

The fuller `PhD/Main/ForMathlib/` development is additional provenance. Keep the
repository's independent `PhD/Main/` and `PhD/TauCeti/` import chains separate.

## Snapshots used

These pins make the code and ownership comparison reproducible; they are not
mathematical hypotheses of the roadmap.

| Repository | Commit |
| --- | --- |
| Local PhD HEAD | `eefb3d91f34b27d0bc7822140fa85fecae029884` |
| Local Mathlib dependency | `bbc4475e9e8fd25fbc8e26d636dd8b37be8f105a` |
| [TauCeti](https://github.com/TauCetiProject/TauCeti/tree/82808df9eb88cb87958a5adefb955796123eb38e) | `82808df9eb88cb87958a5adefb955796123eb38e` |
| [TauCetiRoadmap](https://github.com/TauCetiProject/TauCetiRoadmap/tree/97199a4ed890b401e523e38ed11097350518302c) | `97199a4ed890b401e523e38ed11097350518302c` |

Open roadmap heads inspected on 13 October 2026:

| PR | Status at inspection | Head commit |
| --- | --- | --- |
| #817 | Open, draft | `b45e54cbcf0c012d7f78b2cf62a716a69fb5ce66` |
| #813 | Open, draft | `ae824af115b07053c757e5cf5e48f7e50f0ea6af` |
| #815 | Open, draft | `059fd1582e0ebc00212a3a5fb8447127a6c76b7b` |
| #854 | Open | `513dd5071d665c4b75a66fbdff8492865d021dc3` |
| #780 | Open | `750be03d1c6132f7702fe910bbbd881172b9035d` |

The local toolchain is `leanprover/lean4:v4.33.0-rc1`. The pinned Mathlib has
restrictedness predicates and the multivariate restricted subring but predates
the named restricted-series type now present on Mathlib master. The PhD project
does not have a Tau Ceti dependency. For that reason `Suggested.lean` imports only
Mathlib and expresses its representative interfaces on native series/subrings.
Its compatibility scaffolding is not a proposed second production API.

Validation on this snapshot: `lake env lean
PhD/TauCeti/RoadmapsNew/RestrictedPowerSeries/Suggested.lean` succeeded, with
13 intentional `sorry` warnings for theorem targets and no errors. Every
definition has a body, and no admitted instance is installed. This checks
elaboration against the local Mathlib pin; the file still needs checking against
the destination roadmap repository's toolchain when it is ported.

## Review and submission

Before submission, settle the ownership table with the affected roadmap authors
and reviewers, then replace the relocated statements with precise dependency
references in coordinated changes. The new roadmap should not be presented as
already resolving overlap while the existing ownership remains unchanged.

The upstream contribution policy requires each roadmap PR to touch only its own
directory. Submit this package under `TauCetiRoadmap/RestrictedPowerSeries/` and
make coordinated revisions to other roadmaps in their own PRs. The topic metadata
is `math.AG`; do not hand-edit generated roadmap listings or root import lists.
This coordination record can accompany the local review or provide the PR
description; it is not a replacement for the mathematical README.

The draft and Lean prototypes were prepared with OpenAI Codex assistance. Any
submission should identify that assistance and the actual model used, and describe
the human review that has actually taken place. Human review should assess the
scope, ownership and mathematical statements; elaboration of `sorry`-backed Lean
signatures does not establish their truth. No external review or maintainer
agreement is claimed by this drafting record.
