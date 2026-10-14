# Quaternionic modular forms: review and coordination

This review accompanies the [new roadmap](README.md). It preserves the
[original roadmap](../../Roadmaps/OverconvergentForms/README.md) and
[prototype](../../Roadmaps/OverconvergentForms/Suggested.lean), incorporates
[PhD PR #21](https://github.com/WilliamCoram/PhD/pull/21), and checks its actual
consumer in [Tau Ceti PR #792](https://github.com/TauCetiProject/TauCetiRoadmap/pull/792).
The new title is **Quaternionic modular forms** because the roadmap develops
classical spaces, quaternionic arithmetic and Hecke operators as well as
overconvergent spaces. It does not cover general overconvergent automorphic
forms for arbitrary reductive groups.

## Character convention and motivation follow-up

Rechecked on 14 October 2026 against Jacobs §1.5, Definition 1.27 and
equation (1.5.13), and Buzzard's *Eigenvarieties* §§8–11. Jacobs uses a single
character `κ_J` with factor `κ_J(cz+d)/(cz+d)²`. The existing automorphy
character `n` is therefore `κ_J·x⁻²`, with trivial determinant twist.
Section 1.1 now supplies that single-character entry point and its exact
comparison, while retaining a separately specified determinant twist for the
general theory. The Hamilton family's degree parameter is explicitly two
less than its Jacobs classical-weight label.

The two general characters can be bundled into one character of a product
group, as in Buzzard. This preserves the independent determinant data; it is
not equivalent to discarding the second factor. The scalar-unit formula
`n(u)ν₀(u)²` explains its role in the central-unit condition and in nonparallel
algebraic weights. The single-character and product-character constructors
are README targets; this update adds no new admitted Lean declarations.

Spectral-halo geometry is no longer listed as a planned downstream project.
Boundary slope phenomena remain contextual motivation. The annular coefficient
ring is still an actual PFA §5.6 target, so its weight action and specialisation
example remain here under that name, independently of any halo roadmap.

## Mathematical corrections

| Issue in the previous specification or prototype | New statement and reason |
| --- | --- |
| Reduced norm was described using the determinant of left multiplication | In dimension four the regular determinant is `nrd²`, and the regular trace is `2·trd`. The split `2 × 2` determinant is `nrd` (§0.1) |
| The rigidification prototype required only an `F`-algebra equivalence | Require linearity over `F_v`; integral compatibility is additional data (§0.1 and prototype) |
| `finite_classSet` allowed an arbitrary topology on adelic units | Require the canonical finite-adele module topology and native units topology. Otherwise “open” has no arithmetic force (§0.3 and prototype) |
| Full stabilisers were too readily called finite | PR #21's general-field statement is finiteness modulo diagonal central scalars. Full finiteness is the degree-one case (§0.3) |
| Trivial stabilisers were identified with neatness, and neat levels were said not to exist over higher-degree totally real fields | Separate neatness, trivial stabiliser action, finite-image action and central-unit behaviour. Standard neatness does not eliminate infinite central units (Convention 7, §2.3) |
| A geometric coefficient bound implied convergence at its boundary radius | Use `rη<1`, or add a separate endpoint-decay hypothesis. Coefficients of size exactly `η^m` do not decay after scaling at `η⁻¹` (§1.1) |
| The character-expansion decay and the lower-left-entry level bound were conflated | Carry distinct `η` and `ρ`; the row bound uses both, together with the determinant contraction (§§1.1–1.2) |
| Coordinate changes from local integral bases to embeddings were treated as isometries | Their matrices are invertible over a splitting field but can have an inverse of norm greater than one, especially with ramification. Shrink the polydisc (§1.1) |
| Pointwise identities risked being used to detect arbitrary ring-valued series | Invoke the exact coefficient-recovery hypotheses. For general coefficient rings use an explicit restricted-series cocycle constructor; field-valued points cannot detect nilpotents (§1.1) |
| All compact-domain characters implicitly had norm-one values in a Banach algebra | State actual coefficient and norm bounds. Compactness of the image only gives boundedness for a general norm (§1.2) |
| The classical algebraic determinant twist was identified with the extension normalised by `ν(π)=1` | The ratio is `ν_alg(π)^{ord(det γ)}`. Spaces at a fixed unit level agree, but Hecke operators and slopes are rescaled (§1.3) |
| Global algebraic weights did not visibly carry the central-unit condition | Require parallel `n_σ+2v_σ`, or a stated finite-image alternative, and keep the source weight dictionary (§1.3) |
| A right Hecke action was declared an ordinary ring homomorphism into composition endomorphisms | Check the imported convolution convention and use the opposite ring when needed. Singleton normalising cosets already detect the reversal (§3.1) |
| An arbitrary family of monoid elements could define a level-preserving Hecke operator in the prototype | Define its raw finite sum first; prove level preservation from an actual double-coset decomposition. The prototype no longer hides this obligation in an admitted definition (§3.1) |
| Certificate independence could be read on the whole ambient block space | Independence is on the invariant product. With nontrivial stabilisers, ambient extensions from different certificates can differ (§3.2) |
| Every individual `U_v` was called compact in the multivariable setting | Contract every infinite analytic factor, using `U_π=∏U_v`. The map `f(z₁,z₂)↦f(pz₁,z₂)` contains identity on `K⟨z₂⟩` (§3.3) |
| The full Hamilton maximal-order level was used as though it supported the analytic Iwahori action | Its matrices need not have a unit lower-right entry or small lower-left entry. Keep the full-level example classical; use admissible wild levels for analytic coefficients (§§0.2, 2.3) |
| Property (Pr) implicitly gave a contractive averaging projector | Its norm can be as large as `‖|H|⁻¹‖`. For example this can exceed one when `p` divides the finite image order (§2.3) |
| The same sharp coefficient bound was applied after arbitrary stabiliser averaging | The ambient extension `BE` adds a factor `‖E‖^n` to the size-`n` minor estimate unless a sharper bound is proved (§4.2) |
| Exact attainment of a lower polygon was inferred without controlling cancellation | Require a dominant-minor or graded noncancellation argument; repeated row weights are not automatically strict (§4.2) |
| Classical degree-zero coefficients were conflated with the entire analytic module | The classical coefficient space is a line; the Tate coefficient space remains infinite dimensional (§1.3) |
| A weight-two `3 × 3` characteristic determinant was treated as the full overconvergent determinant | It is the finite classical factor. The analytic operator still has infinitely many coefficient coordinates (§4.2) |
| A classical space of dimension `d` always contributed `d` finite slopes | Zero eigenvalues contribute no roots of `det(1-TU)`. Use prescribed-dimension reversal and state invertibility when degree `d` is needed (§4.2) |
| Algebraic scalar extension was described as never surjective onto the analytic extension | It can be surjective, in particular for finite field extensions. Use completed extension in general and prove the finite-extension comparison (§4.3) |
| Eigenvalue statements automatically used `ℂ_p` | Use a chosen complete splitting extension of the coefficient field. There need not be an embedding of an arbitrary coefficient field into `ℂ_p` (§4.1) |
| A single completion `F_v=ℚ_p` justified the global theta character | `|nrd(g)|_f det(g_v)` is trivial on global elements by this argument over `F=ℚ`, not over a general totally real field. Layer 5 now states `F=ℚ` explicitly |
| Theta was represented by the plain derivative in every double-coset block | At representative `cᵢ` its scalar is `c(cᵢ)^{-r}`. Include these constants in the intertwining and determinant cancellation (§§5.2–5.3) |
| The illustrative failure of Bol's identity had inconsistent exponents and derivative | Use the direct `D((1+cz)·1)=c` versus `D(1)=0` test; retain the exact paired automorphy-factor hypothesis (§5.1) |
| The kernel on several residue discs was labelled the same-level global polynomial space | It is locally polynomial on each disc. The level/radius theorem identifies its correct deeper classical level (§§2.2, 5.2) |
| Theta's dense range could suggest a Banach-space quotient isomorphism | Preserve the non-surjectivity of the derivative on a closed-disc Tate algebra. Prove the determinant identity by shifts and nonzero diagonal cancellation (§5.3) |
| Generalised small-slope classicality depended on the trivial-stabiliser determinant model | The direct intertwining and invertibility of `U′-λ/p^r` prove it for all admissible levels with the stated target norm bound (§5.3) |
| The six nonzero Hamilton matrix blocks were each described as one summand | The displayed certificate has nine pairs `(i,t)`; some blocks have two summands. Sum over the fibres of `σ` (§§0.5, 3.2) |
| The notation `S` could suggest only cuspidal forms | Use `M(U,A)` and explicitly retain constant/reduced-norm characters; comparison with a cuspidal classical theory requires additional results (Convention 6) |

Several of these corrections have already appeared in the local Layer 1
implementation board. This rewrite carries them into the definitive roadmap
instead of leaving the old statement and a separate errata list in conflict.
It also keeps the original useful distinctions: native series rather than a
custom carrier, right actions, explicit Hecke certificates, finite stabiliser
invariants, and no Jacquet–Langlands assumption in the direct construction.

## PR #21: disposition of every request

PR #21 was inspected at head
`9d948b203d93167c41d8f171a7a4c9ebbf7cd4b5`. It adds a README section and
three representative Lean targets. The returned PR discussion contained no
additional comments to incorporate.

| Requested target | Destination and treatment |
| --- | --- |
| `DefiniteQuaternion.finite_stab` | README §0.3 and the new prototype: compact subgroup `U`, arbitrary `x`, native central simple dimension-four algebra, total definiteness at every real embedding, canonical module topology, finite central quotient, full finiteness when `[F:ℚ]=1` |
| `hamilton_negative_norm` | Named theorem in the new prototype and §0.3's checks, with exactly the totally real field generality requested |
| `stab_top` | Proved directly in the prototype; the README additionally requires the infinitude explanation through central scalars |
| Consumer convention | Preserve `Γ_x=U∩x⁻¹Dˣx`; prove the comparison to the other conjugation convention |
| Normal central subgroup | Give the actual subgroup definition and a separate normality theorem. Finiteness of the coset type can be stated without installing an admitted normality instance |

The PR's finiteness additions are retained in substance. The review also repairs
the pre-existing `finite_classSet` topology signature; PR #21 correctly used a
module-topology hypothesis for its new theorem but did not change the older
prototype elsewhere.

## Overlap audit and handoffs

### Adelic algebraic groups

The open [AdelicAlgebraicGroups PR #792](https://github.com/TauCetiProject/TauCetiRoadmap/pull/792)
was inspected at head `d1f94d06df5eda87dec87fa71d83cb97f4131b6a`.
Its AA.5.3 explicitly consumes `Dfx`, `unitsIncl`, `globalUnits`, `classSet`,
`finite_classSet` and `DefiniteQuaternion.finite_stab` under the old
`TauCetiRoadmap.OverconvergentForms` namespace.

Those arithmetic interfaces are supplied here. The following stay with that
roadmap: general adelic algebraic groups, general reduction and class-number
finiteness, general neat-level and Hecke-pair results, norm-one adelic
compactness, and the weighted class-number/volume comparison. In particular
this draft does not duplicate AA.5.3's formula or omit its central-index term.
The separate FLT division-algebra comparison avoids making our finiteness
theorem depend on an application that already consumes it.

On an eventual upstream submission, coordinate either temporary compatibility
aliases or simultaneous changes to the consumer's namespace and README links.
The new prototype uses `TauCetiRoadmap.QuaternionicModularForms` now. No remote
consumer has been changed, and its current imports should not be described as
already compatible with the rename.

### Shared analysis and Hecke theory

| Existing owner | What this roadmap consumes | What remains here |
| --- | --- | --- |
| RestrictedPowerSeries | Restricted/entire carriers, substitution, differentiation, Gauss norms, coefficient recovery and several-variable comparisons | The arithmetic embedding-coordinate comparison, weight factors and Bol equivariance |
| PadicFunctionalAnalysis §§4.6, 5.4–5.5 | Character analyticity and scalar expansions of `κ(cz+d)` with their quantitative bounds | Assembling the local-field/embedding weight data and proving the ordered matrix-action cocycle |
| PadicFunctionalAnalysis's model-space and (Pr) theory | `c₀`, bounded matrix representation, finite blocks, analytic disc stages and split modules | Evaluation of automorphic functions, finite-image stabiliser actions and their specific Reynolds projectors |
| CompactOperators | Approximation, compactness criteria, determinants, principal-minor identities, Riesz theory, base change | Proving Hecke contraction estimates and interpreting the generic results on forms |
| NewtonPolygons | Scalar polygons, slope factorisation, roots and multiplicities | The arithmetic row bounds and classical/theta factors supplied to those results |
| Merged ModularForms Layer 2(a) | Abstract Hecke ring and its convolution/product API, built on Mathlib | Its action on quaternionic coefficients, local coset adapters, explicit certificates and operator normalisations |
| GlobalNumberFields | Number-field, finite-adele and product-formula infrastructure | Quaternionic integral models, local rigidifications and the Hurwitz calculation |
| LocallyAnalyticDistributions PR #854 | Completed scalar extension via the shared analytic interfaces | The forms-specific scalar-extension and invariant-projection comparison |

In particular, the scalar analytic expansion theorem in PFA §5.5 is not moved
here. The new weight layer invokes it. Its two old consumer-name references,
and the restricted-series coordination table's old-roadmap link, are updated
to point to QuaternionicModularForms. No supplier theorem is duplicated or
removed. Nonreduced weights use explicit coefficient identities where the
supplier's pointwise coefficient-recovery hypothesis is unavailable.

The geometric outputs are the Banach modules, common-radius restriction maps,
commuting Hecke actions, compact controlling operator and compatible Fredholm
series. Weight-space representability, spectral/eigenvariety gluing,
Atkin–Lehner slope symmetry,
Jacquet–Langlands and general automorphic-representation theory remain
downstream. This is a scope boundary, not a claim that those projects already
import this new namespace.

## Merged-roadmap conventions and snapshots

The accepted examples used for organisation are
[OperatorTheory](https://github.com/TauCetiProject/TauCetiRoadmap/tree/main/TauCetiRoadmap/OperatorTheory)
and [GeometricMeasureTheory](https://github.com/TauCetiProject/TauCetiRoadmap/tree/main/TauCetiRoadmap/GeometricMeasureTheory),
together with the previously inspected analytic/adic examples and
[CONTRIBUTING.md](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/CONTRIBUTING.md).
The new package follows their substantive conventions: a definitive README,
explicit hypotheses, layers with concrete targets and checks, reuse of native
carriers, named dependencies, representative elaborating signatures and one
arXiv topic in metadata. The review and migration notes are separated from the
mathematical specification. An eventual Tau Ceti submission should isolate this
one roadmap and coordinate its supplier dependencies; this local drafting task
does not publish a PR.

Inspected state on 13 October 2026:

- PhD HEAD: `eefb3d91f34b27d0bc7822140fa85fecae029884`.
- Mathlib pin: `bbc4475e9e8fd25fbc8e26d636dd8b37be8f105a`, Lean `v4.33.0-rc1`.
- Tau Ceti merged tree: `97199a4ed890b401e523e38ed11097350518302c`.
- PhD PR #21 and Tau Ceti PR #792: the heads recorded above.
- The merged ModularForms and GlobalNumberFields README files were checked
  at that Tau Ceti snapshot. Current FLT `DivisionAlgebra/Finiteness.lean`
  was inspected for its native carriers and finiteness targets; it is a
  separate project, not installed as a dependency of this prototype.
- Primary mathematical checks used Buzzard's *Eigenvarieties*, the author-hosted
  `GL1.pdf` of *On p-adic families of automorphic forms*, Loeffler §3.1.4,
  Milne §3 and the local Jacobs thesis transcription. Buzzard's different
  `families.pdf` is not the 2004 quaternionic paper.

## Migration and validation

The candidate code includes `PhD/TauCeti/Code/OverconvergentForms/Quaternion/`,
`Adelic/`, `Level/`, `Hamilton/` and `Weight/`, together with the older
`PhD/Main/QMF`, `JacobsSlash` and `LWX` developments. The Layer 1 implementation
board was read for its correction history. None of these is imported by the
new prototype.

Before porting, inspect theorem statements and transitive assumptions, especially
the `HasFiniteClassSets` interface in the local level code, the central-unit
finiteness generalisation, the determinant-normalisation comparison and the
theta representative factors. A file having no direct `sorry` does not by
itself certify the complete target. Reuse existing proofs where they match the
new specification and upstream library APIs; do not copy entire private series
or Fredholm libraries into this package.

The prototype deliberately covers representative interfaces rather than every
milestone: canonical adelic carriers, class-set/stabiliser targets, local-field
linear splittings, determinant-character normalisation, a real form submodule,
evaluation and the certificate formula, native series columns, Bol's identity,
theta and the generalised-eigenvector classicality mechanism. Its theorem
proofs marked `sorry` remain implementation work. Elaboration verifies the
interfaces' syntax and type compatibility, not those mathematical proofs.

Validation completed with
`lake env lean PhD/TauCeti/RoadmapsNew/QuaternionicModularForms/Suggested.lean`:
exit status zero, with only the 15 expected admitted-theorem warnings. All
definitions and the form-submodule closure proofs elaborate without admitted
bodies or instances. The package's local Markdown links and `math.NT` metadata
were checked. The original roadmap and production Lean files were not changed.
