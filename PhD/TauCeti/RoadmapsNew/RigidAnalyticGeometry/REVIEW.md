# Rigid analytic geometry: review and coordination record

Prepared on 13 October 2026 from the
[revised roadmap](../../Roadmaps/RigidAnalyticGeometry/REVISED.md), its
[change record](../../Roadmaps/RigidAnalyticGeometry/CHANGES.md), the
original roadmap and representative algebra source, and
[PhD PR #25](https://github.com/WilliamCoram/PhD/pull/25).
The new mathematical specification is [README.md](README.md).
The original files and the existing mathematical implementation are unchanged.

The revised architecture is worth retaining: classical algebra and general
G-topology here, shared geometric constructions in the adic programme, and
explicit comparisons between them. Two changes are necessary. First, the new
RestrictedPowerSeries roadmap already owns most of the revised Layer 0.
Second, the current adic drafts still name the old rigid roadmap as their
geometry supplier. Merely importing them would create a circular dependency.
The new draft specifies the intended division and records the concrete
coordination work below. It does not claim that upstream authors have agreed
to the changes or that a roadmap target is already a proved theorem.

## Mathematical review

| Point checked | Treatment in the new draft |
| --- | --- |
| Tate versus general affinoid algebra | Import the single Tate package; retain affinoid topology, normalisation, fractions and spectral consequences here. Do not duplicate the new shared series roadmap |
| Characteristic-positive weak stability | Keep the full theorem for `Frac(Tₙ)`, b-separable/countable-type inputs and inseparable finite normalisation. Existing characteristic-zero proofs are not evidence for the stronger statement |
| General Japanese rings | Use PR #779's vocabulary and criteria. This roadmap supplies the Tate/affinoid application, not another definition or general permanence library |
| Automatic continuity | Use the closed-graph proof before the supremum theorem. Clarify that the noetherian intersection is over **all maximal ideals and all positive powers**. A fixed maximal ideal in `K×K` is a counterexample to the unqualified fixed-ideal version |
| Norm and topology | Affinoidness remains an explicit proposition. Topology is presentation independent; chosen norms are bounded-equivalent. BGR strictness is the quotient-to-image homeomorphism condition, not an arbitrary assertion of equality of presentation norms |
| Equidimensionality | Every maximal ideal has height `dim A` for an affinoid domain; `K⟨T⟩×K` disproves the unrestricted reduced-algebra version |
| Zero algebra | Empty maximal spectrum, zero supremum, no normalisation injection. Use positive powers in the unconditional power formula and nontriviality for maximum attainment |
| Spectral norm and nilpotents | The kernel is the nilradical, and reduced affinoids have an equivalent complete supremum norm. A reduced domain need not have a multiplicative supremum norm: use the annulus |
| General BGR statements | Retain integral torsion-free maps from an integrally closed domain in 3.8.1/7; state the valued noetherian integrally closed base and weakly stable fraction-field hypotheses of 3.8.3/7. Keep the reduced, possibly non-domain target |
| Uniform value-group assertion | One positive exponent depends on the affinoid, not on the individual function. This supplies the strict-radius converse without a circular use of that converse |
| Maximum locus | Zariski density belongs to the Tate theorem. On `K×K`, `(1,0)` gives a maximum locus missing a whole component |
| Completed tensors | The quotient/pushout construction, density of the algebraic tensor and a topological isomorphism to the completed tensor are distinct obligations. Finite module base change carries its canonical topology |
| Rational localisation | Keep the unit-ideal and nonzero-denominator conditions, and prove the completion comparison. Reducedness is not preserved by arbitrary flat algebra maps; the forward local-reducedness implication uses affinoid localisation |
| Integral models | Keep the presentation ring `A₀`, power-bounded ring `A°` and arbitrary ring of definition distinct. Reduced `B/ϖB` is sufficient, not necessary, for `B=A°`; `ϖ` need not be a scalar |
| Almost noetherianity | A single finite submodule must work for all scalars with `|c|≤ε`. The `ℂ_p` example tests why this is weaker than noetherianity |
| Kiehl approximation | Uniform scalar, variable finite families; no claim of one finite image containing the actual restriction operator. Its constant coefficient is unchanged, so complete continuity does not imply norm less than one |
| Closed targets and perturbations | No general `A`-linear complement or right inverse is assumed. The closed-target theorem and small-perturbation theorem have different proofs and suppliers |
| Schwartz's theorem | Closed image and finite cokernel over an affinoid base. Surjectivity plus compact perturbation does not imply finite kernel |
| Numerical slopes | Require `r>0`; include the endpoint. Roots of the annihilating polynomial are eigenvalues, while Fredholm roots are reciprocals. Do not assert a global family decomposition at every cutoff |
| Coherent and arbitrary modules | Separate algebraic Čech exactness for arbitrary modules from finite-module Banach strictness and coherent cohomology |
| Quasi-Stein | Countable admissible affinoid exhaustion with dense restrictions. No extra relative-compactness hypothesis; generation is on each member, not necessarily by a globally finite family |
| Formal functions | Keep the stable principal filtration and both uniform pro-zero assertions. The general-ideal theorem requires its own noetherian filtration argument. Ideal-adic and Banach completions are different |
| Analytification | Include relative analytification over an affinoid base. Normality and reducedness compare using excellent local rings and completions; local integrality does not, as the node demonstrates |
| Classical/adic points | Constructible density does not identify the carriers or determine arbitrary subsets. The rank-two point below Gauss is outside the adic open corresponding to the rigid open disc despite `v(T)<1` |
| Image of the comparison functor | Distinguish full faithfulness, being locally in the image, the quasi-separated equivalence and affinoid detection. Preserve both non-quasi-separated examples from PR #25 |
| Properness and GAGA | Keep the stated hypotheses of the converse properness comparison and the relative proper GAGA maps. Do not promote them to unrestricted properness or étale-topos equivalences |

These checks use the existing BGR transcriptions in the Layer 0–2 reference
directories, the exact target statements in the inspected PRs, and the
primary references linked in the README. They are a review of statements,
dependencies and examples, not a fresh proof audit of all local mathematics.
In particular the Kiehl locators are carried from the PR and its supplier
references, with the Banach formulation compared to Bosch's account.

## Disposition of PR #25

PR #25 was inspected at head
`af8261a42a548ed86a11fff72c486673ef122ae7`. It appends 247 README lines and
508 prototype lines to the original roadmap. The returned discussion had
no additional comments. The proposals below incorporate its mathematics
without importing its second copies of shared definitions.

| Requested interface | New location and owner |
| --- | --- |
| Japanese/Nagata vocabulary and criteria, Layer 0 | README scope table and §0.2: consume SchemeAndStackFoundations; own the valued-field and affinoid application |
| Positive-polyradius strict-affinoid criterion, Part IV F1.1 | §1.5: series and finite monomial extension from RPS, converse and supremum comparison here |
| Finite canonical reductions | §2.3, including the actual induced map and finite type over the residue field |
| `height_eq_ringKrullDim_of_isDomain` | §1.2 and prototype; domain hypothesis and product counterexample retained |
| Reducedness local on rational covers | Layers 3–4: shared Part II geometry, transported to the classical algebras for Part IV R5.7 |
| Finite modules under complete field extension | §1.3, with canonical elementary-tensor formula, topologies, arbitrary complete isometric extension and all three checks |
| `proper_cohomology_principalFiltration` | §7.5, as a Part III proof contract and classical comparison; eventual stability, uniform cofinality and uniform image condition are all retained |
| `analytification_stalk_isReduced_iff`, `analytification_stalk_isNormal_iff` | §8.1, completed local rings and excellence; no local-integrality assertion |
| `isReduced_iff_analytification`, `isNormal_iff_analytification` | §8.1, including global-to-local justification and nonreduced controls |
| Constructible closure in `Spv A` and density in `Spa(A,A°)` | §8.2, including `L_A`, rational traces and the rank-two countercheck |
| Image of `r`, quasi-separated equivalence and affinoid detection | §8.3, with full faithfulness, local image, ringed-topos comparison and both gluing examples |
| Banach item 1: strict complete continuity, ordinary implication, closed-target descent | §7.1(2), owned in Part III, using CompactOperators' existing ordinary predicate |
| Banach item 1: `exists_c0_surjective` | §7.1(1), PFA's model-space quotient contract, arbitrary index set |
| Banach item 2: Schwartz finite-cokernel theorem | §7.1(3), Part III |
| Banach item 3: perturbation of surjections and generators | §7.1(1), explicit PFA §1.2 contract; no splitting assumption |
| Banach item 4: relative compactness and actual restriction | §7.1(4), Part III, preserving the `c₀` precomposition and finite-module restriction map |
| Banach item 5: almost noetherianity and discrete corollary | §2.3 and prototype, owned here for presentation rings |
| Banach item 6: `IsSlopeLE`, `IsSlopeDecomposition`, projection | §7.2 consumes LAD §4.16 and CompactOperators; own only the affinoid point/norm comparison |
| Banach item 7: reduced ring-of-definition quotient | §2.3 and prototype give the affinoid supremum corollary of Part II's general theorem |

The prototype intentionally does not copy the PR's artificial geometric
placeholders or its operator/slope definitions. It uses an explicit
`IsAffinoidAlgebra` hypothesis, rather than making affinoidness a typeclass
because the historical skeleton happened to do so. Its filtration theorem
is a precisely stated algebraic consequence of stability, not a substitute
for the proper-cohomology theorem or its cokernel assertion.

## Retention of the revised roadmap and PR #20

| Revised programme | New disposition |
| --- | --- |
| Layer 0 Tate algebra through strict finite-module theory | Imported in §0.1 from RPS; no mathematics discarded |
| Layer 0 weak stability and Japanese application | §0.2, using the generic algebra owner |
| Layers 1–2 algebra, fractions, tensor presentations, norms and reduction | Layers 1–2; status exceptions below remain visible |
| Layers 3–5 geometry and acyclicity | Shared geometric contracts and explicit classical comparisons in Layers 3–5 |
| General G-topology, enhancement, pasting and sheafification | §6.1; its affinoid application and gluing comparison in §6.2 |
| PR #20 finite injective maps are closed embeddings | §1.1 |
| PR #20 presentation-integrality and finite reductions | §2.3 |
| PR #20 subdomain injectivity and faithful flat covers | Layers 3–4 |
| PR #20 arbitrary complete-field faithful flatness | §1.3, used in §6.2 |
| PR #20 identity principle and locally free variant | §7.3 |
| PR #20 proper cohomology finiteness and closed Čech ranges | §7.4 |
| PR #20 formal functions, subdomain, finite-flat and field base change | §§7.4–7.5 |
| PR #20 connectedness and reduced irreducible components under analytification | §8.1 |
| Relative analytification and proper GAGA | §§8.1 and 8.4 |
| Étale/pro-étale comparisons | Explicit external ownership, rather than the revised draft's open-ended instruction to consume them if needed |

## Overlap audit and required handoffs

### Existing local suppliers

RPS now owns the Tate-algebra portion of old Layer 0, including reduction,
maximum modulus, Rückert theory, closed ideals and finite Tate modules.
The new rigid roadmap retains weak stability/Japaneseness applications and
general affinoid algebra. Its polyradius construction is imported; its
strict-affinoid converse remains here. This follows the division already
recorded in RPS §5.4. The RPS coordination record now links to this proposal.

PFA owns general gauges, open mapping, finite-module topology and `c₀`
quotients. The perturbation result of PR #25 is made an explicit supplier
contract in §7.1; the current PFA §1.2 states its open-mapping input but
does not yet spell out that corollary. Likewise the b-separable inputs to
weak stability must be reconciled with PFA's countable-type package.
These are named handoffs, not silently available declarations.

CompactOperators §0.1 already sends strict complete continuity and
cohomological applications to Part III. That division is preserved. Its
ordinary predicate and projector construction are reused. At the inspected
head, LAD §4.16 itself specifies `NumericalSlopeDecomposition`, its projector,
functoriality and uniqueness. Copying PR #25's numerical definition here
would overlap it. The new §7.2 only supplies the classical-point dictionary
and names the exact shared interface.

### The reverse dependencies in Parts II and III

Part II's current scope table and “Local restatements” section say that
`RigidSpace`, its gluing, analytification, `r`, classical constructible
density, the quasi-separated equivalence and the normal/reduced comparison
are supplied by the **old RigidAnalyticGeometry** roadmap. Its prototype
explicitly avoids restating supplied declarations. Part III likewise names
that old roadmap for quasi-Stein theorems, proper mapping, proper Čech
strictness, formal functions, principal filtrations and proper GAGA.

The revised local roadmap proposes the opposite direction for those proofs.
The new draft retains that proposed architecture, subject to these concrete
changes before production integration:

1. Keep a one-way classical algebra supplier to Part II R0.9. RPS supplies
   Tate algebra; this roadmap supplies general affinoids, norms and integral
   models. Neither uses the later geometry to prove its algebraic floor.
2. Move the shared geometric construction obligations to Part II, and the
   coherent/Kiehl/GAGA proof obligations to Part III. Replace their old
   “supplied by RigidAnalyticGeometry” proof references for those groups.
   Retain references here only for the independent algebra and comparisons.
3. Put general G-site lemmas below the two presentations. Build the shared
   rigid category once; its comparison with the BGR G-site belongs here.
4. Implement each Kiehl prerequisite in its owner from §7.1. In particular,
   almost noetherianity is an independent algebraic input, and the proper
   filtration proof cannot depend on its own transported classical version.
5. Coordinate consumer target names and compatibility aliases. PR #25 and
   current upstream tables cite historical section numbers; use the mapping
   tables above to retarget them. Do not import a roadmap prototype as a
   mathematical dependency.

No remote roadmap or PR was changed. Until these handoffs are agreed, the
new package is a coordinated **proposal**, not an assertion that the open
adic PRs already provide the needed proofs. This is the principal remaining
integration issue; an apparently overlap-free list of imports would conceal it.

### Other boundaries

PR #779 retains general Japanese/Nagata and scheme foundations. Part II
retains the general reduced-ring-of-definition theorem, and this roadmap
identifies its conclusion with the affinoid supremum ball. Part IV receives
the strict-radius and local-reducedness interfaces, while retaining dagger
and étale geometry. General completed tensors belong to Part II/LAD;
the finite-affinoid-module comparison is here. Neither QuaternionicModularForms
nor eigenvariety gluing acquires new foundational definitions from this draft.

## Sources, models and implementation status

The draft follows the current
[contribution guidelines](https://github.com/TauCetiProject/TauCetiRoadmap/blob/97199a4ed890b401e523e38ed11097350518302c/CONTRIBUTING.md)
and [writing checklist](https://github.com/TauCetiProject/TauCetiRoadmap/blob/97199a4ed890b401e523e38ed11097350518302c/README.md#writing-a-roadmap).
The merged examples used were
[OperatorTheory](https://github.com/TauCetiProject/TauCetiRoadmap/tree/97199a4ed890b401e523e38ed11097350518302c/TauCetiRoadmap/OperatorTheory),
[GeometricMeasureTheory](https://github.com/TauCetiProject/TauCetiRoadmap/tree/97199a4ed890b401e523e38ed11097350518302c/TauCetiRoadmap/GeometricMeasureTheory),
and [AnalyticToricGeometry](https://github.com/TauCetiProject/TauCetiRoadmap/tree/97199a4ed890b401e523e38ed11097350518302c/TauCetiRoadmap/AnalyticToricGeometry).
The borrowed conventions are a definitive, timeless README, an explicit
library floor, single native carriers, canonical comparison maps, required
checks and named owners. Historical findings are kept in this review rather
than appended as competing specifications to the README.

| Source | Inspected commit |
| --- | --- |
| PhD baseline | `eefb3d91f34b27d0bc7822140fa85fecae029884` |
| Mathlib dependency | `bbc4475e9e8fd25fbc8e26d636dd8b37be8f105a` |
| TauCetiRoadmap merged main | `97199a4ed890b401e523e38ed11097350518302c` |
| PhD PR #25 | `af8261a42a548ed86a11fff72c486673ef122ae7` |
| [Part II #817](https://github.com/TauCetiProject/TauCetiRoadmap/pull/817) | `1d89276a2ce598ec97db2cf0f21c0edc04a16058` |
| [Part III #813](https://github.com/TauCetiProject/TauCetiRoadmap/pull/813) | `3c091e772acdb1d5220ad8f87b227ea8ee9e2fd4` |
| [Part IV #815](https://github.com/TauCetiProject/TauCetiRoadmap/pull/815) | `658a5eb94fc06abe8ea218d3b4177c2197557f0c` |
| [SchemeAndStackFoundations #779](https://github.com/TauCetiProject/TauCetiRoadmap/pull/779) | `28f49b6448d1cf52e31ea697e7b6af700e5eb2ff` |
| [LocallyAnalyticDistributions #854](https://github.com/TauCetiProject/TauCetiRoadmap/pull/854) | `84b4aff9523485ea44083ef2f20c4a39fc242270` |

All five supplier PRs were open at inspection. Part III is stacked on
Part II; Part IV has additional stack dependencies. The revised roadmap's
older Part II–IV pins therefore cannot be used as a statement of current
ownership. Merge status of a roadmap is also not proof status of its code.

The local source under `PhD/TauCeti/Code/RigidAnalyticGeometry/` is useful
provenance. Its three Layer 0–2 work boards record important limitations:

- Weak stability of the Gauss fraction field, Japanese applications and
  some Banach-function consequences currently use characteristic zero.
- The general reduced finite torsion-free spectral theorem has narrower
  domain implementations; the general integral-map equation target has a
  finite-map implementation. The full statements remain required.
- The fraction-algebra quotient and localisation-density results do not
  yet provide every seminormed completion comparison.
- The finite monomial polyradius extension is available as source; the
  converse strictness criterion and supremum comparison are separate work.
- Norm-equivalence proofs do not install a complete supremum-norm carrier.
  An algebraic finite-field tensor result does not install its topology.
- The annulus norm calculation and the proof that its algebra is a domain
  are separate obligations.

These are recorded-source observations, not fresh successful builds or axiom
audits. Preserve authorship when migrating and keep the two independent
`PhD/Main` and `PhD/TauCeti` source chains separate. The manifest has no
Tau Ceti dependency, so the prototype adds no fictitious upstream imports.

## Validation and authorship

`lake env lean PhD/TauCeti/RoadmapsNew/RigidAnalyticGeometry/Suggested.lean`
completed successfully against Lean `v4.33.0-rc1` and the Mathlib pin above,
with exactly 20 expected warnings for the 20 admitted theorem targets and
no errors. Its definitions have concrete bodies, with no admitted instances
or opaque carriers. Compilation validates the interfaces only;
geometry and completed tensors remain precise README contracts on their
shared suppliers, not proved by this file. Local Markdown links, whitespace,
the `math.AG` metadata and prototype structure checks passed separately.
No production theorem is modified or certified here.

This draft and review were prepared with AI assistance from Codex (GPT-6).
They are an author-side mathematical/interface review, not an independent
expert approval. A future upstream contribution should retain the AI
attribution in its PR description and submit only the roadmap's directory;
supplier ownership changes need their corresponding coordinated revisions.
