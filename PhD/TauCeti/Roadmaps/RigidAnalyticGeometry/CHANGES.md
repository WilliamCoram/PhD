# Changes in the revised rigid analytic geometry roadmap

The [revised roadmap](REVISED.md) proposes the division of work suggested in
[PhD issue #18](https://github.com/WilliamCoram/PhD/issues/18): retain the full
classical algebra of Layers 0–2, develop the general G-topological formalism, and
consume the geometry of Layers 3–8 from AdicSpaces Parts II and III, with Part IV
supplying the later site comparisons.

This comparison uses the PhD repository at commit
`eefb3d91f34b27d0bc7822140fa85fecae029884` on 13 October 2026. That baseline already
includes the targets added by [#20](https://github.com/WilliamCoram/PhD/pull/20).
The revision is a proposal for implementation ownership and integration; upstream
roadmaps have not been edited or their maintainers' agreement presumed.

## Files and preservation

Two new documents belong beside the existing roadmap in
`PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/`:

| File | Purpose |
|---|---|
| `REVISED.md` | The new roadmap, including implementation status, mathematical requirements, dependencies and acceptance examples |
| `CHANGES.md` | This comparison with the original roadmap |

The existing `README.md` and `Suggested.lean` are preserved byte for byte. No Lean
implementation, imports, dependency pins, build settings or historical work-board
files are changed. The revision does not turn the historical `sorry`-backed target
signatures into proved declarations.

## Principal scope changes

| Subject | Original programme | Revised programme |
|---|---|---|
| Overall structure | A largely self-contained progression from Tate algebras to rigid varieties and their adic comparison | An algebra programme, general G-topology, and explicit interfaces to the adic geometry programme |
| Layers 0–2 | Full BGR classical algebra, with historical status paragraphs and later amendments | Full mathematical scope retained; current proofs, missing generality and integration work distinguished |
| Layers 3–4 | Construct affinoid varieties and subdomains and prove their geometry locally | Consume Part II R1.1/R1.9 and the relevant morphism theory; own the algebra and coordinate-ring comparisons |
| Layer 5 | Develop the Čech and Tate-acyclicity programme locally | Consume Part III R3.1; compare complexes, restrictions and the classical site; keep genuinely missing general site lemmas |
| Layer 6 | General G-topologies followed by an independent construction of rigid varieties | Keep the full general G-topology programme; identify the classical affinoid site with the shared geometry supplied by Part II |
| Layer 7 | Local coherence and properness programme, enlarged by #20 | Consume the geometric theorems from Parts II and III and retain the #20 statements as explicit requirements |
| Layer 8 | Local analytification and rigid–adic comparison, enlarged by #20 to proper GAGA | Consume Part II analytification/comparison and Part III GAGA; treat Part IV site comparisons as later dependencies |
| Overlap with Part II R0.9 | Similar algebraic goals appear in both programmes | Integrate the existing classical algebra once and expose it through compatible interfaces |
| General completed tensors | Presentation constructions with limited comparison to other models | Keep the presentation algebra and its proved universal property; make the comparison with upstream completion a separate task |

The classical geometric statements remain visible as acceptance requirements.
Assigning a theorem to an upstream supplier does not establish that it is already
proved or remove its hypotheses. If a requested statement is missing upstream,
the gap remains explicit and should be implemented in its agreed owner.

## Material retained locally

The shortened presentation does not narrow Layers 0–2 to the minimum needed by
the adic roadmaps. In particular, the following remain in scope:

- The full Tate-algebra Gauss norm, reduction, evaluation and maximum modulus
  programme; Weierstrass polynomials, finiteness and distinguished charts.
- Rückert theory and its noetherian, factorial, normal, Jacobson and dimension
  consequences; strict closedness of ideals and finite-module subobjects.
- Weak stability of Tate fraction fields and the Japanese property, including
  the characteristic-positive and inseparable cases still missing from the code.
- Affinoid presentations, quotient norms, normalisation, finite residue fields,
  automatic continuity, strictness, tensor presentations and generalised fractions.
- Several-variable restricted series at arbitrary positive polyradii, including
  the full strict-affinoid criterion.
- The supremum seminorm, maximum modulus, spectral radius, integral equations,
  power-boundedness, reduced Banach function algebras and reduction of maps.
- BGR's more general torsion-free and integral-map statements, even where the
  current implementation proves the domain or finite-map case needed by consumers.
- General G-topologies, enhancement, pasting, stalks, sheafification and extension
  of sheaves from weak to strong G-topologies.

The finite-reduction and integral-elements statements added in #20 are now placed
directly in revised §2.6. They no longer sit behind a broad exclusion of reduction
theory. The further geometric reduction theory used for formal models stays with
Part III.

## Treatment of the targets added in number 20

The original appendix says that Parts II–IV will import classical geometric
results from this roadmap. Applying the simple split in #18 without accounting
for that appendix would create an ownership conflict and could produce a circular
proof plan. The revision preserves the mathematical requirements while separating
independent algebraic inputs from geometric results to be supplied upstream.

### Algebraic exports

| Original target or requirement | Revised location | Treatment |
|---|---|---|
| Tate algebra, Gauss norm, strict finite modules, normalisation, Jacobson property, finite residue fields | Layers 0–1 | Reuse the proved algebra as a common input to Part II R0.9 and the other consumers |
| Dimension under finite injective maps; polynomial generation of Tate maximal ideals | §1.2 | Keep as algebraic exports, including the material formerly presented in §3.1.3 |
| `isClosedEmbedding_of_finite_injective` | §1.3.4 | Retain finite strictness and automatic continuity with the complete-norm hypotheses |
| `isUnit_toRationalLocalization_of_span_eq_top` | §1.4.2 | Retain the unit-ideal hypothesis explicitly |
| `supSeminorm_pow_pos` | Convention 5 and §§2.1, 2.6 | Retain the positive-exponent formulation for the zero algebra |
| `powerBounded_integral_over_presentation` | §2.6.1 | Retain the integral-closure description, including nonreduced affinoids |
| `reduction_finite_of_finite` | §2.6.2 | Retain the induced finite reduction map and finite-type consequence |
| `height_eq_ringKrullDim_of_isDomain` | §1.2.5 | Treat the statement as classical algebra supplied to Part II R1.9 |

### Local geometry and scalar extension

| Original target or requirement | Revised location | Proposed supplier and local responsibility |
|---|---|---|
| Subdomain universal property, infinitesimal quotients, transitivity, preimages, intersections and local completions | Layer 4 | Part II R1.1 supplies geometry; local comparisons identify coordinate rings and maps |
| Gerritzen–Grauert, including its ambient-cover form | Layer 4 | Part II R1.1; retain the stronger form needed by acyclicity and descent |
| `AffinoidSubdomain.injective_of_isDomain` | Layer 4 | Part II R1.9, using the supplied flatness result; preserve nonemptiness |
| `faithfullyFlat_affinoidCover` | Layer 4 | Part II R1.1 and the Part III acyclicity/descent interfaces; preserve empty-cover conventions |
| `iUnion_rationalDomain_nonzero_eq_univ_iff` | Layer 4 | Part II R1.1/R1.9; retain nonzero denominators and the unit-ideal equivalence |
| Rational/Laurent refinements and arbitrary-module Tate exactness | Layer 5 | Part III R3.1 and the common acyclicity foundation; track arbitrary modules separately from finite modules |
| General G-topology and locally G-ringed presentation | §§6.1–6.3 | General formalism remains local; compare it with the shared rigid category |
| Rigid gluing, fibre products and completed scalar extension | §6.4 | Part II geometry and completed tensors; local algebra comparisons |
| `faithfullyFlat_scalarExtension` | §6.4 | A retained scalar-extension requirement coordinated with Part II R0.3 and Part III R3.6 |

### Coherence proper mapping and GAGA

| Original target or requirement | Revised location | Proposed supplier and preserved condition |
|---|---|---|
| Exact associated modules, Kiehl's affinoid equivalence, coherent affinoid acyclicity | §7.1 | Part III R3.1–R3.3; compare the actual module sheaves and cohomology |
| Finite morphisms, coherent ideals, closed subvarieties, relative compactness and rigid properness | §§7.1–7.2 | Parts II and III on the common geometric category |
| `identityPrinciple`, `identityPrinciple_locallyFree` | §7.2 | Part II R1.9; retain normality, connectedness and a nonempty open; vector bundles rather than arbitrary coherent sheaves |
| `quasiStein_dense_restriction`, `quasiStein_global_generation`, `quasiStein_acyclic` | §7.3 | Part III R3.4; retain a countable admissible affinoid exhaustion with dense restrictions |
| `quasiStein_higherDirectImage` | §7.3 | Part III R3.4; require quasi-Stein inverse images of affinoid opens |
| `kiehlProperMapping`, `proper_cohomology_finite`, `proper_cech_closedRange` | §7.4.1–2 | Part III R3.6; retain Kiehl properness, coherence, finiteness and strictness |
| `proper_formalFunctions` | §7.4.3 | Part III R3.6; preserve the canonical ideal-adic completion map |
| `proper_cohomology_affinoidSubdomain` | §7.4.4 | Part III R3.6; preserve the canonical restriction-induced tensor comparison |
| `proper_cohomology_finiteFlat`, `proper_cohomology_fieldExtension` | §7.4.5 | Part III R3.6; retain finite flatness or a complete isometric field extension as appropriate |
| Classical analytification and its local-ring and morphism compatibilities | §8.1 | Part II R1.3–R1.6 and R1.9 |
| `analytificationModules_exact_coherent`, `analytification_isProper` | §8.1 | Parts II and III; preserve the relative affinoid-base formulation |
| `proper_gaga_cohomology`, `proper_gaga_equivalence`, `proper_gaga_directImage` | §8.3 | Part III R3.7; use the specified analytification functor and canonical maps |
| `analytification_preconnected_iff`, `analytification_irreducibleComponents` | §8.1 | Part II R1.5/R1.9; preserve the connectedness comparison and reduced component structures |

This matrix assigns a destination to every named addition in the #20 README
appendix. It does not delete or rewrite the corresponding historical Lean
signatures, and it does not claim that each proposed supplier has already adopted
the exact statement.

## Dependency and availability corrections

The original layer chain is replaced by dependencies between the relevant theorem
groups: common foundations, classical algebra, algebra comparisons, Part II
geometry, Part III coherence, then classical site/cohomology comparisons and
applications. General G-topology sits below both geometric presentations.

In particular, a local transport theorem cannot serve as an input to the upstream
theorem from which it is transported. If an upstream proof still needs a classical
result from #20, that result must be proved independently in the common foundations
or in the supplier programme before the transport is used.

The new availability section incorporates
[the update to issue #18](https://github.com/WilliamCoram/PhD/issues/18#issuecomment-6117270006)
and checks the actual upstream files at pinned commits. It distinguishes:

- a mathematical target in a README;
- a Lean signature or concrete definition in `Suggested.lean`;
- a proved library theorem suitable for a production dependency.

At the inspected commits, Parts II, III and IV are open draft PRs. Their Lean
files include theorem signatures with `sorry`, and substantial geometry remains
in READMEs. Some algebra and subdomain signatures are now present, so the revision
also avoids treating the issue comment as a permanent assertion that all rigid
material is absent from Lean.

The PhD dependency manifest has no Tau Ceti or TauCetiRoadmap dependency. The
revision therefore supplies an integration policy instead of adding unresolvable
imports or treating a roadmap import as proof of the desired mathematics.

## Implementation status and mathematical qualifications

The broad historical status paragraphs are replaced by a table tied to source
paths at the current PhD commit. The following qualifications are explicit in the
revised targets.

| Point | Clarification in the revision |
|---|---|
| Tate carrier | Follow the actual `MvPowerSeries.Restricted` implementation and prove comparisons with upstream carriers; do not prescribe a redundant replacement |
| Affinoid predicate | The implementation uses a proposition through an explicit hypothesis; the historical skeleton's class is not the implemented interface |
| Characteristic | Weak stability, Japaneseness and the reduced Banach function capstones are not yet implemented in their full characteristic-free generality |
| Continuity proof | Use the existing closed-graph route, avoiding a dependency on Layer 2's supremum-norm theorem |
| Tensor universal property | Preserve the existing continuous Banach-algebra universal property, while distinguishing it from a general normed completed-tensor construction |
| Finite field extension | Distinguish the proved algebraic affinoidness result from the additional topological identification |
| Generalised fractions | Density of the algebraic localisation does not by itself establish the unbuilt seminorm-completion model or the adic comparison |
| Polyradii | Follow the implemented finite-monomorphism proof; retain the converse and supremum-norm comparisons as remaining work; use the term strict affinoid precisely |
| General BGR statements | Keep torsion-free versus domain and integral versus finite-map formulations distinct |
| Complete supremum norm | The existing norm inequalities are not an already installed second complete normed-ring structure |
| Uniformity | Separate boundedness proved in the local Banach vocabulary from its pending Huber-class comparison; nonreduced affinoids remain in the geometry |
| Rational domains | State the unit-ideal condition and nonzero-denominator convention; inequalities alone include common zeros |
| Properness comparison | Retain the hypotheses of Part II R1.7, including restrictions on converse implications |
| Cohomology | Keep finite-module topological assertions, arbitrary-module algebraic exactness, strictness and derived sheaf cohomology distinct |

The remaining source-board examples, such as noncompleteness of the Tate fraction
field or a particular ramified quadratic instance for a reduction counterexample,
are not promoted to completed results. The revised acceptance list prioritises
examples that test the retained algebra and the new comparisons. The original
roadmap and work boards retain the more extensive historical example catalogue.

## Acceptance examples corrected or sharpened

1. For `p+T²` over `ℚ_p`, the supremum is attained at `T=1`; its value at `T=0`
   is `|p| < 1`. The original acceptance paragraph incorrectly used the zero point.
2. The power formula excludes exponent zero when the affinoid algebra is zero.
3. An open-disc exhaustion uses radii `|ϖ|^(1/n)` approaching one in `√|K×|`.
   Radii taken only from `|K×|` need not approach one over a discretely valued field.
4. The annulus's norm computation and its domain assertion are separate checks;
   the current source records the latter as deferred.
5. Nilpotents, empty spectra and nonclassical adic points explicitly test that the
   comparisons preserve the intended algebras and distinguish their point spaces.
6. The Laurent complex comparison fixes its differential sign and augmentation,
   and GAGA tests use the specified canonical maps under properness hypotheses.

## Reference pins and validation scope

The comparison uses the following immutable source snapshots:

- [PhD original roadmap and #20 appendix](https://github.com/WilliamCoram/PhD/blob/eefb3d91f34b27d0bc7822140fa85fecae029884/PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md).
- [PhD current algebra source](https://github.com/WilliamCoram/PhD/tree/eefb3d91f34b27d0bc7822140fa85fecae029884/PhD/TauCeti/Code/RigidAnalyticGeometry).
- [AdicSpacesPartII](https://github.com/TauCetiProject/TauCetiRoadmap/blob/b45e54cbcf0c012d7f78b2cf62a716a69fb5ce66/TauCetiRoadmap/AdicSpacesPartII/README.md), PR #817.
- [AdicSpacesPartIII](https://github.com/TauCetiProject/TauCetiRoadmap/blob/ae824af115b07053c757e5cf5e48f7e50f0ea6af/TauCetiRoadmap/AdicSpacesPartIII/README.md), PR #813.
- [AdicSpacesPartIV](https://github.com/TauCetiProject/TauCetiRoadmap/blob/059fd1582e0ebc00212a3a5fb8447127a6c76b7b/TauCetiRoadmap/AdicSpacesPartIV/README.md), PR #815.

The accompanying source and work-board checks establish the documented scope and
implementation distinctions. This is a documentation change: no new Lean proofs,
build results or transitive axiom checks are claimed. The implementation roadmap
specifies those checks for future proof milestones.
