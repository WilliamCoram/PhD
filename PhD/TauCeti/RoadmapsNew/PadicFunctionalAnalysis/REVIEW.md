# P-adic functional analysis: review and revision

Prepared on 13 October 2026 from the
[previous roadmap](../../Roadmaps/PadicFunctionalAnalysis/README.md), its
[Lean prototype](../../Roadmaps/PadicFunctionalAnalysis/Suggested.lean),
[PhD PR #23](https://github.com/WilliamCoram/PhD/pull/23), and the
supplier contracts in the Tau Ceti PRs referenced there. The revised
specification is [README.md](README.md).

This is an author-side review and redraft prepared with Codex (GPT-6).
It checks mathematical statements, representative interfaces and ownership.
It does not constitute external review, agreement by other roadmap authors,
or a proof-dependency audit of the candidate implementation files.

The interface choices below were revisited on 14 October 2026 in response
to the author's questions about Banach modules, bases, matrices and Tate
conditions. The original source audit remains dated 13 October.

## Interface choices and source recheck

1. **Use the existing classes for Banach modules.** The roadmap uses a
   normed additive group, a module action, `IsBoundedSMul`, ultrametricity
   and completeness. A new foundational `BanachModule` class would mostly
   repackage these assumptions and risk duplicate structures or unnecessary
   completeness hypotheses. A local abbreviation is harmless if useful.
   The distinction between contractive action and an action bounded by
   `C‖a‖‖x‖` is now explicit. The adapted-norm comparison in §0.3 supplies
   a contractive model for the latter, with `‖x‖≤‖x‖'≤C‖x‖`; exact
   isometries must still refer to the selected norm.

2. **Keep the output-first matrix convention and name its transpose
   adapter.** Mathlib's `LinearMap.toMatrix_apply` gives output coordinates
   of an input basis vector. The current
   [LocallyAnalyticDistributions PR #854, Convention 2 and §4.1](https://github.com/TauCetiProject/TauCetiRoadmap/blob/aa2639b7433a688a21bc314d7e05c453188aeb4b/TauCetiRoadmap/LocallyAnalyticDistributions/README.md)
   uses input-first coefficients but explicitly identifies them with
   `matrixCoeff u j i` from this roadmap. Its output-coordinate bounds
   `r_j=sup_i ‖b_ij‖` likewise match CompactOperators' `rowNorm j`.
   There is therefore no conflicting convention to resolve by reversing
   our existing API. Section 2.6 now specifies both actions and composition
   orders, null columns versus uniform output decay, and the distinction
   between reindexing coefficients and taking an operator on the dual.
   `matrixCoeffInputFirst` is the explicit adapter in the prototype.

   This is a consumer-roadmap convention, not evidence of a landed
   nonarchimedean matrix implementation. Searches for the relevant names
   and inspection of Tau Ceti's `Analysis/Normed` tree did not locate a
   competing `c₀` operator-matrix API. The existing local CompactOperators
   and QuaternionicModularForms conventions remain compatible.

3. **Make the basis and model formulations interconvertible.** Keep
   `IsONable` as existence of a linear isometry with `C₀(I,R)`, and add
   the fixed-index basis equivalence under complete ring/module hypotheses.
   A specified basis gives a specified coordinate isometry and unique
   unconditional expansion; the inverse construction pulls back coordinate
   vectors. Completeness cannot be omitted: finite-support sequences have
   dense orthonormal span but do not give the complete model. Mathlib's
   [unconditional Schauder bases](https://github.com/leanprover-community/mathlib4/blob/bbc4475e9e8fd25fbc8e26d636dd8b37be8f105a/Mathlib/Analysis/Normed/Module/Bases.lean)
   supply the field-valued comparison; their normed-field assumptions do
   not replace the coefficient-ring version here. The prototype now states
   the chosen-basis construction and the fixed-index equivalence explicitly.

4. **Separate normed Tate data from the existing topological class.**
   The proposed `NormedRing.IsTate` concerns a specified norm and an exactly
   scaling unit. Tau Ceti's landed
   [Huber definitions](https://github.com/TauCetiProject/TauCeti/blob/ea3f6eafadd29eb5e5068b3708b4c7a3e132b2e9/TauCeti/RingTheory/Huber/Basic.lean)
   use `IsPseudoUniformizer` for a topologically nilpotent unit and
   `IsTateRing` for a Huber ring containing one. Its
   [normed comparisons](https://github.com/TauCetiProject/TauCeti/blob/ea3f6eafadd29eb5e5068b3708b4c7a3e132b2e9/TauCeti/RingTheory/Huber/Normed.lean)
   already prove `IsPseudoUniformizer.of_norm_lt_one` and
   `IsTateRing.of_isUnit_norm_lt_one`; reuse them. Neither Tate condition
   includes completeness. The converse chooses a ring of definition,
   a suitable positive power of a pseudo-uniformiser and a gauge parameter.
   It produces a normed Tate model only with separation and nontriviality,
   not a theorem that every pre-existing compatible norm has exact scaling.
   Section 0.4 makes both directions and their different hypotheses explicit.
   Its example `N(x)=max(|x|_p,|x|_p²)` on `ℚ_p` gives the usual topology
   but no multiplicative unit of norm less than one: for `|ϖ|_p=r<1`,
   `N(ϖ)N(ϖ⁻¹)=r⁻¹>1`.
   The Mathlib-only prototype proves topological nilpotence from its normed
   datum without duplicating Tau Ceti's Huber classes.

5. **Retain the annular example as motivation.** Section 5.6 remains a
   coefficient-ring example motivated by boundary weight calculations in
   Liu–Wan–Xiao. The discontinued downstream roadmap is no longer an
   ownership or dependency entry.

This recheck used Tau Ceti commit
`ea3f6eafadd29eb5e5068b3708b4c7a3e132b2e9` and open PR #854 at head
`aa2639b7433a688a21bc314d7e05c453188aeb4b`, specifically its module, basis
and matrix contracts. The earlier PR snapshots below record the original
broader review; this follow-up does not claim to re-audit all their contents.

## Incorporation of PR #23

The complete two-file diff was read. PR #23 was open, with head
`77b47a7c501d2cbcca5be670262597c4e7558d8f` and base
`eefb3d91f34b27d0bc7822140fa85fecae029884`. No review comments were
returned at inspection. Its additions are incorporated into the relevant
layers rather than appended as a second specification. The existing
two-level section numbering is retained; third-level references in the
consumer PRs should be updated to the corresponding sections below.

The following groups cover all the requested handoffs, including requests
that merely designate this roadmap as supplier rather than add a theorem.

| # | PR #23 request | Revised location and treatment | Consumer |
| --- | --- | --- | --- |
| 1 | `tateGauge`, `exists_tateSeminorm`, kernel, equivalence and radius-power formulas | §0.4; same named prototype targets, with membership of the unit in the ring of definition explicit | #817 §R0.4 |
| 2 | Finite Banach modules over Noetherian bases | §1.4; retains Banach–Tate generality | #854 §4.1 |
| 3 | Scalar action on the native discrete `C₀` carrier | §2.1 | #854 §4.1 |
| 4 | Extension from bounded families | §2.1; distinguish construction from the continuity-to-bound converse | #854 §4.1 |
| 5 | Orthonormal and potentially orthonormal modules | §2.2; corrected coefficient-norm definition | #854 §4.1 |
| 6 | (Pr), lifting and finite projectivity | §2.2 | #854 §4.2 |
| 7 | Countable-type orthogonalisation | §2.4; no discrete valuation imposed | #817 §R0 |
| 8 | `exists_continuousLinearEquiv_prod_of_countableType`, completed scalar extension | §2.4; strict splitting is independent of the imported tensor construction | #813 §R3.6 |
| 9 | Matrices and their convention | §2.6; output index first, explicitly transpose for the consumer | #854 §4.1 |
| 10 | Finite coordinate truncations | §2.6 | #854 §4.1 |
| 11 | Approximation on closed finite submodules | §2.6; retain closedness without Noetherianity | #854 §4.1 |
| 12 | `exists_finset_norm_le` | §2.6; Noetherian Banach–Tate coefficients, no freeness requirement | #854 §4.1 |
| 13 | `norm_toCLMEquiv_eq_iSup_coeff`, `mem_range_amiceTransform_iff` | §3.4 and same named prototype targets; native measure and series carriers | #780 §2.5 |
| 14 | `existsUnique_integral_iff_norm_le_one` | §3.4; unique extension specified on integral test functions, field dual norm only | #780 §2.5 |
| 15 | `phiMeasure`, `pMultiplesIndicator`, `weightMeasure`, `existsUnique_psiMeasure`, `amiceTransform_phiMeasure` | §3.4; the restriction-and-division construction has no mass normalisation | #780 §§2.2, 2.11 |
| 16 | Disc stages, inclusions and locally polynomial functions | §§4.2–4.3; injectivity now has a coefficient hypothesis | #854 §0.1 |
| 17 | Amice basis and Mahler analyticity criterion | §4.4; module-valued coefficient theorem, field-valued corollaries | #854 §0.1 |
| 18 | The stage-bounded distribution carrier | §4.7; algebraic union and compatible stage functionals, without a global topology | #854 §0.1 |
| 19 | `amiceDualNorm`, `amiceDiscNorm` and both comparison inequalities | §4.7 and same named prototype targets; factorial multiplies the moment | #854 §1.1 |
| 20 | Dirac transform and additive convolution | §4.7; compare with the later general distribution construction | #854 §1.4 |
| 21 | Unit decomposition and weight parameters for all primes | §§5.1–5.2; sign at two, topologically nilpotent coordinates for rings | #780 §3a.1 |
| 22 | `exists_character_of_hasEval`, `eq_aeval_binomialSeries`, `existsUnique_character_of_norm_lt_one`, unique algebra specialisations and Amice/group-algebra compatibility | §5.3; separate adic and normed targets, import the generic completed group algebra and generic measure comparison | #780 §§3a.1, 4.5 |
| 23 | `extendIntegralMeasure`, `weightTest`, `measureFun`, its bound and injectivity | §5.3; reuse generic coefficient extension and the existing character set | #780 §3a.1 |

`Suggested.lean` is representative, as in the merged models, and does not
repeat every target in the table. Its field-valued `measurePairing` avoids
inventing a second coefficient-extension construction; the integral
`measureFun` contract follows by composing the supplier's extension.
The prototype takes the chosen generator and unit decomposition as data.
The README fixes the production choice `γ=exp(q)`.

## Mathematical findings

1. **The old orthonormal-family predicate was too weak over rings.** It
   maximised `‖a_i e_i‖`, not `‖a_i‖`. For `R=ℚ_p⟨T⟩` and `E=ℚ_p`
   with action through evaluation at zero, the singleton `1` passes the
   old predicate although `T` annihilates it. The new definition controls
   scalar coefficients and implies linear independence.

2. **Coefficient evaluation and level transitions need injectivity
   hypotheses.** For `E=𝔽_p`, the coefficient vector of `X^p−X` is
   nonzero, but every re-expansion `X=b+pY` is zero. Sections 4.1–4.4
   distinguish coefficients from functions and require, for example,
   `p`-torsion-freeness for injectivity. Banach `ℚ_p`-modules satisfy it.
   The Amice diagonal gives an explicit proof route.

3. **The old distribution norm had the factorial on the wrong side.**
   PR #23 correctly fixes this: `D_h=sup |b_n| |⌊n/p^h⌋!|` because the
   basis vector is `⌊n/p^h⌋! binom(x,n)`. The inequalities
   `S_h≤D_h≤p S_(h+1)` are retained. Every stage must be bounded;
   a bound at one stage is not the locally analytic dual. See
   [Colmez II.2](https://webusers.imj-prg.fr/~pierre.colmez/fonctionsdunevariable.pdf)
   and [Rodrigues Jacinto–Williams, Theorem 3.43](https://arxiv.org/abs/2309.15692).

4. **The triangular-matrix test violated its own column hypothesis.**
   A matrix with entry `p` at every position below the diagonal has
   non-null columns, so it does not act on `c₀`. The revised test is
   `1+pS`, with `S` the shift, and the theorem explicitly requires null
   columns. The upper-triangular part has finite columns and bounded inverse.

5. **The polynomial norm check confused two norms.** The Gauss norm of
   `x^p−x` is one. Its continuous sup norm on `ℤ_p`, hence its Mahler
   coefficient sup norm, is `p⁻¹`. At two, `x²−x=2binom(x,2)` makes
   the discrepancy immediate.

6. **The van der Put example omitted the leading digit.** For `f(x)=x`,
   the coefficient at `n` is that digit times `p^(ℓ(n)−1)`, not simply
   `p^(ℓ(n)−1)`. The new description gives the general subtraction formula.

7. **The reduction-degree claim in the Amice proof was too strong.**
   Colmez's Lemma I.4.9 gives degree at most the block degree on earlier
   discs, not strictly smaller in every case. Section 4.4 uses the correct
   finite block reduction and requires reconciliation of the disc ordering.

8. **Some norm-one assertions need field or coefficient bounds.**
   Multiplication by a continuous function is bounded by its sup norm.
   Compactness bounds a Banach-algebra-valued character but does not force
   all its values to have norm one. For example, the principal character
   `s↦1+p⁻¹sε` in a dual-number algebra with the maximum norm has a value
   of norm `p`. Field-valued characters do have norm-one values. The
   revised §§3.2, 4.6 and 5.2–5.5 distinguish these cases.

9. **Locally polynomial modules were incorrectly called free in general.**
   Their coordinate module is `E^(p^h(k+1))`; the stated free rank applies
   when `E=R`. Integral disc bases use `((x−a)/p^h)^j`, since `p^h` is
   not a unit in integral coefficients.

10. **The prime two needs actual separate formulas.** The sign section
    modulo four is not the limit of repeated squaring. The generator is
    `exp(4)`, since `exp(2)` does not converge. A parameter of norm
    `2^(−1/2)` is on the excluded level-one boundary and is analytic at
    level two. Integral `ℤ₂[C₂]⟦T⟧` remains local; its two field-valued
    characters do not split it integrally.

11. **Topological and numerical bounds were conflated.** Ring norms
    inducing the same topology need power comparisons in general, as in
    the corrected [Johansson–Newton §2.1](https://arxiv.org/abs/1604.07739).
    The operator norm is an infimum of bounds or supremum of ratios,
    not automatically the supremum of values on the unit ball. The
    identity and Neumann inverse have norm zero on the zero module.
    Rounding a norm gives the strict lower comparison only away from zero.

12. **The Tate gauge is a seminorm before separation.** PR #23's
    requirements that `ϖ∈A₀` and that its powers give a neighbourhood
    basis are retained, together with the zero-ring and nonmultiplicative
    examples. A unit outside the ring of definition can even destroy the
    ultrametric inequality. The numerical gauge is not canonical; its
    topology is. See [Kedlaya–Liu, Remark 2.4.4](https://arxiv.org/abs/1301.0792).

13. **Finite-coordinate approximation needs closedness or a supplier
    theorem providing it.** Noetherianity supplies closedness in the
    relevant model-space result; it is not silently assumed over all
    Banach–Tate rings. Relative truncation error less than one actually
    gives equality with a finite coordinate maximum. The weaker bound
    requested in PR #23 remains the public interface.

14. **General coefficient algebras need algebraic series identities.**
    A proof by evaluating in scalar fields does not automatically detect
    nilpotents. The binomial/exponential comparison uses formal identities
    and justified Cauchy products. The adic and normed specialisation
    statements remain separate: a Banach `ℚ_p`-algebra need not have a
    linear topology over itself.

15. **The halo completion claim did not describe its coefficient carrier.**
    The old carrier allows arbitrary formal `U=p/T` tails, including
    `Σ U^j`. The `p`-adic completion of `ℤ_p[[T]][U]/(TU−p)` imposes
    additional decay and does not contain that arbitrary tail. Section 5.6
    specifies the full formal ring `ℤ_p[[T,U]]/(TU−p)`, its Laurent
    normal forms, and a distinct `T`-gauge topology. In that gauge
    `‖U‖=1`, so the partial geometric sums do not converge. The formal
    sum is still a valid ring element. This is consistent with the double
    formal-series notation in [Liu–Wan–Xiao §3.15](https://arxiv.org/abs/1412.2584).

16. **Halo specialisations need the correct field and topology.**
    There are no `ℚ_p`-points with `p⁻¹<|T|<1`. Joint detection uses
    `ℂ_p`-points; continuity for a chosen gauge does not assert an
    arbitrary Lipschitz bound. At two the finite group-ring factor adds
    `δ−1` to the full maximal ideal, even though `(p,T)=(T)` in the
    principal coefficient ring.

17. **Some old scope and status claims were too broad.** Continuous
    functions are uniformly approximable by locally constant ones; they
    are not all locally constant. General reflexivity claims are removed
    from scope. The scalar expansion of `κ(cz+d)` stays here, while the
    matrix-action cocycle and its ordering convention go to their operator
    owner. Candidate files with admitted proofs or admitted instances are
    not advertised as completed mathematics.

## Overlap and dependency decisions

The consuming PRs were read at their current heads, not only through the
descriptions in #23. Their supplier sections explicitly assign these
interfaces to p-adic functional analysis. The new roadmap implements that
division of responsibility:

* RestrictedPowerSeries owns the series carriers, norms, evaluation,
  translation, substitution and open-disc algebra. This roadmap applies
  those to disc charts and duality.
* LocallyAnalyticDistributions owns the limit topology, strong dual,
  general completed tensors, manifold extensions and geometric Mellin
  transform. The algebraic stage carrier and quantitative estimates live here.
* PadicMeasuresIwasawaAlgebras owns general clopen integration, measure
  topologies, coefficient extension and the generic completed-group-algebra
  comparison. This roadmap owns bounded Mahler duality, the integral dual
  ball, `φ,ψ` and the chosen Amice-coordinate compatibility.
* ProfiniteProPGroups supplies the inverse-limit algebra and procyclic
  coordinate. The finite-factor and universal-character comparisons are
  added here. NewtonPolygons keeps the complete-DVR preparation requested
  by PhD PR #22; it is not repeated in this roadmap.
* CompactOperators supplies complete continuity and Fredholm theory;
  local-field arithmetic and automorphic matrix actions stay with their
  respective roadmaps.

The dependency order is deliberately finer than whole roadmaps. The strict
splitting theorem precedes tensors; its base-extension corollary uses only
LocallyAnalyticDistributions §0.0. Similarly the generic measure/group-algebra
comparison in #780 §1.7 is independent of Amice, and precedes this roadmap's
coordinate comparison. These two routes do not create circular proofs.

These are source-aligned handoffs, not evidence that the targets have
already been implemented or that a new ownership change has been accepted.

## Format, sources and reproducibility

The structure follows the inspected merged
[OperatorTheory #126](https://github.com/TauCetiProject/TauCetiRoadmap/pull/126)
and [GeometricMeasureTheory #828](https://github.com/TauCetiProject/TauCetiRoadmap/pull/828),
with [AnalyticToricGeometry #281](https://github.com/TauCetiProject/TauCetiRoadmap/pull/281)
and [AdicSpaces #80](https://github.com/TauCetiProject/TauCetiRoadmap/pull/80)
as additional models inspected for the preceding revisions. The
[contribution guidelines](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/CONTRIBUTING.md)
call for a definitive README, native library vocabulary, grounded layers,
explicit conventions, representative Lean interfaces, required checks and
honest review attribution. Historical findings and source status stay in
this file. `metadata.toml` files the roadmap under `math.NT`.

| Source | Inspected revision |
| --- | --- |
| PhD local baseline | `eefb3d91f34b27d0bc7822140fa85fecae029884` |
| PhD #23 | `77b47a7c501d2cbcca5be670262597c4e7558d8f` |
| TauCetiRoadmap #780 | `b5fdc51c197a09e7bc8d656e1e070a15815d36b3` |
| TauCetiRoadmap #854 | `84b4aff9523485ea44083ef2f20c4a39fc242270` |
| TauCetiRoadmap #817 | `29dfd5af03163501630db9e09eebeb29a2e1209a` |
| TauCetiRoadmap #813 | `302a49597c41fff57193d728474d231fd10ef77b` |
| TauCetiRoadmap merged comparison snapshot | `97199a4ed890b401e523e38ed11097350518302c` |
| Local Mathlib | `bbc4475e9e8fd25fbc8e26d636dd8b37be8f105a` |
| Lean toolchain | `leanprover/lean4:v4.33.0-rc1` |

The four consuming Tau Ceti PRs were open at inspection. Their current
supplier sections supersede the earlier snapshots used in the restricted
series coordination survey.

Current Mathlib's
[Amice transform file](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/Padics/Measure/AmiceTransform.lean)
was inspected at file blob `b770008a9a161d9325e4f771610cf331c89b3d6d`.
It supplies the native transform, moment extensionality and integral linear
equivalence. Convolution is in `Measure/Monoid`. These files postdate the
local pin, hence the prototype's small compatibility definition. Integration
must reuse those declarations and add comparisons, not duplicate them.

Representative files under `PhD/TauCeti/Code/PadicFunctionalAnalysis`,
including `ModelSpace/Basic.lean`, `ModelSpace/Closed.lean` and
`CountableType.lean`, contain admitted targets, including instances.
The old roadmap's historical status table was not repeated as a current
proof audit. The independent `PhD/Main` source remains a possible migration
source whose provenance and transitive axioms need checking when used.

## Validation

The mathematical review includes the counterexamples and boundary checks
above, comparison with the cited primary sources, and a section-by-section
check against PR #23 and its consuming roadmaps. The original roadmap is
preserved. No changes were made to a remote PR or to production imports.

The command

```sh
lake env lean PhD/TauCeti/RoadmapsNew/PadicFunctionalAnalysis/Suggested.lean
```

completed successfully again on 14 October at the recorded pin, with only the 21 expected
warnings for admitted theorem/example targets. Definitions and the coordinate
vector's continuity/decay proofs elaborate without admitted instances. The
new normed-to-topological nilpotence lemma is proved; the two basis/model
theorems are additional admitted targets. The input-first matrix adapter has
a definitional body.
This checks the interfaces, not the truth of the admitted targets. No full
repository build was needed for this isolated roadmap package.

The follow-up changes only this package's README, representative interfaces
and review note. Local links were checked, the removed dependency was searched
for, and matrix conventions were compared with the existing compact-operator
and quaternionic roadmaps.

The original revision also gave the restricted-series README and coordination note a narrow
ownership clarification: the Amice interfaces now explicitly point here,
while measure and distribution topologies remain with their consuming
roadmaps. No restricted-series theorem or Lean file was changed.
