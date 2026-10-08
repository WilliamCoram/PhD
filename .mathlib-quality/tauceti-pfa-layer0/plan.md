# Development Plan: p-adic functional analysis, Layer 0 (ultrametric sums and nonarchimedean Banach modules)

Board: `.mathlib-quality/tauceti-pfa-layer0/` (named; the default board path belongs to another
project, and `tauceti-of-layer0/` is a parallel board — never touch it or a sentinel that names
another board). Specification: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, Layer 0
(§0.1–§0.4) and its Examples. Code: `PhD/TauCeti/Code/PadicFunctionalAnalysis/`, module prefix
`PhD.TauCeti.Code.PadicFunctionalAnalysis`, importing **Mathlib only** — never `PhD.Main.*`
(CI-gated two-chain rule). Planned 2026-09-18.

## Goal

The bookkeeping that every later layer of the roadmap uses, stated once, for a nonarchimedean
normed ring `R` (`[NormedRing R] [IsUltrametricDist R]`, plus `[NormOneClass R]`,
`[CompleteSpace R]` where stated) and normed `R`-modules
(`[NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [IsUltrametricDist M]`):

```lean
-- §0.1  the unique dominant term (Sums.lean)
theorem IsUltrametricDist.norm_tsum_eq_of_forall_lt (hf : Summable f) {i₀ : ι}
    (hlt : ∀ i, i ≠ i₀ → ‖f i‖ < ‖f i₀‖) : ‖∑' i, f i‖ = ‖f i₀‖
-- §0.2  the unit ball and the Neumann series (UnitBall.lean)
def Subring.unitClosedBall (R) [SeminormedRing R] [NormOneClass R] [IsUltrametricDist R] : Subring R
theorem NormedRing.isUnit_iff_isUnit_mk (a : unitClosedBall R) :
    IsUnit a ↔ IsUnit (Ideal.Quotient.mk (openUnitBallIdeal R) a)
-- §0.4  Tate normed rings and the scaling trick (Tate.lean)
structure NormedRing.PseudoUniformizer (R) [NormedRing R]   -- unit, isMultiplicative, norm_lt_one
class NormedRing.IsTate (R) [NormedRing R] : Prop
theorem PseudoUniformizer.existsUnique_zpow_norm_smul_mem_Ioc (hδ : 0 < δ) (hm : m ≠ 0) :
    ∃! n : ℤ, ‖((ϖ.unit ^ n : Rˣ) : R) • m‖ ∈ Set.Ioc (δ * ‖(ϖ : R)‖) δ
theorem NormedRing.isTate_of_normedAlgebra (K R) … [NormedAlgebra K R] [NormOneClass R] : IsTate R
-- §0.4.5 / §0.4.6  the two Huber bridges, and the round trip (Huber.lean, GaugeNorm.lean)
theorem PseudoUniformizer.isAdic_ideal : IsAdic ϖ.ideal                          -- MILESTONE M1
theorem Subring.gaugeNorm_le_zpow_iff … : A₀.gaugeNorm ϖ a r ≤ a ^ (-n) ↔ r ∈ ϖ ^ n • A₀
noncomputable def Subring.gaugeRingNorm … : RingNorm A                           -- MILESTONE M2
theorem PseudoUniformizer.gaugeNorm_unitClosedBall (r : R) :
    (unitClosedBall R).gaugeNorm ϖ.unit ‖(ϖ : R)‖⁻¹ r = Real.zpowCeil ‖(ϖ : R)‖ ‖r‖
```

together with: null families on a product, iterated sums and bounded biadditive maps (§0.1.4–5);
ball ideals, the linear topology of `R⁰`, the Jacobson radical, the local ring of a normed field
(§0.2.1, §0.2.3); the norm criteria for power-boundedness and topological nilpotency (§0.2.1–2);
multiplicative elements (§0.2.4); the missing module instances and the transfer of completeness
(§0.3.1–2); Johansson–Newton's Lemmas 2.1.6–2.1.7 (§0.3.2); the rescaled norm (§0.3.3); residue
rings and modules (§0.3.4); the valuation `v_ϖ` (§0.4.3); and the roadmap's worked examples.

## References

| Tag | Reference | Used for |
|---|---|---|
| [RM] | `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, Layer 0 | the specification; every leaf discharges a numbered clause |
| [JN] | Johansson–Newton, *Extended eigenvarieties for overconvergent cohomology*, arXiv:1604.07739v4, §2.1 — `references/jn.txt` (Def 2.1.1 l. 475, "multiplicative" l. 487, Def 2.1.2 l. 489, unit remark l. 496, Remark 2.1.3 l. 499, Def 2.1.4 l. 514 and remark l. 519, Lemma 2.1.6 l. 565, Lemma 2.1.7 l. 605) | Tate normed rings, `v_ϖ`, both Huber bridges, norm comparison |
| [Bel] | Bellaïche, *The Eigenbook*, draft §II.1 — `references/bellaiche.txt` (Exercise II.1.1 l. 1963, footnote 1 p. 56 l. ~2030, Hypothesis II.1.11 l. 2074, `R⁰`, `R̃`, `M⁰`, `M̃` l. 2078, Lemma II.1.12 l. 2083, Theorem II.1.13 l. 2108) | multiplicative elements, residue modules, the rescaled norm |
| [Buz07] | Buzzard, *Eigenvarieties*, §2 — `references/buzzard.txt` (`ρ` l. 156, "renormalise" l. 269) | the scaling trick |
| [Sch] | Schneider, *Nonarchimedean Functional Analysis* (lecture-notes version) — `references/schneider.txt` (Lemma 1.2 l. 184, series remark l. 625, §5.B quotient seminorm l. 970, Prop 8.3 l. 2281, Prop 10.1 l. 2948) | unit ball of a field, sums, quotient norms, the rescaled norm |
| [Wed] | Wedhorn, *Adic Spaces*, arXiv:1910.05934 — `references/wedhorn.txt` (Def 5.25 l. 1569, Def 5.27 l. 1589, Example 5.29 l. 1606, Prop 5.30 l. 1619, Def 6.1 l. 2054, Def 6.10 l. 2161, Example 6.13 l. 2170, Prop 6.14 l. 2176, Cor 6.15 l. 2184) | boundedness vocabulary, the Huber side of both bridges |
| [Col10] | Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 — `references/colmez.txt` (Prop 1.1.5 l. 117, rescaled valuation l. 129) | the rescaled norm |
| [Mathlib] | pinned Mathlib (`lean4 v4.33.0-rc1`) | see the inventory |
| [PR] | mathlib4#40013 (W. Coram), `Mathlib/Topology/Algebra/{Bounded,PowerBounded}.lean` — diff at `references/pr40013.diff` | the exact names and shapes of the seam definitions |
| [SRC] | `PhD/Main/TateFredholm/{00_Tate, 01_OperatorNorm, 07_Residue, 08_BaseChange}.lean`, `HandClean/00_TateRings.lean`, `PhD/Main/LWX/05_Sharpness.lean`, `PhD/Main/ForMathlib/Analysis/Normed/Ring/{PowerBounded, TopologicallyNilpotent}.lean` at `747bb77` | **read-only reference for proof ideas** (sorry-free, different presentation); never imported, never mirrored; cited per leaf as "[SRC] File.decl" |

## Mathlib inventory (every name verified by elaboration, `scratch/names.lean`, `names2.lean`)

| Concept | Mathlib status | Our action |
|---|---|---|
| Null family ⇔ summable (complete nonarchimedean group) | `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`; `IsUltrametricDist.nonarchimedeanAddGroup` | USE; no restatement |
| `‖∑' f‖ ≤ ⨆ ‖f i‖` | **present**: `IsUltrametricDist.norm_tsum_le`, `nnnorm_tsum_le`, `norm_tsum_le_of_forall_le(_of_nonneg)` | USE (⚠ the roadmap says it is absent — erratum E1) |
| strict bound, unique dominant term for `tsum` | absent (finite pairwise-distinct form only: `norm_sum_eq_sup'_of_pairwise_ne`) | PROVE |
| iterated sums | `Summable.tsum_prod'`, `Summable.prod_factor`, `Summable.tsum_comm'`; ring products `tsum_mul_tsum_of_nonarchimedean` | USE; PROVE the null-family and biadditive forms |
| closed unit ball | `Submonoid.unitClosedBall` (a submonoid only) | DEFINE `Subring.unitClosedBall` extending it |
| ball ideals, linear topology of `R⁰` | absent | DEFINE + instance |
| topological nilpotency | `IsTopologicallyNilpotent`, `topologicalNilradical`, `IsTopologicallyNilpotent.mem_topologicalNilradical_iff`; `tendsto_pow_atTop_nhds_zero_of_norm_lt_one` | USE; wrap in dot notation |
| bounded / power-bounded | **absent** (mathlib4#40013 open; Tau Ceti has `TauCeti.Huber.IsPowerBounded`, not a dependency here) | SEAM: reproduce the two definitions verbatim from the PR in `PowerBounded.lean`; delete at migration |
| Neumann series | `Units.oneSub`, `summable_geometric_of_norm_lt_one`, `mul_neg_geom_series`, `geom_series_mul_neg`, `tsum_geometric_le_of_norm_lt_one` | USE; PROVE the ultrametric equalities |
| Jacobson radical, local rings | `Ideal.mem_jacobson_bot`, `IsLocalRing.of_nonunits_add`, `IsLocalRing.maximalIdeal` | USE |
| multiplicative elements | `NormMulClass` (whole-ring) only | DEFINE `NormedRing.IsMultiplicative` |
| `IsUltrametricDist` on `X × Y`, on a quotient; `IsBoundedSMul R ↥S` | absent (checked by `inferInstance`); `Pi`, subtypes, `Submodule.Quotient.instIsBoundedSMul`, `Submodule.Quotient.completeSpace` present | PROVE the three instances |
| completeness along a bi-bounded equivalence | `AddMonoidHomClass.lipschitz_of_bound`, `completeSpace_congr`, `AntilipschitzWith.isUniformEmbedding` | PROVE one lemma |
| Tate normed rings, pseudo-uniformisers, `v_ϖ` | absent | DEFINE |
| `Real.logb`, floors, `zpow` monotonicity | `Real.rpow_logb`, `Real.logb_pos_iff_of_base_lt_one`, `Int.floor_le`, `Int.lt_floor_add_one`, `zpow_le_zpow_right_of_le_one₀`, … (⚠ no `Real.logb_zpow`; use `Real.logb_rpow` + `Real.rpow_intCast`) | USE |
| bundled norms | `AddGroupNorm`, `AddGroupNorm.toNormedAddCommGroup`, `RingNorm` | USE for `rescaledNorm`, `gaugeRingNorm` |
| adic topology | `IsAdic`, `isAdic_iff`, `Ideal.span_singleton_pow`, `Ideal.mem_span_singleton` | USE |
| Huber / Tate rings (`PairOfDefinition`, `IsTateRing`) | **absent** (Tau Ceti has them, not a dependency here) | SEAM: state the four components in Mathlib vocabulary (`IsOpen`, `Ideal.FG`, `IsAdic`, `IsTopologicallyNilpotent`) |
| quotient module over quotient ring | instance in `Mathlib/Algebra/Module/Torsion/Basic.lean` (needs the import) | USE |
| `ℚ_[p]`, `ℤ_[p]`, `ℂ_[p]` | `PadicInt.subring`, `PadicInt.isUnit_iff`, `Padic.norm_eq_zpow_neg_valuation`, `PadicInt.ker_toZMod`, `ZMod.ringHom_surjective`, `PadicComplex.norm_extends`, `IsAlgClosed.exists_pow_nat_eq` | USE in `Examples.lean` |

## File structure (as for a Tau Ceti PR; Tau Ceti home in each module docstring)

| File | Roadmap | Tau Ceti home | Contents |
|---|---|---|---|
| `Sums.lean` | §0.1 | `TauCeti/Analysis/Normed/Group/Ultra/InfiniteSum.lean` | largest norm attained; strict bound; dominant term; null families on a product; iterated sums; biadditive maps |
| `UnitBall.lean` | §0.2.1, §0.2.3 | `…/Normed/Ring/Ultra/UnitBall.lean` | `Subring.unitClosedBall`, `closedBallIdeal`, `openUnitBallIdeal`, linear topology, Neumann norms, units mod `R⁰⁰`, Jacobson radical, local ring of a field |
| `PowerBounded.lean` | §0.2.1–2 | `…/Normed/Ring/Ultra/PowerBounded.lean` | **seam** definitions (mathlib4#40013) + norm criteria |
| `Multiplicative.lean` | §0.2.4 | `…/Normed/Ring/Ultra/Multiplicative.lean` | `NormedRing.IsMultiplicative` and its API, units, modules |
| `Module.lean` | §0.3.1–2 | `…/Normed/Module/Ultra/Basic.lean` | three instances; completeness along a bi-bounded equivalence |
| `Tate.lean` | §0.4.1–4 | `…/Normed/Ring/Ultra/Tate.lean` | `PseudoUniformizer`, `IsTate`, scaling trick, `val`, bridge from normed algebras |
| `NormComparison.lean` | §0.3.2 | `…/Normed/Ring/Ultra/NormComparison.lean` | [JN] Lemmas 2.1.6–2.1.7 |
| `Rescale.lean` | §0.3.3 | `…/Normed/Module/Ultra/Rescale.lean` | `Real.zpowCeil`, `Rescaled ϖ M`, its instances |
| `Residue.lean` | §0.3.4 | `…/Normed/Module/Ultra/Residue.lean` | `Submodule.unitClosedBall`, `ϖ.ideal`, `ResidueRing`, `ResidueModule` |
| `GaugeNorm.lean` | §0.4.6 | `…/Normed/Ring/Ultra/GaugeNorm.lean` | the gauge norm of a Tate ring (Mathlib-only, independent) |
| `Huber.lean` | §0.4.5 | `…/Normed/Ring/Ultra/Huber.lean` | **seam**: open subring, ideal powers = balls, `IsAdic`, the round trip |
| `Examples.lean` | Examples, §0.2.2, §0.4.7 | tests | `ℚ_p`, `ℤ_p`, `ℂ_p`, the two counterexamples |

Import graph: `Sums ← UnitBall`; `Multiplicative ← Tate ← {NormComparison, Rescale (+Module), Residue
(+UnitBall)}`; `{Residue, PowerBounded, GaugeNorm, Rescale} ← Huber ← Examples (+Rescale)`.
`PowerBounded`, `Module`, `GaugeNorm`, `Sums`, `Multiplicative` have no in-chain imports.

## Dependency graph (by ticket group)

```text
G1 Sums ──────────────→ G2 UnitBall (T009 needs T002) ─┐
G4 Multiplicative ──→ G6 Tate ──→ G7 NormComparison     ├─→ G9 Residue ─→ G10 Huber (M1) ─→ G12 Examples
G5 Module ─────────────┴──────→ G8 Rescale ────────────┘         ↑ (T036 only)     ↑
G3 PowerBounded ──────────────────────────────────────────────────┤                  │
G11 GaugeNorm (M2) ───────────────────────────────────────────────┘   G8 Rescale ────┘
```

## Generality and design decisions (binding for the tickets)

1. **Mathlib's vocabulary** ([RM] convention 1). No `BanachModule`, no `NonarchimedeanNormedRing`.
   Ultrametric = `IsUltrametricDist`; module = `Module` + `IsBoundedSMul`; multiplicative norm =
   `NormMulClass` / `NormSMulClass`.
2. **Weakest structure that carries the proof.** `SeminormedRing` / `SeminormedAddCommGroup` where
   no separation is used; `NormedAddCommGroup` exactly where `tsum` identities need `T2` or a vector
   must have positive norm; commutativity only where an `Ideal` quotient or `IsAdic` needs it
   (`isUnit_iff_isUnit_mk`, `Residue.lean`, `Huber.lean`, `GaugeNorm.lean`). Completeness only where a
   sum must exist.
3. **`IsTate` is a Prop, `PseudoUniformizer` is data** ([RM] convention 2), both in the namespace
   `NormedRing` (so nothing sits in the root namespace, [RM] convention 12). The structure has the
   three fields of [JN] Def 2.1.2 and no positivity field: `0 < ‖ϖ‖` is a theorem under
   `[NormOneClass R]`, which is [JN]'s `|1| = 1`. ⚠ Without `NormOneClass` the trivial ring is "Tate"
   (erratum E5); every lemma that needs positivity carries `[NormOneClass R]`. Given a
   pseudo-uniformiser, `[NormOneClass R]` is equivalent to `[Nontrivial R]`
   (`PseudoUniformizer.normOneClass_of_nontrivial`), so nothing is lost by the stronger-looking class.
4. **Two norms are two normed rings.** "Two norms on `R` inducing the same topology" is a ring
   isomorphism `e : R ≃+* S` between two normed rings, continuous both ways; "bounded-equivalent
   norms on `M`" is an equivalence with a bound in each direction, the bounds carried in the
   hypotheses ([RM] "never wrap a one-line bound in a new predicate"). [JN] Lemma 2.1.7's upper bound
   is proved for a *continuous ring homomorphism* `e : R →+* S` — bijectivity is never used — and
   the hypothesis `‖e ϖ‖ < 1` of [SRC] is dropped: it follows from continuity and multiplicativity.
   The exponent is explicit, `s = Real.logb ‖ϖ‖ ‖e ϖ‖`, so each statement has one conclusion.
5. **The rescaled norm lives on a type synonym** `Rescaled ϖ M`, indexed by the pseudo-uniformiser
   (which supplies `0 < ‖ϖ‖ < 1` without a `Fact`). Its real-variable core is `Real.zpowCeil c x`,
   defined by the sources' infimum formula, with the closed form `c ^ ⌊logb c x⌋` as a lemma.
   ⚠ `Rescaled ϖ M` needs `[IsUltrametricDist M]` (`zpowCeil` is not subadditive) and is a normed
   `R`-module only when the norm of `R` takes values in `‖ϖ‖ ^ ℤ ∪ {0}` (erratum E3):
   `isBoundedSMul_rescaled` is a theorem with that hypothesis, not an instance.
6. **Seams are declared, not hidden.** `PowerBounded.lean` reproduces `TopologicalRing.IsBounded`
   and `PowerBounded.IsPowerBounded` verbatim from mathlib4#40013; `Huber.lean` and `GaugeNorm.lean`
   state the Huber side in Mathlib's vocabulary, with the basis hypothesis
   `(𝓝 0).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ϖ ^ n • A₀` ([Wed] Example 6.13 / Cor 6.15) as the
   common interface: `hasBasis_nhds_zero_smul_unitClosedBall` produces it, `GaugeNorm.lean`
   consumes it, and `gaugeNorm_unitClosedBall` closes the loop. At migration these re-target
   `TauCeti.Huber.{IsPowerBounded, PairOfDefinition, IsTateRing, IsPseudoUniformizer}`.
7. **The gauge norm is a `RingNorm`**, with the topology statement as a `HasBasis` at `0`, which
   avoids putting a second `NormedRing` instance on `A`. `T2Space A` is used only for definiteness
   and `‖1‖ = 1`; the seminorm statements carry no separation hypothesis.
8. **One conclusion per declaration.** [JN] 2.1.6 and 2.1.7 are split into their inequalities; the
   only bundled statements are `∃!` (the scaling trick) and the `Prop` structure fields.
9. **Imports are minimal, per file** (both Mathlib and Tau Ceti require it; `import Mathlib` costs
   8 684 jobs per file here). When a proof needs a lemma from an unimported module, add that module.

## Roadmap errata and clarifications found while planning

| # | Roadmap clause | Finding | Board action |
|---|---|---|---|
| E1 | "Existing Mathlib": "⚠ Mathlib has no bound `‖∑' i, f i‖ ≤ ⨆ i, ‖f i‖`"; §0.1.2 | false at the pin: `IsUltrametricDist.norm_tsum_le` | §0.1.2 reduces to "the supremum is attained"; README corrected |
| E2 | §0.2.3 "`R⁰⁰` is the unique maximal ideal of `R⁰` when the norm is multiplicative" | **false**: `ℚ_p⟨X⟩` with the Gauss norm has `R⁰/R⁰⁰ = 𝔽_p[X]` | replaced by `openUnitBallIdeal_le_jacobson_bot` (complete `R`) and `maximalIdeal_unitClosedBall` (normed fields); README corrected |
| E3 | §0.3.3 "on any normed `R`-module" | the rescaled module is a normed module over `R` only if `‖R‖ ⊆ ‖π‖ ^ ℤ ∪ {0}` (`ℂ_p`, `π = p`, `‖r‖ = p^{-1/2}`) | `isBoundedSMul_rescaled` carries the hypothesis; README clarified |
| E4 | Layer 0 Examples: "the Tate normed ring `ℚ_p⟨X⟩`" ; §0.4.7 `R⟨X⟩`, `Λ^{>1/p}[1/T]` | needs the normed ring `R⟨X⟩` of §4.1 / §5.6 | not on this board; README moves the example to Layer 4 |
| E5 | §0.4.1 "A Tate normed ring is nontrivial" | false without `‖1‖ = 1` (the zero ring); with it, it is `NormOneClass.nontrivial` | lemmas carry `[NormOneClass R]`; README corrected |
| E6 | §0.4.3 seam with `normAddVal` | `NormedField.normAddVal` is Newton-polygons Layer 1, not yet in this chain | EXTERNAL: stated on whichever board lands second; recorded, not ticketed |
| E7 | §0.4.5 "State it as an instance of `TauCeti.Huber.IsTateRing`" | not a dependency of this repository | stated in Mathlib vocabulary (decision 6) |
| E8 | §0.1.2 "the supremum is attained when some `f i ≠ 0`"; §0.1.3 "If `‖f i‖ < B` for every `i` and `f → 0` cofinitely" | the right hypothesis for §0.1.2 is a nonempty index type; §0.1.3 needs `0 < B` (empty index type) and does **not** need nullity or summability (`∑' f = 0` otherwise) | skeleton states them so (L1.2–L1.4); README corrected |

## Build and verification protocol

- Skeleton gate: `lake build PhD.TauCeti.Code.PadicFunctionalAnalysis.Examples
  PhD.TauCeti.Code.PadicFunctionalAnalysis.NormComparison` (together they import all twelve files);
  must succeed with `sorry` warnings only. Verified 2026-09-18: 2 626 jobs, 0 errors.
- Import gate (CI): no `import PhD.Main.*` under `PhD/TauCeti/`.
- Each ticket: `lake build` of its module, then `#print axioms` on each declaration — only
  `propext`, `Classical.choice`, `Quot.sound`. `lake exe runLinter` on the module at cleanup.
- `/beastmode` runs inline as the main agent (user preference), one ticket at a time, naming this
  board. No `timeout` binary on this machine; use the tool timeout.
- The chain root `PhD/TauCeti.lean` gains the two leaf modules `Examples` and `NormComparison` in T045
  (together they import all twelve files; the root lists leaf modules only, as for `NewtonPolygons`).
  Append-only edit: another board may be editing the same file.
