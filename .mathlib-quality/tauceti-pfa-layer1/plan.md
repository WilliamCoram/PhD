# Development Plan: p-adic functional analysis, Layer 1 (bounded linear maps)

Board: `.mathlib-quality/tauceti-pfa-layer1/` (named; the default board path belongs to another
project, and the other `tauceti-*` boards are parallel boards — never touch them or a sentinel that
names another board). Specification: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`,
Layer 1 (§1.1–§1.4) and its Examples. Code: `PhD/TauCeti/Code/PadicFunctionalAnalysis/Operator/`,
module prefix `PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator`, importing **Mathlib and Layer 0
only** — never `PhD.Main.*` (CI-gated two-chain rule). Planned 2026-10-06, on top of the completed
Layer 0 board (`tauceti-pfa-layer0`, 2026-09-29). **COMPLETE 2026-10-06**: 47/47 tickets, sorry-free,
`lake build PhD.TauCeti` 3 619 jobs. Rename during execution: the two lemmas behind M2's Nakayama step
live in `NormedRing` (`NormedRing.forall_mem_of_forall_exists_eq_add_sum_smul_of_norm_lt_one`,
`NormedRing.exists_forall_exists_eq_sum_smul_norm_le`) because the parallel `tauceti-rag-layer2`
board declares field-scalar `Submodule.*` lemmas with the original names (theirs are special cases).

## Goal

The operator norm, the open mapping theorem and its companions, and the finiteness theorems, for
normed modules over a Tate normed ring `R` (`[NormedRing R] [NormOneClass R] [NormedRing.IsTate R]`,
Layer 0's class) — `M`, `N` normed `R`-modules (`[NormedAddCommGroup M] [Module R M]
[IsBoundedSMul R M]`), Banach where stated:

```lean
-- §1.1  the operator norm, scoped (Operator/Norm.lean, Operator/Banach.lean)
scoped instance ContinuousLinearMap.Ultra.instNorm : Norm (M →L[R] N)          -- Mathlib's formula
theorem ContinuousLinearMap.Ultra.continuous_iff_exists_bound [IsTate R] (f : M →ₗ[R] N) :
    Continuous f ↔ ∃ C, ∀ x, ‖f x‖ ≤ C * ‖x‖
theorem ContinuousLinearMap.Ultra.le_opNorm [IsTate R] (u : M →L[R] N) (x : M) : ‖u x‖ ≤ ‖u‖ * ‖x‖
scoped instance ContinuousLinearMap.Ultra.instNormedAddCommGroup : NormedAddCommGroup (M →L[R] N)
scoped instance ContinuousLinearMap.Ultra.instCompleteSpace [CompleteSpace N] : CompleteSpace (M →L[R] N)
scoped instance ContinuousLinearMap.Ultra.instNormedRing : NormedRing (M →L[R] M)
theorem ContinuousLinearMap.Ultra.instNormedAddCommGroup_eq :                   -- §1.1.6
    (instNormedAddCommGroup : NormedAddCommGroup (M →L[K] N)) = ContinuousLinearMap.toNormedAddCommGroup
-- §1.2  the open mapping theorem and its companions (OpenMapping, ClosedGraph, BanachSteinhaus, Pi)
theorem ContinuousLinearMap.Ultra.exists_preimage_norm_le [CompleteSpace M] [CompleteSpace N]
    (u : M →L[R] N) (hu : Surjective u) : ∃ C > 0, ∀ y, ∃ x, u x = y ∧ ‖x‖ ≤ C * ‖y‖   -- MILESTONE M1
noncomputable def ContinuousLinearMap.Ultra.quotKerEquivRangeL (hu : IsClosed (range u)) :
    (M ⧸ ker u) ≃L[R] range u
theorem ContinuousLinearMap.Ultra.continuous_of_isClosed_graph (f : M →ₗ[R] N)
    (hf : IsClosed (f.graph : Set (M × N))) : Continuous f
theorem ContinuousLinearMap.Ultra.banach_steinhaus (u : ι → M →L[R] N)
    (h : ∀ x, ∃ C, ∀ i, ‖u i x‖ ≤ C) : ∃ C, ∀ i, ‖u i‖ ≤ C
theorem ContinuousLinearMap.Ultra.opNorm_pi_eq (u : (ι → R) →L[R] M) : ‖u‖ = ⨆ i, ‖u (Pi.single i 1)‖
-- §1.4  finitely generated modules (Operator/Finite.lean)
theorem ContinuousLinearMap.Ultra.exists_bound_of_finite [Module.Finite R P] [CompleteSpace P]
    (φ : P →ₗ[R] M) : ∃ C, ∀ x, ‖φ x‖ ≤ C * ‖x‖                                     -- Buzzard 2.2
theorem Submodule.isClosed_of_isNoetherianRing [IsNoetherianRing R] [Module.Finite R M]
    (N : Submodule R M) : IsClosed (N : Set M)                                       -- MILESTONE M2
```

together with the Neumann series in `M →L[R] M` (§1.1.5), sums of operators (§1.1.4), the
sequential closed graph theorem and continuity of pointwise limits (§1.2.3–4), the nonarchimedean
Nakayama lemma for submodules and BGR 3.7.2/1 (§1.4.2), the existence of a Banach norm on a finitely
generated module (§1.4.1), and the roadmap's worked examples including the two counterexamples
(§1.1.2's `ℤ_p` with the squared norm, §1.4.3's non-closed principal ideal of `ℓ^∞(ℕ, ℚ_p)`).

## References

| Tag | Reference | Used for |
|---|---|---|
| [RM] | `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, Layer 1 (README lines 483–582) | the specification; every leaf discharges a numbered clause |
| [JN] | Johansson–Newton, arXiv:1604.07739v4, §2.1 — `references/jn.txt` (Def 2.1.4 l. 514–525: boundedness l. 522, the operator norm l. 523, OMT l. 525; the BGR §3.7.2–3.7.3 transfer l. 526–531) | the norm, continuity = boundedness, OMT citation, §1.4.1 |
| [Sch] | Schneider, *Nonarchimedean Functional Analysis* (lecture notes) — `references/schneider.txt` (Prop 3.1 l. 520, its proof l. 536–546, Cor 3.2 l. 538, the warning l. 547–550, Prop 3.3 l. 551–588, Prop 4.13 Step 1 l. 903–913, Prop 6.15 l. 1683–1690, Example 2 after Cor 6.16 l. 1715–1718, Prop 8.3 l. 2281, Prop 8.5 l. 2322–2355, Prop 8.6 l. 2357–2372, Cor 8.7 l. 2373–2375) | continuity = boundedness, the sup formula and its warning, completeness, the Pi bound, Banach–Steinhaus, closed graph, open mapping |
| [Bel] | Bellaïche, *The Eigenbook*, draft §II.1 — `references/bellaiche.txt` (II.1.1 l. 1955–1989: the norm of `φ` l. 1975–1981, OMT l. 1983–1989) | the Banach module `Hom_R(M, N)`, submultiplicativity, the quantitative OMT |
| [Buz07] | Buzzard, *Eigenvarieties*, §2 — `references/buzzard.txt` (closed ideals l. 173, Prop 2.1 l. 182–189, Lemma 2.2 l. 201–210, the `ρ`-trick l. 266–272) | Buzzard's Lemma 2.2, the scaling trick |
| [BGR] | Bosch–Güntzer–Remmert, *Non-Archimedean Analysis* — `references/bgr-3.7.md` (3.7.2/1 l. 27, "immediate consequence" l. 35, 3.7.2/2 l. 39, 3.7.3/2 l. 56, 3.7.3/3 l. 60, 3.7.3/4 l. 68, 1.2.4/4 l. 135, 1.2.4/5 l. 138, 1.2.4/6 l. 142) | §1.4, the Neumann series, Nakayama |
| [Lud] | Ludwig, arXiv:2407.18073 — `references/ludwig.txt` (completeness l. 218–222, OMT l. 226–228, Lemma 2.14 l. 231–236, Lemma 2.24 l. 336–340, Remark 2.25 l. 345–358) | Buzzard 2.2 in Banach–Tate form, Bellaïche's Hypothesis 3.1.8 |
| [Mathlib] | pinned Mathlib (`lean4 v4.33.0-rc1`): `Analysis/Normed/Operator/{Basic,NormedSpace,Banach,BanachSteinhaus}.lean`, `Analysis/SpecificLimits/Normed.lean` (`Units.oneSub`) | the formula and every field-scalar proof we transport; see the inventory |
| [L0] | Layer 0 of this chain, `PhD/TauCeti/Code/PadicFunctionalAnalysis/{Tate,Multiplicative,Module,UnitBall,Sums}.lean` | `PseudoUniformizer`, `IsTate`, the scaling trick `existsUnique_zpow_norm_smul_mem_Ioc`, `norm_zpow_smul`, `IsMultiplicative.norm_smul`, `Submodule.instIsBoundedSMul`, `Prod.instIsUltrametricDist`, `norm_tsum_geometric`, `norm_one_sub_of_norm_lt_one`, `openUnitBallIdeal_le_jacobson_bot` |
| [RAG] | `PhD/TauCeti/Code/RigidAnalyticGeometry/BanachAlgebra/Noetherian.lean` (in-chain, field scalars) | the Nakayama route to BGR 3.7.2/1, **proof idea only** (not imported) |
| [SRC] | `PhD/Main/TateFredholm/{01_OperatorNorm, 05_Noetherian}.lean` at `747bb77` | **read-only reference for proof ideas** (sorry-free, different presentation); never imported |

## Mathlib inventory (every name verified by elaboration: `scratch/names.lean`, `names2.lean`, `names3.lean`)

| Concept | Mathlib status | Our action |
|---|---|---|
| operator norm, `opNorm_le_bound`, `le_opNorm`, `opNorm_comp_le`, completeness, `toNormedRing`, `exists_preimage_norm_le`, `isOpenMap`, `ContinuousLinearEquiv.ofBijective`, `continuous_of_isClosed_graph`, `banach_steinhaus`, `continuousLinearMapOfTendsto` | present for `NontriviallyNormedField` scalars only | RESTATE in `ContinuousLinearMap.Ultra`, proofs transported with the scaling trick |
| topology / norm on `M →L[R] N` over a normed ring | **absent** (`#synth` fails; the strong topology needs a normed field) | our scoped instances create no diamond over a ring |
| `Module R (M →L[R] N)` | present (`ContinuousLinearMap.module`), needs `SMulCommClass R R N`, i.e. **commutative `R`** | the `IsBoundedSMul` instance and `opNorm_smul_le` take `[NormedCommRing R]` |
| `ContinuousLinearMap.ring`, `HasSummableGeomSeries` from `CompleteSpace`, `Units.oneSub`, `Units.val_oneSub`, `Units.isOpen` | present | USE (§1.1.5 is these applied to the Banach ring `M →L[R] M`) |
| `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`, `IsUltrametricDist.norm_tsum_le` | present | USE (§1.1.4's convergence and bound are these, once the instances exist) |
| `NormedAddCommGroup.ext` | absent; `MetricSpace.ext`, `PseudoMetricSpace.ext` present | the agreement theorem goes through `MetricSpace.ext` and `cases` |
| `NormedAddCommGroup.ofCore` | present but takes a `NormedSpace.Core` (field) | the instance is built by hand from `AddGroupNorm.toNormedAddCommGroup` with `toNorm := instNorm` |
| Baire: `nonempty_interior_of_iUnion_of_closed`, `BaireSpace` for complete metric spaces | present (`Mathlib.Topology.Baire.CompleteMetrizable`) | USE |
| `LinearMap.mkContinuous`, `AddMonoidHomClass.continuous_of_bound`, `LinearMap.continuous_of_bound` | present for `Ring` scalars | USE |
| quotient norms: `Submodule.Quotient.{seminormedAddCommGroup, normedAddCommGroup, completeSpace, norm_mk_lt, norm_mk_le, instIsBoundedSMul}` | present; `instIsBoundedSMul` needs `SeminormedCommRing` scalars | strictness (§1.2.2) is stated over `[NormedCommRing R]` |
| `LinearMap.quotKerEquivRange`, `LinearMap.graph`, `graph_eq_range_prod`, `LinearEquiv.ofLeftInverse`, `IsSeqClosed.isClosed` | present | USE |
| `Pi.normedAddCommGroup`, `Pi.instIsBoundedSMul`, `Pi.instIsUltrametricDist`, `Pi.norm_single`, `norm_le_pi_norm`, `pi_eq_sum_univ`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` | present | USE |
| Nakayama: `Submodule.le_of_le_smul_of_le_jacobson_bot`; `Subsemiring.instModuleSubtypeMem` (a module over the unit ball) | present | USE with [L0] `openUnitBallIdeal_le_jacobson_bot` |
| `Submodule.topologicalClosure`, `isClosed_topologicalClosure`, `fg_iff_exists_fin_generating_family`, `Module.Finite.exists_fin'`, `isNoetherian_of_isNoetherianRing_of_finite` | present | USE |
| `IsBoundedSMul R C₀(I, R)` | **absent** (`#synth` fails; `Module R C₀` exists) | the `C₀` examples move to Layer 2 (erratum E15) |
| `lp B ∞`: `inftyNormedCommRing`, `inftyNormedAlgebra`, `NormOneClass`, `CompleteSpace`, `norm_apply_le_norm`, `norm_le_of_forall_le`, `memℓp_infty` | present; `IsUltrametricDist (lp E ∞)` **absent** | PROVE the instance (§1.4.3's counterexample ring) |
| `Padic.norm_p`, `Padic.norm_p_pow`, `PadicInt.norm_p_pow`, `PadicInt.norm_le_one` | present | USE in `Examples.lean` |

## File structure (as for a Tau Ceti PR; Tau Ceti home in each module docstring)

| File | Roadmap | Tau Ceti home | Contents |
|---|---|---|---|
| `Operator/Norm.lean` | §1.1.1–2, §1.1.6 | `TauCeti/Analysis/Normed/Operator/Ultra/Norm.lean` | scoped `Norm`, order lemmas, the scaling trick, continuity ⇔ boundedness, `le_opNorm`, the ratio supremum, `norm_eq_opNorm` |
| `Operator/Banach.lean` | §1.1.3–6 | `…/Ultra/Banach.lean` | scoped `NormedAddCommGroup`, `IsUltrametricDist`, `CompleteSpace`, `NormedRing`, `NormOneClass`, `IsBoundedSMul`; sums of operators; the Neumann series; `instNormedAddCommGroup_eq` |
| `Operator/OpenMapping.lean` | §1.2.1–2 | `…/Ultra/OpenMapping.lean` | the quantitative OMT, `isOpenMap`, bijective ⇒ equivalence, strictness |
| `Operator/ClosedGraph.lean` | §1.2.3 | `…/Ultra/ClosedGraph.lean` | closed graph theorem, sequential form |
| `Operator/BanachSteinhaus.lean` | §1.2.4 | `…/Ultra/BanachSteinhaus.lean` | uniform boundedness, continuity of pointwise limits |
| `Operator/Pi.lean` | §1.2.5 | `…/Ultra/Pi.lean` | maps out of `ι → R`: the bound, continuity, the norm |
| `Operator/Finite.lean` | §1.4.1–2 | `…/Ultra/Finite.lean` | Buzzard 2.2, Nakayama, BGR 3.7.2/1, closedness over Noetherian `R`, closed ideals, the Banach norm of a f.g. module |
| `Operator/Examples.lean` | Examples, §1.1.2, §1.4.3 | tests | `mulLeftL`, `(x, y) ↦ x + ϖ y`, the `ℚ_p` bijection, `PadicIntSq`, `ℓ^∞(ℕ, ℚ_p)` |

Import graph: `Tate (L0) ← Norm ← {Banach (+UnitBall), Pi, BanachSteinhaus}`;
`Norm (+Module L0) ← OpenMapping ← {ClosedGraph, Finite (+Pi, UnitBall)}`;
`{Banach, BanachSteinhaus, ClosedGraph, Finite} ← Examples`. Skeleton gate:
`lake build PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.Examples` (imports all eight files) —
verified 2026-10-06: 2 254 jobs, 0 errors, 75 `sorry`s.

## Dependency graph (by ticket group)

```text
G1 Norm ──→ G2 Banach ──→ G3 OpenMapping ──→ G4 ClosedGraph
   │                           │  (M1 = T012)
   ├──→ G6 Pi ─────────────────┴──→ G7 Finite (M2 = T023) ──→ G8 Examples ──→ T031 chain root
   └──→ G5 BanachSteinhaus ───────────────────────────────────────┘
```

## Generality and design decisions (binding for the tickets)

1. **One namespace, one scope.** Everything of Layer 1 about `M →L[R] N` lives in
   `ContinuousLinearMap.Ultra`; the instances are `scoped` there, so `open scoped
   ContinuousLinearMap.Ultra` activates the operator norm and nothing else does (roadmap convention
   6). Lemmas keep Mathlib's names (`le_opNorm`, `opNorm_comp_le`, `exists_preimage_norm_le`, …);
   since `ContinuousLinearMap.Ultra` is a child of `ContinuousLinearMap`, an unqualified
   `le_opNorm` inside the namespace is overloaded with Mathlib's field version — workers write
   `Ultra.le_opNorm` when the elaborator complains. At Mathlib-generalisation time these files are
   deleted, which is why the names coincide. The `Submodule`/`Ideal`/`Module.Finite` results of
   `Finite.lean` are named by their subject, as Mathlib would.
2. **Mathlib's formula, verbatim.** `instNorm` is `⟨fun u ↦ sInf {c | 0 ≤ c ∧ ∀ x, ‖u x‖ ≤ c * ‖x‖}⟩`,
   so `norm_eq_opNorm` is `rfl` for field scalars; the `NormedAddCommGroup` instance is built with
   `toNorm := instNorm` so that no second `Norm` instance appears (the metric comes from
   `AddGroupNorm.toNormedAddCommGroup`, `dist_eq := rfl`). The instance-level agreement
   `instNormedAddCommGroup_eq` is proved through `MetricSpace.ext` (Mathlib's instance carries the
   strong-topology uniformity by `replaceUniformity`, equal but not definitionally so).
3. **Weakest hypotheses that carry each proof** (roadmap convention 1, as in Layer 0). The formula
   and its order lemmas: a `Semiring` of scalars and seminormed modules. Everything scaled:
   `[NormedRing R] [NormOneClass R]` plus either an explicit `ϖ : PseudoUniformizer R` (when `‖ϖ‖`
   enters the constant) or `[IsTate R]` (pure existence). The open mapping theorem, the closed graph
   theorem and Banach–Steinhaus need **neither `CompleteSpace R` nor `IsUltrametricDist`** — Mathlib's
   Baire proofs transport without them (E16). Ultrametricity enters only where it is used: the
   ultrametric instance on `M →L[R] N`, the Neumann norms, the Pi bound (§1.2.5, E17), and the
   Nakayama step. Commutativity of `R` enters only through Mathlib: `Module R (M →L[R] N)` and
   `IsBoundedSMul R (M ⧸ S)` need `SMulCommClass R R _`, so `opNorm_smul_le`, `instIsBoundedSMul`,
   the strictness statements and `Finite.lean`'s Noetherian section take `[NormedCommRing R]`.
4. **The scaling trick is one lemma.** `norm_map_le_div_mul_of_forall_norm_le ϖ f hε h x :
   ‖f x‖ ≤ C / (ε * ‖ϖ‖) * ‖x‖` (a bound on the closed `ε`-ball is a bound everywhere), proved from
   Layer 0's `existsUnique_zpow_norm_smul_mem_Ioc`; `exists_bound`, `le_opNorm`,
   `opNorm_le_div_of_forall_norm_le` and `banach_steinhaus` all call it. This replaces Mathlib's
   `rescale_to_shell` / `opNorm_le_of_ball` pair.
5. **Statements say what is true (E9–E11).** `‖u‖` is the supremum of the *ratios* `‖u x‖ / ‖x‖`
   (`opNorm_eq_iSup_div`), not of `‖u x‖` over the unit ball; the unit-ball supremum controls `‖u‖`
   only up to `‖ϖ‖⁻¹` (`opNorm_le_div_of_forall_norm_le` with `ε = 1`). Equality in
   `‖a • u‖ ≤ ‖a‖ ‖u‖` is stated for multiplicative **units** (`opNorm_smul_of_isMultiplicative`).
   Multiplication by `a` on `R` has norm exactly `‖a‖` (`opNorm_mulLeftL`).
6. **Seams are declared, not hidden** (as in Layer 0). S1: the OMT is proved directly by Baire
   (`OpenMapping.lean` docstring) instead of from Tau Ceti's Henkel theorem. S2: §1.4.1's cited
   adic-spaces statements are not imported; the normed readings are proved from Buzzard 2.2 and
   BGR 3.7.2/1 without them. S3: §1.4.2's matrix lemma is replaced by Mathlib's Nakayama lemma over
   `Subring.unitClosedBall R` (the route `RigidAnalyticGeometry/BanachAlgebra/Noetherian.lean`
   already takes for ideals over a field).
7. **One conclusion per declaration.** The iff of §1.1.2 is two iffs; strictness is a bound, an
   existence of a bound, and a `def`; the Neumann series is `IsUnit`, `‖u‖ = 1`, `‖u⁻¹‖ = 1`, and
   openness of the units, separately. The only bundled statements are the `∃ C > 0, ∀ y, ∃ x, … ∧ …`
   shapes inherited from Mathlib's `exists_preimage_norm_le` (shared-witness existentials).
8. **Definitions carry API.** `toContinuousLinearEquivOfContinuous` and
   `continuousLinearEquivOfBijective` have their `coe` simp lemmas; `quotKerEquivRangeL` has the two
   bounds; `mulLeftL`, `addPseudoUniformizerSMul`, `padicGeomSeq` have `apply` lemmas; `PadicIntSq`
   has `norm_def` and `toPadicIntSq`.
9. **Imports are minimal, per file.** When a proof needs a lemma from an unimported module, add that
   module. Never `import Mathlib` in a `Code/` file.

## What is deliberately not on this board

- **§1.3 (finite-dimensional spaces over a complete field).** Mathlib has every "record" item
  (`LinearMap.continuous_of_finiteDimensional`, `FiniteDimensional.complete`,
  `Submodule.closed_of_finiteDimensional`, `LinearMap.exists_antilipschitzWith`,
  `ContinuousLinearMap.isOpen_injective`, `Pi.instIsUltrametricDist` for the sup norm on `K ^ n`) —
  no restatement, as for Layer 0's E1. The orthogonal basis over a discretely valued field and the
  `t`-orthogonal basis for `t < 1` need the `IsOrthogonalFamily` / `t`-orthogonal predicates of
  §2.2, which are not in the chain; the roadmap itself calls them "the finite case of §2.4", and they
  are deferred to the Layer 2 board (E13).
- **§1.4.3's model-space milestone** ("closedness of finitely generated submodules of `C₀(I, R)`")
  is a §2.6 milestone by the roadmap's own wording.
- **The `C₀(I, R)` examples** (coordinate evaluation, the diagonal operator) — E15.

## Roadmap errata and clarifications found while planning (numbering continues Layer 0's E1–E8)

| # | Roadmap clause | Finding | Board action |
|---|---|---|---|
| E9 | §1.1.2 "`‖u‖ = sup_{‖x‖ ≤ 1} ‖u x‖`" | **false** in general: `K = ℚ_p`, `M = ℚ_p` with `‖x‖' = p^{1/2}|x|`, `u = id : M → (ℚ_p, |·|)`; then `‖u‖ = p^{-1/2}` but `sup_{‖x‖' ≤ 1} |x| = sup_{|x| ≤ p^{-1}} |x| = p^{-1}`. [Sch] warns of exactly this after Cor 3.2 ("we in general have `‖f(v)‖ ≠ sup {‖f(v)‖ : ‖v‖ = 1}`") | `opNorm_eq_iSup_div` (ratios) + the two-sided bound `norm_le_opNorm_of_norm_le_one` / `opNorm_le_div_of_forall_norm_le`; README corrected |
| E10 | Layer 1 Examples "multiplication by `a` on `R` has norm `‖a‖` when `a` is multiplicative and can be smaller otherwise" | impossible once `‖1‖ = 1` (always, for a nontrivial Tate normed ring): `‖a‖ = ‖a · 1‖ ≤ ‖mulLeft a‖ · ‖1‖` | `opNorm_mulLeftL : ‖mulLeftL a‖ = ‖a‖` for every `a`; README corrected |
| E11 | §1.1.3 "`‖a • u‖ ≤ ‖a‖ ‖u‖`, with equality for multiplicative `a`" | equality needs a multiplicative **unit**: `R = ℚ_p⟨X⟩`, `a = X` is multiplicative, `N = R ⧸ (X)`, and `a • u = 0` for every `u : R →L[R] N` | stated for `a : Rˣ` with `IsMultiplicative (a : R)` (the form Layer 0's `IsMultiplicative.norm_smul` supports) |
| E12 | §1.2.1 "Derive it from Tau Ceti's topological open mapping theorem (Henkel's theorem)" | not a dependency of this repository | proved directly by Baire, as Mathlib does (seam S1, `OpenMapping.lean` docstring) |
| E13 | §1.3 orthogonal / `t`-orthogonal bases of finite-dimensional spaces | need §2.2's predicates, absent from the chain; the roadmap calls them "the finite case of §2.4" | deferred to the Layer 2 board; recorded here |
| E14 | §1.4.1 "Cite the adic-spaces roadmap for …"; §1.4.2 "the matrix input … is `TauCeti.Huber.isUnit_one_sub_of_isTopologicallyNilpotent_entries`" | neither is available; neither is needed: Buzzard 2.2 and BGR 3.7.2/1 (via Nakayama) prove the normed readings | seams S2, S3 (`Finite.lean` docstring) |
| E15 | Layer 1 Examples on `C₀(I, R)` | `IsBoundedSMul R C₀(I, R)` is absent from Mathlib (verified), and the basis vectors are §2.1's | moved to the Layer 2 examples |
| E16 | §1.2 "`R` is Banach–Tate and `M`, `N` are Banach `R`-modules" | the open mapping, closed graph and Banach–Steinhaus theorems use neither `CompleteSpace R` nor ultrametricity (Mathlib's proofs transport verbatim) | stated without them (clarification, not an error) |
| E17 | §1.2.5 "with norm the maximum of the norms of the images of the basis vectors" | true for ultrametric `M` (otherwise only up to a factor `card ι`) | `[IsUltrametricDist M]`, as convention 1 intends (clarification) |
| E18 | §1.4.3 "Record a counterexample over a non-Noetherian Banach–Tate ring" (no example given) | `ℓ^∞(ℕ, ℚ_p)` with the principal ideal `((pⁿ)ₙ)`: `(p^{⌊n/2⌋})ₙ` is in its closure (truncate) but not in it (`p^{⌊n/2⌋ - n}` is unbounded); non-Noetherianity then follows from M2 | `not_isClosed_span_padicGeomSeq`, `not_isNoetherianRing_lp_infty` |

E9 and E10 are corrected in the roadmap README (2026-10-06, uncommitted, two sentences each);
E11–E18 are board notes and docstring warnings.

## Build and verification protocol

- Skeleton gate: `lake build PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.Examples` — must
  succeed with `sorry` warnings only. Verified 2026-10-06: 2 254 jobs, 0 errors.
- Import gate (CI): no `import PhD.Main.*` under `PhD/TauCeti/`.
- Each ticket: `lake build` of its module, then `#print axioms` on each declaration — only
  `propext`, `Classical.choice`, `Quot.sound`. `lake exe runLinter` on the module at cleanup.
- `/beastmode` runs inline as the main agent (user preference), one ticket at a time, naming this
  board. No `timeout` binary on this machine; use the tool timeout. One Lean process at a time on
  this machine (parallel builds swap-thrash).
- The chain root `PhD/TauCeti.lean` gains the leaf module `Operator.Examples` in T031 (append-only
  edit, after `PadicFunctionalAnalysis.NormComparison`; another board may be editing the same file).
