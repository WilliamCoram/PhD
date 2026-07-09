# Development Plan: Nonarchimedean Fredholm theory over Banach–Tate rings (TateFredholm)

Takeover of `PhD/Test/CompactOperatorsMerged.lean` (namespace `TateFredholm`), created
2026-07 as the merged/most-general of the project's four compact-operator blueprints.
State at takeover: builds clean, **43 sorried declarations**, every sorry carries a
docstring proof sketch with source citations.

## Goal

Discharge every sorry in the `TateFredholm` development: the theory of compact operators
and Fredholm determinants `det(1 − Tu) ∈ R⟦T⟧` over a commutative nonarchimedean
Banach–Tate ring `R` (`[IsTate R]`: a multiplicative pseudo-uniformizer exists), with
**no Noetherian hypothesis** except the single isolated statement
`finite_projective_of_one_sub_compact_nilpotent`.  Headline targets:

- `isCompletelyContinuous_iff_rowNorm` — the compactness criterion, Noetherian-free
  (strictly generalises Johansson–Newton's published statement);
- `charPowerSeries_comm` — the trace property `det(1−T·uv) = det(1−T·vu)` (**milestone**),
  from which conjugation/basis/norm invariance and the (Pr) extension are formal.

## References (full bibliography; each ticket cites into these)

- **[Bel]** J. Bellaïche, *The Eigenbook*, Pathways in Mathematics, Birkhäuser 2021,
  Chapter 3 §3.1 (= draft §II.1, our citations; PDF: scratchpad `Eigenbook.pdf`, pages
  54–64 extracted during blueprint authoring).  Source of the proof *architecture*:
  truncations (Lemma II.1.8), quantitative continuity (Lemma II.1.15), trace property
  (Prop II.1.17), (Pr) results (Ex II.1.19, Props II.1.20–21).
- **[JN]** C. Johansson, J. Newton, *Extended eigenvarieties for overconvergent
  cohomology*, arXiv:1604.07739v4 (Oct 2020), §2.1 (PDF: scratchpad `jn.pdf`, pages
  7–10 extracted).  Source of the *hypotheses*: Banach–Tate rings (Defs 2.1.1–2.1.2,
  2.1.4–2.1.5) and the norm-comparison Lemmas 2.1.6–2.1.7.
- **[Buz]** K. Buzzard, *Eigenvarieties*, LMS LNS 320 (2007), §2 — the ρ-scaling trick
  (`ϖ` for `ρ` per [JN]), matrix facts p. 65, determinant recipe p. 67.
- **[Serre]** J-P. Serre, Publ. Math. IHÉS 12 (1962) — the classical `A = K` case;
  Prop. 1 for the (deferred) Serre specialisation ticket.
- Project blueprint PDF Chapter 6 (numbering 6.x used in docstrings).

**Source-faithfulness note.** The skeleton's docstrings were transcribed from the actual
PDFs (pages listed above) during blueprint authoring; each ticket's sketch below points
back to the source item.  Workers must re-open the cited source passage if a sketch step
surprises them — per the binding rule, drift from the source is a stop condition.

## Mathlib Inventory (verified 2026-07-09 against local checkout)

| Concept | Mathlib status | Our action |
|---------|---------------|------------|
| `C₀(α, β)` Banach structure | `Mathlib.Topology.ContinuousMap.ZeroAtInfty` | USE (already wired via `cSpace`) |
| `Matrix.det_one_sub_mul_comm` | ✓ `Mathlib/LinearAlgebra/Matrix/SchurComplement.lean:410` | USE (finite input to trace property) |
| `RingHom.map_det` | ✓ `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:317` | USE (base change) |
| `nonempty_interior_of_iUnion_of_closed` (Baire) | ✓ `Mathlib/Topology/Baire/Lemmas.lean:245` | USE (OMT ticket T008) |
| `summable_iff_vanishing_norm` | ✓ `Mathlib/Analysis/Normed/Group/InfiniteSum.lean` | USE (input to T018) |
| Operator norm over a normed **ring** | **GAP** (Mathlib: `NontriviallyNormedField` only) | DEVELOP: T003 basic API on our scoped `instNorm` |
| Open mapping theorem over Tate rings | **GAP** (Mathlib: field scalars only) | DEVELOP: T008 from Baire + ϖ-scaling |
| "terms → 0 cofinitely ⟹ Summable" (complete ultrametric) | **GAP** (nnnorm ultrametric API exists in `Mathlib/Analysis/Normed/Group/Ultra.lean`; no summability criterion found) | DEVELOP: T018 (`summable_of_tendsto_cofinite`) |
| `IsUltrametricDist` finset-sum bound | expected in `Ultra.lean` (nnnorm forms confirmed; exact norm-form name to verify at work) | USE/derive in T018 |

## File Structure (after structural ticket T001)

Move out of `Test/` into a real module tree (the blueprint's own TODO):

- `PhD/TateFredholm/Tate.lean` — `Ix`, `IsMultiplicative`, `PseudoUniformizer`, `IsTate`,
  bridge `isTate_of_normedAlgebra` (already proved), `val`; ultrametric summability
  helper (T018)
- `PhD/TateFredholm/OperatorNorm.lean` — scoped `instNorm` + basic API, `le_opNorm`,
  completeness, OMT
- `PhD/TateFredholm/Compact.lean` — `IsFiniteRank`, `IsCompletelyContinuous`, ideal lemmas
- `PhD/TateFredholm/ModelSpace.lean` — `cSpace`, `single`, ONable/(Pr) definitions
- `PhD/TateFredholm/Matrix.lean` — `matrixCoeff`, `truncation`, compactness criterion
- `PhD/TateFredholm/Fredholm.lean` — minors, `charCoeff`, `charPowerSeries`, trace property
- `PhD/TateFredholm/Pr.lean` — lifting property, projectivity, the Noetherian statement
- `PhD/TateFredholm/BaseChange.lean` — norm comparison, equivalent-norm invariance,
  bounded base change, Serre specialisation (assembly T038)
- `PhD/TateFredholm/Residue.lean` — residue machinery for Serre's theorem (skeleton §10
  of the merged file; decomposed 2026-07-09, see `decomposition.md`; tickets T039–T046)

The three parent blueprints (`CompactOperators*.lean` in `Test/`) stay untouched as
source documentation.

## Dependency Graph (ticket level)

```
T001 (split)
 ├─ T002 Tate API ── T004 ϖ-smul ── T005 le_opNorm ── T006 norm_add_le ── T007 complete
 │                                   │                                     
 ├─ T003 opNorm API ─┴───────────────┼── T009/T010/T011 (compact ideal)
 ├─ T008 OMT (Baire+ϖ) ──────────────┼──────────────┐
 ├─ T012 norm_eq_iSup ── T013 instances             │
 │        ├─ T014 isONable_cSpace                    │
 │        ├─ T015 ‖u‖ = sup matrix ── T020 criterion ┼── T021 truncation limit
 │        └─ T016 truncation ── T017 II.1.8 ─────────┘        │
 ├─ T018 ultrametric summability ── T019 coeffEquiv ── T030 lift ── T031 proj ── T032 Noeth
 │        └─ T022 summable_minor ── T024 entire / T025 Lipschitz / T036 baseChange coeff
 ├─ T023 c₀=1     T026 det compat ──┐
 │                                   ├─ [CLEANUP-ALL-1] ── T027 TRACE PROPERTY (milestone)
 │                                   │        └─ T028 conj / T029 extendZero
 └─ T033 JN 2.1.6 ── T034 JN 2.1.7 ── T035/T037 equiv-invariance   T038 Serre (BLOCKED: API gap)
```

## Generality Decisions

- **No ground field**: everything over `[NormedCommRing R] [IsUltrametricDist R]
  [CompleteSpace R] [NormOneClass R]` + `[IsTate R]` exactly where scaling is needed.
  Do not introduce `K` anywhere; the field case is reachable via
  `isTate_of_normedAlgebra`.
- **No Noetherian** except T032 (`[IsNoetherianRing R]`, isolated by design).
- Operator-norm instance stays **scoped** (`open scoped TateFredholm`) — do not globalise;
  the parent files carry their own scoped instances and must remain co-importable.
- New helper lemmas (T003, T018) are stated at maximal generality (any Banach `R`-modules /
  any complete ultrametric commutative group), not just for `cSpace`.
- `IsEntire`, `charCoeff` etc. stay norm-free/topological where they already are.

## Execution notes

- Workers: `/beastmode`, one ticket at a time; parallel capacity ≈ 3 at peak (see
  `Parallel` fields).
- The skeleton compiles at takeover; every ticket is "replace the sorry at the named
  declaration" — signatures are canonical and must not be changed without a B2 stop.
- ChatGPT MCP not configured — validation steps skipped.
