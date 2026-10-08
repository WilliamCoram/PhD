# Ticket board: Tau Ceti `PadicFunctionalAnalysis`, Layer 0

**Board**: `.mathlib-quality/tauceti-pfa-layer0/` (a *named* board: always pass this path to `/beastmode`;
the default board belongs to another project).
**Plan**: `plan.md` · **Decomposition (quotes, attacks, gate)**: `decomposition.md` · **References**: `references/*.txt`
**Roadmap**: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, Layer 0 (§0.1–§0.4) — cited as [RM].
**Code**: `PhD/TauCeti/Code/PadicFunctionalAnalysis/` — twelve files, every declaration already stated with
`sorry`. Planned 2026-09-18. Status: **awaiting approval**; no proof work has started.

## Summary

| | Count |
|---|---|
| Proof / definition tickets | 45 (`T001`–`T045`) |
| Per-file cleanups | 17 (`CLEANUP-1`–`CLEANUP-17`) |
| Pre-milestone sweeps | 2 (`CLEANUP-ALL-1`, `CLEANUP-ALL-2`) |
| Final sweep | 1 (`CLEANUP-FINAL`) |
| **Total** | **65** |

- **Milestone M1** = `T035`: the unit ball of a Tate normed ring is a ring of definition
  (`NormedRing.PseudoUniformizer.isAdic_ideal` and its companions) — [RM] §0.4.5.
- **Milestone M2** = `T039`: the gauge norm of a Hausdorff Tate ring is a ring norm inducing the topology
  (`Subring.gaugeRingNorm`, `Subring.hasBasis_nhds_zero_gaugeNorm`) — [RM] §0.4.6.
- The layer closes with `T036`, the round trip `gaugeNorm_unitClosedBall` (the two bridges are mutually inverse up
  to [JN] Lemma 2.1.7).
- Skeleton: 212 declarations, 191 `sorry`s. Gate (verified 2026-09-18, 2 626 jobs, 0 errors):
  `lake build PhD.TauCeti.Code.PadicFunctionalAnalysis.Examples PhD.TauCeti.Code.PadicFunctionalAnalysis.NormComparison`.
- Tickets that can start immediately (no dependencies): `T001`, `T006`, `T012`, `T015`, `T018`, `T028`, `T037`.

## Worker protocol (binding)

1. **The statements are fixed.** Every ticket's Statement block is copied verbatim from the skeleton by a script.
   Prove the statement as written. If a statement is false or unprovable as stated, that is a **B2 stop** with a
   concrete counterexample or obstruction — never silently change a hypothesis. Private helper lemmas are allowed
   and expected where a sketch says so; they follow the same conventions.
2. **Chain separation.** Never `import PhD.Main.*` here (CI-gated), and never the reverse. `PhD/Main/` files cited as
   [SRC] are read-only references for proof ideas. Never delete `PhD/PR'd/` or legacy files.
3. **Build** with `lake build PhD.TauCeti.Code.PadicFunctionalAnalysis.<Module>` — never `lake build PhD`. There is no
   `timeout` binary on this machine: use the tool timeout and check exit codes. Another board builds in parallel on
   this machine; expect slow builds, and do not kill processes you did not start.
4. **Imports stay minimal per file** (never `import Mathlib` in a `Code/` file). When a proof needs an unimported
   module, add exactly that module.
5. **Done means**: the module builds with no `sorry` in the ticket's declarations, `#print axioms` on each shows only
   `propext`, `Classical.choice`, `Quot.sound`, and the ticket's Status line is updated here.
6. **Cleanup tickets are done inline by the main agent** (no Agent-dispatched cleanup workers), with
   `lake exe runLinter` on the module.
7. **Sentinel ownership.** `.mathlib-quality/beastmode_active` may belong to a parallel instance: `cat` it before
   acting, and delete it only if its `BOARD:` line names this board.
8. **Mathlib first.** Every Mathlib name in a "Mathlib lemmas needed" block was checked by elaboration against the
   pinned Mathlib (`scratch/names*.lean`, six files, about 300 names); `T0xx` there refers to an earlier ticket of this board. If
   Mathlib already has a ticket's statement, use it and record the name.
9. **Conventions** (plan §"Generality and design decisions"): Mathlib vocabulary (`IsUltrametricDist`,
   `IsBoundedSMul`, `NormMulClass`); weakest structure that carries the proof; `IsTate` is a Prop and
   `PseudoUniformizer` is data; two norms are two normed rings; the rescaled norm lives on `Rescaled ϖ M`; seams are
   declared in module docstrings; one conclusion per declaration; one-line `Source:` docstrings.
10. **Commit or push only when the user asks.**

## Roadmap errata (found while planning; see plan.md for the full table)

E1 Mathlib *does* have `IsUltrametricDist.norm_tsum_le` · E2 `R⁰⁰` is **not** maximal for multiplicative norms in
general (`ℚ_p⟨X⟩`); it lies in the Jacobson radical, and is maximal for normed fields · E3 the rescaled module is a
normed `R`-module only when `‖R‖ ⊆ ‖ϖ‖ ^ ℤ ∪ {0}` · E4 the `ℚ_p⟨X⟩` example needs §4.1 · E5 "a Tate normed ring is
nontrivial" needs `‖1‖ = 1` (equivalently `Nontrivial R`, T021) · E6 the `normAddVal` seam is external to this chain ·
E7 §0.4.5 is stated in Mathlib vocabulary · E8 the strict bound needs `0 < B` and no nullity hypothesis; the
supremum is attained on any nonempty index type. E1–E5 and E8 are corrected in the roadmap README (2026-09-18,
uncommitted); E6–E7 are board notes.

## Dependency order

The tickets below are listed in dependency order, group by group (so `T037`–`T039` precede `T034`–`T036`).

```text
G1  Sums            T001 → T002 → T003 → CLEANUP-1 → T004 → T005 → CLEANUP-2
G2  UnitBall        T006 → T007 → T008 → CLEANUP-3 → T009 (also needs T002) → T010 → T011 → CLEANUP-4
G3  PowerBounded    T012 → T013 → T014 → CLEANUP-5
G4  Multiplicative  T015 → T016 → T017 → CLEANUP-6
G5  Module          T018 → T019 → T020 → CLEANUP-7
G6  Tate            CLEANUP-6 → T021 → T022 → T023 → CLEANUP-8 → T024 → T025 → CLEANUP-9
G7  NormComparison  CLEANUP-9 → T026 → T027 → CLEANUP-10
G8  Rescale         T028 → T029 → (CLEANUP-9) T030 → CLEANUP-11 → (CLEANUP-7) T031 → CLEANUP-12
G9  Residue         CLEANUP-4, CLEANUP-9 → T032 → T033 → CLEANUP-13
G11 GaugeNorm       T037 → T038 → CLEANUP-ALL-2 → T039 [M2] → CLEANUP-15
G10 Huber           CLEANUP-13, CLEANUP-5 → T034 → CLEANUP-ALL-1 → T035 [M1]
                    → (CLEANUP-12, CLEANUP-15) T036 → CLEANUP-14
G12 Examples        CLEANUP-13 → T040 → T041 → (CLEANUP-12) T042 → CLEANUP-16
                    → (CLEANUP-5) T043 → T044 → CLEANUP-17
End                 all final per-file cleanups → T045 (chain root) → CLEANUP-FINAL
```

Cleanup cadence: a `/cleanup` after every third proof ticket on a file and after the last one; a `/cleanup-all`
before each milestone; a final `/cleanup-all`. On `GaugeNorm.lean` and `Huber.lean` the pre-milestone sweep is the
mid-file cleanup.

---

## Tickets

