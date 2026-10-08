# Ticket board: Tau Ceti `NewtonPolygons`, Layer 1 (additive valuations of a nonarchimedean field)

**Board**: `.mathlib-quality/tauceti-np-layer1/` (a *named* board: always pass this path to `/beastmode`;
the default board belongs to another project, and `tauceti-np-layer0/` is the finished Layer 0).
**Plan**: `plan.md` · **Decomposition (quotes, attacks, gate)**: `decomposition.md` · **References**: `references/`
**Roadmap**: `PhD/TauCeti/Roadmaps/NewtonPolygons/README.md`, Layer 1 (§1.1–§1.5, Examples) — cited as [RM].
**Code**: `PhD/TauCeti/Code/NewtonPolygons/AddVal/` (`NegLog`, `RatLog`, `Basic`, `RankOne`, `Commensurable`,
`Discrete`, `Normed`, `Padic`, `LaurentSeries`, `Extension`, `PadicComplex`, `Examples`) — 12 files, module
prefix `PhD.TauCeti.Code.NewtonPolygons.AddVal`; the chain root `PhD/TauCeti.lean` imports the leaf
`AddVal.Examples`. Planned 2026-10-06.
**Name check**: every Mathlib name in the "Mathlib lemmas needed" blocks elaborates against the pin
(`scratch/names_tickets_mathlib.lean`, 0 errors) and every skeleton name (`scratch/signatures.lean`, 0 errors);
see `plan.md`, "Name check".

## Summary

| | Count |
|---|---|
| Proof / definition tickets | 52 (`T001`–`T052`; `T052` is the chain-root gate) |
| Per-file cleanups | 21 (`CLEANUP-1`–`CLEANUP-21`) |
| Pre-milestone sweeps | 5 (`CLEANUP-ALL-1`–`CLEANUP-ALL-5`) |
| Final sweep | 1 (`CLEANUP-FINAL`) |
| **Total** | **79** |

- Open: 79 | In Progress: 0 | Done: 0.
- Coverage: every open declaration of the skeleton (144, 152 `sorry`s) is named in exactly one ticket
  (the generator `scratch/gen_tickets.py` fails otherwise).
- **Milestone M1** = `T009`: `Valuation.addVal_map` — the §1.1 dictionary complete, with its naturality.
- **Milestone M2** = `T017`: `Valuation.addValQ_unique` — the element pins the valuation ([RM] §1.4.4).
- **Milestone M3** = `T035`: `NormedField.normAddValZ_padic` — `normAddValZ ℚ_[p] = Padic.addValuation`
  ([RM] §1.3.5).
- **Milestone M4** = `T042`: `NormedField.normAddValZ_algebraMap` — the ramification formula ([RM] §1.3.6).
- **Milestone M5** = `T048`: `PadicComplex.range_normAddValQ` (with `isCommensurable_p`) — the value group of
  `ℂ_p` is `p^ℚ` ([RM] §1.5.4–§1.5.5).
- Parallel capacity: 2 at the start (`NegLog.lean` ∥ `RatLog.lean`), 2 after `Discrete.lean`
  (`LaurentSeries.lean` ∥ `Normed.lean`), 2 after `Normed.lean` (`Padic.lean` ∥ `Extension.lean`); on this
  machine run one Lean process at a time, so the honest estimate is one worker.

Conventions binding every ticket (see `plan.md`, "Generality and design decisions"): the [PR] names of
mathlib4#43578/#43580 for §1.1; `IsCommensurable` is a `Prop` class on `(v, π)`; rings wherever [SRC] allowed
it; `WithTop.map` for rescaled valuations; no `import PhD.Main.*` — the Main-chain files are read-only
proof references, cited as [SRC] (port with the new names, never copy-import). Deviations D1–D6 from the
roadmap text are recorded in `plan.md` and are not to be "fixed" by a worker.

Worker protocol: `/beastmode` inline as the main agent (user preference); after each ticket
`lake build PhD.TauCeti.Code.NewtonPolygons.AddVal.<File>` and `#print axioms` on each declaration (only
`propext`, `Classical.choice`, `Quot.sound`); mark `done` only with zero `sorry` in the ticket's
declarations; append a `Progress` line to the ticket with a timestamp; record any statement repair in
`b2_log.jsonl`.

## Dependency order (ticket groups)

```text
G1 NegLog        : T001 → T002 → T003 → CLEANUP-1 → T004 → CLEANUP-2
G2 RatLog        : T005 → T006 → CLEANUP-3                                   (∥ G1)
G3 Basic         : T007 → T008 → CLEANUP-ALL-1 → T009 [M1] → CLEANUP-4      (after CLEANUP-2)
G4 RankOne       : T010 → T011 → CLEANUP-5                                   (after CLEANUP-4)
G5 Commensurable : T012 → T013 → T014 → CLEANUP-6 → T015 → T016 → CLEANUP-ALL-2 → T017 [M2] → CLEANUP-7
                   → T018 → T019 → CLEANUP-8                                 (after CLEANUP-3, CLEANUP-5)
G6 Discrete      : T020 → T021 → T022 → CLEANUP-9 → T023 → T024 → CLEANUP-10 (after CLEANUP-8)
G7 Normed        : T025 → T026 → T027 → CLEANUP-11 → T028 → T029 → T030 → CLEANUP-12 → T031 → CLEANUP-13
                                                                             (after CLEANUP-10)
G8 Padic         : T032 → T033 → T034 → CLEANUP-14 → CLEANUP-ALL-3 → T035 [M3] → CLEANUP-15
                                                                             (after CLEANUP-13)
G9 LaurentSeries : T036 → T037 → T038 → CLEANUP-16                           (after CLEANUP-10; ∥ G7)
G10 Extension    : T039 → T040 → T041 → CLEANUP-17 → CLEANUP-ALL-4 → T042 [M4] → T043 → T044 → CLEANUP-18
                                                                             (after CLEANUP-13; ∥ G8)
G11 PadicComplex : T045 → T046 → T047 → CLEANUP-19 → CLEANUP-ALL-5 → T048 [M5] → CLEANUP-20
                                                                             (after CLEANUP-15, CLEANUP-18)
G12 Examples     : T049 → T050 → T051 → CLEANUP-21                           (after CLEANUP-16, CLEANUP-20)
G13 gate         : T052 → CLEANUP-FINAL                                      (after every final cleanup)
```
