# Ticket board: Tau Ceti `NewtonPolygons`, Layer 2 (the polygon of a polynomial and of a power series)

**Board**: `.mathlib-quality/tauceti-np-layer2/` (a *named* board: always pass this path to `/beastmode`;
the default board belongs to another project, `tauceti-np-layer0/` and `tauceti-np-layer1/` are the finished
Layers 0 and 1).
**Plan**: `plan.md` · **Decomposition (quotes, attacks, gate)**: `decomposition.md` · **References**: `references/`
**Roadmap**: `PhD/TauCeti/Roadmaps/NewtonPolygons/README.md`, Layer 2 (introduction, §2.1–§2.4, Examples) — cited
as [RM].
**Code**: `PhD/TauCeti/Code/NewtonPolygons/Coeff/` (`NormedAddValuation`, `Generic`, `CoeffVal`, `PowerSeries`,
`Polynomial`, `Extension`, `SupportValue`, `GaussNorm`, `Pure`, `Distinguished`, `Padic`, `Examples`) — 12 files,
module prefix `PhD.TauCeti.Code.NewtonPolygons.Coeff`; the chain root `PhD/TauCeti.lean` imports the leaf
`Coeff.Examples`. Planned 2026-10-06.
**Name check**: every Mathlib / Layer 0 / Layer 1 / rigid-chain name in the "Mathlib lemmas needed" blocks
elaborates against the pin (`scratch/names_tickets_mathlib.lean`) and every skeleton name
(`scratch/signatures.lean`, 0 errors); see `plan.md`, "Name check".

## Summary

| | Count |
|---|---|
| Proof / definition tickets | 72 (`T001`–`T072`; `T072` is the chain-root gate) |
| Per-file cleanups | 28 (`CLEANUP-1`–`CLEANUP-28`) |
| Pre-milestone sweeps | 5 (`CLEANUP-ALL-1`–`CLEANUP-ALL-5`) |
| Final sweep | 1 (`CLEANUP-FINAL`) |
| **Total** | **106** |

- Open: 106 | In Progress: 0 | Done: 0.
- Coverage: every open declaration of the skeleton (256, 261 `sorry`s) is named in exactly one ticket (the
  generator `scratch/gen_tickets.py` fails otherwise).
- **Milestone M1** = `T019`: `PowerSeries.isAdmissible_coeffVal_iff_exists_isRestricted` — the polygon of a
  series exists exactly when the series is restricted at some positive radius ([RM] §2.1.3).
- **Milestone M2** = `T034`: `Polynomial.newtonPolygon_reverse` — the reflection ([RM] §2.2.7, "a milestone,
  not a remark").
- **Milestone M3** = `T049`: `PowerSeries.gaussNorm_rpow_eq_of_supportValue_eq` (with `hasGaussNorm_rpow_iff`
  from `T048`) — the Gauss norm is `b ^ (−s)`, the Legendre transform of the polygon ([RM] §2.3.1–§2.3.2).
- **Milestone M4** = `T062`: `Polynomial.HasFirstBreak.isMulDistinguished` — first break ⟹ distinguished
  ([RM] §2.4.3).
- **Milestone M5** = `T071`: `Polynomial.isPure_one_add_three_pow_mul_X_sq` and
  `Polynomial.isPure_C_inv_mul_cyclotomic_comp_X_add_one` — the acceptance examples `1 + 3^{2j+1} X²` (slope
  `j + ½`) and `Φ_p(X+1)/p` (slope `−1/(p−1)`).
- Parallel capacity: 3 at the start (`NormedAddValuation.lean` ∥ `Generic.lean` ∥ `SupportValue.lean`), 2 after
  `NormedAddValuation.lean` (`CoeffVal.lean` ∥ `Padic.lean`); on this machine run one Lean process at a time
  (other boards are active), so the honest estimate is one worker.

Conventions binding every ticket (see `plan.md`, "Generality and design decisions"): one bundle
`NormedField.NormedAddValuation K Γ` over `[NormedField K]` (no ultrametric or nontriviality instance except
in the three Layer-1 instances); radii are `v.base ^ m`; Gauss norms are `PowerSeries.gaussNorm norm c` with
polynomials through the coercion and `Polynomial.gaussNorm_toAbsoluteValue` as the only bridge; the
supporting value is an `EReal`; restrictedness is the rigid chain's `PowerSeries.IsRestricted`
(`isRestricted_iff'` along `atTop`); no `import PhD.Main.*` — the Main-chain files are read-only proof
references, cited as [SRC]. Deviations and errata D1–D10 are recorded in `plan.md` and are not to be
"fixed" by a worker; in particular §2.4.4 is deferred to Layer 3/4, not ticketed.

Worker protocol: `/beastmode` inline as the main agent (user preference); after each ticket
`lake build PhD.TauCeti.Code.NewtonPolygons.Coeff.<File>` and `#print axioms` on each declaration (only
`propext`, `Classical.choice`, `Quot.sound`); mark `done` only with zero `sorry` in the ticket's
declarations; append a `Progress` line to the ticket with a timestamp; record any statement repair in
`b2_log.jsonl`. `omega`, not `lia`, for linear `ℕ` goals.

## Dependency order (ticket groups)

```text
G1 NormedAddValuation : T001 → T002 → T003 → CLEANUP-1 → T004 → T005 → T006 → CLEANUP-2 → T007 → T008 → T009 → CLEANUP-3
G2 Generic            : T010 → T011 → T012 → CLEANUP-4 → T013 → T014 → T015 → CLEANUP-5          (∥ G1, G7)
G3 CoeffVal           : T016 → T017 → T018 → CLEANUP-6 → CLEANUP-ALL-1 → T019 [M1] → T020 → CLEANUP-7   (after CLEANUP-3)
G4 PowerSeries        : T021 → T022 → T023 → CLEANUP-8 → T024 → T025 → T026 → CLEANUP-9 → T027 → CLEANUP-10
                                                                                     (after CLEANUP-5, CLEANUP-7)
G5 Polynomial         : T028 → T029 → T030 → CLEANUP-11 → T031 → T032 → T033 → CLEANUP-12 → CLEANUP-ALL-2
                        → T034 [M2] → T035 → T036 → CLEANUP-13                               (after CLEANUP-10)
G6 Extension          : T037 → T038 → CLEANUP-14                                            (after CLEANUP-13)
G7 SupportValue       : T039 → T040 → T041 → CLEANUP-15 → T042 → T043 → T044 → CLEANUP-16 → T045 → T046 → CLEANUP-17
                                                                                     (Layer 0 only; ∥ G1–G6)
G8 GaussNorm          : T047 → T048 → CLEANUP-ALL-3 → T049 [M3] → CLEANUP-18 → T050 → T051 → T052 → CLEANUP-19
                        → T053 → CLEANUP-20                                         (after CLEANUP-13, CLEANUP-17)
G9 Pure               : T054 → T055 → T056 → CLEANUP-21 → T057 → T058 → T059 → CLEANUP-22 → T060 → CLEANUP-23
                                                                                     (after CLEANUP-20)
G10 Distinguished     : T061 → CLEANUP-ALL-4 → T062 [M4] → CLEANUP-24                       (after CLEANUP-23)
G11 Padic             : T063 → CLEANUP-25                                                   (after CLEANUP-3; ∥ G3–G10)
G12 Examples          : T064 → T065 → T066 → CLEANUP-26 → T067 → T068 → T069 → CLEANUP-27 → T070 → CLEANUP-ALL-5
                        → T071 [M5] → CLEANUP-28                                 (after CLEANUP-14, CLEANUP-24, CLEANUP-25)
G13 gate              : T072 → CLEANUP-FINAL                                                (after every final cleanup)
```
