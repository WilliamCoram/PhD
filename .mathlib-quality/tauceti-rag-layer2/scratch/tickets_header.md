# Ticket board: Tau Ceti `RigidAnalyticGeometry`, Layer 2 (the supremum seminorm and the reduction)

**Board**: `.mathlib-quality/tauceti-rag-layer2/` (a *named* board: always pass this path to `/beastmode`;
the default board belongs to another project).
**Plan**: `plan.md` · **Decomposition (quotes, attacks, gate)**: `decomposition.md` · **References**: `references/`
**Roadmap**: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, Layer 2 (§2.1–§2.5 + Examples) — cited as [RM].
**Code**: `PhD/TauCeti/Code/RigidAnalyticGeometry/` — `SupSeminorm/{Seminorm, SpectralValue, Integral, Banach,
FunctionAlgebra}.lean`, `BanachAlgebra/Module.lean`, `Affinoid/{SupSeminorm, PowerBounded, Reduction,
FunctionAlgebra, ReductionFunctor, SupExamples}.lean` — 12 new files, every declaration already stated with
`sorry`. Planned 2026-10-06. Status: **PLANNED — awaiting approval; no ticket started.**

## Summary

| | Count |
|---|---|
| Proof / definition tickets | 70 (`T001`–`T070`; `T070` is the chain-root gate) |
| Per-file cleanups | 25 (`CLEANUP-1`–`CLEANUP-25`) |
| Pre-milestone sweeps | 5 (`CLEANUP-ALL-1`–`CLEANUP-ALL-5`) |
| Final sweep | 1 (`CLEANUP-FINAL`) |
| **Total** | **101** |

- **Milestone M1** = `T019`: **`|f|_sup = σ(minpoly_B f)`** (`Affinoid.supSeminorm_eq_supSpectralValue_minpoly`) —
  [RM] §2.1.4, BGR 3.8.1/7 (a).
- **Milestone M2** = `T042`: **the maximum modulus principle** (`IsAffinoidAlgebra.exists_evalNorm_eq_supSeminorm`) —
  [RM] §2.2.1, BGR 6.2.1/4 (i), Bosch 1.4/14.
- **Milestone M3** = `T050`: **power-bounded ⇔ `|f|_sup ≤ 1` and the spectral radius formula**
  (`IsAffinoidAlgebra.isPowerBounded_iff_supSeminorm_le_one` at `T048`,
  `IsAffinoidAlgebra.supSeminorm_eq_smoothingFun`) — [RM] §2.3.1, §2.3.3, BGR 6.2.3/1, 6.2.3/3.
- **Milestone M4** = `T058`: **reduced affinoid algebras are Banach function algebras**
  (`IsAffinoidAlgebra.isBanachFunctionAlgebra_of_isReduced`, `[CharZero K]`) — [RM] §2.4.1, BGR 6.2.4/1.
- **Milestone M5** = `T064`: **BGR 6.3.1/6** (`IsAffinoidAlgebra.injective_of_isometry`,
  `IsAffinoidAlgebra.isStrictMap_of_isometry`, with `T061`, `T063`) — [RM] §2.5.3.
- Skeleton: 180 open declarations, 180 `sorry`s (every `sorry` is a whole declaration or a field of a
  definition). Gate (verified 2026-10-06, 0 errors):
  `lake build PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.SupExamples`.
- Tickets that can start immediately (no dependencies): `T001`, `T002`, `T008`, `T028`.
- **Not on this board** (see `plan.md` §8): BGR 3.8.3/7 for reduced non-domain `A` (D1), characteristic
  `p` for 6.2.4/1 (D2), a completeness statement for `|·|_sup` (D3), "`K⟨X, Y⟩/(XY − c)` is a domain" (D4),
  the construction of `ℚ₂(√2)` for 6.3.1 Example 1 (D5), the `IsUniform` seam (plan §7), the example
  "`Q(T₁)` is not complete" (D9: BGR states it without proof; nothing downstream consumes it).

## Standing rules

- One Lean process at a time (`lake build PhD.TauCeti.Code.RigidAnalyticGeometry.<Module>`), never
  `lake build PhD`; `timeout` does not exist on this machine; never `import PhD.Main.*`.
- Statements are frozen (`theorem_statement_protected`); a false statement is a B2 with an entry in
  `b2_log.jsonl`; a dropped-section-variable defect is repaired in place and logged (Layer 1 precedent).
- Cleanup tickets are done inline by the main agent; `lake exe runLinter PhD.TauCeti.Code.…` per module.
- Mark progress with `python3 .mathlib-quality/tauceti-rag-layer2/scratch/mark.py <ID> <status> "<note>"`.
