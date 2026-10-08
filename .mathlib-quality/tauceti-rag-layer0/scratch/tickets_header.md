# Ticket board: Tau Ceti `RigidAnalyticGeometry`, Layer 0 (the Tate algebras)

**Board**: `.mathlib-quality/tauceti-rag-layer0/` (a *named* board: always pass this path to `/beastmode`;
the default board belongs to another project).
**Plan**: `plan.md` · **Decomposition (quotes, attacks, gate)**: `decomposition.md` · **References**: `references/`
**Roadmap**: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, Layer 0 (§0.1–§0.4) — cited as [RM].
**Code**: `PhD/TauCeti/Code/RigidAnalyticGeometry/` (and `PadicFunctionalAnalysis/Orthonormal.lean`) — 19 files,
every declaration already stated with `sorry`; the floor `Restricted/**` and `TateAlgebra/Tower.lean` are
complete. Planned 2026-10-02. Status: **PLANNED — awaiting approval; no ticket started.**

## Summary

| | Count |
|---|---|
| Proof / definition tickets | 81 (`T001`–`T081`; `T081` is the chain-root gate) |
| Per-file cleanups | 31 (`CLEANUP-1`–`CLEANUP-31`) |
| Pre-milestone sweeps | 4 (`CLEANUP-ALL-1`–`CLEANUP-ALL-4`) |
| Final sweep | 1 (`CLEANUP-FINAL`) |
| **Total** | **117** |

- **Milestone M1** = `T028`: the Gauss norm of `Tₙ` is the supremum norm
  (`MvPowerSeries.Restricted.supSeminorm_eq_norm`) — [RM] §0.1.3–§0.1.4, BGR 5.1.4/6.
- **Milestone M2** = `T050`: `Tₙ` is noetherian, factorial, Jacobson and of Krull dimension `n` — [RM]
  §0.3.2–§0.3.4, BGR 5.2.6/1–3.
- **Milestone M3** = `T070`: ideals of `Tₙ` are strictly closed and `|Tₙ ⧸ 𝔞| = |K|` — [RM] §0.3.1,
  BGR 5.2.7/8, Bosch 1.3/7–9.
- **Milestone M4** = `T077`: `Q(Tₙ)` is weakly stable and `Tₙ` is Japanese, in characteristic zero —
  [RM] §0.4.2–§0.4.3, BGR 5.3.1/1 and 5.3.1/3.
- Skeleton: 205 open declarations, 215 `sorry`s. Gate (verified 2026-10-02, 2 722 jobs, 0 errors):
  `lake build PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Examples`.
- Tickets that can start immediately (no dependencies): `T001`, `T002`, `T022`, `T025`, `T038`, `T044`,
  `T051`, `T055`, `T062`, `T071`, `T076`.
- **Not on this board**: [RM] §0.4.2–§0.4.3 in characteristic `p` (BGR 5.3.1/2 and Part A's b-separable
  modules). See `plan.md`, "Not on this board", and `decomposition.md`, "Unticketed sub-tree".

## Worker protocol (binding)

1. **The statements are fixed.** Every Statement block is copied verbatim from the skeleton by
   `scratch/gen_tickets.py`. Prove the statement as written. If a statement is false or unprovable as stated,
   that is a **B2 stop** with a concrete counterexample or obstruction — never silently change a hypothesis.
   Private helper lemmas are allowed and expected where a sketch says so.
2. **Chain separation.** Never `import PhD.Main.*` here (CI-gated), and never the reverse. The floor
   `Restricted/**` was copied from `PhD/Main/ForMathlib`; do not re-copy or edit it except in `CLEANUP-FINAL`.
   Never delete `PhD/PR'd/` or legacy files.
3. **Seam rules** (plan, "The floor"): `Restricted R c` is opaque — cross it with `Restricted.ext`, `val_*`,
   `congrArg`; no file other than `TateAlgebra/Tower.lean` mentions `Fin.tail`, the floor's `finSuccEquiv` or
   `PowerSeries.Restricted` (use `coeffX0`, `coeff_coeffX0`, `ofPolynomial`, `coeff_ofPolynomial`,
   `isMulDistinguishedX0_iff` and the six Weierstrass statements of `Tower.lean`); if a floor lemma must be
   applied at the unit polyradius, give the polyradius explicitly (`(c := (1 : Fin (n + 1) → ℝ))`).
4. **Never `import Mathlib`** in a file that imports the floor (the floor's `PowerSeries.IsRestricted` clashes
   with `Mathlib.RingTheory.PowerSeries.Restricted`), and do not import that Mathlib file or
   `Mathlib.RingTheory.Polynomial.GaussNorm`. Imports stay minimal per file; when a proof needs an unimported
   module, add exactly that module.
5. **Build** with `lake build PhD.TauCeti.Code.RigidAnalyticGeometry.<Module>` (or
   `PhD.TauCeti.Code.PadicFunctionalAnalysis.Orthonormal`) — never `lake build PhD`. There is no `timeout`
   binary on this machine: use the tool timeout and check exit codes. **One Lean process at a time**; do not
   kill processes you did not start.
6. **Section variables.** An instance-implicit section variable that the *statement* does not mention is not
   part of an `instance` or `def`; the elaborated signatures are in `scratch/signatures.txt`. If a proof
   seems to need a hypothesis that the signature lacks, read the sketch — it says which route avoids it
   (for example T002).
7. **Done means**: the module builds with no `sorry` in the ticket's declarations, `#print axioms` on each
   shows only `propext`, `Classical.choice`, `Quot.sound`, and the ticket's Status line is updated here.
8. **Cleanup tickets are done inline by the main agent** (no Agent-dispatched cleanup workers), with
   `lake exe runLinter` on the module.
9. **Sentinel ownership.** `.mathlib-quality/beastmode_active` may belong to a parallel instance: `cat` it
   before acting, and delete it only if its `BOARD:` line names this board.
10. **Mathlib first.** Every name in a "Mathlib lemmas needed" block was checked by elaboration against the
    pinned Mathlib: `scratch/names_tickets_mathlib.lean` (443 names) and `scratch/names_tickets_chain.lean`
    (53 floor, chain and board names) are generated from those blocks by `scratch/extract_names.py`, and both
    elaborate with no error and no deprecation warning. `T0xx` in a sketch refers to an earlier ticket of this
    board. If Mathlib already has a ticket's statement, use it and record the name.
11. **Readable proofs** (user preference): explicit `ring` identities, `mul_nonneg`, `linarith` over opaque
    `nlinarith`; `omega`, not `lia`.
12. **Commit or push only when the user asks.**

## Roadmap errata (found while planning; full table in `plan.md`)

E1 a Weierstrass polynomial is monic of Gauss norm one (BGR 5.2.3/1), **not** "non-leading coefficients of
norm `< 1`" (`X − 1`) · E2 the Tate algebra is the type `MvPowerSeries.Restricted K 1` of mathlib4#42867, and
its floor is in this chain · E3 the distinguished variable is `X 0` · E4 the maximum-modulus point has a
finite residue field by construction (no forward reference to §1.2.4) · E5 `dim Tₙ ≤ n` by integral descent
(Bosch 1.2/10), not BGR 7.1.1/3 · E6 closedness of ideals is proved here (Bosch 1.3), not cited · E7 the
§0.4.1 route is BGR 3.5.1/3–4 and 4.3/2 in characteristic zero; characteristic `p` is not on this board · E8
the relative form of Bosch 1.8/13 belongs to Layer 4 · E9 "`Q(T₁)` is not complete" belongs to Layer 2 · E10
substitution, evaluation and noetherianity are supplied by this layer · E11 `|f(x)|` is spelled
`spectralValue (minpoly K (mk f))` · E12 the chart example `X₁ − X₂` is already distinguished. E1–E12 are
applied to the roadmap README (uncommitted).

## Dependency order

The tickets below are listed in this order.

```text
G1  Basic            T001 → T002 → T003 → CLEANUP-1 → T004 → T005 → CLEANUP-2
G2  Reduction        (CLEANUP-2) T006 → T007 → T008 → CLEANUP-3 → T009 → T010 → T011 → CLEANUP-4 → T012 → CLEANUP-5
G3  Eval             (CLEANUP-2) T013 → T014 → T015 → CLEANUP-6 → T016 → T017 → T018 → CLEANUP-7
G4  EvalReduction    (CLEANUP-5, CLEANUP-7) T019 → T020 → T021 → CLEANUP-8
G5  SupSeminorm      T022 → T023 → T024 → CLEANUP-9
G6  MaxModulus       T025 → (CLEANUP-5, CLEANUP-8) T026 → (CLEANUP-9) T027 → CLEANUP-ALL-1 → T028 [M1] → CLEANUP-10
G7  Distinguished    (CLEANUP-2) T029 → T030 → (CLEANUP-4) T031 → CLEANUP-11 → T032 → T033 → T034 → CLEANUP-12
G8  Finiteness       (CLEANUP-12) T035 → T036 → T037 → CLEANUP-13
G9  Chart            T038 → T039 → T040 → CLEANUP-14 → (CLEANUP-7) T041 → (CLEANUP-8) T042
                     → (CLEANUP-12) T043 → CLEANUP-15
G10 Rueckert         T044 → T045 → T046 → CLEANUP-16 → T047 → T048 → CLEANUP-17
G11 Tate/Rueckert    (CLEANUP-13, CLEANUP-15) T049 → CLEANUP-ALL-2 → T050 [M2] → CLEANUP-18
G12 Bald             T051 → T052 → T053 → CLEANUP-19 → T054 → CLEANUP-20
G13 Orthonormal      T055 → T056 → T057 → CLEANUP-21
G14 OrthonormalLift  (CLEANUP-20) T058 → (CLEANUP-21) T059 → T060 → CLEANUP-22 → T061 → CLEANUP-23
G15 StrictlyClosed   T062 → (CLEANUP-2, CLEANUP-21) T063 → (CLEANUP-5) T064 → CLEANUP-24
                     → (CLEANUP-23, CLEANUP-20) T065 → T066 → T067 → CLEANUP-25 → T068 → T069
                     → CLEANUP-ALL-3 → T070 [M3] → CLEANUP-26
G16 WeaklyStable     T071 → T072 → T073 → CLEANUP-27 → T074 → T075 → CLEANUP-28
G17 Japanese         T076 → CLEANUP-29
G18 Stable           (CLEANUP-18, CLEANUP-28, CLEANUP-29) CLEANUP-ALL-4 → T077 [M4] → CLEANUP-30
G19 Examples         (CLEANUP-15, CLEANUP-9) T078 → T079 → (CLEANUP-13) T080 → CLEANUP-31
End                  all final per-file cleanups → T081 (chain root) → CLEANUP-FINAL
```

Cleanup cadence: a `/cleanup` after every third proof ticket on a file and after the last one; a
`/cleanup-all` before each milestone; a final `/cleanup-all`. On `MaxModulus.lean` the pre-milestone sweep
`CLEANUP-ALL-1` is the mid-file cleanup.
