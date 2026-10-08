# Ticket board: Tau Ceti `RigidAnalyticGeometry`, Layer 1 (affinoid algebras)

**Board**: `.mathlib-quality/tauceti-rag-layer1/` (a *named* board: always pass this path to `/beastmode`;
the default board belongs to another project).
**Plan**: `plan.md` · **Decomposition (quotes, attacks, gate)**: `decomposition.md` · **References**: `references/`
**Roadmap**: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, Layer 1 (§1.1–§1.5) — cited as [RM].
**Code**: `PhD/TauCeti/Code/RigidAnalyticGeometry/` (`NormedQuotient.lean`, `Restricted/{Algebra, Sum}.lean`,
`TateAlgebra/Eval.lean`, `Affinoid/*.lean`, `BanachAlgebra/*.lean`) and
`PhD/TauCeti/Code/PadicFunctionalAnalysis/PowerBounded.lean` — 16 files, every declaration already stated
with `sorry`. Planned 2026-10-05. Status: **PLANNED — awaiting approval; no ticket started.**

## Summary

| | Count |
|---|---|
| Proof / definition tickets | 64 (`T001`–`T064`; `T064` is the chain-root gate) |
| Per-file cleanups | 24 (`CLEANUP-1`–`CLEANUP-24`) |
| Pre-milestone sweeps | 5 (`CLEANUP-ALL-1`–`CLEANUP-ALL-5`) |
| Final sweep | 1 (`CLEANUP-FINAL`) |
| **Total** | **94** |

- **Milestone M1** = `T004`: Layer 0 restored — the three floor files generalised in place
  (`Restricted/Algebra.lean`, `TateAlgebra/Eval.lean`, `PadicFunctionalAnalysis/PowerBounded.lean`)
  are sorry-free again, so `lake build PhD.TauCeti` is sorry-free below this board.
- **Milestone M2** = `T030`: **Noether normalisation** (`IsAffinoidAlgebra.exists_finite_injective`) —
  [RM] §1.2.1, BGR 6.1.2/1–2, Bosch 1.4/2 (iii).
- **Milestone M3** = `T037`: **every homomorphism into an affinoid algebra is continuous**
  (`AlgHom.continuous_of_isAffinoidAlgebra`) — [RM] §1.3.2, BGR 6.1.3/1, Bosch 1.4/19.
- **Milestone M4** = `T047`: **the affinoid tensor product is the pushout**
  (`Affinoid.isAffinoidTensorProduct_tensorQuotient`) — [RM] §1.1.5, BGR 6.1.1/10–11.
- **Milestone M5** = `T053`: **the universal properties of `A⟨f, g⁻¹⟩` and `A⟨f/g⟩`**
  (`Affinoid.isGeneralisedFractions_toFractions`, `Affinoid.isRationalFractions_toRational`) —
  [RM] §1.4.1–1.4.2, BGR 6.1.4/1–4.
- Skeleton: 153 open declarations, 153 `sorry`s. Gate (verified 2026-10-05, 2 764 jobs, 0 errors):
  `lake build PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.Examples`.
- Tickets that can start immediately (no dependencies): `T001`, `T002`, `T004`, `T005`, `T012`,
  `T013`, `T021`, `T022`, `T024`, `T027`, `T032`, `T034`, `T043`, `T062`.
- **Not on this board**: BGR 6.1.1/6 and 6.1.3/4 (Banach topologies on finite extensions), the
  seminorm-completion model of §1.4.2, §1.4.3–1.4.4, the "only if" of BGR 6.1.5/4 and 6.1.5/5,
  characteristic `p` Japaneseness. See `plan.md`, "Not on this board", and `decomposition.md`,
  "Unticketed sub-trees".

## Worker protocol (binding)

1. **The statements are fixed.** Every Statement block is copied verbatim from the skeleton by
   `scratch/gen_tickets.py`. Prove the statement as written. If a statement is false or unprovable as stated,
   that is a **B2 stop** with a concrete counterexample or obstruction — never silently change a hypothesis.
   Private helper lemmas are allowed and expected where a sketch says so.
2. **Chain separation.** Never `import PhD.Main.*` here (CI-gated), and never the reverse. The floor
   `Restricted/**` is a copy of `PhD/Main/ForMathlib`; apart from the two files this board generalised
   (`Restricted/Algebra.lean`, `TateAlgebra/Eval.lean`) do not edit it. Never delete `PhD/PR'd/` or legacy files.
3. **Seam rules** (plan, "Seam notes", and Layer 0's): `Restricted R c` is opaque — cross it with
   `Restricted.ext`, `val_*`, `congrArg`; never `rw` under `‖coeff t f.1‖`; `smul_smul` not `mul_smul` on
   `TateAlgebra`; give the polyradius explicitly when a floor lemma is applied at `1`; pin `(Cφ := 1)` at
   `eval₂` call sites whose bound is a tactic block; `Submodule.Quotient.completeSpace` does not fire on
   `Restricted` quotients (use the shortcut instance of `Affinoid/Basic.lean`).
4. **Never `import Mathlib`** in a file that imports the floor, and never
   `Mathlib.RingTheory.PowerSeries.Restricted` or `Mathlib.RingTheory.Polynomial.GaussNorm`. Imports stay
   minimal per file; when a proof needs an unimported module, add exactly that module (the tickets name the
   two that are known to be missing: `Mathlib.RingTheory.Filtration`, `Mathlib.RingTheory.Localization.Finiteness`).
5. **Build** with `lake build PhD.TauCeti.Code.RigidAnalyticGeometry.<Module>` (or
   `PhD.TauCeti.Code.PadicFunctionalAnalysis.PowerBounded`) — never `lake build PhD`. There is no `timeout`
   binary on this machine: use the tool timeout and check exit codes. **One Lean process at a time**; do not
   kill processes you did not start. Changing `TateAlgebra/Eval.lean` or `Restricted/Algebra.lean` rebuilds
   Layer 0's cone (about 3 minutes): keep those edits to their tickets.
6. **Section variables.** All theorems carry their sections' instances (Lean includes an instance variable
   whenever its carrier is mentioned); the elaborated signatures are in `scratch/signatures.txt`. If a proof
   seems to need a hypothesis the signature lacks, read the sketch — it names the route that avoids it.
7. **Done means**: the module builds with no `sorry` in the ticket's declarations, `#print axioms` on each
   shows only `propext`, `Classical.choice`, `Quot.sound`, and the ticket's Status line is updated here.
8. **Cleanup tickets are done inline by the main agent** (no Agent-dispatched cleanup workers), with
   `lake exe runLinter` on the module.
9. **Sentinel ownership.** `.mathlib-quality/beastmode_active` may belong to a parallel instance: `cat` it
   before acting, and delete it only if its `BOARD:` line names this board.
10. **Mathlib first.** Every name in a "Mathlib lemmas needed" block was checked by elaboration against the
    pinned Mathlib (`scratch/names_tickets_mathlib.lean`, generated by `scratch/extract_names.py`) and every
    floor, chain and board name by `scratch/names_tickets_chain.lean`; both elaborate with no error. Names
    marked **(search)** in a sketch are the two places where the exact Mathlib name was not pinned down at
    planning time; find them with the five-method search before writing. `T0xx` in a sketch refers to an
    earlier ticket of this board; `L<group>.<n>` to a leaf of `decomposition.md`.
11. **Readable proofs** (user preference): explicit `ring` identities, `mul_nonneg`, `linarith` over opaque
    `nlinarith`; `omega`, not `lia`.
12. **Commit or push only when the user asks.**

## Roadmap deviations and errata (full text in `plan.md`)

V1 §1.3.2 proved by BGR 3.7.5/1 (closed graph), not Bosch's sup-norm route · V2 §1.4.2 completion model
not built (density of `A[g⁻¹]` only) · V3 §1.4.3–1.4.4 off the board · V4 §1.5.2 by BGR's finite
monomorphism, "only if" deferred to Layer 2 · V5 the tensor universal property holds for all Banach
algebras · V6 Japanese in characteristic zero · V7 `K' ⊗_K A` with `K'` on the left, no norm · E1
`IsClosed` as an instance, completeness shortcut · E2 `A⟨X⟩ ≅ A ⊗̂ T_m` replaced by "`A⟨X⟩` affinoid" ·
E3 `comap` of a maximal ideal needs only the target affinoid · E4 `⋂ 𝔪^ν = 0` needs noetherianity only ·
E6 `ρᵢ^s ∈ |K^×|`, the open-disc example holds for every `ρ`.

## Dependency order

The tickets below are listed in this order.

```text
G0  floor restoration   T001 → CLEANUP-1 · T002 → T003 → CLEANUP-2 · CLEANUP-ALL-1 → T004 [M1] → CLEANUP-3
G1  NormedQuotient      T005 → T006 → CLEANUP-4
G2  Sum                 (T003) T007 → T008 → T009 → CLEANUP-5 → T010 → CLEANUP-6
G3  Affinoid/Basic      (T005) T011 · T012 · T013 → CLEANUP-7
G4  Affinoid/Extend     (T002, T004) T014 → (T001, T003) T015 → T016 → CLEANUP-8 → T017 · T018 → T019
                        → CLEANUP-9 → (T010, T013) T020 → CLEANUP-10
G5  Banach/Noetherian   T021 · T022 → T023 → CLEANUP-11
G6  Banach/Continuity   T024 → T025 → (T023) T026 → CLEANUP-12
G7  Affinoid/Noether    T027 → T028 → T029 → CLEANUP-13 → CLEANUP-ALL-2 → T030 [M2] → T031 · T032
                        → CLEANUP-14 → T033 · T034 → T035 → CLEANUP-15
G8  Affinoid/Continuity (T033) T036 → CLEANUP-ALL-3 → (T026) T037 [M3] → T038 → CLEANUP-16
                        → (T020) T039 · (T019, T009, T010) T040 → (T006) T041 → CLEANUP-17
G9  Affinoid/Tensor     (T015) T042 · T043 · (T037) T044 → CLEANUP-18 → T045 · T046 → CLEANUP-ALL-4
                        → (T016, T040) T047 [M4] → T048 → CLEANUP-19
G10 Affinoid/Fractions  (T004) T049 · (T014, T018) T050 → (T016, T040) T051 → CLEANUP-20 · T052
                        → CLEANUP-ALL-5 → T053 [M5] → T054 → CLEANUP-21
G11 Affinoid/BaseChange (T001) T055 → T056 → T057 → CLEANUP-22
G12 Affinoid/Polydisc   (T003) T058 → T059 → (T020) T060 → CLEANUP-23
G13 Affinoid/Examples   (T013) T061 · T062 · (T005, T009, T010) T063 → CLEANUP-24
End                     all final per-file cleanups → T064 (chain root) → CLEANUP-FINAL
```

Cleanup cadence: a `/cleanup` after every third proof ticket on a file and after the last one; a
`/cleanup-all` before each milestone; a final `/cleanup-all`. On `Affinoid/Tensor.lean` the pre-milestone
sweep `CLEANUP-ALL-4` is the mid-file cleanup.
