#!/usr/bin/env python3
import pathlib, runpy, datetime
G = pathlib.Path(__file__).parent
ns = runpy.run_path(str(G / "gen_tickets.py"))
for part in ["tickets_p2.py", "tickets_p3.py", "tickets_p4.py"]:
    exec(compile((G / part).read_text(), str(G / part), "exec"), ns)
T = ns["T"]; extract = ns["extract"]; OUT = ns["OUT"]
proof = [t for t in T if not t.get("cleanup")]
cleans = [t for t in T if t.get("cleanup")]
out = []
out.append(f"""# Ticket board: Tau Ceti `PadicFunctionalAnalysis`, Layer 2 (the model space and orthonormal bases)

**Board**: `.mathlib-quality/tauceti-pfa-layer2/` (a *named* board: always pass this path to `/beastmode`;
the default board belongs to another project, and the other `tauceti-*` boards are parallel boards).
**Plan**: `plan.md` · **Decomposition (quotes, attacks, gate)**: `decomposition.md` · **References**: `references/*`
**Roadmap**: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, Layer 2 (§2.1–§2.7, README l. 585–758) — cited as [RM].
**Code**: `PhD/TauCeti/Code/PadicFunctionalAnalysis/{{ModelSpace/{{Basic,Universal,Reindex,Map,Truncation,Matrix,Dual,Closed,Examples}},
Orthogonal,ONable,Serre,CountableType,Unitriangular}}.lean` — fourteen files, every declaration already stated with `sorry`
(256 declarations, 262 `sorry`s). Planned 2026-10-06. Status: **PLANNED — awaiting plan approval; no ticket started.**

## Summary

| | Count |
|---|---|
| Proof / definition / integration tickets | {len(proof)} (`T001`–`T056`) |
| Per-file cleanups | {len([c for c in cleans if c['id'].startswith('CLEANUP-') and c['id'][8:].isdigit()])} (`CLEANUP-1`–`CLEANUP-24`) |
| Pre-milestone sweeps | 5 (`CLEANUP-ALL-1`–`CLEANUP-ALL-5`) |
| Final sweep | 1 (`CLEANUP-FINAL`) |
| **Total** | **{len(T)}** |

- **Milestone M1** = `T023`: orthonormalisable ⟺ has an orthonormal basis (`Module.isONable_iff_exists_isOrthonormalBasis`) — [RM] §2.2.3.
- **Milestone M2** = `T032`: Serre's theorem over a discretely valued field (`Module.isPotentiallyONable_of_isRankOneDiscrete`,
  `Module.isONable_iff_forall_exists_norm_eq`) — [RM] §2.3.3.
- **Milestone M3** = `T036`: Schneider's Proposition 10.4 (`Module.IsCountableType.exists_continuousLinearEquiv_nat`) — [RM] §2.4.1.
- **Milestone M4** = `T047`: finitely generated submodules of the model space are closed over a Noetherian ring (`isClosed_of_fg`) — [RM] §2.6.5.
- **Milestone M5** = `T051`: the unitriangular-perturbation criterion (`exists_linearIsometryEquiv`, `IsOrthonormalBasis.of_isUnitriangularPerturbation`) — [RM] §2.7.
- Skeleton gate (verified 2026-10-06, 2 688 jobs, 0 errors, one expected linter warning on `toBidual_apply`):
  `lake build PhD.TauCeti.Code.PadicFunctionalAnalysis.ModelSpace.Examples`.
- Tickets that can start immediately: `T001` (alone — it edits the shared `Orthonormal.lean` and two RAG proofs) and `T002`.

## Worker protocol (binding)

1. **The statements are fixed.** Every ticket's Statement block is copied verbatim from the skeleton by `scratch/gen/render.py`. Prove the
   statement as written. If a statement is false or unprovable as stated, that is a **B2 stop** with a concrete counterexample or obstruction —
   never silently change a hypothesis. Private helper lemmas are allowed and expected where a sketch says so; they follow the same conventions.
   Sub-tickets (Tier A) for the long tickets `T030`, `T035`, `T047`, `T050`, `T055` are expected.
2. **Chain separation.** Never `import PhD.Main.*` here (CI-gated), and never the reverse. `PhD/Main/` files cited as [SRC] are read-only
   references for proof ideas. Never delete `PhD/PR'd/` or legacy files.
3. **Build** with `lake build PhD.TauCeti.Code.PadicFunctionalAnalysis.<Module>` (e.g. `…ModelSpace.Basic`, `…Orthogonal`) — never
   `lake build PhD`. There is no `timeout` binary on this machine: use the tool timeout and check exit codes. Run one Lean process at a time.
4. **Imports stay minimal per file** (never `import Mathlib` in a `Code/` file). When a proof needs an unimported module, add exactly that module.
5. **Scopes and instances.** `open scoped ContinuousLinearMap.Ultra` activates Layer 1's operator norm; inside `namespace ContinuousLinearMap.Ultra`
   write `Ultra.le_opNorm` when the elaborator complains. The dual example for `ℚ_p` (`T052`) deliberately uses Mathlib's instance. A `def` whose
   proofs are `sorry` currently lacks the instance arguments those proofs will need (plan decision 10): when a signature grows, re-check its users.
6. **Done means**: the module builds with no `sorry` in the ticket's declarations, `#print axioms` on each shows only `propext`,
   `Classical.choice`, `Quot.sound`, and the ticket's Status line is updated here (`scratch/gen/mark.py <ID> <status> [progress]`).
7. **Cleanup tickets are done inline by the main agent** (no Agent-dispatched cleanup workers), with `lake exe runLinter` on the module.
8. **Sentinel ownership.** `.mathlib-quality/beastmode_active` may belong to a parallel instance: `cat` it before acting, and delete it only if
   its `BOARD:` line names this board. Other `tauceti-*` boards are parallel; never touch their files.
9. **Mathlib first.** Every Mathlib name in a "Mathlib lemmas needed" block was checked by elaboration against the pinned Mathlib
   (`scratch/names*.lean`, five files, ≈ 420 names), except where a sketch says "or …"/"-type" and gives the fallback; Layer 0/1 names are
   marked [L0]/[L1], Newton-polygon names [NP]. `Txxx` refers to an earlier ticket of this board.
10. **Conventions** (plan §"Generality and design decisions"): weakest hypotheses the source allows; commutative scalars only for matrix
    products; explicit bounds and explicit ring arguments; one conclusion per declaration; one-line `Source:` docstrings; readable arithmetic
    (`ring` identity + `mul_le_mul` + `linarith` over `nlinarith`); `omega` not `lia`.
11. **Commit or push only when the user asks.**

## Roadmap errata (found while planning; see `plan.md` for the full table)

E19 orthonormal must be `‖∑ aᵢ eᵢ‖ = max ‖aᵢ‖` over rings (torsion counterexample; T001) · E20 family predicates stay root-level, module predicates in
`Module` · E21 linear independence of orthogonal families needs a multiplicative action · E22 dense range of a diagonal operator needs units ·
E23 the value group of `ℂ_p` is not in Mathlib (hypothesis) · E24 §2.4.2's discretely valued orthogonal basis is off the board (no source text) ·
E25 §2.4.3's closed subspaces via Prop 10.5 · E26 `ofBounded` needs an ultrametric complete target, Tate only for the converse · E27 matrix
formulas over commutative rings · E28 the field dual example for Mathlib's norm · E29 the lifting characterisation's universes.

## Dependency order

```text
G0  Orthonormal (shared)  T001 (alone; then rebuild the chain)
G1  Basic                 T002 → {{T003 ∥ T004}} → CLEANUP-1 → T005 → CLEANUP-2
G2  Universal             CLEANUP-2 → T006 → T007 → T008 → CLEANUP-3
G3  Reindex               CLEANUP-2 → T009 → T010 → T011 → CLEANUP-4 → T012 → CLEANUP-5
G4  Map                   CLEANUP-5 → T013 → CLEANUP-6
G5  Truncation            CLEANUP-2 → T014 → {{T015 ∥ T016}} → CLEANUP-7
G6  Orthogonal            {{T001, CLEANUP-3}} → T017 → T018 → T019 → CLEANUP-8 → T020 → CLEANUP-9
G7  ONable                {{T020, CLEANUP-5, CLEANUP-7}} → T021 → T022 → CLEANUP-ALL-1 → T023 (M1) → CLEANUP-10 → T024 → {{T025 ∥ T026}} → CLEANUP-11 → T027 → CLEANUP-12
G8  Serre                 CLEANUP-12 → T028 → T029 → T030 → CLEANUP-13 → T031 → CLEANUP-ALL-2 → T032 (M2) → T033 → CLEANUP-14
G9  CountableType         CLEANUP-14 → T034 → T035 → CLEANUP-ALL-3 → T036 (M3) → CLEANUP-15 → T037 → CLEANUP-16
G10 Matrix                {{CLEANUP-3, CLEANUP-6}} → T038 → T039 → T040 → CLEANUP-17 → T041 → T042 → CLEANUP-18
G11 Dual                  CLEANUP-17 → T043 → T044 → T045 (needs CLEANUP-12) → CLEANUP-19
G12 Closed                {{CLEANUP-7, CLEANUP-17}} → T046 → CLEANUP-ALL-4 → T047 (M4) → CLEANUP-20
G13 Unitriangular         {{CLEANUP-17, CLEANUP-12}} → T048 → T049 → T050 → CLEANUP-21 → CLEANUP-ALL-5 → T051 (M5) → CLEANUP-22
G14 Examples              {{CLEANUP-16, CLEANUP-19, CLEANUP-20, CLEANUP-22}} → T052 → {{T053 ∥ T054}} → CLEANUP-23 → T055 → CLEANUP-24
Root                      CLEANUP-24 → T056 → CLEANUP-FINAL
```

## Tickets
""")
for t in T:
    if t.get("cleanup"):
        tgt = f"`{t['file']}`" if t['file'] != "project" else "the project"
        cmd = "/cleanup-all" if t['file'] == "project" else "/cleanup"
        out.append(f"""### [{t['id']}] Run `{cmd}` on {tgt}
- **Status**: open · **File**: {tgt} · **Depends on**: {t['deps']} · **Parallel**: no · **Type**: cleanup
- **Description**: {t['note']}. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).
""")
        continue
    if t['decls']:
        stmt = "\n\n".join(extract(t['file'], k) for k in t['decls'])
    elif t['id'] == "T001":
        stmt = "-- the new second conjunct of `IsOrthonormalFamily` (Orthonormal.lean):\n--   ∀ (s : Finset I) (a : I → R), ‖∑ i ∈ s, a i • e i‖₊ = s.sup fun i ↦ ‖a i‖₊\n-- all other statements of `Orthonormal.lean` and of the two RAG files are unchanged (only generalised to normed rings)."
    else:
        stmt = "(no Lean declaration — an edit of `PhD/TauCeti.lean`, the README, and the verification sweep)"
    out.append(f"""### [{t['id']}] {t['title']}
- **Status**: open · **File**: `{t['file']}` · **Depends on**: {t['deps']} · **Parallel**: {t['parallel']} · **Type**: {t['typ']}
- **Leaves**: {t['leaves']}

#### Statement
```lean
{stmt}
```
#### Proof sketch
{t['sketch']}

#### Mathlib lemmas needed
{t['lemmas']}
#### Sources
{t['sources']}
#### Generality decision
{t['generality']}
""")
OUT.write_text("\n".join(out))
print("tickets:", len(T), "proof:", len(proof), "cleanup:", len(cleans))
