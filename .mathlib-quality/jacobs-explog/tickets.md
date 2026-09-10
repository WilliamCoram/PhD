# Ticket Board — jacobs-explog (JacobsSlash → LWX.PadicExpLog dedup)

**BOARD PATH: `.mathlib-quality/jacobs-explog/`** — name it in every invocation.
Other boards (`lwx-halo/`, `jacobs/`, `qmf/`, root NewtonPolygons, …) are other
projects' property — never touch them, except the one sanctioned cross-edit in R3
(close out [FUTURE-JacobsExpLog] on lwx-halo with a pointer here).

Read `plan.md` (this directory) first: it records the 2026-09-04 recon (no import
cycle, p-free defs, rfl cast seam, `Nat.fact_prime_three`, the exact
export/shim/delete census). Governing house rules: no duplicate code; every
deletion/rename → this board's `renames.jsonl`; `lia` → `omega`; never touch
`PhD/PR'd/` or `PhD/LegacyCode/`; another agent may build concurrently — never
kill a running `lake build`.

## Summary
- Total: 3 | Open: 0 | In Progress: 0 | Done: 3 — **BOARD COMPLETE 2026-09-05**

## Dependency front
```
R1 → R2 → R3
```

### [R1] Delete the duplicated sections; wire the p := 3 shim layer
- **Status**: done (2026-09-05) | **File**: PhD/JacobsSlash/1_PadicAnalytic.lean
  | **Type**: refactor
- **Statement**: Add `import PhD.LWX.PadicExpLog`. Delete §§ResidueChar/NatAux/
  LogExp (lines ≈46–781). In `namespace JacobsSlash`: `export LWX.PadicExpLog
  (padicLog padicExp padicLog_one padicExp_zero
  norm_eq_one_of_norm_sub_one_lt_one)`; re-add `private norm_three_pos`; add the
  eight signature-preserving shims (`norm_natCast_eq_one_of_coprime`,
  `sq_norm_factorial_ge`, `norm_padicLog_le`, `norm_padicExp_sub_one_le`,
  `padicExp_add`, `norm_padicLog_eq`, `padicExp_padicLog`, `padicLog_mul`), each
  a one-liner into `LWX.PadicExpLog.*` at `p := 3` with `hp2 := by norm_num`.
  §§UnitPow/Binomial stay verbatim. Update the module docstring.
- **Gate**: `lake build PhD.JacobsSlash.«1_PadicAnalytic»` green, sorry-free.
- **Progress**:
  - 2026-09-05: done as specified. 1_PadicAnalytic.lean 912 → 234 lines (imports now
    just `Mathlib.RingTheory.PowerSeries.Basic` + `PhD.LWX.PadicExpLog`); 5 exports,
    `private norm_three_pos` re-added, 8 one-line shims with the old omit-guards
    mirrored; §§UnitPow/Binomial verbatim. `Nat.cast_ofNat` seam accepted by defeq
    everywhere — no bridging rewrites needed. `lake build` green (1856 jobs), zero
    warnings on the file. Original saved to scratchpad for the session only.

### [R2] Rebuild the downstream JacobsSlash tree
- **Status**: done (2026-09-05) | **Files**: 2_U3Data, 3_*, 4_*, 5_*, U3/*, CN1/*
  | **Depends on**: R1 | **Type**: verify/fix
- **Statement**: Build every downstream module (leaves per PROGRESS.md). Expected
  zero call-site edits (shims preserve signatures; exports preserve identity +
  simp attrs). Fix any residue at the call site ONLY if a shim cannot express the
  old signature — record any such edit here.
- **Gate**: full JacobsSlash tree green, no LegacyCode/PR'd edits.
- **Progress**:
  - 2026-09-05: all 30 JacobsSlash modules (1_–5_, U3/*, CN1/*; no importers of
    JacobsSlash exist outside the folder besides LegacyCode) built green, 3799 jobs,
    with ZERO downstream edits. Only pre-existing unusedVariables notes elsewhere.

### [R3] Lint, renames, docs, board close-out
- **Status**: done (2026-09-05) | **Depends on**: R2 | **Type**: cleanup
- **Statement**: `lake exe runLinter PhD.JacobsSlash.«1_PadicAnalytic»`; write all
  name moves/deletions to this board's `renames.jsonl` (old JacobsSlash name →
  `LWX.PadicExpLog.*` or `deleted-shimmed`); update
  PhD/JacobsSlash/PROGRESS.md (1_PadicAnalytic now = shim layer + UnitPow/
  Binomial); close [FUTURE-JacobsExpLog] on the lwx-halo board with a pointer
  here.
- **Gate**: linter clean; renames.jsonl complete; both boards consistent.
- **Progress**:
  - 2026-09-05: `lake exe runLinter PhD.JacobsSlash.«1_PadicAnalytic»` passed; all shim
    and surviving decls on standard axioms (propext/choice/Quot.sound); renames.jsonl
    written (27 entries: 5 export, 8 shim, 12 delete, 1 private-helpers, 1 keep);
    PROGRESS.md row for 1_PadicAnalytic rewritten; [FUTURE-JacobsExpLog] on lwx-halo
    marked MOVED with a pointer here. No file under PhD/LegacyCode or PhD/PR'd touched.
