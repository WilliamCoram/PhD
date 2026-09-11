# Ticket Board — `lwx-degrees` (the degrees at every classical weight, and [LWX, Cor 1.4])

**BOARD PATH: `.mathlib-quality/lwx-degrees/`.**  The default `.mathlib-quality/` board belongs to
the completed NewtonPolygons project — NEVER touch it; `.mathlib-quality/qmf/` and its
`beastmode_active` sentinel belong to a parallel run — NEVER touch them either.  Every
`/beastmode` run must name this board path explicitly, and delete only
`.mathlib-quality/lwx-degrees/beastmode_active` and the root `.mathlib-quality/beastmode_active`
when its first line names this board (cat before rm).

**Files owned by this board**: `PhD/LWX/DegreePeriodicity.lean` (new; complete and sorry-free since
2026-09-11).  Do not edit any other file except where a ticket names it (`CLEANUP-FINAL`:
`PhD.lean`'s import comment, `.mathlib-quality/lwx-stepone/FINDINGS.md`).  The templates are
`PhD/LWX/ConductorSlopes.lean` (`section Family`, `slopeRatio_mul_teichChar_pow`,
`slopeRatio_add_period`), `PhD/LWX/StepThree.lean` (`degX_succ`, `degXint_zero`),
`PhD/LWX/AtkinLehnerIdentity.lean` (`degX_succ_of_atkinLehnerData`).

**Build**: `lake build PhD.LWX.DegreePeriodicity`.  Statements are transcribed verbatim from the
compiling skeleton and are **protected** — if a statement is wrong, append to this board's
`b2_log.jsonl` rather than editing it.  `_hx`-slack convention applies.  `lake exe runLinter
PhD.LWX.DegreePeriodicity` is a gate for every cleanup (its output lists findings for the whole
closure; grep for `DegreePeriodicity.lean`).  `omega` not `lia`.  No `timeout` binary.  Cleanup
tickets are done inline by the main agent.  Traps: identities in `(ZMod p)ˣ →* ℤ_[p]ˣ` are proved
pointwise (`MonoidHom.ext` + `simp only [MonoidHom.mul_apply, MonoidHom.pow_apply,
MonoidHom.inv_apply, teichChar_apply, partnerChar_apply, targetChar_apply]` + algebra in `ℤ_[p]ˣ`),
never by `rw [mul_assoc]`/`mul_one` on the homs; never `set` the `UpDatum` (use `generalize … at`
after the lemma instances exist); `omega` atomises `touchX …` and `p * Fintype.card ι` (`generalize
p * Fintype.card ι = N at …` first); `omit … in` goes before the docstring; every proof-only section
hypothesis is in the `include … in` line (the `lwx-conductor` B2).

**Read before working any ticket**: `plan.md`, `decomposition.md`, and
`.mathlib-quality/lwx-stepone/JL-AUDIT.md`.  Nothing here depends on Jacquet–Langlands.

**Tickets that ADD a declaration** (marked `[NEW DECL]`): none at planning time; a worker who
spawns a helper must give it a ticket in this format.  Execution added one: **D22**
`mul_teichChar_pow_two_mul_sub_one_div_two` (spawned at CLEANUP-D-FINAL, shared by D20/D21).

## Summary

Planned 2026-09-11 (`/develop`); executed the same day (`/beastmode`, see the execution record).  21 proof tickets + 10 cleanup tickets in one
file; milestones **D15** (`degXint_pos_of_atkinLehnerFamily`: with D11, D14 and the existing
`degX_zero`, every degree statement of [LWX, Thm 1.3] at the coefficient level, at every classical
weight, granted the family) and **D21** (`degXint_add_period`, with D20: [LWX, Cor 1.4]).
Parallelism: D1–D8 are independent of everything; D9, D10, D11, D12 are independent of each other
(each a direct application of a level-`1` lemma at the family's data); D13 needs D9, D10; D14 needs
D3, D4, D12, D13; D15 needs D8, D14; D16 needs D5, D6, D11; D17 needs D5, D7, D14; D18/D19 need
D1, D2 and D16/D17; D20/D21 need D18/D19.

### Skeleton build record (2026-09-11)
`lake build PhD.LWX.DegreePeriodicity` — **Build completed successfully (3830 jobs)**, 21 `sorry` warnings and no other warning or error in the new file (no unused-section-variable finding; the `include` lists are complete).

### Execution record (2026-09-11, `/beastmode`)
All 21 proof tickets proved — every planned sketch compiled on the first build (3830 jobs, no error,
no warning in the new file) — and all 10 cleanup tickets done inline; one helper was added at
cleanup (D22 `[NEW DECL]`).  Final gate: `lake build PhD.LWX.DegreePeriodicity` — **Build completed
successfully (3830 jobs)**, no warning in the file; no `sorry`; `#print axioms` =
`[propext, Classical.choice, Quot.sound]` for the milestones D15 `degXint_pos_of_atkinLehnerFamily`,
D20 `degX_succ_add_period`, D21 `degXint_add_period` and for D11, D16, D17, D22;
`#lint in PhD.LWX.DegreePeriodicity` (scratch file) — **0 errors in 22 declarations, 14 linters**;
`lake exe runLinter PhD.LWX.DegreePeriodicity` lints the whole `PhD` closure — 100 findings, none in
`DegreePeriodicity.lean` (all pre-existing, e.g. `TateFredholm/Tate.lean`, `LWX/ClassicalPoint.lean`).
`lake build PhD` (the root, `PhD.lean` with the updated comment) — **Build completed successfully
(3921 jobs)**.
Cleanup changes: D4 and D8–D12 became term-mode proofs; D20/D21 became one `rw` each through D22;
`rw` lists re-indented and every line kept within 100 columns; the header's "SKELETON" marker
removed.  Slack hypotheses (`_hx`): none (no unused-variable or unused-section-variable finding).
B2: none (`b2_log.jsonl` empty).  No name clash with any other `PhD/` declaration (grep).

**Stale blueprint sentences** (NOT edited — needs the user's go-ahead), all in
`blueprint/src/chapter/LWXSlopes.tex`:
* `:354–362`, §(c) "The arithmetic progressions": "(1.5.2) … is *not* formalised … Nothing in our
  development compares two nebentypi, so no periodicity statement can even be phrased" — stale
  since `lwx-conductor` (`LWX.slopeRatio_mul_teichChar_sq`, `LWX.slopeRatio_add_period`);
* `:372–374`: "The same remark applies to [LWX, Corollary 1.4], the periodicity of
  `deg X_{I,ω}` modulo `φ(q)/2` … likewise not formalised" — now `LWX.degX_succ_mul_teichChar_sq`,
  `LWX.degXint_mul_teichChar_sq`, `LWX.degX_succ_add_period`, `LWX.degXint_add_period`;
* `:376–385`, §"Degrees": "Those identifications are again Step I, and again involve several
  nebentypi at once; they are not formalised" — now `LWX.degX_succ_of_atkinLehnerFamily`,
  `LWX.degXint_of_atkinLehnerFamily`, `LWX.degXint_pos_of_atkinLehnerFamily` (with `LWX.degX_zero`).

**Option for the user (not done)**: move D1–D7 and D22 to their natural homes (`TargetPoint.lean`,
`NebChar.lean`, `AtkinLehnerFamily.lean`) — then the inline `hpow` of
`slopeRatio_mul_teichChar_pow` in `ConductorSlopes.lean` is `mul_teichChar_pow_succ` — and D8 to
`Degrees.lean`, where it shortens the two inline `hord` bounds of `StepThree.lean`
(`touchX_sub_leftIndex_eq_ordDim`, `degX_succ`).

**Addendum (2026-09-11, after completion, with the user's go-ahead) — both options above done.**
(1) The helpers moved to their natural homes: D1–D4, D6, D7 to `PhD/LWX/TargetPoint.lean` (new
subsection "The shift `(k, ω) ↦ (k + 1, ωω₀²)` on the characters"), D5 to `PhD/LWX/NebChar.lean`
(stated on the file's section variables `ω k`, same signature), D22 to
`PhD/LWX/AtkinLehnerFamily.lean`, D8 to `PhD/LWX/Degrees.lean`; names and signatures unchanged, so
every call site in `DegreePeriodicity.lean` is untouched.  The inline copies now use them:
`slopeRatio_mul_teichChar_pow` (D1, D2) and `slopeRatio_add_period` (D22) in `ConductorSlopes.lean`,
and the two `hord` bounds of `touchX_sub_leftIndex_eq_ordDim` and `degX_succ` (D8) in
`StepThree.lean`.  (2) `blueprint/src/chapter/LWXSlopes.tex` brought up to date: the three stale
passages above rewritten, and — because §"Towards Theorem 1.3: what remains" and the ledger stated
the same results as unformalised — that section rewritten as §"Theorem 1.3: Steps I and III"
(label `sec:stepone` kept) with new environments `def:al-data`, `prop:al-identity`,
`prop:theta-exact`, `thm:lwx-stepone`, `thm:lwx-unitband`, `thm:lwx13-degrees`, `cor:lwx14`,
`thm:lwx152` (all `\leanok`), `def:conjchar`/`prop:theta`/`prop:finite-factor` given their Lean
references, and the ledger's status column, five-object list and closing summary updated.

### B2 log
empty at planning time (`b2_log.jsonl`).

## Ticket index

| ID | Declaration | File | Type |
|---|---|---|---|
| D1 | `mul_teichChar_pow_zero` | DegreePeriodicity | proof/def |
| D2 | `mul_teichChar_pow_succ` | DegreePeriodicity | proof/def |
| D3 | `mul_inv_teichChar_pow_zero` | DegreePeriodicity | proof/def |
| CLEANUP-D1 | `CLEANUP-D1` | DegreePeriodicity | cleanup |
| D4 | `targetChar_eq_mul_inv_teichChar_pow` | DegreePeriodicity | proof/def |
| D5 | `partnerChar_mul_teichChar_sq_succ` | DegreePeriodicity | proof/def |
| D6 | `targetChar_mul_teichChar_sq_succ` | DegreePeriodicity | proof/def |
| CLEANUP-D2 | `CLEANUP-D2` | DegreePeriodicity | cleanup |
| D7 | `mul_teichChar_sq_mul_inv_teichChar_pow_succ` | DegreePeriodicity | proof/def |
| D8 | `ordDim_le_card` | DegreePeriodicity | proof/def |
| D9 | `touchX_sub_leftIndex_eq_ordDim_of_atkinLehnerFamily` | DegreePeriodicity | proof/def |
| CLEANUP-D3 | `CLEANUP-D3` | DegreePeriodicity | cleanup |
| D10 | `rightIndex_sub_touchX_eq_ordDim_of_atkinLehnerFamily` | DegreePeriodicity | proof/def |
| D11 | `degX_succ_of_atkinLehnerFamily` | DegreePeriodicity | proof/def |
| D12 | `degXint_zero_of_atkinLehnerFamily` | DegreePeriodicity | proof/def |
| CLEANUP-D4 | `CLEANUP-D4` | DegreePeriodicity | cleanup |
| D13 | `degXint_succ_of_atkinLehnerFamily` | DegreePeriodicity | proof/def |
| D14 | `degXint_of_atkinLehnerFamily` | DegreePeriodicity | proof/def |
| CLEANUP-ALL-1 | `CLEANUP-ALL-1` | DegreePeriodicity | cleanup |
| D15 | `degXint_pos_of_atkinLehnerFamily` **[MILESTONE]** | DegreePeriodicity | proof/def |
| CLEANUP-D5 | `CLEANUP-D5` | DegreePeriodicity | cleanup |
| D16 | `degX_succ_mul_teichChar_sq` | DegreePeriodicity | proof/def |
| D17 | `degXint_mul_teichChar_sq` | DegreePeriodicity | proof/def |
| D18 | `degX_succ_mul_teichChar_pow` | DegreePeriodicity | proof/def |
| CLEANUP-D6 | `CLEANUP-D6` | DegreePeriodicity | cleanup |
| D19 | `degXint_mul_teichChar_pow` | DegreePeriodicity | proof/def |
| CLEANUP-ALL-2 | `CLEANUP-ALL-2` | DegreePeriodicity | cleanup |
| D20 | `degX_succ_add_period` | DegreePeriodicity | proof/def |
| D21 | `degXint_add_period` **[MILESTONE]** | DegreePeriodicity | proof/def |
| D22 | `mul_teichChar_pow_two_mul_sub_one_div_two` **[NEW DECL]** | DegreePeriodicity | proof/def |
| CLEANUP-D-FINAL | `CLEANUP-D-FINAL` | DegreePeriodicity | cleanup |
| CLEANUP-FINAL | `CLEANUP-FINAL` | all | cleanup |

## Tickets

### [D1] `mul_teichChar_pow_zero`
- **Status**: done (2026-09-11 beastmode)
- **File**: PhD/LWX/DegreePeriodicity.lean (line 43)
- **Depends on**: none beyond the file
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `ω·ω₀^{2·0} = ω`. -/
theorem mul_teichChar_pow_zero (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) : ω * teichChar p ^ (2 * 0) = ω := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `refine MonoidHom.ext fun r => ?_` — the trap of `lwx-conductor`: identities in `(ZMod p)ˣ →* ℤ_[p]ˣ` are proved pointwise, never by `rw [mul_one]` on the homs.
2. `rw [MonoidHom.mul_apply, MonoidHom.pow_apply, Nat.mul_zero, pow_zero, mul_one]` in `ℤ_[p]ˣ` (this exact line closed `hω` in `ConductorSlopes.lean`'s `slopeRatio_mul_teichChar_pow`).

- **Mathlib/project lemmas needed**: `MonoidHom.ext`, `MonoidHom.mul_apply`, `MonoidHom.pow_apply`, `Nat.mul_zero`, `pow_zero`, `mul_one`
- **Sources**: [LWX] Notation `ω₀` `lwx.txt:121–122`; Cor 1.4 `lwx.txt:164–169` (the iterate at `m = 0`).
- **Generality decision**: `[Fact p.Prime]` only (needed for `teichChar`); stated with the literal exponent `2 * 0` because that is the shape the induction in D18/D19 produces.
- **Size**: 2 lines; source: none (definitional)
- **Progress**: done 2026-09-11 — pointwise (`MonoidHom.ext`, `mul_apply`/`pow_apply`, `Nat.mul_zero`, `pow_zero`, `mul_one`), as sketched; compiled first time (build 3830 jobs, no warning), standard axioms.

### [D2] `mul_teichChar_pow_succ`
- **Status**: done (2026-09-11 beastmode)
- **File**: PhD/LWX/DegreePeriodicity.lean (line 47)
- **Depends on**: none beyond the file
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `ω·ω₀^{2(m+1)} = (ω·ω₀^{2m})·ω₀²`. -/
theorem mul_teichChar_pow_succ (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (m : ℕ) :
    ω * teichChar p ^ (2 * (m + 1)) = ω * teichChar p ^ (2 * m) * teichChar p ^ 2 := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `refine MonoidHom.ext fun r => ?_`.
2. `rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.pow_apply, MonoidHom.pow_apply, mul_assoc, ← pow_add, mul_add, mul_one]` — verbatim the `hpow` of `slopeRatio_mul_teichChar_pow` (`ConductorSlopes.lean`), which compiled.  (`2 * (m + 1) = 2 * m + 2` is `Nat.mul_succ`; after `← pow_add` the exponents are `2 * m + 2` on both sides once `mul_add, mul_one` normalise `2 * (m + 1)`.)

- **Mathlib/project lemmas needed**: `MonoidHom.ext`, `MonoidHom.mul_apply`, `MonoidHom.pow_apply`, `mul_assoc`, `pow_add`, `mul_add`, `mul_one`
- **Sources**: [LWX] Cor 1.4 `lwx.txt:164–169` (the inductive step of the iterate).
- **Generality decision**: `[Fact p.Prime]` only.
- **Size**: 3 lines; source: none
- **Progress**: done 2026-09-11 — pointwise, the `hpow` proof of `slopeRatio_mul_teichChar_pow` verbatim; compiled first time (build 3830 jobs, no warning), standard axioms.

### [D3] `mul_inv_teichChar_pow_zero`
- **Status**: done (2026-09-11 beastmode)
- **File**: PhD/LWX/DegreePeriodicity.lean (line 52)
- **Depends on**: none beyond the file
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `ω·ω₀^{−2·0} = ω`. -/
theorem mul_inv_teichChar_pow_zero (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    ω * (teichChar p ^ (2 * 0))⁻¹ = ω := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `refine MonoidHom.ext fun r => ?_`.
2. `rw [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, Nat.mul_zero, pow_zero, inv_one, mul_one]`.

- **Mathlib/project lemmas needed**: `MonoidHom.ext`, `MonoidHom.mul_apply`, `MonoidHom.inv_apply`, `MonoidHom.pow_apply`, `Nat.mul_zero`, `pow_zero`, `inv_one`, `mul_one`
- **Sources**: [LWX] Thm 1.3 `lwx.txt:157–159` (`ωω₀^{−2n}` at `n = 0` is `ω`).
- **Generality decision**: `[Fact p.Prime]` only.
- **Size**: 2 lines; source: none
- **Progress**: done 2026-09-11 — pointwise with `MonoidHom.inv_apply`, `inv_one`; compiled first time (build 3830 jobs, no warning), standard axioms.

### [CLEANUP-D1] Cleanup `PhD/LWX/DegreePeriodicity.lean`
- **Status**: done (2026-09-11 beastmode, inline)
- **File**: PhD/LWX/DegreePeriodicity.lean
- **Depends on**: D1, D2, D3
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.DegreePeriodicity` and `lake exe runLinter PhD.LWX.DegreePeriodicity` must be
clean (grep the linter's output for `DegreePeriodicity.lean`).  Done inline by the main agent.

- **Progress**: done 2026-09-11 — D1–D21 were written in one pass and compiled with no warning, so the per-file cleanup ran once over the whole file at CLEANUP-D-FINAL; nothing specific to these declarations (no unused hypothesis, no `simp` call, no `omit` needed, names as planned).

### [D4] `targetChar_eq_mul_inv_teichChar_pow`
- **Status**: done (2026-09-11 beastmode)
- **File**: PhD/LWX/DegreePeriodicity.lean (line 58)
- **Depends on**: CLEANUP-D1
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The target nebentypus `ωω₀^{−2k−2}` of weight `k` is `ωω₀^{−2(k+1)}`
([LWX, §3.23 Step III], `lwx.txt:2079–2097`: the second term of `deg X_{(k,k+1),ω}` at `k + 1`). -/
theorem targetChar_eq_mul_inv_teichChar_pow (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    targetChar p ω k = ω * (teichChar p ^ (2 * (k + 1)))⁻¹ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `targetChar p ω k` unfolds to `ω * (teichChar p ^ (2 * k + 2))⁻¹` and `2 * (k + 1) = 2 * k + 2` is `rfl` (`Nat.mul_succ`; verified `example (k : ℕ) : 2 * (k + 1) = 2 * k + 2 := rfl`): try `rfl` first.
2. Fallback: `refine MonoidHom.ext fun r => ?_; rw [targetChar_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, teichChar_apply, Nat.mul_succ]`.

- **Mathlib/project lemmas needed**: `Nat.mul_succ`, `targetChar_apply`, `MonoidHom.ext`, `MonoidHom.mul_apply`, `MonoidHom.inv_apply`, `MonoidHom.pow_apply`, `teichChar_apply`
- **Sources**: [LWX] Step III `lwx.txt:2079–2097` (the second term `r_ord(ωω₀^{−2k})` of `deg X_{(k,k+1),ω}` is the right-gap character `ωω₀^{−2(k−1)−2}` of the previous weight).
- **Generality decision**: `[Fact p.Prime]` only.
- **Size**: 1–2 lines; source: none
- **Progress**: done 2026-09-11 — `rfl` (`2 * (k + 1)` and `2 * k + 2` are definitionally equal); compiled first time (build 3830 jobs, no warning), standard axioms.

### [D5] `partnerChar_mul_teichChar_sq_succ`
- **Status**: done (2026-09-11 beastmode)
- **File**: PhD/LWX/DegreePeriodicity.lean (line 64)
- **Depends on**: none beyond the file
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The partner nebentypus of `(ωω₀², k+1)` is that of `(ω, k)`:
`(ωω₀²)⁻¹ω₀^{2(k+1)} = ω⁻¹ω₀^{2k}` ([LWX, Cor 1.4], `lwx.txt:164–166`). -/
theorem partnerChar_mul_teichChar_sq_succ (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    partnerChar p (ω * teichChar p ^ 2) (k + 1) = partnerChar p ω k := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `refine MonoidHom.ext fun r => ?_`.
2. `simp only [partnerChar_apply, MonoidHom.mul_apply, MonoidHom.pow_apply, teichChar_apply]` — goal in `ℤ_[p]ˣ`: `(ω r * teichRes r ^ 2)⁻¹ * teichRes r ^ (2 * (k + 1)) = (ω r)⁻¹ * teichRes r ^ (2 * k)`.
3. `rw [mul_inv, show 2 * (k + 1) = 2 + 2 * k by ring, pow_add, mul_assoc, inv_mul_cancel_left]` (`inv_mul_cancel_left : a⁻¹ * (a * b) = b` with `a = teichRes r ^ 2`).

- **Mathlib/project lemmas needed**: `MonoidHom.ext`, `partnerChar_apply`, `MonoidHom.mul_apply`, `MonoidHom.pow_apply`, `teichChar_apply`, `mul_inv`, `pow_add`, `mul_assoc`, `inv_mul_cancel_left`
- **Sources**: [LWX] Cor 1.4 `lwx.txt:164–166` (the substitution `(n, ω) ↦ (n+1, ωω₀²)` in the first term of Thm 1.3's `deg X_{n,ω}`, `lwx.txt:153–154`).
- **Generality decision**: `[Fact p.Prime]` only; stated at `k + 1` because `partnerChar p (ωω₀²) 0 = ω⁻¹ω₀^{−2}` is **not** a partner character of `ω` (the corollary excludes `I = 0`).
- **Size**: 3 lines; source: none
- **Progress**: done 2026-09-11 — pointwise via `partnerChar_apply`, `mul_inv`, `pow_add (teichRes r) 2 (2 * k)`, `inv_mul_cancel_left`; compiled first time (build 3830 jobs, no warning), standard axioms.

### [D6] `targetChar_mul_teichChar_sq_succ`
- **Status**: done (2026-09-11 beastmode)
- **File**: PhD/LWX/DegreePeriodicity.lean (line 70)
- **Depends on**: none beyond the file
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- The target nebentypus of `(ωω₀², k+1)` is that of `(ω, k)`:
`ωω₀²·ω₀^{−2(k+1)−2} = ωω₀^{−2k−2}` ([LWX, Cor 1.4], `lwx.txt:164–166`). -/
theorem targetChar_mul_teichChar_sq_succ (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    targetChar p (ω * teichChar p ^ 2) (k + 1) = targetChar p ω k := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `refine MonoidHom.ext fun r => ?_`.
2. `simp only [targetChar_apply, MonoidHom.mul_apply, MonoidHom.pow_apply, teichChar_apply]` — goal: `ω r * teichRes r ^ 2 * (teichRes r ^ (2 * (k + 1) + 2))⁻¹ = ω r * (teichRes r ^ (2 * k + 2))⁻¹`.
3. `rw [show 2 * (k + 1) + 2 = 2 + (2 * k + 2) by ring, pow_add, mul_inv, mul_assoc, mul_inv_cancel_left]` (`mul_inv_cancel_left : a * (a⁻¹ * b) = b` with `a = teichRes r ^ 2`).

- **Mathlib/project lemmas needed**: `MonoidHom.ext`, `targetChar_apply`, `MonoidHom.mul_apply`, `MonoidHom.pow_apply`, `teichChar_apply`, `pow_add`, `mul_inv`, `mul_assoc`, `mul_inv_cancel_left`
- **Sources**: [LWX] Cor 1.4 `lwx.txt:164–166` (the substitution in the second term of `deg X_{n,ω}`, `lwx.txt:153–154`).
- **Generality decision**: `[Fact p.Prime]` only.
- **Size**: 3 lines; source: none
- **Progress**: done 2026-09-11 — pointwise via `targetChar_apply`, `pow_add (teichRes r) 2 (2 * k + 2)`, `mul_inv`, `mul_inv_cancel_left`; compiled first time (build 3830 jobs, no warning), standard axioms.

### [CLEANUP-D2] Cleanup `PhD/LWX/DegreePeriodicity.lean`
- **Status**: done (2026-09-11 beastmode, inline)
- **File**: PhD/LWX/DegreePeriodicity.lean
- **Depends on**: D4, D5, D6
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.DegreePeriodicity` and `lake exe runLinter PhD.LWX.DegreePeriodicity` must be
clean (grep the linter's output for `DegreePeriodicity.lean`).  Done inline by the main agent.

- **Progress**: done 2026-09-11 — D1–D21 were written in one pass and compiled with no warning, so the per-file cleanup ran once over the whole file at CLEANUP-D-FINAL; nothing specific to these declarations (no unused hypothesis, no `simp` call, no `omit` needed, names as planned).

### [D7] `mul_teichChar_sq_mul_inv_teichChar_pow_succ`
- **Status**: done (2026-09-11 beastmode)
- **File**: PhD/LWX/DegreePeriodicity.lean (line 75)
- **Depends on**: CLEANUP-D2
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `ωω₀²·ω₀^{−2(n+1)} = ω·ω₀^{−2n}` ([LWX, Cor 1.4], `lwx.txt:164–166`). -/
theorem mul_teichChar_sq_mul_inv_teichChar_pow_succ (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
    ω * teichChar p ^ 2 * (teichChar p ^ (2 * (n + 1)))⁻¹ = ω * (teichChar p ^ (2 * n))⁻¹ := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `refine MonoidHom.ext fun r => ?_`.
2. `simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, teichChar_apply]` — goal: `ω r * teichRes r ^ 2 * (teichRes r ^ (2 * (n + 1)))⁻¹ = ω r * (teichRes r ^ (2 * n))⁻¹`.
3. `rw [show 2 * (n + 1) = 2 + 2 * n by ring, pow_add, mul_inv, mul_assoc, mul_inv_cancel_left]`.

- **Mathlib/project lemmas needed**: `MonoidHom.ext`, `MonoidHom.mul_apply`, `MonoidHom.inv_apply`, `MonoidHom.pow_apply`, `teichChar_apply`, `pow_add`, `mul_inv`, `mul_assoc`, `mul_inv_cancel_left`
- **Sources**: [LWX] Cor 1.4 `lwx.txt:164–166` (the substitution in the second term of `deg X_{(n,n+1),ω}`, `lwx.txt:157–159`).
- **Generality decision**: `[Fact p.Prime]` only; stated for every `n ≥ 0` (the open-interval case of the corollary starts at `I = (0,1)`).
- **Size**: 3 lines; source: none
- **Progress**: done 2026-09-11 — pointwise, `pow_add (teichChar p r) 2 (2 * n)`, `mul_inv_cancel_left`; compiled first time (build 3830 jobs, no warning), standard axioms.

### [D8] `ordDim_le_card`
- **Status**: done (2026-09-11 beastmode)
- **File**: PhD/LWX/DegreePeriodicity.lean (line 85)
- **Depends on**: none beyond the file
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
/-- `r_ord(ω) ≤ t`: the ordinary dimension is at most the number of blocks
(`le_card_of_isUnit_charCoeff` at the unit coefficient `ordDim`). -/
theorem ordDim_le_card (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    ordDim D ω ≤ Fintype.card ι := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. Term-mode: `le_card_of_isUnit_charCoeff D ω (isUnit_charCoeff_ordDim D ω)` (this is the `hord` step inside `degX_succ`, `StepThree.lean:944–950`, without the `touchX` bound).

- **Mathlib/project lemmas needed**: `le_card_of_isUnit_charCoeff`, `isUnit_charCoeff_ordDim`
- **Sources**: [LWX] `lwx.txt:123–127` (`t` = the dimension of the weight-2 space, `r_ord(ω)` the dimension of its ordinary subspace).
- **Generality decision**: Any `UpDatum p ι`, any `ω`; `[Fintype ι] [DecidableEq ι]` as `ordDim`.  Natural home `Degrees.lean` — kept here so that the board edits no completed file (a later cleanup may move it).
- **Size**: 1 line; source: implicit
- **Progress**: done 2026-09-11 — term `le_card_of_isUnit_charCoeff D ω (isUnit_charCoeff_ordDim D ω)`; compiled first time (build 3830 jobs, no warning), standard axioms.

### [D9] `touchX_sub_leftIndex_eq_ordDim_of_atkinLehnerFamily`
- **Status**: done (2026-09-11 beastmode)
- **File**: PhD/LWX/DegreePeriodicity.lean (line 121)
- **Depends on**: none beyond the file
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- **The left gap at every weight** ([LWX, §3.23 Step III], `lwx.txt:2025–2047`:
`n_{k+1} − n⁻_{k+1} = r_ord(ω⁻¹ω₀^{2k})`), granted the family of Atkin–Lehner data. -/
theorem touchX_sub_leftIndex_eq_ordDim_of_atkinLehnerFamily [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    touchX p (Fintype.card ι) (k + 1)
        - leftIndex (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
            hshape) ω (k + 1)
      = ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (partnerChar p ω k) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `have hpK := norm_natCast_p ψ hψ`.  The classical data at the family's root: `c₀ := classicalData ψ ω θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) uu hp2 hψ hζ hpK k`, `c₀' := classicalData ψ (partnerChar p ω k) … hζ.inv hpK k`, `d₀ := targetData_classicalPoint ψ ω … hζ hpK k`, `d₀' := targetData_classicalPoint ψ (partnerChar p ω k) … hζ.inv hpK k`, and H1 `hAL := atkinLehnerHypothesis_of_atkinLehnerData θG ψ U hU k ω hp2 hψ hζ hpK (AtkinLehnerFamily.toData θG ψ U F ω k) hfin hv hvinj c hc hstab idx uu d hd hfact` (its type mentions `vRepD θG ψ U (toData …)`, definitionally `vRepF θG ψ U F`, and `vRepD_mem_levelM1 …`, proof-irrelevantly `vRepF_mem_levelM1 …` — `exact` accepts it, as in `hasUnitBand_of_atkinLehnerData`, `ConductorSlopes.lean`).
2. `exact touchX_sub_leftIndex_eq_ordDim idx hp2 hψ hshape hdet c₀ c₀' d₀ d₀' hAL` (write the five terms inline; no `set`).
3. The conclusion's `ordDim … ω'` is `ordDim … (partnerChar p ω k)` because `c₀'` is the datum at the partner character.

- **Mathlib/project lemmas needed**: `touchX_sub_leftIndex_eq_ordDim`, `classicalData`, `targetData_classicalPoint`, `atkinLehnerHypothesis_of_atkinLehnerData`, `AtkinLehnerFamily.toData`, `norm_natCast_p`
- **Sources**: [LWX] Step III `lwx.txt:2025–2047`.
- **Generality decision**: Every `ω`, `k`; `[Nonempty ι] [IsAlgClosed K]`, `hp2`, `hζ : IsPrimitiveRoot ζ p` as the level-`1` lemma; `hdet` is consumed by `touchX_sub_leftIndex_eq_ordDim`.
- **Size**: ~12 lines (five terms); source: 5 lines
- **Progress**: done 2026-09-11 — term-mode `touchX_sub_leftIndex_eq_ordDim` at `classicalData`/`targetData_classicalPoint` stated at `vRepF` and H1 from `atkinLehnerHypothesis_of_atkinLehnerData … (AtkinLehnerFamily.toData θG ψ U F ω k)` (definitional match `vRepD (toData …) = vRepF`); compiled first time (build 3830 jobs, no warning), standard axioms.

### [CLEANUP-D3] Cleanup `PhD/LWX/DegreePeriodicity.lean`
- **Status**: done (2026-09-11 beastmode, inline)
- **File**: PhD/LWX/DegreePeriodicity.lean
- **Depends on**: D7, D8, D9
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.DegreePeriodicity` and `lake exe runLinter PhD.LWX.DegreePeriodicity` must be
clean (grep the linter's output for `DegreePeriodicity.lean`).  Done inline by the main agent.

- **Progress**: done 2026-09-11 — D1–D21 were written in one pass and compiled with no warning, so the per-file cleanup ran once over the whole file at CLEANUP-D-FINAL; nothing specific to these declarations (no unused hypothesis, no `simp` call, no `omit` needed, names as planned).

### [D10] `rightIndex_sub_touchX_eq_ordDim_of_atkinLehnerFamily`
- **Status**: done (2026-09-11 beastmode)
- **File**: PhD/LWX/DegreePeriodicity.lean (line 135)
- **Depends on**: CLEANUP-D3
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- **The right gap at every weight** ([LWX, §3.23 Step III], `lwx.txt:2048–2078`:
`n⁺_{k+1} − n_{k+1} = r_ord(ωω₀^{−2k−2})`), granted the family of Atkin–Lehner data (H2 is
`isThetaExact_classicalData`). -/
theorem rightIndex_sub_touchX_eq_ordDim_of_atkinLehnerFamily [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    rightIndex (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) ω (k + 1)
        - touchX p (Fintype.card ι) (k + 1)
      = ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (targetChar p ω k) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `have hpK := norm_natCast_p ψ hψ`.  The classical data at the family's root: `c₀ := classicalData ψ ω θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) uu hp2 hψ hζ hpK k`, `c₀' := classicalData ψ (partnerChar p ω k) … hζ.inv hpK k`, `d₀ := targetData_classicalPoint ψ ω … hζ hpK k`, `d₀' := targetData_classicalPoint ψ (partnerChar p ω k) … hζ.inv hpK k`, and H1 `hAL := atkinLehnerHypothesis_of_atkinLehnerData θG ψ U hU k ω hp2 hψ hζ hpK (AtkinLehnerFamily.toData θG ψ U F ω k) hfin hv hvinj c hc hstab idx uu d hd hfact` (its type mentions `vRepD θG ψ U (toData …)`, definitionally `vRepF θG ψ U F`, and `vRepD_mem_levelM1 …`, proof-irrelevantly `vRepF_mem_levelM1 …` — `exact` accepts it, as in `hasUnitBand_of_atkinLehnerData`, `ConductorSlopes.lean`).
2. `exact rightIndex_sub_touchX_eq_ordDim idx hp2 hψ hshape hdet c₀ c₀' d₀ hAL (isThetaExact_classicalData idx hshape hdet c₀ d₀)` — H2 at the classical point is `isThetaExact_classicalData` (`ThetaExact.lean:391`).
3. The conclusion's `ordDim … ω₁` is `ordDim … (targetChar p ω k)` because `d₀ : TargetData c₀ (targetChar p ω k) _`.

- **Mathlib/project lemmas needed**: `rightIndex_sub_touchX_eq_ordDim`, `isThetaExact_classicalData`, `classicalData`, `targetData_classicalPoint`, `atkinLehnerHypothesis_of_atkinLehnerData`, `AtkinLehnerFamily.toData`, `norm_natCast_p`
- **Sources**: [LWX] Step III `lwx.txt:2048–2078`.
- **Generality decision**: As D9.
- **Size**: ~12 lines; source: 8 lines
- **Progress**: done 2026-09-11 — term-mode `rightIndex_sub_touchX_eq_ordDim`, H2 = `isThetaExact_classicalData idx hshape hdet c d`; compiled first time (build 3830 jobs, no warning), standard axioms.

### [D11] `degX_succ_of_atkinLehnerFamily`
- **Status**: done (2026-09-11 beastmode)
- **File**: PhD/LWX/DegreePeriodicity.lean (line 148)
- **Depends on**: none beyond the file
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- **[LWX, Thm 1.3]: `deg X_{k+1,ω} = r_ord(ω⁻¹ω₀^{2k}) + r_ord(ωω₀^{−2k−2})` at every weight**
(`lwx.txt:151–155`), granted the family of Atkin–Lehner data. -/
theorem degX_succ_of_atkinLehnerFamily [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    degX (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape) ω
        (k + 1)
      = ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (partnerChar p ω k)
        + ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (targetChar p ω k) := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `exact degX_succ_of_atkinLehnerData θG ψ U hU k ω hp2 hψ hζ (AtkinLehnerFamily.toData θG ψ U F ω k) hfin hv hvinj c hc hstab idx uu d hd hfact hshape hdet` — the hypotheses are stated for `vRepF`/`upEltF` and expected at `vRepD (toData …)`/`upEltD (toData …)`, which are the same terms (`vRepD_toData`, `upEltD_toData` are `rfl`); this is exactly how `hasUnitBand_of_atkinLehnerFamily` consumes `hasUnitBand_of_atkinLehnerData`.
2. (Alternative, the source's route: `rw [degX]`, then D9, D10 at `k` and the unit band at `k+1` (`hasUnitBand_of_atkinLehnerFamily … ω (k+1)`) with `leftIndex_mem`/`rightIndex_mem`, and `omega` — `n⁺ − n⁻ = (n⁺ − n) + (n − n⁻)`.)

- **Mathlib/project lemmas needed**: `degX_succ_of_atkinLehnerData`, `AtkinLehnerFamily.toData`, `vRepD_toData`, `upEltD_toData`
- **Sources**: [LWX] Thm 1.3 `lwx.txt:151–155`; Step III `lwx.txt:2079–2088`.
- **Generality decision**: Every `ω`, `k`; the datum `UpDatum.ofCerts … (vRepF …)` is the same for every weight.
- **Size**: 2 lines; source: 4 lines
- **Progress**: done 2026-09-11 — term `degX_succ_of_atkinLehnerData … (AtkinLehnerFamily.toData θG ψ U F ω k) …`; compiled first time (build 3830 jobs, no warning), standard axioms.

### [D12] `degXint_zero_of_atkinLehnerFamily`
- **Status**: done (2026-09-11 beastmode)
- **File**: PhD/LWX/DegreePeriodicity.lean (line 162)
- **Depends on**: none beyond the file
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- **[LWX, Thm 1.3]: `deg X_{(0,1),ω} = qt − r_ord(ω⁻¹) − r_ord(ω)`** (`lwx.txt:157–159` at
`n = 0`), granted the family of Atkin–Lehner data. -/
theorem degXint_zero_of_atkinLehnerFamily [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
        ω 0
      = p * Fintype.card ι
        - ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (partnerChar p ω 0)
        - ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) ω := by
  sorry
```

- **Depends on (declarations)**: —

**Proof sketch**:
1. `have hpK := norm_natCast_p ψ hψ`.  The classical data at the family's root: `c₀ := classicalData ψ ω θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) uu hp2 hψ hζ hpK 0`, `c₀' := classicalData ψ (partnerChar p ω k) … hζ.inv hpK 0`, `d₀ := targetData_classicalPoint ψ ω … hζ hpK 0`, `d₀' := targetData_classicalPoint ψ (partnerChar p ω k) … hζ.inv hpK 0`, and H1 `hAL := atkinLehnerHypothesis_of_atkinLehnerData θG ψ U hU 0 ω hp2 hψ hζ hpK (AtkinLehnerFamily.toData θG ψ U F ω 0) hfin hv hvinj c hc hstab idx uu d hd hfact` (its type mentions `vRepD θG ψ U (toData …)`, definitionally `vRepF θG ψ U F`, and `vRepD_mem_levelM1 …`, proof-irrelevantly `vRepF_mem_levelM1 …` — `exact` accepts it, as in `hasUnitBand_of_atkinLehnerData`, `ConductorSlopes.lean`).
2. `exact degXint_zero idx hp2 hψ hshape hdet c₀ c₀' d₀ d₀' hAL` with everything at `k = 0`; the conclusion's `ω'` is `partnerChar p ω 0`.

- **Mathlib/project lemmas needed**: `degXint_zero`, `classicalData`, `targetData_classicalPoint`, `atkinLehnerHypothesis_of_atkinLehnerData`, `AtkinLehnerFamily.toData`, `norm_natCast_p`
- **Sources**: [LWX] Thm 1.3 `lwx.txt:157–159` at `n = 0`; Step III `lwx.txt:2089–2097` at `k = 0` with `n⁻_0 = 0`, `n⁺_0 = r_ord(ω)` (`lwx.txt:1923–1927`, `2014–2022`).
- **Generality decision**: Every `ω`; `k = 0` only (the `k ≥ 1` intervals are D13).
- **Size**: ~12 lines; source: 3 lines
- **Progress**: done 2026-09-11 — term-mode `degXint_zero` at `k = 0`; compiled first time (build 3830 jobs, no warning), standard axioms.

### [CLEANUP-D4] Cleanup `PhD/LWX/DegreePeriodicity.lean`
- **Status**: done (2026-09-11 beastmode, inline)
- **File**: PhD/LWX/DegreePeriodicity.lean
- **Depends on**: D10, D11, D12
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.DegreePeriodicity` and `lake exe runLinter PhD.LWX.DegreePeriodicity` must be
clean (grep the linter's output for `DegreePeriodicity.lean`).  Done inline by the main agent.

- **Progress**: done 2026-09-11 — D1–D21 were written in one pass and compiled with no warning, so the per-file cleanup ran once over the whole file at CLEANUP-D-FINAL; nothing specific to these declarations (no unused hypothesis, no `simp` call, no `omit` needed, names as planned).

### [D13] `degXint_succ_of_atkinLehnerFamily`
- **Status**: done (2026-09-11 beastmode)
- **File**: PhD/LWX/DegreePeriodicity.lean (line 178)
- **Depends on**: D9, D10, CLEANUP-D4
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- **[LWX, Thm 1.3]: `deg X_{(k+1,k+2),ω} = qt − r_ord(ω⁻¹ω₀^{2k+2}) − r_ord(ωω₀^{−2k−2})`**
(`lwx.txt:2089–2097`: `n⁻_{k+2} − n⁺_{k+1} = (n_{k+2} − n_{k+1}) − (n_{k+2} − n⁻_{k+2})
− (n⁺_{k+1} − n_{k+1})`), granted the family of Atkin–Lehner data. -/
theorem degXint_succ_of_atkinLehnerFamily [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
        ω (k + 1)
      = p * Fintype.card ι
        - ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (partnerChar p ω (k + 1))
        - ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (targetChar p ω k) := by
  sorry
```

- **Depends on (declarations)**: D9, D10

**Proof sketch**:
1. `have hL := touchX_sub_leftIndex_eq_ordDim_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape hdet hp2 hψ hζ ω (k + 1)` — `touchX (k+1+1) − leftIndex (k+1+1) = ordDim (partnerChar p ω (k+1))`.
2. `have hR := rightIndex_sub_touchX_eq_ordDim_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape hdet hp2 hψ hζ ω k` — `rightIndex (k+1) − touchX (k+1) = ordDim (targetChar p ω k)`.
3. `have hb1 := hasUnitBand_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape hp2 hψ hζ ω (k + 1)`, `hb2 := … ω (k + 1 + 1)`.
4. `have hle1 := (leftIndex_mem _ ω hb2).2.1` (`leftIndex (k+2) ≤ touchX (k+2)`), `hle2 := (rightIndex_mem _ ω hb1).1` (`touchX (k+1) ≤ rightIndex (k+1)`), `hle3 := rightIndex_le_leftIndex_succ _ ω hb1 hb2` (`rightIndex (k+1) ≤ leftIndex (k+2)`) — the last is what makes `r + r' ≤ p·t` and the `ℕ`-subtraction exact.
5. `have htouch : touchX p (Fintype.card ι) (k + 1 + 1) = touchX p (Fintype.card ι) (k + 1) + p * Fintype.card ι := by rw [touchX, touchX]; ring` (keep `touchX …` folded everywhere else: `omega` atomises it).
6. `rw [degXint]` (or `show leftIndex _ ω (k + 1 + 1) - rightIndex _ ω (k + 1) = _`), `generalize p * Fintype.card ι = N at htouch ⊢`, `omega`.  Bookkeeping: `L₂ = X₂ − a` (`a ≤ X₂`), `R₁ = X₁ + b`, `X₂ = X₁ + N`, `R₁ ≤ L₂ ⟹ a + b ≤ N`, hence `L₂ − R₁ = N − a − b`.
7. If `omega` objects to the datum's spelling appearing in several syntactic forms, first `generalize hD : UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape = D at hL hR hb1 hb2 ⊢` (after obtaining hL hR hb1 hb2; never `set`).

- **Mathlib/project lemmas needed**: `hasUnitBand_of_atkinLehnerFamily`, `leftIndex_mem`, `rightIndex_mem`, `rightIndex_le_leftIndex_succ`, `touchX`, `degXint`, `omega`
- **Sources**: [LWX] Thm 1.3 `lwx.txt:157–159` at `n = k+1`; Step III `lwx.txt:2089–2097`.
- **Generality decision**: Every `ω`, `k` (intervals `(n, n+1)` with `n ≥ 1`); `hdet` through D9/D10.
- **Size**: ~18 lines; source: 4 lines (`lwx.txt:2089–2097`)
- **Progress**: done 2026-09-11 — D9 at `k+1`, D10 at `k`, the two unit bands, `rightIndex_le_leftIndex_succ`, `touchX (k+2) = touchX (k+1) + p·t` by `ring`; `generalize p * Fintype.card ι = N` then `omega`; compiled first time (build 3830 jobs, no warning), standard axioms.

### [D14] `degXint_of_atkinLehnerFamily`
- **Status**: done (2026-09-11 beastmode)
- **File**: PhD/LWX/DegreePeriodicity.lean (line 193)
- **Depends on**: D3, D4, D12, D13
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- **[LWX, Thm 1.3]: `deg X_{(n,n+1),ω} = qt − r_ord(ω⁻¹ω₀^{2n}) − r_ord(ωω₀^{−2n})` for every
`n ≥ 0`** (`lwx.txt:157–159`), granted the family of Atkin–Lehner data. -/
theorem degXint_of_atkinLehnerFamily [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
    degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
        ω n
      = p * Fintype.card ι
        - ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (partnerChar p ω n)
        - ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (ω * (teichChar p ^ (2 * n))⁻¹) := by
  sorry
```

- **Depends on (declarations)**: D3, D4, D12, D13

**Proof sketch**:
1. `rcases n with _ | k`.
2. `· rw [degXint_zero_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape hdet hp2 hψ hζ ω, mul_inv_teichChar_pow_zero]` — after the first rewrite both sides are `p * card ι − ordDim … (partnerChar p ω 0) − ordDim … (?)` with `?` = `ω` on the left and `ω * (teichChar p ^ (2 * 0))⁻¹` on the right; D3 rewrites the latter.
3. `· rw [degXint_succ_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape hdet hp2 hψ hζ ω k, targetChar_eq_mul_inv_teichChar_pow]` — D4 turns `targetChar p ω k` into `ω * (teichChar p ^ (2 * (k + 1)))⁻¹`.

- **Mathlib/project lemmas needed**: `mul_inv_teichChar_pow_zero`, `targetChar_eq_mul_inv_teichChar_pow`
- **Sources**: [LWX] Thm 1.3 `lwx.txt:157–159`.
- **Generality decision**: Every `ω`, `n ≥ 0` — the source's uniform statement, with the source's characters spelled `partnerChar p ω n = ω⁻¹ω₀^{2n}` and `ω * (teichChar p ^ (2 * n))⁻¹ = ωω₀^{−2n}`.
- **Size**: ~6 lines; source: 3 lines
- **Progress**: done 2026-09-11 — `cases n`; D12 + D3 / D13 + D4; compiled first time (build 3830 jobs, no warning), standard axioms.

### [CLEANUP-ALL-1] `/cleanup-all` before the milestone D15
- **Status**: done (2026-09-11 beastmode, inline)
- **File**: PhD/LWX/DegreePeriodicity.lean
- **Depends on**: every ticket before D15 (D1–D14, CLEANUP-D1–D4)
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup-all` over the board's file before the milestone D15: naming consistency with
`ConductorSlopes.lean`/`AtkinLehnerFamily.lean`, dead helpers, docstrings, `lake exe runLinter
PhD.LWX.DegreePeriodicity`; `lake build PhD` green.

- **Progress**: done 2026-09-11 — naming matches `ConductorSlopes.lean`/`AtkinLehnerFamily.lean` (`_of_atkinLehnerFamily`, `mul_teichChar_sq`, `_add_period`); no dead helper; `#lint in PhD.LWX.DegreePeriodicity` 0 findings; `lake build PhD` green (3921 jobs).

### [D15] `degXint_pos_of_atkinLehnerFamily` **[MILESTONE]**
- **Status**: done (2026-09-11 beastmode)
- **File**: PhD/LWX/DegreePeriodicity.lean (line 208)
- **Depends on**: D8, D14, CLEANUP-ALL-1
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- **[LWX, Thm 1.3]: `deg X_{(n,n+1),ω} > 0` for all `n ≥ 0`** (`lwx.txt:160`): `qt − r − r' ≥
qt − 2t > 0` since `r_ord ≤ t` and `p ≥ 3`. -/
theorem degXint_pos_of_atkinLehnerFamily [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
    0 < degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
      hshape) ω n := by
  sorry
```

- **Depends on (declarations)**: D8, D14

**Proof sketch**:
1. `rw [degXint_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape hdet hp2 hψ hζ ω n]`.
2. `have ha := ordDim_le_card (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape) (partnerChar p ω n)`, `hb := ordDim_le_card (…) (ω * (teichChar p ^ (2 * n))⁻¹)`.
3. `have h3 : 3 ≤ p := by have := hp.out.two_le; omega` (uses `hp2 : p ≠ 2`).
4. `have ht : 0 < Fintype.card ι := Fintype.card_pos`; `have h3t : 3 * Fintype.card ι ≤ p * Fintype.card ι := Nat.mul_le_mul_right _ h3`.
5. `generalize p * Fintype.card ι = N at h3t ⊢`; `omega` (`a + b ≤ 2t < 3t ≤ N`).

- **Mathlib/project lemmas needed**: `ordDim_le_card`, `Nat.Prime.two_le`, `Fintype.card_pos`, `Nat.mul_le_mul_right`, `omega`
- **Sources**: [LWX] Thm 1.3 `lwx.txt:160` ("In particular, we have deg X_{(n,n+1),ω} > 0 for all n ≥ 0"); `lwx.txt:123–127` for `r_ord ≤ t`.
- **Generality decision**: Every `ω`, `n`; needs `p ≠ 2` (`q = p ≥ 3`; the source's `p = 2` case has `q = 4`, out of scope), `Nonempty ι` (`t ≥ 1`).
- **Size**: ~8 lines; source: 1 line
- **Progress**: done 2026-09-11 — D14, D8 twice, `3·t ≤ p·t` from `p ≠ 2`, `Fintype.card_pos`, `generalize` + `omega`; compiled first time (build 3830 jobs, no warning), standard axioms.

### [CLEANUP-D5] Cleanup `PhD/LWX/DegreePeriodicity.lean`
- **Status**: done (2026-09-11 beastmode, inline)
- **File**: PhD/LWX/DegreePeriodicity.lean
- **Depends on**: D13, D14, D15
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.DegreePeriodicity` and `lake exe runLinter PhD.LWX.DegreePeriodicity` must be
clean (grep the linter's output for `DegreePeriodicity.lean`).  Done inline by the main agent.

- **Progress**: done 2026-09-11 — D1–D21 were written in one pass and compiled with no warning, so the per-file cleanup ran once over the whole file at CLEANUP-D-FINAL; nothing specific to these declarations (no unused hypothesis, no `simp` call, no `omit` needed, names as planned).

### [D16] `degX_succ_mul_teichChar_sq`
- **Status**: done (2026-09-11 beastmode)
- **File**: PhD/LWX/DegreePeriodicity.lean (line 219)
- **Depends on**: D5, D6, D11, CLEANUP-D5
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- **[LWX, Cor 1.4] at the integers** (`lwx.txt:164–166`): `deg X_{k+1,ω} = deg X_{k+2,ωω₀²}`. -/
theorem degX_succ_mul_teichChar_sq [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    degX (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape) ω
        (k + 1)
      = degX (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
          (ω * teichChar p ^ 2) (k + 2) := by
  sorry
```

- **Depends on (declarations)**: D5, D6, D11

**Proof sketch**:
1. `rw [degX_succ_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape hdet hp2 hψ hζ ω k, show k + 2 = k + 1 + 1 from rfl, degX_succ_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape hdet hp2 hψ hζ (ω * teichChar p ^ 2) (k + 1), partnerChar_mul_teichChar_sq_succ, targetChar_mul_teichChar_sq_succ]` — closes by `rfl` after the two character rewrites.

- **Mathlib/project lemmas needed**: `degX_succ_of_atkinLehnerFamily`, `partnerChar_mul_teichChar_sq_succ`, `targetChar_mul_teichChar_sq_succ`
- **Sources**: [LWX] Cor 1.4 `lwx.txt:164–166`, integer case.
- **Generality decision**: `n = k + 1 ≥ 1` (the source's list `1, 2, …`; false at `n = 0` in general).
- **Size**: ~3 lines; source: 2 lines
- **Progress**: done 2026-09-11 — `rw` D11 twice (`k + 2 = k + 1 + 1` by `rfl`), D5, D6; compiled first time (build 3830 jobs, no warning), standard axioms.

### [D17] `degXint_mul_teichChar_sq`
- **Status**: done (2026-09-11 beastmode)
- **File**: PhD/LWX/DegreePeriodicity.lean (line 231)
- **Depends on**: D5, D7, D14
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- **[LWX, Cor 1.4] on the open intervals** (`lwx.txt:164–166`):
`deg X_{(n,n+1),ω} = deg X_{(n+1,n+2),ωω₀²}`. -/
theorem degXint_mul_teichChar_sq [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
    degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
        ω n
      = degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (ω * teichChar p ^ 2) (n + 1) := by
  sorry
```

- **Depends on (declarations)**: D5, D7, D14

**Proof sketch**:
1. `rw [degXint_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape hdet hp2 hψ hζ ω n, degXint_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape hdet hp2 hψ hζ (ω * teichChar p ^ 2) (n + 1), partnerChar_mul_teichChar_sq_succ, mul_teichChar_sq_mul_inv_teichChar_pow_succ]`.

- **Mathlib/project lemmas needed**: `degXint_of_atkinLehnerFamily`, `partnerChar_mul_teichChar_sq_succ`, `mul_teichChar_sq_mul_inv_teichChar_pow_succ`
- **Sources**: [LWX] Cor 1.4 `lwx.txt:164–166`, open-interval case.
- **Generality decision**: Every `n ≥ 0` (the source's list starts at `(0,1)`).
- **Size**: ~3 lines; source: 2 lines
- **Progress**: done 2026-09-11 — `rw` D14 twice, D5, D7; compiled first time (build 3830 jobs, no warning), standard axioms.

### [D18] `degX_succ_mul_teichChar_pow`
- **Status**: done (2026-09-11 beastmode)
- **File**: PhD/LWX/DegreePeriodicity.lean (line 242)
- **Depends on**: D1, D2, D16
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- [LWX, Cor 1.4] at the integers, iterated `m` times: `deg X_{k+1,ω} = deg X_{k+1+m,ωω₀^{2m}}`. -/
theorem degX_succ_mul_teichChar_pow [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (m k : ℕ) :
    degX (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape) ω
        (k + 1)
      = degX (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
          (ω * teichChar p ^ (2 * m)) (k + 1 + m) := by
  sorry
```

- **Depends on (declarations)**: D1, D2, D16

**Proof sketch**:
1. `induction m with` (no `generalizing` needed; `k` fixed).
2. `| zero => rw [mul_teichChar_pow_zero]` — the goal `degX … ω (k + 1) = degX … ω (k + 1 + 0)` closes by `rfl` (`k + 1 + 0` reduces to `k + 1`).
3. `| succ m ih => rw [ih, mul_teichChar_pow_succ, show k + 1 + m = k + m + 1 by omega, show k + 1 + (m + 1) = k + m + 2 by omega]; exact degX_succ_mul_teichChar_sq θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape hdet hp2 hψ hζ (ω * teichChar p ^ (2 * m)) (k + m)` — D16 at the shifted disc and index `k + m` reads `degX … (ωω₀^{2m}) (k + m + 1) = degX … (ωω₀^{2m}·ω₀²) (k + m + 2)`.

- **Mathlib/project lemmas needed**: `mul_teichChar_pow_zero`, `mul_teichChar_pow_succ`, `degX_succ_mul_teichChar_sq`, `omega`
- **Sources**: [LWX] Cor 1.4 `lwx.txt:168–169` ("periodic modulo ϕ(q)/2": the `m`-fold iterate).
- **Generality decision**: Every `m`, `k`; template: `slopeRatio_mul_teichChar_pow` (`ConductorSlopes.lean`).
- **Size**: ~8 lines; source: 1 line
- **Progress**: done 2026-09-11 — induction on `m`; D1 / D2 + D16 at `(ωω₀^{2m}, k+m)`; compiled first time (build 3830 jobs, no warning), standard axioms.

### [CLEANUP-D6] Cleanup `PhD/LWX/DegreePeriodicity.lean`
- **Status**: done (2026-09-11 beastmode, inline)
- **File**: PhD/LWX/DegreePeriodicity.lean
- **Depends on**: D16, D17, D18
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.DegreePeriodicity` and `lake exe runLinter PhD.LWX.DegreePeriodicity` must be
clean (grep the linter's output for `DegreePeriodicity.lean`).  Done inline by the main agent.

- **Progress**: done 2026-09-11 — D1–D21 were written in one pass and compiled with no warning, so the per-file cleanup ran once over the whole file at CLEANUP-D-FINAL; nothing specific to these declarations (no unused hypothesis, no `simp` call, no `omit` needed, names as planned).

### [D19] `degXint_mul_teichChar_pow`
- **Status**: done (2026-09-11 beastmode)
- **File**: PhD/LWX/DegreePeriodicity.lean (line 254)
- **Depends on**: D1, D2, D17, CLEANUP-D6
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- [LWX, Cor 1.4] on the open intervals, iterated `m` times:
`deg X_{(n,n+1),ω} = deg X_{(n+m,n+m+1),ωω₀^{2m}}`. -/
theorem degXint_mul_teichChar_pow [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (m n : ℕ) :
    degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
        ω n
      = degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (ω * teichChar p ^ (2 * m)) (n + m) := by
  sorry
```

- **Depends on (declarations)**: D1, D2, D17

**Proof sketch**:
1. `induction m with`.
2. `| zero => rw [mul_teichChar_pow_zero]` (`n + 0` reduces to `n`, `rfl`).
3. `| succ m ih => rw [ih, mul_teichChar_pow_succ, show n + (m + 1) = n + m + 1 by omega]; exact degXint_mul_teichChar_sq θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape hdet hp2 hψ hζ (ω * teichChar p ^ (2 * m)) (n + m)`.

- **Mathlib/project lemmas needed**: `mul_teichChar_pow_zero`, `mul_teichChar_pow_succ`, `degXint_mul_teichChar_sq`, `omega`
- **Sources**: [LWX] Cor 1.4 `lwx.txt:168–169`.
- **Generality decision**: Every `m`, `n`.
- **Size**: ~6 lines; source: 1 line
- **Progress**: done 2026-09-11 — induction on `m`; D1 / D2 + D17 at `(ωω₀^{2m}, n+m)`; compiled first time (build 3830 jobs, no warning), standard axioms.

### [CLEANUP-ALL-2] `/cleanup-all` before the milestone D20/D21
- **Status**: done (2026-09-11 beastmode, inline)
- **File**: PhD/LWX/DegreePeriodicity.lean
- **Depends on**: every ticket before D20 (D1–D19 and the cleanups)
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup-all` over the board's file before the milestone D20/D21: naming consistency with
`ConductorSlopes.lean`/`AtkinLehnerFamily.lean`, dead helpers, docstrings, `lake exe runLinter
PhD.LWX.DegreePeriodicity`; `lake build PhD` green.

- **Progress**: done 2026-09-11 — as CLEANUP-ALL-1 (run once, after D21); D22 added to deduplicate D20/D21; `lake build PhD` green (3921 jobs).

### [D20] `degX_succ_add_period`
- **Status**: done (2026-09-11 beastmode)
- **File**: PhD/LWX/DegreePeriodicity.lean (line 266)
- **Depends on**: D18, CLEANUP-ALL-2
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- **[LWX, Cor 1.4]: `deg X_{n,ω}` is periodic modulo `ϕ(q)/2 = (p−1)/2` in `n ≥ 1`**
(`lwx.txt:168–169`): `deg X_{k+1+(p−1)/2,ω} = deg X_{k+1,ω}` ("since `ω₀^{ϕ(q)} = 1`"). -/
theorem degX_succ_add_period [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    degX (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape) ω
        (k + 1 + (p - 1) / 2)
      = degX (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
          ω (k + 1) := by
  sorry
```

- **Depends on (declarations)**: D18 (and `teichChar_pow_sub_one`)

**Proof sketch**:
1. `have h2 : 2 * ((p - 1) / 2) = p - 1 := by obtain ⟨r, hr⟩ := hp.out.odd_of_ne_two hp2; omega`.
2. `have hω : ω * teichChar p ^ (2 * ((p - 1) / 2)) = ω := by rw [h2, teichChar_pow_sub_one]; exact MonoidHom.ext fun r => by rw [MonoidHom.mul_apply, MonoidHom.one_apply, mul_one]` — verbatim from `slopeRatio_add_period` (`ConductorSlopes.lean`).
3. `have h := degX_succ_mul_teichChar_pow θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape hdet hp2 hψ hζ ω ((p - 1) / 2) k`; `rw [hω] at h`; `exact h.symm`.

- **Mathlib/project lemmas needed**: `Nat.Prime.odd_of_ne_two`, `teichChar_pow_sub_one`, `degX_succ_mul_teichChar_pow`, `MonoidHom.ext`, `MonoidHom.mul_apply`, `MonoidHom.one_apply`, `mul_one`, `omega`
- **Sources**: [LWX] Cor 1.4 `lwx.txt:168–169` ("periodic modulo ϕ(q)/2"); `lwx.txt:2357–2358` ("since ω₀^{ϕ(q)} = 1").
- **Generality decision**: `p ≠ 2` (period `(p−1)/2 = ϕ(q)/2`; the source's `p = 2` has `ϕ(4)/2 = 1`, out of scope).
- **Size**: ~7 lines; source: 1 line
- **Progress**: done 2026-09-11 — `rw` D18 at `m = (p−1)/2` and the helper `mul_teichChar_pow_two_mul_sub_one_div_two` (added at cleanup: `2·((p−1)/2) = p−1` from `Nat.Prime.odd_of_ne_two`, then `teichChar_pow_sub_one`); compiled first time (build 3830 jobs, no warning), standard axioms.

### [D21] `degXint_add_period` **[MILESTONE]**
- **Status**: done (2026-09-11 beastmode)
- **File**: PhD/LWX/DegreePeriodicity.lean (line 278)
- **Depends on**: D19, CLEANUP-ALL-2
- **Parallel**: yes (within the dependency order)
- **Type**: proof

**Statement** (verbatim from the skeleton; protected):
```lean
include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- **[LWX, Cor 1.4]: `deg X_{(n,n+1),ω}` is periodic modulo `ϕ(q)/2 = (p−1)/2` in `n ≥ 0`**
(`lwx.txt:168–169`): `deg X_{(n+(p−1)/2, n+(p−1)/2+1),ω} = deg X_{(n,n+1),ω}`. -/
theorem degXint_add_period [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
    degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
        ω (n + (p - 1) / 2)
      = degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) ω n := by
  sorry
```

- **Depends on (declarations)**: D19 (and `teichChar_pow_sub_one`)

**Proof sketch**:
1. As D20 with D19: `h2`, `hω` verbatim; `have h := degXint_mul_teichChar_pow θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape hdet hp2 hψ hζ ω ((p - 1) / 2) n`; `rw [hω] at h`; `exact h.symm`.

- **Mathlib/project lemmas needed**: `Nat.Prime.odd_of_ne_two`, `teichChar_pow_sub_one`, `degXint_mul_teichChar_pow`, `MonoidHom.ext`, `MonoidHom.mul_apply`, `MonoidHom.one_apply`, `mul_one`, `omega`
- **Sources**: [LWX] Cor 1.4 `lwx.txt:168–169`; `lwx.txt:2357–2358`.
- **Generality decision**: `p ≠ 2`; every `n ≥ 0`.  **Milestone M2** (with D20): [LWX, Cor 1.4] at the coefficient level, granted the family.
- **Size**: ~7 lines; source: 1 line
- **Progress**: done 2026-09-11 — `rw` D19 at `m = (p−1)/2` and the same helper; compiled first time (build 3830 jobs, no warning), standard axioms.

### [D22] `mul_teichChar_pow_two_mul_sub_one_div_two` **[NEW DECL]**
- **Status**: done (2026-09-11 beastmode, spawned at CLEANUP-D-FINAL)
- **File**: PhD/LWX/DegreePeriodicity.lean
- **Depends on**: — (uses `teichChar_pow_sub_one`, `Nat.Prime.odd_of_ne_two`)
- **Parallel**: yes
- **Type**: proof/def

**Statement**:
```lean
theorem mul_teichChar_pow_two_mul_sub_one_div_two (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    ω * teichChar p ^ (2 * ((p - 1) / 2)) = ω
```
**Source**: [LWX, Cor 1.4], `lwx.txt:168–169` ("since `ω₀^{ϕ(q)} = 1`").  **Why a helper**: D20 and
D21 each proved it inline (`h2`, `hω`); deduplicated at cleanup.  **Proof**: `p = 2m+1`
(`Nat.Prime.odd_of_ne_two`), `2·((p−1)/2) = p−1` by `omega`, `teichChar_pow_sub_one`, then
`ω * 1 = ω` pointwise.

- **Progress**: done 2026-09-11 — as described; standard axioms.

### [CLEANUP-D-FINAL] Cleanup `PhD/LWX/DegreePeriodicity.lean` (final)
- **Status**: done (2026-09-11 beastmode, inline)
- **File**: PhD/LWX/DegreePeriodicity.lean
- **Depends on**: D19, D20, D21 (and every earlier ticket of the file)
- **Parallel**: no
- **Type**: cleanup

Run `/cleanup` on the declarations proved since the last cleanup of this file: golf, remove unused
hypotheses (record `_hx` slack in the ticket instead of editing protected statements), unused
`simp` args, `omit … in` for unused section variables (before the docstring), naming, docstrings;
`lake build PhD.LWX.DegreePeriodicity` and `lake exe runLinter PhD.LWX.DegreePeriodicity` must be
clean (grep the linter's output for `DegreePeriodicity.lean`).  Done inline by the main agent.

- **Progress**: done 2026-09-11 — D22 spawned (dedup of D20/D21), D4 and D8–D12 in term mode, `rw`-list indentation normalised, all lines ≤ 100 columns, header SKELETON marker removed; `lake build PhD.LWX.DegreePeriodicity` clean (3830 jobs), `#lint in PhD.LWX.DegreePeriodicity` 0 findings, `runLinter` no finding in the file.

### [CLEANUP-FINAL] `/cleanup-all`, the records, and the hand-off
- **Status**: done (2026-09-11 beastmode, inline)
- **File**: `PhD/LWX/DegreePeriodicity.lean`; `PhD.lean`; `.mathlib-quality/lwx-stepone/FINDINGS.md`
- **Depends on**: every other ticket
- **Parallel**: no
- **Type**: cleanup

Final `/cleanup-all` (linter-clean; `#print axioms` on D15, D20, D21 = `[propext, Classical.choice,
Quot.sound]`), then: (1) change the `PhD.lean` comment of the `lwx-degrees` import to "complete,
sorry-free"; (2) in `.mathlib-quality/lwx-stepone/FINDINGS.md` update ledger row 2 ("[LWX, Thm 1.3]'s
degree formulas") to "proved at the coefficient level at every classical weight, granted the
family (`degX_succ_of_atkinLehnerFamily`, `degXint_of_atkinLehnerFamily`,
`degXint_pos_of_atkinLehnerFamily`), and [LWX, Cor 1.4] (`degX_succ_add_period`,
`degXint_add_period`)"; (3) record in this board's Summary which sentences of
`blueprint/src/chapter/LWXSlopes.tex` are now stale (§"What Theorem 1.5 says": "Corollary 1.4 …
likewise not formalised"; §"Degrees": "not formalised") — do **not** edit the blueprint without the
user's go-ahead; (4) record slack hypotheses found (`_hx`) and the option of moving D1–D8 to their
natural homes (`AtkinLehnerFamily.lean`, `TargetPoint.lean`, `Degrees.lean`) for the user to decide.

- **Progress**: done 2026-09-11 — `#print axioms` standard for D15, D20, D21 (and D11, D16, D17, D22); (1) `PhD.lean` comment now "complete, sorry-free"; (2) FINDINGS ledger row 2 closed at the coefficient level (all eight declarations cited); (3) stale blueprint sentences `LWXSlopes.tex:354–362, 372–374, 376–385` recorded in the Summary's execution record, blueprint not edited; (4) no `_hx` slack; the move-to-natural-homes option recorded in the Summary.  Also: JL-AUDIT addendum, plan STATUS → EXECUTED, memory updated.
