# Ticket board: Tau Ceti `PadicFunctionalAnalysis`, Layer 1 (bounded linear maps)

**Board**: `.mathlib-quality/tauceti-pfa-layer1/` (a *named* board: always pass this path to `/beastmode`;
the default board belongs to another project, and the other `tauceti-*` boards are parallel boards).
**Plan**: `plan.md` · **Decomposition (quotes, attacks, gate)**: `decomposition.md` · **References**: `references/*`
**Roadmap**: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, Layer 1 (§1.1–§1.4) — cited as [RM].
**Code**: `PhD/TauCeti/Code/PadicFunctionalAnalysis/Operator/` — eight files, every declaration already stated with
`sorry`. Planned 2026-10-06. Status: **COMPLETE 2026-10-06** — all 47 tickets done; the eight Operator files are sorry-free, lint clean, standard axioms, and in the chain root.

## Summary

| | Count |
|---|---|
| Proof / definition / integration tickets | 31 (`T001`–`T031`) |
| Per-file cleanups | 13 (`CLEANUP-1`–`CLEANUP-13`) |
| Pre-milestone sweeps | 2 (`CLEANUP-ALL-1`, `CLEANUP-ALL-2`) |
| Final sweep | 1 (`CLEANUP-FINAL`) |
| **Total** | **47** |

- **Milestone M1** = `T012`: the quantitative open mapping theorem over a Tate normed ring
  (`ContinuousLinearMap.Ultra.exists_preimage_norm_le`, `isOpenMap`) — [RM] §1.2.1.
- **Milestone M2** = `T023`: every submodule of a finitely generated Banach module over a Noetherian Banach–Tate
  ring is closed (`Submodule.isClosed_of_isNoetherianRing`) — [RM] §1.4.2.
- The agreement with Mathlib (§1.1.6) is `T010`; the layer's two counterexamples are `T028` and `T029`–`T030`.
- Skeleton: 99 declaration headers, 75 `sorry`s. Gate (verified 2026-10-06, 2 254 jobs, 0 errors):
  `lake build PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.Examples`.
- Tickets that can start immediately (no dependencies): `T001`, `T002`, `T021`.

## Worker protocol (binding)

1. **The statements are fixed.** Every ticket's Statement block is copied verbatim from the skeleton by
   `scratch/gen/gen_tickets.py`. Prove the statement as written. If a statement is false or unprovable as stated,
   that is a **B2 stop** with a concrete counterexample or obstruction — never silently change a hypothesis.
   Private helper lemmas are allowed and expected where a sketch says so; they follow the same conventions.
2. **Chain separation.** Never `import PhD.Main.*` here (CI-gated), and never the reverse. `PhD/Main/` files cited
   as [SRC] and the in-chain [RAG] file are read-only references for proof ideas. Never delete `PhD/PR'd/` or
   legacy files.
3. **Build** with `lake build PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.<Module>` — never `lake build PhD`.
   There is no `timeout` binary on this machine: use the tool timeout and check exit codes. Run one Lean process
   at a time (parallel builds swap-thrash).
4. **Imports stay minimal per file** (never `import Mathlib` in a `Code/` file). When a proof needs an unimported
   module, add exactly that module.
5. **The scope.** Everything lives in `namespace ContinuousLinearMap.Ultra`; outside it, `open scoped
   ContinuousLinearMap.Ultra` activates the operator norm. An unqualified `le_opNorm`, `opNorm_le_bound`, … inside
   the namespace is overloaded with Mathlib's field version — write `Ultra.le_opNorm` when the elaborator
   complains. Never open the scope for field scalars (`T010`, `T027` use Mathlib's instances on purpose).
6. **Done means**: the module builds with no `sorry` in the ticket's declarations, `#print axioms` on each shows
   only `propext`, `Classical.choice`, `Quot.sound`, and the ticket's Status line is updated here.
7. **Cleanup tickets are done inline by the main agent** (no Agent-dispatched cleanup workers), with
   `lake exe runLinter` on the module.
8. **Sentinel ownership.** `.mathlib-quality/beastmode_active` may belong to a parallel instance: `cat` it before
   acting, and delete it only if its `BOARD:` line names this board.
9. **Mathlib first.** Every Mathlib name in a "Mathlib lemmas needed" block was checked by elaboration against
   the pinned Mathlib (`scratch/names*.lean`, three files, about 250 names), except where a sketch says
   "if … is not found" and gives the fallback. `T0xx` refers to an earlier ticket of this board; "Layer 0" names
   are in `PhD/TauCeti/Code/PadicFunctionalAnalysis/*.lean`.
10. **Conventions** (plan §"Generality and design decisions"): Mathlib's formula verbatim; weakest hypotheses
    (no `CompleteSpace R`, no ultrametricity in §1.2 proper; commutative `R` only where Mathlib's instances force
    it); explicit `ϖ` when a constant mentions `‖ϖ‖`, `[IsTate R]` otherwise; one conclusion per declaration;
    one-line `Source:` docstrings; readable arithmetic (`ring` identity + `mul_le_mul` + `linarith` over `nlinarith`).
11. **Commit or push only when the user asks.**

## Roadmap errata (found while planning; see `plan.md` for the full table)

E9 `‖u‖` is the supremum of the ratios, not of `‖u x‖` over the unit ball · E10 multiplication by `a` has norm
exactly `‖a‖` once `‖1‖ = 1` · E11 equality in `‖a • u‖ ≤ ‖a‖‖u‖` needs a multiplicative *unit* · E12 the OMT is
proved by Baire, not from Henkel's theorem (seam S1) · E13 §1.3's orthogonal bases are deferred to Layer 2 ·
E14 §1.4.1's adic-spaces citations and §1.4.2's matrix lemma are replaced by Buzzard 2.2 and Nakayama (seams
S2, S3) · E15 the `C₀` examples move to Layer 2 · E16 §1.2 needs neither `CompleteSpace R` nor ultrametricity ·
E17 §1.2.5 needs an ultrametric target · E18 the §1.4.3 counterexample is `ℓ^∞(ℕ, ℚ_p)`. E9 and E10 are corrected
in the roadmap README (2026-10-06, uncommitted).

## Dependency order

```text
G1  Norm            T001 ∥ T002 → T003 → CLEANUP-1 → T004 → CLEANUP-2
G2  Banach          CLEANUP-2 → T005 → T006 → T007 → CLEANUP-3 → T008 → T009 → T010 → CLEANUP-4
G3  OpenMapping     CLEANUP-2 → T011 → CLEANUP-ALL-1 (needs CLEANUP-4) → T012 (M1) → T013 → CLEANUP-5 → T014 → CLEANUP-6
G4  ClosedGraph     CLEANUP-6 → T015 → CLEANUP-7
G5  BanachSteinhaus CLEANUP-2 → T016 → T017 → CLEANUP-8
G6  Pi              CLEANUP-2 → T018 → T019 → CLEANUP-9
G7  Finite          {CLEANUP-6, CLEANUP-9} → T020 ; T021 (free) ; T020 → T022 → CLEANUP-10 → CLEANUP-ALL-2 → T023 (M2) → T024 → CLEANUP-11
G8  Examples        {CLEANUP-11, CLEANUP-4, CLEANUP-7, CLEANUP-8} → T025 → T026 → T027 → CLEANUP-12 → T028 → T029 → T030 → CLEANUP-13
Root                CLEANUP-13 → T031 → CLEANUP-FINAL
```

## Tickets

### [T001] Order-theoretic lemmas of the operator norm
- **Status**: done (2026-10-06) · **File**: `Norm.lean` · **Depends on**: none · **Parallel**: yes (no dependencies) · **Type**: lemmas
- **Progress**: 2026-10-06 DONE — all seven proved term-mode or short tactic; neg_apply is the root lemma (ContinuousLinearMap.neg_apply deprecated); axioms standard
- **Leaves**: L1.1–L1.7

#### Statement
```lean
theorem bounds_bddBelow {u : M →L[R] N} : BddBelow {c : ℝ | 0 ≤ c ∧ ∀ x, ‖u x‖ ≤ c * ‖x‖} := by
  sorry

theorem opNorm_nonneg (u : M →L[R] N) : 0 ≤ ‖u‖ := by
  sorry

theorem opNorm_le_bound (u : M →L[R] N) {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, ‖u x‖ ≤ C * ‖x‖) :
    ‖u‖ ≤ C := by
  sorry

@[simp]
theorem opNorm_zero : ‖(0 : M →L[R] N)‖ = 0 := by
  sorry

theorem le_opNorm_of_bound (u : M →L[R] N) (h : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖) (x : M) :
    ‖u x‖ ≤ ‖u‖ * ‖x‖ := by
  sorry

theorem norm_id_le : ‖ContinuousLinearMap.id R M‖ ≤ 1 := by
  sorry

@[simp]
theorem opNorm_neg (u : M →L[R] N) : ‖-u‖ = ‖u‖ := by
  sorry
```
#### Proof sketch
1. `bounds_bddBelow`: the bound set is bounded below by `0`: `⟨0, fun _ hc ↦ hc.1⟩`.
2. `opNorm_nonneg`: `Real.sInf_nonneg fun _ hc ↦ hc.1` (with `sInf ∅ = 0` no boundedness is needed).
3. `opNorm_le_bound`: `csInf_le bounds_bddBelow ⟨hC, h⟩`.
4. `opNorm_zero`: `le_antisymm (opNorm_le_bound _ le_rfl fun x ↦ by simp) (opNorm_nonneg _)`.
5. `le_opNorm_of_bound`: `obtain ⟨C, hC⟩ := h`. Case `‖x‖ = 0` (seminormed `M`!): `hC x` gives `‖u x‖ ≤ 0`, so both
   sides are `0` (`norm_nonneg`, `mul_zero`). Case `‖x‖ ≠ 0`: `‖u x‖ / ‖x‖` is a lower bound of the bound set
   (`div_le_iff₀ (lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx))` on `hc.2 x`), and the set is nonempty (`max C 0`
   is in it: `le_max_right`, and `hC x` with `mul_le_mul_of_nonneg_right (le_max_left _ _)`), so
   `le_csInf ⟨_, _⟩ _ : ‖u x‖ / ‖x‖ ≤ ‖u‖`; finish with `div_mul_cancel₀`.
6. `norm_id_le`: `opNorm_le_bound _ zero_le_one fun x ↦ by simp` (`id_apply`, `one_mul`).
7. `opNorm_neg`: `simp only [norm_def, ContinuousLinearMap.neg_apply, norm_neg]`.

#### Mathlib lemmas needed
`Real.sInf_nonneg`, `csInf_le`, `le_csInf`, `div_le_iff₀`, `div_mul_cancel₀`, `norm_nonneg`, `le_max_left`, `le_max_right`, `mul_le_mul_of_nonneg_right`, `ContinuousLinearMap.id_apply`, `ContinuousLinearMap.neg_apply`, `norm_neg`.
#### Sources
[Mathlib] `ContinuousLinearMap.{bounds_bddBelow, opNorm_nonneg, opNorm_le_bound, opNorm_zero, norm_id_le, opNorm_neg}` in `Mathlib/Analysis/Normed/Operator/Basic.lean:173–235` (their proofs transport verbatim); [RM] §1.1.1.
#### Generality decision
Semiring scalars and seminormed modules — the formula needs nothing else (decision 3); `opNorm_neg` in a `Ring` section because `-u` needs it. `le_opNorm_of_bound` is stated with an existential bound so that it applies before any Tate hypothesis.

### [T002] The scaling trick for linear maps
- **Status**: done (2026-10-06) · **File**: `Norm.lean` · **Depends on**: none · **Parallel**: yes (parallel with T001) · **Type**: lemma
- **Progress**: 2026-10-06 DONE — shell lemma + explicit div identity (div_mul_div_comm, mul_div_mul_left); axioms standard
- **Leaves**: L1.8

#### Statement
```lean
theorem norm_map_le_div_mul_of_forall_norm_le (ϖ : PseudoUniformizer R) (f : M →ₗ[R] N)
    {ε C : ℝ} (hε : 0 < ε) (h : ∀ x, ‖x‖ ≤ ε → ‖f x‖ ≤ C) (x : M) :
    ‖f x‖ ≤ C / (ε * ‖(ϖ : R)‖) * ‖x‖ := by
  sorry
```
#### Proof sketch
1. `0 ≤ C`: from `h 0 (by simp [hε.le])` after `map_zero, norm_zero`.
2. Case `x = 0`: `simp` (both sides `0` after `map_zero`; the RHS is `_ * 0`).
3. Case `x ≠ 0`: `obtain ⟨n, ⟨h₁, h₂⟩, -⟩ := ϖ.existsUnique_zpow_norm_smul_mem_Ioc hε hx`, giving
   `ε * ‖ϖ‖ < ‖(ϖ.unit ^ n : R) • x‖ ≤ ε` (`Set.mem_Ioc`).
4. Bound on the scaled vector: `hfx := h _ h₂`; rewrite `f.map_smul` and `ϖ.norm_zpow_smul` to get
   `‖ϖ‖ ^ n * ‖f x‖ ≤ C`.
5. Rewrite `h₁` with `ϖ.norm_zpow_smul`: `ε * ‖ϖ‖ < ‖ϖ‖ ^ n * ‖x‖`. Put `t := ‖ϖ‖ ^ n > 0` (`zpow_pos ϖ.norm_pos`).
6. Conclude: `‖f x‖ ≤ C / t` (`le_div_iff₀`), and `C / t ≤ C / (ε * ‖ϖ‖) * ‖x‖` because
   `C * (ε * ‖ϖ‖) ≤ C * (t * ‖x‖)` (`mul_le_mul_of_nonneg_left h₁.le hC`), cleared with `div_le_iff₀`,
   `le_div_iff₀` (denominators `t`, `ε * ‖ϖ‖` positive) and `ring`-normalisation. Keep the identity explicit
   (readability over `nlinarith`).

#### Mathlib lemmas needed
`NormedRing.PseudoUniformizer.existsUnique_zpow_norm_smul_mem_Ioc` (L0), `NormedRing.PseudoUniformizer.norm_zpow_smul` (L0), `NormedRing.PseudoUniformizer.norm_pos` (L0), `LinearMap.map_smul`, `Set.mem_Ioc`, `zpow_pos`, `le_div_iff₀`, `div_le_iff₀`, `mul_le_mul_of_nonneg_left`, `map_zero`, `norm_zero`.
#### Sources
[Sch] Prop 3.1 proof, `schneider.txt:541–546` ("choose an integer `m` such that `|a|^{m+2} < ‖v‖ ≤ |a|^{m+1}`"); [Buz07] `buzzard.txt:266–270`; [SRC] `01_OperatorNorm.le_opNorm` (the same computation inline).
#### Generality decision
Explicit `ϖ` (the constant mentions `‖ϖ‖`), `[NormOneClass R]` for `0 < ‖ϖ‖`, a *linear* map `f` (continuity is irrelevant), closed ball `‖x‖ ≤ ε` so that `ε = 1` is literally the unit ball.

### [T003] Continuity is boundedness over a Tate normed ring
- **Status**: done (2026-10-06) · **File**: `Norm.lean` · **Depends on**: T001, T002 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-06 DONE — exists_bound via Metric.continuousAt_iff + scaling trick at δ/2; axioms standard
- **Leaves**: L1.9–L1.12

#### Statement
```lean
theorem exists_bound [IsTate R] (u : M →L[R] N) : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖ := by
  sorry

theorem continuous_iff_exists_bound [IsTate R] (f : M →ₗ[R] N) :
    Continuous f ↔ ∃ C, ∀ x, ‖f x‖ ≤ C * ‖x‖ := by
  sorry

theorem continuous_iff_exists_forall_norm_le [IsTate R] (f : M →ₗ[R] N) :
    Continuous f ↔ ∃ C, ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ C := by
  sorry

theorem le_opNorm [IsTate R] (u : M →L[R] N) (x : M) : ‖u x‖ ≤ ‖u‖ * ‖x‖ := by
  sorry
```
#### Proof sketch
1. `exists_bound`: `obtain ⟨ϖ⟩ := NormedRing.IsTate.exists_pseudoUniformizer (R := R)`. Continuity at `0`:
   `obtain ⟨δ, hδ, H⟩ := Metric.continuousAt_iff.1 u.continuous.continuousAt 1 one_pos`; after `map_zero` and
   `dist_zero_right`, `H : ‖y‖ < δ → ‖u y‖ < 1`. Then `⟨1 / (δ / 2 * ‖(ϖ : R)‖), fun x ↦
   norm_map_le_div_mul_of_forall_norm_le ϖ (u : M →ₗ[R] N) (half_pos hδ) (fun y hy ↦ (H (by linarith)).le) x⟩`.
2. `continuous_iff_exists_bound`: `⟨fun hf ↦ exists_bound ⟨f, hf⟩, fun ⟨C, hC⟩ ↦ AddMonoidHomClass.continuous_of_bound f C hC⟩`
   (⚠ `LinearMap.continuous_of_bound` is not a name at this pin).
3. `continuous_iff_exists_forall_norm_le`: (⇒) from step 2 with `C' := max C 0`:
   `‖f x‖ ≤ C * ‖x‖ ≤ max C 0 * 1`. (⇐) `obtain ⟨ϖ⟩` again; `norm_map_le_div_mul_of_forall_norm_le ϖ f one_pos h`
   is a bound, then `AddMonoidHomClass.continuous_of_bound`.
4. `le_opNorm`: `le_opNorm_of_bound u (exists_bound u) x`.

#### Mathlib lemmas needed
`NormedRing.IsTate.exists_pseudoUniformizer`, `Metric.continuousAt_iff`, `Continuous.continuousAt`, `dist_zero_right`, `map_zero`, `half_pos`, `AddMonoidHomClass.continuous_of_bound`, `mul_le_of_le_one_right`, `le_max_left`, `le_max_right`.
#### Sources
[JN] `jn.txt:522–523` ("continuity of an `R`-linear map `φ` is equivalent to boundedness"); [Sch] Prop 3.1 `schneider.txt:520–546`; [RM] §1.1.2.
#### Generality decision
`[IsTate R]` as a Prop (existence only; no constant in the statements); `continuous_iff_*` stated for `LinearMap`s, `le_opNorm` for the continuous map. The unit-ball form uses the closed ball.

### [CLEANUP-1] Run `/cleanup` on `Norm.lean`
- **Status**: done (2026-10-06) · **File**: `Norm.lean` · **Depends on**: T003 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 inline audit with CLEANUP-2: style ok, runLinter passed
- **Description**: after the 3rd proof ticket on `Norm.lean` (cadence rule). Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T004] The unit-ball comparison and the ratio supremum
- **Status**: done (2026-10-06) · **File**: `Norm.lean` · **Depends on**: CLEANUP-1 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-06 DONE — ratio supremum via le_ciSup/ciSup_le; axioms standard
- **Leaves**: L1.13–L1.15

#### Statement
```lean
theorem opNorm_le_div_of_forall_norm_le (ϖ : PseudoUniformizer R) (u : M →L[R] N) {ε C : ℝ}
    (hε : 0 < ε) (h : ∀ x, ‖x‖ ≤ ε → ‖u x‖ ≤ C) : ‖u‖ ≤ C / (ε * ‖(ϖ : R)‖) := by
  sorry

theorem norm_le_opNorm_of_norm_le_one [IsTate R] (u : M →L[R] N) {x : M} (hx : ‖x‖ ≤ 1) :
    ‖u x‖ ≤ ‖u‖ := by
  sorry

theorem opNorm_eq_iSup_div [IsTate R] (u : M →L[R] N) : ‖u‖ = ⨆ x, ‖u x‖ / ‖x‖ := by
  sorry
```
#### Proof sketch
1. `opNorm_le_div_of_forall_norm_le`: `hC : 0 ≤ C := by simpa using h 0 (by simp [hε.le])`; then
   `opNorm_le_bound u (div_nonneg hC (mul_pos hε ϖ.norm_pos).le) (norm_map_le_div_mul_of_forall_norm_le ϖ (u : M →ₗ[R] N) hε h)`.
2. `norm_le_opNorm_of_norm_le_one`: `(le_opNorm u x).trans (mul_le_of_le_one_right (opNorm_nonneg u) hx)`.
3. `opNorm_eq_iSup_div`: `hbdd : BddAbove (Set.range fun x ↦ ‖u x‖ / ‖x‖)` with bound `‖u‖`
   (`div_le_of_le_mul₀ (norm_nonneg _) (opNorm_nonneg _) (le_opNorm u x)`). `le_antisymm`:
   (≤) `opNorm_le_bound _ (Real.iSup_nonneg fun x ↦ div_nonneg (norm_nonneg _) (norm_nonneg _))`; for `x` with
   `‖x‖ = 0` both sides vanish (`le_opNorm` gives `‖u x‖ ≤ 0`); otherwise `‖u x‖ = ‖u x‖ / ‖x‖ * ‖x‖`
   (`div_mul_cancel₀`) and `le_ciSup hbdd x`. (≥) `ciSup_le fun x ↦ div_le_of_le_mul₀ … (le_opNorm u x)`
   (`Nonempty M` from `0`).

#### Mathlib lemmas needed
`div_nonneg`, `mul_pos`, `mul_le_of_le_one_right`, `div_le_of_le_mul₀`, `Real.iSup_nonneg`, `le_ciSup`, `ciSup_le`, `div_mul_cancel₀`, `norm_nonneg`.
#### Sources
[Sch] Cor 3.2 and the warning `schneider.txt:538–550`; [JN] `jn.txt:523`; [RM] §1.1.2 corrected (erratum E9 in `plan.md`).
#### Generality decision
The ratio supremum ranges over all `x` (the `x = 0` term is `0`); the two-sided unit-ball comparison is the honest replacement for the false `sup_{‖x‖ ≤ 1}` formula; explicit `ϖ` in the lemma whose constant mentions `‖ϖ‖`.

### [CLEANUP-2] Run `/cleanup` on `Norm.lean`
- **Status**: done (2026-10-06) · **File**: `Norm.lean` · **Depends on**: T004 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 Norm.lean: 0 sorry, lines ≤ 100, runLinter passed, 18 decls standard axioms
- **Description**: final per-file cleanup of `Norm.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T005] The normed group of bounded operators
- **Status**: done (2026-10-06) · **File**: `Banach.lean` · **Depends on**: CLEANUP-2 · **Parallel**: no · **Type**: lemmas + instances
- **Progress**: 2026-10-06 DONE — add_apply is the root lemma; instIsUltrametricDist via isUltrametricDist_of_isNonarchimedean_norm
- **Leaves**: L2.1–L2.5

#### Statement
```lean
theorem opNorm_add_le (u v : M →L[R] N) : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := by
  sorry

theorem opNorm_eq_zero_iff (u : M →L[R] N) : ‖u‖ = 0 ↔ u = 0 := by
  sorry

theorem opNorm_add_le_max [IsUltrametricDist N] (u v : M →L[R] N) : ‖u + v‖ ≤ max ‖u‖ ‖v‖ := by
  sorry

scoped instance instIsUltrametricDist [IsUltrametricDist N] : IsUltrametricDist (M →L[R] N) := by
  sorry
```
#### Proof sketch
1. `opNorm_add_le`: `opNorm_le_bound _ (add_nonneg (opNorm_nonneg u) (opNorm_nonneg v)) fun x ↦ by
   rw [ContinuousLinearMap.add_apply, add_mul]; exact norm_add_le_of_le (le_opNorm u x) (le_opNorm v x)`.
2. `opNorm_eq_zero_iff`: (→) `ext x; exact norm_le_zero_iff.1 (by simpa [h] using le_opNorm u x)`;
   (←) `rintro rfl; exact opNorm_zero`.
3. Check that `instNormedAddCommGroup` (already complete in the skeleton) still elaborates after steps 1–2 are
   proved; do not change its shape (`toNorm` must stay `instNorm`, decision 2).
4. `opNorm_add_le_max`: `opNorm_le_bound _ (le_max_of_le_left (opNorm_nonneg u)) fun x ↦ by
   rw [ContinuousLinearMap.add_apply, max_mul_of_nonneg _ _ (norm_nonneg x)];
   exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (le_opNorm u x) (le_opNorm v x))`.
5. `instIsUltrametricDist`: `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm opNorm_add_le_max`.

#### Mathlib lemmas needed
`norm_add_le_of_le`, `ContinuousLinearMap.add_apply`, `add_mul`, `norm_le_zero_iff`, `IsUltrametricDist.norm_add_le_max`, `max_le_max`, `max_mul_of_nonneg`, `le_max_of_le_left`, `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`.
#### Sources
[Bel] `bellaiche.txt:1975–1981`; [RM] §1.1.3; [Mathlib] `ContinuousLinearMap.opNorm_add_le`, `opNorm_zero_iff`.
#### Generality decision
Ultrametricity of `M →L[R] N` needs only ultrametric `N`; the normed-group instance needs `[NormedAddCommGroup N]` (separation) and `[IsTate R]` (through `le_opNorm`).

### [T006] Completeness of the operator space
- **Status**: done (2026-10-06) · **File**: `Banach.lean` · **Depends on**: T005 · **Parallel**: no · **Type**: instance
- **Progress**: 2026-10-06 DONE — Schneider 3.3 transcription with Metric.cauchySeq_iff (two-index), limit via LinearMap.mkContinuous
- **Leaves**: L2.6

#### Statement
```lean
scoped instance instCompleteSpace [CompleteSpace N] : CompleteSpace (M →L[R] N) := by
  sorry
```
#### Proof sketch
Transcribe [SRC] `01_OperatorNorm.exists_lim_of_cauchySeq` (sorry-free) into `Metric.complete_of_cauchySeq_tendsto`:
1. `refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_`; `Metric.cauchySeq_iff.1 hu`.
2. Pointwise Cauchy: `dist (u m x) (u n x) = ‖(u m - u n) x‖ ≤ ‖u m - u n‖ * ‖x‖` (`dist_eq_norm`,
   `ContinuousLinearMap.sub_apply`, `le_opNorm`); use `ε / (‖x‖ + 1)`.
3. `choose v₀ hv₀ using fun x ↦ cauchySeq_tendsto_of_complete (hptwise x)`; additivity and `R`-linearity of `v₀`
   by `tendsto_nhds_unique` against `(hv₀ x).add (hv₀ y)` and `(hv₀ x).const_smul c` (`map_add`, `map_smul`).
4. Bound: `obtain ⟨N₀, hN₀⟩ := hu' 1 one_pos`; `‖v₀ x‖ ≤ (‖u N₀‖ + 1) * ‖x‖` by `le_of_tendsto (hv₀ x).norm`
   and `Filter.eventually_atTop` (`‖u n x‖ ≤ ‖u n - u N₀‖ * ‖x‖ + ‖u N₀‖ * ‖x‖`).
5. `v := LinearMap.mkContinuous { toFun := v₀, map_add' := _, map_smul' := _ } _ hbound`.
6. `Metric.tendsto_atTop`: for `ε`, take `N₁` from the Cauchy condition at `ε / 2`; `dist (u n) v = ‖u n - v‖ ≤ ε / 2`
   by `opNorm_le_bound` and, for each `x`, `le_of_tendsto` on `fun m ↦ ‖u n x - u m x‖ → ‖(u n - v) x‖`.

#### Mathlib lemmas needed
`Metric.complete_of_cauchySeq_tendsto`, `Metric.cauchySeq_iff`, `cauchySeq_tendsto_of_complete`, `tendsto_nhds_unique`, `Filter.Tendsto.add`, `Filter.Tendsto.const_smul`, `Filter.Tendsto.sub`, `Filter.Tendsto.norm`, `le_of_tendsto`, `Filter.eventually_atTop`, `LinearMap.mkContinuous`, `Metric.tendsto_atTop`, `dist_eq_norm`, `ContinuousLinearMap.sub_apply`, `map_add`, `map_smul`.
#### Sources
[Sch] Prop 3.3 `schneider.txt:551–588`; [Bel] `bellaiche.txt:1981`; [Lud] `ludwig.txt:218–222`; [SRC] `01_OperatorNorm.exists_lim_of_cauchySeq`.
#### Generality decision
`[CompleteSpace N]` only; completeness of `M` is not used and not assumed.

### [T007] The Banach ring of endomorphisms and the scalars
- **Status**: done (2026-10-06) · **File**: `Banach.lean` · **Depends on**: T006 · **Parallel**: no · **Type**: lemmas + instances
- **Progress**: 2026-10-06 DONE — norm_id via le_of_mul_le_mul_right; equality for multiplicative units via le_inv_mul_iff₀
- **Leaves**: L2.7–L2.12

#### Statement
```lean
theorem opNorm_comp_le {P : Type*} [NormedAddCommGroup P] [Module R P] [IsBoundedSMul R P]
    (v : N →L[R] P) (u : M →L[R] N) : ‖v.comp u‖ ≤ ‖v‖ * ‖u‖ := by
  sorry

theorem norm_id [Nontrivial M] : ‖ContinuousLinearMap.id R M‖ = 1 := by
  sorry

theorem opNorm_smul_le (a : R) (u : M →L[R] N) : ‖a • u‖ ≤ ‖a‖ * ‖u‖ := by
  sorry

scoped instance instIsBoundedSMul : IsBoundedSMul R (M →L[R] N) := by
  sorry

theorem opNorm_smul_of_isMultiplicative {a : Rˣ} (ha : IsMultiplicative (a : R))
    (u : M →L[R] N) : ‖(a : R) • u‖ = ‖(a : R)‖ * ‖u‖ := by
  sorry
```
#### Proof sketch
1. `opNorm_comp_le`: `opNorm_le_bound _ (mul_nonneg (opNorm_nonneg v) (opNorm_nonneg u)) fun x ↦ by
   rw [ContinuousLinearMap.comp_apply, mul_assoc];
   exact (le_opNorm v _).trans (mul_le_mul_of_nonneg_left (le_opNorm u x) (opNorm_nonneg v))`.
2. `norm_id`: `le_antisymm norm_id_le`; `obtain ⟨x, hx⟩ := exists_ne (0 : M)`;
   `have h := le_opNorm (ContinuousLinearMap.id R M) x`; `rw [ContinuousLinearMap.id_apply] at h`;
   `exact le_of_mul_le_mul_right (by simpa using h) (norm_pos_iff.2 hx)`.
3. Check `instNormedRing` / `instNormOneClass` (complete in the skeleton) still elaborate.
4. `opNorm_smul_le`: `opNorm_le_bound _ (mul_nonneg (norm_nonneg a) (opNorm_nonneg u)) fun x ↦ by
   rw [ContinuousLinearMap.smul_apply, mul_assoc];
   exact (norm_smul_le a _).trans (mul_le_mul_of_nonneg_left (le_opNorm u x) (norm_nonneg a))`.
5. `instIsBoundedSMul`: `IsBoundedSMul.of_norm_smul_le opNorm_smul_le`.
6. `opNorm_smul_of_isMultiplicative`: `refine le_antisymm (opNorm_smul_le _ _) ?_`;
   `have h := opNorm_smul_le ((a⁻¹ : Rˣ) : R) ((a : R) • u)`; `rw [smul_smul, Units.inv_mul, one_smul, ha.norm_inv] at h`;
   `rwa [le_inv_mul_iff₀ ha.norm_pos] at h`.

#### Mathlib lemmas needed
`ContinuousLinearMap.comp_apply`, `ContinuousLinearMap.smul_apply`, `ContinuousLinearMap.id_apply`, `norm_smul_le`, `exists_ne`, `le_of_mul_le_mul_right`, `norm_pos_iff`, `IsBoundedSMul.of_norm_smul_le`, `smul_smul`, `Units.inv_mul`, `one_smul`, `le_inv_mul_iff₀`; Layer 0: `NormedRing.IsMultiplicative.norm_inv`, `NormedRing.IsMultiplicative.norm_pos`.
#### Sources
[Bel] `bellaiche.txt:1978` ("`|φ'φ| ≤ |φ'||φ|`"); [RM] §1.1.3 (E11: equality for multiplicative *units*); [Mathlib] `opNorm_comp_le`, `norm_id`, `opNorm_smul_le`.
#### Generality decision
The scalar statements live in a `[NormedCommRing R]` section because Mathlib's `ContinuousLinearMap.module` needs `SMulCommClass R R N` (inventory). `norm_id` takes `[Nontrivial M]`, the normed-group reading of Mathlib's `NontrivialTopology`.

### [CLEANUP-3] Run `/cleanup` on `Banach.lean`
- **Status**: done (2026-10-06) · **File**: `Banach.lean` · **Depends on**: T007 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 inline audit: wrapped the >100-char line, proofs short; linter run deferred to CLEANUP-4 (file still has T008–T010 sorries)
- **Description**: after the 3rd proof ticket on `Banach.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T008] Sums of operators
- **Status**: done (2026-10-06) · **File**: `Banach.lean` · **Depends on**: CLEANUP-3 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-06 DONE — summability is Mathlib's nonarchimedean criterion on the scoped instances; pointwise sums via HasSum.map along w ↦ w x (omit CompleteSpace N)
- **Leaves**: L2.13–L2.15

#### Statement
```lean
theorem summable_of_tendsto_cofinite_zero [IsUltrametricDist N] {u : ι → M →L[R] N}
    (hu : Tendsto u cofinite (𝓝 0)) : Summable u := by
  sorry

theorem hasSum_apply {u : ι → M →L[R] N} {v : M →L[R] N} (hu : HasSum u v) (x : M) :
    HasSum (fun i ↦ u i x) (v x) := by
  sorry

theorem tsum_apply {u : ι → M →L[R] N} (hu : Summable u) (x : M) :
    (∑' i, u i) x = ∑' i, u i x := by
  sorry
```
#### Proof sketch
1. `summable_of_tendsto_cofinite_zero`: `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hu`; the
   instances `NonarchimedeanAddGroup (M →L[R] N)` (via `IsUltrametricDist.nonarchimedeanAddGroup` from T005) and
   `CompleteSpace` (T006) must be found by unification — if not, `haveI` them.
2. `hasSum_apply`: `let e : (M →L[R] N) →+ N := AddMonoidHom.mk' (fun v ↦ v x) fun _ _ ↦ rfl`;
   `have he : Continuous e := AddMonoidHomClass.continuous_of_bound e ‖x‖ fun v ↦ by rw [mul_comm]; exact le_opNorm v x`;
   `exact hu.map e he`.
3. `tsum_apply`: `(hasSum_apply hu.hasSum x).tsum_eq.symm`.

#### Mathlib lemmas needed
`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`, `IsUltrametricDist.nonarchimedeanAddGroup`, `AddMonoidHom.mk'`, `AddMonoidHomClass.continuous_of_bound`, `HasSum.map`, `Summable.hasSum`, `HasSum.tsum_eq`.
#### Sources
[RM] §1.1.4 ("`∑' uᵢ` converges in operator norm and pointwise, and `‖∑' uᵢ‖ ≤ sup ‖uᵢ‖`" — the bound is Mathlib's `IsUltrametricDist.norm_tsum_le` on the ultrametric instance, no restatement).
#### Generality decision
`hasSum_apply` needs neither completeness nor ultrametricity (only `le_opNorm`); if the linter flags the unused section variables, `omit` them at cleanup.

### [T009] The Neumann series in the endomorphism ring
- **Status**: done (2026-10-06) · **File**: `Banach.lean` · **Depends on**: T008 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-06 DONE — Units.oneSub/Units.inv_unique + Layer 0 norm lemmas; needed import Mathlib.Analysis.Normed.Ring.Units
- **Leaves**: L2.16–L2.19

#### Statement
```lean
theorem isUnit_of_norm_one_sub_lt_one (u : M →L[R] M) (hu : ‖1 - u‖ < 1) : IsUnit u := by
  sorry

theorem norm_eq_one_of_norm_one_sub_lt_one [Nontrivial M] (u : M →L[R] M) (hu : ‖1 - u‖ < 1) :
    ‖u‖ = 1 := by
  sorry

theorem norm_inv_eq_one_of_norm_one_sub_lt_one [Nontrivial M] (u : (M →L[R] M)ˣ)
    (hu : ‖1 - (u : M →L[R] M)‖ < 1) : ‖((u⁻¹ : (M →L[R] M)ˣ) : M →L[R] M)‖ = 1 := by
  sorry

theorem isOpen_setOf_isUnit : IsOpen {u : M →L[R] M | IsUnit u} := by
  sorry
```
#### Proof sketch
All four are Mathlib's / Layer 0's facts about a complete normed ring, applied to `M →L[R] M` with the scoped
instances (`instNormedRing`, `instCompleteSpace` with `N := M`, `instIsUltrametricDist`, `instNormOneClass`).
`HasSummableGeomSeries (M →L[R] M)` comes from `CompleteSpace`; `haveI` it if unification stalls.
1. `isUnit_of_norm_one_sub_lt_one`: `⟨Units.oneSub (1 - u) hu, by rw [Units.val_oneSub, sub_sub_cancel]⟩`.
2. `norm_eq_one_of_norm_one_sub_lt_one`: `have h := NormedRing.norm_one_sub_of_norm_lt_one hu` (in the ring
   `M →L[R] M`; needs `NormOneClass` ⇐ `Nontrivial M`, `IsUltrametricDist` ⇐ ultrametric `M`); `rwa [sub_sub_cancel] at h`.
3. `norm_inv_eq_one_of_norm_one_sub_lt_one`: `have hval : ((u⁻¹ : (M →L[R] M)ˣ) : M →L[R] M) = ((Units.oneSub (1 - u) hu)⁻¹ : (M →L[R] M)ˣ) :=
   Units.inv_unique (by rw [Units.val_oneSub, sub_sub_cancel])`; the inverse of `Units.oneSub t h` is `∑' n, t ^ n`
   by definition (`rfl`; check with `#print Units.oneSub`); finish with `NormedRing.norm_tsum_geometric hu`.
4. `isOpen_setOf_isUnit`: `Units.isOpen`.

#### Mathlib lemmas needed
`Units.oneSub`, `Units.val_oneSub`, `Units.inv_unique`, `Units.isOpen`, `sub_sub_cancel`; Layer 0: `NormedRing.norm_one_sub_of_norm_lt_one`, `NormedRing.norm_tsum_geometric`.
#### Sources
[RM] §1.1.5; [BGR] 1.2.4/4–5 `bgr-3.7.md:135–139`; Layer 0 §0.2.3.
#### Generality decision
`[IsUltrametricDist M] [CompleteSpace M]` for the Banach ring; `[Nontrivial M]` exactly where `‖1‖ = 1` is used (the two norm equalities), not for `IsUnit` or openness.

### [T010] Agreement with Mathlib at the instance level
- **Status**: done (2026-10-06) · **File**: `Banach.lean` · **Depends on**: T009 · **Parallel**: no · **Type**: theorem
- **Progress**: 2026-10-06 DONE — private normedAddCommGroup_ext (cases) + MetricSpace.ext rfl: norms and dists agree definitionally, uniformities propositionally
- **Leaves**: L2.20

#### Statement
```lean
theorem instNormedAddCommGroup_eq :
    (instNormedAddCommGroup : NormedAddCommGroup (M →L[K] N)) =
      ContinuousLinearMap.toNormedAddCommGroup := by
  sorry
```
#### Proof sketch
1. Prove a private extensionality lemma (Mathlib has `MetricSpace.ext` but no `NormedAddCommGroup.ext` at this
   pin): for `i j : NormedAddCommGroup E`, if `i.toAddCommGroup = j.toAddCommGroup`, `∀ x, @norm E i.toNorm x =
   @norm E j.toNorm x` and `∀ x y, @dist E i.toDist x y = @dist E j.toDist x y`, then `i = j`:
   `cases i; cases j`, turn the three hypotheses into equalities of the `toNorm` (`funext`), `toAddCommGroup`
   and `toMetricSpace` (`MetricSpace.ext (funext₂ h)`) fields, `subst`, `rfl`.
2. Apply it: the additive groups are both `ContinuousLinearMap.addCommGroup` (`rfl`); the norms agree by
   `norm_eq_opNorm` (`rfl`); the distances agree because both instances satisfy `dist x y = ‖x - y‖`
   (`NormedAddCommGroup.dist_eq` on each side, with the norms already identified).
3. Mathlib's side carries the strong-topology uniformity through `replaceUniformity`
   (`Mathlib/Analysis/Normed/Operator/Basic.lean:379–383`); `MetricSpace.ext` only needs `dist`, so this is
   invisible to the proof.

#### Mathlib lemmas needed
`MetricSpace.ext`, `funext`, `NormedAddCommGroup.dist_eq`, `norm_eq_opNorm` (T001-level `rfl`).
#### Sources
[RM] §1.1.6; [Mathlib] `ContinuousLinearMap.toNormedAddCommGroup` (`Operator/NormedSpace.lean:166`).
#### Generality decision
Field scalars only (`NontriviallyNormedField K`, `NormedSpace`); the scoped instance's `IsTate K` is Layer 0's instance for fields.

### [CLEANUP-4] Run `/cleanup` on `Banach.lean`
- **Status**: done (2026-10-06) · **File**: `Banach.lean` · **Depends on**: T010 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 Banach.lean: 0 sorry, lines ≤ 100, runLinter passed, axioms standard
- **Description**: final per-file cleanup of `Banach.lean` (also the 3rd proof ticket since CLEANUP-3). Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T011] The Baire step of the open mapping theorem
- **Status**: done (2026-10-06) · **File**: `OpenMapping.lean` · **Depends on**: CLEANUP-2 · **Parallel**: yes (with G2, G5, G6) · **Type**: lemma
- **Progress**: 2026-10-06 DONE — Mathlib's Baire step with the Layer 0 shell lemma at radius ε/2; constant 4n/(ε‖ϖ‖); readable inequalities (le_div_iff₀, inv_mul_le_iff₀, explicit ring identities)
- **Leaves**: L3.1

#### Statement
```lean
theorem exists_approx_preimage_norm_le (u : M →L[R] N) (hu : Surjective u) :
    ∃ C ≥ 0, ∀ y, ∃ x, dist (u x) y ≤ 1 / 2 * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖ := by
  sorry
```
#### Proof sketch
Transcribe `Mathlib/Analysis/Normed/Operator/Banach.lean:92–152` (`exists_approx_preimage_norm_le`) with
Layer 0's shell lemma in place of `rescale_to_shell`; [SRC] `01_OperatorNorm.exists_approx_preimage_norm_le` is
a sorry-free transcription to copy from.
1. `A : ⋃ n : ℕ, closure (u '' ball 0 n) = univ` from surjectivity and `exists_nat_gt ‖x‖`.
2. `nonempty_interior_of_iUnion_of_closed (fun n ↦ isClosed_closure) A` gives `n, a` with
   `a ∈ interior (closure (u '' ball 0 n))`; `mem_interior_iff_mem_nhds`, `Metric.mem_nhds_iff` give `ε > 0` with
   `ball a ε ⊆ closure (u '' ball 0 n)`.
3. `obtain ⟨ϖ⟩ := IsTate.exists_pseudoUniformizer`; `refine ⟨4 * n / (ε * ‖ϖ‖), by positivity, fun y ↦ ?_⟩`;
   `rcases eq_or_ne y 0 with rfl | hy`, the zero case by `simp`.
4. `obtain ⟨j, ⟨hj₁, hj₂⟩, -⟩ := ϖ.existsUnique_zpow_norm_smul_mem_Ioc (half_pos εpos) hy`; set
   `d := (ϖ.unit ^ j : R)`, `δ := ‖d • y‖ / 4 > 0`.
5. `a + d • y ∈ ball a ε` (`hj₂` and `half_lt_self`) and `a ∈ ball a ε`; `Metric.mem_closure_iff` gives
   `x₁ x₂ ∈ ball 0 n` with `dist (u x₁) (a + d • y) < δ`, `dist (u x₂) a < δ`.
6. `I : ‖u (x₁ - x₂) - d • y‖ ≤ 2 * δ` (`map_sub`, `abel`, `norm_sub_le`).
7. `x := (ϖ.unit ^ (-j) : R) • (x₁ - x₂)`: `J : ‖u x - y‖ ≤ 1 / 2 * ‖y‖` using `(ϖ.unit ^ (-j)) • d • y = y`
   (`smul_smul`, `← Units.val_mul`, `zpow_neg`, `inv_mul_cancel`), `ϖ.norm_zpow_smul`, and
   `‖ϖ‖ ^ (-j) * ‖d • y‖ = ‖y‖`; `K : ‖x‖ ≤ 4 * n / (ε * ‖ϖ‖) * ‖y‖` from `‖x₁ - x₂‖ ≤ 2 * n` and
   `‖ϖ‖ ^ (-j) * (ε * ‖ϖ‖) ≤ 2 * ‖y‖` (from `hj₁`). Keep the real-number identities explicit.

#### Mathlib lemmas needed
`nonempty_interior_of_iUnion_of_closed`, `isClosed_closure`, `mem_interior_iff_mem_nhds`, `Metric.mem_nhds_iff`, `Metric.mem_closure_iff`, `Metric.mem_ball`, `dist_eq_norm`, `exists_nat_gt`, `Set.mem_iUnion`, `subset_closure`, `half_pos`, `half_lt_self`, `norm_sub_le`, `smul_smul`, `Units.val_mul`, `zpow_neg`, `inv_mul_cancel`; Layer 0: `existsUnique_zpow_norm_smul_mem_Ioc`, `norm_zpow_smul`, `norm_pos`.
#### Sources
[Mathlib] docstring of `ContinuousLinearMap.exists_approx_preimage_norm_le`; [Bel] `bellaiche.txt:1983–1989`; [SRC] `01_OperatorNorm.exists_approx_preimage_norm_le`.
#### Generality decision
`[CompleteSpace N]` only (Baire on `N`); no `CompleteSpace M`, no `CompleteSpace R`, no ultrametricity (E16).

### [CLEANUP-ALL-1] Run `/cleanup-all` on the project
- **Status**: done (2026-10-06) · **File**: the project · **Depends on**: T011, CLEANUP-2, CLEANUP-4 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 inline sweep of Norm/Banach/OpenMapping(T011): all lines ≤ 100, Norm + Banach lint clean and standard axioms; no cross-file duplication
- **Description**: pre-milestone sweep (`/cleanup-all` on the Layer 1 files so far) before M1. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T012] The quantitative open mapping theorem (MILESTONE M1)
- **Status**: done (2026-10-06) · **File**: `OpenMapping.lean` · **Depends on**: CLEANUP-ALL-1 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-06 DONE (MILESTONE M1) — Mathlib's iteration transcribed verbatim; isQuotientMap through Ultra.isOpenMap (dot notation would hit Mathlib's field version)
- **Leaves**: L3.2–L3.4

#### Statement
```lean
theorem exists_preimage_norm_le (u : M →L[R] N) (hu : Surjective u) :
    ∃ C > 0, ∀ y, ∃ x, u x = y ∧ ‖x‖ ≤ C * ‖y‖ := by
  sorry

protected theorem isOpenMap (u : M →L[R] N) (hu : Surjective u) : IsOpenMap u := by
  sorry

theorem isQuotientMap (u : M →L[R] N) (hu : Surjective u) : IsQuotientMap u := by
  sorry
```
#### Proof sketch
1. `exists_preimage_norm_le`: transcribe `Mathlib/Analysis/Normed/Operator/Banach.lean:162–225` verbatim
   (also [SRC] `exists_preimage_norm_le`): `obtain ⟨C, C0, hC⟩ := exists_approx_preimage_norm_le u hu`;
   `choose g hg using hC`; `h y := y - u (g y)` with `‖h y‖ ≤ 1 / 2 * ‖y‖`; `refine ⟨2 * C + 1, by linarith, fun y ↦ ?_⟩`;
   `‖h^[n] y‖ ≤ (1 / 2) ^ n * ‖y‖` by induction (`Function.iterate_succ'`); `u_n := g (h^[n] y)` with
   `‖u_n‖ ≤ (1 / 2) ^ n * (C * ‖y‖)`; `Summable (‖u_n‖)` by `Summable.of_nonneg_of_le` and
   `summable_geometric_of_lt_one`; `x := ∑' n, u_n`; `‖x‖ ≤ (2 * C + 1) * ‖y‖` via `norm_tsum_le_tsum_norm`,
   `Summable.tsum_le_tsum`, `tsum_mul_right`, `tsum_geometric_two`; `u (∑ i < n, u_i) = y - h^[n] y` by induction
   (`Finset.sum_range_succ`, `Function.iterate_succ_apply'`); pass to the limit with `HasSum.tendsto_sum_nat`,
   `tendsto_nhds_unique`, `squeeze_zero`, `tendsto_pow_atTop_nhds_zero_of_lt_one`.
2. `isOpenMap`: transcribe `Banach.lean:229–248`: `Metric.isOpen_iff`; for `y = u x ∈ u '' s` and the
   `ε`-ball around `x` inside `s`, the ball of radius `ε / C` around `y` is in the image (preimage `w` of
   `z - y` with `‖w‖ ≤ C * ‖z - y‖ < ε`).
3. `isQuotientMap`: `(Ultra.isOpenMap u hu).isQuotientMap u.continuous hu`.

#### Mathlib lemmas needed
`Function.iterate_succ'`, `Function.iterate_succ_apply'`, `Summable.of_nonneg_of_le`, `summable_geometric_of_lt_one`, `summable_geometric_two`, `Summable.of_norm`, `norm_tsum_le_tsum_norm`, `Summable.tsum_le_tsum`, `tsum_mul_right`, `tsum_geometric_two`, `Finset.sum_range_succ`, `HasSum.tendsto_sum_nat`, `tendsto_nhds_unique`, `squeeze_zero`, `tendsto_pow_atTop_nhds_zero_of_lt_one`, `tendsto_iff_norm_sub_tendsto_zero`, `Metric.isOpen_iff`, `Metric.mem_ball`, `dist_eq_norm`, `mul_div_cancel₀`, `IsOpenMap.isQuotientMap`.
#### Sources
[Bel] `bellaiche.txt:1983–1989`; [JN] `jn.txt:525`; [Lud] `ludwig.txt:226–228`; [Sch] Prop 8.6 `schneider.txt:2357–2372`; [Mathlib] `ContinuousLinearMap.{exists_preimage_norm_le, isOpenMap, isQuotientMap}`; [RM] §1.2.1 (seam S1 recorded in the module docstring).
#### Generality decision
`[CompleteSpace M] [CompleteSpace N]`, nothing on `R` beyond Tate; `isOpenMap` is `protected` as in Mathlib.

### [T013] Bijective operators are isomorphisms
- **Status**: done (2026-10-06) · **File**: `OpenMapping.lean` · **Depends on**: T012 · **Parallel**: no · **Type**: lemma + defs
- **Progress**: 2026-10-06 DONE — continuous_symm from the quantitative OMT; defs unchanged
- **Leaves**: L3.5–L3.6

#### Statement
```lean
theorem continuous_symm (e : M ≃ₗ[R] N) (he : Continuous e) : Continuous e.symm := by
  sorry

noncomputable def toContinuousLinearEquivOfContinuous (e : M ≃ₗ[R] N) (he : Continuous e) :
    M ≃L[R] N :=
  { e with
    continuous_toFun := he
    continuous_invFun := continuous_symm e he }

noncomputable def continuousLinearEquivOfBijective (u : M →L[R] N) (hu : Bijective u) :
    M ≃L[R] N :=
  toContinuousLinearEquivOfContinuous (LinearEquiv.ofBijective (u : M →ₗ[R] N) hu) u.continuous
```
#### Proof sketch
1. `continuous_symm`: `let u : M →L[R] N := ⟨e, he⟩`; `obtain ⟨C, -, hC⟩ := exists_preimage_norm_le u e.surjective`;
   `refine AddMonoidHomClass.continuous_of_bound e.symm C fun y ↦ ?_`; `obtain ⟨x, hx, hle⟩ := hC y`;
   `e.symm y = x` because `e x = y` (`e.symm_apply_apply`, `hx`, or `e.injective`); `rwa` and conclude.
2. The two `def`s and their `coe` lemmas are complete; check they elaborate against the proved `continuous_symm`.

#### Mathlib lemmas needed
`AddMonoidHomClass.continuous_of_bound`, `LinearEquiv.surjective`, `LinearEquiv.injective`, `LinearEquiv.symm_apply_apply`, `LinearEquiv.apply_symm_apply`.
#### Sources
[Sch] Cor 8.7 `schneider.txt:2373–2375`; [Mathlib] `LinearEquiv.continuous_symm`, `LinearEquiv.toContinuousLinearEquivOfContinuous`, `ContinuousLinearEquiv.ofBijective`; [RM] §1.2.2.
#### Generality decision
Both modules Banach; `continuousLinearEquivOfBijective` takes `Function.Bijective u` (Mathlib's takes `ker = ⊥`, `range = ⊤`; the `Bijective` form is what `ClosedGraph.lean` and `Finite.lean` have).

### [CLEANUP-5] Run `/cleanup` on `OpenMapping.lean`
- **Status**: done (2026-10-06) · **File**: `OpenMapping.lean` · **Depends on**: T013 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 inline audit merged with CLEANUP-6
- **Description**: after the 3rd proof ticket on `OpenMapping.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T014] Strictness of operators with closed range
- **Status**: done (2026-10-06) · **File**: `OpenMapping.lean` · **Depends on**: CLEANUP-5 · **Parallel**: no · **Type**: lemmas + def
- **Progress**: 2026-10-06 DONE — quotient-norm bound via Submodule.Quotient.norm_mk_lt with slack ε/(‖u‖+1); bounded inverse from the OMT on M ⧸ ker u → range u
- **Leaves**: L3.7–L3.9

#### Statement
```lean
theorem norm_quotKerEquivRange_apply_le (x : M ⧸ LinearMap.ker (u : M →ₗ[R] N)) :
    ‖(LinearMap.quotKerEquivRange (u : M →ₗ[R] N) x : N)‖ ≤ ‖u‖ * ‖x‖ := by
  sorry

theorem exists_norm_quotKerEquivRange_symm_le
    (hu : IsClosed (LinearMap.range (u : M →ₗ[R] N) : Set N)) :
    ∃ C : ℝ, ∀ y : LinearMap.range (u : M →ₗ[R] N),
      ‖(LinearMap.quotKerEquivRange (u : M →ₗ[R] N)).symm y‖ ≤ C * ‖y‖ := by
  sorry

noncomputable def quotKerEquivRangeL (hu : IsClosed (LinearMap.range (u : M →ₗ[R] N) : Set N)) :
    (M ⧸ LinearMap.ker (u : M →ₗ[R] N)) ≃L[R] LinearMap.range (u : M →ₗ[R] N) :=
  haveI : IsClosed (LinearMap.ker (u : M →ₗ[R] N) : Set M) := u.isClosed_ker
  haveI : CompleteSpace (LinearMap.range (u : M →ₗ[R] N)) := hu.completeSpace_coe
  toContinuousLinearEquivOfContinuous (LinearMap.quotKerEquivRange (u : M →ₗ[R] N)) (by sorry)
```
#### Proof sketch
1. `norm_quotKerEquivRange_apply_le`: `refine le_of_forall_pos_lt_add fun ε hε ↦ ?_`;
   `obtain ⟨m, rfl, hm⟩ := Submodule.Quotient.norm_mk_lt x (div_pos hε …)` (choose the slack so that
   `‖u‖ * (‖x‖ + slack) < ‖u‖ * ‖x‖ + ε`; if `‖u‖ = 0` handle directly); rewrite
   `LinearMap.quotKerEquivRange_apply_mk`; `(le_opNorm u m).trans` and `mul_lt_mul_of_pos_left`.
2. `exists_norm_quotKerEquivRange_symm_le`: `haveI : IsClosed (LinearMap.ker (u : M →ₗ[R] N) : Set M) := u.isClosed_ker`
   (so `Submodule.Quotient.normedAddCommGroup`, `Submodule.Quotient.completeSpace`,
   `Submodule.Quotient.instIsBoundedSMul` apply — the last needs `NormedCommRing R`);
   `haveI := hu.completeSpace_coe`; `ū : (M ⧸ ker u) →L[R] range u :=
   LinearMap.mkContinuous (LinearMap.quotKerEquivRange (u : M →ₗ[R] N)).toLinearMap ‖u‖ (by simpa using norm_quotKerEquivRange_apply_le u)`
   (the norm of a point of `range u` is the norm in `N`: `Submodule.coe_norm`);
   `obtain ⟨C, -, hC⟩ := exists_preimage_norm_le ū (LinearEquiv.surjective _)`; identify the preimage of `y` with
   `(quotKerEquivRange u).symm y` by injectivity; `⟨C, …⟩`.
3. `quotKerEquivRangeL`: the remaining `sorry` is `Continuous (quotKerEquivRange u)`:
   `AddMonoidHomClass.continuous_of_bound _ ‖u‖ (by simpa using norm_quotKerEquivRange_apply_le u)`.

#### Mathlib lemmas needed
`le_of_forall_pos_lt_add`, `Submodule.Quotient.norm_mk_lt`, `LinearMap.quotKerEquivRange_apply_mk`, `mul_lt_mul_of_pos_left`, `ContinuousLinearMap.isClosed_ker`, `IsClosed.completeSpace_coe`, `Submodule.Quotient.normedAddCommGroup`, `Submodule.Quotient.completeSpace`, `Submodule.Quotient.instIsBoundedSMul`, `LinearMap.mkContinuous`, `LinearEquiv.surjective`, `LinearEquiv.injective`, `Submodule.coe_norm`, `AddMonoidHomClass.continuous_of_bound`.
#### Sources
[BGR] 3.7.3/4 `bgr-3.7.md:68`; [Sch] Prop 8.3 `schneider.txt:2281`; [RM] §1.2.2.
#### Generality decision
`[NormedCommRing R]` because Mathlib's `IsBoundedSMul` on quotients needs commutative scalars (inventory); the first bound needs no completeness. `quotKerEquivRangeL` is the `def` that `/beastmode` must not restate.

### [CLEANUP-6] Run `/cleanup` on `OpenMapping.lean`
- **Status**: done (2026-10-06) · **File**: `OpenMapping.lean` · **Depends on**: T014 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 OpenMapping.lean: 0 sorry, lines ≤ 100, runLinter passed, axioms standard
- **Description**: final per-file cleanup of `OpenMapping.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T015] The closed graph theorem
- **Status**: done (2026-10-06) · **File**: `ClosedGraph.lean` · **Depends on**: CLEANUP-6 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-06 DONE — Mathlib's graph argument with toContinuousLinearEquivOfContinuous; sequential form via IsSeqClosed.isClosed
- **Leaves**: L4.1–L4.2

#### Statement
```lean
theorem continuous_of_isClosed_graph (f : M →ₗ[R] N) (hf : IsClosed (f.graph : Set (M × N))) :
    Continuous f := by
  sorry

theorem continuous_of_seq_closed_graph (f : M →ₗ[R] N)
    (hf : ∀ (u : ℕ → M) (x : M) (y : N), Tendsto u atTop (𝓝 x) → Tendsto (f ∘ u) atTop (𝓝 y) →
      y = f x) :
    Continuous f := by
  sorry
```
#### Proof sketch
Transcribe `Mathlib/Analysis/Normed/Operator/Banach.lean:532–560` with the board's equivalence constructor.
1. `continuous_of_isClosed_graph`: `let : CompleteSpace f.graph := completeSpace_coe_iff_isComplete.mpr hf.isComplete`;
   `φ₀ : M →ₗ[R] M × N := LinearMap.id.prod f` with `Function.LeftInverse Prod.fst φ₀` (`fun x ↦ rfl`);
   `φ : M ≃ₗ[R] f.graph := (LinearEquiv.ofLeftInverse this).trans (LinearEquiv.ofEq _ _ f.graph_eq_range_prod.symm)`;
   `ψ : f.graph ≃L[R] M := toContinuousLinearEquivOfContinuous φ.symm continuous_subtype_val.fst`;
   `exact (continuous_subtype_val.comp ψ.symm.continuous).snd`. Instances: `IsBoundedSMul R (M × N)` (Mathlib),
   `IsBoundedSMul R f.graph` (Layer 0 `Submodule.instIsBoundedSMul`), `CompleteSpace (M × N)`.
2. `continuous_of_seq_closed_graph`: `refine continuous_of_isClosed_graph f (IsSeqClosed.isClosed ?_)`;
   `rintro φ ⟨x, y⟩ hφg hφ`; apply `hf (Prod.fst ∘ φ) x y ((continuous_fst.tendsto _).comp hφ)`; the second
   tendsto is `(continuous_snd.tendsto _).comp hφ` after `f ∘ Prod.fst ∘ φ = Prod.snd ∘ φ` (`hφg n`).

#### Mathlib lemmas needed
`completeSpace_coe_iff_isComplete`, `IsClosed.isComplete`, `LinearMap.id`, `LinearMap.prod`, `LinearEquiv.ofLeftInverse`, `LinearEquiv.ofEq`, `LinearMap.graph_eq_range_prod`, `continuous_subtype_val`, `Continuous.fst`, `Continuous.snd`, `IsSeqClosed.isClosed`, `continuous_fst`, `continuous_snd`, `Filter.Tendsto.comp`; Layer 0: `Submodule.instIsBoundedSMul`.
#### Sources
[Sch] Prop 8.5 `schneider.txt:2322–2325`; [Mathlib] `LinearMap.continuous_of_isClosed_graph`, `continuous_of_seq_closed_graph`; [RM] §1.2.3.
#### Generality decision
Both modules Banach; no ultrametricity, no `CompleteSpace R` (E16).

### [CLEANUP-7] Run `/cleanup` on `ClosedGraph.lean`
- **Status**: done (2026-10-06) · **File**: `ClosedGraph.lean` · **Depends on**: T015 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 ClosedGraph.lean: 0 sorry, lines ≤ 100, runLinter passed, axioms standard
- **Description**: final per-file cleanup of `ClosedGraph.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T016] Banach–Steinhaus
- **Status**: done (2026-10-06) · **File**: `BanachSteinhaus.lean` · **Depends on**: CLEANUP-2 · **Parallel**: yes (with G2, G3, G6) · **Type**: theorem
- **Progress**: 2026-10-06 DONE — Baire on the closed sets ⋂ᵢ {‖uᵢ x‖ ≤ n}, then opNorm_le_div_of_forall_norm_le at radius ε/2
- **Leaves**: L5.1

#### Statement
```lean
theorem banach_steinhaus {ι : Type*} (u : ι → M →L[R] N) (h : ∀ x, ∃ C, ∀ i, ‖u i x‖ ≤ C) :
    ∃ C, ∀ i, ‖u i‖ ≤ C := by
  sorry
```
#### Proof sketch
1. `obtain ⟨ϖ⟩ := IsTate.exists_pseudoUniformizer (R := R)`.
2. `A n := ⋂ i, {x : M | ‖u i x‖ ≤ n}`; closed: `isClosed_iInter fun i ↦ isClosed_le (continuous_norm.comp (u i).continuous) continuous_const`;
   covering: for `x`, `obtain ⟨C, hC⟩ := h x`, `obtain ⟨n, hn⟩ := exists_nat_ge C`, so `x ∈ A n`.
3. `nonempty_interior_of_iUnion_of_closed` gives `n`, `x₀`, and (`mem_interior_iff_mem_nhds`, `Metric.mem_nhds_iff`)
   `ε > 0` with `ball x₀ ε ⊆ A n`.
4. For `‖y‖ ≤ ε / 2`: `x₀ + y ∈ ball x₀ ε` and `x₀ ∈ ball x₀ ε`, so `‖u i y‖ = ‖u i (x₀ + y) - u i x₀‖ ≤ n + n`
   (`map_add`, `add_sub_cancel_left`, `norm_sub_le`).
5. `refine ⟨2 * n / (ε / 2 * ‖(ϖ : R)‖), fun i ↦ opNorm_le_div_of_forall_norm_le ϖ (u i) (half_pos hε) fun y hy ↦ ?_⟩`
   with step 4.

#### Mathlib lemmas needed
`isClosed_iInter`, `isClosed_le`, `continuous_norm`, `continuous_const`, `exists_nat_ge`, `nonempty_interior_of_iUnion_of_closed`, `mem_interior_iff_mem_nhds`, `Metric.mem_nhds_iff`, `Metric.mem_ball`, `dist_eq_norm`, `map_add`, `add_sub_cancel_left`, `norm_sub_le`, `Set.mem_iInter`, `Set.mem_iUnion`.
#### Sources
[Sch] Prop 6.15 `schneider.txt:1683–1690` with Example 2 `schneider.txt:1715–1718` (Baire); [Mathlib] `banach_steinhaus` (statement; its current proof goes through barrelled spaces); [RM] §1.2.4.
#### Generality decision
`[CompleteSpace M]` only; `N` any normed module; no ultrametricity (it would only replace `2n` by `n`).

### [T017] Pointwise limits of bounded operators are bounded
- **Status**: done (2026-10-06) · **File**: `BanachSteinhaus.lean` · **Depends on**: T016 · **Parallel**: no · **Type**: theorem
- **Progress**: 2026-10-06 DONE — pointwise bounded via Tendsto.bddAbove_range, then T016 and le_of_tendsto
- **Leaves**: L5.2

#### Statement
```lean
theorem continuous_of_tendsto (u : ℕ → M →L[R] N) (f : M →ₗ[R] N)
    (h : ∀ x, Tendsto (fun n ↦ u n x) atTop (𝓝 (f x))) : Continuous f := by
  sorry
```
#### Proof sketch
1. Pointwise bounded: for each `x`, `(h x).norm.bddAbove_range` gives `C x` with `∀ n, ‖u n x‖ ≤ C x`
   (`Filter.Tendsto.bddAbove_range`, `mem_upperBounds`, `Set.mem_range_self`).
2. `obtain ⟨C, hC⟩ := banach_steinhaus u (fun x ↦ ⟨_, …⟩)`.
3. `‖f x‖ ≤ C * ‖x‖`: `le_of_tendsto (h x).norm (Filter.Eventually.of_forall fun n ↦ (le_opNorm (u n) x).trans
   (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg x)))`.
4. `AddMonoidHomClass.continuous_of_bound f C`.

#### Mathlib lemmas needed
`Filter.Tendsto.bddAbove_range`, `Filter.Tendsto.norm`, `le_of_tendsto`, `Filter.Eventually.of_forall`, `mul_le_mul_of_nonneg_right`, `AddMonoidHomClass.continuous_of_bound`, `mem_upperBounds`, `Set.mem_range_self`.
#### Sources
[RM] §1.2.4 ("a pointwise limit of continuous linear maps from a Banach module is continuous"); [Mathlib] `continuousLinearMapOfTendsto`.
#### Generality decision
Sequences (`atTop` on `ℕ`): a net convergent along a general filter need not be pointwise bounded; the limit `f` is given as a linear map, so the statement is one conclusion (continuity).

### [CLEANUP-8] Run `/cleanup` on `BanachSteinhaus.lean`
- **Status**: done (2026-10-06) · **File**: `BanachSteinhaus.lean` · **Depends on**: T017 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 BanachSteinhaus.lean: 0 sorry, lines ≤ 100, runLinter passed, axioms standard
- **Description**: final per-file cleanup of `BanachSteinhaus.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T018] The bound for maps out of a finite free module
- **Status**: done (2026-10-06) · **File**: `Pi.lean` · **Depends on**: CLEANUP-2 · **Parallel**: yes (with G2, G3, G5) · **Type**: lemmas
- **Progress**: 2026-10-06 DONE — x = ∑ xᵢ • eᵢ via Pi.single_smul + Finset.univ_sum_single, then the ultrametric finite-sum bound
- **Leaves**: L6.1–L6.2

#### Statement
```lean
theorem norm_map_le_iSup_mul (f : (ι → R) →ₗ[R] M) (x : ι → R) :
    ‖f x‖ ≤ (⨆ i, ‖f (Pi.single i 1)‖) * ‖x‖ := by
  sorry

theorem continuous_pi (f : (ι → R) →ₗ[R] M) : Continuous f := by
  sorry
```
#### Proof sketch
1. `norm_map_le_iSup_mul`: write `x = ∑ i, x i • Pi.single i 1` (`Finset.univ_sum_single x` and
   `Pi.single_smul`/`smul_eq_mul`/`mul_one`, or `pi_eq_sum_univ` directly); `rw` it on the left only (`conv_lhs`),
   then `map_sum`, `map_smul`. Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` with
   `C := (⨆ i, ‖f (Pi.single i 1)‖) * ‖x‖` (`mul_nonneg (Real.iSup_nonneg fun _ ↦ norm_nonneg _) (norm_nonneg _)`);
   termwise `‖x i • f (Pi.single i 1)‖ ≤ ‖x i‖ * ‖f (Pi.single i 1)‖ ≤ ‖x‖ * ⨆ …`
   (`norm_smul_le`, `norm_le_pi_norm`, `le_ciSup (Set.finite_range _).bddAbove i`, `mul_le_mul`), then `mul_comm`.
2. `continuous_pi`: `AddMonoidHomClass.continuous_of_bound f _ (norm_map_le_iSup_mul f)`.

#### Mathlib lemmas needed
`Finset.univ_sum_single`, `Pi.single_smul`, `pi_eq_sum_univ`, `map_sum`, `map_smul`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `Real.iSup_nonneg`, `norm_smul_le`, `norm_le_pi_norm`, `le_ciSup`, `Set.finite_range`, `Set.Finite.bddAbove`, `mul_le_mul`, `AddMonoidHomClass.continuous_of_bound`.
#### Sources
[Sch] Prop 4.13 Step 1 `schneider.txt:909–913`; [BGR] 3.7.3/2 proof `bgr-3.7.md:57–59`; [RM] §1.2.5.
#### Generality decision
`[IsUltrametricDist M]` on the target (E17); no `NormOneClass`, no Tate hypothesis; `[DecidableEq ι]` because `Pi.single` needs it.

### [T019] The operator norm of a map out of a finite free module
- **Status**: done (2026-10-06) · **File**: `Pi.lean` · **Depends on**: T018 · **Parallel**: no · **Type**: lemma
- **Progress**: 2026-10-06 DONE — le_antisymm with ciSup_le and Pi.norm_single; empty ι by Real.iSup_of_isEmpty
- **Leaves**: L6.3

#### Statement
```lean
theorem opNorm_pi_eq [NormOneClass R] (u : (ι → R) →L[R] M) :
    ‖u‖ = ⨆ i, ‖u (Pi.single i 1)‖ := by
  sorry
```
#### Proof sketch
1. `refine le_antisymm (opNorm_le_bound _ (Real.iSup_nonneg fun _ ↦ norm_nonneg _) (norm_map_le_iSup_mul u)) ?_`.
2. `cases isEmpty_or_nonempty ι`: empty — `Real.iSup_of_isEmpty` and `opNorm_nonneg`; nonempty —
   `ciSup_le fun i ↦ ?_` with `‖u (Pi.single i 1)‖ ≤ ‖u‖ * ‖Pi.single i 1‖ = ‖u‖`
   (`le_opNorm_of_bound u ⟨_, norm_map_le_iSup_mul u⟩`, `Pi.norm_single`, `norm_one`, `mul_one`).

#### Mathlib lemmas needed
`Real.iSup_nonneg`, `Real.iSup_of_isEmpty`, `isEmpty_or_nonempty`, `ciSup_le`, `Pi.norm_single`, `norm_one`, `mul_one`.
#### Sources
[RM] §1.2.5 ("with norm the maximum of the norms of the images of the basis vectors").
#### Generality decision
`[NormOneClass R]` for `‖Pi.single i 1‖ = 1`; no `IsTate` (the bound of T018 feeds `le_opNorm_of_bound`).

### [CLEANUP-9] Run `/cleanup` on `Pi.lean`
- **Status**: done (2026-10-06) · **File**: `Pi.lean` · **Depends on**: T019 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 Pi.lean: 0 sorry, lines ≤ 100, runLinter passed, axioms standard
- **Description**: final per-file cleanup of `Pi.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T020] Buzzard's Lemma 2.2
- **Status**: done (2026-10-06) · **File**: `Finite.lean` · **Depends on**: CLEANUP-6, CLEANUP-9 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-06 DONE — Buzzard 2.2 as a bound: OMT on a surjection Fin n → R ↠ P plus the Pi bound for φ ∘ π
- **Leaves**: L7.1–L7.2

#### Statement
```lean
theorem exists_bound_of_finite (φ : P →ₗ[R] M) : ∃ C, ∀ x, ‖φ x‖ ≤ C * ‖x‖ := by
  sorry

theorem continuous_of_finite (φ : P →ₗ[R] M) : Continuous φ := by
  sorry
```
#### Proof sketch
1. `exists_bound_of_finite`: `obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R P`;
   `let πL : (Fin n → R) →L[R] P := ⟨π, continuous_pi π⟩` (ultrametric `P`);
   `obtain ⟨C, hC0, hC⟩ := exists_preimage_norm_le πL hπ` (`CompleteSpace (Fin n → R)` from `CompleteSpace R`);
   `refine ⟨(⨆ i, ‖(φ ∘ₗ π) (Pi.single i 1)‖) * C, fun p ↦ ?_⟩`; `obtain ⟨a, rfl, ha⟩ := hC p`;
   `‖φ (π a)‖ = ‖(φ ∘ₗ π) a‖ ≤ (⨆ …) * ‖a‖` (`norm_map_le_iSup_mul`, ultrametric `M`) `≤ (⨆ …) * (C * ‖p‖)`
   (`mul_le_mul_of_nonneg_left ha (Real.iSup_nonneg …)`), `mul_assoc`.
2. `continuous_of_finite`: `obtain ⟨C, hC⟩ := exists_bound_of_finite φ; exact AddMonoidHomClass.continuous_of_bound φ C hC`.

#### Mathlib lemmas needed
`Module.Finite.exists_fin'`, `LinearMap.comp_apply`, `Real.iSup_nonneg`, `mul_le_mul_of_nonneg_left`, `mul_assoc`, `AddMonoidHomClass.continuous_of_bound`; board: `continuous_pi`, `norm_map_le_iSup_mul`, `exists_preimage_norm_le`.
#### Sources
[Buz07] Lemma 2.2 `buzzard.txt:201–210`; [Lud] Lemma 2.14 `ludwig.txt:231–236`; [BGR] 3.7.3/2–3 `bgr-3.7.md:56–63` (uniqueness of the Banach norm is this lemma applied to the identity between two norms); [RM] §1.4.1.
#### Generality decision
No Noetherian hypothesis. `[IsUltrametricDist P]` for `continuous_pi π`, `[IsUltrametricDist M]` for the bound on `φ ∘ π` (added to the skeleton during the adversarial pass), `[CompleteSpace R]` for the domain of the open mapping theorem, `[CompleteSpace P]` for its codomain.

### [T021] The nonarchimedean Nakayama lemma for submodules
- **Status**: done (2026-10-06) · **File**: `Finite.lean` · **Depends on**: none (Layer 0 only) · **Parallel**: yes · **Type**: lemma
- **Progress**: 2026-10-06 DONE — RAG's ideal proof transported; M generalised to [AddCommGroup M] [Module R M] (the normed hypotheses were unused — a strict generalisation, all call sites unaffected) · 2026-10-06 RENAMED to NormedRing.forall_mem_of_forall_exists_eq_add_sum_smul_of_norm_lt_one (and T022's lemma to NormedRing.exists_forall_exists_eq_sum_smul_norm_le): the tauceti-rag-layer2 board's uncommitted BanachAlgebra/Module.lean declares field-scalar Submodule.* lemmas with the same names; theirs are special cases of these
- **Leaves**: L7.3

#### Statement
```lean
theorem NormedRing.forall_mem_of_forall_exists_eq_add_sum_smul_of_norm_lt_one (N : Submodule R M)
    {n : ℕ} (x : Fin n → M)
    (h : ∀ i, ∃ y ∈ N, ∃ c : Fin n → R, (∀ j, ‖c j‖ < 1) ∧ x i = y + ∑ j, c j • x j) :
    ∀ i, x i ∈ N := by
  sorry
```
#### Proof sketch
Transcribe [RAG] `Ideal.forall_mem_of_forall_exists_eq_add_sum_mul_of_norm_lt_one` (`RigidAnalyticGeometry/BanachAlgebra/Noetherian.lean:52–72`) from ideals to submodules:
1. `N' : Submodule (unitClosedBall R) M := Submodule.span _ (Set.range x)`;
   `N₀ : Submodule (unitClosedBall R) M := N.restrictScalars (unitClosedBall R)` (instances
   `Subsemiring.instModuleSubtypeMem`, `Submonoid.instIsScalarTowerSubtypeMem` — verified to synthesise).
2. `hle : N' ≤ N₀ ⊔ openUnitBallIdeal R • N'`: `Submodule.span_le.2`; `rintro _ ⟨i, rfl⟩`; `obtain ⟨y, hy, c, hc, hxi⟩ := h i`;
   `rw [SetLike.mem_coe, hxi]`; `Submodule.add_mem_sup hy (Submodule.sum_mem _ fun j _ ↦ ?_)`;
   `c j • x j = (⟨c j, mem_unitClosedBall.2 (hc j).le⟩ : unitClosedBall R) • x j` is `rfl`;
   `Submodule.smul_mem_smul (mem_openUnitBallIdeal.2 (hc j)) (Submodule.subset_span ⟨j, rfl⟩)`.
3. `Submodule.le_of_le_smul_of_le_jacobson_bot (Submodule.fg_span (Set.finite_range x)) openUnitBallIdeal_le_jacobson_bot hle`
   gives `N' ≤ N₀`; apply it to `Submodule.subset_span ⟨i, rfl⟩`.

#### Mathlib lemmas needed
`Submodule.span_le`, `SetLike.mem_coe`, `Submodule.add_mem_sup`, `Submodule.sum_mem`, `Submodule.smul_mem_smul`, `Submodule.subset_span`, `Submodule.fg_span`, `Set.finite_range`, `Submodule.le_of_le_smul_of_le_jacobson_bot`, `Submodule.restrictScalars`; Layer 0: `Subring.mem_unitClosedBall`, `NormedRing.mem_openUnitBallIdeal`, `NormedRing.openUnitBallIdeal_le_jacobson_bot`.
#### Sources
[BGR] 1.2.4/6 `bgr-3.7.md:142–150`; [RAG] the ideal case (sorry-free, same proof); [RM] §1.4.2 (seam S3: Mathlib's Nakayama replaces the matrix lemma).
#### Generality decision
`[NormedCommRing R] [NormOneClass R] [IsUltrametricDist R] [CompleteSpace R]` — the hypotheses of Layer 0's Jacobson-radical lemma; nothing on `M` beyond being a normed module (no completeness).

### [T022] Bounded coefficients on a closed finitely generated submodule
- **Status**: done (2026-10-06) · **File**: `Finite.lean` · **Depends on**: T020 · **Parallel**: no · **Type**: lemma
- **Progress**: 2026-10-06 DONE — OMT on Fin n → R ↠ J; omit [IsUltrametricDist R] (unused)
- **Leaves**: L7.4

#### Statement
```lean
theorem NormedRing.exists_forall_exists_eq_sum_smul_norm_le {n : ℕ} (x : Fin n → M)
    (J : Submodule R M) (hJ : IsClosed (J : Set M)) (hx : Submodule.span R (Set.range x) = J) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ J, ∃ a : Fin n → R, y = ∑ i, a i • x i ∧ ∀ i, ‖a i‖ ≤ C * ‖y‖ := by
  sorry
```
#### Proof sketch
Transcribe [RAG] `Ideal.exists_forall_exists_eq_sum_mul_norm_le` (`BanachAlgebra/Noetherian.lean:85–115`) over the Tate ring:
1. `hmem : ∀ a : Fin n → R, ∑ i, a i • x i ∈ J` (`J.sum_mem`, `J.smul_mem`, `hx ▸ Submodule.subset_span ⟨i, rfl⟩`).
2. `πl : (Fin n → R) →ₗ[R] J := { toFun := fun a ↦ ⟨∑ i, a i • x i, hmem a⟩, map_add' := …, map_smul' := … }`
   (`Subtype.ext`, `add_smul`, `Finset.sum_add_distrib`, `Finset.smul_sum`, `smul_smul`).
3. `haveI : CompleteSpace J := hJ.completeSpace_coe`; `πL : (Fin n → R) →L[R] J := ⟨πl, continuous_pi πl⟩`
   (`J` is ultrametric as a subtype of `M`).
4. Surjective: `rintro ⟨y, hy⟩`; `hx ▸ hy` and `Submodule.mem_span_range_iff_exists_fun.1`.
5. `obtain ⟨C, hC0, hC⟩ := exists_preimage_norm_le πL hsurj`; for `y ∈ J`, `obtain ⟨a, ha, hna⟩ := hC ⟨y, hy⟩`;
   `⟨a, (congrArg Subtype.val ha).symm, fun i ↦ (norm_le_pi_norm a i).trans hna⟩`.

#### Mathlib lemmas needed
`Submodule.sum_mem`, `Submodule.smul_mem`, `Submodule.subset_span`, `Subtype.ext`, `add_smul`, `Finset.sum_add_distrib`, `Finset.smul_sum`, `smul_smul`, `IsClosed.completeSpace_coe`, `Submodule.mem_span_range_iff_exists_fun`, `norm_le_pi_norm`, `congrArg`; board: `continuous_pi`, `exists_preimage_norm_le`.
#### Sources
[BGR] 3.7.2/1 proof `bgr-3.7.md:30–33` ("By BANACH's Theorem, `π` is open"); [RAG] the ideal case.
#### Generality decision
`[CompleteSpace M]` (for `J`), `[CompleteSpace R]` (for `Fin n → R`), ultrametric `M` (for `continuous_pi`); the constant is positive so that `C⁻¹` can be used in T023.

### [CLEANUP-10] Run `/cleanup` on `Finite.lean`
- **Status**: done (2026-10-06) · **File**: `Finite.lean` · **Depends on**: T022 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 merged with CLEANUP-11 (file proved in one pass)
- **Description**: after the 3rd proof ticket on `Finite.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [CLEANUP-ALL-2] Run `/cleanup-all` on the project
- **Status**: done (2026-10-06) · **File**: the project · **Depends on**: CLEANUP-10, CLEANUP-6, CLEANUP-7, CLEANUP-8, CLEANUP-9, CLEANUP-4 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 sweep: Norm, Banach, OpenMapping, ClosedGraph, BanachSteinhaus, Pi, Finite all sorry-free, lint clean, standard axioms, lines ≤ 100
- **Description**: pre-milestone sweep (`/cleanup-all` on all Layer 1 files so far) before M2. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T023] Closedness of submodules of finitely generated Banach modules (MILESTONE M2)
- **Status**: done (2026-10-06) · **File**: `Finite.lean` · **Depends on**: CLEANUP-ALL-2 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-06 DONE (MILESTONE M2) — BGR 3.7.2/1 via T021 + T022 with dist < C⁻¹; Noetherian corollary via isNoetherian_of_isNoetherianRing_of_finite
- **Leaves**: L7.5–L7.6

#### Statement
```lean
theorem Submodule.isClosed_of_fg_topologicalClosure (N : Submodule R M)
    (hfg : N.topologicalClosure.FG) : IsClosed (N : Set M) := by
  sorry

theorem Submodule.isClosed_of_isNoetherianRing [IsNoetherianRing R] [Module.Finite R M]
    (N : Submodule R M) : IsClosed (N : Set M) := by
  sorry
```
#### Proof sketch
1. `isClosed_of_fg_topologicalClosure`: transcribe [RAG] `Ideal.isClosed_of_fg_closure` (`Noetherian.lean:130–162`):
   `obtain ⟨n, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg`; `J := N.topologicalClosure`, closed by
   `Submodule.isClosed_topologicalClosure`; `obtain ⟨C, hC0, hC⟩ := NormedRing.exists_forall_exists_eq_sum_smul_norm_le x J hJ hx`;
   `hxN : ∀ i, x i ∈ N` by `NormedRing.forall_mem_of_forall_exists_eq_add_sum_smul_of_norm_lt_one N x fun i ↦ ?_`:
   `x i ∈ closure (N : Set M)` (`Submodule.topologicalClosure_coe`, `hx ▸ Submodule.subset_span ⟨i, rfl⟩`),
   `Metric.mem_closure_iff.1 … C⁻¹ (inv_pos.2 hC0)` gives `y ∈ N`, `dist (x i) y < C⁻¹`;
   `hC _ (J.sub_mem hxi (N.le_topologicalClosure hy))` gives `c` with `x i - y = ∑ j, c j • x j` and
   `‖c j‖ ≤ C * ‖x i - y‖ < C * C⁻¹ = 1`; rearrange to `x i = y + ∑ …` (`sub_eq_iff_eq_add'`/`abel`).
   Finish: `isClosed_of_closure_subset`: `closure N ⊆ J = span (range x) ≤ N` (`Submodule.span_le.2`).
2. `isClosed_of_isNoetherianRing`: `haveI := isNoetherian_of_isNoetherianRing_of_finite R M`;
   `exact N.isClosed_of_fg_topologicalClosure (IsNoetherian.noetherian _)`.

#### Mathlib lemmas needed
`Submodule.fg_iff_exists_fin_generating_family`, `Submodule.isClosed_topologicalClosure`, `Submodule.topologicalClosure_coe`, `Submodule.le_topologicalClosure`, `Submodule.subset_span`, `Submodule.span_le`, `Submodule.sub_mem`, `Metric.mem_closure_iff`, `dist_eq_norm`, `inv_pos`, `mul_lt_mul_of_pos_left`, `mul_inv_cancel₀`, `isClosed_of_closure_subset`, `isNoetherian_of_isNoetherianRing_of_finite`, `IsNoetherian.noetherian`.
#### Sources
[BGR] 3.7.2/1 `bgr-3.7.md:27–33` and `bgr-3.7.md:35–37`; [JN] `jn.txt:526–531`; Fresnel–van der Put Lemma 1.2.3 as cited by [RM] §1.4.2; [RAG] `Ideal.isClosed_of_fg_closure`, `Ideal.isClosed_of_isNoetherianRing`.
#### Generality decision
BGR 3.7.2/1 proper (`isClosed_of_fg_topologicalClosure`) has **no** Noetherian hypothesis; `isClosed_of_isNoetherianRing` adds `[IsNoetherianRing R] [Module.Finite R M]`. Each hypothesis is necessary (T029–T030 exhibit the failure without Noetherianity).

### [T024] Closed ideals and the Banach norm of a finitely generated module
- **Status**: done (2026-10-06) · **File**: `Finite.lean` · **Depends on**: T023 · **Parallel**: no · **Type**: theorems
- **Progress**: 2026-10-06 DONE — needed import Mathlib.Topology.MetricSpace.Ultra.Pi for IsUltrametricDist (Fin n → R)
- **Leaves**: L7.7–L7.8

#### Statement
```lean
theorem Ideal.isClosed_of_isTate_of_isNoetherianRing [IsNoetherianRing R] (I : Ideal R) :
    IsClosed (I : Set R) := by
  sorry

theorem Module.Finite.exists_surjective_isClosed_ker [IsNoetherianRing R] (P : Type*)
    [AddCommGroup P] [Module R P] [Module.Finite R P] :
    ∃ (n : ℕ) (π : (Fin n → R) →ₗ[R] P),
      Function.Surjective π ∧ IsClosed (LinearMap.ker π : Set (Fin n → R)) := by
  sorry
```
#### Proof sketch
1. `Ideal.isClosed_of_isTate_of_isNoetherianRing`: `Submodule.isClosed_of_isNoetherianRing (M := R) I`
   (`Module.Finite R R` is an instance).
2. `Module.Finite.exists_surjective_isClosed_ker`: `obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R P`;
   `exact ⟨n, π, hπ, Submodule.isClosed_of_isNoetherianRing (M := Fin n → R) (LinearMap.ker π)⟩`
   (`IsUltrametricDist (Fin n → R)` from `R`, `CompleteSpace (Fin n → R)`, `Module.Finite R (Fin n → R)` are instances).

#### Mathlib lemmas needed
`Module.Finite.exists_fin'`, `Module.Finite.self`, `Pi.instIsUltrametricDist`; board: `Submodule.isClosed_of_isNoetherianRing`.
#### Sources
[Buz07] `buzzard.txt:173`; [BGR] 3.7.2/2 `bgr-3.7.md:39`, 3.7.3/3 `bgr-3.7.md:60–63`; [RM] §1.4.1.
#### Generality decision
The ideal lemma's name avoids the in-chain field-scalar `Ideal.isClosed_of_isNoetherianRing` of `RigidAnalyticGeometry/BanachAlgebra/Noetherian.lean` (same chain root). `P` carries no norm: the statement produces the Banach structure.

### [CLEANUP-11] Run `/cleanup` on `Finite.lean`
- **Status**: done (2026-10-06) · **File**: `Finite.lean` · **Depends on**: T024 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 Finite.lean: 0 sorry, lines ≤ 100, runLinter passed, axioms standard
- **Description**: final per-file cleanup of `Finite.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T025] Multiplication by a ring element
- **Status**: done (2026-10-06) · **File**: `Examples.lean` · **Depends on**: CLEANUP-11, CLEANUP-4, CLEANUP-7, CLEANUP-8 · **Parallel**: no · **Type**: def + lemma
- **Progress**: 2026-10-06 DONE — _root_.norm_mul_le (NormedRing.norm_mul_le is ambiguous under open NormedRing)
- **Leaves**: L8.1

#### Statement
```lean
noncomputable def mulLeftL (a : R) : R →L[R] R :=
  (LinearMap.mulLeft R a).mkContinuous ‖a‖ fun x ↦ by sorry

theorem opNorm_mulLeftL (a : R) : ‖mulLeftL a‖ = ‖a‖ := by
  sorry
```
#### Proof sketch
1. The bound in `mulLeftL`: `fun x ↦ by rw [LinearMap.mulLeft_apply]; exact norm_mul_le a x`.
2. `opNorm_mulLeftL`: `le_antisymm (opNorm_le_bound _ (norm_nonneg a) fun x ↦ by simpa using norm_mul_le a x)`;
   for `≥`: `have h := le_opNorm_of_bound (mulLeftL a) ⟨‖a‖, fun x ↦ by simpa using norm_mul_le a x⟩ 1`;
   `simpa [mulLeftL_apply, norm_one] using h`.

#### Mathlib lemmas needed
`LinearMap.mulLeft_apply`, `norm_mul_le`, `norm_one`, `mul_one`.
#### Sources
[RM] Layer 1 Examples, corrected (erratum E10 in `plan.md`: `‖a‖ = ‖a · 1‖ ≤ ‖mulLeft a‖ ‖1‖`).
#### Generality decision
`[NormedCommRing R] [NormOneClass R]`, no Tate hypothesis: the example shows equality holds for every `a` as soon as `‖1‖ = 1`.

### [T026] The open mapping constant of `(x, y) ↦ x + ϖ y`
- **Status**: done (2026-10-06) · **File**: `Examples.lean` · **Depends on**: T025 · **Parallel**: no · **Type**: def + lemmas
- **Progress**: 2026-10-06 DONE — private norm_add_mul_le shared by the def's bound and the lower bound
- **Leaves**: L8.2–L8.4

#### Statement
```lean
noncomputable def addPseudoUniformizerSMul : R × R →L[R] R :=
  (LinearMap.fst R R R + (ϖ : R) • LinearMap.snd R R R).mkContinuous 1 fun m ↦ by sorry

theorem exists_preimage_norm_le_addPseudoUniformizerSMul (n : R) :
    ∃ m : R × R, addPseudoUniformizerSMul ϖ m = n ∧ ‖m‖ ≤ 1 * ‖n‖ := by
  sorry

theorem one_le_of_forall_exists_preimage_norm_le_addPseudoUniformizerSMul {C : ℝ}
    (hC : ∀ n : R, ∃ m : R × R, addPseudoUniformizerSMul ϖ m = n ∧ ‖m‖ ≤ C * ‖n‖) : 1 ≤ C := by
  sorry
```
#### Proof sketch
1. The bound `1` in `addPseudoUniformizerSMul`: `‖m.1 + ϖ * m.2‖ ≤ max ‖m.1‖ (‖ϖ‖ * ‖m.2‖) ≤ max ‖m.1‖ ‖m.2‖ = ‖m‖`
   (`LinearMap.add_apply`, `LinearMap.smul_apply`, `smul_eq_mul`, `IsUltrametricDist.norm_add_le_max`,
   `ϖ.isMultiplicative.norm_mul`, `mul_le_of_le_one_left (norm_nonneg _) ϖ.norm_lt_one.le`, `Prod.norm_def`, `one_mul`).
2. `exists_preimage_norm_le_addPseudoUniformizerSMul`: `⟨(n, 0), by simp, by simp [Prod.norm_def]⟩`.
3. `one_le_of_forall_exists_preimage_norm_le_addPseudoUniformizerSMul`: `obtain ⟨m, hm, hle⟩ := hC 1`;
   `calc 1 = ‖(1 : R)‖ := norm_one.symm; _ = ‖addPseudoUniformizerSMul ϖ m‖ := by rw [hm]; _ ≤ ‖m‖ := (step 1's bound);
   _ ≤ C * ‖(1 : R)‖ := hle; _ = C := by rw [norm_one, mul_one]`.

#### Mathlib lemmas needed
`LinearMap.add_apply`, `LinearMap.smul_apply`, `smul_eq_mul`, `IsUltrametricDist.norm_add_le_max`, `mul_le_of_le_one_left`, `Prod.norm_def`, `norm_fst_le`, `norm_snd_le`, `norm_one`, `mul_one`; Layer 0: `NormedRing.IsMultiplicative.norm_mul`, `PseudoUniformizer.norm_lt_one`.
#### Sources
[RM] Layer 1 Examples ("the open mapping constant for the quotient map `R ² → R`, `(x, y) ↦ x + ϖ y`").
#### Generality decision
`[IsUltrametricDist R]` for the constant `1`; `[NormOneClass R]` for the lower bound; explicit `ϖ`.

### [T027] A continuous bijection whose inverse has norm `p`
- **Status**: done (2026-10-06) · **File**: `Examples.lean` · **Depends on**: T026 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-10-06 DONE — Mathlib's norm_smul + ContinuousLinearMap.norm_id
- **Leaves**: L8.5–L8.6

#### Statement
```lean
theorem bijective_padic_smul_id :
    Function.Bijective ((p : ℚ_[p]) • ContinuousLinearMap.id ℚ_[p] ℚ_[p]) := by
  sorry

theorem norm_padic_inv_smul_id : ‖(p : ℚ_[p])⁻¹ • ContinuousLinearMap.id ℚ_[p] ℚ_[p]‖ = p := by
  sorry
```
#### Proof sketch
These two use Mathlib's field-scalar instances on `ℚ_[p] →L[ℚ_[p]] ℚ_[p]` (do not open the scope in this section).
1. `bijective_padic_smul_id`: `hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero`;
   `Function.bijective_iff_has_inverse.2 ⟨fun y ↦ (p : ℚ_[p])⁻¹ * y, fun x ↦ by simp [hp0], fun y ↦ by simp [hp0]⟩`
   (`ContinuousLinearMap.smul_apply`, `ContinuousLinearMap.id_apply`, `smul_eq_mul`, `inv_mul_cancel_left₀`).
2. `norm_padic_inv_smul_id`: `rw [norm_smul, norm_inv, Padic.norm_p, inv_inv, ContinuousLinearMap.norm_id, mul_one]`;
   if the `NontrivialTopology ℚ_[p]` instance behind `norm_id` is not found, prove `‖id‖ = 1` with
   `ContinuousLinearMap.opNorm_eq_of_bounds` (bound `1`, and `‖id 1‖ = 1`).

#### Mathlib lemmas needed
`Function.bijective_iff_has_inverse`, `Nat.cast_ne_zero`, `inv_mul_cancel_left₀`, `mul_inv_cancel_left₀`, `norm_smul`, `norm_inv`, `Padic.norm_p`, `inv_inv`, `ContinuousLinearMap.norm_id`, `ContinuousLinearMap.opNorm_eq_of_bounds`.
#### Sources
[RM] Layer 1 Examples ("a continuous bijection of Banach `ℚ_p`-spaces whose inverse has norm `p`"); the scoped norm agrees by `norm_eq_opNorm`.
#### Generality decision
Field scalars, Mathlib's norm; the example is also a sanity check of §1.1.6.

### [CLEANUP-12] Run `/cleanup` on `Examples.lean`
- **Status**: done (2026-10-06) · **File**: `Examples.lean` · **Depends on**: T027 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 merged with CLEANUP-13
- **Description**: after the 3rd proof ticket on `Examples.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T028] `ℤ_p` with the squared norm: continuous, unbounded
- **Status**: done (2026-10-06) · **File**: `Examples.lean` · **Depends on**: CLEANUP-12 · **Parallel**: no · **Type**: instances + lemmas
- **Progress**: 2026-10-06 DONE — squared norm ultrametric by cases on le_total; unbounded via pow_unbounded_of_one_lt
- **Leaves**: L8.7–L8.11

#### Statement
```lean
noncomputable instance : NormedAddCommGroup (PadicIntSq p) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun x ↦ ‖((toPadicIntSq p).symm x : ℤ_[p])‖ ^ 2
      map_zero' := by sorry
      add_le' := by sorry
      neg' := by sorry
      eq_zero_of_map_eq_zero' := by sorry }

instance : IsBoundedSMul ℤ_[p] (PadicIntSq p) := by
  sorry

instance : IsUltrametricDist (PadicIntSq p) := by
  sorry

theorem continuous_symm_toPadicIntSq : Continuous (toPadicIntSq p).symm := by
  sorry

theorem not_exists_bound_symm_toPadicIntSq :
    ¬ ∃ C : ℝ, ∀ x : PadicIntSq p, ‖(toPadicIntSq p).symm x‖ ≤ C * ‖x‖ := by
  sorry
```
#### Proof sketch
Throughout, `(toPadicIntSq p).symm x` is definitionally `x` as an element of `ℤ_[p]`; `norm_def` unfolds `‖x‖`.
1. Norm fields: `map_zero'`: `norm_zero`, `zero_pow two_ne_zero`; `add_le'`: `pow_le_pow_left (norm_nonneg _)
   (IsUltrametricDist.norm_add_le_max _ _) 2`, then `max_pow`-style `(max a b) ^ 2 = max (a ^ 2) (b ^ 2)`
   (`Monotone.map_max (pow_left_mono 2)`) and `max_le_add_of_nonneg`; `neg'`: `norm_neg`;
   `eq_zero_of_map_eq_zero'`: `pow_eq_zero_iff two_ne_zero`, `norm_eq_zero`.
2. `IsBoundedSMul`: `IsBoundedSMul.of_norm_smul_le fun r x ↦ ?_`: `‖r • x‖ = (‖r‖ * ‖x‖) ^ 2 = ‖r‖ ^ 2 * ‖x‖ ^ 2 ≤ ‖r‖ * ‖x‖ ^ 2`
   (`norm_def`, `smul_eq_mul`, `PadicInt.norm_mul` / `norm_mul`, `mul_pow`, `pow_le_of_le_one (norm_nonneg r) (PadicInt.norm_le_one r) two_ne_zero`).
3. `IsUltrametricDist`: `isUltrametricDist_of_isNonarchimedean_norm` with the `max` computation of step 1.
4. `continuous_symm_toPadicIntSq`: `Metric.continuous_iff.2 fun x ε hε ↦ ⟨ε ^ 2, by positivity, fun y hy ↦ ?_⟩`;
   `dist y x = ‖y - x‖ ^ 2 < ε ^ 2` gives `‖y - x‖ < ε` (`pow_lt_pow_iff_left₀`, `abs_lt_abs`-free: use
   `lt_of_pow_lt_pow_left₀ 2 hε.le`).
5. `not_exists_bound_symm_toPadicIntSq`: `rintro ⟨C, hC⟩`; `obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (Nat.one_lt_cast.2 hp.out.one_lt)`;
   `have := hC (toPadicIntSq p (p ^ n))`; `rw [norm_def, PadicInt.norm_p_pow, …]` to get `(p : ℝ) ^ (-n : ℤ) ≤ C * ((p : ℝ) ^ (-n : ℤ)) ^ 2`;
   multiply by `(p : ℝ) ^ (2 n) > 0` (`zpow_neg`, `zpow_natCast`, `inv_pow`) to get `p ^ n ≤ C`, contradicting `hn`.

#### Mathlib lemmas needed
`norm_zero`, `zero_pow`, `pow_le_pow_left`, `Monotone.map_max`, `pow_left_mono`, `max_le_add_of_nonneg`, `norm_neg`, `pow_eq_zero_iff`, `norm_eq_zero`, `IsBoundedSMul.of_norm_smul_le`, `norm_mul`, `mul_pow`, `pow_le_of_le_one`, `PadicInt.norm_le_one`, `IsUltrametricDist.norm_add_le_max`, `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`, `Metric.continuous_iff`, `dist_eq_norm`, `lt_of_pow_lt_pow_left₀`, `pow_unbounded_of_one_lt`, `Nat.one_lt_cast`, `PadicInt.norm_p_pow`, `zpow_neg`, `zpow_natCast`, `inv_pow`, `le_div_iff₀`.
#### Sources
[RM] §1.1.2 ("the identity map from `ℤ_p` with the norm `‖x‖²` (a normed `ℤ_p`-module) to `ℤ_p` with its norm is continuous and unbounded. The Tate hypothesis is exactly what is needed"); Layer 0 `not_isTate_padicInt`.
#### Generality decision
The scalars are `ℤ_p` (not `ℚ_p`): `‖r‖ ≤ 1` is what makes the squared norm a module norm; the synonym carries `toPadicIntSq` as its only interface.

### [T029] A non-closed principal ideal of `ℓ^∞(ℕ, ℚ_p)`
- **Status**: done (2026-10-06) · **File**: `Examples.lean` · **Depends on**: T028 · **Parallel**: no · **Type**: instance + def + theorem
- **Progress**: 2026-10-06 DONE — c = (p^⌊n/2⌋) in the closure (truncations b_N, bounded by p^(2N)), not in the ideal (‖b(2k)‖ = p^k unbounded)
- **Leaves**: L8.12–L8.14

#### Statement
```lean
instance lp.instIsUltrametricDist {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, IsUltrametricDist (E i)] : IsUltrametricDist (lp E ∞) := by
  sorry

noncomputable def padicGeomSeq : lp (fun _ : ℕ ↦ ℚ_[p]) ∞ :=
  ⟨fun n ↦ (p : ℚ_[p]) ^ n, memℓp_infty ⟨1, by sorry⟩⟩

theorem not_isClosed_span_padicGeomSeq :
    ¬ IsClosed ((Ideal.span {padicGeomSeq p} : Ideal (lp (fun _ : ℕ ↦ ℚ_[p]) ∞)) :
      Set (lp (fun _ : ℕ ↦ ℚ_[p]) ∞)) := by
  sorry
```
#### Proof sketch
1. `lp.instIsUltrametricDist`: `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun f g ↦
   lp.norm_le_of_forall_le (le_max_of_le_left (norm_nonneg f)) fun i ↦ ?_`; `rw [lp.coeFn_add, Pi.add_apply]`;
   `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (lp.norm_apply_le_norm top_ne_zero f i) (lp.norm_apply_le_norm top_ne_zero g i))`.
2. `padicGeomSeq` bounded: `rintro _ ⟨n, rfl⟩; exact (norm_pow_le' _ …).trans (pow_le_one₀ (norm_nonneg _) Padic.norm_p_lt_one.le)`
   (or `Padic.norm_p_pow` with `zpow_le_one_of_nonpos₀`).
3. `not_isClosed_span_padicGeomSeq`: set `S := (Ideal.span {padicGeomSeq p} : Set _)`,
   `c : lp (fun _ : ℕ ↦ ℚ_[p]) ∞ := ⟨fun n ↦ (p : ℚ_[p]) ^ (n / 2), memℓp_infty ⟨1, …⟩⟩`.
   (i) `c ∈ closure S` (`Metric.mem_closure_iff`): given `ε > 0`, `obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 hp.out.one_lt))`
   for `(p : ℝ)⁻¹ ^ N < ε`; `b : lp _ ∞ := ⟨fun n ↦ if n < 2 * N then (p : ℚ_[p]) ^ (n / 2) * ((p : ℚ_[p]) ^ n)⁻¹ else 0, bounded (finitely many nonzero)⟩`;
   `b * padicGeomSeq p ∈ S` by `Ideal.mem_span_singleton'.2 ⟨b, rfl⟩`; `dist c (b * a) = ‖c - b * a‖ ≤ (p : ℝ)⁻¹ ^ N < ε`
   by `lp.norm_le_of_forall_le`: coordinate `n`: `lp.coeFn_sub`, `lp.infty_coeFn_mul`, `Pi.mul_apply`; for `n < 2N`
   the coordinate is `0` (`inv_mul_cancel_right₀`); for `n ≥ 2N` it is `p ^ (n / 2)` of norm `(p⁻¹) ^ (n / 2) ≤ (p⁻¹) ^ N`
   (`Padic.norm_p_pow`, `pow_le_pow_of_le_one`, `Nat.le_div_iff_mul_le`).
   (ii) `c ∉ S`: `rintro h`; `obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h`; coordinatewise
   `b n * p ^ n = p ^ (n / 2)` (`congrFun (congrArg Subtype.val hb) n`, `lp.infty_coeFn_mul`); at `n = 2k`:
   `b (2k) = p ^ k * (p ^ (2k))⁻¹` has norm `(p : ℝ) ^ k` (`norm_mul`, `norm_inv`, `Padic.norm_p_pow`, `zpow_neg`,
   `Nat.mul_div_cancel_left`); `lp.norm_apply_le_norm top_ne_zero b (2 * k)` gives `(p : ℝ) ^ k ≤ ‖b‖` for every `k`,
   against `pow_unbounded_of_one_lt ‖b‖ (Nat.one_lt_cast.2 hp.out.one_lt)`.
   Conclude: `fun hS ↦ (hS.closure_eq ▸ hc_closure : c ∈ S)` contradicts (ii).

#### Mathlib lemmas needed
`IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`, `lp.norm_le_of_forall_le`, `lp.norm_apply_le_norm`, `lp.coeFn_add`, `lp.coeFn_sub`, `lp.infty_coeFn_mul`, `memℓp_infty`, `norm_pow_le'`, `pow_le_one₀`, `Padic.norm_p_lt_one`, `Padic.norm_p_pow`, `Metric.mem_closure_iff`, `exists_pow_lt_of_lt_one`, `inv_lt_one_of_one_lt₀`, `Nat.one_lt_cast`, `Ideal.mem_span_singleton'`, `inv_mul_cancel_right₀`, `pow_le_pow_of_le_one`, `Nat.le_div_iff_mul_le`, `Nat.mul_div_cancel_left`, `norm_mul`, `norm_inv`, `zpow_neg`, `pow_unbounded_of_one_lt`, `IsClosed.closure_eq`, `top_ne_zero`.
#### Sources
[RM] §1.4.3 ("Not every finitely generated submodule of a Banach module is closed. Record a counterexample over a non-Noetherian Banach–Tate ring"); [Lud] Remark 2.25 `ludwig.txt:351–358` (Bellaïche's Hypothesis 3.1.8); erratum E18 in `plan.md` (the example is the planner's).
#### Generality decision
The `lp` ultrametric instance is stated for every family `E` (§2.5 will reuse it); the counterexample is a *principal* ideal, the strongest form; `p` arbitrary.

### [T030] `ℓ^∞(ℕ, ℚ_p)` is not Noetherian
- **Status**: done (2026-10-06) · **File**: `Examples.lean` · **Depends on**: T029 · **Parallel**: no · **Type**: theorem
- **Progress**: 2026-10-06 DONE — M2 applied to ℓ^∞ with IsTate from isTate_of_normedAlgebra ℚ_[p]
- **Leaves**: L8.15

#### Statement
```lean
theorem not_isNoetherianRing_lp_infty : ¬ IsNoetherianRing (lp (fun _ : ℕ ↦ ℚ_[p]) ∞) := by
  sorry
```
#### Proof sketch
1. `intro h`; `haveI : NormedRing.IsTate (lp (fun _ : ℕ ↦ ℚ_[p]) ∞) := NormedRing.isTate_of_normedAlgebra ℚ_[p] _`
   (`lp.inftyNormedAlgebra`, `NormOneClass` from `Nonempty ℕ`).
2. `exact not_isClosed_span_padicGeomSeq p (Submodule.isClosed_of_isNoetherianRing (R := lp _ ∞) (M := lp _ ∞) _)`
   — the remaining instances (`NormedCommRing`, ultrametric from T029, `CompleteSpace`, `IsBoundedSMul R R`,
   `Module.Finite R R`) are found by unification; `haveI` any that is not.

#### Mathlib lemmas needed
`lp.inftyNormedCommRing`, `lp.inftyNormedAlgebra`, `Module.Finite.self`; Layer 0: `NormedRing.isTate_of_normedAlgebra`; board: `Submodule.isClosed_of_isNoetherianRing`, `not_isClosed_span_padicGeomSeq`.
#### Sources
[RM] §1.4.3 ("a non-Noetherian Banach–Tate ring"); [Buz07] `buzzard.txt:173` (closed ideals ⇔ Noetherian).
#### Generality decision
This is M2 read backwards: every hypothesis of `Submodule.isClosed_of_isNoetherianRing` except Noetherianity holds for `ℓ^∞(ℕ, ℚ_p)`.

### [CLEANUP-13] Run `/cleanup` on `Examples.lean`
- **Status**: done (2026-10-06) · **File**: `Examples.lean` · **Depends on**: T030 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 Examples.lean: 0 sorry, lines ≤ 100, runLinter passed, 19 decls standard axioms
- **Description**: final per-file cleanup of `Examples.lean`. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).

### [T031] Add Layer 1 to the chain root
- **Status**: done (2026-10-06) · **File**: `PhD/TauCeti.lean` · **Depends on**: CLEANUP-13 · **Parallel**: no · **Type**: integration
- **Progress**: 2026-10-06 DONE — root imports Operator.Examples; lake build PhD.TauCeti: 3619 jobs, 0 errors; 0 sorry in Operator/; 85 named decls standard axioms
- **Leaves**: —

#### Statement
```lean
(no Lean declaration — an edit of `PhD/TauCeti.lean`)
```
#### Proof sketch
1. Append `import PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.Examples` to `PhD/TauCeti.lean`, in alphabetical
   position after `PhD.TauCeti.Code.PadicFunctionalAnalysis.NormComparison` (append-only edit; another board may be
   editing the file — re-read it first).
2. `lake build PhD.TauCeti` must succeed; then `#print axioms` on `exists_preimage_norm_le`,
   `Submodule.isClosed_of_isNoetherianRing`, `instNormedAddCommGroup_eq`, `not_isNoetherianRing_lp_infty`
   (only `propext`, `Classical.choice`, `Quot.sound`), and `grep -c sorry` over `Operator/` must be `0`.
3. Record the completion line in this board's header and in `plan.md`.

#### Mathlib lemmas needed
—
#### Sources
[RM] "Existing Lean work" (the chain root lists leaf modules only).
#### Generality decision
—

### [CLEANUP-FINAL] Run `/cleanup-all` on the project
- **Status**: done (2026-10-06) · **File**: the project · **Depends on**: T031 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-10-06 all eight Operator files: runLinter passed (one batch), 0 sorry, 0 lines > 100, standard axioms, no PhD.Main imports
- **Description**: final `/cleanup-all` of the whole Layer 1 (per-file `runLinter`, no `sorry`, standard axioms). Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).
