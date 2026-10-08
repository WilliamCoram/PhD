# Ticket Board — Tau Ceti OverconvergentForms Layer 1 (weights and weight modules)

Board: `.mathlib-quality/tauceti-of-layer1/` (named — always pass the path). Companion files:
`plan.md` (goal, decisions D1–D12, errata E1–E6, the FLOOR-PENDING scope boundary), `decomposition.md`
(the leaves, sources, attack logs; the ticket sketches below are copied from it). Code:
`PhD/TauCeti/Code/OverconvergentForms/Weight/`. Build one module at a time with
`~/.elan/bin/lake build PhD.TauCeti.Code.OverconvergentForms.Weight.<Module>`; never `lake build PhD`;
never `import PhD.Main.*`; one Lean process on this machine at a time. The chain root `PhD/TauCeti.lean`
is touched only by T050.

Generated 2026-10-06 from the skeleton (every Statement block is the verbatim Lean of the
skeleton at generation time; line numbers are not recorded because they move).

## Summary

- Total: 75 tickets
- Proof/definition tickets: 50 (T001–T050; milestone tickets: T021, T022 = M1; T028 = M2; T033, T034 = M3; T044, T048 = M4; T025, T050 = M5)
- Cleanup tickets: 25 (20 per-file: one after every third proof ticket on a file plus one final per file; 4 `CLEANUP-ALL` before the milestones M1, M3, M4, M5; 1 `CLEANUP-FINAL`)
- Open: 75 | In Progress: 0 | Done: 0
- Parallel capacity: 1 worker (one Lean process per machine); the dependency graph allows 3 (Level/Dictionary, Mobius→Identity, Mobius→Action) if a second machine is available.

## Dependency order

```text
Level: T001 → T002 → T003 → CLEANUP-1 → T004 → T005 → CLEANUP-2 → Dictionary: T006 → CLEANUP-3
Mobius: T007 → T008 → T009 → CLEANUP-4 → T010 → T011 → T012 → CLEANUP-5 → T013 → CLEANUP-6
Identity (after T007): T014 → T015 → T016 → CLEANUP-7 → T017 → T018 → T019 → CLEANUP-8
Action (after T013): T020 → CLEANUP-ALL-1 → T021 (M1) → T022 (M1) → CLEANUP-9 → T023 → T024 → T025 (M5a) → CLEANUP-10
Expansion (after T019, T022): T026 → T027 → T028 (M2) → CLEANUP-11 → T029 → T030 → T031 → CLEANUP-12 → T032
          → CLEANUP-ALL-2 → T033 (M3) → T034 (M3) → CLEANUP-13 → T035 → CLEANUP-14
Algebraic: T036 → T037 → T038 → CLEANUP-15 → T039 → T040 → T041 → CLEANUP-16
Classical: T042 → T043 → T044 (M4a) → CLEANUP-17 → T045 → T046 → T047 → CLEANUP-18 → CLEANUP-ALL-3 → T048 (M4) → CLEANUP-19
Examples: T049 → CLEANUP-20 → CLEANUP-ALL-4 → T050 (M5) → CLEANUP-FINAL
```

## Working rules (binding for `/beastmode`)

1. A ticket is done when every `sorry` of its declarations is gone, the module builds with no warning
   for those declarations, and `#print axioms` of the ticket's theorems shows only `propext`,
   `Classical.choice`, `Quot.sound` (a failing tactic can leave a `sorry` *without* an `error` line —
   gate on `uses 'sorry'` too).
2. Statements are fixed. If a statement is wrong (B2), repair it in place only when the repair is
   source-faithful and the sole consumer is unaffected, log it in `b2_log.jsonl`, and say so in the
   Progress block; otherwise stop and report.
3. Cross the `Restricted` subtype seam with term steps (`exact`, `congrArg`, `.trans`), never `rw`
   (memory note `restricted-seam-convention`); keep `Restricted` opaque.
4. No `import PhD.Main.*`. The [SRC] files are read-only reference.
5. After finishing a ticket, append a `#### Progress` block to it (date, what was proved, traps met).

## Tickets


### [T001] `det_adjugate_fin_two`, `adjugate_adjugate_fin_two`, `SigmaNorm` and 1 more

- **Status**: done   (finished 2026-10-06T19:58) · **File**: `Level.lean` · **Depends on**: none · **Type**: proof · **Leaves**: L1.1, L1.2

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- In dimension `2` the adjugate preserves the determinant. -/
theorem det_adjugate_fin_two (A : Matrix (Fin 2) (Fin 2) R) : (adjugate A).det = A.det := by
  sorry

/-- In dimension `2` the adjugate is an involution. -/
theorem adjugate_adjugate_fin_two (A : Matrix (Fin 2) (Fin 2) R) : adjugate (adjugate A) = A := by
  sorry

/-- **The norm-form level monoid** `Σ(ρ)`: integral entries, `‖c‖ ≤ ρ`, `‖d‖ = 1`, nonzero
determinant. Source: [Buz07, §9, p. 68]; [Jac03, Definition 1.27]. -/
def SigmaNorm (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) : Submonoid (Matrix (Fin 2) (Fin 2) L) where
  carrier := {g | (∀ i j, ‖g i j‖ ≤ 1) ∧ ‖g 1 0‖ ≤ ρ ∧ ‖g 1 1‖ = 1 ∧ g.det ≠ 0}
  one_mem' := by
    sorry
  mul_mem' := by
    sorry

theorem mem_sigmaNorm_iff {ρ : ℝ} {hρ0 : 0 ≤ ρ} {hρ : ρ < 1} {g : Matrix (Fin 2) (Fin 2) L} :
    g ∈ SigmaNorm L ρ hρ0 hρ ↔
      (∀ i j, ‖g i j‖ ≤ 1) ∧ ‖g 1 0‖ ≤ ρ ∧ ‖g 1 1‖ = 1 ∧ g.det ≠ 0 :=
  Iff.rfl
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L1.1** `Matrix.det_adjugate_fin_two`, `Matrix.adjugate_adjugate_fin_two` — [RM] §1.1.4
  "`adj` […] involutive in dimension `2`, determinant-preserving". Lean: `(adjugate A).det = A.det`,
  `adjugate (adjugate A) = A` for `A : Matrix (Fin 2) (Fin 2) R`, `R` a commutative ring. Discharge:
  `Matrix.det_adjugate` ✓ (`= A.det ^ (Fintype.card n − 1)`, `card (Fin 2) − 1 = 1`, `pow_one`);
  `Matrix.adjugate_adjugate` ✓ (`h : Fintype.card n ≠ 1`, gives `det A ^ (card − 2) • A`, `pow_zero`,
  `one_smul`). Attacks: [2] `A = 0`: `adj 0 = 0` in dimension `2` ✓ both sides `0`; `A = 1` ✓. [3] no
  hypotheses beyond `CommRing`; the roadmap says "in dimension 2", and indeed `adj (adj A) = A` fails
  in dimension `3` (`det A • A`), so the `Fin 2` specialisation is necessary ✓. [5] both Mathlib names
  grep'd at the pin ✓; composition of two lemmas each ✓. SURVIVED.

- **L1.2** `SigmaNorm` (fields `one_mem'`, `mul_mem'`), `mem_sigmaNorm_iff` — [RM] §1.1.1 "For
  `0 ≤ ρ < 1` define `SigmaNorm F_𝔭 ρ := {γ ∈ M₂(F_𝔭) | ‖γ_{ij}‖ ≤ 1, ‖c‖ ≤ ρ, ‖d‖ = 1, det γ ≠ 0}`, a
  submonoid of `M₂(F_𝔭)` (the products preserve the three bounds because `‖d‖ = 1` absorbs the
  cross terms)". Sketch: substrate, *the monoid law*. Discharge: `Matrix.mul_apply` ✓,
  `Fin.sum_univ_two` ✓, `IsUltrametricDist.norm_add_le_max` ✓, `norm_mul_le`/`norm_mul` (field),
  `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` ✓, `Matrix.det_mul` ✓, `Matrix.one_apply` ✓.
  [SRC] `QMF/Weight/00_Series.SigmaNorm` has this exact proof. Attacks: [2] `ρ = 0`: the monoid of
  upper-triangular integral matrices with unit `d` ✓ still a monoid. [3] `ρ < 1` is necessary for
  `mul_mem'`: at `ρ = 1`, `((0 1), (1 1))` and `((1 1), (1 −1))` satisfy the conditions and their
  product has lower-right entry `0` (Layer 0's L11.1 counterexample) ✓; `0 ≤ ρ` is necessary for
  `one_mem'` ✓. [4] the four conditions are [Jac03]'s with `p^α ∣ c ↦ ‖c‖ ≤ ρ`, `p ∤ d ↦ ‖d‖ = 1` ✓.
  SURVIVED.

#### Mathlib lemmas needed

`Matrix.det_adjugate`, `Matrix.adjugate_adjugate`, `Matrix.mul_apply`, `Fin.sum_univ_two`, `IsUltrametricDist.norm_add_le_max`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, `Matrix.det_mul`, `Matrix.one_apply`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.1.1–§1.1.4; [Buz07, §9, p. 68]; [Jac03, Definition 1.27]; [SRC] `QMF/Weight/00_Series.lean`, `QMF/Slash/01_Sigma0.lean`, `QMF/Weight/04_AdicLevel.lean` (proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D8** namespace `AutomorphicForm`; Tate-algebra seams in `MvPowerSeries.Restricted` / `PowerSeries.Restricted` / `Matrix`; **D9** `SigmaNorm L ρ hρ0 hρ` with explicit real hypotheses; `LevelBounds S ρ` bundles them with the four conditions.

#### Progress

- 2026-10-06T19:58: DONE. `det_adjugate_fin_two` by `det_adjugate` + simp; `adjugate_adjugate_fin_two` by `adjugate_adjugate A (by simp)` + simp; `SigmaNorm` monoid law transcribed from [SRC] (isosceles on the `d`-entry). Module builds, no warning, axioms std (propext, Classical.choice, Quot.sound).

### [T002] `LevelBounds`, `levelBounds_sigmaNorm`, `mono` and 6 more

- **Status**: done   (finished 2026-10-06T19:58) · **File**: `Level.lean` · **Depends on**: [T001] · **Type**: proof · **Leaves**: L1.3, L1.4

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- **The level bounds** of a submonoid `S ⊆ M₂(L)` at radius `ρ`: every member has integral
entries, `‖c‖ ≤ ρ`, `‖d‖ = 1` and nonzero determinant, and `0 ≤ ρ < 1`. Equivalently
`S ≤ SigmaNorm L ρ`. Source: roadmap §1.1.1. -/
structure LevelBounds (S : Submonoid (Matrix (Fin 2) (Fin 2) L)) (ρ : ℝ) : Prop where
  rho_nonneg : 0 ≤ ρ
  rho_lt_one : ρ < 1
  integral : ∀ {g}, g ∈ S → ∀ i j, ‖g i j‖ ≤ 1
  c_le : ∀ {g}, g ∈ S → ‖g 1 0‖ ≤ ρ
  d_unit : ∀ {g}, g ∈ S → ‖g 1 1‖ = 1
  det_ne_zero : ∀ {g}, g ∈ S → g.det ≠ 0

theorem levelBounds_sigmaNorm (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) : LevelBounds (SigmaNorm L ρ hρ0 hρ) ρ := by
  sorry

theorem LevelBounds.mono {T : Submonoid (Matrix (Fin 2) (Fin 2) L)} (hb : LevelBounds T ρ)
    (hST : S ≤ T) : LevelBounds S ρ := by
  sorry

/-- Level bounds at `ρ` are level bounds at every `ρ ≤ ρ' < 1`. -/
theorem LevelBounds.mono_radius (hb : LevelBounds S ρ) {ρ' : ℝ} (hρρ' : ρ ≤ ρ') (hρ' : ρ' < 1) :
    LevelBounds S ρ' := by
  sorry

theorem LevelBounds.le_sigmaNorm (hb : LevelBounds S ρ) :
    S ≤ SigmaNorm L ρ hb.rho_nonneg hb.rho_lt_one := by
  sorry

theorem LevelBounds.of_le (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) (h : S ≤ SigmaNorm L ρ hρ0 hρ) :
    LevelBounds S ρ := by
  sorry

theorem LevelBounds.d_ne_zero (hb : LevelBounds S ρ) {g : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S) :
    g 1 1 ≠ 0 := by
  sorry

theorem LevelBounds.norm_det_le_one (hb : LevelBounds S ρ) {g : Matrix (Fin 2) (Fin 2) L}
    (hg : g ∈ S) : ‖g.det‖ ≤ 1 := by
  sorry

/-- On a level, `c z + d` is a unit of the valuation ring for every `z` in the closed unit ball:
`‖c z + d‖ = 1`. Source: roadmap §1.2.2 ("`c z + d ∈ 𝒪^×` because `‖c‖ < 1 = ‖d‖`"). -/
theorem LevelBounds.norm_mul_add_eq_one (hb : LevelBounds S ρ) {g : Matrix (Fin 2) (Fin 2) L}
    (hg : g ∈ S) {z : L} (hz : ‖z‖ ≤ 1) : ‖g 1 0 * z + g 1 1‖ = 1 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L1.3** `LevelBounds` (structure, six fields), `levelBounds_sigmaNorm`, `LevelBounds.mono`,
  `LevelBounds.mono_radius`, `LevelBounds.le_sigmaNorm`, `LevelBounds.of_le` — [RM] §1.1.1 "for a
  submonoid `Σ ⊆ M₂(F_𝔭)` the predicate `LevelBounds Σ ρ`: its elements satisfy the four conditions,
  i.e. `Σ ⊆ SigmaNorm F_𝔭 ρ`". Sketch: unfold; `mono` restricts the quantifier; `mono_radius` uses
  `‖c‖ ≤ ρ ≤ ρ'`; `le_sigmaNorm`/`of_le` are `mem_sigmaNorm_iff` in both directions. Attacks: [3]
  the structure includes `det_ne_zero`, which [SRC]'s `LevelBounds` omitted (erratum E6): without it
  `detChar` (L5.11) cannot be formed ✓ necessary. [4] "the four conditions" of the roadmap ✓ plus
  the two real bounds (decision D9). SURVIVED.

- **L1.4** `LevelBounds.d_ne_zero`, `LevelBounds.norm_det_le_one`, `LevelBounds.norm_mul_add_eq_one`
  — [RM] §1.2.2 "`c z + d ∈ 𝒪^×` because `‖c‖ < 1 = ‖d‖`". Sketch: `‖d‖ = 1 ≠ 0`;
  `det = ad − bc` with four integral entries (`Matrix.det_fin_two` ✓, ultrametric inequality);
  `‖cz‖ ≤ ρ < 1 = ‖d‖` and the isosceles principle. Attacks: [2] `z = 0` ✓; `c = 0` ✓. [3] `‖z‖ ≤ 1` is
  used (`‖cz‖ ≤ ‖c‖`) ✓ necessary (`z = 1/c` gives `cz + d` of norm `≤ 1` but possibly `< 1`). [5]
  `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` ✓. SURVIVED.

#### Mathlib lemmas needed

`Matrix.det_fin_two`, `IsUltrametricDist.norm_add_le_max`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.1.1–§1.1.4; [Buz07, §9, p. 68]; [Jac03, Definition 1.27]; [SRC] `QMF/Weight/00_Series.lean`, `QMF/Slash/01_Sigma0.lean`, `QMF/Weight/04_AdicLevel.lean` (proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D9** `SigmaNorm L ρ hρ0 hρ` with explicit real hypotheses; `LevelBounds S ρ` bundles them with the four conditions.

#### Progress

- 2026-10-06T19:58: DONE. Structure-constructor proofs; `norm_mul_add_eq_one` by the isosceles principle. `omit [IsUltrametricDist L] in` on `mono`, `mono_radius`, `d_ne_zero` (unused-section-variable linter). Axioms std.

### [T003] `norm_apply_zero_zero_le_of_norm_det_le`, `isUnit_sigmaNorm_iff`, `eta` and 3 more

- **Status**: done   (finished 2026-10-06T19:58) · **File**: `Level.lean` · **Depends on**: [T002] · **Type**: proof · **Leaves**: L1.5, L1.6, L1.7

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- **The determinant bound**: on a level, `‖det γ‖ ≤ σ` with `ρ ≤ σ` forces `‖a‖ ≤ σ`, since
`a d = det γ + b c` with `‖d‖ = 1` and `‖b c‖ ≤ ρ`. Source: roadmap §1.1.2; [Buz07, proof of
Lemma 12.2]. -/
theorem LevelBounds.norm_apply_zero_zero_le_of_norm_det_le (hb : LevelBounds S ρ) {σ : ℝ}
    (hρσ : ρ ≤ σ) {g : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S) (hdet : ‖g.det‖ ≤ σ) :
    ‖g 0 0‖ ≤ σ := by
  sorry

/-- The units of `Σ(ρ)` are its elements of determinant norm `1`. Source: roadmap §1.1.2. -/
theorem isUnit_sigmaNorm_iff {hρ0 : 0 ≤ ρ} {hρ : ρ < 1} {g : SigmaNorm L ρ hρ0 hρ} :
    IsUnit g ↔ ‖(g : Matrix (Fin 2) (Fin 2) L).det‖ = 1 := by
  sorry

/-- The matrix `η = diag(ϖ, 1)`. Source: roadmap §1.1.2; [Buz07, §12]. -/
def eta (ϖ : L) : Matrix (Fin 2) (Fin 2) L := !![ϖ, 0; 0, 1]

@[simp] theorem det_eta (ϖ : L) : (eta L ϖ).det = ϖ := by
  sorry

theorem eta_mem_sigmaNorm {ϖ : L} (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    eta L ϖ ∈ SigmaNorm L ρ hρ0 hρ := by
  sorry

/-- `η` lies in every `Σ(ρ)` but is not a unit there when `‖ϖ‖ < 1`. Source: roadmap §1.1.2. -/
theorem not_isUnit_eta {ϖ : L} (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    ¬ IsUnit (⟨eta L ϖ, eta_mem_sigmaNorm hϖ0 hϖ1.le hρ0 hρ⟩ : SigmaNorm L ρ hρ0 hρ) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L1.5** `LevelBounds.norm_apply_zero_zero_le_of_norm_det_le` — [RM] §1.1.2 "For
  `γ ∈ SigmaNorm F_𝔭 ρ` and `ρ ≤ σ`, `‖det γ‖ ≤ σ` implies `‖a‖ ≤ σ`: `a d = det γ + b c` with `‖d‖ = 1`
  and `‖b c‖ ≤ ρ ≤ σ`." Sketch: substrate, *the determinant bound*; [SRC]
  `LevelBounds.norm_apply_zero_zero_le_of_norm_det_le` is this proof verbatim. Attacks: [1] is it
  false without `ρ ≤ σ`? Take `σ < ρ`, `γ = ((0 1), (c 1))` with `‖c‖ = ρ`: `det = −c`, `‖det‖ = ρ > σ`
  — hypothesis fails, no counterexample to the statement; with `γ = ((σ' 0), (c 1))`, `‖σ'‖ ≤ σ`,
  the conclusion holds anyway. The hypothesis `ρ ≤ σ` is used in the bound of the cross term and
  cannot be dropped: `γ = ((1 1), (c 1))` with `‖c‖ = ρ`, `det = 1 − c` of norm `1`; take `σ = 1`
  fine; take `γ = ((c 1), (c 1))`? `det = 0` excluded. `γ = ((1 1),(c 1 + c))`: `det = 1 + c − c = 1`.
  Constructing `‖det‖ ≤ σ < ρ ≤ ‖a‖` needs `‖a‖ ≤ max(‖det‖, ‖bc‖)` to fail, impossible — so the
  statement is TRUE with `σ ≥ ‖bc‖` only, i.e. with `max(ρ, ‖det‖)`; the roadmap's `ρ ≤ σ` is the
  clean sufficient form, kept ✓ (not over-specified in any consumer: §3.5 uses `σ = ‖ϖ‖ ≥ ρ`). [4]
  [Buz07, Lemma 12.2 proof] uses exactly `det(x_δ)/det(η)` a unit ✓. SURVIVED.

- **L1.6** `isUnit_sigmaNorm_iff` — [RM] §1.1.2 "The units of `SigmaNorm F_𝔭 ρ` are its elements
  with `‖det‖ = 1`". Sketch: substrate, *units*; the inverse is `⟨adjugate g / det g, _⟩` with the
  four conditions checked (`Matrix.adjugate_fin_two` ✓, `Matrix.mul_adjugate` ✓,
  `Matrix.adjugate_mul` ✓, `Units.mk`/`isUnit_iff_exists`). Attacks: [1] a unit of `M₂(L)` need not be
  a unit of `Σ(ρ)`: `η⁻¹ = diag(ϖ⁻¹, 1)` is not integral ✓ consistent (`‖det η‖ = ‖ϖ‖ < 1`). [2]
  `‖det g‖ = 1` with `ρ = 0`: `c = 0`, inverse `((d, −b), (0, a))/det` ✓ integral. [3] the statement
  is about units *of the submonoid* `SigmaNorm` (as a `Monoid`), not of `M₂(L)` — the roadmap's
  meaning ✓; for a general `S` with `LevelBounds` the inverse may leave `S`, so the leaf is stated
  for `SigmaNorm` only ✓. SURVIVED.

- **L1.7** `eta`, `det_eta`, `eta_mem_sigmaNorm`, `not_isUnit_eta` — [RM] §1.1.2 "`η = diag(ϖ, 1)` lies
  in every `SigmaNorm F_𝔭 ρ` with `‖det η‖ = ‖ϖ‖` and is not a unit." Sketch: `Matrix.det_fin_two_of` ✓;
  entries `ϖ, 0, 0, 1` integral for `‖ϖ‖ ≤ 1`; `c = 0 ≤ ρ`, `d = 1`; `det = ϖ ≠ 0`; L1.6 with
  `‖ϖ‖ < 1`. Attacks: [2] `ϖ` a unit (`‖ϖ‖ = 1`): `η` IS a unit — hence `not_isUnit_eta` needs
  `‖ϖ‖ < 1` ✓ hypothesis present; `eta_mem_sigmaNorm` needs only `‖ϖ‖ ≤ 1` and `ϖ ≠ 0` ✓. [4]
  [Buz07, §12]: `η_v` "the matrix `((π_v 0), (0 1))`" ✓. SURVIVED.

#### Mathlib lemmas needed

`Matrix.det_fin_two`, `Matrix.det_fin_two_of`, `Matrix.adjugate_fin_two`, `Matrix.mul_adjugate`, `Matrix.adjugate_mul`, `isUnit_iff_exists`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.1.1–§1.1.4; [Buz07, §9, p. 68]; [Jac03, Definition 1.27]; [SRC] `QMF/Weight/00_Series.lean`, `QMF/Slash/01_Sigma0.lean`, `QMF/Weight/04_AdicLevel.lean` (proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D9** `SigmaNorm L ρ hρ0 hρ` with explicit real hypotheses; `LevelBounds S ρ` bundles them with the four conditions.

#### Progress

- 2026-10-06T19:58: DONE. `isUnit_sigmaNorm_iff`: (→) `det u · det u⁻¹ = 1` with both norms ≤ 1 + linarith; (←) explicit inverse `(det g)⁻¹ • adjugate g` (`mul_adjugate`, `adjugate_mul`, `Matrix.mul_smul`, `Matrix.smul_mul`), `‖a‖ = 1` from `ad = det + bc`. `not_isUnit_eta` via `change` across the subtype coercion. Axioms std.

### [CLEANUP-1] `/cleanup` of `Level.lean` (cadence: three proof tickets)

- **Status**: done   (finished 2026-10-06T19:58) · **File**: `Level.lean` · **Depends on**: [T003] · **Type**: cleanup

Run `/cleanup` on `PhD/TauCeti/Code/OverconvergentForms/Weight/Level.lean` (cadence: three proof tickets). Style audit + golf to mathlib standards; add `omit … in` where the skeleton's 'automatically included section variable(s) unused' warnings point; check docstrings cite the roadmap clause and the source; no statement changes without a B2 entry in `b2_log.jsonl`.

#### Progress

- 2026-10-06T19:58: DONE inline (memory: cleanup-inline-no-subagents). Line lengths ≤ 100 (codepoint check; two docstring lines rewrapped), `omit` annotations added, `runLinter PhD.TauCeti.Code.OverconvergentForms.Weight.Level` passes, no statement changes.

### [T004] `SigmaOne`, `mem_sigmaOne_iff`, `sigmaOne_le_sigmaNorm` and 5 more

- **Status**: done   (finished 2026-10-06T19:58) · **File**: `Level.lean` · **Depends on**: [CLEANUP-1] · **Type**: proof · **Leaves**: L1.8, L1.9

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- **The `Σ₁`-type level**: `‖c‖ ≤ ρ²` and `‖d − 1‖ ≤ ρ` inside `Σ(ρ)` — Jacobs's `Σ₁(p)`
(`c ≡ 0 mod p²`, `d ≡ 1 mod p`) at `ρ = ‖p‖`. Source: roadmap §1.1.3. -/
def SigmaOne (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) : Submonoid (Matrix (Fin 2) (Fin 2) L) where
  carrier := {g | g ∈ SigmaNorm L ρ hρ0 hρ ∧ ‖g 1 0‖ ≤ ρ ^ 2 ∧ ‖g 1 1 - 1‖ ≤ ρ}
  one_mem' := by
    sorry
  mul_mem' := by
    sorry

theorem mem_sigmaOne_iff {hρ0 : 0 ≤ ρ} {hρ : ρ < 1} {g : Matrix (Fin 2) (Fin 2) L} :
    g ∈ SigmaOne L ρ hρ0 hρ ↔ g ∈ SigmaNorm L ρ hρ0 hρ ∧ ‖g 1 0‖ ≤ ρ ^ 2 ∧ ‖g 1 1 - 1‖ ≤ ρ :=
  Iff.rfl

theorem sigmaOne_le_sigmaNorm (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    SigmaOne L ρ hρ0 hρ ≤ SigmaNorm L ρ hρ0 hρ := fun _ hg => hg.1

theorem levelBounds_sigmaOne (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) : LevelBounds (SigmaOne L ρ hρ0 hρ) ρ :=
  (levelBounds_sigmaNorm hρ0 hρ).mono (sigmaOne_le_sigmaNorm hρ0 hρ)

/-- **The left-handed monoid** `Σ₀(ρ) = {‖a‖ = 1, ‖c‖ ≤ ρ, integral, det ≠ 0}` of Pollack–Stevens.
Source: roadmap §1.1.4, convention 2. -/
def Sigma0 (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) : Submonoid (Matrix (Fin 2) (Fin 2) L) where
  carrier := {g | (∀ i j, ‖g i j‖ ≤ 1) ∧ ‖g 1 0‖ ≤ ρ ∧ ‖g 0 0‖ = 1 ∧ g.det ≠ 0}
  one_mem' := by
    sorry
  mul_mem' := by
    sorry

theorem mem_sigma0_iff {hρ0 : 0 ≤ ρ} {hρ : ρ < 1} {g : Matrix (Fin 2) (Fin 2) L} :
    g ∈ Sigma0 L ρ hρ0 hρ ↔
      (∀ i j, ‖g i j‖ ≤ 1) ∧ ‖g 1 0‖ ≤ ρ ∧ ‖g 0 0‖ = 1 ∧ g.det ≠ 0 :=
  Iff.rfl

/-- **The adjugate dictionary**: `adj ((a b), (c d)) = ((d −b), (−c a))` sends `Σ(ρ)` onto `Σ₀(ρ)`.
Source: roadmap §1.1.4. -/
theorem adjugate_mem_sigma0_iff {hρ0 : 0 ≤ ρ} {hρ : ρ < 1} {g : Matrix (Fin 2) (Fin 2) L} :
    g.adjugate ∈ Sigma0 L ρ hρ0 hρ ↔ g ∈ SigmaNorm L ρ hρ0 hρ := by
  sorry

theorem adjugate_mem_sigmaNorm_iff {hρ0 : 0 ≤ ρ} {hρ : ρ < 1} {g : Matrix (Fin 2) (Fin 2) L} :
    g.adjugate ∈ SigmaNorm L ρ hρ0 hρ ↔ g ∈ Sigma0 L ρ hρ0 hρ := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L1.8** `SigmaOne` (fields), `mem_sigmaOne_iff`, `sigmaOne_le_sigmaNorm`, `levelBounds_sigmaOne` —
  [RM] §1.1.3 "`{γ ∈ SigmaNorm F_𝔭 ρ | ‖c‖ ≤ ρ², ‖d − 1‖ ≤ ρ}` (Jacobs's `Σ₁(p)`: `c ≡ 0 mod p²`,
  `d ≡ 1 mod p` at `ρ = ‖p‖`) is a submonoid with level bounds `ρ`". Sketch: substrate, *`Σ₁`-type
  levels*; [SRC] `QMF/Weight/04_AdicLevel.SigmaOne` is this proof. Attacks: [2] `ρ = 0`: `c = 0`,
  `d = 1`, still a monoid ✓. [3] why `ρ²` for `c` and `ρ` for `d − 1`: the product's `d − 1` picks up
  `c b'` of norm `≤ ρ²` and `d(d' − 1)` of norm `≤ ρ` — with `‖c‖ ≤ ρ` only, `‖(gh)_{11} − 1‖ ≤ ρ` still
  holds, so the `ρ²` is Jacobs's level (`9 ∣ c`), not a closure requirement; kept as the roadmap
  states it ✓ (it is what makes `U₁(9)`'s image land in it, L1.11). [4] [Jac03, Definition 1.20]:
  `U₁(9)` has `3`-component `{9 ∣ c, d ≡ 1 mod 9}`; at `ρ = ‖3‖`, `‖d − 1‖ ≤ ‖9‖ ≤ ‖3‖` ✓ (roadmap
  §1.1.3). SURVIVED.

- **L1.9** `Sigma0` (fields), `mem_sigma0_iff`, `adjugate_mem_sigma0_iff`, `adjugate_mem_sigmaNorm_iff`
  — [RM] §1.1.4 "it exchanges `SigmaNorm F_𝔭 ρ` with the left-handed monoid
  `Σ₀(ρ) := {‖a‖ = 1, ‖c‖ ≤ ρ, integral, det ≠ 0}` of Pollack–Stevens". Sketch: `Sigma0`'s monoid law
  is L1.2's with the roles of `a` and `d` exchanged (`(gh)_{00} = a a' + b c'`, `‖b c'‖ ≤ ρ < 1`);
  the two `iff`s are `Matrix.adjugate_fin_two` ✓ + `norm_neg` + `Matrix.det_adjugate_fin_two` (L1.1)
  + `Matrix.adjugate_adjugate_fin_two` for the reverse. Attacks: [1] transposition instead of
  adjugate would send `‖c‖ ≤ ρ` to `‖b‖ ≤ ρ` (roadmap convention 2's warning) — the adjugate is the
  right map ✓. [4] [SRC] `QMF/Slash/01_Sigma0.adj` ✓. SURVIVED.

#### Mathlib lemmas needed

`Matrix.adjugate_fin_two`, `norm_neg`, `Matrix.mul_apply`, `Fin.sum_univ_two`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.1.1–§1.1.4; [Buz07, §9, p. 68]; [Jac03, Definition 1.27]; [SRC] `QMF/Weight/00_Series.lean`, `QMF/Slash/01_Sigma0.lean`, `QMF/Weight/04_AdicLevel.lean` (proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D9** `SigmaNorm L ρ hρ0 hρ` with explicit real hypotheses; `LevelBounds S ρ` bundles them with the four conditions.

#### Progress

- 2026-10-06T19:58: DONE. `SigmaOne` monoid law: `(gh)₁₁ − 1 = c b' + d(d' − 1) + (d − 1)` by `ring`, three ultrametric bounds; `Sigma0` law mirrors `SigmaNorm` with the isosceles step on the `a`-entry; `adjugate_mem_sigma0_iff` by `adjugate_fin_two` + `simp [Fin.forall_fin_two]` + `tauto`; the converse by `adjugate_adjugate_fin_two`. Axioms std.

### [T005] `adjugateEquiv`, `adjugateEquiv_apply_coe`, `adjugate_eta`

- **Status**: done   (finished 2026-10-06T19:58) · **File**: `Level.lean` · **Depends on**: [T004] · **Type**: proof · **Leaves**: L1.10

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- **Right actions of `Σ(ρ)` are left actions of `Σ₀(ρ)` along the adjugate**: the
anti-automorphism `adj` of `M₂(L)` induces a monoid isomorphism `Σ(ρ)ᵐᵒᵖ ≃* Σ₀(ρ)`. Source:
roadmap §1.1.4, convention 2 ("the dictionary to the left-handed form is the adjugate"). -/
noncomputable def adjugateEquiv (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    (SigmaNorm L ρ hρ0 hρ)ᵐᵒᵖ ≃* Sigma0 L ρ hρ0 hρ where
  toFun g := ⟨(g.unop : Matrix (Fin 2) (Fin 2) L).adjugate, adjugate_mem_sigma0_iff.mpr g.unop.2⟩
  invFun g := MulOpposite.op ⟨(g : Matrix (Fin 2) (Fin 2) L).adjugate,
    adjugate_mem_sigmaNorm_iff.mpr g.2⟩
  left_inv g := by
    sorry
  right_inv g := by
    sorry
  map_mul' g h := by
    sorry

@[simp] theorem adjugateEquiv_apply_coe {hρ0 : 0 ≤ ρ} {hρ : ρ < 1} (g : (SigmaNorm L ρ hρ0 hρ)ᵐᵒᵖ) :
    (adjugateEquiv L ρ hρ0 hρ g : Matrix (Fin 2) (Fin 2) L) =
      (g.unop : Matrix (Fin 2) (Fin 2) L).adjugate :=
  rfl

/-- The adjugate of `η = diag(ϖ, 1)` is the left-handed `diag(1, ϖ)`. Source: roadmap §1.1.4. -/
theorem adjugate_eta (ϖ : L) : (eta L ϖ).adjugate = !![1, 0; 0, ϖ] := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L1.10** `adjugateEquiv` (fields `left_inv`, `right_inv`, `map_mul'`), `adjugateEquiv_apply_coe`,
  `adjugate_eta` — [RM] §1.1.4 "A right action of `SigmaNorm` is the same as a left action of `Σ₀`
  along `adj`, and `adj η` is the left-handed `diag(1, ϖ)`." Lean: `(SigmaNorm L ρ)ᵐᵒᵖ ≃* Sigma0 L ρ`.
  Sketch: `left_inv`/`right_inv` are `adjugate_adjugate_fin_two`; `map_mul'`: `(op g · op h).unop =
  h · g`, `adj (h g) = adj g · adj h` ✓ `Matrix.adjugate_mul_distrib`; `adjugate_eta` by
  `Matrix.adjugate_fin_two_of` ✓. Attacks: [1] the direction: `op g * op h = op (h * g)` in
  `MulOpposite` (`MulOpposite.op_mul` ✓) and `adj (h g) = adj g adj h`, so `toFun (op g * op h) =
  adj (h g) = adj g · adj h = toFun (op g) · toFun (op h)` ✓ a homomorphism (not anti). [4] the
  roadmap's "left-handed `diag(1, ϖ)`" ✓. SURVIVED.

#### Mathlib lemmas needed

`Matrix.adjugate_mul_distrib`, `Matrix.adjugate_fin_two_of`, `MulOpposite.op_mul`, `MulOpposite.unop_mul`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.1.1–§1.1.4; [Buz07, §9, p. 68]; [Jac03, Definition 1.27]; [SRC] `QMF/Weight/00_Series.lean`, `QMF/Slash/01_Sigma0.lean`, `QMF/Weight/04_AdicLevel.lean` (proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D8** namespace `AutomorphicForm`; Tate-algebra seams in `MvPowerSeries.Restricted` / `PowerSeries.Restricted` / `Matrix`.

#### Progress

- 2026-10-06T19:58: DONE. `adjugateEquiv`: inverses by `adjugate_adjugate_fin_two` (through `Subtype.ext`/`MulOpposite.unop_injective`), `map_mul'` by `change` to `adj (h.unop * g.unop)` + `adjugate_mul_distrib`; `adjugate_eta` by `adjugate_fin_two_of` + simp. Axioms std.

### [CLEANUP-2] `/cleanup` of `Level.lean` (final for the file)

- **Status**: done   (finished 2026-10-06T19:58) · **File**: `Level.lean` · **Depends on**: [T005] · **Type**: cleanup

Run `/cleanup` on `PhD/TauCeti/Code/OverconvergentForms/Weight/Level.lean` (final for the file). Style audit + golf to mathlib standards; add `omit … in` where the skeleton's 'automatically included section variable(s) unused' warnings point; check docstrings cite the roadmap clause and the source; no statement changes without a B2 entry in `b2_log.jsonl`.

#### Progress

- 2026-10-06T19:58: DONE inline: final pass on Level.lean — no warning, runLinter passes, every def has a docstring, every proof ≤ 40 lines; the one `<;>` flagged by the linter split into two lines.

### [T006] `mem_monoidM_iff_mem_sigmaNorm`, `coe_mem_sigmaNorm_of_mem_iwahori`, `coe_mem_sigmaOne_of_mem_iwahoriOne`

- **Status**: done   (finished 2026-10-06T19:58) · **File**: `Dictionary.lean` · **Depends on**: [CLEANUP-2] · **Type**: proof · **Leaves**: L1.11

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- **The dictionary** `M_t = Σ(‖ϖ‖^t)`: Buzzard's monoid in valued form is the norm-form level
monoid at radius `‖ϖ‖^t`. Source: roadmap §1.1.1; [L0] `LocalLevel.mem_monoidM_iff_norm`. -/
theorem mem_monoidM_iff_mem_sigmaNorm {ϖ : K} (hϖ1 : Valued.v ϖ < 1) {t : ℕ} (ht : 1 ≤ t)
    {g : Matrix (Fin 2) (Fin 2) K} :
    g ∈ LocalLevel.monoidM K (Valued.v ϖ ^ t) (pow_lt_one₀ zero_le hϖ1 (by omega)) ↔
      g ∈ SigmaNorm K (‖ϖ‖ ^ t) (pow_nonneg (norm_nonneg ϖ) t)
        (pow_lt_one₀ (norm_nonneg ϖ) (Valued.toNormedField.norm_lt_one_iff.mpr hϖ1) (by omega)) := by
  sorry

/-- The Iwahori subgroup `Iw(ϖ^t)` has level bounds `‖ϖ‖^t`. Source: roadmap §1.1.1 ("so that
`Iw(𝔭^t)` and the `U₁`-type groups have level bounds `‖ϖ‖^t`"). -/
theorem coe_mem_sigmaNorm_of_mem_iwahori {ϖ : K} (hϖ1 : Valued.v ϖ < 1) {t : ℕ} (ht : 1 ≤ t)
    {g : GL (Fin 2) K} (hg : g ∈ LocalLevel.iwahori K (Valued.v ϖ ^ t)) :
    (g : Matrix (Fin 2) (Fin 2) K) ∈ SigmaNorm K (‖ϖ‖ ^ t) (pow_nonneg (norm_nonneg ϖ) t)
      (pow_lt_one₀ (norm_nonneg ϖ) (Valued.toNormedField.norm_lt_one_iff.mpr hϖ1) (by omega)) := by
  sorry

/-- A `U₁(ϖ^{2t})`-type subgroup has `Σ₁`-type bounds at `‖ϖ‖^t`: `‖c‖ ≤ ‖ϖ‖^{2t} = (‖ϖ‖^t)²` and
`‖d − 1‖ ≤ ‖ϖ‖^{2t} ≤ ‖ϖ‖^t`. Source: roadmap §1.1.3. -/
theorem coe_mem_sigmaOne_of_mem_iwahoriOne {ϖ : K} (hϖ1 : Valued.v ϖ < 1) {t : ℕ} (ht : 1 ≤ t)
    {g : GL (Fin 2) K} (hg : g ∈ LocalLevel.iwahoriOne K (Valued.v ϖ ^ (2 * t))) :
    (g : Matrix (Fin 2) (Fin 2) K) ∈ SigmaOne K (‖ϖ‖ ^ t) (pow_nonneg (norm_nonneg ϖ) t)
      (pow_lt_one₀ (norm_nonneg ϖ) (Valued.toNormedField.norm_lt_one_iff.mpr hϖ1) (by omega)) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L1.11** `mem_monoidM_iff_mem_sigmaNorm`, `coe_mem_sigmaNorm_of_mem_iwahori`,
  `coe_mem_sigmaOne_of_mem_iwahoriOne` — [RM] §1.1.1 "Prove the valuation dictionary
  `M_t = SigmaNorm F_𝔭 ‖ϖ‖^t` (§0.4.1), so that `Iw(𝔭^t)` and the `U₁`-type groups have level bounds
  `‖ϖ‖^t`"; §1.1.3 "the image under `θ_𝔭` of a `U₁(𝔭^{2t})`-type group has `Σ₁`-type bounds at
  `ρ = ‖ϖ‖^t`". Sketch: substrate, *the dictionary with Layer 0*. Discharge: [L0]
  `LocalLevel.mem_monoidM_iff_norm` ✓, `LocalLevel.coe_mem_monoidM` ✓, `LocalLevel.iwahoriOne`'s
  field `v(d − 1) ≤ γ`; `Valued.toNormedField.norm_le_iff` ✓, `norm_pow`, `pow_le_pow_of_le_one`,
  `Valued.toNormedField.norm_lt_one_iff` ✓ (all in Mathlib's `NormedValued.lean`; the `NormedField`
  instance is `open scoped Valued`, and `IsUltrametricDist` is Mathlib's instance for it, line 213).
  Attacks: [2] `t = 1` ✓ (`2t = 2`); `t = 0` excluded by `1 ≤ t` (then `ρ = 1`, not `< 1`) ✓. [3] the
  `RankOne` hypothesis is what gives the norm ✓ necessary. [4] [Buz07, §9]: `U₁(𝔫)` "congruent to
  `((∗ ∗), (0 1))` mod `𝔫`" at `𝔫 = ϖ^{2t}` has `‖d − 1‖ ≤ ‖ϖ‖^{2t}` ✓ ≤ `‖ϖ‖^t`. SURVIVED.

#### Mathlib lemmas needed

`LocalLevel.mem_monoidM_iff_norm`, `LocalLevel.coe_mem_monoidM`, `Valued.toNormedField.norm_le_iff`, `Valued.toNormedField.norm_lt_one_iff`, `norm_pow`, `pow_le_pow_of_le_one`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.1.1, §1.1.3; [L0] `Level/Local.lean` (`mem_monoidM_iff_norm`, `coe_mem_monoidM`, `iwahoriOne`).

#### Generality decision

Binding decisions of `plan.md`: **D9** `SigmaNorm L ρ hρ0 hρ` with explicit real hypotheses; `LevelBounds S ρ` bundles them with the four conditions.

#### Progress

- 2026-10-06T19:58: DONE. `mem_monoidM_iff_mem_sigmaNorm` is [L0] `LocalLevel.mem_monoidM_iff_norm` on the nose (the `letI` zeta-reduces against `open scoped Valued`); `coe_mem_sigmaOne_of_mem_iwahoriOne` via `iwahori_mono` (`pow_le_pow_right_of_le_one'` in Γ₀) and `Valued.toNormedField.norm_le_iff` + `map_pow`. Builds with no warning.

### [CLEANUP-3] `/cleanup` of `Dictionary.lean` (final for the file)

- **Status**: done   (finished 2026-10-06T19:58) · **File**: `Dictionary.lean` · **Depends on**: [T006] · **Type**: cleanup

Run `/cleanup` on `PhD/TauCeti/Code/OverconvergentForms/Weight/Dictionary.lean` (final for the file). Style audit + golf to mathlib standards; add `omit … in` where the skeleton's 'automatically included section variable(s) unused' warnings point; check docstrings cite the roadmap clause and the source; no statement changes without a B2 entry in `b2_log.jsonl`.

#### Progress

- 2026-10-06T19:58: DONE inline: Dictionary.lean — runLinter passes, no warning, line lengths ≤ 100.

### [T007] `aeval_aeval`, `aeval_X_eq_self`, `MultiBounds` and 5 more

- **Status**: done   (finished 2026-10-06T20:13) · **File**: `Mobius.lean` · **Depends on**: none · **Type**: proof · **Leaves**: L2.1, L2.2

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- **Composition of substitutions**: substituting `x` into `f ∘ y` is substituting `y(x)` into
`f`. Source: BGR 5.1.3/5 (uniqueness of continuous homomorphisms out of the Tate algebra). -/
theorem aeval_aeval {x : σ → B} (hx : ∀ i, ‖x i‖ ≤ 1) {y : σ → Restricted K (1 : σ → ℝ)}
    (hy : ∀ i, ‖y i‖ ≤ 1) (f : Restricted K (1 : σ → ℝ)) :
    aeval 1 x hx (aeval 1 y hy f) =
      aeval 1 (fun i => aeval 1 x hx (y i)) (fun i => (norm_aeval_le hx (y i)).trans (hy i)) f := by
  sorry

/-- The identity substitution. -/
theorem aeval_X_eq_self (f : Restricted K (1 : σ → ℝ)) :
    aeval 1 (fun i => X K (1 : σ → ℝ) i) (fun i => by simp [norm_X]) f = f := by
  sorry

/-- **The level bounds of a multi-matrix** `γ : ι → M₂(K)`: integral entries, `‖c_i‖ ≤ ρ`,
`‖d_i‖ = 1`, with `0 ≤ ρ < 1`. The image of a level `S ⊆ M₂(L)` under isometric embeddings
satisfies them (`Embeddings.multiBounds_toMulti`). Source: roadmap §1.2 preamble, §1.1.1. -/
structure MultiBounds (ρ : ℝ) (γ : ι → Matrix (Fin 2) (Fin 2) K) : Prop where
  rho_nonneg : 0 ≤ ρ
  rho_lt_one : ρ < 1
  integral : ∀ i j k, ‖γ i j k‖ ≤ 1
  c_le : ∀ i, ‖γ i 1 0‖ ≤ ρ
  d_unit : ∀ i, ‖γ i 1 1‖ = 1

theorem MultiBounds.mul (hγ : MultiBounds ρ γ) (hδ : MultiBounds ρ δ) : MultiBounds ρ (δ * γ) := by
  sorry

theorem MultiBounds.one (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    MultiBounds ρ (1 : ι → Matrix (Fin 2) (Fin 2) K) := by
  sorry

theorem MultiBounds.mono {σ : ℝ} (hγ : MultiBounds ρ γ) (hρσ : ρ ≤ σ) (hσ : σ < 1) :
    MultiBounds σ γ := by
  sorry

theorem MultiBounds.d_ne_zero (hγ : MultiBounds ρ γ) (i : ι) : γ i 1 1 ≠ 0 := by
  sorry

theorem MultiBounds.norm_c_div_d_lt_one (hγ : MultiBounds ρ γ) (i : ι) :
    ‖γ i 1 0 / γ i 1 1‖ < 1 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L2.1** `MvPowerSeries.Restricted.aeval_aeval`, `aeval_X_eq_self` — [RM] §1.2.1 (the
  substitution of PFA §4.1.4), §1.2.5 ("`(f ∣_κ γ)(z) = j_κ(γ)(z) · f(w_γ(z))`", which needs
  evaluation of a substituted series). Lean: `aeval x (aeval y f) = aeval (fun i => aeval x (y i)) f`
  for `‖x‖, ‖y‖ ≤ 1`; `aeval X f = f`. Sketch: both sides are continuous `K`-algebra homomorphisms in
  `f` ([RAG] `continuous_aeval` ✓, composition) agreeing on `X i` ([RAG] `aeval_X` ✓); [RAG]
  `algHom_ext_of_continuous` ✓. Attacks: [2] `σ` empty: both sides are the constant coefficient ✓.
  [3] `‖y i‖ ≤ 1` is needed for `aeval y` to exist; `‖aeval x (y i)‖ ≤ 1` follows ([RAG]
  `norm_aeval_le` ✓) ✓ no extra hypothesis. [5] [RAG] names verified by the skeleton's elaboration
  (the statement uses `norm_aeval_le`). SURVIVED.

- **L2.2** `MultiBounds` (structure), `MultiBounds.mul`, `.one`, `.mono`, `.d_ne_zero`,
  `.norm_c_div_d_lt_one` — [RM] §1.1.1 transported to multi-matrices (decision D2). Sketch: as L1.2
  coordinatewise (`Pi.mul_apply`); `‖c/d‖ = ‖c‖/1 ≤ ρ < 1`. Attacks: [3] `.mul` needs `ρ < 1` for the
  `d`-entry (L1.2's counterexample) ✓ in the structure. [4] `MultiBounds ρ (e.toMulti g)` for
  `g ∈ S` is L5.5 ✓. SURVIVED.

#### Mathlib lemmas needed

`MvPowerSeries.Restricted.algHom_ext_of_continuous`, `MvPowerSeries.Restricted.continuous_aeval`, `MvPowerSeries.Restricted.aeval_X`, `MvPowerSeries.Restricted.norm_aeval_le`, `Pi.mul_apply`, `norm_div`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2 preamble, §1.2.1, §1.2.4, §1.2.5; [Buz07, Lemma 8.1, p. 59]; [Jac03, Lemma 2.7, p. 30]; [RAG] `TateAlgebra/Eval.lean`, `Restricted/Units.lean`; [SRC] `QMF/Weight/03_SlashAction.lean`, `TateFredholm/06_WeightGenFun.lean` (proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D2** the series algebra is for multi-matrices `γ : ι → Matrix (Fin 2) (Fin 2) K`; one and several places are instances; **D8** namespace `AutomorphicForm`; Tate-algebra seams in `MvPowerSeries.Restricted` / `PowerSeries.Restricted` / `Matrix`.

#### Progress

- 2026-10-06T20:13: DONE. `aeval_aeval`, `aeval_X_eq_self` by RAG `algHom_ext_of_continuous` (BGR 5.1.3/5) + `DFunLike.congr_fun`. `MultiBounds.mul` — B2 repaired in place (b2_log 2026-10-06T20:20Z): binders swapped to mathlib order `(hδ) (hγ) : MultiBounds ρ (δ * γ)` so that `hδ.mul hγ` bounds `δ * γ`, as `mobiusSubst_mul` (T010) reads it; no other consumer. Axioms std.

### [T008] `coeff_lin`, `coeff_num`, `hasSum_linInv` and 4 more

- **Status**: done   (finished 2026-10-06T20:13) · **File**: `Mobius.lean` · **Depends on**: [T007] · **Type**: proof · **Leaves**: L2.3, L2.4

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
theorem coeff_lin [DecidableEq ι] (i : ι) (t : ι →₀ ℕ) :
    coeff t (lin γ i).1 =
      if t = 0 then γ i 1 1 else if t = Finsupp.single i 1 then γ i 1 0 else 0 := by
  sorry

theorem coeff_num [DecidableEq ι] (i : ι) (t : ι →₀ ℕ) :
    coeff t (num γ i).1 =
      if t = 0 then γ i 0 1 else if t = Finsupp.single i 1 then γ i 0 0 else 0 := by
  sorry

theorem hasSum_linInv (hγ : MultiBounds ρ γ) (i : ι) :
    HasSum (fun m : ℕ => monomial 1 (Finsupp.single i m)
      ((γ i 1 1)⁻¹ * (-(γ i 1 0 / γ i 1 1)) ^ m)) (linInv γ i) := by
  sorry

theorem coeff_linInv [DecidableEq ι] (hγ : MultiBounds ρ γ) (i : ι) (t : ι →₀ ℕ) :
    coeff t (linInv γ i).1 =
      if t = Finsupp.single i (t i) then (γ i 1 1)⁻¹ * (-(γ i 1 0 / γ i 1 1)) ^ (t i) else 0 := by
  sorry

theorem lin_mul_linInv (hγ : MultiBounds ρ γ) (i : ι) : lin γ i * linInv γ i = 1 := by
  sorry

theorem isUnit_lin (hγ : MultiBounds ρ γ) (i : ι) : IsUnit (lin γ i) :=
  IsUnit.of_mul_eq_one (linInv γ i) (lin_mul_linInv hγ i)

theorem inverse_lin (hγ : MultiBounds ρ γ) (i : ι) : Ring.inverse (lin γ i) = linInv γ i := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L2.3** `lin`, `num`, `linInv`, `mobius` (defs), `coeff_lin`, `coeff_num` — [RM] §1.2 preamble "set
  `L_γ := (c_i z_i + d_i)_i` and `N_γ := (a_i z_i + b_i)_i`, families of one-variable polynomials
  indexed by `I_𝔭`, and the Möbius series `w_γ := (N_{γ,i} · L_{γ,i}^{-1})_i`". Sketch: [RAG] `val_C`,
  `val_X`, `val_add`, `val_mul` ✓, `MvPowerSeries.coeff_C`, `coeff_X` (`MvPowerSeries.coeff_X`,
  `coeff_C_mul`) *(ticket)*. Attacks: [2] `t = 0`: `d`; `t = e_i`: `c` ✓ consistent with the `if`
  (for `t = 0 = e_i` impossible). [3] `[DecidableEq ι]` only for the `if` ✓. SURVIVED.

- **L2.4** `hasSum_linInv`, `coeff_linInv`, `lin_mul_linInv`, `isUnit_lin`, `inverse_lin` — [RM] §1.2
  preamble (quoted above). Sketch: substrate, *the inverse*. Discharge: `NormedRing.inverse_one_sub` ✓
  (`inverse (1 − t) = ↑(Units.oneSub t h)⁻¹`), `tsum_geometric_of_norm_lt_one` *(ticket)*, [RAG]
  `hasSum_monomial`-style coefficient extraction (coefficients are continuous: [RAG]
  `DivisionSet.coeff_continuous` ✓), `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero` ✓
  (used by [RAG] `Eval.lean`), `Ring.inverse_unit`/`Units.inv_eq_of_mul_eq_one_right` *(ticket)*.
  Attacks: [1] `linInv` is defined for every `γ` (a `tsum`, junk `0` when not summable); the lemmas
  carry `MultiBounds` so the series converges ✓. [2] `c = 0`: `linInv = C d⁻¹`, `lin = C d` ✓. [3]
  `‖c/d‖ < 1` is exactly the convergence condition ✓ (L2.2). [5] `NormedRing.inverse_one_sub` grep'd ✓.
  SURVIVED.

#### Mathlib lemmas needed

`MvPowerSeries.Restricted.val_C`, `MvPowerSeries.Restricted.val_X`, `MvPowerSeries.Restricted.val_add`, `MvPowerSeries.Restricted.val_mul`, `MvPowerSeries.coeff_C`, `MvPowerSeries.coeff_X`, `NormedRing.inverse_one_sub`, `tsum_geometric_of_norm_lt_one`, `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`, `Ring.inverse_unit`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2 preamble, §1.2.1, §1.2.4, §1.2.5; [Buz07, Lemma 8.1, p. 59]; [Jac03, Lemma 2.7, p. 30]; [RAG] `TateAlgebra/Eval.lean`, `Restricted/Units.lean`; [SRC] `QMF/Weight/03_SlashAction.lean`, `TateFredholm/06_WeightGenFun.lean` (proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D2** the series algebra is for multi-matrices `γ : ι → Matrix (Fin 2) (Fin 2) K`; one and several places are instances.

#### Progress

- 2026-10-06T20:13: DONE. Geometric route: `lin = C d · (1 − u)`, `u = C(−c/d)·X`, `‖u‖ < 1`; `linInv = C d⁻¹ · ∑' uᵐ` (term-mode `tsum_congr`/`tsum_mul_left` — `rw` with the tsum lemma fails across the Restricted instance seam, as the restricted-seam memory warns); `lin_mul_linInv` by `mul_neg_geom_series`; coefficients via a private `hasSum_coeff` (continuity of `coeff t`, `‖a_t‖ ≤ ‖f‖`) + `hasSum_single`. Axioms std.

### [T009] `norm_lin_le_one`, `norm_num_le_one`, `norm_linInv_le_one` and 1 more

- **Status**: done   (finished 2026-10-06T20:13) · **File**: `Mobius.lean` · **Depends on**: [T008] · **Type**: proof · **Leaves**: L2.5, L2.6

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
theorem norm_lin_le_one (hγ : MultiBounds ρ γ) (i : ι) : ‖lin γ i‖ ≤ 1 := by
  sorry

theorem norm_num_le_one (hγ : MultiBounds ρ γ) (i : ι) : ‖num γ i‖ ≤ 1 := by
  sorry

theorem norm_linInv_le_one (hγ : MultiBounds ρ γ) (i : ι) : ‖linInv γ i‖ ≤ 1 := by
  sorry

/-- The Möbius series lie in the unit ball, so they can be substituted. Source: roadmap §1.2.1
("the coefficients of `w_γ` lie in the unit ball, so `w_γ` maps the closed unit polydisc to
itself"). -/
theorem norm_mobius_le_one (hγ : MultiBounds ρ γ) (i : ι) : ‖mobius γ i‖ ≤ 1 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L2.5** `norm_lin_le_one`, `norm_num_le_one`, `norm_linInv_le_one`, `norm_mobius_le_one` — [RM]
  §1.2.1 "the coefficients of `w_γ` lie in the unit ball, so `w_γ` maps the closed unit polydisc to
  itself". Sketch: [RAG] `norm_le_iff_forall_norm_coeff_le` ✓ with L2.3/L2.4's coefficient formulas;
  `‖linInv‖ ≤ 1` from `‖d⁻¹ (c/d)^m‖ ≤ 1`; `NormMulClass` ([RAG] instance ✓) for the product. Attacks:
  [2] `‖lin‖ = 1` exactly (constant term) — stated only `≤ 1`; `norm_aeval_lin` (L2.9) gives the
  pointwise `= 1` ✓. [4] [Buz07, Lemma 8.1(b)] on points ✓. SURVIVED.

- **L2.6** `mobiusSubst` (def), `mobiusSubst_apply`, `mobiusSubst_X`, `norm_mobiusSubst_le`,
  `continuous_mobiusSubst` — [RM] §1.2.1 the substitution. Sketch: [RAG] `aeval 1 (mobius γ)
  (norm_mobius_le_one hγ)`, `aeval_X` ✓, `norm_aeval_le` ✓, `continuous_aeval` ✓ — all already
  discharged in the skeleton (no `sorry`). SURVIVED (compiles).

#### Mathlib lemmas needed

`MvPowerSeries.Restricted.norm_le_iff_forall_norm_coeff_le`, `NormMulClass.norm_mul`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2 preamble, §1.2.1, §1.2.4, §1.2.5; [Buz07, Lemma 8.1, p. 59]; [Jac03, Lemma 2.7, p. 30]; [RAG] `TateAlgebra/Eval.lean`, `Restricted/Units.lean`; [SRC] `QMF/Weight/03_SlashAction.lean`, `TateFredholm/06_WeightGenFun.lean` (proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D2** the series algebra is for multi-matrices `γ : ι → Matrix (Fin 2) (Fin 2) K`; one and several places are instances.

#### Progress

- 2026-10-06T20:13: DONE. Norm bounds by the ultrametric inequality on `C`, `X` (`norm_C`, `norm_X`) and, for `linInv`, coefficientwise via `norm_le_iff_forall_norm_coeff_le`.

### [CLEANUP-4] `/cleanup` of `Mobius.lean` (cadence: three proof tickets)

- **Status**: done   (finished 2026-10-06T20:13) · **File**: `Mobius.lean` · **Depends on**: [T009] · **Type**: cleanup

Run `/cleanup` on `PhD/TauCeti/Code/OverconvergentForms/Weight/Mobius.lean` (cadence: three proof tickets). Style audit + golf to mathlib standards; add `omit … in` where the skeleton's 'automatically included section variable(s) unused' warnings point; check docstrings cite the roadmap clause and the source; no statement changes without a B2 entry in `b2_log.jsonl`.

#### Progress

- 2026-10-06T20:13: DONE inline: Mobius.lean T007–T009 portion — omit annotations from the unused-section-variable warnings, line lengths.

### [T010] `lin_mul`, `num_mul`, `mobius_mul` and 3 more

- **Status**: done   (finished 2026-10-06T20:13) · **File**: `Mobius.lean` · **Depends on**: [CLEANUP-4] · **Type**: proof · **Leaves**: L2.7, L2.8

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- **The automorphy-factor identity** `L_{δγ} = L_γ · (L_δ ∘ w_γ)`, i.e. the cocycle
`j(δγ, z) = j(γ, z) j(δ, γz)` for `j(γ, z) = cz + d`. Source: roadmap §1.2.1. -/
theorem lin_mul (hγ : MultiBounds ρ γ) (δ : ι → Matrix (Fin 2) (Fin 2) K) (i : ι) :
    lin (δ * γ) i = lin γ i * mobiusSubst hγ (lin δ i) := by
  sorry

theorem num_mul (hγ : MultiBounds ρ γ) (δ : ι → Matrix (Fin 2) (Fin 2) K) (i : ι) :
    num (δ * γ) i = lin γ i * mobiusSubst hγ (num δ i) := by
  sorry

/-- **Möbius composition** `w_{δγ} = w_δ ∘ w_γ`. Source: roadmap §1.2.1. -/
theorem mobius_mul (hγ : MultiBounds ρ γ) (hδ : MultiBounds ρ δ) (i : ι) :
    mobius (δ * γ) i = mobiusSubst hγ (mobius δ i) := by
  sorry

theorem mobius_one (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) (i : ι) :
    mobius (1 : ι → Matrix (Fin 2) (Fin 2) K) i = X K 1 i := by
  sorry

/-- Substitution is contravariant: `f ∘ w_{δγ} = (f ∘ w_δ) ∘ w_γ`. Source: roadmap §1.2.1. -/
theorem mobiusSubst_mul (hγ : MultiBounds ρ γ) (hδ : MultiBounds ρ δ) :
    mobiusSubst (hδ.mul hγ) = (mobiusSubst hγ).comp (mobiusSubst hδ) := by
  sorry

theorem mobiusSubst_one (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    mobiusSubst (MultiBounds.one (K := K) (ι := ι) hρ0 hρ) = AlgHom.id K _ := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L2.7** `lin_mul`, `num_mul`, `mobius_mul`, `mobius_one` — [RM] §1.2.1 (quoted in the substrate).
  Sketch: substrate, *Möbius composition*. Discharge: `Matrix.mul_apply` ✓, `Fin.sum_univ_two` ✓,
  `Pi.mul_apply` ✓, `map_add`/`map_mul` of the algebra hom, `mobiusSubst_X` (L2.6), `inverse_lin`
  (L2.4), `Ring.mul_inverse_cancel`/`Ring.inverse_mul_cancel` *(ticket)*, `mobius_one`: `lin 1 = C 1`,
  `num 1 = X i`, `linInv 1 = 1` (geometric series of `0`) — `mobius 1 i = X i`. Attacks: [1] the
  ORDER: `lin (δ * γ) i = lin γ i * mobiusSubst γ (lin δ i)` — check at a point `x`:
  LHS `= c'' x + d''` with `(δγ)_{10} = c' a + d' c`, `(δγ)_{11} = c' b + d' d`; RHS
  `= (c x + d)(c' w(x) + d') = c'(a x + b) + d'(c x + d)` ✓ equal. (The other order `γ * δ` would give
  `c a' + d c'`, wrong.) [2] `γ = 1`: `lin δ · 1 = lin δ` ✓. [3] `hγ` is needed (to invert `lin γ`), `hδ`
  is not needed for `lin_mul`/`num_mul` ✓ (stated without), but IS needed for `mobius_mul` (to invert
  `lin δ` inside the substitution) ✓ stated with both. [4] [RM]'s "`det(δγ) = det δ · det γ`" is
  `Matrix.det_mul` and enters L5.12, not here ✓. SURVIVED.

- **L2.8** `mobiusSubst_mul`, `mobiusSubst_one` — [RM] §1.2.1 ("`w_{δγ} = w_δ ∘ w_γ`" as substitution
  operators). Lean: `mobiusSubst (hδ.mul hγ) = (mobiusSubst hγ).comp (mobiusSubst hδ)`. Sketch: [RAG]
  `algHom_ext_of_continuous` ✓ on `X i` with L2.7 `mobius_mul`; `mobiusSubst_one` with `mobius_one`
  and `aeval_X_eq_self` (L2.1). Attacks: [1] order check: `(f ∘ w_δ) ∘ w_γ` means first substitute
  `w_δ` into `f`, then `w_γ` into the result: `comp (mobiusSubst γ) (mobiusSubst δ)` applied to `f` is
  `mobiusSubst γ (mobiusSubst δ f)` ✓ and `aeval w_γ (aeval w_δ f) = aeval (w_δ ∘ w_γ) f = aeval w_{δγ} f`
  by L2.1 and L2.7 ✓. SURVIVED.

#### Mathlib lemmas needed

`Matrix.mul_apply`, `Fin.sum_univ_two`, `Pi.mul_apply`, `Ring.inverse_mul_cancel`, `Ring.mul_inverse_cancel`, `MvPowerSeries.Restricted.algHom_ext_of_continuous`, `AlgHom.comp_apply`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2 preamble, §1.2.1, §1.2.4, §1.2.5; [Buz07, Lemma 8.1, p. 59]; [Jac03, Lemma 2.7, p. 30]; [RAG] `TateAlgebra/Eval.lean`, `Restricted/Units.lean`; [SRC] `QMF/Weight/03_SlashAction.lean`, `TateFredholm/06_WeightGenFun.lean` (proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D2** the series algebra is for multi-matrices `γ : ι → Matrix (Fin 2) (Fin 2) K`; one and several places are instances.

#### Progress

- 2026-10-06T20:13: DONE. `lin_mul`/`num_mul`: substitute (`mobiusSubst_C` via `AlgHom.commutes` + `algebraMap_apply`), `L_γ w_γ = N_γ`, then `simp only [lin, num, Pi.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul]` + `ring`; `mobius_mul` by a 3-step calc with the two inverses; `mobiusSubst_mul`/`_one` by `algHom_ext_of_continuous`.

### [T011] `aeval_lin`, `aeval_num`, `norm_aeval_lin` and 1 more

- **Status**: done   (finished 2026-10-06T20:13) · **File**: `Mobius.lean` · **Depends on**: [T010] · **Type**: proof · **Leaves**: L2.9

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
theorem aeval_lin {x : ι → K} (hx : ∀ i, ‖x i‖ ≤ 1) (i : ι) :
    aeval 1 x hx (lin γ i) = γ i 1 0 * x i + γ i 1 1 := by
  sorry

theorem aeval_num {x : ι → K} (hx : ∀ i, ‖x i‖ ≤ 1) (i : ι) :
    aeval 1 x hx (num γ i) = γ i 0 0 * x i + γ i 0 1 := by
  sorry

theorem norm_aeval_lin (hγ : MultiBounds ρ γ) {x : ι → K} (hx : ∀ i, ‖x i‖ ≤ 1) (i : ι) :
    ‖aeval 1 x hx (lin γ i)‖ = 1 := by
  sorry

/-- **The pointwise formula** `w_{γ,i}(x) = (a_i x_i + b_i)/(c_i x_i + d_i)` on the closed unit
polydisc. Source: roadmap §1.2.5; [Buz07, Lemma 8.1(b)]. -/
theorem aeval_mobius (hγ : MultiBounds ρ γ) {x : ι → K} (hx : ∀ i, ‖x i‖ ≤ 1) (i : ι) :
    aeval 1 x hx (mobius γ i) = (γ i 0 0 * x i + γ i 0 1) / (γ i 1 0 * x i + γ i 1 1) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L2.9** `aeval_lin`, `aeval_num`, `norm_aeval_lin`, `aeval_mobius`, `norm_aeval_mobius_le_one`,
  `aeval_mobiusSubst` — [RM] §1.2.5 "Prove the pointwise formula `(f ∣_κ γ)(z) = j_κ(γ)(z) · f(w_γ(z))`
  for `z` in the closed unit polydisc (that roadmap's §4.1.3–4)". Sketch: substrate, *the pointwise
  formula*; `norm_aeval_lin`: `‖c x_i + d‖ = 1` by isosceles (L1.4's argument on `K`). The last two
  are discharged in the skeleton. Attacks: [2] `x = 0`: `w(0) = b/d` ✓. [3] `‖x‖ ≤ 1` needed for
  `aeval` and for `‖c x + d‖ = 1` ✓. [4] [Buz07, Lemma 8.1(b)] "sends `(z_i)` to
  `((a_i z_i + b_i)/(c_i z_i + d_i))`" ✓. SURVIVED.

#### Mathlib lemmas needed

`MvPowerSeries.Restricted.aeval_X`, `AlgHom.commutes`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, `div_eq_mul_inv`, `map_mul`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2 preamble, §1.2.1, §1.2.4, §1.2.5; [Buz07, Lemma 8.1, p. 59]; [Jac03, Lemma 2.7, p. 30]; [RAG] `TateAlgebra/Eval.lean`, `Restricted/Units.lean`; [SRC] `QMF/Weight/03_SlashAction.lean`, `TateFredholm/06_WeightGenFun.lean` (proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D2** the series algebra is for multi-matrices `γ : ι → Matrix (Fin 2) (Fin 2) K`; one and several places are instances.

#### Progress

- 2026-10-06T20:13: DONE. `aeval_C_self` (private) + `aeval_X`; `aeval_mobius` via `eq_inv_of_mul_eq_one_right` on the evaluated `lin · linInv = 1`; `norm_aeval_lin` isosceles.

### [T012] `norm_le_one`, `mono`, `rowBound_C` and 4 more

- **Status**: done   (finished 2026-10-06T20:13) · **File**: `Mobius.lean` · **Depends on**: [T011] · **Type**: proof · **Leaves**: L2.10, L2.11

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
theorem RowBound.norm_le_one (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) {f : Restricted K (1 : ι → ℝ)}
    (hf : RowBound σ f) : ‖f‖ ≤ 1 := by
  sorry

theorem RowBound.mono {σ' : ℝ} (hσ0 : 0 ≤ σ) (hσσ' : σ ≤ σ') {f : Restricted K (1 : ι → ℝ)}
    (hf : RowBound σ f) : RowBound σ' f := by
  sorry

theorem rowBound_C (hσ0 : 0 ≤ σ) {a : K} (ha : ‖a‖ ≤ 1) : RowBound σ (C (1 : ι → ℝ) a) := by
  sorry

theorem RowBound.smul {f : Restricted K (1 : ι → ℝ)} (hf : RowBound σ f) {a : K} (ha : ‖a‖ ≤ 1) :
    RowBound σ (a • f) := by
  sorry

/-- Row bounds are closed under products: the ultrametric convolution with `|t₁| + |t₂| = |t|`.
Source: roadmap §1.2.4 ("products of series with this property have it"). -/
theorem RowBound.mul (hσ0 : 0 ≤ σ) {f g : Restricted K (1 : ι → ℝ)} (hf : RowBound σ f)
    (hg : RowBound σ g) : RowBound σ (f * g) := by
  sorry

theorem RowBound.pow (hσ0 : 0 ≤ σ) {f : Restricted K (1 : ι → ℝ)} (hf : RowBound σ f) (n : ℕ) :
    RowBound σ (f ^ n) := by
  sorry

theorem RowBound.prod (hσ0 : 0 ≤ σ) {κ : Type*} (s : Finset κ) {f : κ → Restricted K (1 : ι → ℝ)}
    (hf : ∀ k ∈ s, RowBound σ (f k)) : RowBound σ (∏ k ∈ s, f k) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L2.10** `RowBound` (def), `RowBound.norm_le_one`, `.mono`, `rowBound_C`, `rowBound_one`, `.smul` —
  [RM] §1.2.4 (decision D11). Sketch: `‖coeff_t f‖ ≤ σ^{|t|} ≤ 1` and [RAG]
  `norm_le_iff_forall_norm_coeff_le` ✓; `σ^n ≤ σ'^n` (`pow_le_pow_left₀`); `C a` has only the
  constant coefficient; `‖a • f‖`-coefficients scale by `‖a‖ ≤ 1` ([RAG] `val_smul` ✓). Attacks: [1]
  `RowBound σ (X i)` is FALSE for `σ < 1` (coefficient `1` at degree `1`) — so `RowBound` is not an
  ideal-like property and `rowBound_mobius` genuinely needs `‖a‖ ≤ σ` ✓ (as the roadmap says). [2]
  `σ = 0`: `RowBound 0 f ↔ f` is a constant of norm `≤ 1` ✓ (`0^0 = 1`). [3] `.norm_le_one` needs
  `σ ≤ 1` ✓. SURVIVED.

- **L2.11** `RowBound.mul`, `.pow`, `.prod` — [RM] §1.2.4 "products of series with this property have
  it". Sketch: substrate, *row bounds*. Discharge: `MvPowerSeries.coeff_mul` ✓ (needs `DecidableEq ι`;
  the statement is stated without, so `classical` inside the proof), `Finsupp.mem_antidiagonal` ✓,
  `map_add` of `Finsupp.degree` ✓ (an `AddMonoidHom`), `pow_add`,
  `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` *(ticket; name to confirm — fallback
  `Finset.induction` with `norm_add_le_max`)*, `Finset.prod_induction`. Attacks: [2] `s = ∅`: `∏ = 1`
  ✓ `rowBound_one`. [3] `0 ≤ σ` needed for `σ^{|t₁|} σ^{|t₂|} ≥ 0` manipulations ✓. SURVIVED.

#### Mathlib lemmas needed

`MvPowerSeries.Restricted.norm_le_iff_forall_norm_coeff_le`, `MvPowerSeries.coeff_mul`, `Finsupp.mem_antidiagonal`, `Finsupp.degree`, `map_add`, `pow_add`, `pow_le_pow_left₀`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `Finset.prod_induction`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2 preamble, §1.2.1, §1.2.4, §1.2.5; [Buz07, Lemma 8.1, p. 59]; [Jac03, Lemma 2.7, p. 30]; [RAG] `TateAlgebra/Eval.lean`, `Restricted/Units.lean`; [SRC] `QMF/Weight/03_SlashAction.lean`, `TateFredholm/06_WeightGenFun.lean` (proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D11** row bounds are the predicate `RowBound σ f := ∀ t, ‖coeff t f‖ ≤ σ ^ t.degree`.

#### Progress

- 2026-10-06T20:13: DONE. `RowBound.mul` by `MvPowerSeries.coeff_mul` + `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` + additivity of `Finsupp.degree`; `pow` by induction, `prod` by `Finset.prod_induction`.

### [CLEANUP-5] `/cleanup` of `Mobius.lean` (cadence: three proof tickets)

- **Status**: done   (finished 2026-10-06T20:13) · **File**: `Mobius.lean` · **Depends on**: [T012] · **Type**: cleanup

Run `/cleanup` on `PhD/TauCeti/Code/OverconvergentForms/Weight/Mobius.lean` (cadence: three proof tickets). Style audit + golf to mathlib standards; add `omit … in` where the skeleton's 'automatically included section variable(s) unused' warnings point; check docstrings cite the roadmap clause and the source; no statement changes without a B2 entry in `b2_log.jsonl`.

#### Progress

- 2026-10-06T20:13: DONE inline: omit annotations, no warning.

### [T013] `rowBound_lin`, `rowBound_linInv`, `rowBound_num` and 1 more

- **Status**: done   (finished 2026-10-06T20:13) · **File**: `Mobius.lean` · **Depends on**: [CLEANUP-5] · **Type**: proof · **Leaves**: L2.12

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
theorem rowBound_lin (hγ : MultiBounds ρ γ) (hρσ : ρ ≤ σ) (i : ι) : RowBound σ (lin γ i) := by
  sorry

theorem rowBound_linInv (hγ : MultiBounds ρ γ) (hρσ : ρ ≤ σ) (i : ι) :
    RowBound σ (linInv γ i) := by
  sorry

theorem rowBound_num (hγ : MultiBounds ρ γ) (hρσ : ρ ≤ σ) {i : ι} (ha : ‖γ i 0 0‖ ≤ σ) :
    RowBound σ (num γ i) := by
  sorry

/-- **The row bound of the Möbius series**: `‖coeff_l w_{γ,i}‖ ≤ σ^l` when `‖a_i‖ ≤ σ` and `ρ ≤ σ`
(the constant term `b_i/d_i` only needs `≤ 1 = σ^0`). Source: roadmap §1.2.4. -/
theorem rowBound_mobius (hγ : MultiBounds ρ γ) (hρσ : ρ ≤ σ) {i : ι} (ha : ‖γ i 0 0‖ ≤ σ) :
    RowBound σ (mobius γ i) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L2.12** `rowBound_lin`, `rowBound_linInv`, `rowBound_num`, `rowBound_mobius` — [RM] §1.2.4 "the
  row bound: if `‖a‖ ≤ σ` with `ρ ≤ σ < 1` then […] since `‖coeff_l w_{γ,i}‖ ≤ σ^l` for `l ≥ 1` (from
  `‖c‖ ≤ ρ ≤ σ` and `‖a‖ ≤ σ`)". Sketch: substrate, *row bounds*: `lin`'s coefficients `d` (deg 0),
  `c` (deg 1); `linInv`'s `d⁻¹(−c/d)^m` (deg `m`) of norm `‖c‖^m ≤ σ^m`; `num`'s `b`, `a`; product by
  L2.11. Attacks: [3] the roadmap's `σ < 1` is not needed for the bound itself (only `0 ≤ ρ ≤ σ`) ✓
  stated without `σ < 1` — a harmless generalisation (at `σ ≥ 1` the bound is weaker than
  integrality). `‖a‖ ≤ σ` is necessary (L2.10 [1]) ✓. [4] [Jac03, Lemma 2.7] "every coefficient of
  `x` is divisible by `3`" is the case `σ = ‖3‖` ✓. SURVIVED.

#### Mathlib lemmas needed

`Finsupp.degree_single`, `pow_le_pow_left₀`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2 preamble, §1.2.1, §1.2.4, §1.2.5; [Buz07, Lemma 8.1, p. 59]; [Jac03, Lemma 2.7, p. 30]; [RAG] `TateAlgebra/Eval.lean`, `Restricted/Units.lean`; [SRC] `QMF/Weight/03_SlashAction.lean`, `TateFredholm/06_WeightGenFun.lean` (proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D11** row bounds are the predicate `RowBound σ f := ∀ t, ‖coeff t f‖ ≤ σ ^ t.degree`.

#### Progress

- 2026-10-06T20:13: DONE. Coefficientwise from `coeff_lin`/`coeff_num`/`coeff_linInv` (degree of `single i m` is `m`); `rowBound_mobius` = `RowBound.mul`.

### [CLEANUP-6] `/cleanup` of `Mobius.lean` (final for the file)

- **Status**: done   (finished 2026-10-06T20:13) · **File**: `Mobius.lean` · **Depends on**: [T013] · **Type**: cleanup

Run `/cleanup` on `PhD/TauCeti/Code/OverconvergentForms/Weight/Mobius.lean` (final for the file). Style audit + golf to mathlib standards; add `omit … in` where the skeleton's 'automatically included section variable(s) unused' warnings point; check docstrings cite the roadmap clause and the source; no statement changes without a B2 entry in `b2_log.jsonl`.

#### Progress

- 2026-10-06T20:13: DONE inline: final pass on Mobius.lean — 21 `omit` annotations, docstring reflowed to 100 columns, `runLinter` passes, no warning, axioms std on all 16 checked capstones (no sorryAx).

### [T014] `norm_det_le_one_of_forall_norm_le_one`, `norm_adjugate_apply_le_one`, `norm_mulVec_apply_le_one`

- **Status**: done   (finished 2026-10-06T20:30) · **File**: `Identity.lean` · **Depends on**: [T007] · **Type**: proof · **Leaves**: L3.1

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- Over an ultrametric normed ring, an integral matrix has integral determinant. -/
theorem norm_det_le_one_of_forall_norm_le_one {A : Matrix n n R} (hA : ∀ i j, ‖A i j‖ ≤ 1) :
    ‖A.det‖ ≤ 1 := by
  sorry

/-- Over an ultrametric normed ring, an integral matrix has integral adjugate. -/
theorem norm_adjugate_apply_le_one {A : Matrix n n R} (hA : ∀ i j, ‖A i j‖ ≤ 1) (i j : n) :
    ‖A.adjugate i j‖ ≤ 1 := by
  sorry

/-- Over an ultrametric normed ring, an integral matrix maps the unit polydisc into itself. -/
theorem norm_mulVec_apply_le_one {A : Matrix n n R} (hA : ∀ i j, ‖A i j‖ ≤ 1) {v : n → R}
    (hv : ∀ j, ‖v j‖ ≤ 1) (i : n) : ‖(A.mulVec v) i‖ ≤ 1 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L3.1** `Matrix.norm_det_le_one_of_forall_norm_le_one`, `Matrix.norm_adjugate_apply_le_one`,
  `Matrix.norm_mulVec_apply_le_one` — the "determinant calculation" needs `det`, `adj` and `M v`
  integral. Sketch: `Matrix.det_apply` ✓ (sum over permutations of signed products),
  `Finset.norm_prod_le`-type bounds and the ultrametric sum bound; `Matrix.adjugate_apply` ✓
  (`adjugate A i j = det (A.updateRow j (Pi.single i 1))`, an integral matrix); `Matrix.mulVec`,
  `Matrix.dotProduct` ✓ ultrametric sum. Attacks: [2] `n` empty: `det = 1`, `‖1‖ = 1 ≤ 1` needs
  `NormOneClass` ✓ in the hypotheses. [3] `NormOneClass R` is necessary (`‖1‖ ≤ 1` is used) ✓. [5]
  Mathlib names grep'd ✓ (`det_apply` is `Matrix.det_apply`). SURVIVED.

#### Mathlib lemmas needed

`Matrix.det_apply`, `Matrix.adjugate_apply`, `Matrix.mulVec`, `Matrix.dotProduct`, `Finset.norm_prod_le`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `Equiv.Perm.sign`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2.3; [Buz07, proof of Proposition 8.3, pp. 63–64]; PFA roadmap §4.1.5; [RAG] `Restricted/PowerSeries/MulWeierstrassPrep.lean`, `Restricted/Sum.lean`, `Restricted/Iso.lean`; [SRC] `QMF/Weight/04_Char.lean` (`eq_zero_of_forall_evalAt_eq_zero`, one variable, proof idea only).

#### Generality decision

Binding decisions of `plan.md`: **D8** namespace `AutomorphicForm`; Tate-algebra seams in `MvPowerSeries.Restricted` / `PowerSeries.Restricted` / `Matrix`.

#### Progress

- 2026-10-06T20:30: DONE. `det_apply` + ultrametric finite sum, the sign handled by `Int.units_eq_one_or`; adjugate via `adjugate_apply` (an integral `updateRow` matrix); `mulVec` via `dotProduct` + ultrametric sum. Axioms std.

### [T015] `exists_isMulDistinguished_of_ne_zero`, `aeval_ne_zero_of_isUnit`, `eq_zero_of_forall_aeval_eq_zero`

- **Status**: done   (finished 2026-10-06T20:30) · **File**: `Identity.lean` · **Depends on**: [T014] · **Type**: proof · **Leaves**: L3.2, L3.3

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- A nonzero restricted series over a field is Martin-distinguished at its greatest index
achieving the Gauss norm. Source: [Mar16, Definition 1.24]; BGR 5.2.1. -/
theorem exists_isMulDistinguished_of_ne_zero {f : PowerSeries.Restricted K 1} (hf : f ≠ 0) :
    ∃ s, IsMulDistinguished 1 f.1 s := by
  sorry

/-- A unit of the Tate algebra does not vanish at any point of the closed unit disc. -/
theorem aeval_ne_zero_of_isUnit {e : PowerSeries.Restricted K 1} (he : IsUnit e) {x : K}
    (hx : ‖x‖ ≤ 1) :
    aeval (fun _ : Unit => (1 : ℝ)) (fun _ => x) (fun _ => hx) e ≠ 0 := by
  sorry

/-- **Strassmann's theorem**: a restricted power series vanishing at infinitely many points of the
closed unit disc is zero. Source: PFA roadmap §4.1.5 ("obtained from Weierstrass preparation:
`f = P · u` with `P` a polynomial and `u` a unit of `K⟨X⟩`, so the zeros of `f` in the closed disc
are the roots of `P`"); [Buz07, p. 64] ("a function on a closed `1`-ball that vanishes at
infinitely many points […] is identically zero"). -/
theorem eq_zero_of_forall_aeval_eq_zero (Z : Set K) (hZ : Z.Infinite) (hZ1 : ∀ z ∈ Z, ‖z‖ ≤ 1)
    {f : PowerSeries.Restricted K 1}
    (hf : ∀ z (hz : z ∈ Z),
      aeval (fun _ : Unit => (1 : ℝ)) (fun _ => z) (fun _ => hZ1 z hz) f = 0) :
    f = 0 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L3.2** `PowerSeries.Restricted.exists_isMulDistinguished_of_ne_zero`, `aeval_ne_zero_of_isUnit`
  — [RAG] `IsMulDistinguished` (Martin's Definition 1.24) and the unit/evaluation compatibility.
  Sketch: substrate, *Strassmann*, first and third sentences. Discharge: [RAG]
  `PowerSeries.Restricted.exists_greatest_achievesGaussNorm` ✓ (`AchievesGaussNorm … k₀ ∧ ∀ k > k₀,
  ‖coeff k q‖ c^k < ‖q‖`), [RAG] `IsUnit.isNormMulUnit` ✓, `IsMulDistinguished` fields; `map_mul`,
  `map_one` of `aeval`, `mul_ne_zero_iff`/`IsUnit.ne_zero`. Attacks: [2] `f` a nonzero constant:
  `k₀ = 0`, distinguished of order `0` ✓ (then `ω = 1`). [3] `K` a field is essential for
  "coefficient ≠ 0 ⇒ norm-multiplicative unit" ✓ (over a ring, Strassmann fails: `𝔽_p[[t]]`…). [5] the
  radius is `1` and `PowerSeries.Restricted K 1 = MvPowerSeries.Restricted K (σ := Unit) (fun _ ↦ 1)`
  ([RAG] `abbrev`); the `aeval` in the statement is at `fun _ : Unit => (1 : ℝ)` — the `Fact (∀ i, 0 < c i)`
  instance is [RAG] `PowerSeries/GaussNorm.lean:102` from `Fact (0 < 1)` *(ticket: a local instance
  `⟨one_pos⟩` may be needed)*. SURVIVED.

- **L3.3** `PowerSeries.Restricted.eq_zero_of_forall_aeval_eq_zero` — PFA §4.1.5 (quoted). Sketch:
  substrate, *Strassmann*. Discharge: L3.2, [RAG] `weierstrassPreparation_exists_of_isMulDistinguished`
  ✓ (hypotheses `[CompleteSpace A] [NormOneClass A]`, `IsMulDistinguished c g.1 s`), [RAG]
  `aeval_toRestricted` ✓ (`aeval (toRestricted p) = p.aeval x`; here `Polynomial.toRestricted` for
  one variable — [RAG] `Polynomial.toRestricted` ✓ with `val_toRestricted`), `Polynomial.eq_zero_of_infinite_isRoot`
  ✓, `Polynomial.Monic.ne_zero` ✓, `Set.Infinite.mono`. Attacks: [1] is the theorem false over a
  non-complete `K`? Completeness is needed for `aeval` and for the preparation theorem ✓ hypothesis
  present. [2] `Z` infinite but `f = 0` ✓ trivial. [3] `‖z‖ ≤ 1` is needed for evaluation ✓; `Z`
  infinite is necessary (a nonzero polynomial vanishes on a finite set) ✓. [4] [Buz07, p. 64]: "a
  function on a closed `1`-ball that vanishes at infinitely many points, and hence it is identically
  zero" ✓ exactly. [5] verified names; composition is `3` lemmas plus L3.2 ✓. SURVIVED.

⚠ The `Fact (∀ i : Unit, 0 < (fun _ ↦ (1:ℝ)) i)` instance comes from [RAG] `PowerSeries/GaussNorm.lean:102` via `Fact (0 < 1)`; add `haveI : Fact ((0:ℝ) < 1) := ⟨one_pos⟩` locally if search stalls.

#### Mathlib lemmas needed

`PowerSeries.Restricted.exists_greatest_achievesGaussNorm`, `IsUnit.isNormMulUnit`, `PowerSeries.Restricted.weierstrassPreparation_exists_of_isMulDistinguished`, `MvPowerSeries.Restricted.aeval_toRestricted`, `Polynomial.toRestricted`, `Polynomial.eq_zero_of_infinite_isRoot`, `Polynomial.Monic.ne_zero`, `Set.Infinite.mono`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2.3; [Buz07, proof of Proposition 8.3, pp. 63–64]; PFA roadmap §4.1.5; [RAG] `Restricted/PowerSeries/MulWeierstrassPrep.lean`, `Restricted/Sum.lean`, `Restricted/Iso.lean`; [SRC] `QMF/Weight/04_Char.lean` (`eq_zero_of_forall_evalAt_eq_zero`, one variable, proof idea only).

#### Generality decision

Binding decisions of `plan.md`: **D8** namespace `AutomorphicForm`; Tate-algebra seams in `MvPowerSeries.Restricted` / `PowerSeries.Restricted` / `Matrix`.

#### Progress

- 2026-10-06T20:30: DONE. Strassmann: greatest achieving index (`exists_greatest_achievesGaussNorm`, needs a local `Fact ((0:ℝ) < 1)`) ⇒ `IsMulDistinguished`; RAG `weierstrassPreparation_exists_of_isMulDistinguished` ⇒ `f = e · ω`; units do not vanish (`IsUnit.map`); polynomial evaluation via `Polynomial.ringHom_ext` on `(aeval).toRingHom.comp toRestricted`; `Polynomial.eq_zero_of_infinite_isRoot`. New public lemma `MvPowerSeries.Restricted.aeval_C` added to Mobius.lean. Axioms std.

### [T016] `eq_zero_of_isEmpty_of_aeval_eq_zero`, `aeval_renameEquiv`, `sliceNone` and 1 more

- **Status**: done   (finished 2026-10-06T20:30) · **File**: `Identity.lean` · **Depends on**: [T015] · **Type**: proof · **Leaves**: L3.4, L3.5

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- Over an empty index type a restricted series is its constant coefficient, and vanishing at
the (unique) point of the polydisc makes it zero. -/
theorem eq_zero_of_isEmpty_of_aeval_eq_zero [IsEmpty σ] {f : Restricted K (1 : σ → ℝ)}
    (hf : aeval 1 (fun _ => (0 : K)) (fun _ => by simp) f = 0) : f = 0 := by
  sorry

/-- Evaluation after renaming the variables along a bijection. -/
theorem aeval_renameEquiv {τ : Type*} (e : σ ≃ τ) {x : τ → K} (hx : ∀ j, ‖x j‖ ≤ 1)
    (f : Restricted K (1 : σ → ℝ)) :
    aeval 1 x hx (renameEquiv K e f) = aeval 1 (x ∘ e) (fun i => hx (e i)) f := by
  sorry

/-- **Slicing**: substitute the one-variable `X` for the variable `none` and the constants `y j`
for the variables `some j`, turning a series in `Option τ` variables into a one-variable restricted
series. Source: [Buz07, p. 64] ("fix `z_β ∈ ℤ_p` for `β ≥ 2` and consider the function […] sending
`z_1` to `f(z_1 e_1 + z_2 e_2 + …)`"). -/
noncomputable def sliceNone : Restricted K (1 : Option τ → ℝ) →ₐ[K] PowerSeries.Restricted K 1 :=
  aeval 1
    (fun o => o.elim (PowerSeries.Restricted.X K 1) (fun j => PowerSeries.Restricted.C 1 (y j)))
    (fun o => by
      have := hy
      sorry)

theorem aeval_sliceNone {t : K} (ht : ‖t‖ ≤ 1) (f : Restricted K (1 : Option τ → ℝ)) :
    aeval (fun _ : Unit => (1 : ℝ)) (fun _ => t) (fun _ => ht) (sliceNone y hy f) =
      aeval 1 (fun o => o.elim t y) (fun o => by cases o <;> simp [ht, hy]) f := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L3.4** `eq_zero_of_isEmpty_of_aeval_eq_zero`, `aeval_renameEquiv` — the base case and the
  transport of `Finite.induction_empty_option`. Sketch: [RAG] `isEmptyEquiv` ✓ (`Restricted R c ≃+* R`
  by the constant coefficient, `isEmptyEquiv_apply` ✓) and `aeval` of a constant is the constant
  (`AlgHom.commutes`, [RAG] `algebraMap_apply` ✓); `aeval_renameEquiv` by [RAG]
  `ringHom_ext_of_continuous` ✓ on `C` and `X` ([RAG] `renameEquiv_C`, `renameEquiv_X` ✓,
  `continuous_renameHom` ✓). Attacks: [2] `σ` empty for `aeval_renameEquiv` ✓ trivial. [5] names from
  [RAG] `Sum.lean`/`Iso.lean` ✓ grep'd. SURVIVED.

- **L3.5** `sliceNone` (norm field), `aeval_sliceNone` — [Buz07, p. 64] "consider the function on the
  affinoid unit disc over `L` sending `z_1` to `f(z_1 e_1 + z_2 e_2 + …)`". Sketch: `‖X‖ = 1`, `‖C y‖ =
  ‖y‖ ≤ 1` ([RAG] `norm_X` ✓, `norm_C` ✓); `aeval_sliceNone` is L2.1 `aeval_aeval` with
  `aeval (fun _ => t) X = t`, `aeval (fun _ => t) (C y) = y`. Attacks: [2] `τ` empty: the slice is
  `renameEquiv` to one variable ✓ consistent. [3] `hy` is needed for `C (y j)` to be substitutable
  (norm `≤ 1`) — the roadmap's "with the others fixed in `ℤ_p`" ✓. SURVIVED.

#### Mathlib lemmas needed

`MvPowerSeries.Restricted.isEmptyEquiv`, `MvPowerSeries.Restricted.isEmptyEquiv_apply`, `MvPowerSeries.Restricted.ringHom_ext_of_continuous`, `MvPowerSeries.Restricted.renameEquiv_X`, `MvPowerSeries.Restricted.renameEquiv_C`, `MvPowerSeries.Restricted.continuous_renameHom`, `MvPowerSeries.Restricted.norm_X`, `MvPowerSeries.Restricted.norm_C`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2.3; [Buz07, proof of Proposition 8.3, pp. 63–64]; PFA roadmap §4.1.5; [RAG] `Restricted/PowerSeries/MulWeierstrassPrep.lean`, `Restricted/Sum.lean`, `Restricted/Iso.lean`; [SRC] `QMF/Weight/04_Char.lean` (`eq_zero_of_forall_evalAt_eq_zero`, one variable, proof idea only).

#### Generality decision

Binding decisions of `plan.md`: **D8** namespace `AutomorphicForm`; Tate-algebra seams in `MvPowerSeries.Restricted` / `PowerSeries.Restricted` / `Matrix`.

#### Progress

- 2026-10-06T20:30: DONE — REPLANNED (inline /develop --continue): the Option-slicing helpers `sliceNone`, `aeval_sliceNone` (and T017's `coeffNone`, `coeff_coeffNone`, `eq_zero_of_forall_coeffNone_eq_zero`, `coeff_sliceNone`, T018's `eq_zero_of_forall_aeval_eq_zero_option`) were replaced by the iterated-ring route through RAG `sumEquiv : K⟨X ⊕ Y⟩ ≃+* K⟨Y⟩⟨X⟩` (BGR 6.1.1/7, roadmap RAG §1.1.3): the coefficient identity `coeff_k(slice) = (coeffNone_k)(y)` (a long monomial computation) becomes `val_map` + `MvPowerSeries.coeff_map`, and the evaluation compatibility becomes one `ringHom_ext_of_continuous` (`aeval_map_sumEquiv`). Same mathematics (Buzzard p. 64, one variable at a time), no consumer outside Identity.lean. `eq_zero_of_isEmpty_of_aeval_eq_zero` (constant coefficient, `Subsingleton (σ →₀ ℕ)`) and `aeval_renameEquiv` (ring-hom ext) as planned. Axioms std.

### [CLEANUP-7] `/cleanup` of `Identity.lean` (cadence: three proof tickets)

- **Status**: done   (finished 2026-10-06T20:30) · **File**: `Identity.lean` · **Depends on**: [T016] · **Type**: cleanup

Run `/cleanup` on `PhD/TauCeti/Code/OverconvergentForms/Weight/Identity.lean` (cadence: three proof tickets). Style audit + golf to mathlib standards; add `omit … in` where the skeleton's 'automatically included section variable(s) unused' warnings point; check docstrings cite the roadmap clause and the source; no statement changes without a B2 entry in `b2_log.jsonl`.

#### Progress

- 2026-10-06T20:30: DONE inline: Identity.lean first half — unused simp arguments removed, omit annotations.

### [T017] `coeffNone`, `eq_zero_of_forall_coeffNone_eq_zero`, `coeff_sliceNone`

- **Status**: done   (finished 2026-10-06T20:30) · **File**: `Identity.lean` · **Depends on**: [CLEANUP-7] · **Type**: proof · **Leaves**: L3.6

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- The coefficient of `X_{none}^k`, a restricted series in the remaining variables: the
`(k, t)`-coefficient of `f` at the multi-index `t`. -/
noncomputable def coeffNone (k : ℕ) :
    Restricted K (1 : Option τ → ℝ) →ₗ[K] Restricted K (1 : τ → ℝ) where
  toFun f := ⟨fun t => coeff (Finsupp.single none k + t.mapDomain Option.some) f.1, by sorry⟩
  map_add' f g := by sorry
  map_smul' a f := by sorry

/-- A series in `Option τ` variables is determined by its coefficients in the variable `none`. -/
theorem eq_zero_of_forall_coeffNone_eq_zero {f : Restricted K (1 : Option τ → ℝ)}
    (hf : ∀ k, coeffNone K k f = 0) : f = 0 := by
  sorry

/-- The coefficients of a slice are the evaluations of the coefficients in `none`. -/
theorem coeff_sliceNone (k : ℕ) (f : Restricted K (1 : Option τ → ℝ)) :
    coeff (Finsupp.single () k) (sliceNone y hy f).1 = aeval 1 y hy (coeffNone K k f) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L3.6** `coeffNone` (fields: restrictedness, `map_add'`, `map_smul'`), `coeff_coeffNone`,
  `eq_zero_of_forall_coeffNone_eq_zero`, `coeff_sliceNone` — the coefficient of `X_{none}^k` as a
  series in the remaining variables, and its two properties. Sketch: restrictedness:
  `t ↦ single none k + mapDomain some t` is injective (`Finsupp.mapDomain_injective` ✓
  `Option.some_injective`), so `‖coeff_{…} f‖ → 0` cofinitely in `t` ([RAG] `tendsto_norm_coeff_cofinite`
  ✓ composed with an injection, `Filter.Tendsto.comp` + `Function.Injective.tendsto_cofinite` ✓);
  linearity coefficientwise ([RAG] `val_add`, `val_smul` ✓). `eq_zero_of_forall_coeffNone_eq_zero`:
  every `m : Option τ →₀ ℕ` is `single none (m none) + mapDomain some (m.comapDomain some …)`
  (`Finsupp.ext`, case on `o`) *(ticket: use `Finsupp.comapDomain` or `Finsupp.filter`/`subtypeDomain`;
  alternatively `Finsupp.equivFunOnFinite` is not available as `τ` is not finite — use
  `Finsupp.mapDomain_apply` with injectivity)*. `coeff_sliceNone`: `sliceNone y = map (aeval y) ∘
  (sumEquiv ∘ renameEquiv)` as continuous ring homs agreeing on generators, then [RAG] `val_map` ✓;
  or directly: both sides are continuous `K`-linear in `f` and agree on monomials
  (`aeval` of a monomial, `coeff` of a monomial). Attacks: [1] could `coeffNone` fail to be
  restricted? Only if the coefficients of `f` did not tend to `0` along the injective reindexing ✓
  they do. [2] `k` larger than every degree of `f` in `none`: `coeffNone k f = 0` ✓. [3]
  `[CompleteSpace K]` is not needed for `coeffNone` itself but is in the section variables — the
  cleanup ticket may `omit` it ✓. SURVIVED.

#### Mathlib lemmas needed

`Finsupp.mapDomain_injective`, `Option.some_injective`, `Function.Injective.tendsto_cofinite`, `MvPowerSeries.Restricted.tendsto_norm_coeff_cofinite`, `MvPowerSeries.Restricted.val_map`, `Finsupp.ext`, `Finsupp.mapDomain_apply`, `Finsupp.single_apply`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2.3; [Buz07, proof of Proposition 8.3, pp. 63–64]; PFA roadmap §4.1.5; [RAG] `Restricted/PowerSeries/MulWeierstrassPrep.lean`, `Restricted/Sum.lean`, `Restricted/Iso.lean`; [SRC] `QMF/Weight/04_Char.lean` (`eq_zero_of_forall_evalAt_eq_zero`, one variable, proof idea only).

#### Generality decision

Binding decisions of `plan.md`: **D8** namespace `AutomorphicForm`; Tate-algebra seams in `MvPowerSeries.Restricted` / `PowerSeries.Restricted` / `Matrix`.

#### Progress

- 2026-10-06T20:30: DONE via the replan of T016: new public helpers `MvPowerSeries.Restricted.map_C`, `map_X`, `coeff_map`, `continuous_map` (norm-nonincreasing coefficient maps) replace `coeffNone` and its lemmas.

### [T018] `eq_zero_of_forall_aeval_eq_zero_option`, `eq_zero_of_forall_aeval_eq_zero`

- **Status**: done   (finished 2026-10-06T20:30) · **File**: `Identity.lean` · **Depends on**: [T017] · **Type**: proof · **Leaves**: L3.7, L3.8

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- The induction step: vanishing on `Z^{Option τ}` reduces to vanishing on `Z^τ` of every
coefficient in the variable `none`, by Strassmann's theorem on the slices. -/
theorem eq_zero_of_forall_aeval_eq_zero_option {τ : Type*} (Z : Set K) (hZ : Z.Infinite)
    (hZ1 : ∀ z ∈ Z, ‖z‖ ≤ 1)
    (ih : ∀ g : Restricted K (1 : τ → ℝ),
      (∀ y (hy : ∀ j, y j ∈ Z), aeval 1 y (fun j => hZ1 _ (hy j)) g = 0) → g = 0)
    {f : Restricted K (1 : Option τ → ℝ)}
    (hf : ∀ x (hx : ∀ o, x o ∈ Z), aeval 1 x (fun o => hZ1 _ (hx o)) f = 0) : f = 0 := by
  sorry

/-- **Strassmann's theorem**: a restricted power series vanishing at infinitely many points of the
closed unit disc is zero. Source: PFA roadmap §4.1.5 ("obtained from Weierstrass preparation:
`f = P · u` with `P` a polynomial and `u` a unit of `K⟨X⟩`, so the zeros of `f` in the closed disc
are the roots of `P`"); [Buz07, p. 64] ("a function on a closed `1`-ball that vanishes at
infinitely many points […] is identically zero"). -/
theorem eq_zero_of_forall_aeval_eq_zero (Z : Set K) (hZ : Z.Infinite) (hZ1 : ∀ z ∈ Z, ‖z‖ ≤ 1)
    {f : PowerSeries.Restricted K 1}
    (hf : ∀ z (hz : z ∈ Z),
      aeval (fun _ : Unit => (1 : ℝ)) (fun _ => z) (fun _ => hZ1 z hz) f = 0) :
    f = 0 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L3.7** `eq_zero_of_forall_aeval_eq_zero_option` — the induction step (substrate, *several
  variables*). Sketch: for `y ∈ Z^τ`, `aeval_sliceNone` + `hf` give `sliceNone y f` vanishing on `Z`;
  L3.3 gives `sliceNone y f = 0`; `coeff_sliceNone` gives `aeval y (coeffNone k f) = 0`; `ih` gives
  `coeffNone k f = 0`; L3.6 concludes. Attacks: [1] composition: could all `coeffNone k f` vanish with
  `f ≠ 0`? No (L3.6's last lemma) ✓. [3] `ih` is stated for the SAME `Z` ✓ (the induction is over the
  variable type with `Z` fixed). [4] [Buz07, p. 64] "fix `z_β ∈ ℤ_p` for `β ≥ 2` […] let `z_2` vary, and
  so on" ✓ this is the induction. SURVIVED.

- **L3.8** `MvPowerSeries.Restricted.eq_zero_of_forall_aeval_eq_zero` — [RM] §1.2.3 (quoted).
  Sketch: `Finite.induction_empty_option` ✓ with `P σ := ∀ f : Restricted K (1 : σ → ℝ), (vanishing
  on Z^σ) → f = 0`; `of_equiv` by L3.4 `aeval_renameEquiv` (transport `f` along `renameEquiv K e.symm`
  and `x ∘ e`); `h_empty` by L3.4; `h_option` by L3.7. Attacks: [1] universe: `Finite.induction_empty_option`
  has `P : Type u → Prop` — `σ : Type*` ✓ the statement is universe-polymorphic in `σ` alone. [2]
  `σ = Unit`: recovers Strassmann ✓ (through `Option PEmpty ≃ Unit`). [3] `[Finite σ]` is necessary
  (the roadmap's `I_𝔭` is finite) ✓; `Z` infinite necessary (L3.3). [4] matches the roadmap's "one
  variable at a time" ✓. SURVIVED.

#### Mathlib lemmas needed

`Finite.induction_empty_option`, `Equiv.optionEquivSumPUnit`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2.3; [Buz07, proof of Proposition 8.3, pp. 63–64]; PFA roadmap §4.1.5; [RAG] `Restricted/PowerSeries/MulWeierstrassPrep.lean`, `Restricted/Sum.lean`, `Restricted/Iso.lean`; [SRC] `QMF/Weight/04_Char.lean` (`eq_zero_of_forall_evalAt_eq_zero`, one variable, proof idea only).

#### Generality decision

Binding decisions of `plan.md`: **D6** `Embeddings.exists_integralBasis` is a Prop field; `[CharZero K]` where the identity theorem is used; **D8** namespace `AutomorphicForm`; Tate-algebra seams in `MvPowerSeries.Restricted` / `PowerSeries.Restricted` / `Matrix`.

#### Progress

- 2026-10-06T20:30: DONE. Induction on `Fin n` (not `Finite.induction_empty_option`: `P` lives on one universe and `Option α ≃ α ⊕ PUnit` would leave `Unit`) with `Fin (n+1) ≃ Fin n ⊕ Unit` (`finSuccEquiv` ∘ `optionEquivSumPUnit`) and transport along `renameEquiv`; the step `eq_zero_of_forall_aeval_eq_zero_sum` specialises the inner variable at `z ∈ Z`, applies the IH to `map (aeval z) (sumEquiv f)`, then Strassmann to each coefficient (the radius `1 ∘ Sum.inr` vs `fun _ => 1` crossed by defeq, `show` before `rw`). Axioms std.

### [T019] `norm_linearForms_le_one`, `aeval_aeval_linearForms`, `eq_zero_of_forall_aeval_mulVec_natCast_eq_zero`

- **Status**: done   (finished 2026-10-06T20:30) · **File**: `Identity.lean` · **Depends on**: [T018] · **Type**: proof · **Leaves**: L3.9, L3.10

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
theorem norm_linearForms_le_one {M : Matrix σ σ K} (hM : ∀ i j, ‖M i j‖ ≤ 1) (i : σ) :
    ‖linearForms M i‖ ≤ 1 := by
  sorry

/-- Evaluating the linear substitution: `(f ∘ M)(y) = f(M y)`. -/
theorem aeval_aeval_linearForms {M : Matrix σ σ K} (hM : ∀ i j, ‖M i j‖ ≤ 1) {y : σ → K}
    (hy : ∀ j, ‖y j‖ ≤ 1) (f : Restricted K (1 : σ → ℝ)) :
    aeval 1 y hy (aeval 1 (linearForms M) (norm_linearForms_le_one hM) f) =
      aeval 1 (M.mulVec y) (Matrix.norm_mulVec_apply_le_one hM hy) f := by
  sorry

/-- **Buzzard's determinant calculation**: in characteristic zero, a restricted series vanishing at
the points `M n`, `n ∈ ℕ^σ`, for an integral matrix `M` with `det M ≠ 0`, is zero: `f ∘ M`
vanishes on `ℕ^σ`, hence is zero; so `f` vanishes on `M(polydisc) ⊇ det(M) · polydisc` by
Cramer's rule, hence on `(det M · ℕ)^σ`, hence is zero. Source: [Buz07, p. 64] ("this contains all
the `L`-points of a small polydisc in `B₁` by a determinant calculation"). -/
theorem eq_zero_of_forall_aeval_mulVec_natCast_eq_zero [CharZero K] {M : Matrix σ σ K}
    (hM : ∀ i j, ‖M i j‖ ≤ 1) (hdet : M.det ≠ 0) {f : Restricted K (1 : σ → ℝ)}
    (hf : ∀ n : σ → ℕ, aeval 1 (M.mulVec fun β => (n β : K))
      (Matrix.norm_mulVec_apply_le_one hM fun β => IsUltrametricDist.norm_natCast_le_one K (n β))
      f = 0) :
    f = 0 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L3.9** `linearForms` (def), `norm_linearForms_le_one`, `aeval_aeval_linearForms` — the linear
  substitution and its evaluation. Sketch: ultrametric sum of `‖M_{iβ} X_β‖ ≤ 1` ([RAG] `norm_C`,
  `norm_X` ✓, `NormMulClass`); L2.1 `aeval_aeval` and `aeval y (∑_β C M_{iβ} X_β) = ∑_β M_{iβ} y_β =
  (M.mulVec y)_i` (`Matrix.mulVec`, `Matrix.dotProduct` ✓, `map_sum`). Attacks: [2] `M = 0`: all
  substitutions `0`, `f(0)` ✓. [3] integrality of `M` is needed for the substitution to exist ✓.
  SURVIVED.

- **L3.10** `eq_zero_of_forall_aeval_mulVec_natCast_eq_zero` — [Buz07, p. 64] "this contains all the
  `L`-points of a small polydisc in `B_1` by a determinant calculation". Sketch: substrate, *Buzzard's
  determinant calculation*. Discharge: L3.8 twice (with `Z = Set.range (Nat.cast : ℕ → K)` and
  `Z' = Set.range (fun n : ℕ => M.det * n)`), `Set.infinite_range_of_injective` ✓, `Nat.cast_injective`
  ✓ (`CharZero`), `mul_right_injective₀` ✓, `IsUltrametricDist.norm_natCast_le_one` ✓, L3.1,
  `Matrix.mul_adjugate` ✓, `Matrix.mulVec_mulVec` ✓, `Matrix.smul_mulVec_assoc`/`Matrix.one_mulVec` ✓,
  L3.9. Attacks: [1] is `[CharZero K]` needed? Over `𝔽_p((t))` the set `ℕ·1` is finite and the route
  fails; the theorem might still hold by another route but the roadmap's `K ⊇ ℚ_p` has
  characteristic `0` ✓ hypothesis kept (B2 lesson C3). [2] `σ` empty: `det = 1`, vacuous ✓. [3]
  `det M ≠ 0` necessary (for `M = 0`, `f = X_1` vanishes at all `M n = 0`) ✓. [4] [Buz07]'s "small
  polydisc" is `det(M) · polydisc` ✓ by Cramer. SURVIVED.

⚠ Long proof (two applications of the several-variable theorem and Cramer); budget it as the biggest leaf of AG1.

#### Mathlib lemmas needed

`Set.infinite_range_of_injective`, `Nat.cast_injective`, `mul_right_injective₀`, `IsUltrametricDist.norm_natCast_le_one`, `Matrix.mul_adjugate`, `Matrix.mulVec_mulVec`, `Matrix.smul_mulVec_assoc`, `Matrix.one_mulVec`, `map_sum`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2.3; [Buz07, proof of Proposition 8.3, pp. 63–64]; PFA roadmap §4.1.5; [RAG] `Restricted/PowerSeries/MulWeierstrassPrep.lean`, `Restricted/Sum.lean`, `Restricted/Iso.lean`; [SRC] `QMF/Weight/04_Char.lean` (`eq_zero_of_forall_evalAt_eq_zero`, one variable, proof idea only).

#### Generality decision

Binding decisions of `plan.md`: **D6** `Embeddings.exists_integralBasis` is a Prop field; `[CharZero K]` where the identity theorem is used.

#### Progress

- 2026-10-06T20:30: DONE. `aeval_aeval_linearForms` from Mobius `aeval_aeval` + a private `aeval_congr` (point-equality transport of the dependent norm proof); Cramer: `x = M (adj M · n)` by `mulVec_mulVec`, `mul_adjugate`, `smul_mulVec`, `one_mulVec`; `choose … using fun i => hx i` (plain `using hx` tries to clear `hx`, on which the goal depends). Axioms std.

### [CLEANUP-8] `/cleanup` of `Identity.lean` (final for the file)

- **Status**: done   (finished 2026-10-06T20:30) · **File**: `Identity.lean` · **Depends on**: [T019] · **Type**: cleanup

Run `/cleanup` on `PhD/TauCeti/Code/OverconvergentForms/Weight/Identity.lean` (final for the file). Style audit + golf to mathlib standards; add `omit … in` where the skeleton's 'automatically included section variable(s) unused' warnings point; check docstrings cite the roadmap clause and the source; no statement changes without a B2 entry in `b2_log.jsonl`.

#### Progress

- 2026-10-06T20:30: DONE inline: final pass on Identity.lean — docstrings reflowed to 100 columns, module docstring lists `aeval_map_sumEquiv`, runLinter passes, no warning, axioms std on the six capstones (no sorryAx).

### [T020] `kappaSlash`, `norm_kappaSlash_apply_le`

- **Status**: done   (finished 2026-10-06T20:43) · **File**: `Action.lean` · **Depends on**: [T013] · **Type**: proof · **Leaves**: L4.1

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- **The weight action** of `γ` on the Tate algebra: `f ∣ γ := j(γ) · (f ∘ w_γ)`, a bounded
`K`-linear operator. Source: roadmap §1.2.5; [Buz07, §10, p. 72]; [Jac03, Definition 1.27]. -/
noncomputable def kappaSlash (γ : S) : Restricted K (1 : ι → ℝ) →L[K] Restricted K (1 : ι → ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f => W.autFactor γ * mobiusSubst (W.bounds γ) f
      map_add' := by sorry
      map_smul' := by sorry }
    1 (by sorry)

/-- The action is norm-decreasing. Source: [Buz07, §10, p. 72]. -/
theorem norm_kappaSlash_apply_le (γ : S) (f : Restricted K (1 : ι → ℝ)) :
    ‖W.kappaSlash γ f‖ ≤ ‖f‖ := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L4.1** `WeightData` (structure, no `sorry`), `rho_nonneg`, `rho_lt_one`, `norm_autFactor_le`
  (discharged), `kappaSlash` (fields `map_add'`, `map_smul'`, the bound), `kappaSlash_apply` (`rfl`),
  `norm_kappaSlash_apply_le` — [RM] §1.2.5 "`f ∣_κ γ := …`, bounded of norm at most `1`, `K`-linear".
  Sketch: substrate. Discharge: `map_add`, `map_smul` of `mobiusSubst`, `mul_add`, `mul_smul_comm`
  ✓; `NormMulClass.norm_mul` ✓ ([RAG] instance), `RowBound.norm_le_one` (L2.10),
  `norm_mobiusSubst_le` (L2.6), `LinearMap.mkContinuous` ✓ (compiled), `LinearMap.mkContinuous_apply`
  ✓. Attacks: [1] the bound constant is `1` — `mkContinuous` needs `‖f x‖ ≤ 1 * ‖x‖` ✓. [3]
  `rowBound_autFactor` (not just `‖j‖ ≤ 1`) is a field because L4.3 needs it; `norm_autFactor_le`
  is derived ✓ minimal. [4] [Buz07]: "a continuous `𝒪(X)`-module homomorphism […] norm-decreasing" ✓.
  SURVIVED.

#### Mathlib lemmas needed

`LinearMap.mkContinuous`, `LinearMap.mkContinuous_apply`, `mul_add`, `mul_smul_comm`, `NormMulClass.norm_mul`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2.4–§1.2.6, §1.2.8, §1.4; [Buz07, §10, pp. 71–72]; [Jac03, Proposition 2.6, Lemma 2.7]; [RAG] `Restricted/Sum.lean` (`renameHom`); [SRC] `QMF/Weight/03_SlashAction.lean` (`kappaSlash_one`, `kappaSlash_mul`, `twist`, `comap`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D1** the carrier is the Tate algebra `MvPowerSeries.Restricted K (1 : ι → ℝ)`; the action is the substitution operator, the kernel array is the theorem `kappaSlash_monomial`; **D3** engine `WeightData` (cocycle a field) / public `AnalyticWeight` (cocycle a theorem).

#### Progress

- 2026-10-06T20:43: Engine record + kappaSlash (LinearMap.mkContinuous, norm ≤ 1) filled; build clean, std axioms.

### [CLEANUP-ALL-1] `/cleanup-all` (before milestone T021 (M1))

- **Status**: done   (finished 2026-10-06T20:43) · **File**: `(project so far)` · **Depends on**: [CLEANUP-6], [CLEANUP-8], [T020] · **Type**: cleanup

Run `/cleanup-all` on `PhD/TauCeti/Code/OverconvergentForms/Weight/` (before milestone T021 (M1)). Inline, as the main agent (memory note `cleanup-inline-no-subagents`). Gates: every touched module builds with no warning; `runLinter` clean; no `sorry`; the four `omit`-able section-variable warnings of the skeleton are gone.

#### Progress

- 2026-10-06T20:43: Level/Dictionary/Mobius/Identity/Action: runLinter passes on each, no line over 100 chars, terminal simps only, omit annotations placed before docstrings.

### [T021] `kappaSlash_one`, `kappaSlash_mul`

- **Status**: done   (finished 2026-10-06T20:43) · **File**: `Action.lean` · **Depends on**: [CLEANUP-ALL-1] · **Type**: milestone · **Leaves**: L4.2 · **Milestone**: M1 (part 1): the weight action is a right action

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- `f ∣ 1 = f`. Source: roadmap §1.2.6. -/
theorem kappaSlash_one : W.kappaSlash 1 = ContinuousLinearMap.id K _ := by
  sorry

/-- `(f ∣ δ) ∣ γ = f ∣ (δγ)`: the weight action is a right action. Source: roadmap §1.2.6; [Jac03,
Definition 1.27] ("It is an easy check that `Σ_α` is a monoid and that `∥_κ` is a right action"). -/
theorem kappaSlash_mul (γ δ : S) :
    W.kappaSlash (δ * γ) = (W.kappaSlash γ).comp (W.kappaSlash δ) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L4.2** `kappaSlash_one`, `kappaSlash_mul` — [RM] §1.2.6 "`f ∣ 1 = f` and `(f ∣ δ) ∣ γ = f ∣ (δγ)`: the
  weight action is a right action of `Σ` on `A` by operators of norm at most `1`". Sketch:
  substrate, *the action and its laws*; `ContinuousLinearMap.ext`. Discharge: `autFactor_one`,
  `autFactor_mul` (fields), L2.8 `mobiusSubst_one`/`mobiusSubst_mul`, `map_mul` of `mobiusSubst`,
  `mul_assoc`, `mul_left_comm`. Attacks: [1] order: with `kappaSlash_mul : kappaSlash (δ * γ) =
  (kappaSlash γ).comp (kappaSlash δ)`, applying to `f`: `f ∣ (δγ) = (f ∣ δ) ∣ γ` ✓ the sources' right
  action. [2] `δ = 1` ✓ reduces to `kappaSlash_one`. [4] [Jac03] "`∥_κ` is a right-action" ✓. SURVIVED.
  **Milestone M1 (part).**

#### Mathlib lemmas needed

`ContinuousLinearMap.ext`, `ContinuousLinearMap.comp_apply`, `mul_assoc`, `mul_left_comm`, `map_mul`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2.4–§1.2.6, §1.2.8, §1.4; [Buz07, §10, pp. 71–72]; [Jac03, Proposition 2.6, Lemma 2.7]; [RAG] `Restricted/Sum.lean` (`renameHom`); [SRC] `QMF/Weight/03_SlashAction.lean` (`kappaSlash_one`, `kappaSlash_mul`, `twist`, `comap`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D3** engine `WeightData` (cocycle a field) / public `AnalyticWeight` (cocycle a theorem); **D12** right actions are `DistribMulAction Sᵐᵒᵖ A` built by `DistribMulAction.compHom`, as definitions.

#### Progress

- 2026-10-06T20:43: kappaSlash_one (mobiusSubst_congr + mobiusSubst_one) and kappaSlash_mul (mobiusSubst_mul + cocycle) proved; std axioms.

### [T022] `kappaSlash_monomial`, `norm_coeff_kappaSlash_monomial_le`, `norm_coeff_kappaSlash_monomial_le_one`

- **Status**: done   (finished 2026-10-06T20:43) · **File**: `Action.lean` · **Depends on**: [T021] · **Type**: milestone · **Leaves**: L4.3 · **Milestone**: M1 (part 2): the matrix of the action and its row bound

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- **The action on monomials**: `z^r ∣ γ = j(γ) ∏_i w_{γ,i}^{r_i}` — the columns of the matrix of
the action, Jacobs's generating function read off column by column. Source: roadmap §1.2.5;
[Jac03, Proposition 2.6]. -/
theorem kappaSlash_monomial (γ : S) (r : ι →₀ ℕ) :
    W.kappaSlash γ (monomial 1 r 1) =
      W.autFactor γ * r.prod fun i k => mobius (W.toMulti γ) i ^ k := by
  sorry

/-- **The row bound**: if `‖a_i‖ ≤ σ` for every `i` and `ρ ≤ σ`, then every matrix coefficient of
the action satisfies `‖coeff_t (z^r ∣ γ)‖ ≤ σ^{|t|}`. Source: roadmap §1.2.4; [Jac03, Lemma 2.7]
("it suffices to prove that every entry in `D(1/3) ε_{k,l}` is in `𝒪_3`"). -/
theorem norm_coeff_kappaSlash_monomial_le (γ : S) {σ : ℝ} (hρσ : ρ ≤ σ)
    (ha : ∀ i, ‖W.toMulti γ i 0 0‖ ≤ σ) (t r : ι →₀ ℕ) :
    ‖coeff t (W.kappaSlash γ (monomial 1 r 1)).1‖ ≤ σ ^ t.degree := by
  sorry

/-- Every matrix coefficient of the action lies in the unit ball. Source: roadmap §1.2.4 ("the
coefficients of `H_γ` lie in the unit ball"). -/
theorem norm_coeff_kappaSlash_monomial_le_one (γ : S) (t r : ι →₀ ℕ) :
    ‖coeff t (W.kappaSlash γ (monomial 1 r 1)).1‖ ≤ 1 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L4.3** `kappaSlash_monomial`, `norm_coeff_kappaSlash_monomial_le`,
  `norm_coeff_kappaSlash_monomial_le_one`, `tendsto_norm_coeff_kappaSlash_monomial` (discharged) —
  [RM] §1.2.5 "`z^r ↦ j_κ(γ) ∏_i w_{γ,i}^{r_i}`"; §1.2.4 "the row bound: if `‖a‖ ≤ σ` with `ρ ≤ σ < 1`
  then `‖coeff_{(m,r)} H_γ‖ ≤ σ^{|m|}` for all `m, r`"; "the coefficients of `H_γ` lie in the unit ball;
  for fixed `r` they tend to `0` in `m`". Sketch: substrate; `monomial 1 r 1 = r.prod (fun i k => X i ^ k)`
  ([RAG] `monomial`, `MvPowerSeries.monomial_eq`-type *(ticket)*), `map_finsupp_prod`, `map_pow`;
  row bound by L2.11/L2.12 and `RowBound.mono`; `≤ 1` from `RowBound ρ` at `σ = ρ`… no — at `σ := 1`
  is not allowed (`‖a‖ ≤ 1` ✓ integral, `ρ ≤ 1` ✓): `norm_coeff_kappaSlash_monomial_le` at `σ = 1`
  gives `≤ 1^{|t|} = 1` ✓. Attacks: [1] [Jac03]'s kernel has the extra factor `(cx + d)^{-2}` — his
  normalisation; the roadmap's convention 5 absorbs it into `n` ✓ (no `(cx+d)^{-2}` here). [3]
  `σ < 1` of the roadmap is not needed for the inequality ✓ dropped (L2.12). [4] [Jac03, Lemma 2.7]
  "every coefficient of `x` is divisible by `3`" = `RowBound ‖3‖` ✓; [Jac03, Prop 2.6] = the
  monomial formula read column by column ✓ (decision D1). SURVIVED. **Milestone M1 (part).**

#### Mathlib lemmas needed

`map_finsupp_prod`, `map_pow`, `MvPowerSeries.Restricted.monomial`, `Finsupp.prod`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2.4–§1.2.6, §1.2.8, §1.4; [Buz07, §10, pp. 71–72]; [Jac03, Proposition 2.6, Lemma 2.7]; [RAG] `Restricted/Sum.lean` (`renameHom`); [SRC] `QMF/Weight/03_SlashAction.lean` (`kappaSlash_one`, `kappaSlash_mul`, `twist`, `comap`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D1** the carrier is the Tate algebra `MvPowerSeries.Restricted K (1 : ι → ℝ)`; the action is the substitution operator, the kernel array is the theorem `kappaSlash_monomial`; **D11** row bounds are the predicate `RowBound σ f := ∀ t, ‖coeff t f‖ ≤ σ ^ t.degree`.

#### Progress

- 2026-10-06T20:43: kappaSlash_monomial via aeval_monomial; norm_coeff_kappaSlash_monomial_le from RowBound.mul/prod/pow + rowBound_mobius; tendsto lemma from the row bound at σ<1; std axioms.

### [CLEANUP-9] `/cleanup` of `Action.lean` (cadence: three proof tickets)

- **Status**: done   (finished 2026-10-06T20:43) · **File**: `Action.lean` · **Depends on**: [T022] · **Type**: cleanup

Run `/cleanup` on `PhD/TauCeti/Code/OverconvergentForms/Weight/Action.lean` (cadence: three proof tickets). Style audit + golf to mathlib standards; add `omit … in` where the skeleton's 'automatically included section variable(s) unused' warnings point; check docstrings cite the roadmap clause and the source; no statement changes without a B2 entry in `b2_log.jsonl`.

#### Progress

- 2026-10-06T20:43: Inline: docstrings reflowed to 100 chars; deprecated ContinuousLinearMap.smul_apply replaced by smul_apply; lint clean.

### [T023] `kappaSlashHom`, `smulCommClass`, `twist` and 2 more

- **Status**: done   (finished 2026-10-06T20:43) · **File**: `Action.lean` · **Depends on**: [CLEANUP-9] · **Type**: proof · **Leaves**: L4.4, L4.5

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- The action as a monoid homomorphism from the opposite monoid into the endomorphisms. -/
noncomputable def kappaSlashHom : Sᵐᵒᵖ →* Module.End K (Restricted K (1 : ι → ℝ)) where
  toFun γ := (W.kappaSlash γ.unop : Restricted K (1 : ι → ℝ) →ₗ[K] Restricted K (1 : ι → ℝ))
  map_one' := by sorry
  map_mul' := by sorry

theorem smulCommClass :
    letI := W.kappaSlashAction
    SMulCommClass K Sᵐᵒᵖ (Restricted K (1 : ι → ℝ)) := by
  sorry

/-- **The twist** by a norm-one character `χ : S →* Kˣ`: `f ↦ χ(γ) • (f ∣ γ)`. The character
`γ ↦ v(det γ)` and a nebentypus pulled back through `d` are the instances. Source: roadmap §1.2.8. -/
noncomputable def twist (χ : S →* Kˣ) (hχ : ∀ γ, ‖(χ γ : K)‖ = 1) : WeightData S K ι ρ where
  toMulti := W.toMulti
  bounds := W.bounds
  autFactor γ := (χ γ : K) • W.autFactor γ
  rowBound_autFactor γ := (W.rowBound_autFactor γ).smul (hχ γ).le
  autFactor_one := by sorry
  autFactor_mul := by sorry

theorem twist_kappaSlash (χ : S →* Kˣ) (hχ : ∀ γ, ‖(χ γ : K)‖ = 1) (γ : S) :
    (W.twist χ hχ).kappaSlash γ = (χ γ : K) • W.kappaSlash γ := by
  sorry

/-- **Pullback** along a monoid homomorphism `φ : S' →* S`. The single-place instance of §1.4.2
(`S_𝔮` acting trivially for `𝔮 ≠ 𝔭`) is the pullback along the projection `∏_𝔮 S_𝔮 → S_𝔭`, and
Layer 2 pulls the action back along `θ_𝔭 : Δ_t → S`. -/
noncomputable def comap {S' : Type*} [Monoid S'] (φ : S' →* S) : WeightData S' K ι ρ where
  toMulti := W.toMulti.comp φ
  bounds γ := W.bounds (φ γ)
  autFactor γ := W.autFactor (φ γ)
  rowBound_autFactor γ := W.rowBound_autFactor (φ γ)
  autFactor_one := by sorry
  autFactor_mul := by sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L4.4** `kappaSlashHom` (fields), `kappaSlashAction` (discharged), `op_smul_def` (`rfl`),
  `smulCommClass` — [RM] convention 2 "implemented as Mathlib's `DistribMulAction Δᵐᵒᵖ A` with
  `SMulCommClass K Δᵐᵒᵖ A`". Sketch: substrate, *the opposite action*; `MulOpposite.unop_mul` ✓,
  `MulOpposite.unop_one` ✓, L4.2, `ContinuousLinearMap.coe_comp`; `SMulCommClass` from
  `map_smul` of the operator (`DistribMulAction.compHom` smul is application ✓
  `Module.End.applyModule`). Attacks: [1] `map_mul'`: `kappaSlashHom (γ * δ) = kappaSlashHom γ *
  kappaSlashHom δ` in `Module.End` (composition `γ ∘ δ`): `(γ δ).unop = δ.unop γ.unop`, so we need
  `kappaSlash (δ.unop * γ.unop) = kappaSlash γ.unop ∘ kappaSlash δ.unop` ✓ exactly L4.2's orientation.
  SURVIVED.

- **L4.5** `restrictRadius` (discharged), `restrictRadius_kappaSlash` (`rfl`), `twist` (fields
  `autFactor_one`, `autFactor_mul`), `twist_kappaSlash`, `comap` (fields), `comap_kappaSlash` (`rfl`)
  — [RM] §1.2.8 "A datum at `(Σ, ρ)` restricts to any `(Σ', ρ')` with `Σ' ⊆ Σ` and `ρ ≤ ρ'` […]. For a
  character `χ : Σ →* K^×` of norm `1` on `Σ`, the twisted action `f ↦ χ(γ) • (f ∣_κ γ)` is again a
  right action by operators of norm at most `1`"; §1.4.2 (the pullback). Sketch: substrate,
  *twist, pullback*; `map_one`, `map_mul` of `χ`/`φ`, `Units.val_mul`, `smul_mul_assoc`,
  `mul_smul_comm`, `map_smul` of `mobiusSubst`, `smul_smul`. Attacks: [2] `χ = 1`: `twist = W` ✓. [3]
  `hχ` (norm one) is needed for `rowBound_autFactor` of the twist ✓ (B2 lesson J015). [4] the
  roadmap's "`γ ↦ v(det γ)` is such a character" is L5.11's `detChar` ✓. SURVIVED.

#### Mathlib lemmas needed

`MulOpposite.unop_mul`, `MulOpposite.unop_one`, `DistribMulAction.compHom`, `Module.End.applyModule`, `Units.val_mul`, `smul_mul_assoc`, `smul_smul`, `map_smul`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2.4–§1.2.6, §1.2.8, §1.4; [Buz07, §10, pp. 71–72]; [Jac03, Proposition 2.6, Lemma 2.7]; [RAG] `Restricted/Sum.lean` (`renameHom`); [SRC] `QMF/Weight/03_SlashAction.lean` (`kappaSlash_one`, `kappaSlash_mul`, `twist`, `comap`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D12** right actions are `DistribMulAction Sᵐᵒᵖ A` built by `DistribMulAction.compHom`, as definitions.

#### Progress

- 2026-10-06T20:43: kappaSlashHom, kappaSlashAction (compHom), smulCommClass, restrictRadius, twist (smul_mul_smul_comm with all four arguments explicit; twist_kappaSlash pointwise), comap; std axioms.

### [T024] `coeff_renameHom_mapDomain`, `coeff_renameHom_of_not_mem_range`, `rowBound_renameHom` and 3 more

- **Status**: done   (finished 2026-10-06T20:43) · **File**: `Action.lean` · **Depends on**: [T023] · **Type**: proof · **Leaves**: L4.6, L4.7

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- Renaming along an injection moves the coefficient at `t` to the coefficient at `e(t)`. -/
theorem coeff_renameHom_mapDomain {e : σ → τ} (he : Function.Injective e)
    (f : Restricted K (1 : σ → ℝ)) (t : σ →₀ ℕ) :
    coeff (t.mapDomain e) (renameHom K e f).1 = coeff t f.1 := by
  sorry

/-- Renaming along an injection has no coefficients outside the renamed multi-indices. -/
theorem coeff_renameHom_of_not_mem_range {e : σ → τ} (he : Function.Injective e)
    (f : Restricted K (1 : σ → ℝ)) {t : τ →₀ ℕ} (ht : ¬ ∃ s : σ →₀ ℕ, s.mapDomain e = t) :
    coeff t (renameHom K e f).1 = 0 := by
  sorry

/-- Row bounds are preserved by renaming along an injection (the total degree is). -/
theorem rowBound_renameHom {e : σ → τ} (he : Function.Injective e) {σ' : ℝ} (hσ0 : 0 ≤ σ')
    {f : Restricted K (1 : σ → ℝ)} (hf : RowBound σ' f) : RowBound σ' (renameHom K e f) := by
  sorry

theorem multiBounds_piMulti {ρ : ℝ} {γ : ∀ p, ιp p → Matrix (Fin 2) (Fin 2) K}
    (hγ : ∀ p, MultiBounds ρ (γ p)) : MultiBounds ρ (piMulti γ) := by
  sorry

/-- The Möbius series of the product are the renamed Möbius series of the places. -/
theorem renameHom_mobius {ρ : ℝ} {γ : ∀ p, ιp p → Matrix (Fin 2) (Fin 2) K}
    (hγ : ∀ p, MultiBounds ρ (γ p)) (p : P) (i : ιp p) :
    renameHom K (Sigma.mk p) (mobius (γ p) i) = mobius (piMulti γ) ⟨p, i⟩ := by
  sorry

/-- Substitution of the product's Möbius series commutes with renaming into the `p`-block. -/
theorem renameHom_mobiusSubst {ρ : ℝ} {γ : ∀ p, ιp p → Matrix (Fin 2) (Fin 2) K}
    (hγ : ∀ p, MultiBounds ρ (γ p)) (p : P) (f : Restricted K (1 : ιp p → ℝ)) :
    renameHom K (Sigma.mk p) (mobiusSubst (hγ p) f) =
      mobiusSubst (multiBounds_piMulti hγ) (renameHom K (Sigma.mk p) f) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L4.6** `coeff_renameHom_mapDomain`, `coeff_renameHom_of_not_mem_range`, `rowBound_renameHom` —
  needed by L4.8 (row bound of the product). Sketch: `renameHom K e f = ∑' t, monomial (mapDomain e t)
  (coeff t f)` — from [RAG] `hasSum_monomial` ✓, continuity of `renameHom` ([RAG]
  `continuous_renameHom` ✓), `renameHom` of a monomial is the renamed monomial (`map_mul`, `map_pow`,
  `renameHom_X`, `renameHom_C` ✓ and `monomial = C a * ∏ X^k`); coefficients of a convergent sum of
  monomials with pairwise distinct exponents (injectivity of `mapDomain e`,
  `Finsupp.mapDomain_injective` ✓); `Finsupp.degree_mapDomain` ✓. Attacks: [2] `e` the identity ✓
  (`renameHom id = id` by ext). [3] injectivity is necessary for `coeff_renameHom_mapDomain` (a
  non-injective rename merges coefficients) ✓ hypothesis present; `Sigma.mk p` is injective
  (`sigma_mk_injective` ✓). SURVIVED.

- **L4.7** `piMulti` (def), `multiBounds_piMulti`, `renameHom_mobius`, `renameHom_mobiusSubst` — [RM]
  §1.4.1 "the action with kernel `∏_𝔭 H_{γ_𝔭}` — the tensor product of the actions at the places,
  acting on the variables of `I_𝔭` through `γ_𝔭`". Sketch: substrate, *product*: `renameHom` is a
  continuous ring hom, `lin`/`num` are built from `C` and `X`, `linInv` is a convergent sum of
  monomials (`renameHom` commutes with `tsum` by continuity, `Filter.Tendsto` + `HasSum.map`-type
  lemma *(ticket)*), hence `renameHom (mobius (γ p) i) = mobius (piMulti γ) ⟨p, i⟩`; then
  `renameHom_mobiusSubst` by [RAG] `ringHom_ext_of_continuous` ✓ on `C`, `X`. Attacks: [2] `P` a
  singleton: `piMulti γ = γ p` up to the `Sigma` reindexing ✓. [3] the bounds are the same `ρ` at
  every place; different `ρ_p` are unified by `WeightData.restrictRadius` to `max` ✓ (roadmap
  §1.4.1's "`ρ_𝔭 ≤ σ` at every `𝔭`"). SURVIVED.

#### Mathlib lemmas needed

`MvPowerSeries.Restricted.hasSum_monomial`, `MvPowerSeries.Restricted.continuous_renameHom`, `MvPowerSeries.Restricted.renameHom_X`, `MvPowerSeries.Restricted.renameHom_C`, `Finsupp.mapDomain_injective`, `Finsupp.degree_mapDomain`, `sigma_mk_injective`, `HasSum.map`, `MvPowerSeries.Restricted.ringHom_ext_of_continuous`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2.4–§1.2.6, §1.2.8, §1.4; [Buz07, §10, pp. 71–72]; [Jac03, Proposition 2.6, Lemma 2.7]; [RAG] `Restricted/Sum.lean` (`renameHom`); [SRC] `QMF/Weight/03_SlashAction.lean` (`kappaSlash_one`, `kappaSlash_mul`, `twist`, `comap`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D2** the series algebra is for multi-matrices `γ : ι → Matrix (Fin 2) (Fin 2) K`; one and several places are instances.

#### Progress

- 2026-10-06T20:43: renameHom_monomial (map_finsuppProd + Finsupp.prod_mapDomain_index_inj), coeff_renameHom_mapDomain / _of_not_mem_range via a private hasSum_coeff_renameHom, rowBound_renameHom, renameHom_mobius (inverse uniqueness for linInv), renameHom_mobiusSubst (ringHom_ext_of_continuous; X case via change + rw); std axioms.

### [T025] `pi`

- **Status**: done   (finished 2026-10-06T20:43) · **File**: `Action.lean` · **Depends on**: [T024] · **Type**: milestone · **Leaves**: L4.8 · **Milestone**: M5 (part 1): the product over the places

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- **The product of weight data over finitely many places**: on `K⟨z_{(p,i)}⟩`, the monoid
`∏_p S_p` acts through the multi-matrix `(γ_p)_p` with automorphy factor `∏_p j_p(γ_p)` (each in
its own variables) — the tensor product of the actions at the places. Source: roadmap §1.4.1;
[Buz07, §10] (`A_{κ,r}` at `r = 1` for the monoid `M_t`). -/
noncomputable def WeightData.pi (W : ∀ p, WeightData (Sp p) K (ιp p) ρ) :
    WeightData (∀ p, Sp p) K (Σ p, ιp p) ρ where
  toMulti :=
    { toFun := fun γ => piMulti fun p => (W p).toMulti (γ p)
      map_one' := by sorry
      map_mul' := by sorry }
  bounds γ := multiBounds_piMulti fun p => (W p).bounds (γ p)
  autFactor γ := ∏ p, renameHom K (Sigma.mk p) ((W p).autFactor (γ p))
  rowBound_autFactor γ := by sorry
  autFactor_one := by sorry
  autFactor_mul := by sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L4.8** `WeightData.pi` (fields `map_one'`, `map_mul'`, `rowBound_autFactor`, `autFactor_one`,
  `autFactor_mul`), `pi_toMulti` (`rfl`), `pi_autFactor` (`rfl`), `WeightData.single` (discharged) —
  [RM] §1.4.1 "Prove it is a right action by operators of norm at most `1`, with the row bound
  `σ^{|m|}` in the total degree over `I` when `‖a_𝔭‖ ≤ σ` and `ρ_𝔭 ≤ σ` at every `𝔭`"; §1.4.2 "the
  sub-instance […] with `Σ_𝔮` acting trivially for `𝔮 ≠ 𝔭`". Sketch: substrate; `Pi.mul_apply`,
  `Finset.prod_mul_distrib` ✓, `map_prod` of `mobiusSubst`, L4.6/L4.7, L2.11 `RowBound.prod`;
  `autFactor_one`: `∏ ren_p 1 = 1`. The row bound and the action laws of the product are then the
  general L4.2/L4.3 applied to `pi W` ✓ (no separate statement needed). Attacks: [1] is the
  cocycle of the product really factorwise? `j(δγ) = ∏_p ren_p(j_p(δ_p γ_p)) = ∏_p ren_p(j_p(γ_p) ·
  (j_p(δ_p) ∘ w_{γ_p})) = ∏_p ren_p(j_p(γ_p)) · ∏_p (ren_p(j_p(δ_p)) ∘ w_γ)` by L4.7 ✓ and the substitution
  is multiplicative ✓. [2] `P` empty: `A = K⟨∅⟩ = K`, trivial action ✓. [4] [Buz07, §10] `A_{κ,r}` on
  the product of the `B_{r_j}` ✓; the roadmap's full character `n : ∏ 𝒪_𝔭^× → K^×` is `∏ n_𝔭 ∘ pr_𝔭`
  (every character of a finite product of groups into a commutative group is such a product;
  Mathlib `MonoidHom.noncommPiCoprod`) — stated at the `WeightData` level only (plan.md D2) ✓.
  SURVIVED. **Milestone M5 (part).**

#### Mathlib lemmas needed

`Pi.mul_apply`, `Finset.prod_mul_distrib`, `map_prod`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2.4–§1.2.6, §1.2.8, §1.4; [Buz07, §10, pp. 71–72]; [Jac03, Proposition 2.6, Lemma 2.7]; [RAG] `Restricted/Sum.lean` (`renameHom`); [SRC] `QMF/Weight/03_SlashAction.lean` (`kappaSlash_one`, `kappaSlash_mul`, `twist`, `comap`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D2** the series algebra is for multi-matrices `γ : ι → Matrix (Fin 2) (Fin 2) K`; one and several places are instances; **D3** engine `WeightData` (cocycle a field) / public `AnalyticWeight` (cocycle a theorem).

#### Progress

- 2026-10-06T20:43: WeightData.pi proved. B2 REPAIRED IN PLACE (logged in b2_log.jsonl): multiBounds_piMulti now takes hρ0 hρ explicitly and pi takes [Nonempty P] (empty place set made the radius facts unprovable). pi_toMulti/pi_autFactor rfl, single = comap of Pi.evalMonoidHom; std axioms.

### [CLEANUP-10] `/cleanup` of `Action.lean` (final for the file)

- **Status**: done   (finished 2026-10-06T20:43) · **File**: `Action.lean` · **Depends on**: [T025] · **Type**: cleanup

Run `/cleanup` on `PhD/TauCeti/Code/OverconvergentForms/Weight/Action.lean` (final for the file). Style audit + golf to mathlib standards; add `omit … in` where the skeleton's 'automatically included section variable(s) unused' warnings point; check docstrings cite the roadmap clause and the source; no statement changes without a B2 entry in `b2_log.jsonl`.

#### Progress

- 2026-10-06T20:43: Action.lean final: build clean with no warnings, runLinter passes, [Fintype P] scoped to the product declarations, [DecidableEq P] dropped (unused).

### [T026] `continuous_aeval_point`, `norm_point_le_one`

- **Status**: done   (finished 2026-10-06T21:01) · **File**: `Expansion.lean` · **Depends on**: [T019], [T022] · **Type**: proof · **Leaves**: L5.1, L5.2

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- Evaluation of a fixed restricted series is continuous in the point of the closed unit
polydisc: the series is the uniform limit of its polynomial truncations there. Source: PFA roadmap
§4.1.3 ("evaluation at the points of `R⁰` gives a bounded `R`-linear map `R⟨X⟩ → C(R⁰, R)`"). -/
theorem continuous_aeval_point (f : Restricted K (1 : σ → ℝ)) :
    Continuous fun x : {x : σ → K // ∀ i, ‖x i‖ ≤ 1} => aeval 1 x.1 x.2 f := by
  sorry

theorem norm_point_le_one (z : Subring.unitClosedBall L) (i : ι) : ‖e.point z i‖ ≤ 1 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L5.1** `MvPowerSeries.Restricted.continuous_aeval_point` — PFA §4.1.3 "evaluation at the points
  of `R⁰` gives a bounded `R`-linear map `R⟨X⟩ → C(R⁰, R)` of norm `1`" (the function side). Sketch:
  `f = lim_S ∑_{t ∈ S} a_t z^t` uniformly on the polydisc ([RAG] `exists_finset_norm_sub_sum_monomial_lt`
  ✓ with `norm_aeval_le`: `‖f(x) − P(x)‖ ≤ ‖f − P‖ < ε` for all `x`), each polynomial evaluation is
  continuous (`continuous_finset_sum`, `continuous_pow`, `Continuous.mul`), and a uniform limit of
  continuous maps is continuous (`TendstoUniformly.continuous` ✓ or `continuous_of_uniform_approx_of_continuous`
  ✓). Attacks: [2] `σ` empty: constant ✓. [3] `[CompleteSpace K]` for `aeval` ✓. SURVIVED.

- **L5.2** `Embeddings` (structure), `Embeddings.self` (discharged), `point`, `norm_point_le_one`,
  `evalPoint`, `evalPoint_X` (discharged), `norm_evalPoint_le` (discharged) — [RM] Layer 1 preamble
  "`I_𝔭 = Hom_{ℚ_p}(F_𝔭, K)`"; §1.2.2 "for every `z ∈ 𝒪`, embedded as `(i(z))_i` in the closed unit
  polydisc". Sketch: `‖e_i z‖ = ‖z‖ ≤ 1` ([PFA] `Subring.norm_le_one` ✓, `norm_emb`). Attacks: [3] the
  `exists_integralBasis` field: necessary for L5.4 in this generality (without it, `ι` could contain
  the same embedding twice, and `e(𝒪_L)` would lie in a diagonal, where nonzero series vanish) ✓ —
  a genuine attack on a naive `Embeddings` without the field: `ι = Fin 2`, `e_0 = e_1`, `f = z_0 − z_1`
  vanishes on `e(𝒪_L)`. So the field is NECESSARY ✓ (this is why "distinct embeddings" matters in
  Buzzard). [4] `Embeddings.self` is the `F = ℚ` case ✓. SURVIVED.

#### Mathlib lemmas needed

`MvPowerSeries.Restricted.exists_finset_norm_sub_sum_monomial_lt`, `MvPowerSeries.Restricted.norm_aeval_le`, `TendstoUniformly.continuous`, `continuous_finset_sum`, `continuous_pow`, `Subring.norm_le_one`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2.2–§1.2.3, §1.2.5–§1.2.6, §1.2.8, convention 3; [Buz07, §8, pp. 62–64, p. 66; §10, p. 72]; [Jac03, Definition 1.27]; [PFA] `UnitBall.lean`; [SRC] `QMF/Weight/04_Char.lean` (`ExpansionData`, `AnalyticWeight`, `lin_eval_cocycle`, `col_eq_of_mem`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D6** `Embeddings.exists_integralBasis` is a Prop field; `[CharZero K]` where the identity theorem is used.

#### Progress

- 2026-10-06T21:01: continuous_aeval_point (uniform approximation by truncations, continuous_of_uniform_approx_of_continuous; seam crossed by a calc of term steps) and norm_point_le_one; std axioms.

### [T027] `ofAlgHom`

- **Status**: done   (finished 2026-10-06T21:01) · **File**: `Expansion.lean` · **Depends on**: [T026] · **Type**: proof · **Leaves**: L5.3

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- **Dedekind's lemma**: `[L : k] = |ι|` distinct `k`-algebra embeddings `L → K` over a
nontrivially normed base field `k` have an integral basis with invertible embedding matrix. Source:
[Buz07, p. 63] ("It is a standard fact (linear independence of distinct field embeddings) that the
continuous group homomorphisms `𝒪 → K` form a finite-dimensional `K`-vector space with basis the set
`I`"). -/
noncomputable def ofAlgHom {k : Type*} [NontriviallyNormedField k] [NormedAlgebra k L]
    [NormedAlgebra k K] [FiniteDimensional k L] (e : ι → (L →ₐ[k] K)) (he : Function.Injective e)
    (hcard : Fintype.card ι = Module.finrank k L) (hiso : ∀ i x, ‖e i x‖ = ‖x‖) :
    Embeddings L K ι where
  emb i := (e i : L →+* K)
  norm_emb := hiso
  exists_integralBasis := by
    sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L5.3** `Embeddings.ofAlgHom` (field `exists_integralBasis`) — [Buz07, p. 63] (quoted). Sketch:
  substrate, *Dedekind*. Discharge: `linearIndependent_monoidHom` ✓, `Matrix.exists_vecMul_eq_zero_iff`
  ✓, `Module.finBasisOfFinrankEq` *(ticket)*, `NontriviallyNormedField.exists_norm_lt_one` ✓,
  `norm_smul` (`NormedAlgebra` gives `NormedSpace k L` ✓), `Matrix.det_mul_column`/`Matrix.det_smul`
  *(ticket)*, `Fintype.linearIndependent_iff`. Attacks: [1] is `hcard : card ι = finrank k L`
  necessary? With fewer embeddings than the degree the matrix is not square — the statement needs
  `ι` to index a basis ✓; with `|ι| = [L : k]` all embeddings into `K` are present only if `K` splits
  `L` — not needed for the lemma (any `[L : k]` distinct embeddings work) ✓ more general than the
  roadmap's "`K` splits `F`". [2] `[L : k] = 1`: `ι` a point, `b = 1`, `det = 1` ✓. [3] `hiso` is the
  `Embeddings.norm_emb` field, not used in the basis argument ✓ (it is a field of the result). [4]
  [Buz07] "linear independence of distinct field embeddings" ✓ Dedekind. SURVIVED.

#### Mathlib lemmas needed

`linearIndependent_monoidHom`, `Matrix.exists_vecMul_eq_zero_iff`, `Module.finBasisOfFinrankEq`, `NontriviallyNormedField.exists_norm_lt_one`, `norm_smul`, `Matrix.det_smul`, `Fintype.linearIndependent_iff`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2.2–§1.2.3, §1.2.5–§1.2.6, §1.2.8, convention 3; [Buz07, §8, pp. 62–64, p. 66; §10, p. 72]; [Jac03, Definition 1.27]; [PFA] `UnitBall.lean`; [SRC] `QMF/Weight/04_Char.lean` (`ExpansionData`, `AnalyticWeight`, `lin_eval_cocycle`, `col_eq_of_mem`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D6** `Embeddings.exists_integralBasis` is a Prop field; `[CharZero K]` where the identity theorem is used.

#### Progress

- 2026-10-06T21:01: ofAlgHom: Dedekind via linearIndependent_monoidHom + Matrix.exists_vecMul_eq_zero_iff on a reindexed finBasisOfFinrankEq, then rescaling by a ∈ k with ‖a‖ < (1 + Σ‖b'β‖)⁻¹ (Matrix.det_smul); std axioms.

### [T028] `eq_zero_of_forall_evalPoint_eq_zero`, `ext_of_forall_evalPoint_eq`

- **Status**: done   (finished 2026-10-06T21:01) · **File**: `Expansion.lean` · **Depends on**: [T027] · **Type**: milestone · **Leaves**: L5.4 · **Milestone**: M2: the identity theorem on `e(𝒪_L)`

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- **The identity theorem on `e(𝒪_L)`**: a restricted series vanishing at every integral point
`e(z)`, `z ∈ 𝒪_L`, is zero. Source: roadmap §1.2.3; [Buz07, pp. 63–64] ("that `𝒪` is Zariski-dense
in `B₁`"). -/
theorem eq_zero_of_forall_evalPoint_eq_zero [CharZero K] {f : Restricted K (1 : ι → ℝ)}
    (hf : ∀ z, e.evalPoint z f = 0) : f = 0 := by
  sorry

theorem ext_of_forall_evalPoint_eq [CharZero K] {f g : Restricted K (1 : ι → ℝ)}
    (h : ∀ z, e.evalPoint z f = e.evalPoint z g) : f = g := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L5.4** `Embeddings.eq_zero_of_forall_evalPoint_eq_zero`, `ext_of_forall_evalPoint_eq` — [RM]
  §1.2.3 (quoted); [Buz07, pp. 63–64]. Sketch: substrate, *the identity theorem on `e(𝒪_L)`*.
  Discharge: L3.10 with `M := Matrix.of fun i β => e.emb i (b β)` (`hM` from `norm_emb` and
  `‖b β‖ ≤ 1`; `hdet` from the field), `map_sum`, `map_natCast`, `Matrix.mulVec`/`Matrix.dotProduct`
  ✓, `Subring.sum_mem`, `Subring.natCast_mem`-type, [PFA] `Subring.mem_unitClosedBall` ✓; `ext` by
  `sub_eq_zero` and `map_sub`. Attacks: [1] L5.2 [3]'s counterexample shows the basis field is what
  makes this true ✓. [3] `[CharZero K]` (L3.10). [4] the roadmap's "`K^d → K^{I_𝔭}` isometry for a
  suitable renormalisation" is replaced by Cramer (erratum E2) ✓ same conclusion. SURVIVED.
  **Milestone M2.**

#### Mathlib lemmas needed

`map_sum`, `map_natCast`, `Subring.sum_mem`, `Subring.mem_unitClosedBall`, `sub_eq_zero`, `map_sub`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2.2–§1.2.3, §1.2.5–§1.2.6, §1.2.8, convention 3; [Buz07, §8, pp. 62–64, p. 66; §10, p. 72]; [Jac03, Definition 1.27]; [PFA] `UnitBall.lean`; [SRC] `QMF/Weight/04_Char.lean` (`ExpansionData`, `AnalyticWeight`, `lin_eval_cocycle`, `col_eq_of_mem`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D6** `Embeddings.exists_integralBasis` is a Prop field; `[CharZero K]` where the identity theorem is used.

#### Progress

- 2026-10-06T21:01: M2 DONE: identity theorem on e(𝒪_L) from Identity's eq_zero_of_forall_aeval_mulVec_natCast_eq_zero at the points Σ n_β b_β (aeval_congr made public in Identity.lean); ext version by sub_eq_zero; std axioms.

### [CLEANUP-11] `/cleanup` of `Expansion.lean` (cadence: three proof tickets)

- **Status**: done   (finished 2026-10-06T21:01) · **File**: `Expansion.lean` · **Depends on**: [T028] · **Type**: cleanup

Run `/cleanup` on `PhD/TauCeti/Code/OverconvergentForms/Weight/Expansion.lean` (cadence: three proof tickets). Style audit + golf to mathlib standards; add `omit … in` where the skeleton's 'automatically included section variable(s) unused' warnings point; check docstrings cite the roadmap clause and the source; no statement changes without a B2 entry in `b2_log.jsonl`.

#### Progress

- 2026-10-06T21:01: Inline: omit annotations (norm_point_le_one, toMulti_apply, toMultiHom_apply, multiBounds_toMulti), deprecated continuous_finset_sum/prod renamed.

### [T029] `toMultiHom`, `multiBounds_toMulti`, `coe_unitOfNormEqOne` and 2 more

- **Status**: done   (finished 2026-10-06T21:01) · **File**: `Expansion.lean` · **Depends on**: [CLEANUP-11] · **Type**: proof · **Leaves**: L5.5, L5.6

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- `γ ↦ (i(γ))_i` is a monoid homomorphism. -/
def toMultiHom : Matrix (Fin 2) (Fin 2) L →* (ι → Matrix (Fin 2) (Fin 2) K) where
  toFun := e.toMulti
  map_one' := by sorry
  map_mul' := by sorry

/-- Level bounds transport along the isometric embeddings. -/
theorem multiBounds_toMulti {S : Submonoid (Matrix (Fin 2) (Fin 2) L)} {ρ : ℝ}
    (hb : LevelBounds S ρ) {g : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S) :
    MultiBounds ρ (e.toMulti g) := by
  sorry

@[simp] theorem coe_unitOfNormEqOne (x : L) (hx : ‖x‖ = 1) :
    ((unitOfNormEqOne x hx : Subring.unitClosedBall L) : L) = x := by
  sorry

@[simp] theorem coe_linUnit {g : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S) (z : Subring.unitClosedBall L) :
    ((hb.linUnit hg z : Subring.unitClosedBall L) : L) = g 1 0 * z + g 1 1 := by
  sorry

/-- The Möbius image `γ · z = (a z + b)/(c z + d) ∈ 𝒪_L` of an integral point. Source: roadmap
§1.2.6 ("`col_δ ∘ w_γ` at `e(z)` is `col_δ` at `e(γ·z)`"); [Buz07, Lemma 8.1(b)]. -/
noncomputable def mobiusPt {g : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S) (z : Subring.unitClosedBall L) :
    Subring.unitClosedBall L :=
  ⟨(g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1), by
    have := hb.norm_mul_add_eq_one hg (Subring.norm_le_one z)
    sorry⟩
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L5.5** `toMulti` (def), `toMulti_apply` (`rfl`), `toMultiHom` (fields), `toMultiHom_apply`,
  `multiBounds_toMulti` — [RM] preamble "`γ_i := i(γ) ∈ M₂(K)`". Sketch: `RingHom.mapMatrix` ✓ is a
  ring hom (`map_one`, `map_mul` of `(e.emb i).mapMatrix`), `Pi.one_apply`, `Pi.mul_apply`;
  `norm_emb` transports each bound. Attacks: [2] `ι` empty ✓ vacuous. [4] [Buz07]'s `γ_i` ✓.
  SURVIVED.

- **L5.6** `unitsIncl` (discharged), `coe_unitsIncl` (`rfl`), `unitOfNormEqOne` (discharged),
  `coe_unitOfNormEqOne`, `LevelBounds.linUnit` (discharged), `coe_linUnit`, `dUnit` (discharged),
  `mobiusPt` (membership field), `coe_mobiusPt` (`rfl`) — [RM] §1.2.2 "`c z + d ∈ 𝒪^×`"; §1.2.6
  `γ·z ∈ 𝒪`. Sketch: `IsUnit.unit_spec` ✓ for the coercions; `‖(az + b)/(cz + d)‖ = ‖az + b‖/1 ≤ 1`
  (L1.4 `norm_mul_add_eq_one`, `norm_div`, ultrametric). Attacks: [2] `z = 0`: `γ·0 = b/d` ✓ integral.
  [3] `mobiusPt` needs `hg : g ∈ S` only for `cz + d ≠ 0` ✓. SURVIVED.

#### Mathlib lemmas needed

`RingHom.mapMatrix`, `Pi.one_apply`, `Pi.mul_apply`, `IsUnit.unit_spec`, `norm_div`, `Subring.mem_unitClosedBall`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2.2–§1.2.3, §1.2.5–§1.2.6, §1.2.8, convention 3; [Buz07, §8, pp. 62–64, p. 66; §10, p. 72]; [Jac03, Definition 1.27]; [PFA] `UnitBall.lean`; [SRC] `QMF/Weight/04_Char.lean` (`ExpansionData`, `AnalyticWeight`, `lin_eval_cocycle`, `col_eq_of_mem`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D2** the series algebra is for multi-matrices `γ : ι → Matrix (Fin 2) (Fin 2) K`; one and several places are instances.

#### Progress

- 2026-10-06T21:01: toMultiHom (mapMatrix map_one/map_mul), multiBounds_toMulti, coe_unitOfNormEqOne (IsUnit.unit_spec), coe_linUnit, mobiusPt membership (norm_div + ultrametric); std axioms.

### [T030] `mobiusPt_one`, `mobiusPt_mul`, `linUnit_mul` and 6 more

- **Status**: done   (finished 2026-10-06T21:01) · **File**: `Expansion.lean` · **Depends on**: [T029] · **Type**: proof · **Leaves**: L5.7, L5.8, L5.9

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
theorem mobiusPt_one (z : Subring.unitClosedBall L) : hb.mobiusPt S.one_mem z = z := by
  sorry

/-- Möbius composition on integral points: `(δγ)·z = δ·(γ·z)`. -/
theorem mobiusPt_mul {g h : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S) (hh : h ∈ S)
    (z : Subring.unitClosedBall L) :
    hb.mobiusPt (S.mul_mem hh hg) z = hb.mobiusPt hh (hb.mobiusPt hg z) := by
  sorry

/-- **The automorphy cocycle in `𝒪_L^×`**: `c''z + d'' = (c'(γ·z) + d')(cz + d)` for `δγ = ((a'' b''), (c'' d''))`.
Source: roadmap §1.2.1 (`j(δγ, z) = j(γ, z) j(δ, γz)`). -/
theorem linUnit_mul {g h : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S) (hh : h ∈ S)
    (z : Subring.unitClosedBall L) :
    hb.linUnit (S.mul_mem hh hg) z = hb.linUnit hh (hb.mobiusPt hg z) * hb.linUnit hg z := by
  sorry

theorem linUnit_one (z : Subring.unitClosedBall L) : hb.linUnit S.one_mem z = 1 := by
  sorry

/-- The determinant of a level element, as a unit of `L`. -/
noncomputable def detUnits : S →* Lˣ where
  toFun g := Units.mk0 _ (hb.det_ne_zero g.2)
  map_one' := by sorry
  map_mul' := by sorry

/-- A level element as an element of `GL₂(L)`. -/
noncomputable def toGL : S →* GL (Fin 2) L where
  toFun g := Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hb.det_ne_zero g.2)
  map_one' := by sorry
  map_mul' := by sorry

theorem evalPoint_lin {g : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S) (z : Subring.unitClosedBall L)
    (i : ι) : e.evalPoint z (lin (e.toMulti g) i) = e.emb i (hb.linUnit hg z) := by
  sorry

/-- The Möbius series at an integral point is the embedded Möbius image: `w_{γ,i}(e(z)) = i(γ·z)`.
Source: roadmap §1.2.6. -/
theorem evalPoint_mobius {g : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S) (z : Subring.unitClosedBall L)
    (i : ι) : e.evalPoint z (mobius (e.toMulti g) i) = e.emb i (hb.mobiusPt hg z) := by
  sorry

/-- `(f ∘ w_γ)(e(z)) = f(e(γ·z))`. Source: roadmap §1.2.6. -/
theorem evalPoint_mobiusSubst {g : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S)
    (z : Subring.unitClosedBall L) (f : Restricted K (1 : ι → ℝ)) :
    e.evalPoint z (mobiusSubst (e.multiBounds_toMulti hb hg) f) = e.evalPoint (hb.mobiusPt hg z) f := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L5.7** `mobiusPt_one`, `mobiusPt_mul`, `linUnit_mul`, `linUnit_one` — [RM] §1.2.1 "`j(δγ, z) =
  j(γ, z) j(δ, γz)`" at the integral points; Möbius composition on points. Sketch: field identities
  `(a'(az+b)/(cz+d) + b')/(c'(az+b)/(cz+d) + d') = (a''z + b'')/(c''z + d'')` after clearing the
  nonzero denominator `cz + d` (`div_add_div_same`, `div_div_eq_mul_div`, `field_simp` with
  `norm_mul_add_eq_one`-derived `≠ 0`), `Units.ext`, `Subtype.ext`; `Matrix.mul_apply`,
  `Fin.sum_univ_two` ✓. Attacks: [1] orientation: `linUnit (δγ) z = linUnit δ (γ·z) · linUnit γ z`:
  `c''z + d'' = (c'a + d'c)z + (c'b + d'd) = c'(az + b) + d'(cz + d) = (c'(γ·z) + d')(cz + d)` ✓. [2]
  `γ = 1` ✓. SURVIVED.

- **L5.8** `detUnits` (fields), `coe_detUnits` (`rfl`), `toGL` (fields), `coe_toGL` (`rfl`) — [RM]
  §1.2.8 "`γ ↦ v(det γ)`"; §1.3.2 (`GL₂`). Sketch: `Units.mk0` ✓, `Matrix.det_one` ✓, `Matrix.det_mul`
  ✓, `Units.ext`; `Matrix.GeneralLinearGroup.mkOfDetNeZero` ✓, `Matrix.GeneralLinearGroup.ext`.
  Attacks: [3] `det_ne_zero` of `LevelBounds` (erratum E6) is exactly what is used ✓. SURVIVED.

- **L5.9** `evalPoint_lin`, `evalPoint_mobius`, `evalPoint_mobiusSubst` — [RM] §1.2.6 ("`col_δ ∘ w_γ`
  at `e(z)` is `col_δ` at `e(γ·z)`"). Sketch: L2.9 `aeval_lin`, `aeval_mobius` with `x = e(z)`,
  `map_mul`/`map_add`/`map_div₀` of `e.emb i` (a ring hom into a field: `map_div₀` ✓);
  `aeval_mobiusSubst` (L2.9) and `funext` of `evalPoint_mobius` with `aeval` congruence in the
  point and its proof (`Subtype`-free: both `aeval 1 x hx` with the same `x`; use
  `congrArg`/`simp only` carefully — the proof argument `hx` is a `Prop` so `congr` is fine).
  Attacks: [2] `z = 0` ✓. [4] [Buz07, Lemma 8.1] ✓. SURVIVED.

#### Mathlib lemmas needed

`Units.ext`, `Subtype.ext`, `div_add_div_same`, `Matrix.mul_apply`, `Fin.sum_univ_two`, `Units.mk0`, `Matrix.det_one`, `Matrix.det_mul`, `Matrix.GeneralLinearGroup.mkOfDetNeZero`, `Matrix.GeneralLinearGroup.ext`, `map_div₀`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2.2–§1.2.3, §1.2.5–§1.2.6, §1.2.8, convention 3; [Buz07, §8, pp. 62–64, p. 66; §10, p. 72]; [Jac03, Definition 1.27]; [PFA] `UnitBall.lean`; [SRC] `QMF/Weight/04_Char.lean` (`ExpansionData`, `AnalyticWeight`, `lin_eval_cocycle`, `col_eq_of_mem`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D2** the series algebra is for multi-matrices `γ : ι → Matrix (Fin 2) (Fin 2) K`; one and several places are instances.

#### Progress

- 2026-10-06T21:01: mobiusPt_one/mul (div_add', div_div_div_cancel_right₀), linUnit_mul/one, detUnits/toGL (Units.ext), evalPoint_lin/mobius/mobiusSubst (aeval_lin, aeval_mobius, aeval_mobiusSubst + aeval_congr); std axioms.

### [T031] `col_eq_of_mem`, `col_one`

- **Status**: done   (finished 2026-10-06T21:01) · **File**: `Expansion.lean` · **Depends on**: [T030] · **Type**: proof · **Leaves**: L5.10

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- **Uniqueness of the expansion on the level**: two expansion data for the same character agree
on every lower row of `S`, by the identity theorem. Source: roadmap §1.2.3. -/
theorem col_eq_of_mem [CharZero K] (E₁ E₂ : ExpansionData e S ρ n) {g : Matrix (Fin 2) (Fin 2) L}
    (hg : g ∈ S) : E₁.col (g 1 0) (g 1 1) = E₂.col (g 1 0) (g 1 1) := by
  sorry

/-- The expansion at the identity is `1`. -/
theorem col_one [CharZero K] : E.col 0 1 = 1 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L5.10** `ExpansionData` (structure), `norm_col_le_one` (discharged), `col_eq_of_mem`, `col_one`,
  `restrict` (discharged) — [RM] §1.2.2 (the two bullets), §1.2.3 "Two expansion data for the same
  `n` at the same level agree on every `(c, d)` occurring in `Σ`", §1.2.8 (restriction). Sketch:
  substrate; `col_one`: `(1 : Matrix) 1 0 = 0`, `(1 : Matrix) 1 1 = 1` (`Matrix.one_apply` ✓), the
  field at `g = 1` gives `n(linUnit 1 z) = n 1 = 1` (L5.7 `linUnit_one`), and `evalPoint z 1 = 1`
  (`map_one`); L5.4 `ext_of_forall_evalPoint_eq`. Attacks: [1] erratum E1: the roadmap's third
  condition (`→ 0` at radius `ρ^{-1}`) is dropped as unused and not implied — attack [3] on the
  roadmap SUCCEEDED, recorded in `plan.md` (D7, E1); the two remaining fields are consumed (L4.3,
  L5.12). [2] `ρ = 0`: `RowBound 0` forces `col(c, d)` constant `= n(d)` and indeed `c = 0` on the level
  ✓ consistent. [3] `[CharZero K]` only on `col_eq_of_mem`/`col_one` ✓. [4] [Jac03, Def 1.27] "by
  `κ(cz + d)` we mean the power series expansion" ✓; [Buz07, p. 66] "single out one such thickening"
  ✓ carried as data. SURVIVED.

#### Mathlib lemmas needed

`Matrix.one_apply`, `map_one`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2.2–§1.2.3, §1.2.5–§1.2.6, §1.2.8, convention 3; [Buz07, §8, pp. 62–64, p. 66; §10, p. 72]; [Jac03, Definition 1.27]; [PFA] `UnitBall.lean`; [SRC] `QMF/Weight/04_Char.lean` (`ExpansionData`, `AnalyticWeight`, `lin_eval_cocycle`, `col_eq_of_mem`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D7** `ExpansionData` has two analytic fields (row decay, evaluation); the roadmap's third is dropped (E1).

#### Progress

- 2026-10-06T21:01: col_eq_of_mem by ext_of_forall_evalPoint_eq; col_one via linUnit_one; std axioms.

### [CLEANUP-12] `/cleanup` of `Expansion.lean` (cadence: three proof tickets)

- **Status**: done   (finished 2026-10-06T21:01) · **File**: `Expansion.lean` · **Depends on**: [T031] · **Type**: cleanup

Run `/cleanup` on `PhD/TauCeti/Code/OverconvergentForms/Weight/Expansion.lean` (cadence: three proof tickets). Style audit + golf to mathlib standards; add `omit … in` where the skeleton's 'automatically included section variable(s) unused' warnings point; check docstrings cite the roadmap clause and the source; no statement changes without a B2 entry in `b2_log.jsonl`.

#### Progress

- 2026-10-06T21:01: Inline: unused binder names in detUnits.map_mul' replaced by _, omit annotations on coe_detUnits/coe_toGL.

### [T032] `evalPoint_autFactor`, `autFactor_one`

- **Status**: done   (finished 2026-10-06T21:01) · **File**: `Expansion.lean` · **Depends on**: [CLEANUP-12] · **Type**: proof · **Leaves**: L5.11

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- The automorphy factor at an integral point: `j_κ(γ)(e(z)) = v(det γ) n(cz + d)`. -/
theorem evalPoint_autFactor (γ : S) (z : Subring.unitClosedBall L) :
    e.evalPoint z (κ.autFactor γ) = (κ.detChar γ : K) * κ.n (κ.expansion.bounds.linUnit γ.2 z) := by
  sorry

theorem autFactor_one [CharZero K] : κ.autFactor 1 = 1 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L5.11** `AnalyticWeight` (structure), `bounds`, `detChar` (discharged), `detChar_apply`,
  `norm_detChar` (discharged), `autFactor` (def), `rowBound_autFactor` (discharged),
  `evalPoint_autFactor`, `autFactor_one` — [RM] §1.2.2 "An analytic weight at level `(Σ, ρ)` is
  `κ = (n, v, col)`"; §1.2.4 "Define `j_κ(γ) := v(det γ) • col(c, d) ∈ A`, of Gauss norm at most `1`
  with constant term `v(det γ) n(d)`". Sketch: `map_smul` of `evalPoint`, the `evalPoint_col` field;
  `autFactor_one`: `detChar 1 = 1` (`map_one`), `col_one` (L5.10). Attacks: [3] decision D4: `v` on
  `L^×` with norm one — attack: does `norm_v` exclude Buzzard's literal `det^v`? Yes (erratum E3) and
  that is intended: without norm one the action is not norm-decreasing ✓. [4] the constant term
  `v(det γ) n(d)` of the roadmap is `evalPoint_autFactor` at `z = 0` ✓. SURVIVED.

#### Mathlib lemmas needed

`map_smul`, `map_one`, `Algebra.smul_def`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2.2–§1.2.3, §1.2.5–§1.2.6, §1.2.8, convention 3; [Buz07, §8, pp. 62–64, p. 66; §10, p. 72]; [Jac03, Definition 1.27]; [PFA] `UnitBall.lean`; [SRC] `QMF/Weight/04_Char.lean` (`ExpansionData`, `AnalyticWeight`, `lin_eval_cocycle`, `col_eq_of_mem`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D4** `v : Lˣ →* Kˣ` of norm one; Buzzard's `v(ϖ) = 1` is the construction `extendUnits`.

#### Progress

- 2026-10-06T21:01: evalPoint_autFactor (map_smul + evalPoint_col), autFactor_one (col_one); std axioms.

### [CLEANUP-ALL-2] `/cleanup-all` (before milestone T033 (M3))

- **Status**: done   (finished 2026-10-06T21:01) · **File**: `(project so far)` · **Depends on**: [CLEANUP-2], [CLEANUP-3], [CLEANUP-10], [T032] · **Type**: cleanup

Run `/cleanup-all` on `PhD/TauCeti/Code/OverconvergentForms/Weight/` (before milestone T033 (M3)). Inline, as the main agent (memory note `cleanup-inline-no-subagents`). Gates: every touched module builds with no warning; `runLinter` clean; no `sorry`; the four `omit`-able section-variable warnings of the skeleton are gone.

#### Progress

- 2026-10-06T21:01: Level, Dictionary, Mobius, Identity, Action, Expansion: each builds with no warning, runLinter passes on each, no sorry, no line over 100 chars.

### [T033] `autFactor_mul`

- **Status**: done   (finished 2026-10-06T21:01) · **File**: `Expansion.lean` · **Depends on**: [CLEANUP-ALL-2] · **Type**: milestone · **Leaves**: L5.12 · **Milestone**: M3 (part 1): the cocycle, derived

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- **The cocycle, derived**: `j_κ(δγ) = j_κ(γ) · (j_κ(δ) ∘ w_γ)`. Both sides are restricted series
agreeing at every integral point `e(z)` — by Möbius composition, the multiplicativity of `n` and
`v`, and `det(δγ) = det δ det γ` — hence equal by the identity theorem. ⚠ This is the only place a
character is analysed. Source: roadmap §1.2.6. -/
theorem autFactor_mul [CharZero K] (γ δ : S) :
    κ.autFactor (δ * γ) =
      κ.autFactor γ * mobiusSubst (e.multiBounds_toMulti κ.expansion.bounds γ.2) (κ.autFactor δ) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L5.12** `autFactor_mul` — [RM] §1.2.6 (quoted); the DERIVED cocycle. Sketch: substrate,
  *expansion data, uniqueness, the cocycle*. Discharge: L5.4 `ext_of_forall_evalPoint_eq`, `map_mul`
  of `evalPoint`, L5.9 `evalPoint_mobiusSubst`, L5.11 `evalPoint_autFactor` (three times), L5.7
  `linUnit_mul`, `map_mul` of `κ.n` and `κ.detChar` (`Units.val_mul`), `Matrix.det_mul` ✓ (inside
  `detUnits`), `mul_comm`/`mul_left_comm`/`ring`. Attacks: [1] orientation: RHS `= j(γ) · (j(δ) ∘ w_γ)`
  evaluated at `e(z)`: `v(det γ) n(cz+d) · v(det δ) n(c'(γz) + d')`; LHS `v(det δγ) n(c''z + d'')`;
  `linUnit_mul` gives `n(c''z+d'') = n(c'(γz)+d') n(cz+d)` ✓ and `v(det (δγ)) = v(det δ) v(det γ)` ✓
  equal. [2] `δ = 1` ✓. [3] `[CharZero K]` enters only here and in L5.10 ✓ (the engine needs none).
  [4] the roadmap's ⚠ "derived, never assumed" ✓ it is a theorem; [SRC] `ExpansionData.toWeightSeries`
  derived it the same way (`lin_eval_cocycle`, `evalAt_injOn`). SURVIVED. **Milestone M3 (part).**

#### Mathlib lemmas needed

`Units.val_mul`, `Matrix.det_mul`, `mul_comm`, `mul_left_comm`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2.2–§1.2.3, §1.2.5–§1.2.6, §1.2.8, convention 3; [Buz07, §8, pp. 62–64, p. 66; §10, p. 72]; [Jac03, Definition 1.27]; [PFA] `UnitBall.lean`; [SRC] `QMF/Weight/04_Char.lean` (`ExpansionData`, `AnalyticWeight`, `lin_eval_cocycle`, `col_eq_of_mem`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D3** engine `WeightData` (cocycle a field) / public `AnalyticWeight` (cocycle a theorem); **D6** `Embeddings.exists_integralBasis` is a Prop field; `[CharZero K]` where the identity theorem is used.

#### Progress

- 2026-10-06T21:01: M3 part 1 DONE: autFactor_mul derived by the identity theorem from linUnit_mul, evalPoint_mobiusSubst and multiplicativity of n, v; std axioms.

### [T034] `evalPoint_kappaSlash`, `kappaSlash_eq_of_n_eq`

- **Status**: done   (finished 2026-10-06T21:01) · **File**: `Expansion.lean` · **Depends on**: [T033] · **Type**: milestone · **Leaves**: L5.13, L5.14 · **Milestone**: M3 (part 2): the action on points; the action depends only on `(n, v)`

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- **The action on points** (Buzzard's definition): `(f ∣_κ γ)(e(z)) = n(cz + d) v(det γ) f(e(γ·z))`.
Source: roadmap §1.2.5; [Buz07, §10, p. 72]. -/
theorem evalPoint_kappaSlash [CharZero K] (γ : S) (f : Restricted K (1 : ι → ℝ))
    (z : Subring.unitClosedBall L) :
    e.evalPoint z (κ.kappaSlash γ f) =
      (κ.n (κ.expansion.bounds.linUnit γ.2 z) : K) * (κ.detChar γ : K) *
        e.evalPoint (κ.expansion.bounds.mobiusPt γ.2 z) f := by
  sorry

/-- The action depends only on the characters `(n, v)`, not on the expansion datum. Source: roadmap
§1.2.3, §1.2.6. -/
theorem kappaSlash_eq_of_n_eq [CharZero K] (κ' : AnalyticWeight e S ρ) (hn : κ.n = κ'.n)
    (hv : κ.v = κ'.v) (γ : S) : κ.kappaSlash γ = κ'.kappaSlash γ := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L5.13** `toWeightData` (discharged), `toWeightData_toMulti`/`_autFactor` (`rfl`), `kappaSlash`
  (def), `kappaSlash_apply` (`rfl`), `kappaSlash_one`, `kappaSlash_mul`, `norm_kappaSlash_apply_le`,
  `kappaSlash_monomial`, `norm_coeff_kappaSlash_monomial_le` (all discharged by L4),
  `kappaSlashAction` (discharged) — the re-exports. Compiles with no `sorry` except through the
  engine's leaves ✓. Attacks: [5] `norm_coeff_kappaSlash_monomial_le` passes `‖(γ : Matrix) 0 0‖ ≤ σ`
  through `e.norm_emb` ✓ (compiled). SURVIVED (compiles).

- **L5.14** `evalPoint_kappaSlash`, `kappaSlash_eq_of_n_eq` — [RM] §1.2.5 "in particular, for a
  polynomial `f` and `z ∈ 𝒪`, `(f ∣_κ γ)(z) = n(cz + d) v(det γ) f((az + b)/(cz + d))` — Buzzard's
  definition on points"; §1.2.6 "by clause 3 it depends only on `(n, v)` and `γ`, not on the expansion
  datum". Sketch: `kappaSlash_apply`, `map_mul` of `evalPoint`, L5.11, L5.9; for the second: the two
  `toWeightData` agree on `toMulti` (same `e`) and on `autFactor` (`col_eq_of_mem` with `hn ▸`,
  `detChar` with `hv ▸`), so `kappaSlash_apply` gives equality (`ContinuousLinearMap.ext`). Attacks:
  [1] the roadmap says "for a polynomial `f`" — the statement here is for every `f ∈ A` ✓ stronger,
  true since `evalPoint` is defined on all of `A`. [3] `hn : κ.n = κ'.n` is a dependent equality
  (`ExpansionData` is indexed by `n`): the proof rewrites `κ'` along `hn` — `subst`/`cases` on the
  structure *(ticket: destructure `κ'`, `obtain ⟨n', v', hv', E'⟩ := κ'`, then `subst`)* ✓. [4]
  [Buz07, §10] `(h.γ)(z, x) := n(cz + d, x) (v(det(γ))(x)) h((az + b)/(cz + d), x)` ✓ literally.
  SURVIVED. **Milestone M3 (part).**

#### Mathlib lemmas needed

`ContinuousLinearMap.ext`, `map_mul`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2.2–§1.2.3, §1.2.5–§1.2.6, §1.2.8, convention 3; [Buz07, §8, pp. 62–64, p. 66; §10, p. 72]; [Jac03, Definition 1.27]; [PFA] `UnitBall.lean`; [SRC] `QMF/Weight/04_Char.lean` (`ExpansionData`, `AnalyticWeight`, `lin_eval_cocycle`, `col_eq_of_mem`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D3** engine `WeightData` (cocycle a field) / public `AnalyticWeight` (cocycle a theorem).

#### Progress

- 2026-10-06T21:01: M3 part 2 DONE: evalPoint_kappaSlash (Buzzard's formula on points), kappaSlash_eq_of_n_eq (destructure both weights, subst, col_eq_of_mem); std axioms.

### [CLEANUP-13] `/cleanup` of `Expansion.lean` (cadence: three proof tickets)

- **Status**: done   (finished 2026-10-06T21:01) · **File**: `Expansion.lean` · **Depends on**: [T034] · **Type**: cleanup

Run `/cleanup` on `PhD/TauCeti/Code/OverconvergentForms/Weight/Expansion.lean` (cadence: three proof tickets). Style audit + golf to mathlib standards; add `omit … in` where the skeleton's 'automatically included section variable(s) unused' warnings point; check docstrings cite the roadmap clause and the source; no statement changes without a B2 entry in `b2_log.jsonl`.

#### Progress

- 2026-10-06T21:01: Inline: docstrings and long signatures reflowed to 100 chars.

### [T035] `kappaSlash_restrict`, `continuous_n`

- **Status**: done   (finished 2026-10-06T21:01) · **File**: `Expansion.lean` · **Depends on**: [CLEANUP-13] · **Type**: proof · **Leaves**: L5.15

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
theorem kappaSlash_restrict [CharZero K] {S' : Submonoid (Matrix (Fin 2) (Fin 2) L)} (hS : S' ≤ S)
    {ρ' : ℝ} (hρρ' : ρ ≤ ρ') (hρ' : ρ' < 1) (γ : S') :
    (κ.restrict hS hρρ' hρ').kappaSlash γ = κ.kappaSlash ⟨γ, hS γ.2⟩ := by
  sorry

/-- The character of a weight is continuous as soon as the level contains a lower unipotent
`((1 0), (c 1))`, `c ≠ 0`: `n(1 + cz) = col(c, 1)(e(z))` is continuous in `z`, so `n` is continuous
on the open subgroup `1 + c𝒪_L`. (The roadmap asks for a continuous character; continuity is a
consequence of the expansion data, not an extra field.) Source: roadmap §1.2.2. -/
theorem continuous_n (hc : ∃ c : L, c ≠ 0 ∧ !![1, 0; c, 1] ∈ S) : Continuous κ.n := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L5.15** `restrict` (discharged), `kappaSlash_restrict`, `continuous_n` — [RM] §1.2.8 "the action
  of `Σ'` is the restriction"; §1.2.2 "a continuous character `n`" (decision D5). Sketch:
  `kappaSlash_restrict` by `kappaSlash_apply` on both sides (`rfl`-ish after unfolding; the
  `MultiBounds` proof arguments differ but are `Prop`); `continuous_n`: substrate, *continuity of
  `n`*. Discharge: `Units.continuous_iff` ✓ *(name to confirm at ticket)*, `continuous_of_continuousAt_one`
  ✓, L5.1, `Continuous.comp`, `Metric.continuousAt_iff`/`Filter.Tendsto` on the neighbourhood
  `{u | ‖u − 1‖ ≤ ‖c‖}` (open: `Metric.isOpen_ball`-type with `≤` → use `‖u − 1‖ < ‖c‖·2`… or the
  closed ball is open in an ultrametric space: `IsUltrametricDist.isOpen_closedBall` ✓), `Units.val`
  continuous (`Units.continuous_val` ✓), `Units.continuous_coe_inv` ✓. Attacks: [1] is continuity
  false for some weight? If `S` has no lower unipotent (e.g. `S = {1}`), `ExpansionData` constrains
  `n` only at `1`, and a discontinuous `n` is an `AnalyticWeight` — hence the hypothesis `hc` is
  NECESSARY ✓ (and the roadmap's `SigmaNorm` levels contain `((1 0), (c 1))` for every `‖c‖ ≤ ρ`,
  `ρ > 0`). [3] `c ≠ 0` necessary (`c = 0` gives no neighbourhood) ✓. [5] moderate risk on the
  `Units` topology lemma names; flagged *(ticket)*. SURVIVED.

#### Mathlib lemmas needed

`Units.continuous_iff`, `continuous_of_continuousAt_one`, `Units.continuous_val`, `Units.continuous_coe_inv`, `IsUltrametricDist.isOpen_closedBall`, `Metric.continuousAt_iff`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.2.2–§1.2.3, §1.2.5–§1.2.6, §1.2.8, convention 3; [Buz07, §8, pp. 62–64, p. 66; §10, p. 72]; [Jac03, Definition 1.27]; [PFA] `UnitBall.lean`; [SRC] `QMF/Weight/04_Char.lean` (`ExpansionData`, `AnalyticWeight`, `lin_eval_cocycle`, `col_eq_of_mem`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D5** continuity of `n` is a theorem (`continuous_n`), not a field.

#### Progress

- 2026-10-06T21:01: kappaSlash_restrict (pointwise rfl), continuous_n: continuous_of_continuousAt_one + Units.isEmbedding_val₀, on the open set ‖u-1‖<‖c‖ n(u) = col(c,1)(e((u-1)/c)) via continuous_aeval_point; std axioms.

### [CLEANUP-14] `/cleanup` of `Expansion.lean` (final for the file)

- **Status**: done   (finished 2026-10-06T21:01) · **File**: `Expansion.lean` · **Depends on**: [T035] · **Type**: cleanup

Run `/cleanup` on `PhD/TauCeti/Code/OverconvergentForms/Weight/Expansion.lean` (final for the file). Style audit + golf to mathlib standards; add `omit … in` where the skeleton's 'automatically included section variable(s) unused' warnings point; check docstrings cite the roadmap clause and the source; no statement changes without a B2 entry in `b2_log.jsonl`.

#### Progress

- 2026-10-06T21:01: Expansion.lean final: build clean with no warnings, runLinter passes, module docstring rewrapped without splitting code spans.

### [T036] `extendUnits`, `extendUnits_unitsIncl`, `extendUnits_unit` and 1 more

- **Status**: done   (finished 2026-10-06T21:13) · **File**: `Algebraic.lean` · **Depends on**: [T034] · **Type**: proof · **Leaves**: L6.1

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- **Buzzard's extension of `v`**: for a pseudo-uniformiser `ϖ` with `‖L^×‖ = ‖ϖ‖^ℤ`, a character
`v₀` of `𝒪_L^×` extends to `L^×` by `v(ϖ^k u) := v₀(u)`. Source: roadmap §1.2.2; [Buz07, §10, p. 71]
("`v(π_j) = 1`"). -/
noncomputable def extendUnits (ϖ : NormedRing.PseudoUniformizer L)
    (hϖ : ∀ x : L, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖(ϖ : L)‖ ^ k)
    (v₀ : (Subring.unitClosedBall L)ˣ →* Kˣ) : Lˣ →* Kˣ where
  toFun x := v₀ (unitOfNormEqOne ((x : L) * ((ϖ.unit ^ (Classical.choose (hϖ x x.ne_zero)))⁻¹ : Lˣ))
    (by sorry))
  map_one' := by sorry
  map_mul' := by sorry

theorem extendUnits_unitsIncl (ϖ : NormedRing.PseudoUniformizer L)
    (hϖ : ∀ x : L, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖(ϖ : L)‖ ^ k) (v₀ : (Subring.unitClosedBall L)ˣ →* Kˣ)
    (u : (Subring.unitClosedBall L)ˣ) : extendUnits ϖ hϖ v₀ (unitsIncl L u) = v₀ u := by
  sorry

theorem extendUnits_unit (ϖ : NormedRing.PseudoUniformizer L)
    (hϖ : ∀ x : L, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖(ϖ : L)‖ ^ k) (v₀ : (Subring.unitClosedBall L)ˣ →* Kˣ) :
    extendUnits ϖ hϖ v₀ ϖ.unit = 1 := by
  sorry

theorem norm_extendUnits (ϖ : NormedRing.PseudoUniformizer L)
    (hϖ : ∀ x : L, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖(ϖ : L)‖ ^ k) (v₀ : (Subring.unitClosedBall L)ˣ →* Kˣ)
    (hv₀ : ∀ u, ‖(v₀ u : K)‖ = 1) (x : Lˣ) : ‖(extendUnits ϖ hϖ v₀ x : K)‖ = 1 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L6.1** `extendUnits` (fields: norm of `u`, `map_one'`, `map_mul'`), `extendUnits_unitsIncl`,
  `extendUnits_unit`, `norm_extendUnits` — [RM] §1.2.2 "extended to the nonzero elements of `𝒪` by
  `v(ϖ^k u) := v(u)` (Buzzard §10, '`v(π_j) = 1`')". Sketch: substrate, *`extendUnits`*. Discharge:
  `Classical.choose_spec`, `zpow_right_injective₀` ✓, `norm_zpow` ✓ ([PFA] `PseudoUniformizer.norm_zpow`
  ✓), `norm_mul`, `norm_inv`, `zpow_add₀`, `Units.ext`, `map_mul` of `v₀`. Attacks: [1] is `hϖ`
  (`‖L^×‖ = ‖ϖ‖^ℤ`) necessary? For `L = ℂ_p` no such `ϖ` exists and Buzzard's extension is undefined
  — the roadmap's `L = F_𝔭` is discretely valued ✓ the hypothesis is the honest one. [2] `x` a unit:
  `k = 0`, `extendUnits x = v₀ x` ✓ (`extendUnits_unitsIncl`). [3] `hv₀` (norm one on `𝒪_L^×`) is
  needed for `norm_extendUnits` ✓ (B2 lesson J015). [4] [Buz07, p. 71] ✓ "`v(π_j) = 1`". SURVIVED.

#### Mathlib lemmas needed

`Classical.choose_spec`, `zpow_right_injective₀`, `NormedRing.PseudoUniformizer.norm_zpow`, `norm_mul`, `norm_inv`, `zpow_add₀`, `Units.ext`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.3.1, §1.3.4, §1.3.5; [Buz07, §10, p. 71; §11, pp. 73–74]; [PFA] `Tate.lean` (`PseudoUniformizer`), `UnitBall.lean` (`closedBallIdeal`); [SRC] `QMF/Weight/06_Algebraic.lean` (`algExpansionData`, `norm_coeff_linear_pow_le`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D4** `v : Lˣ →* Kˣ` of norm one; Buzzard's `v(ϖ) = 1` is the construction `extendUnits`.

#### Progress

- 2026-10-06T21:13: extendUnits: private helpers choose_eq_of_norm_eq (zpow_right_injective₀) and norm_mul_inv_zpow_choose; map_one'/map_mul' by Units.ext + Subtype.ext after coe_unitOfNormEqOne removes the dependent proof, then rewriting the exponent; extendUnits_unitsIncl/_unit/norm_extendUnits; std axioms.

### [T037] `algChar`, `coe_algChar`, `norm_algChar` and 2 more

- **Status**: done   (finished 2026-10-06T21:13) · **File**: `Algebraic.lean` · **Depends on**: [T036] · **Type**: proof · **Leaves**: L6.2, L6.3

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- **The algebraic character** `u ↦ ∏_i i(u)^{n_i}` of `𝒪_L^×`, `n ∈ ℤ^ι`. Source: roadmap §1.3.1;
[Buz07, §11, p. 73]. -/
noncomputable def algChar (n : ι → ℤ) : (Subring.unitClosedBall L)ˣ →* Kˣ where
  toFun u := ∏ i, (Units.map ((e.emb i).comp (Subring.unitClosedBall L).subtype).toMonoidHom u) ^ n i
  map_one' := by sorry
  map_mul' := by sorry

theorem coe_algChar (n : ι → ℤ) (u : (Subring.unitClosedBall L)ˣ) :
    (e.algChar n u : K) = ∏ i, e.emb i (u : Subring.unitClosedBall L) ^ n i := by
  sorry

theorem norm_algChar (n : ι → ℤ) (u : (Subring.unitClosedBall L)ˣ) : ‖(e.algChar n u : K)‖ = 1 := by
  sorry

/-- For `n ≥ 0` the expansion is the polynomial `∏_i (i(d) + i(c) z_i)^{n_i}`. -/
theorem algCol_natCast (n : ι → ℕ) (c d : L) :
    e.algCol (fun i => (n i : ℤ)) c d = ∏ i, lin (e.toMulti !![1, 0; c, d]) i ^ n i := by
  sorry

/-- **The algebraic weights have expansion data at every level**. Source: roadmap §1.3.1 ("This is
an expansion datum at every level `(SigmaNorm F_𝔭 ρ, ρ)`, `ρ < 1` (Buzzard §11: `r(κ)_j = |π_j|`)"). -/
noncomputable def algExpansionData {S : Submonoid (Matrix (Fin 2) (Fin 2) L)} {ρ : ℝ}
    (hb : LevelBounds S ρ) (n : ι → ℤ) : ExpansionData e S ρ (e.algChar n) where
  bounds := hb
  col := e.algCol n
  rowBound_col := by sorry
  evalPoint_col := by sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L6.2** `algChar` (fields), `coe_algChar`, `norm_algChar` — [RM] §1.3.1 "`n(u) := ∏_i i(u)^{n_i}`".
  Sketch: `Finset.prod_mul_distrib` ✓, `mul_zpow` ✓, `map_mul` of `Units.map`, `Units.val_zpow_eq_zpow_val`
  ✓ *(name to confirm)*, `norm_prod`, `norm_zpow`, `norm_emb`, `‖u‖ = 1` ([PFA]
  `NormedRing.isUnit_iff_norm_eq_one` ✓). Attacks: [2] `n = 0`: the trivial character ✓. [4]
  [Buz07, §11] `α ↦ ∏ α_i^{n_i}` ✓. SURVIVED.

- **L6.3** `algCol` (def), `algCol_natCast`, `algExpansionData` (fields `rowBound_col`,
  `evalPoint_col`), `algWeight` (discharged), `algWeight_n`/`_v` (`rfl`) — [RM] §1.3.1 "`col(c, d) :=
  ∏_i (i(d) + i(c) z_i)^{n_i}`, a polynomial when every `n_i ≥ 0` and otherwise the product of
  `i(d)^{n_i} (1 + (i(c)/i(d)) z_i)^{n_i}` with the binomial series of a negative integer exponent […].
  This is an expansion datum at every level `(SigmaNorm F_𝔭 ρ, ρ)`, `ρ < 1`". Sketch: substrate,
  *algebraic expansion data*; `algCol_natCast`: `Int.toNat_natCast`, `Int.toNat_of_nonpos`/`neg_natCast`
  → `pow_zero`, `mul_one`. Discharge: L2.12 `rowBound_lin`, `rowBound_linInv` (with
  `MultiBounds ρ (e.toMulti !![1,0;c,d])` from `hg` — the matrix `!![1, 0; c, d]` has `a = 1`, `b = 0`
  integral, same `c, d` ✓), L2.11 `RowBound.prod`, `RowBound.pow`, `RowBound.mul`; L5.9 `evalPoint_lin`,
  `lin_mul_linInv` (L2.4) + `map_mul`, `zpow` arithmetic, `coe_algChar` (L6.2). Attacks: [1] erratum
  E4: no binomial coefficients; the geometric inverse gives the same series ✓ (the roadmap's
  "coefficients are integers" is the `RowBound ρ` bound). [2] `n_i < 0`: `linInv^{|n_i|}` ✓ restricted
  by L2.4. [3] the level bounds are the only hypothesis ✓ "at every level". [4] [Buz07, §11]
  "`r(κ)_j = |π_j|`" — data at every `ρ < 1` ✓ even better than `|π|`. SURVIVED.

#### Mathlib lemmas needed

`Finset.prod_mul_distrib`, `mul_zpow`, `Units.val_zpow_eq_zpow_val`, `norm_prod`, `norm_zpow`, `NormedRing.isUnit_iff_norm_eq_one`, `Int.toNat_natCast`, `zpow_natCast`, `zpow_neg`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.3.1, §1.3.4, §1.3.5; [Buz07, §10, p. 71; §11, pp. 73–74]; [PFA] `Tate.lean` (`PseudoUniformizer`), `UnitBall.lean` (`closedBallIdeal`); [SRC] `QMF/Weight/06_Algebraic.lean` (`algExpansionData`, `norm_coeff_linear_pow_le`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D4** `v : Lˣ →* Kˣ` of norm one; Buzzard's `v(ϖ) = 1` is the construction `extendUnits`.

#### Progress

- 2026-10-06T21:13: algChar (simp; mul_zpow, prod_mul_distrib), coe_algChar, norm_algChar; algCol_natCast; algExpansionData via private multiBounds_lowerRow and pow_toNat_mul_inv_pow_toNat (zpow from toNat parts), rowBound_lin/linInv, evalPoint_lin + lin_mul_linInv; std axioms.

### [T038] `kappaSlash_algWeight_monomial`

- **Status**: done   (finished 2026-10-06T21:13) · **File**: `Algebraic.lean` · **Depends on**: [T037] · **Type**: proof · **Leaves**: L6.4

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- **The algebraic weight on monomials**: for `r ≤ n`, `z^r ∣ γ = v(det γ) ∏_i L_i^{n_i − r_i} N_i^{r_i}`
— Buzzard's `L_{n,v}` formula. Source: roadmap §1.3.2; [Buz07, §9, p. 68]. -/
theorem kappaSlash_algWeight_monomial [CharZero K] (hb : LevelBounds S ρ) (n : ι → ℕ)
    (v : Lˣ →* Kˣ) (hv : ∀ x, ‖(v x : K)‖ = 1) (γ : S) (r : ι →₀ ℕ) (hr : ∀ i, r i ≤ n i) :
    (e.algWeight hb (fun i => (n i : ℤ)) v hv).kappaSlash γ (monomial 1 r 1) =
      ((e.algWeight hb (fun i => (n i : ℤ)) v hv).detChar γ : K) •
        ∏ i, lin (e.toMulti γ) i ^ (n i - r i) * num (e.toMulti γ) i ^ r i := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L6.4** `kappaSlash_algWeight_monomial` — [RM] §1.3.2 "`f ∣_{(n,v)} γ := ∏_i i(det γ)^{v_i} ∏_i
  (c_i z_i + d_i)^{n_i} · f(w_γ(z))`" at `f = z^r`, `r ≤ n`: `lin^{n−r} num^r`. Sketch: L4.3
  `kappaSlash_monomial`, `algCol_natCast`, `autFactor` unfolding, `mobius = num · linInv`,
  `mul_pow`, `lin^{n} · (num · linInv)^r = lin^{n−r} (lin · linInv)^r num^r = lin^{n−r} num^r`
  (`pow_sub_mul_pow`-type, `lin_mul_linInv`, `one_pow`), `Finset.prod_mul_distrib`. Attacks: [3]
  `r ≤ n` is necessary (else `lin^{n−r}` is `lin^{-(r−n)}`, a series, not a polynomial — the roadmap
  states the polynomial form for `m ≤ n`) ✓. [4] [Buz07, §9] `(c_i Z_i + d_i)^{n_i} ((a_i Z_i + b_i)/(c_i Z_i +
  d_i))^{m_i}` ✓ with the `det^v` as the normalised `detChar` (erratum E3). SURVIVED.

#### Mathlib lemmas needed

`mul_pow`, `pow_sub_mul_pow`, `one_pow`, `Finset.prod_mul_distrib`, `Finsupp.prod`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.3.1, §1.3.4, §1.3.5; [Buz07, §10, p. 71; §11, pp. 73–74]; [PFA] `Tate.lean` (`PseudoUniformizer`), `UnitBall.lean` (`closedBallIdeal`); [SRC] `QMF/Weight/06_Algebraic.lean` (`algExpansionData`, `norm_coeff_linear_pow_le`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D1** the carrier is the Tate algebra `MvPowerSeries.Restricted K (1 : ι → ℝ)`; the action is the substitution operator, the kernel array is the theorem `kappaSlash_monomial`.

#### Progress

- 2026-10-06T21:13: kappaSlash_algWeight_monomial: kappaSlash_monomial, algCol_natCast, Finsupp.prod_fintype, lin^n·(num·linInv)^r = lin^(n-r)·num^r·(lin·linInv)^r by ring; std axioms.

### [CLEANUP-15] `/cleanup` of `Algebraic.lean` (cadence: three proof tickets)

- **Status**: done   (finished 2026-10-06T21:13) · **File**: `Algebraic.lean` · **Depends on**: [T038] · **Type**: cleanup

Run `/cleanup` on `PhD/TauCeti/Code/OverconvergentForms/Weight/Algebraic.lean` (cadence: three proof tickets). Style audit + golf to mathlib standards; add `omit … in` where the skeleton's 'automatically included section variable(s) unused' warnings point; check docstrings cite the roadmap clause and the source; no statement changes without a B2 entry in `b2_log.jsonl`.

#### Progress

- 2026-10-06T21:13: Inline: omit annotations on the extendUnits lemmas, coe/norm_algChar and the private helpers.

### [T039] `lowerRightResidue`, `lowerRightResidue_apply`, `residueUnit_linUnit`

- **Status**: done   (finished 2026-10-06T21:13) · **File**: `Algebraic.lean` · **Depends on**: [CLEANUP-15] · **Type**: proof · **Leaves**: L6.5

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- **The lower-right residue character** `γ ↦ d mod 𝔞_ρ` of the level: multiplicative because
`(δγ)_{11} = c'b + d'd ≡ d'd mod 𝔞_ρ`. Source: roadmap §1.2.8 ("a nebentypus pulled back through
`d`"), §1.3.4. -/
noncomputable def lowerRightResidue :
    S →* (Subring.unitClosedBall L ⧸ NormedRing.closedBallIdeal L ⟨ρ, hb.rho_nonneg⟩)ˣ where
  toFun g := hb.residueUnit ((g : Matrix (Fin 2) (Fin 2) L) 1 1)
  map_one' := by sorry
  map_mul' := by sorry

theorem lowerRightResidue_apply (g : S) :
    hb.lowerRightResidue g =
      Units.map (Ideal.Quotient.mk (NormedRing.closedBallIdeal L ⟨ρ, hb.rho_nonneg⟩)).toMonoidHom
        (hb.dUnit g.2) := by
  sorry

/-- On the level, `cz + d ≡ d mod 𝔞_ρ` for every integral `z`. Source: roadmap §1.3.4 ("because
`ψ(cz + d) = ψ(d)` for `z ∈ 𝒪` and `ϖ^α ∣ c`"). -/
theorem residueUnit_linUnit {g : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S) (z : Subring.unitClosedBall L) :
    Units.map (Ideal.Quotient.mk (NormedRing.closedBallIdeal L ⟨ρ, hb.rho_nonneg⟩)).toMonoidHom
      (hb.linUnit hg z) = hb.residueUnit (g 1 1) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L6.5** `residueUnit` (def), `lowerRightResidue` (fields), `lowerRightResidue_apply`,
  `residueUnit_linUnit` — [RM] §1.3.4 "For a character `ψ` of `𝒪^×` of finite order factoring through
  `(𝒪/𝔭^α)^×` […] at every level with `‖c‖ ≤ ‖ϖ‖^α` […] because `ψ(cz + d) = ψ(d)` for `z ∈ 𝒪` and
  `ϖ^α ∣ c`". Sketch: substrate, *nebentypus*. Discharge: `dif_pos` with L1.3 `d_unit`,
  `Ideal.Quotient.eq` ✓, [PFA] `NormedRing.mem_closedBallIdeal` ✓, `Units.ext`, `Units.map`,
  `Matrix.mul_apply`, `Fin.sum_univ_two`, ultrametric bound `‖c' b‖ ≤ ρ`. Attacks: [1] the ideal is
  `𝔞_ρ = {‖x‖ ≤ ρ}` (the roadmap's `𝔭^α` at `ρ = ‖ϖ‖^α`) — for a non-discretely-valued `L` this is
  still an ideal ✓ ([PFA] `closedBallIdeal`). [2] `ρ = 0`: `𝔞_0 = 0`, residue = `d` itself ✓. [3]
  `residueUnit` junk `1` off the unit circle is never hit on the level (`‖d‖ = 1`) ✓
  (`lowerRightResidue_apply`). [4] [Buz07, p. 74] the submonoid "`π^t ∣ (d − 1)`" is the kernel of
  this character ✓. SURVIVED.

#### Mathlib lemmas needed

`dif_pos`, `Ideal.Quotient.eq`, `NormedRing.mem_closedBallIdeal`, `Units.ext`, `Matrix.mul_apply`, `Fin.sum_univ_two`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.3.1, §1.3.4, §1.3.5; [Buz07, §10, p. 71; §11, pp. 73–74]; [PFA] `Tate.lean` (`PseudoUniformizer`), `UnitBall.lean` (`closedBallIdeal`); [SRC] `QMF/Weight/06_Algebraic.lean` (`algExpansionData`, `norm_coeff_linear_pow_le`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D9** `SigmaNorm L ρ hρ0 hρ` with explicit real hypotheses; `LevelBounds S ρ` bundles them with the four conditions.

#### Progress

- 2026-10-06T21:13: residueUnit_of_mem (new public helper, dif_pos), lowerRightResidue (map_mul': (gh)₁₁ − g₁₁h₁₁ = g₁₀h₀₁ ∈ 𝔞_ρ via Ideal.Quotient.eq + mem_closedBallIdeal as term steps), lowerRightResidue_apply, residueUnit_linUnit; std axioms.

### [T040] `twistResidue`, `kappaSlash_twistResidue`

- **Status**: done   (finished 2026-10-06T21:13) · **File**: `Algebraic.lean` · **Depends on**: [T039] · **Type**: proof · **Leaves**: L6.6

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- **Loading a character of the residue ring**: `col(c, d) ↦ ψ(d̄) • col(c, d)` is an expansion
datum for `u ↦ n(u) ψ(ū)`. Stated for every `n` with expansion data (the roadmap's `n` algebraic is
the instance `classicalShape`). Source: roadmap §1.3.4; [Buz07, §11, p. 74]. -/
noncomputable def twistResidue
    (ψ : (Subring.unitClosedBall L ⧸ NormedRing.closedBallIdeal L ⟨ρ, E.bounds.rho_nonneg⟩)ˣ →* Kˣ)
    (hψ : ∀ x, ‖(ψ x : K)‖ = 1) :
    ExpansionData e S ρ (n * ψ.comp (Units.map
      (Ideal.Quotient.mk (NormedRing.closedBallIdeal L ⟨ρ, E.bounds.rho_nonneg⟩)).toMonoidHom)) where
  bounds := E.bounds
  col c d := (ψ (E.bounds.residueUnit d) : K) • E.col c d
  rowBound_col hg := (E.rowBound_col hg).smul (hψ _).le
  evalPoint_col := by sorry

/-- The loaded weight acts by the twist of the action by `ψ ∘ (lower-right residue)`. Source:
roadmap §1.2.8, §1.3.4. -/
theorem kappaSlash_twistResidue [CharZero K]
    (ψ : (Subring.unitClosedBall L ⧸ NormedRing.closedBallIdeal L ⟨ρ, κ.bounds.rho_nonneg⟩)ˣ →* Kˣ)
    (hψ : ∀ x, ‖(ψ x : K)‖ = 1) (γ : S) :
    (κ.twistResidue ψ hψ).kappaSlash γ = (ψ (κ.bounds.lowerRightResidue γ) : K) • κ.kappaSlash γ := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L6.6** `ExpansionData.twistResidue` (field `evalPoint_col`), `twistResidue_col` (`rfl`),
  `AnalyticWeight.twistResidue` (discharged), `kappaSlash_twistResidue` — [RM] §1.3.4 "the character
  `n ψ` has […] the expansion datum `col(c, d) = ψ(d) · ∏ (i(d) + i(c) z_i)^{n_i}`"; §1.2.8 ("a
  nebentypus pulled back through `d`"). Sketch: substrate; `kappaSlash_twistResidue`:
  `(κ.twistResidue ψ).toWeightData = κ.toWeightData.twist (ψ ∘ lowerRightResidue) _` on `autFactor`
  (`twistResidue_col`, `lowerRightResidue_apply`, `smul_smul`, `mul_comm`), then L4.5
  `twist_kappaSlash`. Attacks: [1] B2 lesson T-AG1a: the nebentypus factor is constant in `z` ✓
  (`residueUnit_linUnit`). [3] erratum E5: stated for every `n`, not only algebraic ✓ (the proof never
  uses algebraicity). [4] [Buz07, p. 74] `κ(α, β) = ε(α) ∏ α_i^{n_i} β_i^{v_i}` ✓. SURVIVED.

#### Mathlib lemmas needed

`smul_smul`, `mul_comm`, `map_smul`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.3.1, §1.3.4, §1.3.5; [Buz07, §10, p. 71; §11, pp. 73–74]; [PFA] `Tate.lean` (`PseudoUniformizer`), `UnitBall.lean` (`closedBallIdeal`); [SRC] `QMF/Weight/06_Algebraic.lean` (`algExpansionData`, `norm_coeff_linear_pow_le`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D4** `v : Lˣ →* Kˣ` of norm one; Buzzard's `v(ϖ) = 1` is the construction `extendUnits`.

#### Progress

- 2026-10-06T21:13: twistResidue.evalPoint_col (map_smul, residueUnit_linUnit), kappaSlash_twistResidue (show + smul_comm + smul_mul_assoc); std axioms.

### [T041] `autFactor_classicalShape`, `smul_one_mem_sigmaNorm`, `kappaSlash_smul_one` and 1 more

- **Status**: done   (finished 2026-10-06T21:13) · **File**: `Algebraic.lean` · **Depends on**: [T040] · **Type**: proof · **Leaves**: L6.7, L6.8

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- The automorphy factor of a classical-shape weight: `ψ(d̄) v(det γ) ∏ (i(d) + i(c) z_i)^{n_i}`. -/
theorem autFactor_classicalShape (hb : LevelBounds S ρ) (n : ι → ℤ) (v : Lˣ →* Kˣ)
    (hv : ∀ x, ‖(v x : K)‖ = 1)
    (ψ : (Subring.unitClosedBall L ⧸ NormedRing.closedBallIdeal L ⟨ρ, hb.rho_nonneg⟩)ˣ →* Kˣ)
    (hψ : ∀ x, ‖(ψ x : K)‖ = 1) (γ : S) :
    (e.classicalShape hb n v hv ψ hψ).autFactor γ =
      ((ψ (hb.lowerRightResidue γ) : K) * ((e.algWeight hb n v hv).detChar γ : K)) •
        e.algCol n ((γ : Matrix (Fin 2) (Fin 2) L) 1 0) ((γ : Matrix (Fin 2) (Fin 2) L) 1 1) := by
  sorry

/-- The scalar matrix `u · 1`, `u ∈ 𝒪_L^×`, lies in every `Σ(ρ)`. Source: roadmap §1.3.5. -/
theorem smul_one_mem_sigmaNorm {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) (u : (Subring.unitClosedBall L)ˣ) :
    ((u : Subring.unitClosedBall L) : L) • (1 : Matrix (Fin 2) (Fin 2) L) ∈ SigmaNorm L ρ hρ0 hρ := by
  sorry

/-- **The scalars act by `κ(u, u²) = n(u) v(u²)`**. Source: roadmap §1.3.5 ("acts on `A` by the scalar
`n(u) v(u²)`"). -/
theorem kappaSlash_smul_one [CharZero K] (u : (Subring.unitClosedBall L)ˣ)
    (hu : ((u : Subring.unitClosedBall L) : L) • (1 : Matrix (Fin 2) (Fin 2) L) ∈ S)
    (f : Restricted K (1 : ι → ℝ)) :
    κ.kappaSlash ⟨_, hu⟩ f = ((κ.n u : K) * (κ.v (unitsIncl L u ^ 2) : K)) • f := by
  sorry

/-- **The weight condition**: an element fixed by a scalar acting through `κ(u, u²) ≠ 1` is zero;
hence `A^G = 0` unless `κ(γ, γ²) = 1` on `G`. Source: roadmap §1.3.5. -/
theorem eq_zero_of_kappaSlash_eq_self_of_ne_one [CharZero K] (u : (Subring.unitClosedBall L)ˣ)
    (hu : ((u : Subring.unitClosedBall L) : L) • (1 : Matrix (Fin 2) (Fin 2) L) ∈ S)
    (hκ : (κ.n u : K) * (κ.v (unitsIncl L u ^ 2) : K) ≠ 1) {f : Restricted K (1 : ι → ℝ)}
    (hf : κ.kappaSlash ⟨_, hu⟩ f = f) : f = 0 := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L6.7** `classicalShape` (discharged), `autFactor_classicalShape` — [RM] §1.3.4 "The weights
  `(n ψ, v)` are the classical-shape weights: their automorphy factor is a constant times a
  polynomial in `c z + d`". Sketch: unfold `autFactor`, `twistResidue_col`, `algWeight`'s `col`,
  `lowerRightResidue_apply`/`residueUnit`, `smul_smul`. Attacks: [2] `ψ = 1` ✓ `algWeight`. [4]
  "a constant times a polynomial" ✓ for `n ≥ 0`; for `n_i < 0` it is a constant times `algCol`, as
  stated ✓. SURVIVED.

- **L6.8** `smul_one_mem_sigmaNorm`, `kappaSlash_smul_one`, `eq_zero_of_kappaSlash_eq_self_of_ne_one`
  — [RM] §1.3.5 (quoted). Sketch: substrate, *scalars*. Discharge: `Matrix.smul_apply`,
  `Matrix.one_apply` ✓, `Matrix.det_smul` ✓ (`det (u • 1) = u^2 det 1`), `Fintype.card_fin`; L5.4 for
  `col(0, u) = C (n u)` (both evaluate to `n(u)`: the `evalPoint_col` field with `linUnit (u·1) z = u`),
  `mobius_one`-style computation for `w = X` (`num = C u * X`, `linInv = C u⁻¹`, `mobius = X` by
  `C u * X * C u⁻¹ = X`), L2.1 `aeval_X_eq_self`, `kappaSlash_apply`, `Algebra.smul_def`;
  `sub_eq_zero`, `smul_eq_zero`, `sub_ne_zero`. Attacks: [1] `v(u²)` with `u² ∈ L^×`: `det (u • 1) =
  u²` ✓ `unitsIncl L u ^ 2`. [2] `u = 1` ✓ `kappaSlash_one`. [3] `hu : u • 1 ∈ S` is a hypothesis (true
  for `SigmaNorm`, L6.8's first lemma, not for every `S`) ✓. [4] "`κ(u, u²) = n(u) v(u²)`" ✓;
  [Buz07, §9, p. 68] "the totally positive units in `𝒪_F^×` act trivially on `L_{n,v}` if `n + 2v ∈ ℤ`"
  is the classical instance. SURVIVED.

#### Mathlib lemmas needed

`Matrix.smul_apply`, `Matrix.one_apply`, `Matrix.det_smul`, `Fintype.card_fin`, `Algebra.smul_def`, `sub_eq_zero`, `smul_eq_zero`, `sub_ne_zero`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.3.1, §1.3.4, §1.3.5; [Buz07, §10, p. 71; §11, pp. 73–74]; [PFA] `Tate.lean` (`PseudoUniformizer`), `UnitBall.lean` (`closedBallIdeal`); [SRC] `QMF/Weight/06_Algebraic.lean` (`algExpansionData`, `norm_coeff_linear_pow_le`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D4** `v : Lˣ →* Kˣ` of norm one; Buzzard's `v(ϖ) = 1` is the construction `extendUnits`.

#### Progress

- 2026-10-06T21:13: autFactor_classicalShape (mul_smul, smul_comm), smul_one_mem_sigmaNorm, kappaSlash_smul_one (Möbius of a scalar is X via lin_mul_linInv, mobiusSubst = id by algHom_ext_of_continuous, col(0,u) = C n(u) by the identity theorem, det = u²), eq_zero_of_kappaSlash_eq_self_of_ne_one (inv_smul_smul₀); aeval_C_self made public in Mobius; std axioms.

### [CLEANUP-16] `/cleanup` of `Algebraic.lean` (final for the file)

- **Status**: done   (finished 2026-10-06T21:13) · **File**: `Algebraic.lean` · **Depends on**: [T041] · **Type**: cleanup

Run `/cleanup` on `PhD/TauCeti/Code/OverconvergentForms/Weight/Algebraic.lean` (final for the file). Style audit + golf to mathlib standards; add `omit … in` where the skeleton's 'automatically included section variable(s) unused' warnings point; check docstrings cite the roadmap clause and the source; no statement changes without a B2 entry in `b2_log.jsonl`.

#### Progress

- 2026-10-06T21:13: Algebraic.lean final: build clean with no warnings, runLinter passes, no line over 100 chars, unused simp argument dropped.

### [T042] `aeval`, `symAct_one`, `symAct_mul`

- **Status**: done   (finished 2026-10-06T21:26) · **File**: `Classical.lean` · **Depends on**: [T041] · **Type**: proof · **Leaves**: L7.1, L7.2

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- Substituting weighted-homogeneous polynomials of the right degrees into a weighted-homogeneous
polynomial gives a weighted-homogeneous polynomial. -/
theorem IsWeightedHomogeneous.aeval {w : σ → M} {w' : τ → M} {f : σ → MvPolynomial τ R}
    (hf : ∀ s, IsWeightedHomogeneous w' (f s) (w s)) {φ : MvPolynomial σ R} {m : M}
    (hφ : IsWeightedHomogeneous w φ m) : IsWeightedHomogeneous w' (aeval f φ) m := by
  sorry

theorem symAct_one : symAct (1 : ι → Matrix (Fin 2) (Fin 2) K) = AlgHom.id K _ := by
  sorry

/-- `(P ∣ δ) ∣ γ = P ∣ (δγ)`: a right action. Source: roadmap §1.3.2. -/
theorem symAct_mul (γ δ : ι → Matrix (Fin 2) (Fin 2) K) :
    symAct (δ * γ) = (symAct γ).comp (symAct δ) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L7.1** `MvPolynomial.IsWeightedHomogeneous.aeval` — needed for `symAct_mem_symPow`. Sketch:
  substrate; `MvPolynomial.induction_on'`/`Finsupp.induction` over monomials, `aeval_monomial` ✓,
  `isWeightedHomogeneous_C`, `IsWeightedHomogeneous.mul` (via `weightedHomogeneousSubmodule_mul` ✓),
  `.pow`, `Finsupp.prod`, `Finsupp.weight_apply`/`weight` as a sum, `IsWeightedHomogeneous.add`.
  Attacks: [2] `P = 0` ✓ (`isWeightedHomogeneous_zero`). [3] the hypothesis `hf : ∀ s,
  IsWeightedHomogeneous w' (f s) (w s)` is exactly what makes degrees add ✓. [5] Mathlib has no such
  lemma (grep'd) → genuinely new, general, in the `MvPolynomial` namespace ✓ mathlib-shaped.
  SURVIVED.

- **L7.2** `symWeight`, `SymPow`, `mem_symPow_iff` (`Iff.rfl`), `symVars`, `symAct`, `symAct_X`
  (discharged), `symAct_one`, `symAct_mul` — [RM] §1.3.2 "prove it is a right action of the monoid of
  nonzero-determinant matrices […], and that in the homogeneous model it is `P(X, Y) ↦ det^v P(aX + bY,
  cX + dY)`" (decision D10: the `n`-part is an action of ALL matrices). Sketch: substrate; `symAct_one`:
  `symVars 1 v = X v` (`Matrix.one_apply`, `Finset.sum_ite_eq`), `MvPolynomial.aeval_X_left` ✓;
  `symAct_mul`: `MvPolynomial.algHom_ext` ✓ on `X v`, `aeval_X`, `map_sum`, `map_mul`, `aeval_C`,
  `Finset.sum_comm`, `Finset.mul_sum`, `Matrix.mul_apply` ✓. Attacks: [1] order: `symAct (δ * γ) =
  symAct γ ∘ symAct δ`: `symAct γ (symAct δ (X v)) = symAct γ (∑_k δ_{jk} X_{(i,k)}) = ∑_k δ_{jk} ∑_l γ_{kl}
  X_{(i,l)} = ∑_l (δγ)_{jl} X_{(i,l)}` ✓ `= symAct (δγ) (X v)` with `(δγ)_{jl} = ∑_k δ_{jk} γ_{kl}` ✓. [3] no
  `det ≠ 0` ✓ (the roadmap's monoid "of nonzero-determinant matrices" is a submonoid of this). [4]
  [Buz07, §9] "`∏ (c_i Z_i + d_i)^{n_i} … ((a_i Z_i + b_i)/(c_i Z_i + d_i))^{m_i}`" dehomogenises to
  `(aX + bY, cX + dY)` ✓ (row `0` of `γ_i` on `X_i`, row `1` on `Y_i`). SURVIVED.

#### Mathlib lemmas needed

`MvPolynomial.induction_on`, `MvPolynomial.aeval_monomial`, `MvPolynomial.isWeightedHomogeneous_C`, `MvPolynomial.weightedHomogeneousSubmodule_mul`, `MvPolynomial.algHom_ext`, `MvPolynomial.aeval_X`, `MvPolynomial.aeval_X_left`, `Finset.sum_comm`, `Finset.mul_sum`, `Matrix.mul_apply`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.3.2–§1.3.3; [Buz07, §9, p. 68; §11, p. 73]; Mathlib `RingTheory/MvPolynomial/WeightedHomogeneous.lean`; [SRC] `QMF/Weight/06_Algebraic.lean` (`polyEmbed`, `polyEmbed_slash`, `homogenise`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D10** `Sym^n` is the homogeneous model `weightedHomogeneousSubmodule`; every multi-matrix acts by `aeval`; `polySubmodule` is its dehomogenised image.

#### Progress

- 2026-10-06T21:26: IsWeightedHomogeneous.aeval via IsWeightedHomogeneous.induction_on (monomial case: C r · ∏ (f s)^(d s), degree = weight); symAct_one (Finset.sum_eq_single), symAct_mul (algHom_ext + Matrix.mul_apply + ring); std axioms.

### [T043] `isWeightedHomogeneous_symVars`, `symPowHom`

- **Status**: done   (finished 2026-10-06T21:26) · **File**: `Classical.lean` · **Depends on**: [T042] · **Type**: proof · **Leaves**: L7.3

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
theorem isWeightedHomogeneous_symVars (γ : ι → Matrix (Fin 2) (Fin 2) K) (v : ι × Fin 2) :
    IsWeightedHomogeneous (symWeight ι) (symVars γ v) (symWeight ι v) := by
  sorry

/-- The right action of the multi-matrices on `L_n`, as a homomorphism from the opposite monoid. -/
noncomputable def symPowHom : (ι → Matrix (Fin 2) (Fin 2) K)ᵐᵒᵖ →* Module.End K (SymPow K ι n) where
  toFun γ := symActₗ n γ.unop
  map_one' := by sorry
  map_mul' := by sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L7.3** `isWeightedHomogeneous_symVars`, `symAct_mem_symPow` (discharged by L7.1), `symActₗ`
  (discharged), `symPowHom` (fields), `symPowAction` (discharged) — the action on `L_n`. Sketch:
  `isWeightedHomogeneous_X` ✓, `isWeightedHomogeneous_C_mul`-type, `IsWeightedHomogeneous.sum`
  *(ticket; or `weightedHomogeneousSubmodule` `sum_mem`)*, `symWeight (i,k) = symWeight (i,j)`
  (both `Pi.single i 1`); `symPowHom`: `LinearMap.ext`, `Subtype.ext`, L7.2. Attacks: [1] orientation
  as in L4.4 ✓. SURVIVED.

#### Mathlib lemmas needed

`MvPolynomial.isWeightedHomogeneous_X`, `MvPolynomial.weightedHomogeneousSubmodule`, `Submodule.sum_mem`, `LinearMap.ext`, `Subtype.ext`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.3.2–§1.3.3; [Buz07, §9, p. 68; §11, p. 73]; Mathlib `RingTheory/MvPolynomial/WeightedHomogeneous.lean`; [SRC] `QMF/Weight/06_Algebraic.lean` (`polyEmbed`, `polyEmbed_slash`, `homogenise`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D10** `Sym^n` is the homogeneous model `weightedHomogeneousSubmodule`; every multi-matrix acts by `aeval`; `polySubmodule` is its dehomogenised image; **D12** right actions are `DistribMulAction Sᵐᵒᵖ A` built by `DistribMulAction.compHom`, as definitions.

#### Progress

- 2026-10-06T21:26: isWeightedHomogeneous_symVars (IsWeightedHomogeneous.sum of C_mul X), symPowHom (LinearMap.ext + Subtype.ext + symAct_one/mul); std axioms.

### [T044] `finrank_symPow`

- **Status**: done   (finished 2026-10-06T21:26) · **File**: `Classical.lean` · **Depends on**: [T043] · **Type**: milestone · **Leaves**: L7.4 · **Milestone**: M4 (part 1): `dim L_n = ∏ (n_i + 1)`

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- **The dimension of `L_n`**: `∏_i (n_i + 1)`. Source: roadmap §1.3.2 ("free of rank
`∏ (n_i + 1)`"); [Buz07, §9, p. 68]. -/
theorem finrank_symPow : Module.finrank K (SymPow K ι n) = ∏ i, (n i + 1) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L7.4** `finrank_symPow` — [RM] §1.3.2 "free of rank `∏ (n_i + 1)`". Sketch: substrate,
  *dimension*. Discharge: `weightedHomogeneousSubmodule_eq_finsupp_supported` ✓,
  `Finsupp.supportedEquivFinsupp` ✓, `LinearEquiv.finrank_eq` ✓, `Module.finrank_finsupp`-type
  (`finrank (α →₀ K) = card α`: `Module.finrank_finsupp_self` ✓), `Fintype.card_congr`,
  `Fintype.card_pi` ✓, `Fintype.card_fin` ✓, an explicit `Equiv` `{d // weight d = n} ≃ Π i, Fin (n i + 1)`
  (`Finsupp.weight` of `symWeight` is `fun i => d (i,0) + d (i,1)`: `Finsupp.weight_apply`,
  `Finsupp.sum`, `Pi.single_apply`). Attacks: [2] `n = 0`: constants, rank `1` ✓. [1] is the set
  `{d | weight d = n}` finite? Yes (`d ≤ n` coordinatewise) — needed for the `Fintype` instance:
  provide via the `Equiv` ✓. SURVIVED. **Milestone M4 (part).**

#### Mathlib lemmas needed

`MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported`, `Finsupp.supportedEquivFinsupp`, `LinearEquiv.finrank_eq`, `Module.finrank_finsupp_self`, `Fintype.card_congr`, `Fintype.card_pi`, `Fintype.card_fin`, `Finsupp.weight_apply`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.3.2–§1.3.3; [Buz07, §9, p. 68; §11, p. 73]; Mathlib `RingTheory/MvPolynomial/WeightedHomogeneous.lean`; [SRC] `QMF/Weight/06_Algebraic.lean` (`polyEmbed`, `polyEmbed_slash`, `homogenise`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D10** `Sym^n` is the homogeneous model `weightedHomogeneousSubmodule`; every multi-matrix acts by `aeval`; `polySubmodule` is its dehomogenised image.

#### Progress

- 2026-10-06T21:26: M4 part 1 DONE: finrank_symPow via weightedHomogeneousSubmodule_eq_finsupp_supported + AddMonoidAlgebra.supportedEquivFinsupp + finrank_finsupp_self + new weight_symWeight_apply and symPowSupportEquiv ({d | weight d = n} ≃ Π i, Fin (n i + 1)); std axioms.

### [CLEANUP-17] `/cleanup` of `Classical.lean` (cadence: three proof tickets)

- **Status**: done   (finished 2026-10-06T21:26) · **File**: `Classical.lean` · **Depends on**: [T044] · **Type**: cleanup

Run `/cleanup` on `PhD/TauCeti/Code/OverconvergentForms/Weight/Classical.lean` (cadence: three proof tickets). Style audit + golf to mathlib standards; add `omit … in` where the skeleton's 'automatically included section variable(s) unused' warnings point; check docstrings cite the roadmap clause and the source; no statement changes without a B2 entry in `b2_log.jsonl`.

#### Progress

- 2026-10-06T21:26: Inline: omit annotations for the polynomial-only lemmas (no IsUltrametricDist/CompleteSpace/Fintype needed), unused simp args dropped.

### [T045] `classicalHom`

- **Status**: done   (finished 2026-10-06T21:26) · **File**: `Classical.lean` · **Depends on**: [CLEANUP-17] · **Type**: proof · **Leaves**: L7.5

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- **Buzzard's `L_{n,v}`**: `GL₂(L)` acts on `L_n` through the embeddings by
`P ↦ v(det g) · P(aX + bY, cX + dY)`. Source: roadmap §1.3.2; [Buz07, §9, p. 68] ("the same definition
gives an action of `GL₂(F_p)` on `L_{n,v}`"). -/
noncomputable def classicalHom (v : Lˣ →* Kˣ) : (GL (Fin 2) L)ᵐᵒᵖ →* Module.End K (SymPow K ι n) where
  toFun g := (v (Matrix.GeneralLinearGroup.det g.unop) : K) • symActₗ n (e.toMulti g.unop)
  map_one' := by sorry
  map_mul' := by sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L7.5** `classicalHom` (fields), `classicalAction` (discharged), `classicalAction_op_smul`
  (`rfl`) — [RM] §1.3.2 the `(n,v)`-module of `GL₂`; [Buz07, §9] "an action of `GL₂(F_p)` on `L_{n,v}`".
  Sketch: `Matrix.GeneralLinearGroup.det` is a monoid hom (`map_mul`, `map_one` ✓
  `GeneralLinearGroup.det_mul`-type), `map_mul` of `v`, L7.3 `symPowHom`'s laws with `e.toMultiHom`
  (L5.5), `smul_smul`, `LinearMap.smul_comp`/`comp_smul`, `mul_comm`. Attacks: [3] `v` norm-one is
  not needed here (no analysis) ✓ not assumed. [4] erratum E3: `v ∘ det` normalised, matching L6/L7.9
  ✓. SURVIVED.

#### Mathlib lemmas needed

`Matrix.GeneralLinearGroup.det`, `map_mul`, `smul_smul`, `LinearMap.smul_comp`, `LinearMap.comp_smul`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.3.2–§1.3.3; [Buz07, §9, p. 68; §11, p. 73]; Mathlib `RingTheory/MvPolynomial/WeightedHomogeneous.lean`; [SRC] `QMF/Weight/06_Algebraic.lean` (`polyEmbed`, `polyEmbed_slash`, `homogenise`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D4** `v : Lˣ →* Kˣ` of norm one; Buzzard's `v(ϖ) = 1` is the construction `extendUnits`; **D12** right actions are `DistribMulAction Sᵐᵒᵖ A` built by `DistribMulAction.compHom`, as definitions.

#### Progress

- 2026-10-06T21:26: classicalHom: map_one'/map_mul' by LinearMap.ext + Subtype.ext + simp (toMultiHom.map_one/map_mul, symAct_one/mul, smul_smul) with a closing rfl for the restrict coercion; std axioms.

### [T046] `toTate_monomial`, `map_symPow_toTate`, `toTate_injOn` and 3 more

- **Status**: done   (finished 2026-10-06T21:26) · **File**: `Classical.lean` · **Depends on**: [T045] · **Type**: proof · **Leaves**: L7.6, L7.7

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- The dehomogenisation of a monomial. -/
theorem toTate_monomial (d : ι × Fin 2 →₀ ℕ) (a : K) :
    toTate K ι (MvPolynomial.monomial d a) =
      monomial 1 (Finsupp.equivFunOnFinite.symm fun i => d (i, 0)) a := by
  sorry

/-- The image of `L_n` under dehomogenisation is `polySubmodule n`. -/
theorem map_symPow_toTate : (SymPow K ι n).map (toTate K ι).toLinearMap = polySubmodule K ι n := by
  sorry

/-- Dehomogenisation is injective on `L_n`. -/
theorem toTate_injOn : Set.InjOn (toTate K ι) (SymPow K ι n) := by
  sorry

/-- **`L_n ≃ polySubmodule n`**. Source: roadmap §1.3.2–§1.3.3. -/
noncomputable def toTateEquiv : SymPow K ι n ≃ₗ[K] polySubmodule K ι n :=
  sorry

theorem coe_toTateEquiv_apply (P : SymPow K ι n) :
    (toTateEquiv n P : Restricted K (1 : ι → ℝ)) = toTate K ι P := by
  sorry

theorem finrank_polySubmodule : Module.finrank K (polySubmodule K ι n) = ∏ i, (n i + 1) := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L7.6** `toTate` (def), `polySubmodule` (def), `toTate_monomial`, `map_symPow_toTate`,
  `toTate_injOn` — [RM] §1.3.2–3 "realised as the polynomials in `A` of degree at most `n_i` in each
  `z_i`"; "exactly the subspace spanned by the monomials `z^m`, `m ≤ n`". Sketch: substrate,
  *dehomogenisation*. Discharge: `MvPolynomial.aeval_monomial` ✓, `Finsupp.prod`, `Finset.prod_ite`,
  [RAG] `monomial` as `C a * ∏ X^k` *(ticket: `MvPowerSeries.monomial_eq`-type on `.1`)*,
  `Submodule.map_span`, `Set.image`, the monomial basis of `SymPow n` (L7.4's `Equiv`),
  `Finsupp.equivFunOnFinite` ✓, linear independence of distinct monomials in the Tate algebra
  (coefficient extraction, [RAG] `val_monomial` ✓). Attacks: [1] is `toTate` injective on all of
  `MvPolynomial`? NO (`X_{(i,1)} − 1 ↦ 0`) — only on `SymPow n` ✓ stated as `InjOn`. [2] `n = 0`:
  `SymPow 0 = K`, `polySubmodule 0 = K·1` ✓. SURVIVED.

- **L7.7** `toTateEquiv` (def), `coe_toTateEquiv_apply`, `finrank_polySubmodule` — [RM] §1.3.3.
  Sketch: `LinearEquiv.ofInjective` ✓ + `LinearEquiv.ofEq` with `map_symPow_toTate`, or
  `Submodule.equivMapOfInjective` ✓; `finrank` transported by L7.4. Attacks: [5] `LinearEquiv.ofInjective`
  needs `Function.Injective` of the restricted map: from `toTate_injOn` via `Set.injOn_iff_injective`
  ✓. SURVIVED.

#### Mathlib lemmas needed

`MvPolynomial.aeval_monomial`, `Finset.prod_ite`, `Submodule.map_span`, `Finsupp.equivFunOnFinite`, `MvPowerSeries.Restricted.val_monomial`, `LinearEquiv.ofInjective`, `Submodule.equivMapOfInjective`, `Set.injOn_iff_injective`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.3.2–§1.3.3; [Buz07, §9, p. 68; §11, p. 73]; Mathlib `RingTheory/MvPolynomial/WeightedHomogeneous.lean`; [SRC] `QMF/Weight/06_Algebraic.lean` (`polyEmbed`, `polyEmbed_slash`, `homogenise`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D10** `Sym^n` is the homogeneous model `weightedHomogeneousSubmodule`; every multi-matrix acts by `aeval`; `polySubmodule` is its dehomogenised image.

#### Progress

- 2026-10-06T21:26: toTate_monomial (aeval_monomial, monomial_eq_C_mul_prod, Fintype.prod_prod_type), map_symPow_toTate (supported_eq_span_single + map_span, symPowSupportEquiv for the reverse inclusion), toTate_injOn (coefficient at (d(i,0))_i via Finset.sum_eq_single and the weight), toTateEquiv (LinearEquiv.ofInjective on domRestrict + ofEq), coe_toTateEquiv_apply (rfl), finrank_polySubmodule; std axioms.

### [T047] `aeval_mul_of_mem_symPow`

- **Status**: done   (finished 2026-10-06T21:26) · **File**: `Classical.lean` · **Depends on**: [T046] · **Type**: proof · **Leaves**: L7.8

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- **The scaling identity of multi-homogeneous polynomials**: for `P ∈ L_n`,
`P(λ_i X_i, λ_i Y_i) = ∏ λ_i^{n_i} P(X, Y)`, in any commutative `K`-algebra. -/
theorem aeval_mul_of_mem_symPow {B : Type*} [CommRing B] [Algebra K B] {P : MvPolynomial (ι × Fin 2) K}
    (hP : P ∈ SymPow K ι n) (lam : ι → B) (g : ι × Fin 2 → B) :
    MvPolynomial.aeval (fun v => lam v.1 * g v) P = (∏ i, lam i ^ n i) * MvPolynomial.aeval g P := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L7.8** `aeval_mul_of_mem_symPow` — the scaling identity (substrate). Sketch: induction over the
  monomials of `P` (`Finsupp.sum`/`MvPolynomial.as_sum`), `aeval_monomial` ✓, `mul_pow`,
  `Finsupp.prod_mul`, and for `weight d = n`: `∏_v λ_{v.1}^{d_v} = ∏_i λ_i^{d(i,0) + d(i,1)} = ∏_i λ_i^{n_i}`
  (`Finsupp.prod_fiberwise`-type / `Fintype.prod_prod_type` ✓ `∏_{(i,j)} = ∏_i ∏_j`, `pow_add`). Attacks:
  [2] `P` a constant: `λ^0 = 1` ✓. [3] `B` commutative is needed for `mul_pow` ✓. SURVIVED.

#### Mathlib lemmas needed

`MvPolynomial.as_sum`, `MvPolynomial.aeval_monomial`, `mul_pow`, `Fintype.prod_prod_type`, `pow_add`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.3.2–§1.3.3; [Buz07, §9, p. 68; §11, p. 73]; Mathlib `RingTheory/MvPolynomial/WeightedHomogeneous.lean`; [SRC] `QMF/Weight/06_Algebraic.lean` (`polyEmbed`, `polyEmbed_slash`, `homogenise`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D10** `Sym^n` is the homogeneous model `weightedHomogeneousSubmodule`; every multi-matrix acts by `aeval`; `polySubmodule` is its dehomogenised image.

#### Progress

- 2026-10-06T21:26: aeval_mul_of_mem_symPow by IsWeightedHomogeneous.induction_on (monomial: mul_pow, prod_mul_distrib, Fintype.prod_prod_type + weight_symWeight_apply); std axioms.

### [CLEANUP-18] `/cleanup` of `Classical.lean` (cadence: three proof tickets)

- **Status**: done   (finished 2026-10-06T21:26) · **File**: `Classical.lean` · **Depends on**: [T047] · **Type**: cleanup

Run `/cleanup` on `PhD/TauCeti/Code/OverconvergentForms/Weight/Classical.lean` (cadence: three proof tickets). Style audit + golf to mathlib standards; add `omit … in` where the skeleton's 'automatically included section variable(s) unused' warnings point; check docstrings cite the roadmap clause and the source; no statement changes without a B2 entry in `b2_log.jsonl`.

#### Progress

- 2026-10-06T21:26: Inline: long signatures and the Buzzard quotation reflowed to 100 chars; deprecated Set.mem_setOf_eq replaced.

### [CLEANUP-ALL-3] `/cleanup-all` (before milestone T048 (M4))

- **Status**: done   (finished 2026-10-06T21:26) · **File**: `(project so far)` · **Depends on**: [CLEANUP-14], [CLEANUP-16], [CLEANUP-18] · **Type**: cleanup

Run `/cleanup-all` on `PhD/TauCeti/Code/OverconvergentForms/Weight/` (before milestone T048 (M4)). Inline, as the main agent (memory note `cleanup-inline-no-subagents`). Gates: every touched module builds with no warning; `runLinter` clean; no `sorry`; the four `omit`-able section-variable warnings of the skeleton are gone.

#### Progress

- 2026-10-06T21:26: Weight/ so far (Level, Dictionary, Mobius, Identity, Action, Expansion, Algebraic, Classical): each builds with no warning, runLinter passes, no sorry, no line over 100 chars.

### [T048] `toTate_symAct`, `toTate_classicalAction`, `polySubmodule_stable`

- **Status**: done   (finished 2026-10-06T21:26) · **File**: `Classical.lean` · **Depends on**: [CLEANUP-ALL-3] · **Type**: milestone · **Leaves**: L7.9 · **Milestone**: M4 (part 2): the bridge `L_n ↪ A` is equivariant

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- **The bridge**: for `γ` in the level, dehomogenisation intertwines the action on `L_n` with the
weight action of the algebraic weight `algWeight (n, 1)`:
`∏ (c_i z_i + d_i)^{n_i} P(w_γ(z), 1) = P(a z + b, c z + d)`. Source: roadmap §1.3.3; [Buz07, §11,
p. 73] ("an `M_1`-equivariant inclusion"). -/
theorem toTate_symAct [CharZero K] (hb : LevelBounds S ρ) (γ : S) {P : MvPolynomial (ι × Fin 2) K}
    (hP : P ∈ SymPow K ι n) :
    toTate K ι (symAct (e.toMulti γ) P) =
      (e.algWeight hb (fun i => (n i : ℤ)) 1 (by simp)).kappaSlash γ (toTate K ι P) := by
  sorry

/-- The bridge for `L_{n,v}`: with the determinant twist on both sides. -/
theorem toTate_classicalAction [CharZero K] (hb : LevelBounds S ρ) (v : Lˣ →* Kˣ)
    (hv : ∀ x, ‖(v x : K)‖ = 1) (γ : S) (P : SymPow K ι n) :
    letI := classicalAction n e v
    toTate K ι (MulOpposite.op (hb.toGL γ) • P : SymPow K ι n) =
      (e.algWeight hb (fun i => (n i : ℤ)) v hv).kappaSlash γ (toTate K ι P) := by
  sorry

/-- `L_n ⊆ A` is stable under the weight action of the algebraic weights. Source: roadmap §1.3.3
("hence `L_n` is a `Σ`-stable finite-dimensional subspace of `A`"). -/
theorem polySubmodule_stable [CharZero K] (hb : LevelBounds S ρ) (v : Lˣ →* Kˣ)
    (hv : ∀ x, ‖(v x : K)‖ = 1) (γ : S) {f : Restricted K (1 : ι → ℝ)}
    (hf : f ∈ polySubmodule K ι n) :
    (e.algWeight hb (fun i => (n i : ℤ)) v hv).kappaSlash γ f ∈ polySubmodule K ι n := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L7.9** `toTate_symAct`, `toTate_classicalAction`, `polySubmodule_stable` — [RM] §1.3.3 "For
  `γ ∈ Σ`, the action of clause 2 on `L_n ⊆ A` agrees with the weight action of `algWeight (n, v)`;
  hence `L_n` is a `Σ`-stable finite-dimensional subspace of `A`". Sketch: substrate, *the bridge*.
  Discharge: `MvPolynomial.aeval_comp`-type (`toTate (aeval f P) = aeval (toTate ∘ f) P`:
  `MvPolynomial.aeval_aeval`? — use `MvPolynomial.comp_aeval` ✓ or `algHom_ext`), `toTate` on
  `symVars` (`map_sum`, `aeval_X`, `Fin.sum_univ_two`, `if_pos`/`if_neg`), L6.3 `algCol_natCast`, L4.3
  `kappaSlash_apply`/`mobiusSubst_apply`, L7.8 with `lam i := lin i`, `g (i,0) := mobius i`, `g (i,1) :=
  1`, `lin_mul_linInv` (L2.4), `(1 : Lˣ →* Kˣ)`'s `detChar = 1` (`MonoidHom.one_apply`, `one_smul`);
  `toTate_classicalAction` from `toTate_symAct` and `classicalAction_op_smul` with `coe_toGL` (`v (det
  (toGL γ)) = detChar γ`); `polySubmodule_stable` from `map_symPow_toTate` (write `f = toTate P`) and
  `toTate_classicalAction` (or `_symAct` + `twist`). Attacks: [1] composition: could `toTate_symAct`
  hold on monomials but fail on sums? Both sides are `K`-linear in `P` ✓. [2] `n = 0`: `symAct γ a = a`,
  `kappaSlash (algWeight 0) γ a = v(det)·a` with `v = 1` ✓. [3] `hb`/`γ ∈ S` is needed (the right side
  exists only on the level) ✓; `[CharZero K]` enters through `kappaSlash` ✓. [4] [Buz07, §11]
  "`M_1`-equivariant inclusion" ✓ with the normalisation of E3. SURVIVED. **Milestone M4.**

⚠ Long proof; the scaling identity (T047) does the work.

#### Mathlib lemmas needed

`MvPolynomial.comp_aeval`, `MvPolynomial.algHom_ext`, `Fin.sum_univ_two`, `MonoidHom.one_apply`, `one_smul`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] §1.3.2–§1.3.3; [Buz07, §9, p. 68; §11, p. 73]; Mathlib `RingTheory/MvPolynomial/WeightedHomogeneous.lean`; [SRC] `QMF/Weight/06_Algebraic.lean` (`polyEmbed`, `polyEmbed_slash`, `homogenise`; proof ideas only).

#### Generality decision

Binding decisions of `plan.md`: **D1** the carrier is the Tate algebra `MvPowerSeries.Restricted K (1 : ι → ℝ)`; the action is the substitution operator, the kernel array is the theorem `kappaSlash_monomial`; **D10** `Sym^n` is the homogeneous model `weightedHomogeneousSubmodule`; every multi-matrix acts by `aeval`; `polySubmodule` is its dehomogenised image.

#### Progress

- 2026-10-06T21:26: M4 part 2 DONE: toTate_symAct (comp_aeval_apply on both sides; homogenised Möbius point g; scaling identity with λ = lin; autFactor of algWeight (n,1) = ∏ lin^n), toTate_classicalAction (det(toGL γ) = detUnits γ by Units.ext), polySubmodule_stable (Submodule.mem_map); std axioms.

### [CLEANUP-19] `/cleanup` of `Classical.lean` (final for the file)

- **Status**: done   (finished 2026-10-06T21:26) · **File**: `Classical.lean` · **Depends on**: [T048] · **Type**: cleanup

Run `/cleanup` on `PhD/TauCeti/Code/OverconvergentForms/Weight/Classical.lean` (final for the file). Style audit + golf to mathlib standards; add `omit … in` where the skeleton's 'automatically included section variable(s) unused' warnings point; check docstrings cite the roadmap clause and the source; no statement changes without a B2 entry in `b2_log.jsonl`.

#### Progress

- 2026-10-06T21:26: Classical.lean final: build clean with no warnings, runLinter passes, no line over 100 chars.

### [T049] `norm_natCast_prime_lt_one` and 1 more

- **Status**: done   (finished 2026-10-06T21:29) · **File**: `Examples.lean` · **Depends on**: [T048], [T013], [T006] · **Type**: proof · **Leaves**: L8.1

#### Statement

As in the skeleton (fixed). Declarations of this ticket, in file order (fill every `sorry`;
definitions with `sorry`-fields count):

```lean
/-- `‖p‖ < 1` in `ℚ_p`: the level `ρ = ‖p‖`. -/
theorem norm_natCast_prime_lt_one (p : ℕ) [Fact p.Prime] : ‖(p : ℚ_[p])‖ < 1 := by
  sorry

/-- The algebraic weight `u ↦ u^k` has the expansion `col(c, d) = (d + c z)^k`. -/
example (k : ℕ) (c d : ℚ_[p]) :
    (Embeddings.self ℚ_[p]).algCol (fun _ : Unit => (k : ℤ)) c d =
      (C 1 d + C 1 c * X ℚ_[p] 1 ()) ^ k := by
  sorry

/-- The matrix of `diag(1, d)` on the weight `u ↦ u^k`: `z^r ↦ d^{k−r} z^r` for `r ≤ k`. -/
example (k r : ℕ) (hr : r ≤ k) {d : ℚ_[p]} (hd : ‖d‖ = 1) :
    ((Embeddings.self ℚ_[p]).algWeight (levelBounds_sigmaNorm (norm_nonneg (p : ℚ_[p])) (norm_natCast_prime_lt_one p))
        (fun _ : Unit => (k : ℤ)) 1 (by simp)).kappaSlash
      ⟨!![1, 0; 0, d], by sorry⟩ (monomial 1 (Finsupp.single () r) 1) =
      d ^ (k - r) • monomial 1 (Finsupp.single () r) 1 := by
  sorry

/-- The matrix of `((1 0), (c 1))` on the weight `u ↦ u^k`: `z^r ↦ (1 + c z)^{k−r} z^r` for `r ≤ k`. -/
example (k r : ℕ) (hr : r ≤ k) {c : ℚ_[p]} (hc : ‖c‖ ≤ ‖(p : ℚ_[p])‖) :
    ((Embeddings.self ℚ_[p]).algWeight (levelBounds_sigmaNorm (norm_nonneg (p : ℚ_[p])) (norm_natCast_prime_lt_one p))
        (fun _ : Unit => (k : ℤ)) 1 (by simp)).kappaSlash
      ⟨!![1, 0; c, 1], by sorry⟩ (monomial 1 (Finsupp.single () r) 1) =
      (1 + C 1 c * X ℚ_[p] 1 ()) ^ (k - r) * X ℚ_[p] 1 () ^ r := by
  sorry

/-- A nebentypus `ψ` of conductor `p` loaded into `u^k ψ(u)` at level `p ∣ c`: the automorphy
factor is `ψ(d̄) (d + c z)^k`. -/
example (k : ℕ)
    (ψ : (Subring.unitClosedBall ℚ_[p] ⧸ NormedRing.closedBallIdeal ℚ_[p]
      ⟨‖(p : ℚ_[p])‖, norm_nonneg _⟩)ˣ →* ℚ_[p]ˣ) (hψ : ∀ x, ‖(ψ x : ℚ_[p])‖ = 1)
    (γ : SigmaNorm ℚ_[p] ‖(p : ℚ_[p])‖ (norm_nonneg (p : ℚ_[p])) (norm_natCast_prime_lt_one p)) :
    ((Embeddings.self ℚ_[p]).classicalShape
        (levelBounds_sigmaNorm (norm_nonneg (p : ℚ_[p])) (norm_natCast_prime_lt_one p)) (fun _ : Unit => (k : ℤ)) 1
        (by simp) ψ hψ).autFactor γ =
      (ψ ((levelBounds_sigmaNorm (norm_nonneg (p : ℚ_[p])) (norm_natCast_prime_lt_one p)).lowerRightResidue γ) :
          ℚ_[p]) •
        (C 1 ((γ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1) +
          C 1 ((γ : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0) * X ℚ_[p] 1 ()) ^ k := by
  sorry

/-- The scalar `−1` acts on the weight `u ↦ u^k` by `(−1)^k`. -/
example (k : ℕ) (f : Restricted ℚ_[p] (1 : Unit → ℝ)) :
    ((Embeddings.self ℚ_[p]).algWeight (levelBounds_sigmaNorm (norm_nonneg (p : ℚ_[p])) (norm_natCast_prime_lt_one p))
        (fun _ : Unit => (k : ℤ)) 1 (by simp)).kappaSlash
      ⟨((-1 : (Subring.unitClosedBall ℚ_[p])ˣ) : Subring.unitClosedBall ℚ_[p]) • 1,
        smul_one_mem_sigmaNorm _ _ _⟩ f = (-1 : ℚ_[p]) ^ k • f := by
  sorry

/-- The adjugate of `((3 0), (9t 1))` is the left-handed `((1 0), (−9t 3))`. -/
example (t : ℚ_[3]) : (!![3, 0; 9 * t, 1] : Matrix (Fin 2) (Fin 2) ℚ_[3]).adjugate =
    !![1, 0; -(9 * t), 3] := by
  sorry
```

#### Proof sketch

Substrate: `decomposition.md`, the "Plain-English proof substrate" of the section this file belongs to.
Leaf sketches, with their attack logs, verbatim from the decomposition:

- **L8.1** `norm_natCast_prime_lt_one` and the six `example`s — [RM] Layer 1 Examples (minus `u^s`).
  Sketch: `padicNormE.norm_p_lt_one` ✓ *(name to confirm: `padicNormE.norm_p_lt_one`)*; (1)
  `algCol_natCast` with `ι = Unit`, `Fintype.prod_unique` ✓, `lin (e.toMulti !![1,0;c,d]) () = C d + C c X`
  (`RingHom.id`); (2) L6.4 at `γ = diag(1, d)`: `lin = C d`, `num = X`, so `d^{k−r} X^r`
  (`Finsupp.prod_single_index`); the membership `⟨!![1,0;0,d], _⟩` needs `‖d‖ = 1`, `det = d ≠ 0`; (3)
  L6.4 at `((1 0), (c 1))`: `lin = 1 + C c X`, `num = X`; (4) L6.7 `autFactor_classicalShape` +
  `algCol_natCast` + `(1 : MonoidHom)`; (5) L6.8 `kappaSlash_smul_one` with `n(−1) = (−1)^k`
  (`coe_algChar`, `zpow_natCast`) and `v = 1`; (6) `Matrix.adjugate_fin_two_of` ✓ + `ring_nf`.
  Attacks: [2] `k = 0` in (2): `d^0 X^r`… with `r ≤ k = 0` so `r = 0` ✓. [3] (3) needs
  `‖c‖ ≤ ‖p‖ = ρ` for membership ✓ hypothesis present. [4] matches the roadmap's list ✓ except the
  FLOOR-PENDING `u^s`. SURVIVED.

#### Mathlib lemmas needed

`padicNormE.norm_p_lt_one`, `Fintype.prod_unique`, `Finsupp.prod_single_index`, `Matrix.adjugate_fin_two_of`, `zpow_natCast`

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] Layer 1, Examples; everything above.

#### Generality decision

Binding decisions of `plan.md`: **D1** the carrier is the Tate algebra `MvPowerSeries.Restricted K (1 : ι → ℝ)`; the action is the substitution operator, the kernel array is the theorem `kappaSlash_monomial`.

#### Progress

- 2026-10-06T21:29: norm_natCast_prime_lt_one (Padic.norm_p_lt_one); the six examples: algCol at Unit (algCol_natCast + Fintype.prod_unique), diag(1,d) and ((1 0),(c 1)) via kappaSlash_algWeight_monomial (membership proofs filled in place), nebentypus via autFactor_classicalShape, scalar −1 via kappaSlash_smul_one + coe_algChar, adjugate via Matrix.adjugate_fin_two_of; build clean, lint clean.

### [CLEANUP-20] `/cleanup` of `Examples.lean` (final for the file)

- **Status**: done   (finished 2026-10-06T21:29) · **File**: `Examples.lean` · **Depends on**: [T049] · **Type**: cleanup

Run `/cleanup` on `PhD/TauCeti/Code/OverconvergentForms/Weight/Examples.lean` (final for the file). Style audit + golf to mathlib standards; add `omit … in` where the skeleton's 'automatically included section variable(s) unused' warnings point; check docstrings cite the roadmap clause and the source; no statement changes without a B2 entry in `b2_log.jsonl`.

#### Progress

- 2026-10-06T21:29: Examples.lean final: no warnings, runLinter passes, long statement lines broken without changing tokens.

### [CLEANUP-ALL-4] `/cleanup-all` (before milestone T050 (M5))

- **Status**: done   (finished 2026-10-06T21:31) · **File**: `(whole layer)` · **Depends on**: [CLEANUP-19], [CLEANUP-20] · **Type**: cleanup

Run `/cleanup-all` on `PhD/TauCeti/Code/OverconvergentForms/Weight/` (before milestone T050 (M5)). Inline, as the main agent (memory note `cleanup-inline-no-subagents`). Gates: every touched module builds with no warning; `runLinter` clean; no `sorry`; the four `omit`-able section-variable warnings of the skeleton are gone.

#### Progress

- 2026-10-06T21:31: All nine Weight modules: build with no warning, runLinter passes on each, no sorry, no line over 100 chars.

### [T050] Import `Weight/Examples` from the chain root `PhD/TauCeti.lean`

- **Status**: done   (finished 2026-10-06T21:33) · **File**: `PhD/TauCeti.lean (chain root)` · **Depends on**: [CLEANUP-ALL-4] · **Type**: milestone · **Milestone**: M5 (part 2): the chain root imports `Weight/Examples`

#### Statement

Add `import PhD.TauCeti.Code.OverconvergentForms.Weight.Examples` to `PhD/TauCeti.lean` and run `lake build PhD.TauCeti`; `#print axioms` on `AnalyticWeight.autFactor_mul`, `Embeddings.eq_zero_of_forall_evalPoint_eq_zero`, `toTate_symAct`, `WeightData.pi` must show only `propext`, `Classical.choice`, `Quot.sound`.

#### Proof sketch

1. Add the import line to `PhD/TauCeti.lean` (alphabetical among the `OverconvergentForms` imports).
2. `lake build PhD.TauCeti` must succeed with no warning.
3. `#print axioms` on the four capstones listed above; only `propext`, `Classical.choice`, `Quot.sound`.
4. `lake exe runLinter` on every `Weight/*` module (see the memory note `runlinter-gate`).

#### Mathlib lemmas needed

(none beyond the leaves' discharge lines)

Names marked ✓ in the decomposition were checked by `grep`/elaboration during planning; the others
are *(ticket)* names to confirm with `grep -rn` on `.lake/packages/mathlib` (the `lean_*` MCP tools
may be absent — see the memory note `lean-project-workflow`).

#### Sources

- [RM] (the chain root gates the layer in CI); `tauceti-of-layer0` precedent.

#### Generality decision

Binding decisions of `plan.md`: **D8** namespace `AutomorphicForm`; Tate-algebra seams in `MvPowerSeries.Restricted` / `PowerSeries.Restricted` / `Matrix`.

#### Progress

- 2026-10-06T21:33: M5 part 2 DONE: chain root PhD/TauCeti.lean imports Weight.Examples; lake build PhD.TauCeti passes (3628 jobs, no warning); #print axioms from the chain root on autFactor_mul, eq_zero_of_forall_evalPoint_eq_zero, toTate_symAct, WeightData.pi (and kappaSlash_mul, finrank_symPow, continuous_n, kappaSlash_smul_one, extendUnits): propext, Classical.choice, Quot.sound only; runLinter passes on all nine Weight modules.

### [CLEANUP-FINAL] `/cleanup-all` (`/cleanup-all` on the whole layer; then `/pre-submit`)

- **Status**: done   (finished 2026-10-06T21:33) · **File**: `(whole layer)` · **Depends on**: [T050] · **Type**: cleanup

Run `/cleanup-all` on `PhD/TauCeti/Code/OverconvergentForms/Weight/` (`/cleanup-all` on the whole layer; then `/pre-submit`). Inline, as the main agent (memory note `cleanup-inline-no-subagents`). Gates: every touched module builds with no warning; `runLinter` clean; no `sorry`; the four `omit`-able section-variable warnings of the skeleton are gone.

#### Progress

- 2026-10-06T21:33: Whole layer: no sorry/admit/set_option/native_decide in Weight/, every file has the copyright header and a module docstring, no line over 100 chars, every module builds with no warning, runLinter clean on all nine; roadmap README gained a Layer 1 status note (FLOOR-PENDING §1.2.7 and u^s recorded).
