# Ticket board: Tau Ceti `PadicFunctionalAnalysis`, Layer 0

**Board**: `.mathlib-quality/tauceti-pfa-layer0/` (a *named* board: always pass this path to `/beastmode`;
the default board belongs to another project).
**Plan**: `plan.md` · **Decomposition (quotes, attacks, gate)**: `decomposition.md` · **References**: `references/*.txt`
**Roadmap**: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, Layer 0 (§0.1–§0.4) — cited as [RM].
**Code**: `PhD/TauCeti/Code/PadicFunctionalAnalysis/` — twelve files, every declaration already stated with
`sorry`. Planned 2026-09-18. Status: **COMPLETE 2026-09-29** — all 65 tickets done; the twelve files are sorry-free and in the chain root.

## Summary

| | Count |
|---|---|
| Proof / definition tickets | 45 (`T001`–`T045`) |
| Per-file cleanups | 17 (`CLEANUP-1`–`CLEANUP-17`) |
| Pre-milestone sweeps | 2 (`CLEANUP-ALL-1`, `CLEANUP-ALL-2`) |
| Final sweep | 1 (`CLEANUP-FINAL`) |
| **Total** | **65** |

- **Milestone M1** = `T035`: the unit ball of a Tate normed ring is a ring of definition
  (`NormedRing.PseudoUniformizer.isAdic_ideal` and its companions) — [RM] §0.4.5.
- **Milestone M2** = `T039`: the gauge norm of a Hausdorff Tate ring is a ring norm inducing the topology
  (`Subring.gaugeRingNorm`, `Subring.hasBasis_nhds_zero_gaugeNorm`) — [RM] §0.4.6.
- The layer closes with `T036`, the round trip `gaugeNorm_unitClosedBall` (the two bridges are mutually inverse up
  to [JN] Lemma 2.1.7).
- Skeleton: 212 declarations, 191 `sorry`s. Gate (verified 2026-09-18, 2 626 jobs, 0 errors):
  `lake build PhD.TauCeti.Code.PadicFunctionalAnalysis.Examples PhD.TauCeti.Code.PadicFunctionalAnalysis.NormComparison`.
- Tickets that can start immediately (no dependencies): `T001`, `T006`, `T012`, `T015`, `T018`, `T028`, `T037`.

## Worker protocol (binding)

1. **The statements are fixed.** Every ticket's Statement block is copied verbatim from the skeleton by a script.
   Prove the statement as written. If a statement is false or unprovable as stated, that is a **B2 stop** with a
   concrete counterexample or obstruction — never silently change a hypothesis. Private helper lemmas are allowed
   and expected where a sketch says so; they follow the same conventions.
2. **Chain separation.** Never `import PhD.Main.*` here (CI-gated), and never the reverse. `PhD/Main/` files cited as
   [SRC] are read-only references for proof ideas. Never delete `PhD/PR'd/` or legacy files.
3. **Build** with `lake build PhD.TauCeti.Code.PadicFunctionalAnalysis.<Module>` — never `lake build PhD`. There is no
   `timeout` binary on this machine: use the tool timeout and check exit codes. Another board builds in parallel on
   this machine; expect slow builds, and do not kill processes you did not start.
4. **Imports stay minimal per file** (never `import Mathlib` in a `Code/` file). When a proof needs an unimported
   module, add exactly that module.
5. **Done means**: the module builds with no `sorry` in the ticket's declarations, `#print axioms` on each shows only
   `propext`, `Classical.choice`, `Quot.sound`, and the ticket's Status line is updated here.
6. **Cleanup tickets are done inline by the main agent** (no Agent-dispatched cleanup workers), with
   `lake exe runLinter` on the module.
7. **Sentinel ownership.** `.mathlib-quality/beastmode_active` may belong to a parallel instance: `cat` it before
   acting, and delete it only if its `BOARD:` line names this board.
8. **Mathlib first.** Every Mathlib name in a "Mathlib lemmas needed" block was checked by elaboration against the
   pinned Mathlib (`scratch/names*.lean`, six files, about 300 names); `T0xx` there refers to an earlier ticket of this board. If
   Mathlib already has a ticket's statement, use it and record the name.
9. **Conventions** (plan §"Generality and design decisions"): Mathlib vocabulary (`IsUltrametricDist`,
   `IsBoundedSMul`, `NormMulClass`); weakest structure that carries the proof; `IsTate` is a Prop and
   `PseudoUniformizer` is data; two norms are two normed rings; the rescaled norm lives on `Rescaled ϖ M`; seams are
   declared in module docstrings; one conclusion per declaration; one-line `Source:` docstrings.
10. **Commit or push only when the user asks.**

## Roadmap errata (found while planning; see plan.md for the full table)

E1 Mathlib *does* have `IsUltrametricDist.norm_tsum_le` · E2 `R⁰⁰` is **not** maximal for multiplicative norms in
general (`ℚ_p⟨X⟩`); it lies in the Jacobson radical, and is maximal for normed fields · E3 the rescaled module is a
normed `R`-module only when `‖R‖ ⊆ ‖ϖ‖ ^ ℤ ∪ {0}` · E4 the `ℚ_p⟨X⟩` example needs §4.1 · E5 "a Tate normed ring is
nontrivial" needs `‖1‖ = 1` (equivalently `Nontrivial R`, T021) · E6 the `normAddVal` seam is external to this chain ·
E7 §0.4.5 is stated in Mathlib vocabulary · E8 the strict bound needs `0 < B` and no nullity hypothesis; the
supremum is attained on any nonempty index type. E1–E5 and E8 are corrected in the roadmap README (2026-09-18,
uncommitted); E6–E7 are board notes.

## Dependency order

The tickets below are listed in dependency order, group by group (so `T037`–`T039` precede `T034`–`T036`).

```text
G1  Sums            T001 → T002 → T003 → CLEANUP-1 → T004 → T005 → CLEANUP-2
G2  UnitBall        T006 → T007 → T008 → CLEANUP-3 → T009 (also needs T002) → T010 → T011 → CLEANUP-4
G3  PowerBounded    T012 → T013 → T014 → CLEANUP-5
G4  Multiplicative  T015 → T016 → T017 → CLEANUP-6
G5  Module          T018 → T019 → T020 → CLEANUP-7
G6  Tate            CLEANUP-6 → T021 → T022 → T023 → CLEANUP-8 → T024 → T025 → CLEANUP-9
G7  NormComparison  CLEANUP-9 → T026 → T027 → CLEANUP-10
G8  Rescale         T028 → T029 → (CLEANUP-9) T030 → CLEANUP-11 → (CLEANUP-7) T031 → CLEANUP-12
G9  Residue         CLEANUP-4, CLEANUP-9 → T032 → T033 → CLEANUP-13
G11 GaugeNorm       T037 → T038 → CLEANUP-ALL-2 → T039 [M2] → CLEANUP-15
G10 Huber           CLEANUP-13, CLEANUP-5 → T034 → CLEANUP-ALL-1 → T035 [M1]
                    → (CLEANUP-12, CLEANUP-15) T036 → CLEANUP-14
G12 Examples        CLEANUP-13 → T040 → T041 → (CLEANUP-12) T042 → CLEANUP-16
                    → (CLEANUP-5) T043 → T044 → CLEANUP-17
End                 all final per-file cleanups → T045 (chain root) → CLEANUP-FINAL
```

Cleanup cadence: a `/cleanup` after every third proof ticket on a file and after the last one; a `/cleanup-all`
before each milestone; a final `/cleanup-all`. On `GaugeNorm.lean` and `Huber.lean` the pre-milestone sweep is the
mid-file cleanup.

---

## Tickets

### [T001] Null families attain their largest norm
- **Status**: done (2026-09-29) · **File**: `Sums.lean` · **Depends on**: none · **Parallel**: yes (with G3, G4, G5, G11) · **Type**: lemmas
- **Progress**: 2026-09-29 DONE — proved in Sums.lean (private helper `finite_setOf_le_norm`); module builds, axioms standard, runLinter clean.
- **Leaves**: L1.1–L1.3

#### Statement
```lean
theorem Filter.Tendsto.bddAbove_range_norm {f : ι → E} (hf : Tendsto f cofinite (𝓝 0)) :
    BddAbove (Set.range fun i ↦ ‖f i‖) := by sorry
theorem Filter.Tendsto.exists_forall_norm_le [Nonempty ι] {f : ι → E}
    (hf : Tendsto f cofinite (𝓝 0)) : ∃ i₀, ∀ i, ‖f i‖ ≤ ‖f i₀‖ := by sorry
theorem Filter.Tendsto.exists_norm_eq_iSup [Nonempty ι] {f : ι → E}
    (hf : Tendsto f cofinite (𝓝 0)) : ∃ i₀, ‖f i₀‖ = ⨆ i, ‖f i‖ := by sorry
```
#### Proof sketch
1. `bddAbove_range_norm`: `have h := hf.norm; rw [norm_zero] at h; exact h.bddAbove_range_of_cofinite` — this
   exact proof compiles (`scratch/names2.lean`).
2. `exists_forall_norm_le`: obtain `i₁` from `Nonempty`. `by_cases h0 : ∀ i, ‖f i‖ ≤ ‖f i₁‖` — done with `i₁`.
   Otherwise take `i₂` with `‖f i₁‖ < ‖f i₂‖`, so `0 < ‖f i₂‖`. The set `{i | ‖f i₂‖ ≤ ‖f i‖}` is finite:
   `hf.norm.eventually (gt_mem_nhds _)` rewritten with `Filter.eventually_cofinite`, then `Set.Finite.subset`.
   Take a maximiser with `hfin.toFinset.exists_max_image (fun i ↦ ‖f i‖) ⟨i₂, by simp⟩`; for an index outside the
   set use `(not_le.1 _).le.trans`. The block is verbatim the inner part of `scratch/spot.lean`, which compiles.
3. `exists_norm_eq_iSup`: from 2, `le_antisymm (le_ciSup hf.bddAbove_range_norm i₀) (ciSup_le h)`.
#### Mathlib lemmas needed
`Filter.Tendsto.norm`, `Filter.Tendsto.bddAbove_range_of_cofinite`, `Filter.eventually_cofinite`, `gt_mem_nhds`, `Finset.exists_max_image`, `Set.Finite.toFinset`, `le_ciSup`, `ciSup_le`.
#### Sources
[RM] §0.1.1–§0.1.2; decomposition L1.1–L1.3.
#### Generality decision
`SeminormedAddCommGroup`, no ultrametric hypothesis (none is used). `Nonempty ι` replaces the roadmap's "some `f i ≠ 0`" — strictly weaker and necessary. In `Filter.Tendsto` for dot notation on `hf`.

### [T002] The strict bound and the unique dominant term
- **Status**: done (2026-09-29) · **File**: `Sums.lean` · **Depends on**: T001 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-09-29 DONE — proved in Sums.lean (private helper `finite_setOf_le_norm`); module builds, axioms standard, runLinter clean.
- **Leaves**: L1.4–L1.8

#### Statement
```lean
theorem norm_tsum_lt_of_forall_lt {f : ι → E} {B : ℝ} (hB : 0 < B) (hlt : ∀ i, ‖f i‖ < B) :
    ‖∑' i, f i‖ < B := by sorry
theorem nnnorm_tsum_lt_of_forall_lt {f : ι → E} {B : ℝ≥0} (hB : 0 < B)
    (hlt : ∀ i, ‖f i‖₊ < B) : ‖∑' i, f i‖₊ < B := by sorry
theorem norm_tsum_eq_of_forall_lt {f : ι → E} (hf : Summable f) {i₀ : ι}
    (hlt : ∀ i, i ≠ i₀ → ‖f i‖ < ‖f i₀‖) : ‖∑' i, f i‖ = ‖f i₀‖ := by sorry
theorem nnnorm_tsum_eq_of_forall_lt {f : ι → E} (hf : Summable f) {i₀ : ι}
    (hlt : ∀ i, i ≠ i₀ → ‖f i‖₊ < ‖f i₀‖₊) : ‖∑' i, f i‖₊ = ‖f i₀‖₊ := by sorry
theorem norm_tsum_sub_tsum_le {f g : ι → E} (hf : Summable f) (hg : Summable g) :
    ‖∑' i, f i - ∑' i, g i‖ ≤ ⨆ i, ‖f i - g i‖ := by sorry
```
#### Proof sketch
1. `norm_tsum_lt_of_forall_lt`: `by_cases hs : Summable f`. Not summable: `tsum_eq_zero_of_not_summable`,
   `norm_zero`, `hB`. Summable: `ι` empty → `tsum_empty`/`simpa using hB`; otherwise `hs.tendsto_cofinite_zero`,
   T001's `exists_forall_norm_le` gives `i₀`, and
   `(IsUltrametricDist.norm_tsum_le f).trans_lt ((ciSup_le h).trans_lt (hlt i₀))`. **Full proof compiles in
   `scratch/spot.lean`** — copy it, replacing the inlined maximiser by T001.
2. `nnnorm_…lt`: `exact_mod_cast norm_tsum_lt_of_forall_lt (B := B) (by exact_mod_cast hB) (fun i ↦ by exact_mod_cast hlt i)`.
3. `norm_tsum_eq_of_forall_lt`: `classical`; `rw [hf.tsum_eq_add_tsum_ite i₀]`. Let `g i := if i = i₀ then 0 else f i`.
   If `‖f i₀‖ = 0`: `hlt` makes `ι` a subsingleton at `i₀` (any other `i` would have `‖f i‖ < 0`), so `g ≡ 0`,
   `tsum_zero`, `add_zero`. If `0 < ‖f i₀‖`: step 1 with `B := ‖f i₀‖` gives `‖∑' g‖ < ‖f i₀‖` (each `‖g i‖` is `0`
   or `‖f i‖`), then `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt _)` and `max_eq_left`.
4. `nnnorm_…eq`: `NNReal.eq`, step 3 with the hypotheses cast.
5. `norm_tsum_sub_tsum_le`: `rw [← hf.tsum_sub hg]; exact IsUltrametricDist.norm_tsum_le _`.
#### Mathlib lemmas needed
`tsum_eq_zero_of_not_summable`, `Summable.tendsto_cofinite_zero`, `IsUltrametricDist.norm_tsum_le`, `Summable.tsum_eq_add_tsum_ite`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, `Summable.tsum_sub`, `NNReal.coe_lt_coe`, `coe_nnnorm`.
#### Sources
[RM] §0.1.2–§0.1.3, §0.1.5; [Sch] `schneider.txt:625`; [SRC] `LWX/05_Sharpness.{norm_tsum_lt_of_forall_lt, norm_tsum_eq_of_forall_lt}`; decomposition L1.4–L1.8.
#### Generality decision
The strict bound carries **no** nullity or summability hypothesis (weaker than [RM] and [SRC]; proved). The dominant-term lemma takes `Summable f`, not "null + complete": equivalent in a complete group and necessary in general. `NormedAddCommGroup` from step 3 on (`tsum_eq_add_tsum_ite` needs `T2`).

### [T003] Null families on a product
- **Status**: done (2026-09-29) · **File**: `Sums.lean` · **Depends on**: T002 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-09-29 DONE — proved in Sums.lean (private helper `finite_setOf_le_norm`); module builds, axioms standard, runLinter clean.
- **Leaves**: L1.9–L1.13

#### Statement
```lean
theorem Filter.Tendsto.iSup_norm_cofinite_left {f : ι × κ → E}
    (hf : Tendsto f cofinite (𝓝 0)) : Tendsto (fun i ↦ ⨆ j, ‖f (i, j)‖) cofinite (𝓝 0) := by sorry
theorem Filter.Tendsto.iSup_norm_cofinite_right {f : ι × κ → E}
    (hf : Tendsto f cofinite (𝓝 0)) : Tendsto (fun j ↦ ⨆ i, ‖f (i, j)‖) cofinite (𝓝 0) := by sorry
theorem tendsto_cofinite_prod_of_tendsto_iSup_norm {f : ι × κ → E}
    (h₁ : ∀ i, Tendsto (fun j ↦ f (i, j)) cofinite (𝓝 0))
    (h₂ : Tendsto (fun i ↦ ⨆ j, ‖f (i, j)‖) cofinite (𝓝 0)) : Tendsto f cofinite (𝓝 0) := by sorry
theorem tendsto_tsum_cofinite_left {f : ι × κ → E} (hf : Tendsto f cofinite (𝓝 0)) :
    Tendsto (fun i ↦ ∑' j, f (i, j)) cofinite (𝓝 0) := by sorry
theorem tendsto_tsum_cofinite_right {f : ι × κ → E} (hf : Tendsto f cofinite (𝓝 0)) :
    Tendsto (fun j ↦ ∑' i, f (i, j)) cofinite (𝓝 0) := by sorry
```
#### Proof sketch
1. `iSup_norm_cofinite_left`: `rw [Metric.tendsto_nhds]; intro ε hε`; with `F := {p | ε / 2 ≤ ‖f p‖}` finite
   (from `hf`, as in T001), show `∀ᶠ i in cofinite, …` by `Filter.eventually_cofinite` and
   `(hF.image Prod.fst).subset`: for `i ∉ Prod.fst '' F`, every `‖f (i, j)‖ < ε / 2`, so
   `⨆ j, ‖f (i, j)‖ ≤ ε / 2 < ε` — `ciSup_le` when `κ` is nonempty, `Real.iSup_of_isEmpty` otherwise; finish with
   `Real.dist_0_eq_abs`, `abs_of_nonneg (Real.iSup_nonneg fun _ ↦ norm_nonneg _)`.
2. `_right`: step 1 applied to `f ∘ Prod.swap` (nullity of the swap: `hf.comp (Equiv.prodComm κ ι).injective.tendsto_cofinite`).
3. `tendsto_cofinite_prod_of_tendsto_iSup_norm`: for `ε > 0`, `I := {i | ε ≤ ⨆ j, ‖f (i, j)‖}` is finite by `h₂`; for
   `i ∈ I`, `Jᵢ := {j | ε ≤ ‖f (i, j)‖}` is finite by `h₁ i`. `{p | ε ≤ ‖f p‖} ⊆ ⋃ i ∈ I, (fun j ↦ (i, j)) '' Jᵢ`, using
   `le_ciSup (h₁ i).bddAbove_range_norm j`. `Set.Finite.biUnion`, `Set.Finite.image`.
4. `tendsto_tsum_cofinite_left`: `squeeze_zero_norm (fun i ↦ IsUltrametricDist.norm_tsum_le _) hf.iSup_norm_cofinite_left`.
5. `_right`: same with step 2.
#### Mathlib lemmas needed
`Metric.tendsto_nhds`, `Filter.eventually_cofinite`, `Set.Finite.image`, `Set.Finite.biUnion`, `ciSup_le`, `Real.iSup_of_isEmpty`, `Real.iSup_nonneg`, `le_ciSup`, `squeeze_zero_norm`, `Function.Injective.tendsto_cofinite`, `IsUltrametricDist.norm_tsum_le`.
#### Sources
[RM] §0.1.4–§0.1.5; decomposition L1.9–L1.13 (L1.11 records why both hypotheses are necessary).
#### Generality decision
Steps 1–3 for seminormed groups with no ultrametric hypothesis; steps 4–5 need `IsUltrametricDist` but **no completeness** (a non-summable row contributes `0`).

### [CLEANUP-1] Run /cleanup on `Sums.lean`
- **Status**: done (2026-09-29) · **File**: `Sums.lean` · **Depends on**: T003 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-09-29 DONE — inline cleanup: runLinter clean, lines ≤ 100 chars, no deprecated tactics, proofs reviewed.
- Per-file cadence (every third proof ticket on the file, and after the last). Inline as the main agent; `lake exe runLinter` on the module; prune imports with `lake exe shake`.

### [T004] Iterated sums of a null family
- **Status**: done (2026-09-29) · **File**: `Sums.lean` · **Depends on**: CLEANUP-1 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-09-29 DONE — proved in Sums.lean (private helper `finite_setOf_le_norm`); module builds, axioms standard, runLinter clean.
- **Leaves**: L1.14–L1.15

#### Statement
```lean
theorem tsum_prod_eq_tsum_tsum [CompleteSpace E] {f : ι × κ → E}
    (hf : Tendsto f cofinite (𝓝 0)) : ∑' p, f p = ∑' i, ∑' j, f (i, j) := by sorry
theorem tsum_tsum_comm [CompleteSpace E] {f : ι × κ → E} (hf : Tendsto f cofinite (𝓝 0)) :
    ∑' i, ∑' j, f (i, j) = ∑' j, ∑' i, f (i, j) := by sorry
```
#### Proof sketch
1. `tsum_prod_eq_tsum_tsum`: `have hs : Summable f := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hf`;
   `exact hs.tsum_prod' fun i ↦ hs.prod_factor i`.
2. `tsum_tsum_comm`: `rw [← tsum_prod_eq_tsum_tsum hf]`; for the right side apply step 1 to
   `f ∘ Prod.swap` and `(Equiv.prodComm ι κ).tsum_eq`. Alternatively `Summable.tsum_comm'` with both families of
   fibres from `prod_factor`.
#### Mathlib lemmas needed
`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`, `Summable.tsum_prod'`, `Summable.prod_factor`, `Equiv.tsum_eq`, `Summable.tsum_comm'`, `IsUltrametricDist.nonarchimedeanAddGroup` (instance).
#### Sources
[RM] §0.1.4; decomposition L1.14–L1.15.
#### Generality decision
`[NormedAddCommGroup E] [IsUltrametricDist E] [CompleteSpace E]`; completeness is necessary (summability).

### [T005] Bounded biadditive maps and sums
- **Status**: done (2026-09-29) · **File**: `Sums.lean` · **Depends on**: T004 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-09-29 DONE — proved in Sums.lean (private helper `finite_setOf_le_norm`); module builds, axioms standard, runLinter clean.
- **Leaves**: L1.16–L1.18

#### Statement
```lean
theorem tendsto_cofinite_prod_of_norm_le_mul {f : ι → E} {g : κ → F} {b : E → F → G}
    (hb : ∀ x y, ‖b x y‖ ≤ ‖x‖ * ‖y‖) (hf : Tendsto f cofinite (𝓝 0))
    (hg : Tendsto g cofinite (𝓝 0)) :
    Tendsto (fun p : ι × κ ↦ b (f p.1) (g p.2)) cofinite (𝓝 0) := by sorry
theorem summable_prod_map₂ {H : Type*} [NormedAddCommGroup H] {f : ι → H} {g : κ → F}
    {b : H → F → G} (hb : ∀ x y, ‖b x y‖ ≤ ‖x‖ * ‖y‖) (hf : Summable f) (hg : Summable g) :
    Summable fun p : ι × κ ↦ b (f p.1) (g p.2) := by sorry
theorem tsum_prod_map₂ {H : Type*} [NormedAddCommGroup H] {f : ι → H} {g : κ → F}
    (b : H →+ F →+ G) (hb : ∀ x y, ‖b x y‖ ≤ ‖x‖ * ‖y‖) (hf : Summable f) (hg : Summable g) :
    ∑' p : ι × κ, b (f p.1) (g p.2) = b (∑' i, f i) (∑' j, g j) := by sorry
```
#### Proof sketch
1. `tendsto_cofinite_prod_of_norm_le_mul`: `squeeze_zero_norm (fun p ↦ hb _ _)`; it remains that
   `p ↦ ‖f p.1‖ * ‖g p.2‖ → 0` cofinitely. Bounds `C_f`, `C_g` from T001. For `ε > 0`:
   `{p | ε ≤ ‖f p.1‖ * ‖g p.2‖} ⊆ {i | ε / (C_g + 1) ≤ ‖f i‖} ×ˢ {j | ε / (C_f + 1) ≤ ‖g j‖}` (if both factors were
   small the product would be `< ε`); `Set.Finite.prod`.
2. `summable_prod_map₂`: step 1 with `hf.tendsto_cofinite_zero`, `hg.tendsto_cofinite_zero`, then
   `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`.
3. `tsum_prod_map₂`: `rw [tsum_prod_eq_tsum_tsum (step 1)]`. Inner sum: `b (f i) : F →+ G` is continuous by
   `AddMonoidHomClass.continuous_of_bound (b (f i)) ‖f i‖ (hb (f i))`, so `(hg.hasSum.map (b (f i)) _).tsum_eq`.
   Outer sum: the same for `b.flip (∑' j, g j)` with bound `‖∑' g‖` (`mul_comm`).
#### Mathlib lemmas needed
`squeeze_zero_norm`, `Set.Finite.prod`, `Summable.tendsto_cofinite_zero`, `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`, `AddMonoidHomClass.continuous_of_bound`, `HasSum.map`, `HasSum.tsum_eq`, `AddMonoidHom.flip`.
#### Sources
[RM] §0.1.4 ("Mathlib's `tsum_mul_tsum_of_nonarchimedean` is the case of a ring, and the module form is what the matrix product of §2.6 needs"); decomposition L1.16–L1.18.
#### Generality decision
Step 1 for an arbitrary function `b` with the norm bound (no additivity, no ultrametric). Step 3 for `b : H →+ F →+ G` — biadditive, no scalars: covers `•`, `*`, and the matrix product. `H`, `F` need be neither ultrametric nor complete; `G` both.

### [CLEANUP-2] Run /cleanup on `Sums.lean`
- **Status**: done (2026-09-29) · **File**: `Sums.lean` · **Depends on**: T005 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-09-29 DONE — inline cleanup: runLinter clean, lines ≤ 100 chars, no deprecated tactics, proofs reviewed.
- Final per-file cleanup for `Sums.lean`.

### [T006] The closed unit ball as a subring: API
- **Status**: done (2026-09-29) · **File**: `UnitBall.lean` · **Depends on**: none · **Parallel**: yes · **Type**: lemmas
- **Progress**: 2026-09-29 DONE — proved in UnitBall.lean; `norm_tsum_geometric_sub_one` needs no `NormOneClass` (omitted, a weakening); module builds, axioms standard, runLinter clean.
- **Leaves**: L2.1–L2.2

#### Statement
```lean
@[simp]
theorem mem_unitClosedBall {x : R} : x ∈ unitClosedBall R ↔ ‖x‖ ≤ 1 := by sorry
theorem norm_le_one (x : unitClosedBall R) : ‖(x : R)‖ ≤ 1 := by sorry
theorem isOpen_unitClosedBall : IsOpen (unitClosedBall R : Set R) := by sorry
theorem isClosed_unitClosedBall : IsClosed (unitClosedBall R : Set R) := by sorry
```
#### Proof sketch
1. `mem_unitClosedBall`: `show x ∈ Metric.closedBall 0 1 ↔ _; exact mem_closedBall_zero_iff`.
2. `norm_le_one`: `mem_unitClosedBall.1 x.2`.
3. `isOpen_unitClosedBall`: `coe_unitClosedBall ▸ IsUltrametricDist.isOpen_closedBall 0 one_ne_zero`.
4. `isClosed_unitClosedBall`: `coe_unitClosedBall ▸ Metric.isClosed_closedBall`.
#### Mathlib lemmas needed
`mem_closedBall_zero_iff`, `IsUltrametricDist.isOpen_closedBall`, `Metric.isClosed_closedBall`.
#### Sources
[RM] §0.2.1; [Sch] Lemma 1.2.i (`schneider.txt:184`); [Wed] Example 6.13 (`wedhorn.txt:2170`); decomposition L2.1–L2.2.
#### Generality decision
`SeminormedRing` (no commutativity, no separation). The definition extends Mathlib's `Submonoid.unitClosedBall` (`unitClosedBall_toSubmonoid` is `rfl`).

### [T007] Ball ideals of the unit ball
- **Status**: done (2026-09-29) · **File**: `UnitBall.lean` · **Depends on**: T006 · **Parallel**: no · **Type**: def fields + lemmas
- **Progress**: 2026-09-29 DONE — proved in UnitBall.lean; `norm_tsum_geometric_sub_one` needs no `NormOneClass` (omitted, a weakening); module builds, axioms standard, runLinter clean.
- **Leaves**: L2.3–L2.4

#### Statement
```lean
def closedBallIdeal (ε : ℝ≥0) : Ideal (unitClosedBall R) where
  carrier := {a | ‖(a : R)‖₊ ≤ ε}
  add_mem' {a b} ha hb := by
    sorry
  zero_mem' := by simp
  smul_mem' r a ha := by
    sorry
def openUnitBallIdeal : Ideal (unitClosedBall R) where
  carrier := {a | ‖(a : R)‖ < 1}
  add_mem' {a b} ha hb := by
    sorry
  zero_mem' := by simp
  smul_mem' r a ha := by
    sorry
@[simp]
theorem mem_closedBallIdeal {ε : ℝ≥0} {a : unitClosedBall R} :
    a ∈ closedBallIdeal R ε ↔ ‖(a : R)‖ ≤ ε := by sorry
@[simp]
theorem mem_openUnitBallIdeal {a : unitClosedBall R} :
    a ∈ openUnitBallIdeal R ↔ ‖(a : R)‖ < 1 := by sorry
theorem closedBallIdeal_mono {ε δ : ℝ≥0} (h : ε ≤ δ) :
    closedBallIdeal R ε ≤ closedBallIdeal R δ := by sorry
theorem closedBallIdeal_one : closedBallIdeal R 1 = ⊤ := by sorry
theorem closedBallIdeal_mul_le (ε δ : ℝ≥0) :
    closedBallIdeal R ε * closedBallIdeal R δ ≤ closedBallIdeal R (ε * δ) := by sorry
theorem closedBallIdeal_le_openUnitBallIdeal {ε : ℝ≥0} (hε : ε < 1) :
    closedBallIdeal R ε ≤ openUnitBallIdeal R := by sorry
```
#### Proof sketch
1. Fill the four `sorry` proof fields of the two definitions. `add_mem'`: `(nnnorm_add_le_max _ _).trans (max_le ha hb)`
   (respectively `max_lt`). `smul_mem'`: `smul_eq_mul`, `Subring.coe_mul`,
   `(nnnorm_mul_le _ _).trans (mul_le_of_le_one_left (zero_le _) (norm_le_one r))` — the strict version with
   `lt_of_le_of_lt`.
2. `mem_*`: `Iff.rfl` after `NNReal.coe_le_coe` (`mem_closedBallIdeal` is stated with the real norm and `(ε : ℝ)`).
3. `mono`: `fun a ha ↦ le_trans ha h`. `one`: `eq_top_iff`, `norm_le_one`. `le_openUnitBallIdeal`: `lt_of_le_of_lt`.
4. `mul_le`: `Ideal.mul_le.2 fun a ha b hb ↦ _`, `nnnorm_mul_le`, `mul_le_mul'`.
#### Mathlib lemmas needed
`IsUltrametricDist.nnnorm_add_le_max`, `nnnorm_mul_le`, `Subring.coe_mul`, `Ideal.mul_le`, `eq_top_iff`, `NNReal.coe_le_coe`.
#### Sources
[RM] §0.2.1, §0.4.5; [Buz07] `buzzard.txt:158`; decomposition L2.3–L2.4.
#### Generality decision
Left ideals of `R⁰` for any `SeminormedRing`; radius `ε : ℝ≥0` so that no positivity proof is an argument of the definition. `openUnitBallIdeal` is separate because it is not a closed ball.

### [T008] The topology of the unit ball
- **Status**: done (2026-09-29) · **File**: `UnitBall.lean` · **Depends on**: T007 · **Parallel**: no · **Type**: lemmas + instance
- **Progress**: 2026-09-29 DONE — proved in UnitBall.lean; `norm_tsum_geometric_sub_one` needs no `NormOneClass` (omitted, a weakening); module builds, axioms standard, runLinter clean.
- **Leaves**: L2.5–L2.8

#### Statement
```lean
theorem isOpen_closedBallIdeal {ε : ℝ≥0} (hε : 0 < ε) :
    IsOpen (closedBallIdeal R ε : Set (unitClosedBall R)) := by sorry
theorem isOpen_openUnitBallIdeal : IsOpen (openUnitBallIdeal R : Set (unitClosedBall R)) := by sorry
theorem hasBasis_nhds_zero_closedBallIdeal :
    (𝓝 (0 : unitClosedBall R)).HasBasis (fun ε : ℝ≥0 ↦ 0 < ε)
      fun ε ↦ (closedBallIdeal R ε : Set (unitClosedBall R)) := by sorry
instance instIsLinearTopologyUnitClosedBall :
    IsLinearTopology (unitClosedBall R) (unitClosedBall R) := by sorry
theorem openUnitBallIdeal_le_topologicalNilradical :
    openUnitBallIdeal R ≤ topologicalNilradical (unitClosedBall R) := by sorry
theorem openUnitBallIdeal_eq_topologicalNilradical [NormMulClass R] :
    openUnitBallIdeal R = topologicalNilradical (unitClosedBall R) := by sorry
```
#### Proof sketch
1. Openness: the coercion `unitClosedBall R → R` is continuous; the carrier is the preimage of
   `Metric.closedBall 0 ε` (open by `IsUltrametricDist.isOpen_closedBall _ hε.ne'` with `ε` cast) respectively of
   `Metric.ball 0 1`. `IsOpen.preimage continuous_subtype_val`.
2. `hasBasis…`: `Metric.nhds_basis_closedBall` on the subtype (its metric is the restriction), reindexed from
   `ℝ` to `ℝ≥0` by `Filter.HasBasis.to_hasBasis` (`ε ↦ ⟨ε, _⟩`, `ε ↦ (ε : ℝ)`).
3. Instance: `IsLinearTopology.mk_of_hasBasis _ hasBasis_nhds_zero_closedBallIdeal` (check the exact argument
   order with `#check`; the ideals are submodules of `R⁰` over itself).
4. `le_topologicalNilradical`: `IsTopologicallyNilpotent.mem_topologicalNilradical_iff`; nullity of powers in the
   subtype from `tendsto_pow_atTop_nhds_zero_of_norm_lt_one` and `tendsto_subtype_rng`/`Subring.coe_pow`.
5. `eq_topologicalNilradical`: `le_antisymm` step 4 and, conversely, `‖aⁿ‖ = ‖a‖ⁿ` (`norm_pow`) tends to `0`, so
   `‖a‖ < 1` (`tendsto_pow_atTop_nhds_zero_iff` on `ℝ` with `abs_norm`).
#### Mathlib lemmas needed
`IsUltrametricDist.isOpen_closedBall`, `Metric.isOpen_ball`, `continuous_subtype_val`, `Metric.nhds_basis_closedBall`, `Filter.HasBasis.to_hasBasis`, `IsLinearTopology.mk_of_hasBasis`, `IsTopologicallyNilpotent.mem_topologicalNilradical_iff`, `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`, `tendsto_pow_atTop_nhds_zero_iff`, `norm_pow`.
#### Sources
[RM] §0.2.1–§0.2.2; [Wed] Example 5.29(2) (`wedhorn.txt:1606`); decomposition L2.5–L2.8 (L2.8 records the counterexample `ε ∈ ℚ_p[ε]/(ε²)` without `NormMulClass`).
#### Generality decision
The linear-topology instance for any `SeminormedRing`; the nilradical statements for `SeminormedCommRing` because Mathlib defines `topologicalNilradical` for commutative rings only.

### [CLEANUP-3] Run /cleanup on `UnitBall.lean`
- **Status**: done (2026-09-29) · **File**: `UnitBall.lean` · **Depends on**: T008 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-09-29 DONE — inline cleanup: runLinter clean, lines ≤ 100 chars, `_root_.norm_mul_le` needed inside `namespace NormedRing` (the structure field shadows it).
- Per-file cadence (every third proof ticket on the file, and after the last). Inline as the main agent; `lake exe runLinter` on the module; prune imports with `lake exe shake`.

### [T009] The Neumann series: ultrametric norms
- **Status**: done (2026-09-29) · **File**: `UnitBall.lean` · **Depends on**: CLEANUP-3, T002 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-09-29 DONE — proved in UnitBall.lean; `norm_tsum_geometric_sub_one` needs no `NormOneClass` (omitted, a weakening); module builds, axioms standard, runLinter clean.
- **Leaves**: L2.9–L2.12

#### Statement
```lean
theorem norm_one_sub_of_norm_lt_one {x : R} (h : ‖x‖ < 1) : ‖1 - x‖ = 1 := by sorry
theorem norm_tsum_geometric [CompleteSpace R] {x : R} (h : ‖x‖ < 1) :
    ‖∑' n : ℕ, x ^ n‖ = 1 := by sorry
theorem norm_tsum_geometric_sub_one [CompleteSpace R] {x : R} (h : ‖x‖ < 1) :
    ‖∑' n : ℕ, x ^ n - 1‖ = ‖x‖ := by sorry
theorem isUnit_of_norm_one_sub_lt_one [CompleteSpace R] {a : unitClosedBall R}
    (h : ‖(1 : R) - a‖ < 1) : IsUnit a := by sorry
```
#### Proof sketch
1. `norm_one_sub_of_norm_lt_one`: `sub_eq_add_neg`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`
   (`‖1‖ = 1 ≠ ‖-x‖`), `max_eq_left`.
2. `norm_tsum_geometric`: T002's `norm_tsum_eq_of_forall_lt (summable_geometric_of_norm_lt_one h) (i₀ := 0)`; for
   `n ≠ 0`, `‖xⁿ‖ ≤ ‖x‖ⁿ < 1 = ‖x⁰‖` by `norm_pow_le' x (Nat.pos_of_ne_zero _)`, `pow_lt_one₀`; `pow_zero`, `norm_one`.
3. `norm_tsum_geometric_sub_one`: `x = 0`: `simp` (`tsum` of `0 ^ n`). `x ≠ 0`: `geom_series_succ x h` rewrites the left
   side as `‖∑' i, x ^ (i + 1)‖`; T002 at `i₀ = 0` with `‖x ^ (i + 2)‖ ≤ ‖x‖ ^ (i + 2) < ‖x‖` (`pow_lt_self_of_lt_one₀`
   or `mul_lt_of_lt_one_left`); summability by `(summable_geometric_of_norm_lt_one h).comp_injective`.
4. `isUnit_of_norm_one_sub_lt_one`: `x := 1 - a`; the inverse is `⟨∑' n, xⁿ, mem_unitClosedBall.2 (step 2).le⟩`;
   `mul_neg_geom_series`, `geom_series_mul_neg` with `1 - x = a`, in the subring by `Subtype.ext`.
#### Mathlib lemmas needed
`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, `summable_geometric_of_norm_lt_one`, `norm_pow_le'`, `pow_lt_one₀`, `geom_series_succ`, `mul_neg_geom_series`, `geom_series_mul_neg`, `Summable.comp_injective`.
#### Sources
[RM] §0.2.3 ("`‖(1 − x)⁻¹‖ = 1` and `‖(1 − x)⁻¹ − 1‖ = ‖x‖`; Mathlib's `Units.oneSub` is the unit, and the ultrametric equalities are new"); decomposition L2.9–L2.12.
#### Generality decision
`NormedRing` (not commutative), `NormOneClass`, ultrametric; completeness only where the series is summed. Stated on `∑' n, x ^ n`, which is definitionally the inverse of `Units.oneSub x h`.

### [T010] Units of the unit ball and the Jacobson radical
- **Status**: done (2026-09-29) · **File**: `UnitBall.lean` · **Depends on**: T009 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-09-29 DONE — proved in UnitBall.lean; `norm_tsum_geometric_sub_one` needs no `NormOneClass` (omitted, a weakening); module builds, axioms standard, runLinter clean.
- **Leaves**: L2.13–L2.14

#### Statement
```lean
theorem isUnit_iff_isUnit_mk (a : unitClosedBall R) :
    IsUnit a ↔ IsUnit (Ideal.Quotient.mk (openUnitBallIdeal R) a) := by sorry
theorem openUnitBallIdeal_le_jacobson_bot :
    openUnitBallIdeal R ≤ Ideal.jacobson (⊥ : Ideal (unitClosedBall R)) := by sorry
```
#### Proof sketch
1. `isUnit_iff_isUnit_mk`: `⇒` `IsUnit.map`. `⇐`: obtain `b` with `mk a * mk b = 1` (surjectivity of
   `Ideal.Quotient.mk`), so `1 - a * b ∈ openUnitBallIdeal R` (`Ideal.Quotient.eq`), i.e. `‖1 - (a * b : R)‖ < 1`; T009
   gives `IsUnit (a * b)`; `isUnit_of_mul_isUnit_left`.
2. `openUnitBallIdeal_le_jacobson_bot`: `Ideal.mem_jacobson_bot.2 fun y ↦ _`; `x * y + 1` satisfies
   `‖1 - (x * y + 1)‖ = ‖x * y‖ ≤ ‖x‖ * ‖y‖ < 1`; T009.
#### Mathlib lemmas needed
`IsUnit.map`, `Ideal.Quotient.mk_surjective`, `Ideal.Quotient.eq`, `isUnit_of_mul_isUnit_left`, `Ideal.mem_jacobson_bot`, `norm_mul_le`.
#### Sources
[RM] §0.2.3, **corrected** (erratum E2: the roadmap's "unique maximal ideal when the norm is multiplicative" is false — `ℚ_p⟨X⟩`); decomposition L2.13–L2.14; [SRC] `PowerBounded.isUnit_iff_isUnit_mk_topologicalNilradical`.
#### Generality decision
`NormedCommRing` + complete: commutativity is used (quotient ring; a unit from a product).

### [T011] The unit ball of a normed field is a local ring
- **Status**: done (2026-09-29) · **File**: `UnitBall.lean` · **Depends on**: T010 · **Parallel**: yes (independent of T009–T010) · **Type**: lemmas + instance
- **Progress**: 2026-09-29 DONE — proved in UnitBall.lean; `norm_tsum_geometric_sub_one` needs no `NormOneClass` (omitted, a weakening); module builds, axioms standard, runLinter clean.
- **Leaves**: L2.15

#### Statement
```lean
theorem isUnit_iff_norm_eq_one {a : unitClosedBall K} : IsUnit a ↔ ‖(a : K)‖ = 1 := by sorry
instance instIsLocalRingUnitClosedBall : IsLocalRing (unitClosedBall K) := by sorry
theorem maximalIdeal_unitClosedBall :
    IsLocalRing.maximalIdeal (unitClosedBall K) = openUnitBallIdeal K := by sorry
```
#### Proof sketch
1. `isUnit_iff_norm_eq_one`: `⇒`: `a * b = 1` in `K⁰` gives `‖a‖ * ‖b‖ = 1` with both `≤ 1`, so `‖a‖ = 1`
   (`mul_eq_one_iff_of_le_one`-style: `‖a‖ = ‖a‖ * 1 ≥ ‖a‖ * ‖b‖ = 1`). `⇐`: `a ≠ 0`, inverse `⟨(a : K)⁻¹, _⟩` with
   `norm_inv`, `inv_one`.
2. Instance: `IsLocalRing.of_nonunits_add`; nonunits are `‖·‖ < 1` by step 1 (`lt_of_le_of_ne`), closed under `+` by
   `norm_add_le_max`. Nontriviality of the subring from `NormOneClass`.
3. `maximalIdeal…`: `Ideal.ext`, `IsLocalRing.mem_maximalIdeal`, `mem_nonunits_iff`, step 1.
#### Mathlib lemmas needed
`norm_inv`, `IsLocalRing.of_nonunits_add`, `IsLocalRing.mem_maximalIdeal`, `mem_nonunits_iff`, `IsUltrametricDist.norm_add_le_max`.
#### Sources
[Sch] Lemma 1.2 ii–iii (`schneider.txt:184`): "`m := {a ∈ K : |a| < 1}` is the unique maximal ideal of `o`; `o× = o ∖ m`"; [RM] §0.2.3 in its corrected field form; decomposition L2.15.
#### Generality decision
`NormedField` with ultrametric norm; **no completeness** and no nontriviality of the valuation (then `K⁰ = K`, `K⁰⁰ = 0`, consistent).

### [CLEANUP-4] Run /cleanup on `UnitBall.lean`
- **Status**: done (2026-09-29) · **File**: `UnitBall.lean` · **Depends on**: T011 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-09-29 DONE — inline cleanup: runLinter clean, lines ≤ 100 chars, `_root_.norm_mul_le` needed inside `namespace NormedRing` (the structure field shadows it).
- Final per-file cleanup for `UnitBall.lean`.

### [T012] Norm-bounded sets are bounded
- **Status**: done (2026-09-29) · **File**: `PowerBounded.lean` · **Depends on**: none · **Parallel**: yes · **Type**: lemmas
- **Progress**: 2026-09-29 DONE — proved in PowerBounded.lean (private helper `norm_pow_succ_of_normMulClass`, no `NormOneClass`); builds, axioms standard, runLinter clean.
- **Leaves**: L3.1–L3.2

#### Statement
```lean
theorem isBounded_of_forall_norm_le {S : Set R} {C : ℝ} (h : ∀ s ∈ S, ‖s‖ ≤ C) :
    IsBounded S := by sorry
theorem isPowerBounded_of_norm_pow_le {a : R} {C : ℝ} (hC : ∀ n : ℕ, ‖a ^ n‖ ≤ C) :
    IsPowerBounded a := by sorry
theorem isPowerBounded_of_norm_le_one {a : R} (ha : ‖a‖ ≤ 1) : IsPowerBounded a := by sorry
```
#### Proof sketch
1. `isBounded_of_forall_norm_le`: `intro U hU; obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU`; `C' := max C 0 + 1`;
   `V := Metric.ball 0 (ε / C')`; for `v ∈ V`, `s ∈ S`: `‖v * s‖ ≤ ‖v‖ * ‖s‖ < (ε / C') * C' = ε`
   (`Set.mul_subset_iff`, `mem_ball_zero_iff`).
2. `isPowerBounded_of_norm_pow_le`: step 1 on `Set.range (a ^ ·)` (`Set.forall_mem_range`).
3. `isPowerBounded_of_norm_le_one`: step 2 with `C := max ‖(1 : R)‖ 1`: `n = 0` gives `pow_zero`; `n + 1`:
   `norm_pow_le' a n.succ_pos` and `pow_le_one₀`.
#### Mathlib lemmas needed
`Metric.mem_nhds_iff`, `Set.mul_subset_iff`, `mem_ball_zero_iff`, `norm_mul_le`, `Set.forall_mem_range`, `norm_pow_le'`, `pow_le_one₀`.
#### Sources
[Wed] Definition 5.27 and Example 5.29(2) (`wedhorn.txt:1589, 1606`); [RM] §0.2.1; decomposition L3.0–L3.2. The two seam definitions are verbatim from mathlib4#40013 and must not be edited.
#### Generality decision
`SeminormedRing`; **no `NormOneClass`** (`‖1‖` is a constant) — weaker than [SRC].

### [T013] Bounded implies norm-bounded, for a multiplicative norm
- **Status**: done (2026-09-29) · **File**: `PowerBounded.lean` · **Depends on**: T012 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-09-29 DONE — proved in PowerBounded.lean (private helper `norm_pow_succ_of_normMulClass`, no `NormOneClass`); builds, axioms standard, runLinter clean.
- **Leaves**: L3.3–L3.4

#### Statement
```lean
theorem IsBounded.exists_norm_le {S : Set R} (hS : IsBounded S) : ∃ C, ∀ s ∈ S, ‖s‖ ≤ C := by sorry
theorem IsPowerBounded.norm_le_one {a : R} (ha : IsPowerBounded a) : ‖a‖ ≤ 1 := by sorry
theorem isPowerBounded_iff_norm_le_one {a : R} : IsPowerBounded a ↔ ‖a‖ ≤ 1 := by sorry
```
#### Proof sketch
1. `IsBounded.exists_norm_le`: apply `hS` to `U := Metric.ball 0 1`; get `V ∈ 𝓝 0` with `V * S ⊆ U`. From
   `NeBot (𝓝[≠] 0)`: `V ∩ {0}ᶜ` is nonempty (`Filter.NeBot.nonempty_of_mem` with `inter_mem_nhdsWithin`), giving
   `v ∈ V`, `v ≠ 0`. For `s ∈ S`: `‖v‖ * ‖s‖ = ‖v * s‖ < 1` (`norm_mul`), so `‖s‖ ≤ ‖v‖⁻¹`.
2. `IsPowerBounded.norm_le_one`: by contradiction `1 < ‖a‖`; step 1 gives `C` with `‖a ^ n‖ ≤ C`; `‖a ^ (n+1)‖ = ‖a‖ ^ (n+1)`
   by induction from `norm_mul`; `tendsto_pow_atTop_atTop_of_one_lt` contradicts the bound.
3. iff: step 2 and T012.
#### Mathlib lemmas needed
`Filter.NeBot.nonempty_of_mem`, `inter_mem_nhdsWithin`, `norm_mul`, `tendsto_pow_atTop_atTop_of_one_lt`, `Filter.Tendsto.eventually_gt_atTop`.
#### Sources
[Wed] Example 5.29(2) ("One has `A° = {x ∈ A ; |x| ≤ 1}`"); [RM] §0.2.2; decomposition L3.3–L3.4; [SRC] `ForMathlib/Analysis/Normed/Ring/PowerBounded`.
#### Generality decision
`NormedRing` + `NormMulClass` + `NeBot (𝓝[≠] 0)`; both necessary (the two counterexamples are T043, T044). `NormOneClass` not assumed.

### [T014] Topological nilpotency and the norm
- **Status**: done (2026-09-29) · **File**: `PowerBounded.lean` · **Depends on**: T013 · **Parallel**: yes (independent of T012–T013) · **Type**: lemmas
- **Progress**: 2026-09-29 DONE — proved in PowerBounded.lean (private helper `norm_pow_succ_of_normMulClass`, no `NormOneClass`); builds, axioms standard, runLinter clean.
- **Leaves**: L3.5

#### Statement
```lean
theorem of_norm_lt_one {R : Type*} [SeminormedRing R] {x : R} (hx : ‖x‖ < 1) :
    IsTopologicallyNilpotent x := by sorry
theorem norm_lt_one {R : Type*} [NormedRing R] [NormMulClass R] {x : R}
    (hx : IsTopologicallyNilpotent x) : ‖x‖ < 1 := by sorry
theorem isTopologicallyNilpotent_iff_norm_lt_one {R : Type*} [NormedRing R] [NormMulClass R]
    {x : R} : IsTopologicallyNilpotent x ↔ ‖x‖ < 1 := by sorry
```
#### Proof sketch
1. `of_norm_lt_one`: `exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx` (`IsTopologicallyNilpotent` unfolds to this
   `Tendsto`; if the unfolding is not definitional use `IsTopologicallyNilpotent` `show`).
2. `norm_lt_one`: `hx.norm` gives `‖xⁿ‖ → 0`; `‖x ^ (n+1)‖ = ‖x‖ ^ (n+1)` (`norm_mul` induction); if `1 ≤ ‖x‖` the powers
   are `≥ 1`, contradiction with `eventually_lt_of_tendsto_lt`.
3. iff: `⟨norm_lt_one, of_norm_lt_one⟩`.
#### Mathlib lemmas needed
`tendsto_pow_atTop_nhds_zero_of_norm_lt_one`, `Filter.Tendsto.norm`, `norm_mul`, `one_le_pow₀`, `Filter.Tendsto.eventually_lt_const`.
#### Sources
[Wed] Definition 5.25 and Example 5.29(2); [RM] §0.2.1–§0.2.2; decomposition L3.5.
#### Generality decision
`of_norm_lt_one` for any `SeminormedRing`; the converse needs `NormMulClass` (not `NeBot`).

### [CLEANUP-5] Run /cleanup on `PowerBounded.lean`
- **Status**: done (2026-09-29) · **File**: `PowerBounded.lean` · **Depends on**: T014 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-09-29 DONE — inline cleanup: runLinter clean, seam definitions untouched.
- Final per-file cleanup for `PowerBounded.lean`. Do not rename or reshape the two seam definitions.

### [T015] Multiplicative elements: products and powers
- **Status**: done (2026-09-29) · **File**: `Multiplicative.lean` · **Depends on**: none · **Parallel**: yes · **Type**: lemmas
- **Progress**: 2026-09-29 DONE — proved in Multiplicative.lean; builds, axioms standard, runLinter clean.
- **Leaves**: L4.1

#### Statement
```lean
theorem mul (ha : IsMultiplicative a) (hb : IsMultiplicative b) : IsMultiplicative (a * b) := by sorry
theorem norm_pow_mul (ha : IsMultiplicative a) (n : ℕ) (x : R) :
    ‖a ^ n * x‖ = ‖a‖ ^ n * ‖x‖ := by sorry
theorem one : IsMultiplicative (1 : R) := by sorry
theorem norm_pow (ha : IsMultiplicative a) (n : ℕ) : ‖a ^ n‖ = ‖a‖ ^ n := by sorry
theorem pow (ha : IsMultiplicative a) (n : ℕ) : IsMultiplicative (a ^ n) := by sorry
theorem isMultiplicative_of_normMulClass {R : Type*} [Norm R] [Mul R] [NormMulClass R] (a : R) :
    IsMultiplicative a := by sorry
```
#### Proof sketch
1. `mul`: `fun x ↦ by rw [mul_assoc, ha, hb, ha, mul_assoc]` ([SRC] `00_Tate.IsMultiplicative.mul`).
2. `norm_pow_mul`: induction on `n`; `pow_succ`, `mul_assoc`, the hypothesis at `a * x`; `pow_zero`, `one_mul` at `0`.
3. `one`: `fun x ↦ by rw [one_mul, norm_one, one_mul]`.
4. `norm_pow`: `by simpa using ha.norm_pow_mul n 1`.
5. `pow`: `fun x ↦ by rw [ha.norm_pow_mul, ha.norm_pow]`.
6. `isMultiplicative_of_normMulClass`: `fun x ↦ norm_mul a x`.
#### Mathlib lemmas needed
`norm_one`, `norm_mul`, `pow_succ`, `mul_assoc`.
#### Sources
[JN] `jn.txt:487` ("`r ∈ R` is multiplicative if `|rs| = |r||s|` for all `s ∈ R`"); [RM] §0.2.4; decomposition L4.1.
#### Generality decision
`SeminormedRing`; `NormOneClass` exactly for `one`, `norm_pow`, `pow` (the `n = 0` case; necessary — decomposition L4.1). Left-multiplicative; no commutativity.

### [T016] Multiplicative units
- **Status**: done (2026-09-29) · **File**: `Multiplicative.lean` · **Depends on**: T015 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-09-29 DONE — proved in Multiplicative.lean; builds, axioms standard, runLinter clean.
- **Leaves**: L4.2–L4.3

#### Statement
```lean
theorem isMultiplicative_units_iff (u : Rˣ) :
    IsMultiplicative (u : R) ↔ ‖((u⁻¹ : Rˣ) : R)‖ = ‖(u : R)‖⁻¹ := by sorry
theorem norm_pos (hu : IsMultiplicative (u : R)) : 0 < ‖(u : R)‖ := by sorry
theorem norm_inv (hu : IsMultiplicative (u : R)) : ‖((u⁻¹ : Rˣ) : R)‖ = ‖(u : R)‖⁻¹ := by sorry
theorem inv (hu : IsMultiplicative (u : R)) : IsMultiplicative ((u⁻¹ : Rˣ) : R) := by sorry
theorem zpow (hu : IsMultiplicative (u : R)) (n : ℤ) : IsMultiplicative ((u ^ n : Rˣ) : R) := by sorry
theorem norm_zpow (hu : IsMultiplicative (u : R)) (n : ℤ) :
    ‖((u ^ n : Rˣ) : R)‖ = ‖(u : R)‖ ^ n := by sorry
```
#### Proof sketch
1. `isMultiplicative_units_iff`. `⇒`: `hu (↑u⁻¹)` with `Units.mul_inv`, `norm_one` gives `1 = ‖u‖ * ‖u⁻¹‖`;
   `eq_inv_of_mul_eq_one_right`. `⇐`: first `0 < ‖u‖` (else `‖u⁻¹‖ = 0⁻¹ = 0` and
   `1 = ‖u * u⁻¹‖ ≤ ‖u‖ * ‖u⁻¹‖ = 0`). Then for `x`: `‖u * x‖ ≤ ‖u‖ * ‖x‖` (`norm_mul_le`) and
   `‖x‖ = ‖u⁻¹ * (u * x)‖ ≤ ‖u‖⁻¹ * ‖u * x‖`; `le_antisymm` after `le_inv_mul_iff₀`.
2. `norm_pos`: as in the `⇐` argument, from `hu (↑u⁻¹)`: `‖u‖ * ‖u⁻¹‖ = 1`. `norm_inv`: step 1 `⇒`.
3. `inv`: step 1 `⇐` for `u⁻¹`, with `inv_inv` and `norm_inv`.
4. `zpow`, `norm_zpow`: `Int.induction_on`; `zpow_add_one`, `zpow_sub_one`, `Units.val_mul`, T015 `mul`, step 3;
   norms by `hu`/`inv` applied to the previous power; `zpow_add_one₀`, `zpow_sub_one₀` with `norm_pos.ne'`.
#### Mathlib lemmas needed
`Units.mul_inv`, `Units.inv_mul`, `norm_mul_le`, `eq_inv_of_mul_eq_one_right`, `le_inv_mul_iff₀`, `Int.induction_on`, `zpow_add_one`, `zpow_sub_one`, `zpow_add_one₀`, `zpow_sub_one₀`, `Units.val_mul`.
#### Sources
[JN] `jn.txt:496` ("a unit `ϖ` … is multiplicative if and only if `|ϖ⁻¹| = |ϖ|⁻¹`"); [Bel] Exercise II.1.1 (`bellaiche.txt:1963`); [RM] §0.2.4; decomposition L4.2–L4.3.
#### Generality decision
`SeminormedRing` + `NormOneClass`; the iff is safe for seminorms (positivity of `‖u‖` is derived).

### [T017] Multiplicative units scale module norms exactly
- **Status**: done (2026-09-29) · **File**: `Multiplicative.lean` · **Depends on**: T016 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-09-29 DONE — proved in Multiplicative.lean; builds, axioms standard, runLinter clean.
- **Leaves**: L4.4

#### Statement
```lean
theorem norm_smul (hu : IsMultiplicative (u : R)) (m : M) : ‖(u : R) • m‖ = ‖(u : R)‖ * ‖m‖ := by sorry
theorem norm_zpow_smul (hu : IsMultiplicative (u : R)) (n : ℤ) (m : M) :
    ‖((u ^ n : Rˣ) : R) • m‖ = ‖(u : R)‖ ^ n * ‖m‖ := by sorry
```
#### Proof sketch
1. `norm_smul`: `le_antisymm (norm_smul_le _ _)`; for the other inequality
   `‖m‖ = ‖(↑u⁻¹ : R) • (u : R) • m‖ ≤ ‖↑u⁻¹‖ * ‖u • m‖ = ‖u‖⁻¹ * ‖u • m‖` (`smul_smul`, `Units.inv_mul`, `one_smul`,
   `hu.norm_inv`), then multiply by `‖u‖ > 0` ([SRC] `01_OperatorNorm.norm_pseudoUniformizer_smul`).
2. `norm_zpow_smul`: step 1 for the unit `u ^ n` with T016's `zpow` and `norm_zpow`.
#### Mathlib lemmas needed
`norm_smul_le`, `smul_smul`, `Units.inv_mul`, `one_smul`, `mul_le_mul_of_nonneg_left`, `mul_inv_cancel₀`.
#### Sources
[JN] `jn.txt:519` ("if `r ∈ R` is a multiplicative unit, then one sees easily that `‖rm‖ = |r|·‖m‖` for all `m ∈ M`"); [Bel] proof of Lemma II.1.12 (`bellaiche.txt:2087`); decomposition L4.4.
#### Generality decision
`SeminormedAddCommGroup M` with `IsBoundedSMul R M` — no ultrametric, no completeness.

### [CLEANUP-6] Run /cleanup on `Multiplicative.lean`
- **Status**: done (2026-09-29) · **File**: `Multiplicative.lean` · **Depends on**: T017 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-09-29 DONE — inline cleanup: runLinter clean; `_root_.` prefixes where the namespace shadows `norm_mul`/`norm_mul_le`; deprecated `Int.ofNat_eq_coe` replaced.
- Final per-file cleanup for `Multiplicative.lean`.

### [T018] Products and submodules
- **Status**: done (2026-09-29) · **File**: `Module.lean` · **Depends on**: none · **Parallel**: yes · **Type**: instances
- **Progress**: 2026-09-29 DONE — proved in Module.lean; builds, axioms standard, runLinter clean.
- **Leaves**: L5.1–L5.2

#### Statement
```lean
instance Prod.instIsUltrametricDist {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [IsUltrametricDist X] [IsUltrametricDist Y] : IsUltrametricDist (X × Y) := by sorry
instance Submodule.instIsBoundedSMul {R M : Type*} [SeminormedRing R] [SeminormedAddCommGroup M]
    [Module R M] [IsBoundedSMul R M] (S : Submodule R M) : IsBoundedSMul R S := by sorry
```
#### Proof sketch
1. `Prod.instIsUltrametricDist`: `⟨fun x y z ↦ _⟩`; `Prod.dist_eq`; `max_le` of the two coordinate inequalities
   `dist_triangle_max`, each followed by `le_max_of_le_left/right` and `max_le_max`.
2. `Submodule.instIsBoundedSMul`: the two fields are the fields of `IsBoundedSMul R M` at the coerced points:
   `dist_smul_pair' r x y := dist_smul_pair r (x : M) y`, `dist_pair_smul' r s x := dist_pair_smul r s (x : M)`
   (`Subtype.dist_eq`, `Submodule.coe_smul`).
#### Mathlib lemmas needed
`Prod.dist_eq`, `dist_triangle_max`, `max_le_max`, `dist_smul_pair`, `dist_pair_smul`, `Subtype.dist_eq`, `Submodule.coe_smul`.
#### Sources
[RM] §0.3.1; decomposition L5.1–L5.2 (absence of both instances verified by a failing `inferInstance`).
#### Generality decision
`PseudoMetricSpace` for the product (no group structure needed); `SeminormedRing`/`SeminormedAddCommGroup` for the submodule.

### [T019] The quotient norm is ultrametric
- **Status**: done (2026-09-29) · **File**: `Module.lean` · **Depends on**: T018 · **Parallel**: no · **Type**: instances
- **Progress**: 2026-09-29 DONE — proved in Module.lean; builds, axioms standard, runLinter clean.
- **Leaves**: L5.3

#### Statement
```lean
instance QuotientAddGroup.instIsUltrametricDist (S : AddSubgroup M) :
    IsUltrametricDist (M ⧸ S) := by sorry
instance Submodule.Quotient.instIsUltrametricDist {R : Type*} [Ring R] [Module R M]
    (S : Submodule R M) : IsUltrametricDist (M ⧸ S) := by sorry
instance Ideal.Quotient.instIsUltrametricDist {R : Type*} [SeminormedCommRing R]
    [IsUltrametricDist R] (I : Ideal R) : IsUltrametricDist (R ⧸ I) := by sorry
```
#### Proof sketch
1. `QuotientAddGroup…`: `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`; given `x y : M ⧸ S` show
   `‖x + y‖ ≤ max ‖x‖ ‖y‖` by `le_of_forall_pos_lt_add`: for `ε > 0` pick representatives `m`, `n` with
   `‖m‖ < ‖x‖ + ε`, `‖n‖ < ‖y‖ + ε` (`QuotientAddGroup.norm_lt_iff`), then
   `‖x + y‖ ≤ ‖m + n‖ ≤ max ‖m‖ ‖n‖ < max ‖x‖ ‖y‖ + ε` (`QuotientAddGroup.norm_mk_le_norm`, `max_add_add_right`).
2. The other two: `inferInstanceAs (IsUltrametricDist (M ⧸ S.toAddSubgroup))` — Mathlib's norm on these quotients is
   defined that way; if `inferInstanceAs` fails, repeat step 1 with `Submodule.Quotient.norm_mk_lt`.
#### Mathlib lemmas needed
`IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`, `QuotientAddGroup.norm_lt_iff`, `QuotientAddGroup.norm_mk_le_norm`, `le_of_forall_pos_lt_add`, `IsUltrametricDist.norm_add_le_max`, `max_add_add_right`.
#### Sources
[Sch] §5.B (`schneider.txt:975`): "for any seminorm `q` on `V` one has the quotient seminorm `q(v + U) := inf_{u ∈ U} q(v + u)`"; Prop 8.3 (`:2281`); [RM] §0.3.1; decomposition L5.3.
#### Generality decision
Seminormed (no closedness of `S` needed for the ultrametric inequality); completeness is already Mathlib's `Submodule.Quotient.completeSpace`.

### [T020] Completeness along a bounded equivalence
- **Status**: done (2026-09-29) · **File**: `Module.lean` · **Depends on**: T019 · **Parallel**: yes (independent) · **Type**: lemma
- **Progress**: 2026-09-29 DONE — proved in Module.lean; builds, axioms standard, runLinter clean.
- **Leaves**: L5.4

#### Statement
```lean
theorem AddEquiv.completeSpace_congr_of_bounds {E F : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] (e : E ≃+ F) {C C' : ℝ} (h : ∀ x, ‖e x‖ ≤ C * ‖x‖)
    (h' : ∀ y, ‖e.symm y‖ ≤ C' * ‖y‖) : CompleteSpace E ↔ CompleteSpace F := by sorry
```
#### Proof sketch
1. Both `e` and `e.symm` are Lipschitz: `AddMonoidHomClass.lipschitz_of_bound e C h`, likewise for `e.symm`.
2. Build the `UniformEquiv` with `toEquiv := e.toEquiv` and the two `LipschitzWith.uniformContinuous`.
3. `completeSpace_congr` along its `isUniformEmbedding` (or `UniformEquiv.completeSpace_iff` if present — `#check`).
#### Mathlib lemmas needed
`AddMonoidHomClass.lipschitz_of_bound`, `LipschitzWith.uniformContinuous`, `UniformEquiv.isUniformEmbedding`, `completeSpace_congr`.
#### Sources
[RM] §0.3.2 ("bounded-equivalent norms have the same bounded maps and the same Cauchy sequences"); [Sch] proof of Prop 10.1 (`schneider.txt:2953`); decomposition L5.4.
#### Generality decision
Two norms are two types related by an additive equivalence with a bound each way (plan decision 4). Seminormed; constants are arbitrary reals.

### [CLEANUP-7] Run /cleanup on `Module.lean`
- **Status**: done (2026-09-29) · **File**: `Module.lean` · **Depends on**: T020 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-09-29 DONE — inline cleanup: runLinter clean.
- Final per-file cleanup for `Module.lean`.

### [T021] Pseudo-uniformisers: norms of powers
- **Status**: done (2026-09-29) · **File**: `Tate.lean` · **Depends on**: CLEANUP-6 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-09-29 DONE — proved in Tate.lean; `val_self`/`val_one`/`val_zpow_self` obtain `Nontrivial R` from `NormOneClass.nontrivial` (not an instance); `val_mul` needs no `NormOneClass` (omitted, a weakening); builds, axioms standard.
- **Leaves**: L6.0b–L6.1

#### Statement
```lean
theorem normOneClass_of_nontrivial [Nontrivial R] (ϖ : PseudoUniformizer R) : NormOneClass R := by sorry
theorem norm_pos : 0 < ‖(ϖ : R)‖ := by sorry
theorem norm_inv : ‖((ϖ.unit⁻¹ : Rˣ) : R)‖ = ‖(ϖ : R)‖⁻¹ := by sorry
theorem norm_zpow (n : ℤ) : ‖((ϖ.unit ^ n : Rˣ) : R)‖ = ‖(ϖ : R)‖ ^ n := by sorry
theorem log_norm_neg : Real.log ‖(ϖ : R)‖ < 0 := by sorry
theorem norm_smul (m : M) : ‖(ϖ : R) • m‖ = ‖(ϖ : R)‖ * ‖m‖ := by sorry
theorem norm_zpow_smul (n : ℤ) (m : M) :
    ‖((ϖ.unit ^ n : Rˣ) : R) • m‖ = ‖(ϖ : R)‖ ^ n * ‖m‖ := by sorry
```
#### Proof sketch
0. `normOneClass_of_nontrivial`: `have h := ϖ.isMultiplicative 1`; `mul_one` turns it into `‖ϖ‖ = ‖ϖ‖ * ‖1‖`;
   `‖ϖ‖ ≠ 0` is `norm_ne_zero_iff.2 ϖ.unit.ne_zero`; conclude with `mul_right_eq_self₀` (proof compiled in
   `scratch/spot2.lean`). It shows `[NormOneClass R]` below is no more than `[Nontrivial R]`.
The other six are T016–T017 at `u := ϖ.unit`, `hu := ϖ.isMultiplicative`:
`ϖ.isMultiplicative.norm_pos`, `.norm_inv`, `.norm_zpow n`, `.norm_smul m`, `.norm_zpow_smul n m`.
`log_norm_neg`: `Real.log_neg ϖ.norm_pos ϖ.norm_lt_one`.
#### Mathlib lemmas needed
`Real.log_neg`, `norm_ne_zero_iff`, `Units.ne_zero`, `mul_right_eq_self₀`; T016, T017.
#### Sources
[JN] Definition 2.1.1(1) (`jn.txt:476`, "`|1| = 1`"), Definition 2.1.2 and the remarks at `jn.txt:496, 519`; [RM] §0.4.1; decomposition L6.0b–L6.1.
#### Generality decision
`NormedRing` + `NormOneClass` (erratum E5: positivity needs `‖1‖ = 1`). `NormedAddCommGroup M` to match T022.

### [T022] The scaling trick
- **Status**: done (2026-09-29) · **File**: `Tate.lean` · **Depends on**: T021 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-09-29 DONE — proved in Tate.lean; `val_self`/`val_one`/`val_zpow_self` obtain `Nontrivial R` from `NormOneClass.nontrivial` (not an instance); `val_mul` needs no `NormOneClass` (omitted, a weakening); builds, axioms standard.
- **Leaves**: L6.2–L6.3

#### Statement
```lean
theorem existsUnique_zpow_norm_smul_mem_Ioc {δ : ℝ} (hδ : 0 < δ) {m : M} (hm : m ≠ 0) :
    ∃! n : ℤ, ‖((ϖ.unit ^ n : Rˣ) : R) • m‖ ∈ Set.Ioc (δ * ‖(ϖ : R)‖) δ := by sorry
theorem existsUnique_zpow_norm_smul_mem_Ioc_one {m : M} (hm : m ≠ 0) :
    ∃! n : ℤ, ‖((ϖ.unit ^ n : Rˣ) : R) • m‖ ∈ Set.Ioc ‖(ϖ : R)‖ 1 := by sorry
```
#### Proof sketch
Put `c := ‖(ϖ : R)‖ ∈ (0, 1)` (T021). By T021, `‖ϖ ^ n • m‖ = c ^ n * ‖m‖`, so the claim is: there is a unique
`n : ℤ` with `δ * c < c ^ n * ‖m‖ ≤ δ`.
1. Existence. `exists_mem_Ioc_zpow (x := ‖m‖ / δ) (y := c⁻¹)` (`0 < ‖m‖ / δ` from `norm_pos_iff.2 hm`; `1 < c⁻¹`
   from `one_lt_inv₀`) gives `k` with `(c⁻¹) ^ k < ‖m‖ / δ ≤ (c⁻¹) ^ (k + 1)`. Take `n := k + 1`: multiplying through
   by `c ^ (k + 1) * δ > 0` gives `δ * c < c ^ (k + 1) * ‖m‖ ≤ δ` (`inv_zpow'`, `zpow_neg`, `zpow_add_one₀`,
   `lt_div_iff₀`, `div_le_iff₀`).
2. Uniqueness. If `n < n'` both work then `n + 1 ≤ n'`, so
   `c ^ n' * ‖m‖ ≤ c ^ (n + 1) * ‖m‖ = c * (c ^ n * ‖m‖) ≤ c * δ` (`zpow_le_zpow_right_of_le_one₀`), contradicting
   `δ * c < c ^ n' * ‖m‖`. Symmetric for `n' < n`; `lt_trichotomy`.
3. `_one`: `by simpa using ϖ.existsUnique_zpow_norm_smul_mem_Ioc one_pos hm`.

#### Mathlib lemmas needed
`exists_mem_Ioc_zpow`, `one_lt_inv₀`, `zpow_le_zpow_right_of_le_one₀`, `zpow_add_one₀`, `inv_zpow'`, `zpow_neg`, `div_le_iff₀`, `lt_div_iff₀`, `norm_pos_iff`.
#### Sources
[RM] §0.4.2; [Buz07] `buzzard.txt:156, 269` ("We use `ρ` to 'normalise' vectors"; "one can use `ρ` to renormalise elements of `M`"); [JN] Definition 2.1.5 ("using a multiplicative pseudo-uniformizer `ϖ` for what Buzzard calls `ρ`"); decomposition L6.2–L6.3.
#### Generality decision
General shell `Ioc (δ * ‖ϖ‖) δ` — Layer 1 scales into the shell of a continuity modulus; the roadmap's `δ = 1` is the corollary. `NormedAddCommGroup M` (a nonzero vector must have positive norm).

### [T023] The valuation of a pseudo-uniformiser: values
- **Status**: done (2026-09-29) · **File**: `Tate.lean` · **Depends on**: T022 · **Parallel**: yes (independent of T022) · **Type**: lemmas
- **Progress**: 2026-09-29 DONE — proved in Tate.lean; `val_self`/`val_one`/`val_zpow_self` obtain `Nontrivial R` from `NormOneClass.nontrivial` (not an instance); `val_mul` needs no `NormOneClass` (omitted, a weakening); builds, axioms standard.
- **Leaves**: L6.4–L6.5

#### Statement
```lean
@[simp]
theorem val_zero : ϖ.val 0 = ⊤ := by sorry
theorem val_of_ne_zero (hr : r ≠ 0) :
    ϖ.val r = ((Real.log ‖r‖ / Real.log ‖(ϖ : R)‖ : ℝ) : WithTop ℝ) := by sorry
@[simp]
theorem val_eq_top_iff : ϖ.val r = ⊤ ↔ r = 0 := by sorry
@[simp]
theorem val_self : ϖ.val (ϖ : R) = 1 := by sorry
@[simp]
theorem val_one : ϖ.val (1 : R) = 0 := by sorry
@[simp]
theorem val_zpow_self (n : ℤ) : ϖ.val ((ϖ.unit ^ n : Rˣ) : R) = ((n : ℝ) : WithTop ℝ) := by sorry
```
#### Proof sketch
1. `val_zero`: `if_pos rfl`. `val_of_ne_zero`: `if_neg hr`. `val_eq_top_iff`: `by_cases`, `WithTop.coe_ne_top`.
2. `val_self`: `ϖ ≠ 0` (`ϖ.unit.ne_zero` in a nontrivial ring, `NormOneClass.nontrivial`), `val_of_ne_zero`,
   `div_self ϖ.log_norm_neg.ne`, `WithTop.coe_one`.
3. `val_one`: `one_ne_zero`, `norm_one`, `Real.log_one`, `zero_div`, `WithTop.coe_zero`.
4. `val_zpow_self`: `Units.ne_zero`, `ϖ.norm_zpow`, `Real.log_zpow`, `mul_div_assoc`, `div_self`, `mul_one`.
#### Mathlib lemmas needed
`WithTop.coe_ne_top`, `Units.ne_zero`, `NormOneClass.nontrivial`, `Real.log_one`, `Real.log_zpow`, `div_self`.
#### Sources
[JN] Definition 2.1.2 (`jn.txt:489`): "`v_ϖ(r) = −log_a |r|`, where `a = |ϖ⁻¹|`"; [RM] §0.4.3; decomposition L6.4–L6.5.
#### Generality decision
`val` takes values in `WithTop ℝ` with `⊤` exactly at `0` (never junk). `NormOneClass` from `val_self` on.

### [CLEANUP-8] Run /cleanup on `Tate.lean`
- **Status**: done (2026-09-29) · **File**: `Tate.lean` · **Depends on**: T023 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-09-29 DONE — inline cleanup: runLinter clean after removing the `synTaut` lemma `coe_unit` (the coercion unfolds at elaboration; nothing referenced it).
- Per-file cadence (every third proof ticket on the file, and after the last). Inline as the main agent; `lake exe runLinter` on the module; prune imports with `lake exe shake`.

### [T024] The valuation of a pseudo-uniformiser: order and arithmetic
- **Status**: done (2026-09-29) · **File**: `Tate.lean` · **Depends on**: CLEANUP-8 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-09-29 DONE — proved in Tate.lean; `val_self`/`val_one`/`val_zpow_self` obtain `Nontrivial R` from `NormOneClass.nontrivial` (not an instance); `val_mul` needs no `NormOneClass` (omitted, a weakening); builds, axioms standard.
- **Leaves**: L6.6–L6.8

#### Statement
```lean
theorem val_le_val_iff : ϖ.val r ≤ ϖ.val s ↔ ‖s‖ ≤ ‖r‖ := by sorry
theorem val_lt_val_iff : ϖ.val r < ϖ.val s ↔ ‖s‖ < ‖r‖ := by sorry
theorem val_nonneg_iff : 0 ≤ ϖ.val r ↔ ‖r‖ ≤ 1 := by sorry
theorem val_add_val_le_val_mul (r s : R) : ϖ.val r + ϖ.val s ≤ ϖ.val (r * s) := by sorry
theorem val_mul [NormMulClass R] (r s : R) : ϖ.val (r * s) = ϖ.val r + ϖ.val s := by sorry
theorem min_val_le_val_add [IsUltrametricDist R] (r s : R) :
    min (ϖ.val r) (ϖ.val s) ≤ ϖ.val (r + s) := by sorry
theorem norm_eq_rpow_of_val_eq {q : ℝ} (h : ϖ.val r = (q : WithTop ℝ)) :
    ‖r‖ = ‖(ϖ : R)‖ ^ q := by sorry
```
#### Proof sketch
1. `val_le_val_iff`: cases on `r = 0`, `s = 0` (`val_zero`, `top_le_iff`, `val_eq_top_iff`, `norm_le_zero_iff`,
   `le_top`). Both nonzero: `WithTop.coe_le_coe`, `div_le_div_right_of_neg ϖ.log_norm_neg`, `Real.log_le_log_iff`.
2. `val_lt_val_iff`: `lt_iff_not_ge` from step 1. `val_nonneg_iff`: step 1 with `s := 1`… precisely
   `0 = val 1 ≤ val r ↔ ‖r‖ ≤ ‖1‖ = 1` (`val_one`, `norm_one`).
3. `val_add_val_le_val_mul`: if `r * s = 0` the right side is `⊤`. Else `r, s ≠ 0`; `← WithTop.coe_add`, `← add_div`,
   `div_le_div_right_of_neg`, `Real.log_mul`, `Real.log_le_log` from `norm_mul_le`.
4. `val_mul`: `mul_eq_zero` cases (`WithTop.add_top`, `top_add`); otherwise `norm_mul`, `Real.log_mul`, `add_div`.
5. `min_val_le_val_add`: from step 1: `‖r + s‖ ≤ max ‖r‖ ‖s‖` means `val (r+s) ≥ val` of whichever has the larger norm;
   `min_le_iff`, `le_max_iff`.
6. `norm_eq_rpow_of_val_eq`: `r ≠ 0` (else `⊤ = ↑q`); `WithTop.coe_inj`; `Real.rpow_def_of_pos ϖ.norm_pos`,
   `mul_div_cancel₀`… giving `exp (log ‖r‖) = ‖r‖` by `Real.exp_log`.
#### Mathlib lemmas needed
`WithTop.coe_le_coe`, `div_le_div_right_of_neg`, `Real.log_le_log_iff`, `Real.log_mul`, `WithTop.coe_add`, `norm_mul_le`, `norm_mul`, `IsUltrametricDist.norm_add_le_max`, `Real.rpow_def_of_pos`, `Real.exp_log`.
#### Sources
[RM] §0.4.3 ("order-reversing in the norm, `val ϖ (r * s) ≥ val ϖ r + val ϖ s` with equality when the norm is multiplicative, `val ϖ (r + s) ≥ min`, and `‖r‖ = ‖ϖ‖ ^ (val ϖ r)`. ⚠ It is not an `AddValuation`"); decomposition L6.6–L6.8; [SRC] `00_Tate.PseudoUniformizer.val_*`.
#### Generality decision
No bundled structure. `NormMulClass` only for `val_mul`; `IsUltrametricDist` only for `min_val_le_val_add`. The seam with `normAddVal` (E6) is external and not part of this ticket.

### [T025] The bridge from normed algebras over a field
- **Status**: done (2026-09-29) · **File**: `Tate.lean` · **Depends on**: T024 · **Parallel**: yes (independent of T022–T024) · **Type**: def fields + theorem
- **Progress**: 2026-09-29 DONE — proved in Tate.lean; `val_self`/`val_one`/`val_zpow_self` obtain `Nontrivial R` from `NormOneClass.nontrivial` (not an instance); `val_mul` needs no `NormOneClass` (omitted, a weakening); builds, axioms standard.
- **Leaves**: L6.9

#### Statement
```lean
noncomputable def ofNormedAlgebra [NormOneClass R] {c : K} (hc₀ : c ≠ 0) (hc₁ : ‖c‖ < 1) :
    PseudoUniformizer R where
  unit := Units.map (algebraMap K R : K →* R) (Units.mk0 c hc₀)
  isMultiplicative := by
    sorry
  norm_lt_one := by
    sorry
theorem isTate_of_normedAlgebra (K R : Type*) [NontriviallyNormedField K] [NormedRing R]
    [NormedAlgebra K R] [NormOneClass R] : IsTate R := by sorry
```
#### Proof sketch
1. Fill the two `sorry` fields of `ofNormedAlgebra`. `isMultiplicative`: the unit coerces to `algebraMap K R c`
   (`Units.coe_map`, `Units.val_mk0`); `algebraMap K R c * x = c • x` (`Algebra.smul_def`), so `norm_smul` and
   `norm_algebraMap'`. `norm_lt_one`: `norm_algebraMap'` and `hc₁`.
2. `isTate_of_normedAlgebra`: `obtain ⟨c, hc₀, hc₁⟩ := NormedField.exists_norm_lt_one K`;
   `⟨⟨ofNormedAlgebra K (norm_pos_iff.1 hc₀) hc₁⟩⟩`.
3. The field instance is already a term (`isTate_of_normedAlgebra K K`).
#### Mathlib lemmas needed
`Units.coe_map`, `Units.val_mk0`, `Algebra.smul_def`, `norm_smul`, `norm_algebraMap'`, `NormedField.exists_norm_lt_one`, `norm_pos_iff`.
#### Sources
[RM] §0.4.4; [Wed] Example 6.13 (`wedhorn.txt:2170`): "Every normed `k`-algebra `(A, ‖·‖)` is a Tate ring"; decomposition L6.9; [SRC] `00_Tate.isTate_of_normedAlgebra`.
#### Generality decision
`NontriviallyNormedField K`, `NormedAlgebra K R`, `NormOneClass R` (necessary: `‖c • 1‖ = ‖c‖`). A theorem, not an instance (`K` is not determined by `R`); the field case is the instance.

### [CLEANUP-9] Run /cleanup on `Tate.lean`
- **Status**: done (2026-09-29) · **File**: `Tate.lean` · **Depends on**: T025 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-09-29 DONE — inline cleanup: runLinter clean after removing the `synTaut` lemma `coe_unit` (the coercion unfolds at elaboration; nothing referenced it).
- Final per-file cleanup for `Tate.lean`.

### [T026] Johansson–Newton Lemma 2.1.6
- **Status**: done (2026-09-29) · **File**: `NormComparison.lean` · **Depends on**: CLEANUP-9 · **Parallel**: yes (with G8, G9) · **Type**: lemmas
- **Progress**: 2026-09-29 DONE — proved in NormComparison.lean (private helpers `exists_pow_norm_map_le`, `norm_map_lt_one`); the upper bound of 2.1.7 uses the scaling trick with shell radius `D₁ / 2`; builds, axioms standard, runLinter clean.
- **Leaves**: L7.1–L7.2

#### Statement
```lean
theorem exists_norm_le_of_norm_map_le_one (e : R ≃+* S) (he : Continuous e)
    (he' : Continuous e.symm) (ϖ : PseudoUniformizer R) :
    ∃ C : ℝ, ∀ a : R, ‖e a‖ ≤ 1 → ‖a‖ ≤ C := by sorry
theorem exists_norm_le_mul_rpow_norm_map (e : R ≃+* S) (he : Continuous e)
    (he' : Continuous e.symm) (ϖ : PseudoUniformizer R) :
    ∃ C s : ℝ, 0 < s ∧ ∀ a : R, 1 ≤ ‖e a‖ → ‖a‖ ≤ C * ‖e a‖ ^ s := by sorry
```
#### Proof sketch
1. Constants. Continuity of `e.symm` at `0` (`Metric.continuousAt_iff`, `map_zero`) gives `D₁ > 0` with
   `‖y‖ < D₁ → ‖e.symm y‖ < 1`. Put `D := min (D₁ / 2) (1 / 2)`. `‖ϖ ^ k‖ = ‖ϖ‖ ^ k → 0` (T015 `norm_pow`,
   `tendsto_pow_atTop_nhds_zero_of_lt_one`) and `e` is continuous at `0`, so eventually `‖e (ϖ ^ k)‖ ≤ D`; intersect
   with `Filter.eventually_ge_atTop 1` to get such an `m` with `1 ≤ m`. Put `K := ‖ϖ‖⁻¹ ^ m`, so `1 < K`
   (`one_lt_inv₀`, `one_lt_pow₀`).
2. First lemma, `C := K`. If `‖e a‖ ≤ 1` then `‖e (ϖ ^ m * a)‖ ≤ ‖e (ϖ ^ m)‖ * ‖e a‖ ≤ D < D₁`, so
   `‖ϖ ^ m * a‖ < 1` (step 1 at `y := e (ϖ ^ m * a)`, `e.symm_apply_apply`); and `‖ϖ ^ m * a‖ = ‖ϖ‖ ^ m * ‖a‖`
   (T015 `norm_pow_mul`), whence `‖a‖ ≤ K`.
3. Second lemma, `s := Real.log K / Real.log 2 > 0` and `C := K * K`. Let `1 ≤ ‖e a‖`,
   `x := Real.log ‖e a‖ / Real.log 2 ≥ 0`, `n := ⌈x⌉₊`. Then `(1 / 2) ^ n * ‖e a‖ ≤ 1` (`Nat.le_ceil`), so
   `‖e (ϖ ^ (m * n) * a)‖ ≤ ‖e (ϖ ^ m)‖ ^ n * ‖e a‖ ≤ 1` (`pow_mul`, `map_pow`, `map_mul`, `norm_mul_le`,
   `norm_pow_le'` for `0 < n`; for `n = 0` the claim is `‖e a‖ ≤ 1`, which holds since then `x = 0`). Step 2 applied
   to `ϖ ^ (m * n) * a` gives `‖ϖ‖ ^ (m * n) * ‖a‖ ≤ K`, i.e. `‖a‖ ≤ K * K ^ n`. Finally `n < x + 1`
   (`Nat.ceil_lt_add_one`), so `K ^ n ≤ K ^ (x + 1) = K * K ^ x` (`Real.rpow_natCast`,
   `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_add`) and `K ^ x = ‖e a‖ ^ s` (both are
   `exp (log K * log ‖e a‖ / log 2)`, `Real.rpow_def_of_pos`).

#### Mathlib lemmas needed
`Metric.continuousAt_iff`, `Continuous.tendsto`, `tendsto_pow_atTop_nhds_zero_of_lt_one`, `Filter.eventually_ge_atTop`, `one_lt_inv₀`, `one_lt_pow₀`, `map_pow`, `RingEquiv.symm_apply_apply`, `norm_mul_le`, `norm_pow_le'`, `Nat.ceil_lt_add_one`, `Nat.le_ceil`, `Real.rpow_natCast`, `Real.rpow_add`, `Real.rpow_def_of_pos`, `Real.rpow_le_rpow_of_exponent_le`.
#### Sources
[JN] Lemma 2.1.6 and its proof, `jn.txt:565–600`, read in full (decomposition §0.3.2 substrate); ⚠ the *published* statement is incorrect, this is the corrected v4 form; [SRC] `08_BaseChange.norm_le_pow_of_equiv`.
#### Generality decision
Split into its two inequalities (one conclusion each); the second pseudo-uniformiser `π` of [JN]/[SRC] is **dropped** — the proof never uses it. First bound stated for `‖e a‖ ≤ 1`, as proved (stronger than `< 1`). `NormedRing`, not commutative.

### [T027] Johansson–Newton Lemma 2.1.7
- **Status**: done (2026-09-29) · **File**: `NormComparison.lean` · **Depends on**: T026 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-09-29 DONE — proved in NormComparison.lean (private helpers `exists_pow_norm_map_le`, `norm_map_lt_one`); the upper bound of 2.1.7 uses the scaling trick with shell radius `D₁ / 2`; builds, axioms standard, runLinter clean.
- **Leaves**: L7.3–L7.5

#### Statement
```lean
theorem logb_norm_map_pos (e : R →+* S) (he : Continuous e) (ϖ : PseudoUniformizer R)
    (hϖ : IsMultiplicative (e (ϖ : R))) : 0 < Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖ := by sorry
theorem exists_norm_map_le_mul_rpow (e : R →+* S) (he : Continuous e) (ϖ : PseudoUniformizer R)
    (hϖ : IsMultiplicative (e (ϖ : R))) :
    ∃ C : ℝ, ∀ a : R, ‖e a‖ ≤ C * ‖a‖ ^ Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖ := by sorry
theorem exists_mul_rpow_le_norm_map (e : R ≃+* S) (he : Continuous e) (he' : Continuous e.symm)
    (ϖ : PseudoUniformizer R) (hϖ : IsMultiplicative (e (ϖ : R))) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : R, C * ‖a‖ ^ Real.logb ‖(ϖ : R)‖ ‖e (ϖ : R)‖ ≤ ‖e a‖ := by sorry
```
#### Proof sketch
1. `logb_norm_map_pos`: `Real.logb_pos_iff_of_base_lt_one ϖ.norm_pos ϖ.norm_lt_one` reduces to `0 < ‖e ϖ‖ < 1`.
   Positivity: T016 `norm_pos` for the unit `Units.map (e : R →* S) ϖ.unit` of `S`. `< 1`:
   `‖e ϖ‖ ^ k = ‖e (ϖ ^ k)‖` (T015 `norm_pow` in `S`, `map_pow`) tends to `0` (`he.tendsto 0` composed with
   `‖ϖ ^ k‖ → 0`), so `‖e ϖ‖ < 1` (`tendsto_pow_atTop_nhds_zero_iff`). Keep `‖e ϖ‖ < 1` as a private helper: step 3
   needs it.
2. `exists_norm_map_le_mul_rpow`: put `s := logb ‖ϖ‖ ‖e ϖ‖`, so `‖e ϖ‖ = ‖ϖ‖ ^ s` (`Real.rpow_logb`). Continuity
   of `e` at `0` gives `D > 0` with `‖a‖ ≤ D → ‖e a‖ ≤ 1`. Take `C := (D * ‖ϖ‖) ^ (-s)`. For `a = 0`: `map_zero`,
   `Real.zero_rpow (step 1).ne'`. For `a ≠ 0` apply the **scaling trick T022** to `R` as a module over itself
   (`smul_eq_mul`) with shell radius `D`: some `n : ℤ` has `D * ‖ϖ‖ < ‖ϖ‖ ^ n * ‖a‖ ≤ D`. The upper bound gives
   `‖e (ϖ ^ n * a)‖ ≤ 1`; and `‖e (ϖ ^ n * a)‖ = ‖e ϖ‖ ^ n * ‖e a‖` by T016 (`zpow`, `norm_zpow`) for the
   multiplicative unit `Units.map e ϖ.unit` (`map_mul`, `map_zpow`, `Units.coe_map`). Hence
   `‖e a‖ ≤ ‖e ϖ‖ ^ (-n) = (‖ϖ‖ ^ (-n)) ^ s`, and the lower bound gives `‖ϖ‖ ^ (-n) < ‖a‖ / (D * ‖ϖ‖)`; conclude with
   `Real.rpow_le_rpow`, `Real.mul_rpow`, `Real.rpow_neg`.
3. `exists_mul_rpow_le_norm_map`: apply step 2 to `e.symm` with the pseudo-uniformiser
   `⟨Units.map e ϖ.unit, hϖ, step 1⟩` of `S` (its image under `e.symm` is `ϖ`, multiplicative by
   `ϖ.isMultiplicative`); its exponent is `logb ‖e ϖ‖ ‖ϖ‖ = s⁻¹` (`Real.inv_logb`). From
   `‖a‖ ≤ C' * ‖e a‖ ^ s⁻¹` raise to the power `s > 0` (`Real.rpow_le_rpow`, `Real.mul_rpow`,
   `Real.rpow_inv_rpow`) and take `C := (max C' 1) ^ (-s)`.

#### Mathlib lemmas needed
`Real.logb_pos_iff_of_base_lt_one`, `Real.rpow_logb`, `Real.inv_logb`, `Real.rpow_le_rpow`, `Real.mul_rpow`, `Real.rpow_neg`, `Real.rpow_inv_rpow`, `Real.zero_rpow`, `tendsto_pow_atTop_nhds_zero_iff`, `Units.map`, `Units.coe_map`, `map_zpow`, `Metric.continuousAt_iff`; T015, T016, T022.
#### Sources
[JN] Lemma 2.1.7 and its proof, `jn.txt:605–640` ("`C₁|a|₁^s ≤ |a|₂ ≤ C₂|a|₁^s` … where `s` is determined by `|ϖ|₂ = |ϖ|₁^s` … Swapping `|−|₁` and `|−|₂` we get a similar inequality"); [SRC] `08_BaseChange.norm_comparison_of_common_uniformizer`; decomposition L7.3–L7.5.
#### Generality decision
The upper bound for a continuous ring **homomorphism** (bijectivity unused); `‖e ϖ‖ < 1` **derived** rather than assumed; the exponent explicit (`Real.logb`), so each lemma has one conclusion. `NormOneClass` on both rings.

### [CLEANUP-10] Run /cleanup on `NormComparison.lean`
- **Status**: done (2026-09-29) · **File**: `NormComparison.lean` · **Depends on**: T027 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-09-29 DONE — inline cleanup: runLinter clean; unused `NormOneClass R` omitted on the private helpers.
- Final per-file cleanup for `NormComparison.lean`.

### [T028] `Real.zpowCeil`: the closed form
- **Status**: done (2026-09-29) · **File**: `Rescale.lean` · **Depends on**: none · **Parallel**: yes (pure real analysis) · **Type**: lemmas
- **Progress**: 2026-09-29 DONE — proved in Rescale.lean (private helpers `bddBelow_zpowCeil_set`, `le_zpow_iff`, `ofRescaled`, `norm_rescaled`); the `NormedAddCommGroup (Rescaled ϖ M)` instance body is now `@AddGroupNorm.toNormedAddCommGroup (Rescaled ϖ M) _ (rescaledNorm ϖ M)` so that its group structure is the synonym's own (instance search for `Module R (Rescaled ϖ M)` failed otherwise); builds, axioms standard, runLinter clean.
- **Leaves**: L8.1

#### Statement
```lean
theorem zpowCeil_nonneg (hc₀ : 0 < c) : 0 ≤ zpowCeil c x := by sorry
theorem zpowCeil_of_nonpos (hc₀ : 0 < c) (hc₁ : c < 1) (hx : x ≤ 0) : zpowCeil c x = 0 := by sorry
theorem zpowCeil_of_pos (hc₀ : 0 < c) (hc₁ : c < 1) (hx : 0 < x) :
    zpowCeil c x = c ^ ⌊logb c x⌋ := by sorry
theorem le_zpowCeil (hc₀ : 0 < c) (hc₁ : c < 1) : x ≤ zpowCeil c x := by sorry
theorem mul_zpowCeil_lt (hc₀ : 0 < c) (hc₁ : c < 1) (hx : 0 < x) : c * zpowCeil c x < x := by sorry
theorem zpowCeil_le_of_le_zpow (hc₀ : 0 < c) {n : ℤ} (h : x ≤ c ^ n) : zpowCeil c x ≤ c ^ n := by sorry
```
#### Proof sketch
Write `S x := {y | ∃ n : ℤ, y = c ^ n ∧ x ≤ c ^ n}`. Every element of `S x` is `≥ 0` (`zpow_nonneg hc₀.le`), so
`S x` is bounded below by `0`. Prove in this order (reorder the file if convenient):
1. `zpowCeil_nonneg`: `Real.sInf_nonneg` with the remark above.
2. `zpowCeil_le_of_le_zpow`: `csInf_le ⟨0, _⟩ ⟨n, rfl, h⟩`.
3. The membership equivalence, as a private helper: for `0 < x`, `x ≤ c ^ n ↔ n ≤ ⌊logb c x⌋`.
   `x = c ^ logb c x` (`Real.rpow_logb hc₀ hc₁.ne hx`), `c ^ n = c ^ (n : ℝ)` (`Real.rpow_intCast`),
   `Real.rpow_le_rpow_left_iff_of_base_lt_one hc₀ hc₁`, then `Int.le_floor`.
4. `zpowCeil_of_pos`: `IsLeast.csInf_eq`. `c ^ N ∈ S x` for `N := ⌊logb c x⌋` by step 3 (`le_rfl`); it is a lower
   bound because `n ≤ N` gives `c ^ N ≤ c ^ n` (`zpow_le_zpow_right_of_le_one₀ hc₀ hc₁.le`).
5. `zpowCeil_of_nonpos`: every `n` qualifies (`x ≤ 0 ≤ c ^ n`). `le_antisymm _ (zpowCeil_nonneg hc₀)`; for `ε > 0`
   pick `k : ℕ` with `c ^ k < ε` (`exists_pow_lt_of_lt_one`), so `sInf ≤ c ^ k < ε` by step 2; `le_of_forall_pos_lt_add`
   closes it.
6. `le_zpowCeil`: `x ≤ 0` → step 1; `0 < x` → step 4 and step 3 (`le_rfl`).
7. `mul_zpowCeil_lt`: step 4; `c * c ^ N = c ^ (N + 1)` (`zpow_add_one₀ hc₀.ne'`, `mul_comm`); `¬ x ≤ c ^ (N + 1)` by
   step 3 since `¬ N + 1 ≤ N`; `not_le`.
⚠ `Real.logb_zpow` does not exist (decomposition L8.1): stay with `rpow` + `Real.rpow_intCast`.
#### Mathlib lemmas needed
`Real.sInf_nonneg`, `csInf_le`, `IsLeast.csInf_eq`, `Real.rpow_logb`, `Real.rpow_intCast`, `Real.rpow_le_rpow_left_iff_of_base_lt_one`, `Int.le_floor`, `Int.lt_floor_add_one`, `zpow_le_zpow_right_of_le_one₀`, `zpow_add_one₀`, `exists_pow_lt_of_lt_one`, `le_of_forall_pos_lt_add`.
#### Sources
[Sch] proof of Prop 10.1 (`schneider.txt:2953`): "replace a given defining norm `‖ ‖′` by the norm `‖v‖ := inf {s ∈ |K| : s ≥ ‖v‖′}` which, because of `r ≤ ‖v‖′/‖v‖ ≤ 1`, defines the same topology"; [Bel] proof of Thm II.1.13 (`bellaiche.txt:2109`); decomposition L8.1.
#### Generality decision
A function on `ℝ`, independent of any ring. The lower inequality is **strict** (`c * zpowCeil c x < x`), stronger than [Sch]. `zpowCeil_nonneg` and `zpowCeil_le_of_le_zpow` need only `0 < c`.

### [T029] `Real.zpowCeil`: algebra
- **Status**: done (2026-09-29) · **File**: `Rescale.lean` · **Depends on**: T028 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-09-29 DONE — proved in Rescale.lean (private helpers `bddBelow_zpowCeil_set`, `le_zpow_iff`, `ofRescaled`, `norm_rescaled`); the `NormedAddCommGroup (Rescaled ϖ M)` instance body is now `@AddGroupNorm.toNormedAddCommGroup (Rescaled ϖ M) _ (rescaledNorm ϖ M)` so that its group structure is the synonym's own (instance search for `Module R (Rescaled ϖ M)` failed otherwise); builds, axioms standard, runLinter clean.
- **Leaves**: L8.2

#### Statement
```lean
theorem exists_zpowCeil_eq_zpow (hc₀ : 0 < c) (hc₁ : c < 1) (hx : 0 < x) :
    ∃ n : ℤ, zpowCeil c x = c ^ n := by sorry
@[simp]
theorem zpowCeil_zpow (hc₀ : 0 < c) (hc₁ : c < 1) (n : ℤ) : zpowCeil c (c ^ n) = c ^ n := by sorry
theorem zpowCeil_pos (hc₀ : 0 < c) (hc₁ : c < 1) (hx : 0 < x) : 0 < zpowCeil c x := by sorry
theorem zpowCeil_eq_zero_iff (hc₀ : 0 < c) (hc₁ : c < 1) : zpowCeil c x = 0 ↔ x ≤ 0 := by sorry
theorem zpowCeil_mono (hc₀ : 0 < c) (hc₁ : c < 1) : Monotone (zpowCeil c) := by sorry
theorem zpowCeil_max (hc₀ : 0 < c) (hc₁ : c < 1) (x y : ℝ) :
    zpowCeil c (max x y) = max (zpowCeil c x) (zpowCeil c y) := by sorry
theorem zpowCeil_zpow_mul (hc₀ : 0 < c) (hc₁ : c < 1) (n : ℤ) (x : ℝ) :
    zpowCeil c (c ^ n * x) = c ^ n * zpowCeil c x := by sorry
theorem zpowCeil_mul_le (hc₀ : 0 < c) (hc₁ : c < 1) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    zpowCeil c (x * y) ≤ zpowCeil c x * zpowCeil c y := by sorry
```
#### Proof sketch
No logarithms are needed beyond T028: use *minimality* (`zpowCeil_le_of_le_zpow`) and `le_zpowCeil`.
1. `exists_zpowCeil_eq_zpow`: `⟨_, zpowCeil_of_pos hc₀ hc₁ hx⟩`.
2. `zpowCeil_zpow`: `le_antisymm (zpowCeil_le_of_le_zpow hc₀ le_rfl) (le_zpowCeil hc₀ hc₁)`.
3. `zpowCeil_pos`: step 1 and `zpow_pos hc₀`. `zpowCeil_eq_zero_iff`: `⇐` is `zpowCeil_of_nonpos`; `⇒` by contraposition
   from `zpowCeil_pos`.
4. `zpowCeil_mono`: let `x ≤ y`. If `y ≤ 0`, both sides are `0`. Otherwise `zpowCeil c y = c ^ N` with `y ≤ c ^ N`
   (step 1 + `le_zpowCeil`), so `x ≤ c ^ N` and minimality applies.
5. `zpowCeil_max`: `(zpowCeil_mono hc₀ hc₁).map_max`.
6. `zpowCeil_zpow_mul`: if `x ≤ 0` both sides vanish (`mul_nonpos_of_nonneg_of_nonpos`, `mul_zero`). If `0 < x`:
   `≤` by minimality at `c ^ n * c ^ N = c ^ (n + N)` (`zpow_add₀`), since `c ^ n * x ≤ c ^ n * c ^ N`; `≥` is the same
   inequality for `-n` and `c ^ n * x`, multiplied back by `c ^ n` (`zpow_neg`, `inv_mul_cancel_left₀`).
7. `zpowCeil_mul_le`: if `x = 0` or `y = 0` the left side is `zpowCeil c 0 = 0`. Otherwise `x ≤ c ^ N`, `y ≤ c ^ M`,
   `x * y ≤ c ^ (N + M)` (`mul_le_mul`), minimality.
⚠ `zpowCeil` is **not subadditive** (`c = 1/2`: `zpowCeil c 0.51 = 1 > 1/2 + 1/64`); do not try to prove
`zpowCeil c (x + y) ≤ …`. Only `max` is preserved.
#### Mathlib lemmas needed
`Monotone.map_max`, `zpow_pos`, `zpow_add₀`, `zpow_neg`, `mul_le_mul`, `mul_le_mul_of_nonneg_left`, `inv_mul_cancel_left₀`.
#### Sources
[RM] §0.3.3; [Bel] proof of Lemma II.1.12 (`bellaiche.txt:2087`, `|πm| = |π||m|`); decomposition L8.2 (with the non-subadditivity attack).
#### Generality decision
All for `0 < c < 1`; `zpowCeil_mul_le` for nonnegative arguments only (that is all a norm supplies).

### [T030] The rescaled norm
- **Status**: done (2026-09-29) · **File**: `Rescale.lean` · **Depends on**: T029, CLEANUP-9 · **Parallel**: no · **Type**: def fields + lemmas
- **Progress**: 2026-09-29 DONE — proved in Rescale.lean (private helpers `bddBelow_zpowCeil_set`, `le_zpow_iff`, `ofRescaled`, `norm_rescaled`); the `NormedAddCommGroup (Rescaled ϖ M)` instance body is now `@AddGroupNorm.toNormedAddCommGroup (Rescaled ϖ M) _ (rescaledNorm ϖ M)` so that its group structure is the synonym's own (instance search for `Module R (Rescaled ϖ M)` failed otherwise); builds, axioms standard, runLinter clean.
- **Leaves**: L8.3

#### Statement
```lean
@[nolint unusedArguments]
noncomputable def rescaledNorm [NormOneClass R] [IsUltrametricDist M] : AddGroupNorm M where
  toFun m := Real.zpowCeil ‖(ϖ : R)‖ ‖m‖
  map_zero' := by
    sorry
  add_le' m n := by
    sorry
  neg' m := by
    sorry
  eq_zero_of_map_eq_zero' m hm := by
    sorry
theorem norm_toRescaled [Module R M] (m : M) :
    ‖toRescaled ϖ M m‖ = Real.zpowCeil ‖(ϖ : R)‖ ‖m‖ := rfl
theorem norm_le_norm_toRescaled [Module R M] (m : M) : ‖m‖ ≤ ‖toRescaled ϖ M m‖ := by sorry
theorem norm_mul_norm_toRescaled_lt [Module R M] {m : M} (hm : m ≠ 0) :
    ‖(ϖ : R)‖ * ‖toRescaled ϖ M m‖ < ‖m‖ := by sorry
theorem exists_norm_rescaled_eq_zpow {m : Rescaled ϖ M} (hm : m ≠ 0) :
    ∃ n : ℤ, ‖m‖ = ‖(ϖ : R)‖ ^ n := by sorry
theorem norm_toRescaled_eq_of_forall_exists_zpow [Module R M]
    (h : ∀ m : M, m ≠ 0 → ∃ n : ℤ, ‖m‖ = ‖(ϖ : R)‖ ^ n) (m : M) : ‖toRescaled ϖ M m‖ = ‖m‖ := by sorry
```
#### Proof sketch
Put `c := ‖(ϖ : R)‖`, with `hc₀ := ϖ.norm_pos` and `hc₁ := ϖ.norm_lt_one` (T021).
1. The four `sorry` fields of `rescaledNorm`. `map_zero'`: `norm_zero`, `Real.zpowCeil_of_nonpos hc₀ hc₁ le_rfl`.
   `add_le'`: `(Real.zpowCeil_mono hc₀ hc₁ (IsUltrametricDist.norm_add_le_max m n)).trans`, rewrite by
   `Real.zpowCeil_max`, then `max_le_add_of_nonneg` with `Real.zpowCeil_nonneg`. `neg'`: `norm_neg`.
   `eq_zero_of_map_eq_zero'`: `(Real.zpowCeil_eq_zero_iff hc₀ hc₁).1 hm`, `norm_le_zero_iff`.
2. `norm_toRescaled` is already `rfl` — it is the unfolding lemma for everything below.
3. `norm_le_norm_toRescaled`: `Real.le_zpowCeil`. `norm_mul_norm_toRescaled_lt`: `Real.mul_zpowCeil_lt` with
   `norm_pos_iff.2 hm`.
4. `exists_norm_rescaled_eq_zpow`: `change ∃ n : ℤ, Real.zpowCeil _ ‖(m : M)‖ = _`, then
   `Real.exists_zpowCeil_eq_zpow` with `norm_pos_iff.2 hm` (the `hm` of `Rescaled ϖ M` is the `hm` of `M`: same type).
5. `norm_toRescaled_eq_of_forall_exists_zpow`: `m = 0` → both sides `0` (`map_zero`, `norm_zero`); otherwise
   `‖m‖ = c ^ n` and `Real.zpowCeil_zpow`.
#### Mathlib lemmas needed
`IsUltrametricDist.norm_add_le_max`, `max_le_add_of_nonneg`, `norm_le_zero_iff`, `norm_pos_iff`, `AddGroupNorm.toNormedAddCommGroup`.
#### Sources
[RM] §0.3.3 ("a norm taking values in `‖π‖ ^ ℤ ∪ {0}`, ultrametric, with `‖π‖ ‖m‖' < ‖m‖ ≤ ‖m‖'`"); [Sch] proof of Prop 10.1; [Col10] `colmez.txt:129`; decomposition L8.3.
#### Generality decision
The rescaled norm lives on the **type synonym** `Rescaled ϖ M` (plan decision 5), never as a second norm on `M`. `[IsUltrametricDist M]` is necessary (T029's warning); `[NormOneClass R]` gives `0 < ‖ϖ‖`.

### [CLEANUP-11] Run /cleanup on `Rescale.lean`
- **Status**: done (2026-09-29) · **File**: `Rescale.lean` · **Depends on**: T030 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-09-29 DONE — inline cleanup: runLinter clean; elaboration 12 s.
- Per-file cadence (every third proof ticket on the file, and after the last). Inline as the main agent; `lake exe runLinter` on the module; prune imports with `lake exe shake`.

### [T031] The rescaled module
- **Status**: done (2026-09-29) · **File**: `Rescale.lean` · **Depends on**: CLEANUP-11, CLEANUP-7 · **Parallel**: no · **Type**: instances + lemmas
- **Progress**: 2026-09-29 DONE — proved in Rescale.lean (private helpers `bddBelow_zpowCeil_set`, `le_zpow_iff`, `ofRescaled`, `norm_rescaled`); the `NormedAddCommGroup (Rescaled ϖ M)` instance body is now `@AddGroupNorm.toNormedAddCommGroup (Rescaled ϖ M) _ (rescaledNorm ϖ M)` so that its group structure is the synonym's own (instance search for `Module R (Rescaled ϖ M)` failed otherwise); builds, axioms standard, runLinter clean.
- **Leaves**: L8.4–L8.5

#### Statement
```lean
instance : IsUltrametricDist (Rescaled ϖ M) := by sorry
instance [CompleteSpace M] : CompleteSpace (Rescaled ϖ M) := by sorry
theorem norm_smul_rescaled (m : Rescaled ϖ M) : ‖(ϖ : R) • m‖ = ‖(ϖ : R)‖ * ‖m‖ := by sorry
theorem isBoundedSMul_rescaled (h : ∀ r : R, r ≠ 0 → ∃ n : ℤ, ‖r‖ = ‖(ϖ : R)‖ ^ n) :
    IsBoundedSMul R (Rescaled ϖ M) := by sorry
```
#### Proof sketch
1. `IsUltrametricDist`: `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`; the inequality is
   `Real.zpowCeil_mono` applied to `norm_add_le_max`, rewritten by `Real.zpowCeil_max` (first half of T030 `add_le'`).
2. `CompleteSpace`: T020 with `e : M ≃+ Rescaled ϖ M := AddEquiv.refl M` (no module structure is available here),
   `C := ‖ϖ‖⁻¹` (from `‖ϖ‖ * zpowCeil < ‖m‖` for `m ≠ 0`, trivial at `0`; `le_inv_mul_iff₀`) and `C' := 1`
   (`Real.le_zpowCeil`); conclude with `(AddEquiv.completeSpace_congr_of_bounds e h h').1 inferInstance`.
3. `norm_smul_rescaled`: unfold the norm (`change`), `ϖ.norm_smul` (T021) on the underlying `M`, then
   `Real.zpowCeil_zpow_mul hc₀ hc₁ 1` with `zpow_one`.
4. `isBoundedSMul_rescaled`: `IsBoundedSMul.of_norm_smul_le`. For `r = 0`: `zero_smul`, `norm_zero`. For `m = 0`
   likewise. Otherwise `‖r‖ = c ^ k` by `h`, the rescaled norm of `m` is `c ^ N` (T030 step 4), and
   `‖r • m‖ ≤ ‖r‖ * ‖m‖ ≤ c ^ k * c ^ N = c ^ (k + N)` on `M` (`norm_smul_le`, `Real.le_zpowCeil`), so minimality
   (`Real.zpowCeil_le_of_le_zpow`) gives the bound.
#### Mathlib lemmas needed
`IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`, `AddEquiv.refl`, `le_inv_mul_iff₀`, `IsBoundedSMul.of_norm_smul_le`, `norm_smul_le`, `zpow_add₀`, `zpow_one`; T020, T021.
#### Sources
[RM] §0.3.3 ("complete when the original is, and with `‖π • m‖' = ‖π‖ ‖m‖'`"); [Bel] Hypothesis II.1.11 (`bellaiche.txt:2076`): "the set of non-zero norms `|R*|` is the discrete subgroup `|π|^ℤ`"; decomposition L8.4–L8.5.
#### Generality decision
**Erratum E3**: `isBoundedSMul_rescaled` is a theorem under the value-group hypothesis, not an instance — without it the statement is false (`R = M = ℂ_p`, `‖r‖ = p^{-1/2}`: `‖r • 1‖' = 1 > ‖r‖ ‖1‖'`).

### [CLEANUP-12] Run /cleanup on `Rescale.lean`
- **Status**: done (2026-09-29) · **File**: `Rescale.lean` · **Depends on**: T031 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-09-29 DONE — inline cleanup: runLinter clean; elaboration 12 s.
- Final per-file cleanup for `Rescale.lean`.

### [T032] The unit ball of a module and the ideal `(ϖ)`
- **Status**: done (2026-09-29) · **File**: `Residue.lean` · **Depends on**: CLEANUP-4, CLEANUP-9 · **Parallel**: yes (with G7, G8) · **Type**: def fields + lemmas
- **Progress**: 2026-09-29 DONE — proved in Residue.lean (private helper `zpow_le_self_of_lt_one`); builds, axioms standard, runLinter clean.
- **Leaves**: L9.1–L9.3

#### Statement
```lean
def unitClosedBall : Submodule (Subring.unitClosedBall R) M where
  carrier := {m | ‖m‖ ≤ 1}
  add_mem' {m n} hm hn := by
    sorry
  zero_mem' := by simp
  smul_mem' r m hm := by
    sorry
@[simp]
theorem mem_unitClosedBall {m : M} : m ∈ unitClosedBall R M ↔ ‖m‖ ≤ 1 := by sorry
theorem toUnitClosedBall_mem_ideal : ϖ.toUnitClosedBall ∈ ϖ.ideal := by sorry
theorem mem_ideal_iff {a : unitClosedBall R} : a ∈ ϖ.ideal ↔ ‖(a : R)‖ ≤ ‖(ϖ : R)‖ := by sorry
theorem ideal_eq_closedBallIdeal : ϖ.ideal = closedBallIdeal R ‖(ϖ : R)‖₊ := by sorry
theorem ideal_le_openUnitBallIdeal : ϖ.ideal ≤ openUnitBallIdeal R := by sorry
theorem ideal_eq_openUnitBallIdeal (h : ∀ r : R, r ≠ 0 → ∃ n : ℤ, ‖r‖ = ‖(ϖ : R)‖ ^ n) :
    ϖ.ideal = openUnitBallIdeal R := by sorry
```
#### Proof sketch
1. Fields of `Submodule.unitClosedBall`. `add_mem'`: `(IsUltrametricDist.norm_add_le_max m n).trans (max_le hm hn)`.
   `smul_mem'`: `Subring.smul_def`, `(norm_smul_le (r : R) m).trans (mul_le_one₀ _ (norm_nonneg m) hm)` with
   `Subring.mem_unitClosedBall.1 r.2`. `mem_unitClosedBall`: `Iff.rfl`.
2. `toUnitClosedBall_mem_ideal`: `Ideal.mem_span_singleton_self _`.
3. `mem_ideal_iff`: `Ideal.mem_span_singleton'` (`∃ b, b * ϖ = a`). `⇒`: `‖b * ϖ‖ ≤ ‖b‖ * ‖ϖ‖ ≤ ‖ϖ‖`. `⇐`: take
   `b := ⟨(ϖ.unit⁻¹ : Rˣ) * a, _⟩`; its norm is `‖ϖ‖⁻¹ * ‖a‖ ≤ 1` by T016 (`ϖ.isMultiplicative.inv`, `.norm_inv`)
   and `inv_mul_le_one₀`; `Subtype.ext`, `mul_right_comm`/`mul_comm`, `Units.inv_mul`.
4. `ideal_eq_closedBallIdeal`: `Ideal.ext`; step 3, `mem_closedBallIdeal`, `coe_nnnorm`.
   `ideal_le_openUnitBallIdeal`: step 3, `mem_openUnitBallIdeal`, `lt_of_le_of_lt _ ϖ.norm_lt_one`.
5. `ideal_eq_openUnitBallIdeal`: `le_antisymm` with step 4. Given `‖a‖ < 1`: `a = 0` → `zero_mem`; otherwise
   `‖a‖ = ‖ϖ‖ ^ n < 1` forces `0 < n` (`zpow_lt_one_iff_right_of_lt_one₀`), so `‖ϖ‖ ^ n ≤ ‖ϖ‖ ^ 1`
   (`zpow_le_zpow_right_of_le_one₀`, `zpow_one`), and step 3 applies.
#### Mathlib lemmas needed
`Subring.smul_def`, `mul_le_one₀`, `Ideal.mem_span_singleton'`, `Ideal.mem_span_singleton_self`, `Units.inv_mul`, `coe_nnnorm`, `zpow_lt_one_iff_right_of_lt_one₀`, `zpow_le_zpow_right_of_le_one₀`; T007 (`mem_closedBallIdeal`, `mem_openUnitBallIdeal`), T016.
#### Sources
[Bel] §II.1.4 (`bellaiche.txt:2078`): "`M⁰ = {m ∈ M, |m| ≤ 1}`, which is an `R⁰`-submodule of `M`"; [Sch] proof of Prop 10.1: "Since `m · B₁(0) ⊆ B₁⁻(0)` …"; [RM] §0.3.4, §0.4.5 at `n = 1`; decomposition L9.1–L9.3.
#### Generality decision
`M⁰` for seminormed rings and modules, no commutativity. The ideal lemmas need `NormedCommRing` (ideals of `R⁰`) and the **multiplicativity** of `ϖ` (a non-multiplicative unit of norm `< 1` can have `‖u⁻¹ a‖ > 1`). Discreteness is a hypothesis of the one lemma that needs it.

### [T033] The residue module: `ϖ M⁰` is a ball
- **Status**: done (2026-09-29) · **File**: `Residue.lean` · **Depends on**: T032 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-09-29 DONE — proved in Residue.lean (private helper `zpow_le_self_of_lt_one`); builds, axioms standard, runLinter clean.
- **Leaves**: L9.5–L9.6

#### Statement
```lean
theorem mem_ideal_smul_top_iff {m : Submodule.unitClosedBall R M} :
    m ∈ (ϖ.ideal • ⊤ : Submodule (unitClosedBall R) (Submodule.unitClosedBall R M)) ↔
      ‖(m : M)‖ ≤ ‖(ϖ : R)‖ := by sorry
theorem mem_ideal_smul_top_iff_norm_lt_one
    (h : ∀ m : M, m ≠ 0 → ∃ n : ℤ, ‖m‖ = ‖(ϖ : R)‖ ^ n) {m : Submodule.unitClosedBall R M} :
    m ∈ (ϖ.ideal • ⊤ : Submodule (unitClosedBall R) (Submodule.unitClosedBall R M)) ↔
      ‖(m : M)‖ < 1 := by sorry
```
#### Proof sketch
1. `mem_ideal_smul_top_iff`, `⇒`: `Submodule.smul_induction_on`. Generator `r • n` with `r ∈ ϖ.ideal`:
   `‖r • n‖ ≤ ‖r‖ * ‖n‖ ≤ ‖ϖ‖ * 1` (T032 step 3, `Submodule.mem_unitClosedBall`). Sums: `norm_add_le_max`, `max_le`.
   `⇐`: `n := ⟨(ϖ.unit⁻¹ : Rˣ) • (m : M), _⟩ ∈ M⁰` since `‖ϖ⁻¹ • m‖ = ‖ϖ‖⁻¹ * ‖m‖ ≤ 1` (T017 for `ϖ.unit⁻¹`, via T016
   `inv`/`norm_inv`); then `m = ϖ.toUnitClosedBall • n` (`Subtype.ext`, `smul_smul`, `Units.mul_inv`, `one_smul`) and
   `Submodule.smul_mem_smul ϖ.toUnitClosedBall_mem_ideal Submodule.mem_top`.
2. `mem_ideal_smul_top_iff_norm_lt_one`: rewrite by step 1; `‖m‖ ≤ ‖ϖ‖ ↔ ‖m‖ < 1`. `⇒`: `ϖ.norm_lt_one`. `⇐`: `m = 0`
   trivial; otherwise `‖m‖ = ‖ϖ‖ ^ n < 1` forces `1 ≤ n`, exactly as in T032 step 5.
The `Module ϖ.ResidueRing (ϖ.ResidueModule M)` instance is found by `inferInstance` (checked in the skeleton;
it needs `Mathlib.Algebra.Module.Torsion.Basic`) — nothing to prove there.
#### Mathlib lemmas needed
`Submodule.smul_induction_on`, `Submodule.smul_mem_smul`, `Submodule.mem_top`, `smul_smul`, `Units.mul_inv`, `one_smul`, `norm_smul_le`, `zpow_lt_one_iff_right_of_lt_one₀`; T016, T017.
#### Sources
[Bel] §II.1.4 (`bellaiche.txt:2078`): "`M̃ = M⁰/πM⁰`, which is a `R̃`-module"; [RM] §0.3.4 ("if the norm of `M` takes values in `‖π‖ ^ ℤ ∪ {0}` then `π M⁰ = {m | ‖m‖ < 1}`"); [Bel] Lemma II.1.12 (`|M| ⊂ |R|`); decomposition L9.5–L9.6.
#### Generality decision
`ϖ M⁰ = {‖m‖ ≤ ‖ϖ‖}` holds for **every** normed module; the open-ball form carries the value hypothesis (necessary: `ℂ_p`, T042).

### [CLEANUP-13] Run /cleanup on `Residue.lean`
- **Status**: done (2026-09-29) · **File**: `Residue.lean` · **Depends on**: T033 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-09-29 DONE — inline cleanup: runLinter clean.
- Final per-file cleanup for `Residue.lean`.

### [T037] The gauge norm: the workhorse
- **Status**: done (2026-09-29) · **File**: `GaugeNorm.lean` · **Depends on**: none · **Parallel**: yes (Mathlib-only file) · **Type**: lemmas
- **Progress**: 2026-09-29 DONE — proved in GaugeNorm.lean (private helpers for membership in `ϖ ^ n A₀`, the down-set and the infimum, and `le_of_forall_zpow_le`); `gaugeNorm_nonneg` needs no topology and `gaugeNorm_neg` no topological-ring hypotheses (omitted, weakenings); builds, axioms standard, runLinter clean.
- **Leaves**: L11.1–L11.3

#### Statement
```lean
theorem gaugeNorm_nonneg (ha : 0 < a) (r : A) : 0 ≤ A₀.gaugeNorm ϖ a r := by sorry
theorem exists_mem_zpow_smul
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ((ϖ : A) ^ n) • (A₀ : Set A))
    (r : A) : ∃ n : ℤ, r ∈ ((ϖ ^ n : Aˣ) : A) • (A₀ : Set A) := by sorry
theorem gaugeNorm_le_zpow_iff (hϖ : (ϖ : A) ∈ A₀)
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ((ϖ : A) ^ n) • (A₀ : Set A))
    (ha : 1 < a) (n : ℤ) :
    A₀.gaugeNorm ϖ a r ≤ a ^ (-n) ↔ r ∈ ((ϖ ^ n : Aˣ) : A) • (A₀ : Set A) := by sorry
theorem gaugeNorm_eq_zero_or_exists_zpow (hϖ : (ϖ : A) ∈ A₀)
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ((ϖ : A) ^ n) • (A₀ : Set A))
    (ha : 1 < a) (r : A) : A₀.gaugeNorm ϖ a r = 0 ∨ ∃ n : ℤ, A₀.gaugeNorm ϖ a r = a ^ n := by sorry
theorem gaugeNorm_le_one_iff (hϖ : (ϖ : A) ∈ A₀)
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ((ϖ : A) ^ n) • (A₀ : Set A))
    (ha : 1 < a) : A₀.gaugeNorm ϖ a r ≤ 1 ↔ r ∈ A₀ := by sorry
```
#### Proof sketch
Write `E r := {n : ℤ | r ∈ ((ϖ ^ n : Aˣ) : A) • (A₀ : Set A)}` and `S r := {a ^ (-n) | n ∈ E r}`; `gaugeNorm` is
`sInf (S r)` and `S r` is bounded below by `0`.
1. `gaugeNorm_nonneg`: `Real.sInf_nonneg`, `zpow_nonneg ha.le`.
2. `exists_mem_zpow_smul` (**no `hϖ`**): `A₀ ∈ 𝓝 0` is `hbasis.mem_of_mem trivial` at `n = 0` (`pow_zero`, `one_smul`).
   `(continuous_mul_right r).tendsto 0` with `zero_mul` makes `{x | x * r ∈ A₀}` a neighbourhood of `0`, so it contains
   some `ϖ ^ N • A₀` (`hbasis.mem_iff`); `ϖ ^ N = ϖ ^ N • 1` lies there (`A₀.one_mem`), so `ϖ ^ N * r ∈ A₀` and
   `r = ϖ ^ (-N) • (ϖ ^ N * r)`: take `n := -N` (`zpow_neg`, `zpow_natCast`, `Units.inv_mul_cancel_left`).
3. Two private helpers on `E r`. (a) *Down-set*: `n ∈ E r → m ≤ n → m ∈ E r`, from `ϖ ^ n • b = ϖ ^ m • (ϖ ^ (n - m) * b)`
   and `ϖ ^ (n - m) ∈ A₀` as a natural power of `ϖ ∈ A₀` (`Int.toNat_of_nonneg`, `pow_mem`) — this is where `hϖ` enters.
   (b) *Dichotomy*: either `E r = Set.univ` (unbounded above + (a)), or `E r` has a greatest element `N`
   (`Int.exists_greatest_of_bdd` with step 2) and `sInf (S r) = a ^ (-N)` (`IsLeast.csInf_eq`; `n ≤ N` gives
   `a ^ (-N) ≤ a ^ (-n)` by `zpow_le_zpow_iff_right₀ ha`).
4. `gaugeNorm_le_zpow_iff`. `⇐`: `csInf_le`. `⇒`: by (b): if `E r = univ` done; else `a ^ (-N) ≤ a ^ (-n)` gives
   `n ≤ N` and (a) applies. Both sides are true when `r ∈ ⋂ ϖ ^ n A₀` — no `T2Space`.
5. `gaugeNorm_eq_zero_or_exists_zpow`: by (b). If `E r = univ`: `sInf (S r) ≤ a ^ (-(k : ℤ))` for all `k : ℕ`, and
   `(a⁻¹) ^ k → 0` (`exists_pow_lt_of_lt_one` for `a⁻¹ < 1`), so the infimum is `0` with step 1. Else `⟨-N, _⟩`.
6. `gaugeNorm_le_one_iff`: step 4 at `n = 0` (`neg_zero`, `zpow_zero`, `Units.val_one`, `one_smul`).
#### Mathlib lemmas needed
`Real.sInf_nonneg`, `csInf_le`, `IsLeast.csInf_eq`, `Filter.HasBasis.mem_of_mem`, `Filter.HasBasis.mem_iff`, `continuous_mul_right`, `Int.exists_greatest_of_bdd`, `zpow_le_zpow_iff_right₀`, `exists_pow_lt_of_lt_one`, `Set.mem_smul_set`, `zpow_natCast`, `pow_mem`.
#### Sources
[JN] Remark 2.1.3(1) (`jn.txt:502`): "If `a ∈ ℝ_{>1}`, then we may define a norm on `R` by `|r| = inf {a^{−n} | r ∈ ϖⁿR₀, n ∈ ℤ}`. Equipped with this norm, `R` is a Tate normed ring with unit ball `R₀`"; [Wed] Prop 6.14 (`wedhorn.txt:2176`): "For every `a ∈ A` there exists `n ∈ ℕ` such that `a sⁿ ∈ B`"; decomposition L11.1–L11.3.
#### Generality decision
Mathlib vocabulary only (plan decision 6): a commutative topological ring `A`, a subring `A₀`, a unit `ϖ ∈ A₀`, and `hbasis` — the fact Tau Ceti's `IsTateRing` supplies. Absorption needs no `hϖ`; the workhorse needs no `T2Space`.

### [T038] The gauge norm: the ring-norm inequalities
- **Status**: done (2026-09-29) · **File**: `GaugeNorm.lean` · **Depends on**: T037 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-09-29 DONE — proved in GaugeNorm.lean (private helpers for membership in `ϖ ^ n A₀`, the down-set and the infimum, and `le_of_forall_zpow_le`); `gaugeNorm_nonneg` needs no topology and `gaugeNorm_neg` no topological-ring hypotheses (omitted, weakenings); builds, axioms standard, runLinter clean.
- **Leaves**: L11.4

#### Statement
```lean
theorem gaugeNorm_add_le_max (hϖ : (ϖ : A) ∈ A₀)
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ((ϖ : A) ^ n) • (A₀ : Set A))
    (ha : 1 < a) (r s : A) :
    A₀.gaugeNorm ϖ a (r + s) ≤ max (A₀.gaugeNorm ϖ a r) (A₀.gaugeNorm ϖ a s) := by sorry
theorem gaugeNorm_neg (r : A) : A₀.gaugeNorm ϖ a (-r) = A₀.gaugeNorm ϖ a r := by sorry
theorem gaugeNorm_mul_le (hϖ : (ϖ : A) ∈ A₀)
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ((ϖ : A) ^ n) • (A₀ : Set A))
    (ha : 1 < a) (r s : A) :
    A₀.gaugeNorm ϖ a (r * s) ≤ A₀.gaugeNorm ϖ a r * A₀.gaugeNorm ϖ a s := by sorry
theorem gaugeNorm_unit_mul (hϖ : (ϖ : A) ∈ A₀)
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ((ϖ : A) ^ n) • (A₀ : Set A))
    (ha : 1 < a) (r : A) : A₀.gaugeNorm ϖ a ((ϖ : A) * r) = a⁻¹ * A₀.gaugeNorm ϖ a r := by sorry
```
#### Proof sketch
Everything goes through the workhorse `gaugeNorm_le_zpow_iff` and the value lemma of T037.
1. `gaugeNorm_neg` (no hypotheses): the two defining sets coincide, since `-(ϖ ^ n • b) = ϖ ^ n • (-b)`
   (`Set.mem_smul_set`, `smul_neg`, `neg_mem`); `congrArg sInf (Set.ext _)`.
2. `gaugeNorm_add_le_max`: `ϖ ^ n • A₀` is closed under addition (`smul_add`, `add_mem`). Let `m := max (N r) (N s)`.
   By the value lemma `m = 0` or `m = a ^ k`. If `m = a ^ k = a ^ (-(-k))`: both `r, s ∈ ϖ ^ (-k) • A₀` (workhorse `⇒`),
   so `r + s` is, so `N (r + s) ≤ a ^ k`. If `m = 0`: `r, s ∈ ϖ ^ n • A₀` for every `n`, hence `N (r + s) ≤ a ^ (-n)`
   for every `n`, hence `≤ 0` (as in T037 step 5).
3. `gaugeNorm_mul_le`: `(ϖ ^ n • b) * (ϖ ^ m • b') = ϖ ^ (n + m) • (b * b')` (`zpow_add`, `mul_mul_mul_comm`). If
   `N r = a ^ k` and `N s = a ^ l`: `r * s ∈ ϖ ^ (-k - l) • A₀`, so `N (r * s) ≤ a ^ (k + l)` (`zpow_add₀`). If `N r = 0`
   (or `N s = 0`): `r ∈ ϖ ^ n • A₀` for all `n`, `s ∈ ϖ ^ m • A₀` for one `m` (T037 absorption), so `r * s` lies in
   every `ϖ ^ n • A₀` and `N (r * s) ≤ 0 = N r * N s`.
4. `gaugeNorm_unit_mul`: `ϖ * r ∈ ϖ ^ n • A₀ ↔ r ∈ ϖ ^ (n - 1) • A₀`, so the defining set of `ϖ * r` is
   `a⁻¹ • S r` (`zpow_sub_one₀`, `neg_sub`); `Real.sInf_smul_of_nonneg (inv_nonneg.2 _)`, `smul_eq_mul`.
#### Mathlib lemmas needed
`Set.mem_smul_set`, `smul_neg`, `smul_add`, `zpow_add`, `zpow_add₀`, `zpow_sub_one₀`, `Real.sInf_smul_of_nonneg`, `smul_eq_mul`.
#### Sources
[JN] Definition 2.1.1 (`jn.txt:476`): "(2) `|r + s| ≤ max(|r|, |s|)`; (3) `|rs| ≤ |r||s|`"; Remark 2.1.3(1): "`ϖ` is a multiplicative pseudo-uniformizer"; decomposition L11.4.
#### Generality decision
No `T2Space` anywhere in this ticket: the inequalities hold for the seminorm. `gaugeNorm_neg` holds for any subring and unit.

### [CLEANUP-ALL-2] Run /cleanup-all on `PhD/TauCeti/Code/PadicFunctionalAnalysis/`
- **Status**: done (2026-09-29) · **Depends on**: T038 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-09-29 DONE — inline sweep: every finished module (Sums, UnitBall, PowerBounded, Multiplicative, Module, Tate, NormComparison, Rescale, Residue, GaugeNorm) builds with no warnings, runLinter clean, standard axioms, lines ≤ 100 chars.
- Before milestone M2 (T039). Sweep every file with finished tickets; do not touch declarations that are still `sorry`.

### [T039] The gauge norm is a ring norm inducing the topology
- **Status**: done (2026-09-29) · **File**: `GaugeNorm.lean` · **Depends on**: CLEANUP-ALL-2 · **Parallel**: no · **Type**: lemmas + def fields · **MILESTONE**
- **Progress**: 2026-09-29 DONE — proved in GaugeNorm.lean (private helpers for membership in `ϖ ^ n A₀`, the down-set and the infimum, and `le_of_forall_zpow_le`); `gaugeNorm_nonneg` needs no topology and `gaugeNorm_neg` no topological-ring hypotheses (omitted, weakenings); builds, axioms standard, runLinter clean.
- **Leaves**: L11.5–L11.6

#### Statement
```lean
theorem hasBasis_nhds_zero_gaugeNorm (hϖ : (ϖ : A) ∈ A₀)
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ((ϖ : A) ^ n) • (A₀ : Set A))
    (ha : 1 < a) :
    (𝓝 (0 : A)).HasBasis (fun ε : ℝ ↦ 0 < ε) fun ε ↦ {r | A₀.gaugeNorm ϖ a r < ε} := by sorry
theorem gaugeNorm_eq_zero_iff (hϖ : (ϖ : A) ∈ A₀)
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ((ϖ : A) ^ n) • (A₀ : Set A))
    (ha : 1 < a) : A₀.gaugeNorm ϖ a r = 0 ↔ r = 0 := by sorry
theorem exists_gaugeNorm_eq_zpow (hϖ : (ϖ : A) ∈ A₀)
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ((ϖ : A) ^ n) • (A₀ : Set A))
    (ha : 1 < a) (hr : r ≠ 0) : ∃ n : ℤ, A₀.gaugeNorm ϖ a r = a ^ n := by sorry
theorem gaugeNorm_one (hϖ : (ϖ : A) ∈ A₀)
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ((ϖ : A) ^ n) • (A₀ : Set A))
    (ha : 1 < a) : A₀.gaugeNorm ϖ a 1 = 1 := by sorry
theorem gaugeNorm_unit (hϖ : (ϖ : A) ∈ A₀)
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ((ϖ : A) ^ n) • (A₀ : Set A))
    (ha : 1 < a) : A₀.gaugeNorm ϖ a (ϖ : A) = a⁻¹ := by sorry
noncomputable def gaugeRingNorm [IsTopologicalRing A] [T2Space A] (A₀ : Subring A) (ϖ : Aˣ)
    (a : ℝ) (hϖ : (ϖ : A) ∈ A₀)
    (hbasis : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ ((ϖ : A) ^ n) • (A₀ : Set A))
    (ha : 1 < a) : RingNorm A where
  toFun := A₀.gaugeNorm ϖ a
  map_zero' := by
    sorry
  add_le' r s := by
    sorry
  neg' r := by
    sorry
  mul_le' r s := by
    sorry
  eq_zero_of_map_eq_zero' r hr := by
    sorry
```
#### Proof sketch
1. `hasBasis_nhds_zero_gaugeNorm`: `hbasis.to_hasBasis`. Given `n : ℕ`, take `ε := a ^ (-(n : ℤ))`:
   `N r < ε → N r ≤ ε → r ∈ ϖ ^ n • A₀` (workhorse; `zpow_natCast`, `Units.val_pow_eq_pow_val`). Given `ε > 0`, pick
   `n : ℕ` with `(a⁻¹) ^ n < ε` (`exists_pow_lt_of_lt_one`); `r ∈ ϖ ^ n • A₀ → N r ≤ a ^ (-(n : ℤ)) < ε`.
2. `gaugeNorm_eq_zero_iff` (`T2Space`). `⇐`: `0 ∈ ϖ ^ n • A₀` for all `n`, so `N 0 ≤ a ^ (-n)` for all `n`. `⇒`: if
   `r ≠ 0`, `{r}ᶜ` is a neighbourhood of `0` (`isOpen_compl_singleton`), so contains some `ϖ ^ n • A₀`; but
   `N r = 0 ≤ a ^ (-n)` puts `r` in it.
3. `exists_gaugeNorm_eq_zpow`: T037's value lemma and step 2.
4. `gaugeNorm_one` (`Nontrivial`): `N 1 ≤ 1` by `gaugeNorm_le_one_iff` and `one_mem`. If `N 1 < 1`, then
   `N 1 = a ^ k` with `k ≤ -1` (step 3 with `one_ne_zero`; `zpow_lt_one_iff_right₀`), so `1 ∈ ϖ • A₀`, i.e.
   `ϖ⁻¹ ∈ A₀`; then `1 = ϖ ^ n • (ϖ⁻¹) ^ n ∈ ϖ ^ n • A₀` for every `n`, so `N 1 = 0`, so `1 = 0` by step 2 — absurd.
5. `gaugeNorm_unit`: T038 `gaugeNorm_unit_mul` at `r = 1`, step 4, `mul_one`.
6. Fields of `gaugeRingNorm`: `map_zero'` from step 2; `add_le'` from T038 and `max_le_add_of_nonneg`; `neg'`, `mul_le'`
   from T038; `eq_zero_of_map_eq_zero'` from step 2.
#### Mathlib lemmas needed
`Filter.HasBasis.to_hasBasis`, `exists_pow_lt_of_lt_one`, `isOpen_compl_singleton`, `zpow_natCast`, `Units.val_pow_eq_pow_val`, `max_le_add_of_nonneg`, `one_mem`, `pow_mem`.
#### Sources
[JN] Remark 2.1.3(1) (`jn.txt:502`), quoted in T037; [RM] §0.4.6 ("inducing the topology of `A`"; "⚠ The Hausdorff hypothesis is necessary: without it the formula gives only a seminorm, with kernel the closure of `0`"); decomposition L11.5–L11.6.
#### Generality decision
`T2Space` exactly where the seminorm must be a norm; `Nontrivial` exactly for `N 1 = 1`. [JN] omit "Hausdorff" because their Tate rings are complete. `gaugeRingNorm` is a `RingNorm`; turning it into a `NormedRing` instance is left to the caller (a second norm on `A` must not become an instance).

### [CLEANUP-15] Run /cleanup on `GaugeNorm.lean`
- **Status**: done (2026-09-29) · **File**: `GaugeNorm.lean` · **Depends on**: T039 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-09-29 DONE — inline sweep: every finished module (Sums, UnitBall, PowerBounded, Multiplicative, Module, Tate, NormComparison, Rescale, Residue, GaugeNorm) builds with no warnings, runLinter clean, standard axioms, lines ≤ 100 chars.
- Final per-file cleanup for `GaugeNorm.lean`.

### [T034] Ideal powers are norm balls
- **Status**: done (2026-09-29) · **File**: `Huber.lean` · **Depends on**: CLEANUP-13, CLEANUP-5 · **Parallel**: no · **Type**: lemmas
- **Progress**: 2026-09-29 DONE — proved in Huber.lean; `isTopologicallyNilpotent` needs neither `NormOneClass` nor ultrametricity (omitted, a weakening); builds, axioms standard, runLinter clean.
- **Leaves**: L10.1–L10.2

#### Statement
```lean
theorem isTopologicallyNilpotent : IsTopologicallyNilpotent (ϖ : R) := by sorry
theorem mem_ideal_pow_iff {n : ℕ} {a : unitClosedBall R} :
    a ∈ ϖ.ideal ^ n ↔ ‖(a : R)‖ ≤ ‖(ϖ : R)‖ ^ n := by sorry
theorem ideal_pow_eq_closedBallIdeal (n : ℕ) :
    ϖ.ideal ^ n = closedBallIdeal R (‖(ϖ : R)‖₊ ^ n) := by sorry
theorem ideal_fg : ϖ.ideal.FG := by sorry
```
#### Proof sketch
1. `isTopologicallyNilpotent`: `IsTopologicallyNilpotent.of_norm_lt_one ϖ.norm_lt_one` (T014).
2. `mem_ideal_pow_iff`: `ideal`, `Ideal.span_singleton_pow`, `Ideal.mem_span_singleton'`. `⇒`: `a = b * ϖ ^ n`,
   `‖a‖ ≤ ‖b‖ * ‖ϖ ^ n‖ ≤ ‖ϖ‖ ^ n` (T015 `norm_pow`). `⇐`: `b := ⟨((ϖ.unit ^ (-(n : ℤ)) : Rˣ) : R) * a, _⟩`, of norm
   `‖ϖ‖ ^ (-n) * ‖a‖ ≤ 1` (T016 `zpow`, `norm_zpow`); `Subtype.ext` and `zpow_neg`, `zpow_natCast`,
   `Units.inv_mul_cancel_left`. At `n = 0` both sides are trivially true — check it is not a special case.
3. `ideal_pow_eq_closedBallIdeal`: `Ideal.ext`; step 2, `mem_closedBallIdeal`, `NNReal.coe_pow`, `coe_nnnorm`.
4. `ideal_fg`: `Submodule.fg_span_singleton _`.
#### Mathlib lemmas needed
`Ideal.span_singleton_pow`, `Ideal.mem_span_singleton'`, `Submodule.fg_span_singleton`, `NNReal.coe_pow`, `coe_nnnorm`, `zpow_neg`, `zpow_natCast`; T014, T015, T016, T007.
#### Sources
[RM] §0.4.5 ("the ideal powers are the norm balls, `ϖⁿ R⁰ = {r ∈ R⁰ | ‖r‖ ≤ ‖ϖ‖ ^ n}`"); [Wed] Def 6.1(ii) (`wedhorn.txt:2059`): "`I` is a finitely generated ideal of `A₀`"; [JN] Remark 2.1.3(1): "`ϖ` is a topologically nilpotent unit"; [SRC] `00_TateRings.mem_ideal_pow`; decomposition L10.1–L10.2.
#### Generality decision
Stated in Mathlib vocabulary (erratum E7); `NormedCommRing` + `NormOneClass` + `IsUltrametricDist`, as `R⁰` must be a subring with ideals.

### [CLEANUP-ALL-1] Run /cleanup-all on `PhD/TauCeti/Code/PadicFunctionalAnalysis/`
- **Status**: done (2026-09-29) · **Depends on**: T034 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-09-29 DONE — inline sweep before M1: all finished modules build without warnings, runLinter clean, standard axioms.
- Before milestone M1 (T035). Sweep every file with finished tickets; do not touch declarations that are still `sorry`.

### [T035] The unit ball is a ring of definition
- **Status**: done (2026-09-29) · **File**: `Huber.lean` · **Depends on**: CLEANUP-ALL-1 · **Parallel**: no · **Type**: theorems · **MILESTONE**
- **Progress**: 2026-09-29 DONE — proved in Huber.lean; `isTopologicallyNilpotent` needs neither `NormOneClass` nor ultrametricity (omitted, a weakening); builds, axioms standard, runLinter clean.
- **Leaves**: L10.3–L10.6

#### Statement
```lean
theorem isAdic_ideal : IsAdic ϖ.ideal := by sorry
theorem exists_pow_mul_mem_unitClosedBall (a : R) : ∃ n : ℕ, (ϖ : R) ^ n * a ∈ unitClosedBall R := by sorry
theorem hasBasis_nhds_zero_smul_unitClosedBall :
    (𝓝 (0 : R)).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ ((ϖ : R) ^ n) • (unitClosedBall R : Set R) := by sorry
theorem isPowerBounded_of_mem_unitClosedBall {R : Type*} [SeminormedRing R] [NormOneClass R]
    [IsUltrametricDist R] {a : R} (ha : a ∈ Subring.unitClosedBall R) :
    PowerBounded.IsPowerBounded a := by sorry
```
#### Proof sketch
1. `isAdic_ideal`: `isAdic_iff` (the `IsTopologicalRing ↥(unitClosedBall R)` instance is Mathlib's subring instance).
   (i) openness: rewrite by T034 `ideal_pow_eq_closedBallIdeal`, then T007 `isOpen_closedBallIdeal (pow_pos _ n)`.
   (ii) cofinality: `Metric.mem_nhds_iff` gives `ε`; `exists_pow_lt_of_lt_one` gives `n` with `‖ϖ‖ ^ n < ε`; an
   element of `ϖ.ideal ^ n` has norm `≤ ‖ϖ‖ ^ n < ε` (T034), so lies in the ball (`mem_ball_zero_iff`,
   the subtype norm is the ambient norm, by `rfl`; cf. `AddSubgroupClass.coe_norm`).
2. `exists_pow_mul_mem_unitClosedBall`: `‖ϖ ^ n * a‖ = ‖ϖ‖ ^ n * ‖a‖` (T015 `norm_pow_mul`). `a = 0`: `n := 0`.
   Otherwise `exists_pow_lt_of_lt_one (inv_pos.2 (norm_pos_iff.2 ha))` and `mul_inv_le_iff₀`.
3. `hasBasis_nhds_zero_smul_unitClosedBall`: first `ϖ ^ n • (R⁰ : Set R) = Metric.closedBall 0 (‖ϖ‖ ^ n)`
   (`Set.ext`, `Set.mem_smul_set`, `smul_eq_mul`; `⇒` by `norm_pow_mul`; `⇐` with `r = ϖ ^ n * (ϖ⁻¹ ^ n * r)` and T016).
   Then `Metric.nhds_basis_closedBall_pow ϖ.norm_pos ϖ.norm_lt_one` rewritten along that identity.
4. `isPowerBounded_of_mem_unitClosedBall`: `PowerBounded.isPowerBounded_of_norm_le_one (mem_unitClosedBall.1 ha)` (T013).
#### Mathlib lemmas needed
`isAdic_iff`, `Metric.mem_nhds_iff`, `exists_pow_lt_of_lt_one`, `mem_ball_zero_iff`, `Metric.nhds_basis_closedBall_pow`, `Set.mem_smul_set`, `smul_eq_mul`; T007, T013, T015, T016, T034.
#### Sources
[JN] Remark 2.1.3(1) (`jn.txt:500`): "The underlying topological ring is a Tate ring in the language of Huber; the unit ball `R₀` is a ring of definition and `ϖ` is a topologically nilpotent unit"; [Wed] Def 6.1(ii), Def 6.10, Prop 6.14 (`wedhorn.txt:2059, 2176`); [Buz07] `buzzard.txt:158`: "the ideals of `A₀` generated by `ρⁿ` … form a basis of open neighbourhoods of zero"; [RM] §0.4.5; decomposition L10.3–L10.6.
#### Generality decision
**Seam (E7)**: with T006 (`isOpen_unitClosedBall`), T034 (`ideal_fg`, `isTopologicallyNilpotent`) these are the fields of Tau Ceti's pair of definition plus the Tate condition, in Mathlib vocabulary. `hasBasis_…` is stated in exactly the hypothesis shape of `GaugeNorm.lean`.

### [T036] The round trip: gauge norm of `(R⁰, ϖ)` is the rescaled norm
- **Status**: done (2026-09-29) · **File**: `Huber.lean` · **Depends on**: T035, CLEANUP-12, CLEANUP-15 · **Parallel**: no · **Type**: theorem
- **Progress**: 2026-09-29 DONE — proved in Huber.lean; `isTopologicallyNilpotent` needs neither `NormOneClass` nor ultrametricity (omitted, a weakening); builds, axioms standard, runLinter clean.
- **Leaves**: L10.7

#### Statement
```lean
theorem gaugeNorm_unitClosedBall (r : R) :
    (unitClosedBall R).gaugeNorm ϖ.unit ‖(ϖ : R)‖⁻¹ r = Real.zpowCeil ‖(ϖ : R)‖ ‖r‖ := by sorry
```
#### Proof sketch
Both sides are `sInf` of a set of reals; show the two sets are equal and finish with `congrArg sInf`.
1. For `n : ℤ`: `r ∈ ((ϖ.unit ^ n : Rˣ) : R) • (R⁰ : Set R) ↔ ‖r‖ ≤ ‖ϖ‖ ^ n` — the `ℤ`-version of T035 step 3, by
   T016 `zpow`/`norm_zpow` (`⇒`: `‖ϖ ^ n * b‖ = ‖ϖ‖ ^ n * ‖b‖ ≤ ‖ϖ‖ ^ n`; `⇐`: `b := ϖ ^ (-n) * r`).
2. `(‖ϖ‖⁻¹) ^ (-n) = ‖ϖ‖ ^ n` (`inv_zpow'`, `neg_neg`).
3. `Subring.gaugeNorm` and `Real.zpowCeil` unfold (`rfl`/`unfold`) to `sInf {y | ∃ n, y = _ ∧ _}`; `Set.ext` with steps
   1–2. Only the two *definitions* are used — no lemma of `GaugeNorm.lean` or `Rescale.lean`.
#### Mathlib lemmas needed
`Set.mem_smul_set`, `smul_eq_mul`, `inv_zpow'`, `neg_neg`, `zpow_neg`, `Units.mul_inv_cancel_left`; T016.
#### Sources
[JN] Remark 2.1.3(1) (`jn.txt:500–502`), both directions, read against [RM] §0.3.3 and [JN] Lemma 2.1.7; decomposition L10.7 (**planner's addition**: the precise sense in which the two bridges are mutually inverse).
#### Generality decision
Equality with the *rescaled* norm `zpowCeil ‖ϖ‖ ‖r‖`, not the original norm (false in `ℂ_p`, T042). At `r = 0` both sides are `0`. Depends on CLEANUP-12 and CLEANUP-15 only so that both definitions are final.

### [CLEANUP-14] Run /cleanup on `Huber.lean`
- **Status**: done (2026-09-29) · **File**: `Huber.lean` · **Depends on**: T036 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-09-29 DONE — inline cleanup: runLinter clean.
- Final per-file cleanup for `Huber.lean`.

### [T040] Examples over `ℚ_p`
- **Status**: done (2026-09-29) · **File**: `Examples.lean` · **Depends on**: CLEANUP-13 · **Parallel**: yes (with G10) · **Type**: examples
- **Progress**: 2026-09-29 DONE — proved in Examples.lean (private helpers `norm_p_padicInt_lt_one`, `norm_p_padicComplex`); builds, axioms standard, runLinter clean.
- **Leaves**: L12.1–L12.4

#### Statement
```lean
theorem unitClosedBall_padic : unitClosedBall ℚ_[p] = PadicInt.subring p := by sorry
theorem ideal_padic_eq_openUnitBallIdeal (hc₀ : (p : ℚ_[p]) ≠ 0) (hc₁ : ‖(p : ℚ_[p])‖ < 1) :
    (ofNormedAlgebra ℚ_[p] hc₀ hc₁ : PseudoUniformizer ℚ_[p]).ideal =
      openUnitBallIdeal ℚ_[p] := by sorry
theorem nonempty_residueRing_padic_equiv_zmod :
    Nonempty ((unitClosedBall ℚ_[p] ⧸ openUnitBallIdeal ℚ_[p]) ≃+* ZMod p) := by sorry
theorem norm_zpow_mul_mem_Ioc_iff {x : ℚ_[p]} (hx : x ≠ 0) (n : ℤ) :
    ‖(p : ℚ_[p]) ^ n * x‖ ∈ Set.Ioc ‖(p : ℚ_[p])‖ 1 ↔ n = -x.valuation := by sorry
```
#### Proof sketch
1. `unitClosedBall_padic`: `Subring.ext fun x ↦ _`; `mem_unitClosedBall` against the carrier `{x | ‖x‖ ≤ 1}` of
   `PadicInt.subring p` (`Iff.rfl` after unfolding).
2. `ideal_padic_eq_openUnitBallIdeal`: T032 `ideal_eq_openUnitBallIdeal`. The pseudo-uniformiser coerces to
   `algebraMap ℚ_[p] ℚ_[p] p = p` (`coe_ofNormedAlgebra`, `Algebra.algebraMap_self`/`rfl`). For `r ≠ 0`:
   `‖r‖ = p ^ (-r.valuation)` (`Padic.norm_eq_zpow_neg_valuation`) `= ‖p‖ ^ r.valuation` (`Padic.norm_p`, `inv_zpow'`).
3. `nonempty_residueRing_padic_equiv_zmod`: transport along step 1 to `ℤ_[p]`; the composite
   `unitClosedBall ℚ_[p] →+* ZMod p` through `PadicInt.toZMod` is surjective (`ZMod.ringHom_surjective`) with kernel
   the open unit ball (`PadicInt.ker_toZMod`, `PadicInt.norm_lt_one_iff_dvd`, `PadicInt.maximalIdeal_eq_span_p`);
   `RingHom.quotientKerEquivOfSurjective`, `Ideal.quotEquivOfEq`.
4. `norm_zpow_mul_mem_Ioc_iff`: `norm_mul`, `norm_zpow`, `Padic.norm_p`, `Padic.norm_eq_zpow_neg_valuation hx`:
   `‖p ^ n * x‖ = (p : ℝ) ^ (-(n + v))`; `Set.mem_Ioc`; `zpow_lt_zpow_iff_right₀`, `zpow_le_one_iff_right₀`
   (base `(p : ℝ) > 1`), `omega`.
#### Mathlib lemmas needed
`PadicInt.subring`, `Padic.norm_eq_zpow_neg_valuation`, `Padic.norm_p`, `inv_zpow'`, `PadicInt.toZMod`, `PadicInt.ker_toZMod`, `ZMod.ringHom_surjective`, `RingHom.quotientKerEquivOfSurjective`, `Ideal.quotEquivOfEq`, `zpow_lt_zpow_iff_right₀`, `zpow_le_one_iff_right₀`.
#### Sources
[RM] Layer 0 Examples ("`ℚ_p` … with `R⁰`", "the shells `‖ϖ‖ < ‖ϖⁿ x‖ ≤ 1` in `ℚ_p` with `ϖ = p`"); decomposition L12.1–L12.4.
#### Generality decision
Concrete instances only; the hypotheses `hc₀`, `hc₁` are kept as arguments so that the statement names the pseudo-uniformiser `ofNormedAlgebra ℚ_[p] hc₀ hc₁`.

### [T041] Examples over `ℤ_p`: the non-example and the Neumann series
- **Status**: done (2026-09-29) · **File**: `Examples.lean` · **Depends on**: T040 · **Parallel**: no · **Type**: examples
- **Progress**: 2026-09-29 DONE — proved in Examples.lean (private helpers `norm_p_padicInt_lt_one`, `norm_p_padicComplex`); builds, axioms standard, runLinter clean.
- **Leaves**: L12.5

#### Statement
```lean
theorem not_isTate_padicInt : ¬ IsTate ℤ_[p] := by sorry
theorem norm_tsum_pow_padicInt : ‖∑' n : ℕ, (p : ℤ_[p]) ^ n‖ = 1 := by sorry
theorem norm_tsum_pow_padicInt_sub_one : ‖∑' n : ℕ, (p : ℤ_[p]) ^ n - 1‖ = (p : ℝ)⁻¹ := by sorry
```
#### Proof sketch
1. `not_isTate_padicInt`: `rintro ⟨⟨ϖ⟩⟩`; `ϖ.unit.isUnit` and `PadicInt.isUnit_iff` give `‖(ϖ : ℤ_[p])‖ = 1`,
   contradicting `ϖ.norm_lt_one`.
2. `‖(p : ℤ_[p])‖ < 1`: `PadicInt.norm_p`, `inv_lt_one_of_one_lt₀`, `Nat.one_lt_cast`, `hp.out.one_lt`.
3. `norm_tsum_pow_padicInt`: T010 `norm_tsum_geometric` with step 2.
4. `norm_tsum_pow_padicInt_sub_one`: T010 `norm_tsum_geometric_sub_one`, then `PadicInt.norm_p`.
#### Mathlib lemmas needed
`PadicInt.isUnit_iff`, `PadicInt.norm_p`, `inv_lt_one_of_one_lt₀`, `Nat.one_lt_cast`; T010.
#### Sources
[RM] §0.4.7 ("A non-example: `ℤ_[p]`, whose norm has no unit of norm less than `1`"); acceptance example ("`‖∑' n, pⁿ‖ = 1` in `ℤ_p`"); decomposition L12.5.
#### Generality decision
Concrete instances; needs `CompleteSpace ℤ_[p]`, `IsUltrametricDist ℤ_[p]`, `NormOneClass ℤ_[p]` — all in Mathlib.

### [T042] Examples over `ℂ_p`: the value group is not discrete
- **Status**: done (2026-09-29) · **File**: `Examples.lean` · **Depends on**: T041, CLEANUP-12 · **Parallel**: no · **Type**: examples
- **Progress**: 2026-09-29 DONE — proved in Examples.lean (private helpers `norm_p_padicInt_lt_one`, `norm_p_padicComplex`); builds, axioms standard, runLinter clean.
- **Leaves**: L12.6

#### Statement
```lean
theorem exists_norm_p_lt_norm_lt_one_padicComplex :
    ∃ x : ℂ_[p], ‖(p : ℂ_[p])‖ < ‖x‖ ∧ ‖x‖ < 1 := by sorry
theorem exists_zpowCeil_norm_ne_padicComplex :
    ∃ x : ℂ_[p], Real.zpowCeil ‖(p : ℂ_[p])‖ ‖x‖ ≠ ‖x‖ := by sorry
theorem ideal_padicComplex_ne_openUnitBallIdeal (hc₀ : (p : ℚ_[p]) ≠ 0)
    (hc₁ : ‖(p : ℚ_[p])‖ < 1) :
    (ofNormedAlgebra ℚ_[p] hc₀ hc₁ : PseudoUniformizer ℂ_[p]).ideal ≠
      openUnitBallIdeal ℂ_[p] := by sorry
```
#### Proof sketch
1. `obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (p : ℂ_[p]) two_pos`, so `‖x‖ ^ 2 = ‖(p : ℂ_[p])‖` (`norm_pow`).
   `‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ =: t ∈ (0, 1)`: `(p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] p` (`map_natCast`),
   `norm_algebraMap'`, `Padic.norm_p`. From `‖x‖ ^ 2 = t`: `t < ‖x‖` (else `‖x‖ ^ 2 ≤ t ^ 2 < t`) and `‖x‖ < 1` (else
   `‖x‖ ^ 2 ≥ 1 > t`); `pow_le_pow_left₀`, `nlinarith`.
2. `exists_zpowCeil_norm_ne_padicComplex`: the same `x`. `Real.zpowCeil t ‖x‖ = t ^ n` for some `n` (T029); if it
   equalled `‖x‖` then `t ^ 1 < t ^ n < t ^ 0`, i.e. `0 < n < 1` (`zpow_lt_zpow_iff_right_of_lt_one₀`), `omega`.
3. `ideal_padicComplex_ne_openUnitBallIdeal`: `⟨x, _⟩ : unitClosedBall ℂ_[p]` lies in `openUnitBallIdeal` but not in
   the ideal, by T032 `mem_ideal_iff` and `coe_ofNormedAlgebra`, `norm_algebraMap'`; `fun h ↦ _` with `h ▸`/`SetLike.ext_iff`.
#### Mathlib lemmas needed
`IsAlgClosed.exists_pow_nat_eq`, `norm_pow`, `map_natCast`, `norm_algebraMap'`, `Padic.norm_p`, `pow_le_pow_left₀`, `zpow_lt_zpow_iff_right_of_lt_one₀`; T029, T032.
#### Sources
[RM] Layer 0 Examples ("the rescaled norm on `ℂ_p` with `π = p` … is not the original norm"); decomposition L12.6. This is the counterexample behind errata E3 and the value hypotheses of T031–T033.
#### Generality decision
Concrete; uses `NormedAlgebra ℚ_[p] ℂ_[p]` and `IsAlgClosed ℂ_[p]` from `Mathlib.NumberTheory.Padics.Complex`.

### [CLEANUP-16] Run /cleanup on `Examples.lean`
- **Status**: done (2026-09-29) · **File**: `Examples.lean` · **Depends on**: T042 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-09-29 DONE — inline cleanup: runLinter clean; over-long lines in the folder wrapped.
- Per-file cadence (every third proof ticket on the file, and after the last). Inline as the main agent; `lake exe runLinter` on the module; prune imports with `lake exe shake`.

### [T043] Counterexample: `ℤ` with the discrete topology
- **Status**: done (2026-09-29) · **File**: `Examples.lean` · **Depends on**: CLEANUP-16, CLEANUP-5 · **Parallel**: no · **Type**: examples
- **Progress**: 2026-09-29 DONE — proved in Examples.lean (private helpers `norm_p_padicInt_lt_one`, `norm_p_padicComplex`); builds, axioms standard, runLinter clean.
- **Leaves**: L12.7

#### Statement
```lean
theorem isPowerBounded_int (n : ℤ) : PowerBounded.IsPowerBounded n := by sorry
theorem norm_two_int : ‖(2 : ℤ)‖ = 2 := by sorry
theorem not_neBot_nhdsNE_zero_int : ¬ NeBot (𝓝[≠] (0 : ℤ)) := by sorry
```
#### Proof sketch
1. `isPowerBounded_int`: unfold `IsPowerBounded`, `TopologicalRing.IsBounded`. Given `U ∈ 𝓝 0` take `V := {0}`:
   `(isOpen_discrete _).mem_nhds rfl`; `{0} * S ⊆ {0}` (`Set.zero_mul_subset`, with `Set.singleton_zero`) and
   `{0} ⊆ U` by `mem_of_mem_nhds`.
2. `norm_two_int`: `Int.norm_eq_abs`; `norm_num`.
3. `not_neBot_nhdsNE_zero_int`: `discreteTopology_iff_nhds_ne.1 inferInstance 0` gives `𝓝[≠] 0 = ⊥`; `Filter.not_neBot`.
#### Mathlib lemmas needed
`isOpen_discrete`, `Set.zero_mul_subset`, `mem_of_mem_nhds`, `Int.norm_eq_abs`, `discreteTopology_iff_nhds_ne`, `Filter.not_neBot`.
#### Sources
[RM] §0.2.2 ("over `ℤ` with the discrete topology every element is power-bounded while `‖2‖ = 2`"); decomposition L12.7.
#### Generality decision
Shows `NeBot (𝓝[≠] 0)` cannot be dropped from T013's converse.

### [T044] Counterexample: the `ℓ¹` norm on `ℝ[X]/(X² − X)`
- **Status**: done (2026-09-29) · **File**: `Examples.lean` · **Depends on**: T043 · **Parallel**: no · **Type**: instance fields + examples
- **Progress**: 2026-09-29 DONE — proved in Examples.lean (private helpers `norm_p_padicInt_lt_one`, `norm_p_padicComplex`); builds, axioms standard, runLinter clean.
- **Leaves**: L12.8

#### Statement
```lean
noncomputable def addGroupNorm : AddGroupNorm L1Pair where
  toFun x := |x.1| + |x.2 - x.1|
  map_zero' := by
    sorry
  add_le' x y := by
    sorry
  neg' x := by
    sorry
  eq_zero_of_map_eq_zero' x hx := by
    sorry
theorem norm_mul_le (x y : L1Pair) : ‖x * y‖ ≤ ‖x‖ * ‖y‖ := by sorry
theorem oneSubTwoX_sq : oneSubTwoX ^ 2 = 1 := by sorry
theorem norm_oneSubTwoX : ‖oneSubTwoX‖ = 3 := by sorry
theorem isPowerBounded_oneSubTwoX : PowerBounded.IsPowerBounded oneSubTwoX := by sorry
```
#### Proof sketch
Coordinates: `a + bX ↦ (u, v) = (a, a + b)`, so multiplication is componentwise and `‖(u, v)‖ = |u| + |v − u|`.
1. Fields of `addGroupNorm`. `map_zero'`: `simp`. `add_le'`: `(x + y).2 − (x + y).1 = (x.2 − x.1) + (y.2 − y.1)`
   (`Prod.fst_add`, `Prod.snd_add`, `ring`), then `abs_add` twice and `linarith`. `neg'`: `abs_neg` after
   `-x.2 − -x.1 = -(x.2 − x.1)`. `eq_zero_of_map_eq_zero'`: both summands vanish (`add_eq_zero_iff_of_nonneg`,
   `abs_eq_zero`), so `x.1 = 0`, `x.2 = x.1`; `Prod.ext`.
2. `norm_mul_le`: with `a := x.1`, `b := x.2 − x.1`, `a' := y.1`, `b' := y.2 − y.1`:
   `x.2 * y.2 − x.1 * y.1 = a * b' + b * a' + b * b'`, so
   `‖x * y‖ = |a a'| + |a b' + b a' + b b'| ≤ (|a| + |b|) (|a'| + |b'|)` by `abs_add_three`, `abs_mul`, and expanding.
3. `oneSubTwoX_sq`: `Prod.ext` + `norm_num` (`(1, −1)² = (1, 1) = 1`).
4. `norm_oneSubTwoX`: `norm_def`; `norm_num` (`|1| + |−1 − 1| = 3`).
5. `isPowerBounded_oneSubTwoX`: T012 `PowerBounded.isPowerBounded_of_norm_pow_le (C := 3)`. For `n = 2k` the power is
   `1` with `‖1‖ = 1`; for `n = 2k + 1` it is `oneSubTwoX` (`pow_mul`, step 3, `one_pow`); `Nat.even_or_odd'`.
#### Mathlib lemmas needed
`abs_add`, `abs_neg`, `abs_mul`, `abs_add_three`, `abs_eq_zero`, `add_eq_zero_iff_of_nonneg`, `Prod.ext`, `pow_mul`, `Nat.even_or_odd'`; T012.
#### Sources
[RM] §0.2.2 ("the `ℓ¹` norm on `ℝ[X]/(X² − X)` … the element `1 − 2X` squares to `1` and has norm `3`"); decomposition L12.8 (arithmetic verified by hand).
#### Generality decision
Shows that submultiplicativity does not suffice in T013: `NormMulClass` cannot be weakened to a `NormedRing`. Realised on `ℝ × ℝ` to avoid a quotient of `ℝ[X]`.

### [CLEANUP-17] Run /cleanup on `Examples.lean`
- **Status**: done (2026-09-29) · **File**: `Examples.lean` · **Depends on**: T044 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-09-29 DONE — inline cleanup: runLinter clean; over-long lines in the folder wrapped.
- Final per-file cleanup for `Examples.lean`.

### [T045] Add Layer 0 to the Tau Ceti chain root
- **Status**: done (2026-09-29) · **File**: `PhD/TauCeti.lean` · **Depends on**: CLEANUP-2, CLEANUP-4, CLEANUP-5, CLEANUP-6, CLEANUP-7, CLEANUP-9, CLEANUP-10, CLEANUP-12, CLEANUP-13, CLEANUP-14, CLEANUP-15, CLEANUP-17 · **Parallel**: no · **Type**: build gate
- **Progress**: 2026-09-29 DONE — appended the two leaf modules to `PhD/TauCeti.lean`; `lake build PhD.TauCeti` passes (2639 jobs, no warnings in this folder); no `sorry`, no `import PhD.Main`; `#print axioms` on every declaration of the twelve modules (milestones included) gives only `propext`, `Classical.choice`, `Quot.sound`; runLinter clean on each module.

#### Statement
Append (append-only — a parallel board also edits this file; re-read it immediately before editing) the two leaf
modules, which import the other ten:
```lean
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Examples
import PhD.TauCeti.Code.PadicFunctionalAnalysis.NormComparison
```
#### Proof sketch
1. `grep -rn "sorry" PhD/TauCeti/Code/PadicFunctionalAnalysis/` returns nothing.
2. `lake build PhD.TauCeti` passes (never `lake build PhD`). No `import PhD.Main` anywhere in the folder.
3. `#print axioms` on the two milestones (`NormedRing.PseudoUniformizer.isAdic_ideal`, `Subring.gaugeRingNorm`) and on
   `NormedRing.PseudoUniformizer.gaugeNorm_unitClosedBall`: `propext`, `Classical.choice`, `Quot.sound` only.
4. `lake exe runLinter` on each of the twelve modules: no findings.
#### Mathlib lemmas needed
None.
#### Sources
Plan, "Build protocol"; memory `tauceti-newton-polygons` (chain layout, CI gate).
#### Generality decision
Not applicable.

### [CLEANUP-FINAL] Run /cleanup-all on `PhD/TauCeti/Code/PadicFunctionalAnalysis/`
- **Status**: done (2026-09-29) · **Depends on**: T045 · **Parallel**: no · **Type**: cleanup
- **Progress**: 2026-09-29 DONE — final sweep: 13 transitively redundant imports removed across 9 files (the build confirms each removal); every name listed in the module docstrings exists; runLinter clean on all twelve modules; `lake build PhD.TauCeti` passes (2639 jobs).
- Final sweep of the whole folder: naming, docstrings, import minimality (`lake exe shake`), module docstrings list the final declaration names, the README provenance table of the roadmap can be pointed at these files.
