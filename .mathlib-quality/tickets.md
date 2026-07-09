# Ticket Board — TateFredholm (nonarchimedean Fredholm theory over Banach–Tate rings)

## Summary
- Total: 63 tickets (1 structural + 46 proof/API + 15 cleanup + CLEANUP-FINAL)
- Open: 63 | Blocked: 0 | In Progress: 0 | Done: 0
- T038's API gap was decomposed 2026-07-09 (`decomposition.md`): sub-tickets T039–T046,
  T038 is now the assembly ticket.  Residue skeleton lives in the merged file §10
  (T001 routes it to `PhD/TateFredholm/Residue.lean`).
- Parallel capacity: ~3 workers at peak (after T001: T002, T003, T008, T012, T018,
  T023, T026, T033 are mutually independent)
- Statements below are the **canonical skeleton declarations** already present in the
  code (takeover mode): a ticket = "fill the sorry of the named declaration(s)".
  Signatures must not change without a B2 stop.  Docstrings in the file carry the
  source citations; sketches below expand them tactically.
- Sources: [Bel] = Bellaïche Eigenbook draft §II.1 (pages 54–64); [JN] =
  arXiv:1604.07739v4 §2.1 (pages 7–10); [Buz] = Buzzard Eigenvarieties §2.
  Full bibliography in `plan.md`.

## Tickets

### [T001] Split CompactOperatorsMerged.lean into PhD/TateFredholm/*
- **Status**: done (finished 2026-07-09; linear import chain Tate → OperatorNorm →
  Compact → ModelSpace → Matrix → Fredholm → Pr → Residue → BaseChange; Mathlib imports
  concentrated in Tate.lean; Test/CompactOperatorsMerged.lean kept as a re-exporting
  stub so old imports/build targets work; `lake build PhD.TateFredholm.BaseChange`
  clean, 54 sorries preserved exactly (2/5/5/5/8/8/3/11/7 per module))
- **File**: PhD/Test/CompactOperatorsMerged.lean → PhD/TateFredholm/{Tate,OperatorNorm,Compact,ModelSpace,Matrix,Fredholm,Pr,BaseChange}.lean
- **Depends on**: none
- **Parallel**: no (everything else depends on it)
- **Type**: structural
- **Description**: Mechanical move per plan.md §File Structure — no statement changes,
  no proof changes.  Preserve the module docstring (split the section-relevant parts
  into each file, keep the full dictionary in Tate.lean).  Add module imports in
  dependency order.  `lake build PhD.TateFredholm.BaseChange` must pass with exactly
  the current 43 sorries.  Leave the three parent blueprints untouched; leave a
  one-line pointer comment in Test/CompactOperatorsMerged.lean or delete it (worker's
  choice — record which).
- **Generality decision**: n/a (structural).

### [T002] PseudoUniformizer API (norm_pos, isMultiplicative_unit_iff, val_self)
- **Status**: open
- **File**: PhD/TateFredholm/Tate.lean
- **Depends on**: T001
- **Parallel**: yes
- **Type**: API lemmas

#### Statement
Fill the sorries of:
```lean
theorem PseudoUniformizer.norm_pos (ϖ : PseudoUniformizer A) : 0 < ‖(ϖ : A)‖
@[simp] theorem PseudoUniformizer.val_self (ϖ : PseudoUniformizer A) : ϖ.val (ϖ : A) = 1
```
and ADD (new declaration, [JN] p. 8 "a unit ϖ is multiplicative iff ‖ϖ⁻¹‖ = ‖ϖ‖⁻¹" —
present in the JN parent file, missing here; needed by T004):
```lean
theorem PseudoUniformizer.norm_inv (ϖ : PseudoUniformizer A) :
    ‖((ϖ.unit⁻¹ : Aˣ) : A)‖ = ‖(ϖ : A)‖⁻¹ := by sorry
```

#### Proof sketch
1. `norm_pos`: `A` is nontrivial (`‖1‖ = 1 ≠ 0` via `NormOneClass`, so `1 ≠ 0` —
   `norm_one`, `one_ne_zero` after `norm_pos_iff`); a unit is nonzero
   (`Units.ne_zero` needs `Nontrivial A`: derive `haveI := NormOneClass.nontrivial`?
   verify instance name, else prove inline from `‖1‖ = 1`); conclude `norm_pos_iff.2`.
2. `norm_inv`: apply `ϖ.isMultiplicative (↑ϖ.unit⁻¹)`; LHS is `‖(1 : A)‖ = 1`
   (`Units.mul_inv`, `norm_one`); solve `1 = ‖ϖ‖ * ‖ϖ⁻¹‖` for `‖ϖ⁻¹‖` by
   `eq_inv_of_mul_eq_one_right`-style real arithmetic (`field_simp` with
   `norm_pos.ne'`).
3. `val_self`: unfold `val`; `Real.log ‖ϖ‖⁻¹ = -Real.log ‖ϖ‖` (`Real.log_inv`);
   numerator `-Real.log ‖ϖ‖`; division gives 1 provided `Real.log ‖ϖ‖ ≠ 0`, which
   holds since `0 < ‖ϖ‖ < 1` (`Real.log_neg` gives `log < 0`).

#### Mathlib lemmas needed
`norm_pos_iff`, `norm_one`, `Units.mul_inv`, `Real.log_inv`, `Real.log_neg` (all
standard; verify `NormOneClass.nontrivial` instance name via loogle, else 2-line inline).

#### Sources
[JN] Def 2.1.2 + following remark (p. 7–8).

#### Generality decision
Any `[NormedRing A]`; no Tate/complete hypotheses.

### [T003] Operator-norm basic API over a normed ring (NEW declarations)
- **Status**: open
- **File**: PhD/TateFredholm/OperatorNorm.lean
- **Depends on**: T001
- **Parallel**: yes
- **Type**: API lemmas (fills the audit gap: nothing about `instNorm` is currently provable-from)

#### Statement
Add (new declarations, immediately after `norm_def`; hypotheses as in the section's
variables — `M N` Banach `R`-modules, no `IsTate` needed):
```lean
theorem opNorm_nonneg (u : M →L[R] N) : 0 ≤ ‖u‖ := by sorry
@[simp] theorem opNorm_zero : ‖(0 : M →L[R] N)‖ = 0 := by sorry
theorem opNorm_le_of_forall (u : M →L[R] N) {C : ℝ} (h0 : 0 ≤ C)
    (h : ∀ x, ‖u x‖ ≤ C * ‖x‖) : ‖u‖ ≤ C := by sorry
theorem opNorm_comp_le [IsTate R] {P : Type*} [NormedAddCommGroup P] [Module R P]
    [IsBoundedSMul R P] (f : N →L[R] P) (u : M →L[R] N) :
    ‖f.comp u‖ ≤ ‖f‖ * ‖u‖ := by sorry
```

#### Proof sketch
1. `opNorm_nonneg`: `Real.le_sInf`-side: `le_csInf` with set nonempty? — no: use
   `Real.sInf_nonneg` (every member is ≥ 0 by its first conjunct); handles the empty
   case (sInf ∅ = 0).
2. `opNorm_zero`: `0 ∈` the set (`norm_zero`, `zero_apply`); `csInf_le` with
   `BddBelow` (bounded below by 0 from the membership conjunct) gives `≤ 0`;
   combine with `opNorm_nonneg`.
3. `opNorm_le_of_forall`: `csInf_le` (same `BddBelow`) at the member `⟨h0, h⟩`.
4. `opNorm_comp_le`: `opNorm_le_of_forall` with `C = ‖f‖ * ‖u‖`
   (`mul_nonneg opNorm_nonneg opNorm_nonneg`); pointwise chain two `le_opNorm`
   (T005) — NOTE: `le_opNorm` needs `[IsTate R]`, hence the instance argument;
   `mul_assoc` + `mul_le_mul_of_nonneg_left`.  (If T005 is not yet done, this
   fourth lemma may be deferred into T011 — record in the board if so.)

#### Mathlib lemmas needed
`Real.sInf_nonneg`, `csInf_le`, `norm_zero`, `ContinuousLinearMap.zero_apply`,
`mul_nonneg`, `mul_le_mul_of_nonneg_left` (all standard order/real API).

#### Sources
[Bel] II.1.1 (the `sInf`/least-bound description of `|φ|`).

#### Generality decision
First three lemmas need NO Tate hypothesis (pure `sInf` bookkeeping) — state them
without `[IsTate R]`.  `opNorm_comp_le` needs `le_opNorm`, hence `[IsTate R]`.

### [T004] norm_pseudoUniformizer_smul
- **Status**: open
- **File**: PhD/TateFredholm/OperatorNorm.lean
- **Depends on**: T002
- **Parallel**: yes (with T003)
- **Type**: lemma

#### Statement
```lean
theorem norm_pseudoUniformizer_smul (ϖ : PseudoUniformizer R) (m : M) :
    ‖(ϖ : R) • m‖ = ‖(ϖ : R)‖ * ‖m‖
```

#### Proof sketch ([JN] Def 2.1.4 remark; [Bel] proof of Lemma II.1.12 first line)
1. `≤`: `norm_smul_le` (from `IsBoundedSMul`).
2. `≥`: write `m = (↑ϖ.unit⁻¹ : R) • ((ϖ : R) • m)` (`smul_smul`,
   `Units.inv_mul`, `one_smul`); then
   `‖m‖ ≤ ‖(↑ϖ.unit⁻¹ : R)‖ * ‖(ϖ:R) • m‖ = ‖ϖ‖⁻¹ * ‖(ϖ:R) • m‖` by
   `norm_smul_le` + T002's `norm_inv`; rearrange with `‖ϖ‖ > 0` (T002 `norm_pos`),
   `le_div_iff`/`mul_comm`.
3. `le_antisymm`.

#### Mathlib lemmas needed
`norm_smul_le`, `smul_smul`, `Units.inv_mul`, `one_smul`, `le_div_iff₀` (or
`div_le_iff₀`) — standard.

#### Sources
[JN] Definition 2.1.4, remark after ("if r is a multiplicative unit then ‖rm‖ = |r|.‖m‖").

#### Generality decision
Any Banach `R`-module `M` (no completeness needed); stated for a `PseudoUniformizer`
but the proof only uses "multiplicative unit" — if convenient, factor through a
`IsMultiplicative`-unit version and specialise (worker's choice; record).

### [T005] le_opNorm (continuity ⟹ boundedness over a Tate ring)
- **Status**: open
- **File**: PhD/TateFredholm/OperatorNorm.lean
- **Depends on**: T003, T004
- **Parallel**: no
- **Type**: lemma

#### Statement
```lean
theorem le_opNorm (u : M →L[R] N) (x : M) : ‖u x‖ ≤ ‖u‖ * ‖x‖
```

#### Proof sketch (Buzzard's ρ-trick, ϖ for ρ; [JN] Def 2.1.4, [Bel] II.1.1)
1. Obtain `ϖ` from `IsTate.nonempty_pseudoUniformizer`.
2. Show the bound set `{c | 0 ≤ c ∧ ∀ x, ‖u x‖ ≤ c * ‖x‖}` is **nonempty**: from
   `u.continuous` (`Metric.continuousAt_iff` at `0`, `map_zero`) get `δ > 0` with
   `‖y‖ ≤ δ → ‖u y‖ ≤ 1`.  Claim `C := (δ * ‖ϖ‖)⁻¹` works: given `x ≠ 0`
   (the `x = 0` case is trivial via `map_zero`), choose `n : ℤ` with
   `δ * ‖ϖ‖ < ‖ϖ‖ ^ n * ‖x‖ ≤ δ` — exists since `‖(ϖ^n) • x‖ = ‖ϖ‖^n * ‖x‖`
   (iterate T004 / `zpow` via the unit) and `0 < ‖ϖ‖ < 1` makes `n ↦ ‖ϖ‖^n * ‖x‖`
   a bi-infinite geometric family (`exists_zpow_between`-style: verify name via
   loogle `∃ n : ℤ, _ < _ ^ n ∧ _ ^ n ≤ _`; else derive from `Real.exists_zpow...`
   or hand-roll with `Int.le_floor` on `Real.log`).  Then
   `‖u x‖ = ‖ϖ‖^(-n) * ‖u ((ϖ^n) • x)‖ ≤ ‖ϖ‖^(-n) ≤ C * ‖x‖`.
3. Once nonempty: for any member `c`, `‖u x‖ ≤ c * ‖x‖`; conclude
   `‖u x‖ ≤ sInf S * ‖x‖` via `le_csInf`-dual reasoning: standard trick — show
   `∀ c ∈ S, ‖u x‖ ≤ c * ‖x‖` and use `Real.sInf` monotonicity
   (`le_csInf` on the set `{c * ‖x‖ | c ∈ S}` or directly:
   `Real.add_neg_lt_sInf`-free route: `csInf_le`-based ε-argument as in Mathlib's
   `ContinuousLinearMap.le_opNorm` proof — mirror it).
4. Mirror Mathlib's `Mathlib/Analysis/Normed/Operator/Basic.lean` proof of
   `le_opNorm` (read it first; only the nonemptiness input differs).

#### Mathlib lemmas needed
`Metric.continuousAt_iff`, `map_zero`, `zpow` norm lemmas, `csInf_le`, `le_csInf`;
integer-power sandwich lemma (name to verify via loogle — fallback: hand-roll, ~15
lines).  Read Mathlib's field-case proof for the sInf endgame pattern.

#### Sources
[JN] Definition 2.1.4 ("continuity ... is equivalent to boundedness", for R Tate);
[Buz] §2 p. 65 footnote (the ρ-trick); [Bel] II.1.1.

#### Generality decision
`[IsTate R]` required (this is the theorem that *needs* the pseudo-uniformizer;
false over a general normed ring).

### [T006] norm_add_le
- **Status**: open
- **File**: PhD/TateFredholm/OperatorNorm.lean
- **Depends on**: T003, T005
- **Parallel**: yes (with T007, T008)
- **Type**: lemma

#### Statement
```lean
theorem norm_add_le (u v : M →L[R] N) : ‖u + v‖ ≤ ‖u‖ + ‖v‖
```

#### Proof sketch
1. `opNorm_le_of_forall` with `C = ‖u‖ + ‖v‖` (`add_nonneg` of two `opNorm_nonneg`).
2. Pointwise: `‖(u+v) x‖ = ‖u x + v x‖ ≤ max ... ≤ ‖u x‖ + ‖v x‖` (plain triangle
   `norm_add_le` on `N` suffices; ultrametric not needed) then two `le_opNorm` and
   `add_mul`.

#### Mathlib lemmas needed
`norm_add_le` (on `N`), `add_mul`, `add_le_add` — standard.

#### Sources
[Bel] II.1.1. | #### Generality decision: `[IsTate R]` via T005.

### [T007] exists_lim_of_cauchySeq (Hom is Banach)
- **Status**: open
- **File**: PhD/TateFredholm/OperatorNorm.lean
- **Depends on**: T005, T006
- **Parallel**: yes (with T008)
- **Type**: lemma

#### Statement
```lean
theorem exists_lim_of_cauchySeq [CompleteSpace N] (u : ℕ → M →L[R] N)
    (hu : ∀ ε > 0, ∃ M₀, ∀ m n, M₀ ≤ m → M₀ ≤ n → ‖u m - u n‖ < ε) :
    ∃ v : M →L[R] N, Tendsto (fun n => ‖u n - v‖) atTop (𝓝 0)
```

#### Proof sketch ([Bel] II.1.1; standard completeness argument)
1. Pointwise: for each `x`, `(u n x)` is Cauchy in `N` (`le_opNorm` on `u m - u n`,
   `sub_apply`); `CompleteSpace N` gives a limit `v₀ x` (`cauchySeq_tendsto_of_complete`).
2. `v₀` is `R`-linear (limits of linear: `map_add`/`map_smul` pass to limits via
   `Tendsto.add`, `Tendsto.const_smul`, uniqueness of limits `tendsto_nhds_unique`).
3. `v₀` bounded: Cauchy ⟹ `‖u n‖` bounded (via `norm_add_le` chain); pointwise limit
   inherits the bound (`le_of_tendsto`); package as CLM with
   `LinearMap.mkContinuousOfExistsBound`-style (over a ring: continuity from
   boundedness is direct — `ε/C` argument, no field needed in this direction).
4. `‖u n - v‖ → 0`: for `n ≥ M₀(ε)`, pointwise `‖(u n - v) x‖ ≤ ε * ‖x‖`
   (`le_of_tendsto` on `m ↦ ‖(u n - u m) x‖`); `opNorm_le_of_forall` gives
   `‖u n - v‖ ≤ ε`; squeeze (`squeeze_zero`).

#### Mathlib lemmas needed
`cauchySeq_tendsto_of_complete`, `tendsto_nhds_unique`, `Tendsto.add`, `le_of_tendsto`,
`squeeze_zero` — standard.

#### Sources
[Bel] II.1.1; [JN] Def 2.1.4. | #### Generality: `[IsTate R]`, `[CompleteSpace N]` only.

### [T008] exists_preimage_norm_le — Open Mapping Theorem over a Banach–Tate ring
- **Status**: open
- **File**: PhD/TateFredholm/OperatorNorm.lean
- **Depends on**: T004
- **Parallel**: yes
- **Type**: theorem (Mathlib gap; substantial — budget a full session)

#### Statement
```lean
theorem exists_preimage_norm_le [CompleteSpace M] [CompleteSpace N]
    (f : M →L[R] N) (hf : Function.Surjective f) :
    ∃ C > 0, ∀ n : N, ∃ m : M, f m = n ∧ ‖m‖ ≤ C * ‖n‖
```

#### Proof sketch (Baire + ϖ-scaling; [Hub94, Lemma 2.4(i)] as cited by [JN]; mirror Mathlib's field proof)
1. Read Mathlib's `Mathlib/Analysis/Normed/Operator/Banach.lean` proof of
   `exists_preimage_norm_le` first; the plan is a transcription with the *only*
   field-use (rescaling into an annulus) replaced by ϖ-powers.
2. Baire: `N = ⋃ (k : ℕ), closure (f '' Metric.closedBall 0 k)`; by
   `nonempty_interior_of_iUnion_of_closed` (verified) some closure has interior;
   translate/scale to: `closedBall 0 1 ⊆ closure (f '' closedBall 0 c₀)` for some
   `c₀` — the scaling steps use `(ϖ : R)^n •`-multiplication and T004 in place of
   field scalars.
3. Iterate to remove the closure: given `n` with `‖n‖ ≤ 1`, build a geometric series
   of approximations (`‖ϖ‖`-geometric instead of `2⁻¹`-geometric); completeness of
   `M` sums it (needs "geometric-decay series converge": ultrametric or plain
   `summable_geometric` bound — `Summable.of_norm_bounded` +
   `summable_geometric_of_lt_one`).
4. General `n`: scale into the unit ball by ϖ-powers, apply, unscale; constant
   `C = c₀ * ‖ϖ‖⁻¹`-flavoured.

#### Mathlib lemmas needed
`nonempty_interior_of_iUnion_of_closed` (✓ verified `Topology/Baire/Lemmas.lean:245`),
`Summable.of_norm_bounded`, `summable_geometric_of_lt_one`, `Metric.closedBall`,
`IsClosed.closure_eq` etc.  Mirror-file: `Analysis/Normed/Operator/Banach.lean`.

#### Sources
[JN] Def 2.1.4 ("The open mapping theorem holds in this context; see [Hub94, Lemma
2.4(i)]"); [Bel] II.1.1 (OMT + quantitative corollary).

#### Generality decision
`[IsTate R]`, both modules complete.  This is new-to-Mathlib mathematics
(group/Tate-module OMT) — a candidate for eventual upstreaming; keep it self-contained.

### [CLEANUP-1] /cleanup on PhD/TateFredholm/OperatorNorm.lean (after T005)
- **Status**: open | **Depends on**: T003, T004, T005 | **Type**: cleanup
- Per-file cadence (3 proof tickets). Blocks T006–T008 pickup on this file.

### [T009] IsFiniteRank.isCompletelyContinuous + IsFiniteRank.add
- **Status**: open
- **File**: PhD/TateFredholm/Compact.lean
- **Depends on**: T003
- **Parallel**: yes
- **Type**: lemmas

#### Statement — fill sorries of
```lean
theorem IsFiniteRank.isCompletelyContinuous {u : M →L[R] N} (hu : IsFiniteRank u) :
    IsCompletelyContinuous u
theorem IsFiniteRank.add {u v : M →L[R] N} (hu : IsFiniteRank u) (hv : IsFiniteRank v) :
    IsFiniteRank (u + v)
```

#### Proof sketch
1. First: the skeleton already reduces to `‖u - u‖ < ε`; `sub_self` + `opNorm_zero`
   (T003) closes it.
2. `add`: witnesses `⟨Qu ⊔ Qv, hQu.sup hQv, _⟩`; range bound: `(u+v) m = u m + v m ∈ Qu ⊔ Qv`
   via `Submodule.add_mem_sup` + `Submodule.mem_sup_left/right` of `hle` memberships.

#### Mathlib lemmas needed
`sub_self`, `Submodule.FG.sup` (verify name: loogle `Submodule.FG _ → Submodule.FG _ →
Submodule.FG (_ ⊔ _)`), `Submodule.add_mem_sup`.

#### Sources
[Bel] after Def II.1.3 ("closed sub-module ... sum of two compact morphisms").
| #### Generality: no Tate needed for `add`; `isCompletelyContinuous` needs T003 only.

### [T010] isCompletelyContinuous_of_tendsto
- **Status**: open | **File**: PhD/TateFredholm/Compact.lean | **Depends on**: T006
- **Parallel**: yes | **Type**: lemma

#### Statement
```lean
theorem isCompletelyContinuous_of_tendsto (u : ℕ → M →L[R] N) (v : M →L[R] N)
    (hu : ∀ n, IsCompletelyContinuous (u n))
    (huv : Tendsto (fun n => ‖u n - v‖) atTop (𝓝 0)) :
    IsCompletelyContinuous v
```

#### Proof sketch
1. Given `ε > 0`: pick `n` with `‖u n - v‖ < ε/2` (`Metric.tendsto_atTop` on `huv`),
   then finite-rank `w` with `‖u n - w‖ < ε/2`.
2. `‖v - w‖ ≤ ‖v - u n‖ + ‖u n - w‖ < ε` via T006 (`norm_add_le` on
   `v - w = (v - u n) + (u n - w)`, `sub_add_sub_cancel`) and norm-of-neg
   (`‖v - u n‖ = ‖u n - v‖` — needs tiny helper `opNorm_neg`/`opNorm_sub_comm`:
   provable from `norm_def` symmetry pointwise (`norm_sub_rev` on values); add as
   private lemma).

#### Mathlib lemmas needed
`Metric.tendsto_atTop`, `sub_add_sub_cancel`, `norm_sub_rev` (pointwise) — standard.

#### Sources
[Bel] after Def II.1.3. | #### Generality: `[IsTate R]` via T006.

### [T011] IsCompletelyContinuous.comp_left / comp_right
- **Status**: open | **File**: PhD/TateFredholm/Compact.lean
- **Depends on**: T003 (incl. `opNorm_comp_le`), T005 | **Parallel**: yes | **Type**: lemmas

#### Statement — fill sorries of `IsCompletelyContinuous.comp_left` and `.comp_right`
(signatures as in skeleton).

#### Proof sketch ([Bel] Lemma II.1.4)
1. `comp_left`: given `ε`, handle `f = 0`-ish by cases on `‖f‖ = 0` vs `> 0`
   (if `‖f‖ = 0` then `‖f.comp u - f.comp v‖ = 0` for any `v` — or simpler: pick
   finite-rank `v` with `‖u - v‖ < ε / max ‖f‖ 1`); `f.comp v` finite rank by
   `IsFiniteRank.comp_left` (done); `f.comp u - f.comp v = f.comp (u - v)`
   (`ContinuousLinearMap.comp_sub`? verify name; else `ext` + `map_sub`);
   `opNorm_comp_le` bounds by `‖f‖ * ε/(max ‖f‖ 1) ≤ ε`.
2. `comp_right`: symmetric with `(u - v).comp f` and the mirrored
   `opNorm_comp_le` (state both directions in T003 if needed — record).

#### Mathlib lemmas needed
`ContinuousLinearMap.comp_sub` / `sub_comp` (verify names via loogle), `max` arithmetic.

#### Sources
[Bel] Lemma II.1.4 (p. 56). | #### Generality: `[IsTate R]`.

### [CLEANUP-2] /cleanup on PhD/TateFredholm/Compact.lean (final)
- **Status**: open | **Depends on**: T009, T010, T011 | **Type**: cleanup

### [T012] cSpace.norm_eq_iSup + norm_single_one
- **Status**: open
- **File**: PhD/TateFredholm/ModelSpace.lean
- **Depends on**: T001
- **Parallel**: yes
- **Type**: lemmas (foundation — unblocks most of the file)

#### Statement — fill sorries of
```lean
theorem cSpace.norm_eq_iSup (f : c(I, R)) : ‖f‖ = ⨆ i : I, ‖f i‖
@[simp] theorem cSpace.norm_single_one (i : I) : ‖single i (1 : R)‖ = 1
```

#### Proof sketch
1. `norm_eq_iSup`: `‖f‖ = ‖f.toBCF‖` by definition of the C₀ norm
   (`ZeroAtInftyContinuousMap.norm_toBCF_eq_norm`? verify; the norm instance is
   induced along `toBCF`, so `rfl`-adjacent); then
   `BoundedContinuousFunction.norm_eq_iSup_norm` (verify exact name via loogle
   `‖_‖ = ⨆ _, ‖_ _‖`).  Mind the `Ix I` vs `I` index (defeq).
2. `norm_single_one`: rewrite with (1); the family is `‖Pi.single i 1 j‖`;
   `ciSup` over it equals `1`: `le_antisymm` — `≤` via `ciSup_le` (each term `≤ 1`
   by cases `j = i` (`norm_one`) / `j ≠ i` (`norm_zero`, `zero_le_one`)); `≥` via
   `le_ciSup` at `j = i` (BddAbove from the same case analysis).

#### Mathlib lemmas needed
`BoundedContinuousFunction.norm_eq_iSup_norm` (verify), `ciSup_le`, `le_ciSup`,
`norm_one`, `norm_zero`.

#### Sources
[Bel] Def II.1.5 / Ex II.1.7; [JN] Def 2.1.5; blueprint Def 6.3.
| #### Generality: `NormOneClass` needed only for the second lemma.

### [T013] cSpace instances: IsBoundedSMul + IsUltrametricDist
- **Status**: open | **File**: PhD/TateFredholm/ModelSpace.lean | **Depends on**: T012
- **Parallel**: yes | **Type**: instances

#### Statement — fill the two instance sorries (`IsBoundedSMul R c(I, R)` via
`.of_norm_smul_le`, and `IsUltrametricDist c(I, R)`).

#### Proof sketch
1. Bounded smul: `norm_eq_iSup` both sides; pointwise `‖(r • f) i‖ = ‖r * f i‖ ≤
   ‖r‖ * ‖f i‖` (`norm_mul_le`); `ciSup_le` + `mul_le_mul_of_nonneg_left` +
   `le_ciSup` (BddAbove: bounded by `‖r‖ * ‖f‖`).  Watch: `(r • f) i = r * f i`
   needs the C₀ smul-apply simp lemma (`ZeroAtInftyContinuousMap.coe_smul`?
   verify; our FunLike is an `inferInstanceAs` alias — if simp lemmas don't fire,
   prove by `rfl`).
2. Ultrametric: `isUltrametricDist_of_forall_norm_add_le_max_norm` (constructor
   confirmed in `Mathlib/Analysis/Normed/Group/Ultra.lean:59`); pointwise
   `‖(f+g) i‖ ≤ max ‖f i‖ ‖g i‖` (`IsUltrametricDist.norm_add_le_max` on `R` —
   verify exact name in Ultra.lean) then `ciSup_le` + `le_max_iff`-casework against
   `le_ciSup`.

#### Mathlib lemmas needed
`isUltrametricDist_of_forall_norm_add_le_max_norm` (✓), `norm_mul_le`, ultrametric
add-lemma on `R` (verify name), `ciSup` API.

#### Sources
[Bel] Ex II.1.7; blueprint Lemma 6.5. | #### Generality: as stated.

### [T014] isONable_cSpace
- **Status**: open | **File**: PhD/TateFredholm/ModelSpace.lean | **Depends on**: T012
- **Parallel**: yes | **Type**: lemma (moderate: builds a reindexing isometry)

#### Statement
```lean
theorem isONable_cSpace {I : Type*} [DecidableEq I] : IsONable R c(I, R)
```

#### Proof sketch
1. `s := Set.range (fun i : I => cSpace.single i (1 : R))`; the map `i ↦ single i 1`
   is injective (evaluate at `i`: `single_apply_self` vs `single_apply_of_ne`,
   `one_ne_zero` from `NormOneClass` + nontriviality as in T002).
2. Get `e : I ≃ s` (`Equiv.ofInjective`).
3. Build `c(I, R) ≃ₗᵢ[R] c(s, R)` by reindexing along `e`: define both directions by
   `f ↦ f ∘ e.symm` / `g ↦ g ∘ e` (as C₀ maps on discrete spaces: continuity free,
   zero-at-infty transfers since `e` maps cofinite to cofinite —
   `Filter.comap`/`Tendsto.comp` with `Function.Injective.tendsto_cofinite`
   (verify name: loogle `Injective _ → Tendsto _ cofinite cofinite`)); linearity and
   `‖·‖`-preservation from `norm_eq_iSup` + `Equiv.iSup_congr`-style reindexing
   (`Equiv.iSup_comp`? verify).
4. Assemble `LinearIsometryEquiv.mk` from the linear equiv + norm preservation.

#### Mathlib lemmas needed
`Equiv.ofInjective`, `Function.Injective.tendsto_cofinite` (verify),
`ciSup` reindexing along an `Equiv` (verify: `Equiv.iSup_comp` or
`Function.Surjective.iSup_comp`).

#### Sources
[JN] Def 2.1.5 (implicit); [Bel] Ex II.1.7. | #### Generality: as stated.

### [CLEANUP-3] /cleanup on PhD/TateFredholm/ModelSpace.lean (final)
- **Status**: open | **Depends on**: T012, T013, T014 | **Type**: cleanup

### [T015] norm_eq_iSup_matrixCoeff
- **Status**: open | **File**: PhD/TateFredholm/Matrix.lean | **Depends on**: T005, T012, T018
- **Parallel**: yes | **Type**: lemma

#### Statement
```lean
theorem norm_eq_iSup_matrixCoeff [IsTate R] (u : c(I, R) →L[R] c(J, R)) :
    ‖u‖ = ⨆ j : J, ⨆ i : I, ‖matrixCoeff u j i‖
```

#### Proof sketch ([Buz] p. 65; [Bel] §II.1.3 "It is clear that |φ| = sup |a_{i,j}|")
1. `≥`: for each `i, j`: `‖matrixCoeff u j i‖ ≤ ‖u (single i 1)‖ ≤ ‖u‖ * 1`
   (coordinate `≤` sup via T012, then T005 + `norm_single_one`); pass to `ciSup_le`
   twice (BddAbove by `‖u‖`).
2. `≤`: `opNorm_le_of_forall` with `C = ⨆⨆...` — pointwise: expand
   `f = ∑' i, f i • single i 1` (HasSum: T018's criterion + `tendsto_cofinite f`;
   prove the expansion as a private lemma `hasSum_single_expansion` — evaluate
   coordinatewise, `tsum` of eventually-single family); then
   `u f = ∑' i, f i • u (single i 1)` (continuity of `u`, `HasSum.mapL`? verify:
   `ContinuousLinearMap.hasSum`); coordinate `j` of a convergent sum is bounded by
   `sup_i ‖f i‖‖a_{ij}‖ ≤ C * ‖f‖` via the ultrametric `norm_tsum_le`-analogue
   (private lemma from T018's toolkit).

#### Mathlib lemmas needed
`ContinuousLinearMap.hasSum` (verify), `tsum` bounds; T018 toolkit.

#### Sources
[Buz] p. 65; [Bel] §II.1.3. | #### Generality: `[IsTate R]`.

### [T016] truncation: well-definedness + norm bound + finite rank
- **Status**: open | **File**: PhD/TateFredholm/Matrix.lean | **Depends on**: T012
- **Parallel**: yes | **Type**: def-completion + lemmas

#### Statement — fill the 4 inner sorries of `truncation` and the sorries of
`norm_truncation_apply_le`, `isFiniteRank_truncation` (signatures in skeleton).

#### Proof sketch
1. zero-at-infty: the truncated family is eventually (cofinitely) equal to the
   pointwise-dominated-by-`f`... simplest: `Tendsto.congr'`-squeeze — off `S` it's
   `f i` truncated... actually the truncation is `0` OFF `S`ᶜ? No: it's `f i` on `S`,
   `0` off `S`; since `S` finite, the function is eventually `0` — cofinite-eventually
   equal to `0` (`Finset.eventually_cofinite_notMem S` then `if_neg`);
   `Tendsto.congr' tendsto_const_nhds` as in `single`.
2. `map_add'`/`map_smul'`: `DFunLike.ext` on C₀ + `if`-push (`apply_ite`); the
   coe-apply is `rfl`-transparent (pattern proven in `single_apply_self`).
3. `cont`: linear + bounded ⟹ continuous without field:
   `AddMonoidHomClass.continuous_of_bound`-style — over a ring use
   `(truncation S).toLinearMap` with `LipschitzWith` from step 4:
   `LipschitzWith.continuous` on `fun f => truncation S f` with constant 1
   (`LipschitzWith.of_dist_le_mul`, `dist_eq_norm`, and step 4 applied to `f - g`
   using linearity already proven).
4. `norm_truncation_apply_le`: T012 both sides; termwise
   `‖if _ then f i else 0‖ ≤ ‖f i‖` (`if`-cases, `norm_zero`, `norm_nonneg`);
   `ciSup_le`/`le_ciSup`.
5. `isFiniteRank_truncation`: `Q := Submodule.span R (Finset.image (fun i =>
   single i (1:R)) S : Set _)` — `Submodule.fg_span` of a finite set
   (`Set.Finite.fg`? verify: `Submodule.fg_span (Set.toFinite _)`); range bound:
   `truncation S f = ∑ i ∈ S, f i • single i 1` (finite sum — prove by `ext j`,
   `Finset.sum_apply`-analogue + `single_apply` case analysis), each summand in the
   span (`Submodule.smul_mem`, `Submodule.subset_span`).

#### Mathlib lemmas needed
`Finset.eventually_cofinite_notMem` (✓ exists, `Order/Filter/Cofinite.lean:90`),
`apply_ite`, `LipschitzWith.of_dist_le_mul`, `Submodule.fg_span`, `Submodule.smul_mem`.

#### Sources
[Bel] §II.1.3 (π_S). | #### Generality: no Tate needed.

### [T017] exists_truncation_near ([Bel] Lemma II.1.8)
- **Status**: open | **File**: PhD/TateFredholm/Matrix.lean | **Depends on**: T008, T016
- **Parallel**: no | **Type**: theorem

#### Statement — as in skeleton (`P.FG`, `∃ S, ∀ p ∈ P, ‖truncation S p - p‖ ≤ ε * ‖p‖`).

#### Proof sketch (transcribe [Bel] Lemma II.1.8's proof, p. 57, verbatim structure)
1. From `hP` get generators; build the continuous surjection
   `π : (Fin r → R) →L[R] P`?? — the skeleton keeps `P` a submodule; work with
   the induced Banach structure on `P` (closed? NOT assumed — [Bel] works with the
   surjection onto the *module* `P` with its subspace norm; mirror: define
   `π : (Fin r → R) → c(I,R)` by `x ↦ ∑ k, x k • gen k`, linear + continuous
   (finite sum), with image exactly `P`'s carrier... adapt: apply T008's OMT to
   `π` viewed into `closure`? — [Bel] applies OMT to `Aʳ → P`; `P` must be complete
   for OMT: [Bel] assumes `P` finite hence gets completeness from the canonical
   topology remark.  **Worker note**: if completeness of `P` blocks, follow [Bel]
   exactly: he uses the open mapping theorem for the surjection `Ar → P` where `P`
   carries the subspace norm and is complete *because finite over complete `R` via
   the canonical-topology theory* — if that machinery is missing, STOP with B2 and
   propose adding hypothesis `IsClosed (P : Set c(I,R))` (source-faithful variant:
   [Buz]/[JN] only ever apply this with closed/finite-free `P`).
2. `Fin r → R` has basis `eₖ`; choose `S` with `‖truncation S (π eₖ) - π eₖ‖ ≤ ε/c`
   for all `k` (finitely many; each `π eₖ ∈ c(I,R)` and truncations converge
   pointwise-in-norm: private lemma `tendsto_truncation_id` — `norm_eq_iSup` of the
   tail, from `tendsto_cofinite`).
3. For `p = π x` with `‖x‖ ≤ c‖p‖` (OMT): `‖truncation S p - p‖ =
   ‖∑ k, x k • (truncation S (π eₖ) - π eₖ)‖ ≤ max_k ‖x k‖ * ε/c ≤ ε‖p‖`
   (ultrametric finite-sum bound — `IsUltrametricDist` finset lemma, verify name).

#### Mathlib lemmas needed
Ultrametric finset-sum bound (verify in `Ultra.lean`), `Pi` norm API on `Fin r → R`.

#### Sources
[Bel] Lemma II.1.8 (p. 57), including its OMT usage.  **Verbatim source quote** (p. 57):
"Since P is finite, there exists a surjective continuous morphism π : Ar → P. By the
open mapping theorem, there is a constant c > 0 such that for every p ∈ P, there
exists m ∈ Ar such that π(m) = p and |m| ≤ c|p|."
| #### Generality: `[IsTate R]` (through OMT).

### [CLEANUP-4] /cleanup on PhD/TateFredholm/Matrix.lean (after T017)
- **Status**: open | **Depends on**: T015, T016, T017 | **Type**: cleanup

### [T018] Ultrametric summability criterion (NEW, Mathlib gap)
- **Status**: open
- **File**: PhD/TateFredholm/Tate.lean
- **Depends on**: T001
- **Parallel**: yes
- **Type**: API lemmas (load-bearing for T015, T019, T022)

#### Statement (new declarations; general complete ultrametric groups)
```lean
theorem summable_of_tendsto_cofinite {ι E : Type*} [NormedAddCommGroup E]
    [IsUltrametricDist E] [CompleteSpace E] {f : ι → E}
    (hf : Tendsto f cofinite (𝓝 0)) : Summable f := by sorry
theorem norm_tsum_le_iSup {ι E : Type*} [NormedAddCommGroup E]
    [IsUltrametricDist E] [CompleteSpace E] {f : ι → E}
    (hf : Tendsto f cofinite (𝓝 0)) : ‖∑' i, f i‖ ≤ ⨆ i, ‖f i‖ := by sorry
```

#### Proof sketch
1. `summable_of_tendsto_cofinite`: `summable_iff_vanishing_norm` (✓ verified,
   `Analysis/Normed/Group/InfiniteSum.lean`): need `∀ ε > 0, ∃ s : Finset ι,
   ∀ t disjoint from s, ‖∑ i ∈ t, f i‖ < ε`; from `hf` (via
   `Filter.eventually_cofinite`) all but finitely many `i` have `‖f i‖ < ε` —
   take `s` = that finite exceptional set; bound the disjoint-sum by the
   ultrametric finset-sum lemma (`IsUltrametricDist.norm_sum_le_max`-style;
   verify exact name/shape in `Analysis/Normed/Group/Ultra.lean`, nnnorm forms
   confirmed present — if only nnnorm exists, coerce).
2. `norm_tsum_le_iSup`: `le_of_tendsto` on partial sums (`HasSum.tendsto_sum_nat`-free:
   use `(hf.summable).hasSum` and `Filter.Tendsto` along `atTop (Finset ι)`), each
   partial sum bounded by the finset ultrametric bound `≤ ⨆ i, ‖f i‖`
   (BddAbove: `⊔` bound needs care if `‖f ·‖` unbounded — it isn't: cofinite decay +
   finitely many exceptions; add BddAbove as a step).

#### Mathlib lemmas needed
`summable_iff_vanishing_norm` (✓), `Filter.eventually_cofinite` (✓),
ultrametric finset bound (verify name), `le_of_tendsto`.

#### Sources
[Bel] §II.1.5 footnote 1 (p. 56): "When the sequence (mᵢ) converges to 0, it is easy
to see that the sequence (∑_{i∈J} mᵢ) converges to some limit"; [JN] p. 9 implicit.
| #### Generality: any complete ultrametric `NormedAddCommGroup` — candidate for
mathlib upstreaming.

### [T019] exists_coeffEquiv
- **Status**: open | **File**: PhD/TateFredholm/Matrix.lean | **Depends on**: T012, T015, T018
- **Parallel**: yes | **Type**: theorem (chunky)

#### Statement — as in skeleton (`∃ φ : (c(I,R) →L[R] N) ≃ₗ[R] (Ix I →ᵇ N), ∀ u, ‖φ u‖ = ‖u‖`).

#### Proof sketch ([Bel] §II.1.3, [Buz] p. 65)
1. Forward map `u ↦ ⟨fun i => u (single i 1), bounded by ‖u‖⟩` (BCF: bound from
   T005 + `norm_single_one`); linear in `u` (ext).
2. Inverse: given bounded family `g`, define `u f := ∑' i, f i • g i` — summable by
   T018 (`‖f i • g i‖ ≤ ‖f i‖ * ‖g‖ → 0` cofinitely, `IsBoundedSMul`); linearity via
   `tsum_add`/`tsum_smul` (needs `Summable` sides — from T018); continuity: bound
   `‖u f‖ ≤ ‖g‖ * ‖f‖` by `norm_tsum_le_iSup` (T018) + termwise, then Lipschitz as
   in T016 step 3.
3. Left/right inverse: evaluate at `single i 1` (tsum collapses:
   `tsum_eq_single` — verify name) / expansion of `f` (private lemma from T015).
4. Norm equality: `≤` both ways (step 1 bound; step 2 bound + `le_opNorm`-style at
   `single`s), `le_antisymm`.

#### Mathlib lemmas needed
`tsum_eq_single` (verify), `tsum_add`, `BoundedContinuousFunction` constructor API.

#### Sources
[Bel] §II.1.3 (p. 56): "Conversely every matrix (a_{i,j}) ... whose coefficients are
bounded, defines an element φ ∈ Hom_R(M,N)." | #### Generality: `[IsTate R]` (via T005).

### [T020] isCompletelyContinuous_iff_rowNorm — the Noetherian-free criterion
- **Status**: open | **File**: PhD/TateFredholm/Matrix.lean | **Depends on**: T015, T016, T017
- **Parallel**: no | **Type**: theorem (KEY)

#### Statement — as in skeleton.

#### Proof sketch (transcribe [Bel] Prop II.1.9, p. 57; ϖ replaces nothing — proof is field-free given T017)
1. (⇐) Given row decay: `π_S ∘ u` is finite rank (T016 + `IsFiniteRank.comp_right`-
   analogue: `(truncation S).comp u` — comp_left with roles: truncation∘u has range
   in truncation's f.g. target: use `isFiniteRank_truncation.comp_right u`);
   `‖π_S∘u − u‖ =` sup of rows off `S` (T015 applied to the difference; matrix of
   `π_S∘u − u` computes by `truncation_apply`) → choose `S` from the decay.
2. (⇒) Given `ε`: finite-rank `v`, `‖u−v‖ < ε`; T017 on the f.g. module containing
   `range v` gives `S` with `‖π_S∘v − v‖ ≤ ε` (apply pointwise bound to `v f`,
   `‖v f‖ ≤ ‖v‖‖f‖`); ultrametric triangle (three-term, as [Bel] writes it):
   `‖π_S∘u − u‖ ≤ max(‖π_S∘(u−v)‖, ‖π_S∘v − v‖, ‖v−u‖) ≤ max(ε,ε,ε)` using
   `norm_truncation_apply_le`-derived `‖π_S∘w‖ ≤ ‖w‖`; conclude rows off `S` are
   `≤ ε` via T015 again.

#### Mathlib lemmas needed
(project lemmas T015–T017; ultrametric max-triangle on our opNorm — derive from
pointwise `IsUltrametricDist` on `c(J,R)` + `opNorm_le_of_forall`).

#### Sources
[Bel] Prop II.1.9 + Scholium II.1.10 (p. 57); [JN] Def 2.1.5 (their Noetherian
hypothesis is NOT used on this route — that's the point; record in docstring).

#### Generality decision
`[IsTate R]` only.  If the proof genuinely needs Noetherian anywhere, that is a B2
STOP (it would falsify the merge thesis) — do not add the hypothesis silently.

### [T021] tendsto_truncation_comp
- **Status**: open | **File**: PhD/TateFredholm/Matrix.lean | **Depends on**: T020
- **Parallel**: yes | **Type**: lemma
- **Sketch**: extract from T020's (⇒) argument: for `ε` get `S₀`; for `S ⊇ S₀`
  monotonicity `‖π_S∘u − u‖ ≤ ‖π_{S₀}∘u − u‖`-style (rows off `S` ⊆ rows off `S₀`;
  via T015 on differences); package as `Filter.tendsto_atTop` on `Finset J` with
  `Finset.le_iff_subset`.  Mathlib: `tendsto_atTop_of_eventually_le`-family.
- **Sources**: [Bel] Scholium II.1.10. | **Generality**: `[IsTate R]`.

### [CLEANUP-5] /cleanup on PhD/TateFredholm/Matrix.lean (final)
- **Status**: open | **Depends on**: T019, T020, T021 | **Type**: cleanup

### [T022] summable_minor (+ private Hadamard bound)
- **Status**: open | **File**: PhD/TateFredholm/Fredholm.lean | **Depends on**: T018, T020
- **Parallel**: yes | **Type**: theorem

#### Statement — as in skeleton; ADD private helper:
```lean
private theorem norm_minor_le [IsTate R] (u : c(I, R) →L[R] c(I, R)) (S : Finset I) :
    ‖minor u S‖ ≤ ∏ j ∈ S, rowNorm u j := by sorry
```

#### Proof sketch ([Bel] estimate (II.1.1), p. 59; [Buz] p. 67 recipe)
1. Hadamard: `Matrix.det_apply` expands into `∑ σ, sign • ∏`; each monomial:
   `‖∏_{i∈S} a_{σ(i),i}‖ ≤ ∏ ‖a‖ ≤ ∏_j rowNorm u j` (`norm_prod_le`-chain:
   `norm_mul_le` induction / `Finset.prod_le_prod` with nonneg); the signed sum is
   ultrametrically bounded by the max monomial (ultrametric finset bound; `zsmul`
   norm: `‖(±1 : ℤ) • x‖ = ‖x‖` — `norm_zsmul`-of-unit or case on sign).
2. Summability of `S ↦ minor u S` over `{S // S.card = n}`: T018's criterion —
   given `ε`, row decay (T020 applied to `hu`) gives finite `J₀` with
   `rowNorm u j < ε'` off `J₀`; any `S ⊄ J₀` picks up a factor `< ε'`, others
   bounded by `M := max over J₀` (or `‖u‖`): `‖minor u S‖ ≤ M^{n-1} ε'`; only
   finitely many `S ⊆ J₀` of card `n` (`Set.Finite.subset` on powerset —
   `Finset.powersetCard` finiteness); choose `ε' = ε / max(M,1)^{n-1}`; conclude
   cofinite smallness, apply `summable_of_tendsto_cofinite`.

#### Mathlib lemmas needed
`Matrix.det_apply` (✓ standard), `Finset.prod_le_prod`, `Finset.powersetCard`
finiteness, T018.

#### Sources
[Bel] (II.1.1) p. 59 — verbatim: "|c_S| ≤ |φ|^{|S∩I₀|} ε^{|S−(S∩I₀)|} since each term
a_{S,σ} of the sum defining c_S is a product of |S| factors a_{iσ(i)}, all of them of
norm ≤ |φ|, and those with σ(i) ∉ I₀ of norm ≤ ε."
| #### Generality: `[IsTate R]`, no Noetherian (contrast [JN]).

### [T023] charCoeff_zero
- **Status**: open | **File**: PhD/TateFredholm/Fredholm.lean | **Depends on**: T001
- **Parallel**: yes | **Type**: lemma
- **Sketch**: the index `{S : Finset I // S.card = 0}` is `Unique` (only `∅`:
  `Finset.card_eq_zero`); `tsum_eq_single`/`tsum_unique` (verify name) collapses;
  `minor u ∅` is `Matrix.det` of the empty matrix `= 1` (`Matrix.det_isEmpty` —
  needs `IsEmpty (↥(∅:Finset I))` ✓ `Finset.isEmpty_coe_sort`? verify); `pow_zero`,
  `one_mul`.
- **Mathlib**: `tsum_unique` / `Matrix.det_isEmpty` (verify names). |
  **Sources**: [Bel] p. 59 "c₀ = 1". | **Generality**: none extra.

### [T024] charPowerSeries_isEntire
- **Status**: open | **File**: PhD/TateFredholm/Fredholm.lean | **Depends on**: T022
- **Parallel**: yes | **Type**: theorem
- **Sketch** ([Bel] Lemma II.1.14, p. 59 — transcribe): fix `C > 0`; set
  `ε = min (1/(2C)) 1`, get `I₀` from row decay; for `n > |I₀|`:
  `‖cₙ‖ ≤` (norm_tsum_le_iSup from T018 + T022's per-minor bound)
  `≤ max(1,M)^{|I₀|} ε^{n−|I₀|}`, so `‖cₙ‖Cⁿ ≤ D/2ⁿ` with
  `D := max(1,M)^{|I₀|} ε^{-|I₀|}` — `squeeze_zero` against geometric
  (`tendsto_pow_atTop_nhds_zero_of_lt_one`).  Watch the `(-1)^n` factor:
  `norm_neg_one_pow`-style `‖(-1)^n * x‖ ≤ ‖x‖` (norm_mul_le + `norm_one`-of-`±1`:
  needs `‖(-1:R)‖ = 1` — from `NormOneClass` + ultrametric? Actually `‖-1‖ = ‖1‖ = 1`
  by `norm_neg`).
- **Mathlib**: `tendsto_pow_atTop_nhds_zero_of_lt_one` (verify exact name),
  `squeeze_zero`, `norm_neg`. | **Sources**: [Bel] Lemma II.1.14 (verbatim proof
  transcribed in docstring). | **Generality**: `[IsTate R]`.

### [T025] norm_charCoeff_sub_le (quantitative Lipschitz)
- **Status**: open | **File**: PhD/TateFredholm/Fredholm.lean | **Depends on**: T022
- **Parallel**: yes | **Type**: theorem
- **Sketch** ([Bel] Lemma II.1.15, p. 59 — transcribe): private telescoping lemma:
  for tuples with `‖aₖ‖,‖bₖ‖ ≤ B`: `‖∏a − ∏b‖ ≤ B^{m−1} max ‖aₖ−bₖ‖`
  (`Finset.prod` induction, ultrametric max on the telescope); apply per-monomial
  with `B = max ‖u‖ ‖v‖` (entries bounded by opNorm: from T015 `≥` direction),
  `‖a−b‖ ≤ ‖u−v‖` (matrixCoeff is evaluation: linear in `u`, bound by T005 chain);
  sum over `σ` and tsum over `S` ultrametrically (T018 `norm_tsum_le_iSup`).
- **Mathlib**: `Finset.prod` induction API. | **Sources**: [Bel] Lemma II.1.15 —
  verbatim: "|a_{S,σ} − a'_{S,σ}| ≤ max(|φ|,|φ'|)^{|S|−1}|φ−φ'|". |
  **Generality**: `[IsTate R]`.

### [T026] charCoeff_eq_det_coeff
- **Status**: open | **File**: PhD/TateFredholm/Fredholm.lean | **Depends on**: T023
- **Parallel**: yes | **Type**: theorem
- **Sketch** ([Bel] (II.1.2), p. 60): minors over `S' ⊄ S` vanish (a row `j ∉ S` is
  zero by `hS` → `Matrix.det_eq_zero_of_row_eq_zero`); tsum reduces to the finite
  sum over `{S' ⊆ S}` (`tsum_eq_sum` — verify, needs vanishing off a finset:
  `tsum_eq_sum` exists); RHS: expand `Matrix.det (1 - X • M)` coefficientwise —
  standard char-poly coefficient identity: `det(1 − X·M) = ∑_k (−1)^k e_k(minors) X^k`;
  if Mathlib's `Matrix.charpoly` API (`Matrix.charpoly_coeff_eq...`? or
  `Polynomial.coeff_det...`) doesn't provide principal-minor coefficients directly,
  prove by `Matrix.det_apply` on the polynomial matrix + `Polynomial.coeff_prod`
  bookkeeping (moderate; budget accordingly; check
  `Mathlib/LinearAlgebra/Matrix/Charpoly` for `coeff` lemmas first — loogle
  `Matrix.charpoly _ .coeff`).
- **Sources**: [Bel] (II.1.2) p. 60. | **Generality**: no compactness/Tate.

### [CLEANUP-6] /cleanup on PhD/TateFredholm/Fredholm.lean (after T026)
- **Status**: open | **Depends on**: T022, T023, T024, T025, T026 | **Type**: cleanup

### [CLEANUP-ALL-1] /cleanup-all before the milestone
- **Status**: open | **Depends on**: all open proof tickets T002–T026 | **Type**: cleanup
- Pre-milestone project-wide pass (cadence rule 3).

### [T027] charPowerSeries_comm — the trace property (MILESTONE)
- **Status**: open | **File**: PhD/TateFredholm/Fredholm.lean
- **Depends on**: T011, T021, T025, T026, CLEANUP-ALL-1 | **Parallel**: no | **Type**: theorem

#### Statement — as in skeleton.

#### Proof sketch (transcribe [Bel] Prop II.1.17, pp. 60–61, faithfully)
1. Both composites compact: T011.
2. Reduce to `u` truncated: `π_S∘u → u` (T021); LHS/RHS coefficients are continuous
   in the operator (T025 + `‖(π_S∘u)∘v − u∘v‖ ≤ ...` via `opNorm_comp_le`);
   coefficientwise limits (`tendsto_nhds_unique` after passing both sides to the
   limit) — so WLOG `u = π_S∘u` (rows supported on `S`).
3. Reduce to `v` truncated similarly on the other side ([Bel] uses `π_{S'} u`-inner
   truncation — follow his exact two-step: first fix `u` truncated, then
   `det(1−Tπ_{S'}vu) = det(1−Tuπ_{S'}v)` for each `S'` by step 4, then limit in `S'`).
4. Finite case: both sides are `charCoeff_eq_det_coeff` polynomials (T026;
   row-supported hypotheses hold by construction — compute `matrixCoeff` of the
   composites); conclude by `Matrix.det_one_sub_mul_comm` (✓ verified,
   `SchurComplement.lean:410`) applied to the polynomial matrices `X•A`, `B`
   (associativity bookkeeping: `(X•A)*B = X•(A*B)` — `Matrix.smul_mul`).
5. Assemble: `PowerSeries.ext` + coefficient limits.

#### Mathlib lemmas needed
`Matrix.det_one_sub_mul_comm` (✓), `Matrix.smul_mul`, `tendsto_nhds_unique`,
`PowerSeries.ext`.

#### Sources
[Bel] Prop II.1.17 (pp. 60–61) — verbatim structure quoted in the file's docstring;
(II.1.3) p. 60 for the finite case.

#### Generality decision
`[IsTate R]`, no Noetherian.  This is the theorem every invariance statement feeds
from — do not weaken to isometric φ.

### [T028] charPowerSeries_conj
- **Status**: open | **File**: PhD/TateFredholm/Fredholm.lean | **Depends on**: T027
- **Parallel**: yes | **Type**: corollary
- **Sketch** ([Bel] Cor II.1.18): apply T027 with `u' := (φ:...).comp u` (compact by
  T011) and `v := (φ.symm : ...)`: LHS = the conjugate, RHS = `φ.symm ∘ (φ ∘ u)`
  `= u` (`ContinuousLinearEquiv.symm_comp_self`-simp + `comp_assoc`); pure rewriting.
  Real proof expected (~10 lines) — attempt without sorry.
- **Sources**: [Bel] Cor II.1.18 p. 61. | **Generality**: `[IsTate R]`.

### [T029] charPowerSeries_extendZero
- **Status**: open | **File**: PhD/TateFredholm/Fredholm.lean | **Depends on**: T022, T023
- **Parallel**: yes | **Type**: theorem
- **Sketch** ([Buz] pp. 72–73; [Bel] §II.1.6): coefficientwise; minors of `v` over
  `S ⊆ I⊕J` meeting `inr(J)` have a zero row (`hJrow`) → det 0
  (`Matrix.det_eq_zero_of_row_eq_zero`); reindex the surviving subsets
  `{S ⊆ inl(I)}` ≃ `{Finset I}` (`Finset.map` along `Sum.inl` embedding —
  `Equiv` between the card-n subtypes; `tsum_eq_tsum_of_ne_zero_bij` — verify name);
  matched minors equal by `hII` (`Matrix.det_congr`-of-entries: `Matrix.det` of
  equal matrices — `congr`/`Matrix.ext`).
- **Mathlib**: `Matrix.det_eq_zero_of_row_eq_zero` (verify exact name — loogle),
  `tsum_eq_tsum_of_ne_zero_bij` (verify), `Function.Embedding.sumInl`.
- **Sources**: [Buz] pp. 72–73. | **Generality**: `[IsTate R]` for summability only.

### [CLEANUP-7] /cleanup on PhD/TateFredholm/Fredholm.lean (final)
- **Status**: open | **Depends on**: T027, T028, T029 | **Type**: cleanup

### [T030] HasPr.exists_lift
- **Status**: open | **File**: PhD/TateFredholm/Pr.lean | **Depends on**: T008, T019
- **Parallel**: yes | **Type**: theorem
- **Sketch** ([Bel] Ex II.1.19 forward, p. 61): `⟨s, ι, π, hπι⟩ := hP`; suffices to
  lift `α ∘ π : c(s,R) →L N` to `β₀ : c(s,R) →L M` (then `β := β₀ ∘ ι` works:
  `f∘β₀∘ι = α∘π∘ι = α` by `hπι`); for the model space: OMT (T008) on `f` gives
  `C`; lift each `α(π(e_i))` with norm `≤ C‖α∘π‖` (bounded family); assemble via
  T019's inverse construction.
- **Sources**: [Bel] Ex II.1.19 (p. 61). | **Generality**: `[IsTate R]`.

### [T031] HasPr.projective
- **Status**: open | **File**: PhD/TateFredholm/Pr.lean | **Depends on**: T030
- **Parallel**: no | **Type**: theorem
- **Sketch** ([Bel] Prop II.1.20, p. 61 — transcribe): `Module.Finite` gives a
  surjection `Rʳ →ₗ P`; upgrade to CLM (finite free source: continuity of linear maps
  from `Fin r → R` — finite sums of bounded maps; private helper); it is surjective;
  T030 with `α = id` gives a continuous section; `Module.Projective.of_split`
  (verify name: loogle `Function.Surjective _ → Module.Projective` /
  `Module.Projective.of_split`) from the linear split.
- **Mathlib**: `Module.Projective.of_split` (verify), `Module.Finite.exists_fin`.
- **Sources**: [Bel] Prop II.1.20 — verbatim: "choose a surjective continuous map
  f : Ar → P and apply Exercise II.1.19 to α = Id_P... hence P ≃ β(P) is a direct
  summand of Ar and is therefore projective." | **Generality**: `[IsTate R]`.

### [T032] finite_projective_of_one_sub_compact_nilpotent (the Noetherian statement)
- **Status**: open | **File**: PhD/TateFredholm/Pr.lean | **Depends on**: T021, T030, T031
- **Parallel**: no | **Type**: theorem (chunky — budget a full session)
- **Sketch** (transcribe [Bel] Prop II.1.21, p. 62 — follow verbatim, it is subtle):
  expand `(1−u)ⁿ = 0` binomially → `id = -(∑_{k≥1} C(n,k) (-u)^k)` = compact
  (T011 + T009.add closure); embed `P ⊴ c(s,R)` via `hP`; extend `id_P` by zero to
  compact `ũ = ι∘π`-conjugate; Scholium (T021): finite-rank `q` with
  `‖ũ − q‖ < 1/‖π‖`-controlled; then `π∘q∘ι : P → P` is invertible
  (`‖id − π q ι‖ < 1` + geometric-series inverse — needs completeness of the
  operator ring: T007-derived Neumann series, private lemma); hence `P` injects in
  `q`'s f.g. image; `IsNoetherianRing` closes f.g. (`Submodule.fg_of_...`
  `IsNoetherian.noetherian`); projective by T031.
- **Sources**: [Bel] Prop II.1.21 (p. 62), full verbatim proof in the extracted text.
- **Generality**: `[IsTate R] [IsNoetherianRing R]` — the ONLY Noetherian ticket.

### [CLEANUP-8] /cleanup on PhD/TateFredholm/Pr.lean (final)
- **Status**: open | **Depends on**: T030, T031, T032 | **Type**: cleanup

### [T033] norm_le_pow_of_equiv (JN Lemma 2.1.6)
- **Status**: open | **File**: PhD/TateFredholm/BaseChange.lean | **Depends on**: T002
- **Parallel**: yes | **Type**: theorem
- **Sketch** (transcribe [JN] Lemma 2.1.6 proof, p. 9, verbatim): equivalence
  (`he'` continuity at 0) gives `D₁ < 1` with `‖e a‖ ≤ D₁ → ‖a‖ ≤ 1`; pick `m` with
  `‖e (ϖ^m)‖ ≤ D₁` (`ϖ` top-nilpotent: `‖(ϖ:R)^m‖ = ‖ϖ‖^m → 0`, continuity of `e`);
  `C₁ := ‖ϖ‖^{-m}` via multiplicativity (T004-style scaling on `R` itself); second
  bound: `n := ⌈log‖e a‖ / log‖e(ϖ^m)‖⁻¹⌉`, scale `a` by `ϖ^{mn}` into the π-unit
  ball, unscale: `‖a‖ ≤ C₁^{n+1} ≤ C₂ ‖e a‖^s` with
  `s := (log (C₁‖e(ϖ^m)‖⁻¹))⁻¹`, `C₂ := C₁²` — real-exponent algebra via
  `Real.rpow_natCast`, `Real.rpow_le_rpow_left_iff`, `Real.log` monotonicity.
- **Mathlib**: `Real.rpow` API, `Int.ceil` bounds (`Int.le_ceil`, `Int.ceil_le`).
- **Sources**: [JN] Lemma 2.1.6 (p. 9) — proof extracted verbatim in planning notes;
  note their footnote: this is the erratum statement — implement THIS version.
- **Generality**: as stated (bicontinuous ring iso).

### [T034] norm_comparison_of_common_uniformizer (JN Lemma 2.1.7)
- **Status**: open | **File**: PhD/TateFredholm/BaseChange.lean | **Depends on**: T033
- **Parallel**: no | **Type**: theorem
- **Sketch** (transcribe [JN] Lemma 2.1.7, pp. 9–10): same scaling with the common
  `ϖ`: `n` s.t. `‖ϖ^{-m(n-1)}‖ < ‖a‖ ≤ ‖ϖ^{-mn}‖`; `‖e a‖ ≤ ‖e ϖ‖^{-m(n+1)} ≤ C₂‖a‖^s`
  with `s` from `‖e ϖ‖ = ‖ϖ‖^s` (define `s := log‖e ϖ‖ / log‖ϖ‖`, positive since
  both logs negative); swap roles for the lower bound.
- **Sources**: [JN] Lemma 2.1.7 (pp. 9–10). | **Generality**: as stated.

### [T035] isCompletelyContinuous_map_equiv + isCompletelyContinuous_baseChange
- **Status**: open | **File**: PhD/TateFredholm/BaseChange.lean | **Depends on**: T020
- **Parallel**: yes | **Type**: lemmas
- **Sketch**: both via T020 on each side.  Bounded case: `rowNorm v j ≤ C * rowNorm u j`
  (termwise `‖ψ a‖ ≤ C‖a‖`, `ciSup` monotone — `Real.iSup_le` + `mul` bounds);
  squeeze.  Equiv case: row decay is a topological statement — `rowNorm v j =
  ⨆ ‖e a_{ij}‖`; from `rowNorm u → 0` and continuity of `e` at 0 get uniform
  smallness: for ε pick δ (continuity) with `‖x‖ ≤ δ → ‖e x‖ ≤ ε`; rows of `u`
  eventually `≤ δ` termwise... careful: need `sup_i ‖e a‖ ≤ ε` from
  `sup_i ‖a‖ ≤ δ` — termwise fine.  (This is where T033's quantitative version is
  NOT needed — plain continuity suffices; note it.)
- **Sources**: [JN] Prop 2.1.8 discussion (p. 10). | **Generality**: `[IsTate]` both sides.

### [T036] charCoeff_baseChange
- **Status**: open | **File**: PhD/TateFredholm/BaseChange.lean | **Depends on**: T022, T035
- **Parallel**: yes | **Type**: theorem
- **Sketch**: `minor v S = ψ (minor u S)` by `RingHom.map_det` (✓ verified) +
  entrywise `hv` (`Matrix.ext`-congr under `ψ.mapMatrix`); push `ψ` through the tsum:
  `ψ` bounded ⟹ continuous (`AddMonoidHomClass.continuous_of_bound` or Lipschitz as
  in T016) ⟹ `Summable.map` `(ψ : R →+ S)`-hom (verify `Summable.map` signature:
  needs `ContinuousAddMonoidHom`-style args — Mathlib `Summable.map f hf.continuous`
  pattern) and `tsum` commutes (`Summable.map_tsum`-form / `(hsum.hasSum.map _).tsum_eq`);
  finish with `map_mul`, `map_pow`, `map_neg`, `map_one`.
- **Mathlib**: `RingHom.map_det` (✓), `Summable.map` + `map_tsum` pattern (verify
  exact combinator; `Topology/Algebra/InfiniteSum/Basic.lean:272` region confirmed).
- **Sources**: [Bel] Lemma II.1.23 (matrix-wise); [Buz] Cor 2.10. |
  **Generality**: bounded `ψ` (NOT contractive — [JN] Def 2.1.1 boundedness).

### [T037] charPowerSeries_map_equiv
- **Status**: open | **File**: PhD/TateFredholm/BaseChange.lean | **Depends on**: T036, T035
- **Parallel**: no | **Type**: theorem
- **Sketch**: same skeleton as T036 with `ψ = (e : R →+* S)`; the tsum-transfer uses
  continuity of `e` (given) instead of boundedness — the `Summable.map` route works
  verbatim; do NOT route through T036 (e is not bounded; docstring explains).
  Coefficientwise + `PowerSeries.ext` as in the already-proven
  `charPowerSeries_baseChange`.
- **Sources**: [JN] Prop 2.1.8. | **Generality**: as stated.

### [T038] isPotentiallyONable_of_uniformizer — Serre's theorem (ASSEMBLY)
- **Status**: open (decomposed 2026-07-09 — see `decomposition.md`; sub-tickets T039–T046)
- **File**: PhD/TateFredholm/BaseChange.lean (§9 Classical)
- **Depends on**: T045, T046 | **Parallel**: no | **Type**: theorem (assembly)
- **Sketch** ([Bel] Thm II.1.13 proof, p. 58 — three sentences, transcribed): type
  synonym `E′ := E` carrying the `rescale π`-norm; build `NormedAddCommGroup E′` from
  an `AddGroupNorm` out of T046 (R7a definiteness-side + R7b + `rescale_neg` trivial),
  `NormedSpace K E′` from R7c, `IsUltrametricDist` from R7b, `CompleteSpace` +
  `E ≃L[K] E′` = identity with continuity both ways from R7a's sandwich; `hE′` (norm
  values in `‖π‖^ℤ`) definitional; apply T045 (`isONable_of_discrete_norms`) to `E′`,
  weaken to `IsPotentiallyONable`, transport along the identity equiv (compose the isos).
- **Mathlib**: `AddGroupNorm`/`NormedAddCommGroup.induced`-free construction (build
  `NormedAddCommGroup` via `AddGroupNorm.toNormedAddCommGroup`? verify constructor
  name), standard type-synonym pattern.
- **Sources**: [Bel] Thm II.1.13 (p. 58), verbatim quote in decomposition.md.
- **Generality**: field `K` with the discreteness hypothesis — intrinsically classical
  (docstring already explains why it fails over general Tate rings).

### [T039] exists_norm_eq_zpow (R1 — discreteness of the value group)
- **Status**: open | **File**: PhD/TateFredholm/Residue.lean | **Depends on**: T001
- **Parallel**: yes | **Type**: lemma
- **Sketch** (decomposition.md R1): archimedean sandwich `‖π‖^(n+1) < ‖x‖ ≤ ‖π‖^n`;
  `y := x * π^(-n)` has `‖y‖ ∈ (‖π‖, 1]` by `norm_mul`/`norm_zpow`; `hπmax` kills
  `‖y‖ < 1`; so `‖y‖ = 1`, `‖x‖ = ‖π‖^n`.
- **Mathlib**: `norm_zpow`, `norm_mul`, sandwich via `Real.log`-monotonicity or
  `exists_mem_Ioc_zpow`-family (verify name via loogle `∃ n : ℤ, _ ∈ Set.Ioc _ _`).
- **Sources**: [Bel] p. 58 (quote in decomposition.md).

### [T040] unitBall + unitBall_isUnit_iff (R2, R3)
- **Status**: open | **File**: PhD/TateFredholm/Residue.lean | **Depends on**: T001
- **Parallel**: yes | **Type**: def-completion + lemma
- **Sketch**: R2 five fields — `norm_mul` (`≤ 1·1`), ultrametric add
  (`IsUltrametricDist.norm_add_le_max`-form), `norm_one`, `norm_zero`, `norm_neg`.
  R3: (⇐) inverse has norm `1` (`norm_inv`), package `Units`; (⇒)
  `1 = ‖x‖‖x⁻¹‖` with both factors `≤ 1`.
- **Sources**: [Bel] p. 58 ("which is a subring of R"); R3 note in decomposition.md.

### [T041] isMaximal_span_pi (R4 — the residue field)
- **Status**: open | **File**: PhD/TateFredholm/Residue.lean | **Depends on**: T039, T040
- **Parallel**: no | **Type**: theorem
- **Sketch** (decomposition.md R4): membership `x ∈ span{π} ↔ ‖x‖ ≤ ‖π‖`
  (`Ideal.mem_span_singleton`, divide in `K`); any `x ∉ (π)` has `‖x‖ = 1` by T039
  (discreteness) hence is a unit by T040; conclude by `Ideal.isMaximal_iff`.
  Downstream consumers use `Ideal.Quotient.field` (✓ mathlib) on this.
- **Sources**: [Bel] p. 58 Thm II.1.13 proof ("basis over 𝔽_p" — the field property at
  general K; reformulation note in decomposition.md).

### [CLEANUP-13] /cleanup on PhD/TateFredholm/Residue.lean (after T041)
- **Status**: open | **Depends on**: T039, T040, T041 | **Type**: cleanup

### [T042] exists_residue_approx (R5 — residue basis, quotient machinery)
- **Status**: open | **File**: PhD/TateFredholm/Residue.lean | **Depends on**: T041, CLEANUP-13
- **Parallel**: no | **Type**: theorem (chunky; contains the tree's flagged risk)
- **Sketch** (decomposition.md R5, route (i)–(v)): `Module K⁰ E` via `Module.compHom`
  along `(unitBall K).subtype`; `E⁰` submodule; `Ẽ := E⁰ ⧸ (span{π} • ⊤)` as module
  over `K̃ := K⁰ ⧸ span{π}` — **locate instance `Module (R ⧸ I) (M ⧸ I•⊤)`
  (`Submodule.Quotient.module'`-family) or hand-build (≤ 25 lines, documented
  fallback)**; `K̃` field via T041 + `Ideal.Quotient.field`; `Basis.ofVectorSpace`;
  choose representative lifts; unfold both basis clauses back to the norm phrasing
  (spanning ⇒ one-step approximation with `Finsupp` coefficients; independence ⇒
  norm-detection).  `‖eᵢ‖ = 1` from `hE` (nonzero residue ⇒ norm `> ‖π‖` ⇒ `= 1`).
- **Mathlib**: `Module.compHom`, `Ideal.Quotient.field` (✓), `Basis.ofVectorSpace`
  (verify exact location), `Submodule.Quotient` API.
- **Sources**: [Bel] Lemma II.1.12 proof (verbatim quote in decomposition.md).

### [T043] exists_expansion_of_residue_approx (R6a — successive approximation, the heart)
- **Status**: open | **File**: PhD/TateFredholm/Residue.lean | **Depends on**: T018, T042
- **Parallel**: no | **Type**: theorem (largest single proof of the subtree, ~120 LOC;
  source proof is one 12-line paragraph, p. 58)
- **Sketch** (transcribe [Bel] Lemma II.1.12 proof, quoted in decomposition.md):
  iterate the one-step approximation: `m − ∑ aⁿᵢ eᵢ = πⁿ`-small with
  `‖aⁿᵢ − aⁿ⁺¹ᵢ‖ ≤ ‖π‖ⁿ`; per-index Cauchy (`cauchySeq_tendsto_of_complete` in `K`),
  limits `aᵢ`; cofinite decay of the limit family (stagewise finite supports +
  geometric increments); `HasSum` by comparing partial sums to the stage
  approximations; norm formula: sup attained at stage 1 when `‖m‖ = 1`, general `m`
  by `π`-power scaling (`hE`).
- **Mathlib**: `cauchySeq_tendsto_of_complete`, geometric bounds
  (`tendsto_pow_atTop_nhds_zero_of_lt_one`), `Finsupp` support unions; project T018.
- **Sources**: [Bel] Lemma II.1.12 proof — full verbatim quote in decomposition.md.

### [T044] expansion_unique_of_residue_indep (R6b)
- **Status**: open | **File**: PhD/TateFredholm/Residue.lean | **Depends on**: T018, T039
- **Parallel**: yes (with T043) | **Type**: theorem
- **Sketch** (decomposition.md R6b, incl. the resolved attack): let `c := a − b`;
  `HasSum (cᵢ • eᵢ) 0`; if `c ≠ 0` the sup `‖cᵢ‖` is *attained* (cofinite decay +
  finitely many large terms — no discreteness needed); normalise by a scalar of that
  attained norm; split head (finite, `‖·‖ = 1` coefficients) + tail (`≤ ‖π‖`); the
  head combination has norm `≤ ‖π‖` (ultrametric from the zero sum and small tail);
  `hindep` forces head coefficients `≤ ‖π‖ < 1` — contradiction.
- **Sources**: [Bel] Lemma II.1.12 ("The other direction is easy and left to the
  reader" — expansion recorded in decomposition.md).

### [CLEANUP-14] /cleanup on PhD/TateFredholm/Residue.lean (after T044)
- **Status**: open | **Depends on**: T042, T043, T044 | **Type**: cleanup

### [T045] isONable_of_discrete_norms (R6 — assembly of the Lemma II.1.12 direction)
- **Status**: open | **File**: PhD/TateFredholm/Residue.lean | **Depends on**: T042, T043, T044
- **Parallel**: no | **Type**: theorem
- **Sketch** (decomposition.md R6): coefficient map from T043-existence +
  T044-uniqueness; linearity derived from uniqueness (expansion of `m + m′` vs sum of
  expansions; scalars likewise); isometry from the norm clause; inverse by summing any
  `a : c(ι,K)` (T018); package `LinearIsometryEquiv`; reindex `ι` into `Set E` via
  injectivity (from T044) as in T014's route; handle `E = 0` degenerately.
- **Sources**: [Bel] Lemma II.1.12 statement ("M is orthonormalizable iff M̃ free").

### [T046] rescale lemmas (R7a, R7b, R7c)
- **Status**: open | **File**: PhD/TateFredholm/Residue.lean | **Depends on**: T039
- **Parallel**: yes | **Type**: lemmas
- **Sketch** (decomposition.md R7): unfold `rescale`; floor characterisation
  `Int.floor_le`/`Int.le_floor` + `Real.log` monotonicity (`log‖π‖ < 0` flips —
  `Real.log_neg`); R7a sandwich incl. the strict upper bound; R7b: the floor of the
  max is the max of floors under a monotone transform (case on which of
  `‖m‖, ‖n‖` is larger + ultrametric on `E`); R7c: `‖c‖ = ‖π‖^k` (T039), floor shifts
  by exactly `k` (`Int.floor_add_intCast`), `zpow_add₀`.
- **Mathlib**: `Int.floor_add_intCast` (verify name), `Real.log_zpow`, `zpow_add₀`,
  `Real.log_neg`.
- **Sources**: [Bel] Thm II.1.13 proof, sentence 1 (quote in decomposition.md).

### [CLEANUP-15] /cleanup on PhD/TateFredholm/Residue.lean (final)
- **Status**: open | **Depends on**: T045, T046, T038 | **Type**: cleanup

### [CLEANUP-9] /cleanup on PhD/TateFredholm/BaseChange.lean (after T035)
- **Status**: open | **Depends on**: T033, T034, T035 | **Type**: cleanup

### [CLEANUP-10] /cleanup on PhD/TateFredholm/BaseChange.lean (final)
- **Status**: open | **Depends on**: T036, T037 | **Type**: cleanup

### [CLEANUP-11] /cleanup on PhD/TateFredholm/Tate.lean (final)
- **Status**: open | **Depends on**: T002, T018 | **Type**: cleanup

### [CLEANUP-12] /cleanup on PhD/TateFredholm/OperatorNorm.lean (final)
- **Status**: open | **Depends on**: T006, T007, T008 | **Type**: cleanup

### [CLEANUP-FINAL] /cleanup-all on PhD/TateFredholm/
- **Status**: open | **Depends on**: everything above except T038 | **Type**: cleanup
- Final pass; then `/pre-submit`.  T038 excluded while blocked — if it is
  de-scoped, delete its skeleton declaration or move it to a `Postponed.lean`
  with a documented sorry (user decision at that point).
