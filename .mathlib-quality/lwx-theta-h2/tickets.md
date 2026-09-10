# Ticket Board — `lwx-theta-h2` (H2 discharged; the theta target at the classical points)

**BOARD PATH: `.mathlib-quality/lwx-theta-h2/`.**  The default `.mathlib-quality/` board belongs to
the completed NewtonPolygons project — NEVER touch it; `.mathlib-quality/qmf/` and its
`beastmode_active` sentinel belong to a parallel run — NEVER touch them either.  Every
`/beastmode` run must name this board path explicitly, and delete only
`.mathlib-quality/lwx-theta-h2/beastmode_active` (cat before rm).

**Files owned by this board**: `PhD/LWX/ThetaExact.lean`, `PhD/LWX/TargetPoint.lean`,
`PhD/LWX/DegreeFormula.lean` (all new; skeletoned and building).  Do not edit any other file
except in `CLEANUP-A-FINAL` (the two relocations named there).

**Build**: `lake build PhD.LWX.ThetaExact PhD.LWX.TargetPoint PhD.LWX.DegreeFormula`; full
`lake build PhD` is green (3906 jobs, 2026-09-10) with sorry warnings only.  Statements are
transcribed verbatim from the compiling skeleton and are **protected** — if a statement is wrong,
append to this board's `b2_log.jsonl` rather than editing it.  `_hx`-slack convention applies to
a hypothesis that turns out unneeded.  `lake exe runLinter PhD.LWX.<Module>` is a gate for every
cleanup.  `omega` not `lia`.  No `timeout` binary on this machine.  Cleanup tickets are done
inline by the main agent.

**Read before working any ticket**: `plan.md`, `decomposition.md`, and
`.mathlib-quality/lwx-stepone/JL-AUDIT.md`.  Nothing here depends on Jacquet–Langlands or on
[Jo11]; if a ticket seems to need either, the route has drifted — file a B2.

## Summary

**2026-09-10, `/beastmode` — BOARD COMPLETE (all 70 tickets done).**  `PhD/LWX/ThetaExact.lean`,
`PhD/LWX/TargetPoint.lean` and `PhD/LWX/DegreeFormula.lean` are **sorry-free**; `lake build PhD`
is green and `lake exe runLinter` reports nothing on any of the three modules.

**Milestone D2 — `LWX.degX_succ_classicalPoint`**: [LWX, Thm 1.3]'s degree formula
`deg X_{k+1,ω} = r_ord(ω') + r_ord(ω·ω₀^{−2k−2})` at the classical points, **granted H1 alone**.
`#print axioms` = `[propext, Classical.choice, Quot.sound]` for it and for
`isThetaExact_classicalData`, `targetData_classicalPoint`, `isThetaExact_of_isClassicalShape`.

What the board delivered:

- **Part A (A1–A25) — hypothesis H2 is no longer a hypothesis at a classical-shape pair.**
  `LWX.isThetaExact_of_isClassicalShape` derives the determinant identity `IsThetaExact` states
  from the two classical shapes, and `LWX.isThetaExact_classicalData` specialises it to a
  `ClassicalData` with its `TargetData`.  The route is the planned one: `θ^{k+1} = D ∘ σ` with the
  section `τ` (`shiftBlock`/`insertBlock`/`diagBlock`), `τ∘σ = 1 − π_{≤k}`, and the existing
  `TateFredholm.charPowerSeries_eq_of_diag_intertwine`.
- **Part B (B1–B23) — the theta target exists at the classical points.**
  `LWX.targetData_classicalPoint` inhabits `TargetData` at `weightPoint p (−(k+2)) ζ` with the
  nebentypus `targetChar p ω k = ω·ω₀^{−2k−2}`, closing the old board's gap **AG-ζ**
  (`LWX.targetConst_eq_classicalData_u`).
- **Assembly (D1, D2)** and 20 cleanup tickets, including the two relocations of CLEANUP-A-FINAL:
  `TateFredholm.matrixCoeff_truncation` now lives in `PhD/TateFredholm/Matrix.lean` and
  `TateFredholm.charPowerSeries_smul` in `PhD/TateFredholm/Riesz.lean`.

### Deviations from the plan (all recorded; no statement was edited, no B2 filed)

1. **`weightPoint` helpers.** Part B needed six private norm helpers that the plan folded into
   B4's sketch (`inv_p_pos`, `norm_sq_lt_of_le_inv`, `norm_p_mul_le_inv`, `norm_p_mul_sq_lt`,
   `norm_padicExp_p_mul_sub_one_le`, `norm_mul_le_one`).  They are the `‖x‖ ≤ 1` generalisations
   of `ClassicalPoint.lean`'s private helpers and serve B4–B10 and B18–B21.
2. **B23 could not use `rw [← targetConst_eq_classicalData_u …]`** — rewriting backwards through
   the structure projection `(classicalData …).u i t a` hit a `whnf` timeout.  Replaced by a
   `funext` equality of the two constant *functions* followed by `rw [← hu]`, which is cheap.

### Two engineering traps found (worth remembering)

- **`rw [tsum_eq_single x (fun z hz => by …)]` over a compound index type hangs.**  The inline
  `by` block is elaborated against a goal still carrying the `tsum`'s function metavariable; on
  `ι × (ZMod (p^h) × ℕ)` this ran >12 CPU-minutes without tripping `maxHeartbeats`.  The fix is to
  state the vanishing as a named `have` first (metavariable-free), then `rw [tsum_eq_single x h]`.
  Same for `congrArg (fun T => …) hint` followed by `simp only [...] at h1`: replaced by a `have`
  with the explicit statement proved by `rw [hint]`.
- **`omit … in` must precede the docstring**, exactly like `set_option … in`; between docstring
  and `theorem` it is a parse error ("unexpected token 'omit'; expected 'lemma'").

### Ticket counts

- Total: 70 tickets (50 proof/definition, 20 cleanup). **Done: 70.**  Open: 0.  B2s: 0.
- Hypothesis of the deliverable: **H1** (`AtkinLehnerHypothesis`) only.
- Still out of scope, as planned: H1 itself, `ω' = ω⁻¹ω₀^{2k}` (the partner nebentypus, the other
  half of AG-ω₀), [LWX, Thm 1.5]'s second half.

---
## Part A — `PhD/LWX/ThetaExact.lean`

### [A1] `TateFredholm.matrixCoeff_truncation`
- **Status**: done — **relocated to `PhD/TateFredholm/Matrix.lean` by CLEANUP-A-FINAL**
- **File**: PhD/TateFredholm/Matrix.lean (was PhD/LWX/ThetaExact.lean:54) | **Depends on**: — | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem matrixCoeff_truncation (S : Finset I) (j i : I) :
    matrixCoeff (truncation (R := R) S) j i = if j = i ∧ j ∈ S then 1 else 0 := by
  sorry
```

#### Proof sketch
1. `rw [matrixCoeff, truncation_apply]` — the goal is `(if j ∈ S then cSpace.single i 1 j else 0) = if j = i ∧ j ∈ S then 1 else 0`.
2. `by_cases hji : j = i`; `· subst hji; simp [cSpace.single_apply_self]` and `· simp [cSpace.single_apply_of_ne hji, hji]` (both `if`s reduce; `split_ifs` if `simp` stalls).

#### Mathlib lemmas needed
- `TateFredholm.truncation_apply` (`Matrix.lean:260`)
- `TateFredholm.cSpace.single_apply_self`, `cSpace.single_apply_of_ne` (`ModelSpace.lean:112–115`)
- `TateFredholm.matrixCoeff` (`Matrix.lean:34`, unfold)

#### Sources
Definitional; `truncation` is Bellaïche's `π_S` (docstring at `Matrix.lean:238`).

#### Generality decision
General `R`, `I`; no `IsTate`, no `CompleteSpace` needed — add `omit`s at cleanup and relocate to `Matrix.lean` in CLEANUP-A-FINAL.

---
### [A2] `TateFredholm.charPowerSeries_smul`
- **Status**: done — **relocated to `PhD/TateFredholm/Riesz.lean` by CLEANUP-A-FINAL**
- **File**: PhD/TateFredholm/Riesz.lean (was PhD/LWX/ThetaExact.lean:61) | **Depends on**: — | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem charPowerSeries_smul [IsTate R] (a : R) (u : c(I, R) →L[R] c(I, R))
    (hu : IsCompactoid u) :
    charPowerSeries (a • u) = PowerSeries.rescale a (charPowerSeries u) := by
  sorry
```

#### Proof sketch
1. `refine PowerSeries.ext fun n => ?_`.
2. `rw [charPowerSeries_coeff, PowerSeries.coeff_rescale, charPowerSeries_coeff, charCoeff_smul a u hu n]`.

#### Mathlib lemmas needed
- `TateFredholm.charCoeff_smul` (`Riesz.lean:1514`)
- `TateFredholm.charPowerSeries_coeff`
- `PowerSeries.coeff_rescale`

#### Sources
`charCoeff_smul`'s docstring: "`cₙ(a•u) = aⁿ cₙ(u)` (the minors are `n`-linear in the rows)"; [Serre1962, §5].

#### Generality decision
General Tate ring `R`; relocate next to `charCoeff_smul` in `Riesz.lean` at CLEANUP-A-FINAL (one rebuild).

---
### [A3] `LWX.shiftOne`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean:79 | **Depends on**: — | **Parallel**: yes | **Type**: def

#### Statement
```lean
def shiftOne (r : ℕ) : c(ℕ, K) →L[K] c(ℕ, K) :=
```

#### Proof sketch
Discharge the column-finiteness obligation `(fun i => by sorry)`: copy `thetaOne`'s proof (`Theta.lean:78–84`) verbatim — `refine tendsto_const_nhds.congr' ?_; rw [Filter.EventuallyEq, Filter.eventually_cofinite]; refine (Set.finite_singleton (i - r)).subset fun j hj => ?_; rw [Set.mem_singleton_iff]; by_contra hcon; exact hj (by simp [show i ≠ j + r by omega])`.  The bound obligation is already discharged.

#### Mathlib lemmas needed
- `TateFredholm.ofCoeffs` (`GenFun.lean:178`)
- `Filter.eventually_cofinite`, `Set.finite_singleton`, `tendsto_const_nhds`, `Filter.Tendsto.congr'`

#### Sources
`thetaOne` (`Theta.lean:72`) is the model; [Bu04, §7] `bu04.txt:1064` (the derivative on Taylor coefficients).

#### Generality decision
Single disc, exponent `r` arbitrary.

---
### [CLEANUP-A1] Cleanup `PhD/LWX/ThetaExact.lean`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean | **Depends on**: A1, A2, A3 | **Parallel**: no | **Type**: cleanup

Run `/cleanup` inline on the file (naming, docstrings, `omit`s for unused section variables,
golf, no `set_option maxHeartbeats` left behind), then `lake exe runLinter PhD.LWX.ThetaExact` and
`lake build PhD.LWX.ThetaExact`.  Cadence rule: after every third proof ticket on this file.

---
### [A4] `LWX.insertOne`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean:87 | **Depends on**: — | **Parallel**: yes | **Type**: def

#### Statement
```lean
def insertOne (r : ℕ) : c(ℕ, K) →L[K] c(ℕ, K) :=
```

#### Proof sketch
As A3 with the support `{i + r}`: `(Set.finite_singleton (i + r)).subset fun j hj => …; by_contra hcon; exact hj (by simp [hcon])` (here `hcon : j ≠ i + r` makes the `if` false).

#### Mathlib lemmas needed
- as A3

#### Sources
Section `τ` of the shift; the coordinate form of [Bu04, Prop 4]'s kernel statement (`bu04.txt:1111–1114`).

#### Generality decision
Single disc, `r` arbitrary.

---
### [A5] `LWX.diagOne`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean:95 | **Depends on**: — | **Parallel**: yes | **Type**: def

#### Statement
```lean
def diagOne (r : ℕ) : c(ℕ, K) →L[K] c(ℕ, K) :=
```

#### Proof sketch
1. Bound: `split_ifs; · exact IsUltrametricDist.norm_natCast_le_one K _; · simp` (as `thetaOne`, `Theta.lean:74–77`).
2. Column: support `{i}` — `(Set.finite_singleton i).subset …; by_contra hcon; exact hj (by simp [Ne.symm hcon])` (the `if i = j` is false for `j ≠ i`).

#### Mathlib lemmas needed
- `IsUltrametricDist.norm_natCast_le_one`
- as A3

#### Sources
The scalar part `(j+1)⋯(j+r)` of `thetaOne`'s matrix (`matrixCoeff_thetaOne`).

#### Generality decision
Single disc, `r` arbitrary.

---
### [A6] `LWX.matrixCoeff_shiftOne`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean:100 | **Depends on**: A3 | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem matrixCoeff_shiftOne (r j i : ℕ) :
    matrixCoeff (shiftOne K r) j i = if i = j + r then 1 else 0 := by
  sorry
```

#### Proof sketch
`exact matrixCoeff_ofCoeffs _ _ _ j i` (as `matrixCoeff_thetaOne`, `Theta.lean:88`).

#### Mathlib lemmas needed
- `TateFredholm.matrixCoeff_ofCoeffs` (`GenFun.lean:191`)

#### Sources
Definitional.

#### Generality decision
—

---
### [CLEANUP-A2] Cleanup `PhD/LWX/ThetaExact.lean`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean | **Depends on**: A4, A5, A6 | **Parallel**: no | **Type**: cleanup

Run `/cleanup` inline on the file (naming, docstrings, `omit`s for unused section variables,
golf, no `set_option maxHeartbeats` left behind), then `lake exe runLinter PhD.LWX.ThetaExact` and
`lake build PhD.LWX.ThetaExact`.  Cadence rule: after every third proof ticket on this file.

---
### [A7] `LWX.matrixCoeff_insertOne`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean:104 | **Depends on**: A4 | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem matrixCoeff_insertOne (r j i : ℕ) :
    matrixCoeff (insertOne K r) j i = if j = i + r then 1 else 0 := by
  sorry
```

#### Proof sketch
`exact matrixCoeff_ofCoeffs _ _ _ j i` (as `matrixCoeff_thetaOne`, `Theta.lean:88`).

#### Mathlib lemmas needed
- `TateFredholm.matrixCoeff_ofCoeffs` (`GenFun.lean:191`)

#### Sources
Definitional.

#### Generality decision
—

---
### [A8] `LWX.matrixCoeff_diagOne`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean:108 | **Depends on**: A5 | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem matrixCoeff_diagOne (r j i : ℕ) :
    matrixCoeff (diagOne K r) j i
      = if i = j then ((Nat.descFactorial (j + r) r : ℕ) : K) else 0 := by
  sorry
```

#### Proof sketch
`exact matrixCoeff_ofCoeffs _ _ _ j i` (as `matrixCoeff_thetaOne`, `Theta.lean:88`).

#### Mathlib lemmas needed
- `TateFredholm.matrixCoeff_ofCoeffs` (`GenFun.lean:191`)

#### Sources
Definitional.

#### Generality decision
—

---
### [A9] `LWX.thetaOne_eq_diagOne_comp_shiftOne`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean:114 | **Depends on**: A6, A8 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem thetaOne_eq_diagOne_comp_shiftOne (r : ℕ) :
    thetaOne K r = (diagOne K r).comp (shiftOne K r) := by
  sorry
```

#### Proof sketch
1. `refine ext_matrixCoeff fun j i => ?_`; `rw [matrixCoeff_thetaOne, matrixCoeff_comp]`.
2. The sum `∑' l, matrixCoeff (shiftOne K r) l i * matrixCoeff (diagOne K r) j l` collapses: `rw [tsum_eq_single j (fun l hl => by rw [matrixCoeff_diagOne, if_neg hl, mul_zero])]` — note `matrixCoeff_diagOne r j l = if l = j then … else 0`.
3. `rw [matrixCoeff_shiftOne, matrixCoeff_diagOne, if_pos rfl]; split_ifs <;> simp`.

#### Mathlib lemmas needed
- `TateFredholm.ext_matrixCoeff` (`Matrix.lean:66`)
- `TateFredholm.matrixCoeff_comp` (`Matrix.lean:84`)
- `tsum_eq_single`
- `LWX.matrixCoeff_thetaOne` (`Theta.lean:86`)

#### Sources
`thetaOne`'s matrix `if i = j + r then descFactorial (j+r) r else 0` is the product of the diagonal (row `j`) and the shift.

#### Generality decision
Order `D ∘ σ` (scale by the *target* index): `σ ∘ D` would give `descFactorial (j+2r) r` — wrong.

---
### [CLEANUP-A3] Cleanup `PhD/LWX/ThetaExact.lean`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean | **Depends on**: A7, A8, A9 | **Parallel**: no | **Type**: cleanup

Run `/cleanup` inline on the file (naming, docstrings, `omit`s for unused section variables,
golf, no `set_option maxHeartbeats` left behind), then `lake exe runLinter PhD.LWX.ThetaExact` and
`lake build PhD.LWX.ThetaExact`.  Cadence rule: after every third proof ticket on this file.

---
### [A10] `LWX.shiftOne_comp_insertOne`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean:119 | **Depends on**: A6, A7 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem shiftOne_comp_insertOne (r : ℕ) : (shiftOne K r).comp (insertOne K r) = 1 := by
  sorry
```

#### Proof sketch
1. `refine ext_matrixCoeff fun j i => ?_`; `rw [matrixCoeff_comp, matrixCoeff_one]`.
2. `rw [tsum_eq_single (i + r) (fun l hl => by rw [matrixCoeff_insertOne, if_neg hl, zero_mul])]`, then `rw [matrixCoeff_insertOne, matrixCoeff_shiftOne, if_pos rfl, one_mul]`.
3. Goal `(if i + r = j + r then 1 else 0) = if j = i then 1 else 0`: `by_cases h : j = i <;> simp [h]` (+ `omega` for `i + r = j + r ↔ j = i`).

#### Mathlib lemmas needed
- `TateFredholm.matrixCoeff_one` (`Riesz.lean:729`)
- as A9

#### Sources
Coordinate form of `σ ∘ τ = 1`.

#### Generality decision
`r` arbitrary.

---
### [A11] `LWX.insertOne_comp_shiftOne`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean:124 | **Depends on**: A1, A6, A7 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem insertOne_comp_shiftOne (r : ℕ) :
    (insertOne K r).comp (shiftOne K r) = 1 - truncation (Finset.range r) := by
  sorry
```

#### Proof sketch
1. `refine ext_matrixCoeff fun j i => ?_`; `rw [matrixCoeff_comp, matrixCoeff_sub, matrixCoeff_one, matrixCoeff_truncation, Finset.mem_range]`.
2. `rcases le_or_gt r i with hri | hri`.
   - `r ≤ i`: `rw [tsum_eq_single (i - r) (fun l hl => by rw [matrixCoeff_shiftOne, if_neg (by omega), zero_mul])]`, `rw [matrixCoeff_shiftOne, matrixCoeff_insertOne, if_pos (by omega)]`; then `by_cases h : j = i` and `simp [h]` with `omega` for `j = i - r + r ↔ j = i` and `¬ i < r`.
   - `i < r`: every term is `0` (`i = l + r` impossible): `rw [tsum_eq_zero (fun l => by rw [matrixCoeff_shiftOne, if_neg (by omega), zero_mul])]` (name: `tsum_zero` after `funext`); RHS: `by_cases h : j = i <;> simp [h, hri]` (`1 − 1 = 0`).

#### Mathlib lemmas needed
- `TateFredholm.matrixCoeff_sub` (`Matrix.lean:43`)
- A1
- as A10
- `Finset.mem_range`

#### Sources
[Bu04, Prop 4] `bu04.txt:1111–1114`: the kernel of `θ` is "polynomials of degree at most `k − 2`" — in coordinates, `τ ∘ σ` kills exactly the first `r` coordinates.

#### Generality decision
`r` arbitrary; `1 - truncation (range r)` is the projection off the first `r` coordinates.

---
### [A12] `LWX.matrixCoeff_shiftBlock`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean:145 | **Depends on**: A6 | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem matrixCoeff_shiftBlock (h r : ℕ) (x y : ι × (ZMod (p ^ h) × ℕ)) :
    matrixCoeff (shiftBlock p ι K h r) x y = if y = (x.1, (x.2.1, x.2.2 + r)) then 1 else 0 := by
  sorry
```

#### Proof sketch
1. `obtain ⟨i, a, j⟩ := x; obtain ⟨i', a', j'⟩ := y`; `rw [<block def>, matrixCoeff_blockMap, matrixCoeff_blockMap, <one-disc lemma>]`.
2. Exhaustive case split: `by_cases hi : i = i' <;> by_cases ha : a = a' <;> by_cases hj : <index condition> <;> simp [hi, ha, hj, Prod.ext_iff]` (use `eq_comm` where the `Prod` equality is oriented the other way).

#### Mathlib lemmas needed
- `TateFredholm.matrixCoeff_blockMap` (`BlockMap.lean:82`)
- `Prod.ext_iff`

#### Sources
Blockwise transport of the one-disc matrix.

#### Generality decision
Block model, `h r` arbitrary.

---
### [CLEANUP-A4] Cleanup `PhD/LWX/ThetaExact.lean`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean | **Depends on**: A10, A11, A12 | **Parallel**: no | **Type**: cleanup

Run `/cleanup` inline on the file (naming, docstrings, `omit`s for unused section variables,
golf, no `set_option maxHeartbeats` left behind), then `lake exe runLinter PhD.LWX.ThetaExact` and
`lake build PhD.LWX.ThetaExact`.  Cadence rule: after every third proof ticket on this file.

---
### [A13] `LWX.matrixCoeff_insertBlock`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean:149 | **Depends on**: A7 | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem matrixCoeff_insertBlock (h r : ℕ) (x y : ι × (ZMod (p ^ h) × ℕ)) :
    matrixCoeff (insertBlock p ι K h r) x y
      = if x = (y.1, (y.2.1, y.2.2 + r)) then 1 else 0 := by
  sorry
```

#### Proof sketch
1. `obtain ⟨i, a, j⟩ := x; obtain ⟨i', a', j'⟩ := y`; `rw [<block def>, matrixCoeff_blockMap, matrixCoeff_blockMap, <one-disc lemma>]`.
2. Exhaustive case split: `by_cases hi : i = i' <;> by_cases ha : a = a' <;> by_cases hj : <index condition> <;> simp [hi, ha, hj, Prod.ext_iff]` (use `eq_comm` where the `Prod` equality is oriented the other way).

#### Mathlib lemmas needed
- `TateFredholm.matrixCoeff_blockMap` (`BlockMap.lean:82`)
- `Prod.ext_iff`

#### Sources
Blockwise transport of the one-disc matrix.

#### Generality decision
Block model, `h r` arbitrary.

---
### [A14] `LWX.matrixCoeff_diagBlock`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean:154 | **Depends on**: A8 | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem matrixCoeff_diagBlock (h r : ℕ) (x y : ι × (ZMod (p ^ h) × ℕ)) :
    matrixCoeff (diagBlock p ι K h r) x y
      = if x = y then ((Nat.descFactorial (x.2.2 + r) r : ℕ) : K) else 0 := by
  sorry
```

#### Proof sketch
1. `obtain ⟨i, a, j⟩ := x; obtain ⟨i', a', j'⟩ := y`; `rw [<block def>, matrixCoeff_blockMap, matrixCoeff_blockMap, <one-disc lemma>]`.
2. Exhaustive case split: `by_cases hi : i = i' <;> by_cases ha : a = a' <;> by_cases hj : <index condition> <;> simp [hi, ha, hj, Prod.ext_iff]` (use `eq_comm` where the `Prod` equality is oriented the other way).

#### Mathlib lemmas needed
- `TateFredholm.matrixCoeff_blockMap` (`BlockMap.lean:82`)
- `Prod.ext_iff`

#### Sources
Blockwise transport of the one-disc matrix.

#### Generality decision
Block model, `h r` arbitrary.

---
### [A15] `LWX.thetaBlock_eq_diagBlock_comp_shiftBlock`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean:160 | **Depends on**: A9 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem thetaBlock_eq_diagBlock_comp_shiftBlock (h r : ℕ) :
    thetaBlock (p := p) (K := K) (ι := ι) h r
      = (diagBlock p ι K h r).comp (shiftBlock p ι K h r) := by
  sorry
```

#### Proof sketch
`rw [thetaBlock, thetaDisc, diagBlock, shiftBlock, blockMap_comp, blockMap_comp, thetaOne_eq_diagOne_comp_shiftOne]`.

#### Mathlib lemmas needed
- `TateFredholm.blockMap_comp` (`BlockMap.lean:127`)
- `LWX.thetaBlock` (`AtkinLehnerInst.lean:73`), `LWX.thetaDisc` (`Theta.lean:96`)

#### Sources
A9 blockwise.

#### Generality decision
—

---
### [CLEANUP-A5] Cleanup `PhD/LWX/ThetaExact.lean`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean | **Depends on**: A13, A14, A15 | **Parallel**: no | **Type**: cleanup

Run `/cleanup` inline on the file (naming, docstrings, `omit`s for unused section variables,
golf, no `set_option maxHeartbeats` left behind), then `lake exe runLinter PhD.LWX.ThetaExact` and
`lake build PhD.LWX.ThetaExact`.  Cadence rule: after every third proof ticket on this file.

---
### [A16] `LWX.shiftBlock_comp_insertBlock`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean:166 | **Depends on**: A10 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem shiftBlock_comp_insertBlock (h r : ℕ) :
    (shiftBlock p ι K h r).comp (insertBlock p ι K h r) = 1 := by
  sorry
```

#### Proof sketch
`rw [shiftBlock, insertBlock, blockMap_comp, blockMap_comp, shiftOne_comp_insertOne, ContinuousLinearMap.one_def, blockMap_id, blockMap_id]` (if `1` is not syntactically `id` after the first rewrites, `show` the goal with `ContinuousLinearMap.id`).

#### Mathlib lemmas needed
- `TateFredholm.blockMap_id` (`BlockMap.lean:92`)
- `ContinuousLinearMap.one_def`

#### Sources
A10 blockwise.

#### Generality decision
—

---
### [A17] `LWX.insertBlock_comp_shiftBlock`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean:172 | **Depends on**: A1, A12, A13 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem insertBlock_comp_shiftBlock (h k : ℕ) :
    (insertBlock p ι K h (k + 1)).comp (shiftBlock p ι K h (k + 1))
      = 1 - truncation (classicalSupport p ι h k) := by
  sorry
```

#### Proof sketch
1. `refine ext_matrixCoeff fun x y => ?_`; `rw [matrixCoeff_comp, matrixCoeff_sub, matrixCoeff_one, matrixCoeff_truncation, mem_classicalSupport_iff]`.
2. `rcases le_or_gt (k + 1) y.2.2 with hy | hy`.
   - `k + 1 ≤ y.2.2`: `rw [tsum_eq_single (y.1, (y.2.1, y.2.2 - (k + 1))) (fun z hz => by rw [matrixCoeff_shiftBlock, if_neg ?_, zero_mul]; …)]` — the excluded `z` satisfies `y ≠ (z.1, (z.2.1, z.2.2 + (k+1)))` unless `z` is the single index (`Prod.ext_iff`, `omega`); then `rw [matrixCoeff_shiftBlock, matrixCoeff_insertBlock]`, `if_pos` with `Prod.ext_iff` + `Nat.sub_add_cancel hy`, and `by_cases hxy : x = y <;> simp [hxy]` (RHS `1 − 0` since `¬ y.2.2 ≤ k`).
   - `y.2.2 < k + 1`: all terms vanish (`y = (z.1,(z.2.1, z.2.2 + (k+1)))` forces `k + 1 ≤ y.2.2`): `tsum` of the zero function; RHS `by_cases hxy : x = y <;> simp [hxy]` (`1 − 1 = 0` since `y.2.2 ≤ k`).

#### Mathlib lemmas needed
- `LWX.mem_classicalSupport_iff` (`Touching.lean:309`)
- A1, A12, A13
- `Nat.sub_add_cancel`, `Prod.ext_iff`

#### Sources
[Bu04, Prop 4] `bu04.txt:1111–1114` blockwise: `τσ = 1 − π_{≤ k}`, the projection off the classical coordinates `classicalSupport p ι h k` (`Touching.lean:305`).

#### Generality decision
Specialised to `r = k + 1` because `classicalSupport` is indexed by `k`.

---
### [A18] `LWX.matrixCoeff_diagBlock_comp`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean:178 | **Depends on**: A14 | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem matrixCoeff_diagBlock_comp (h r : ℕ)
    (T : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K))
    (x y : ι × (ZMod (p ^ h) × ℕ)) :
    matrixCoeff ((diagBlock p ι K h r).comp T) x y
      = ((Nat.descFactorial (x.2.2 + r) r : ℕ) : K) * matrixCoeff T x y := by
  sorry
```

#### Proof sketch
`rw [matrixCoeff_comp, tsum_eq_single x (fun z hz => by rw [matrixCoeff_diagBlock, if_neg (Ne.symm hz), mul_zero]), matrixCoeff_diagBlock, if_pos rfl, mul_comm]`.

#### Mathlib lemmas needed
- A14
- `TateFredholm.matrixCoeff_comp`

#### Sources
Row scaling by a diagonal.

#### Generality decision
`T` arbitrary.

---
### [CLEANUP-A6] Cleanup `PhD/LWX/ThetaExact.lean`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean | **Depends on**: A16, A17, A18 | **Parallel**: no | **Type**: cleanup

Run `/cleanup` inline on the file (naming, docstrings, `omit`s for unused section variables,
golf, no `set_option maxHeartbeats` left behind), then `lake exe runLinter PhD.LWX.ThetaExact` and
`lake build PhD.LWX.ThetaExact`.  Cadence rule: after every third proof ticket on this file.

---
### [A19] `LWX.matrixCoeff_comp_diagBlock`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean:186 | **Depends on**: A14 | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem matrixCoeff_comp_diagBlock (h r : ℕ)
    (T : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K))
    (x y : ι × (ZMod (p ^ h) × ℕ)) :
    matrixCoeff (T.comp (diagBlock p ι K h r)) x y
      = matrixCoeff T x y * ((Nat.descFactorial (y.2.2 + r) r : ℕ) : K) := by
  sorry
```

#### Proof sketch
`rw [matrixCoeff_comp, tsum_eq_single y (fun z hz => by rw [matrixCoeff_diagBlock, if_neg hz, zero_mul]), matrixCoeff_diagBlock, if_pos rfl, mul_comm]`.

#### Mathlib lemmas needed
- A14
- `TateFredholm.matrixCoeff_comp`

#### Sources
Column scaling by a diagonal.

#### Generality decision
`T` arbitrary.

---
### [A20] `LWX.diagBlock_comp_eq_of_intertwine`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean:197 | **Depends on**: A15, A16 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem diagBlock_comp_eq_of_intertwine (h k : ℕ)
    {U U' : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K)} (c : K)
    (hint : (thetaBlock (p := p) (K := K) (ι := ι) h (k + 1)).comp U
      = c • (U'.comp (thetaBlock (p := p) (K := K) (ι := ι) h (k + 1)))) :
    (diagBlock p ι K h (k + 1)).comp
        ((shiftBlock p ι K h (k + 1)).comp (U.comp (insertBlock p ι K h (k + 1))))
      = (c • U').comp (diagBlock p ι K h (k + 1)) := by
  sorry
```

#### Proof sketch
1. `have h1 := congrArg (fun T => T.comp (insertBlock p ι K h (k + 1))) hint` (both sides composed with `τ`).
2. Rewrite `h1`: LHS `((D.comp σ).comp U).comp τ` → `D.comp (σ.comp (U.comp τ))` by `thetaBlock_eq_diagBlock_comp_shiftBlock` and `ContinuousLinearMap.comp_assoc` (twice); RHS `(c • (U'.comp θ)).comp τ = c • (U'.comp (θ.comp τ))` by `ContinuousLinearMap.smul_comp`, `comp_assoc`, and `θ.comp τ = D.comp (σ.comp τ) = D` by A15, `comp_assoc`, `shiftBlock_comp_insertBlock`, `ContinuousLinearMap.one_def`, `ContinuousLinearMap.comp_id`.
3. `rw [ContinuousLinearMap.smul_comp]` on the goal's RHS and `exact h1`.

#### Mathlib lemmas needed
- A15, A16
- `ContinuousLinearMap.comp_assoc`, `ContinuousLinearMap.smul_comp`, `ContinuousLinearMap.comp_id`, `ContinuousLinearMap.one_def`

#### Sources
[LWX] `lwx.txt:2049–2056` (equivariance of the theta sequence), transported along the section; uses only `σ ∘ τ = 1`.

#### Generality decision
Any `U U'` with the intertwining as hypothesis; the Hecke operators enter only at A24.

---
### [A21] `LWX.charPowerSeries_shiftBlock_comp_eq_of_intertwine`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean:208 | **Depends on**: A18, A19, A20 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem charPowerSeries_shiftBlock_comp_eq_of_intertwine (h k : ℕ)
    {U U' : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K)} (c : K)
    (hint : (thetaBlock (p := p) (K := K) (ι := ι) h (k + 1)).comp U
      = c • (U'.comp (thetaBlock (p := p) (K := K) (ι := ι) h (k + 1)))) :
    charPowerSeries ((shiftBlock p ι K h (k + 1)).comp (U.comp (insertBlock p ι K h (k + 1))))
      = charPowerSeries (c • U') := by
  sorry
```

#### Proof sketch
1. `refine charPowerSeries_eq_of_diag_intertwine (fun x => ((Nat.descFactorial (x.2.2 + (k + 1)) (k + 1) : ℕ) : K)) (fun x => isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (Nat.descFactorial_pos.2 (Nat.le_add_left _ _)).ne')) fun x y => ?_`.
2. `have := congrArg (fun T => matrixCoeff T x y) (diagBlock_comp_eq_of_intertwine h k c hint)`; `simpa only [matrixCoeff_diagBlock_comp, matrixCoeff_comp_diagBlock] using this`.

#### Mathlib lemmas needed
- `TateFredholm.charPowerSeries_eq_of_diag_intertwine` (`Conjugation.lean:85`)
- `Nat.descFactorial_pos`, `Nat.cast_ne_zero`, `isUnit_iff_ne_zero`
- A18, A19, A20

#### Sources
[LWX] `lwx.txt:2056–2059` ("equal to the dimension of slope zero subspace of `S^{D,†}_{(−k−2,ψ)}`"), read on characteristic series; the diagonal conjugation is the whole content.

#### Generality decision
`CharZero K` is used here (falling factorials are units). No compactness needed.

---
### [CLEANUP-A7] Cleanup `PhD/LWX/ThetaExact.lean`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean | **Depends on**: A19, A20, A21 | **Parallel**: no | **Type**: cleanup

Run `/cleanup` inline on the file (naming, docstrings, `omit`s for unused section variables,
golf, no `set_option maxHeartbeats` left behind), then `lake exe runLinter PhD.LWX.ThetaExact` and
`lake build PhD.LWX.ThetaExact`.  Cadence rule: after every third proof ticket on this file.

---
### [A22] `LWX.charPowerSeries_comp_one_sub_truncation_eq`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean:218 | **Depends on**: A17 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem charPowerSeries_comp_one_sub_truncation_eq (h k : ℕ)
    {U : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K)}
    (hU : IsCompactoid U) :
    charPowerSeries (U.comp (1 - truncation (classicalSupport p ι h k)))
      = charPowerSeries
          ((shiftBlock p ι K h (k + 1)).comp (U.comp (insertBlock p ι K h (k + 1)))) := by
  sorry
```

#### Proof sketch
`rw [← insertBlock_comp_shiftBlock, ← ContinuousLinearMap.comp_assoc, charPowerSeries_comm _ _ (hU.comp_right _), ContinuousLinearMap.comp_assoc]`.

#### Mathlib lemmas needed
- A17
- `TateFredholm.charPowerSeries_comm` (`Fredholm.lean:773`)
- `TateFredholm.IsCompactoid.comp_right` (`Matrix.lean:550`)

#### Sources
Trace property of Fredholm determinants ([Serre1962]); `1 − π = τσ`.

#### Generality decision
`U` compactoid; `σ` need not be.

---
### [A23] `LWX.charPowerSeries_comp_one_sub_truncation_eq_rescale`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean:228 | **Depends on**: A2, A21, A22 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem charPowerSeries_comp_one_sub_truncation_eq_rescale (h k : ℕ)
    {U U' : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K)}
    (hU : IsCompactoid U) (hU' : IsCompactoid U') (c : K)
    (hint : (thetaBlock (p := p) (K := K) (ι := ι) h (k + 1)).comp U
      = c • (U'.comp (thetaBlock (p := p) (K := K) (ι := ι) h (k + 1)))) :
    charPowerSeries (U.comp (1 - truncation (classicalSupport p ι h k)))
      = PowerSeries.rescale c (charPowerSeries U') := by
  sorry
```

#### Proof sketch
`rw [charPowerSeries_comp_one_sub_truncation_eq h k hU, charPowerSeries_shiftBlock_comp_eq_of_intertwine h k c hint, charPowerSeries_smul c U' hU']`.

#### Mathlib lemmas needed
- A2, A21, A22

#### Sources
The determinant identity `IsThetaExact` states, for arbitrary intertwined operators.

#### Generality decision
General core of Part A.

---
### [A24] `LWX.isThetaExact_of_isClassicalShape`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean:249 | **Depends on**: A23 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem isThetaExact_of_isClassicalShape
    (κ : AnalyticWeight UK (M1Kh h ψ) ρ) (κ' : AnalyticWeight UK' (M1Kh h ψ) ρ') {k : ℕ}
    {u : ι → Fin p → ZMod (p ^ h) → K} (hcl : IsClassicalShape θG h ψ U hU vRep hvΔ uu κ k u)
    (hcl' : IsClassicalShape' θG h ψ U hU vRep hvΔ uu κ' k u)
    (hdet : ∀ i t, (certM1 θG U hU vRep hvΔ uu i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p)
    (hρ : 0 ≤ ρ) (hσ : max ρ (p : ℝ)⁻¹ < 1) (hρ' : 0 ≤ ρ') (hσ' : max ρ' (p : ℝ)⁻¹ < 1)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape) :
    IsThetaExact θG h ψ U hU vRep hvΔ idx uu κ κ' k := by
  sorry
```

#### Proof sketch
1. `unfold IsThetaExact` (or `show charPowerSeries _ = PowerSeries.rescale _ (charPowerSeries _)` — `discHeckeCharPowerSeries` is a `def`, defeq to `charPowerSeries (discHeckeBlockOp …)`; do not `rw` it).
2. `exact charPowerSeries_comp_one_sub_truncation_eq_rescale h k (isCompactoid_discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu hρ hσ hshape) (isCompactoid_discHeckeBlockOp θG h ψ κ' U hU vRep hvΔ idx uu hρ' hσ' hshape) (ψ p ^ (k + 1)) (thetaBlock_comp_discHeckeBlockOp_of_isClassicalShape θG h ψ U hU vRep hvΔ idx uu κ κ' hcl hcl' hdet)`.

#### Mathlib lemmas needed
- A23
- `LWX.thetaBlock_comp_discHeckeBlockOp_of_isClassicalShape` (`StepThree.lean:205`)
- `LWX.isCompactoid_discHeckeBlockOp` (`DiscForms.lean:240`)
- `LWX.IsThetaExact` (`StepThree.lean:341`)

#### Sources
[LWX, §3.23 Step III] `lwx.txt:2049–2059`; [Bu04, §7] `bu04.txt:1093–1096` (the Hecke relation).

#### Generality decision
Level `h` and radii arbitrary; `hshape` for compactness, `hdet` for the intertwining.

---
### [CLEANUP-A8] Cleanup `PhD/LWX/ThetaExact.lean`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean | **Depends on**: A22, A23, A24 | **Parallel**: no | **Type**: cleanup

Run `/cleanup` inline on the file (naming, docstrings, `omit`s for unused section variables,
golf, no `set_option maxHeartbeats` left behind), then `lake exe runLinter PhD.LWX.ThetaExact` and
`lake build PhD.LWX.ThetaExact`.  Cadence rule: after every third proof ticket on this file.

---
### [A25] `LWX.isThetaExact_classicalData`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean:264 | **Depends on**: A24 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem isThetaExact_classicalData {hp2 : p ≠ 2} {hψ : ∀ x, ‖ψ x‖ = ‖x‖}
    {ω ω₁ : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₁ : K} {k : ℕ}
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    (hdet : ∀ i t, (certM1 θG U hU vRep hvΔ uu i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p)
    (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k) (d : TargetData c ω₁ T₁) :
    IsThetaExact θG 1 ψ U hU vRep hvΔ idx uu c.weight d.weight k := by
  sorry
```

#### Proof sketch
`exact isThetaExact_of_isClassicalShape θG 1 ψ U hU vRep hvΔ idx uu c.weight d.weight c.shape d.shape hdet (haloRhoH_nonneg 1 T₀) (max_lt (haloRhoH_lt_one 1 T₀ c.hT) inv_lt_one_p) (haloRhoH_nonneg 1 T₁) (max_lt (haloRhoH_lt_one 1 T₁ d.hT) inv_lt_one_p) hshape` (`c.weight`/`d.weight` unfold by defeq to the `haloWeightH`s in `c.shape`/`d.shape`).

#### Mathlib lemmas needed
- A24
- `LWX.haloRhoH_nonneg`, `LWX.haloRhoH_lt_one` (`HaloWeightH.lean:789,807`)
- `LWX.inv_lt_one_p`
- `LWX.ClassicalData.weight`, `LWX.TargetData.weight` (defs)

#### Sources
H2 at a classical datum with its theta target — the hypothesis `hH2` of `degX_succ`.

#### Generality decision
End of Part A.

---
### [CLEANUP-A-FINAL] Cleanup `PhD/LWX/ThetaExact.lean`
- **Status**: done
- **File**: PhD/LWX/ThetaExact.lean | **Depends on**: A25 | **Parallel**: no | **Type**: cleanup

Run `/cleanup` inline on the file (naming, docstrings, `omit`s for unused section variables,
golf, no `set_option maxHeartbeats` left behind), then `lake exe runLinter PhD.LWX.ThetaExact` and
`lake build PhD.LWX.ThetaExact`.  Cadence rule: after every third proof ticket on this file.

**Final per-file duties (this ticket only edits other files):** relocate
`TateFredholm.matrixCoeff_truncation` to `PhD/TateFredholm/Matrix.lean` (next to
`truncation_apply`) and `TateFredholm.charPowerSeries_smul` to `PhD/TateFredholm/Riesz.lean`
(next to `charCoeff_smul`), delete them here, and run the full `lake build PhD` once.  Add
`omit [CharZero K] in` on every lemma of the file that does not use it (everything before A21).

---
## Part B — `PhD/LWX/TargetPoint.lean`

### [B1] `LWX.teichChar_unitsMap_toZMod`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean:60 | **Depends on**: — | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem teichChar_unitsMap_toZMod (a : ℤ_[p]ˣ) :
    teichChar p (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) = teichmuller a := by
  sorry
```

#### Proof sketch
`exact teichRes_toZMod a`.

#### Mathlib lemmas needed
- `LWX.teichRes_toZMod` (`HaloWeight.lean:154`)

#### Sources
[LWX, Notation 2.1] `lwx.txt:413–414` (`Δ`-component).

#### Generality decision
—

---
### [B2] `LWX.targetChar_apply`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean:70 | **Depends on**: — | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem targetChar_apply (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) (r : (ZMod p)ˣ) :
    targetChar p ω k r = ω r * (teichRes r ^ (2 * k + 2))⁻¹ := by
  sorry
```

#### Proof sketch
`rw [targetChar, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, teichChar_apply]`.

#### Mathlib lemmas needed
- `MonoidHom.mul_apply`, `MonoidHom.inv_apply`, `MonoidHom.pow_apply`

#### Sources
[LWX] `lwx.txt:2074–2076`: `r_ord(ωω₀^{−2k−2})`.

#### Generality decision
—

---
### [B3] `LWX.weightPoint_natCast`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean:83 | **Depends on**: — | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem weightPoint_natCast (k : ℕ) (ζ : K) : weightPoint p (k : ℤ) ζ = classicalPoint p k ζ := by
  sorry
```

#### Proof sketch
`rw [weightPoint, classicalPoint, Int.cast_natCast]`.

#### Mathlib lemmas needed
- `Int.cast_natCast`
- `LWX.classicalPoint` (`ClassicalPoint.lean:190`)

#### Sources
[LWX] `lwx.txt:431–433`, `1794–1798`.

#### Generality decision
—

---
### [CLEANUP-B1] Cleanup `PhD/LWX/TargetPoint.lean`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean | **Depends on**: B1, B2, B3 | **Parallel**: no | **Type**: cleanup

Run `/cleanup` inline on the file (naming, docstrings, `omit`s for unused section variables,
golf, no `set_option maxHeartbeats` left behind), then `lake exe runLinter PhD.LWX.TargetPoint` and
`lake build PhD.LWX.TargetPoint`.  Cadence rule: after every third proof ticket on this file.

---
### [B4] `LWX.norm_weightPoint`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean:87 | **Depends on**: B3 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem norm_weightPoint (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    ‖weightPoint p s ζ‖ = ‖ζ - 1‖ := by
  sorry
```

#### Proof sketch
Mirror `norm_classicalPoint` (`ClassicalPoint.lean:231–248`).  First add two **private** helpers (sub-tickets if the worker prefers): `norm_p_mul_sq_lt (hpK) {x : K} (hx : ‖x‖ ≤ 1) : ‖((p:ℕ):K) * x‖ ^ 2 < ‖((p:ℕ):K)‖` (as `norm_p_mul_natCast_sq_lt`, with `hx` in place of `norm_natCast_le_one`) and `norm_padicExp_p_mul_sub_one_le' (hp2) (hpK) (hx) : ‖padicExp (p * x) - 1‖ ≤ p⁻¹` (via `PadicExpLog.norm_padicExp_sub_one_le h3 hp2`).  Then with `x := (s : K)`, `hx := IsUltrametricDist.norm_intCast_le_one`: `E := padicExp (p * s)`, `hE1`, `hEn : ‖E‖ = 1` (`norm_eq_one_of_norm_sub_le`), `hgt := inv_lt_norm_sub_one_of_isPrimitiveRoot hp2 hζ hpK`, split `weightPoint = (ζ − 1) * E + (E − 1)`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, `max_eq_left`.

#### Mathlib lemmas needed
- `LWX.PadicExpLog.norm_padicExp_sub_one_le` (`PadicExpLog.lean:361`; `h3` first)
- `LWX.norm_eq_one_of_norm_sub_le`
- `LWX.inv_lt_norm_sub_one_of_isPrimitiveRoot` (`ClassicalPoint.lean:207`)
- `IsUltrametricDist.norm_intCast_le_one`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`

#### Sources
[LWX] `lwx.txt:1796–1798`: valuation `p/(q(p−1))`.

#### Generality decision
All `s ∈ ℤ`; the helpers serve B8–B10, B18–B20 too.

---
### [B5] `LWX.norm_weightPoint_pow`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean:93 | **Depends on**: B4 | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem norm_weightPoint_pow (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    ‖weightPoint p s ζ‖ ^ (p - 1) = ‖((p : ℕ) : K)‖ := by
  sorry
```

#### Proof sketch
`rw [norm_weightPoint hp2 hζ hpK s]; exact norm_sub_one_pow_of_isPrimitiveRoot hζ (by rw [hpK]; exact inv_lt_one_p)` (as `norm_classicalPoint_pow`).

#### Mathlib lemmas needed
- `LWX.norm_sub_one_pow_of_isPrimitiveRoot` (`ClassicalPoint.lean:172`)

#### Sources
as B4

#### Generality decision
—

---
### [B6] `LWX.inv_lt_norm_weightPoint`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean:99 | **Depends on**: B4 | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem inv_lt_norm_weightPoint (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    (p : ℝ)⁻¹ < ‖weightPoint p s ζ‖ := by
  sorry
```

#### Proof sketch
`rw [norm_weightPoint hp2 hζ hpK s]; exact inv_lt_norm_sub_one_of_isPrimitiveRoot hp2 hζ hpK`.

#### Mathlib lemmas needed
- as B4

#### Sources
as B4

#### Generality decision
—

---
### [CLEANUP-B2] Cleanup `PhD/LWX/TargetPoint.lean`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean | **Depends on**: B4, B5, B6 | **Parallel**: no | **Type**: cleanup

Run `/cleanup` inline on the file (naming, docstrings, `omit`s for unused section variables,
golf, no `set_option maxHeartbeats` left behind), then `lake exe runLinter PhD.LWX.TargetPoint` and
`lake build PhD.LWX.TargetPoint`.  Cadence rule: after every third proof ticket on this file.

---
### [B7] `LWX.norm_weightPoint_lt_one`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean:105 | **Depends on**: B4 | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem norm_weightPoint_lt_one (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    ‖weightPoint p s ζ‖ < 1 := by
  sorry
```

#### Proof sketch
`rw [norm_weightPoint hp2 hζ hpK s]; exact norm_sub_one_lt_one_of_isPrimitiveRoot hζ (by rw [hpK]; exact inv_lt_one_p)`.

#### Mathlib lemmas needed
- `LWX.norm_sub_one_lt_one_of_isPrimitiveRoot` (`ClassicalPoint.lean:56`)

#### Sources
as B4

#### Generality decision
—

---
### [B8] `LWX.TH_one_weightPoint`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean:111 | **Depends on**: B4 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem TH_one_weightPoint (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    TH p 1 (weightPoint p s ζ) = PadicExpLog.padicExp (((p : ℕ) : K) ^ 2 * (s : K)) - 1 := by
  sorry
```

#### Proof sketch
Mirror `TH_one_classicalPoint` (`ClassicalPoint.lean:293`): `rw [TH, weightPoint, show ∀ x : K, (1 : K) + (x - 1) = x from fun x => by ring, pow_one, mul_pow, hζ.pow_eq_one, one_mul, ← PadicExpLog.padicExp_natCast_mul h3 hp2 hdisc p]; congr 2; push_cast; ring` with `h3 : ‖p‖ < 1` from `hpK`, `hdisc := norm_p_mul_sq_lt hpK (norm_intCast_le_one …)`.

#### Mathlib lemmas needed
- `LWX.PadicExpLog.padicExp_natCast_mul` (`PadicExpLog.lean:578`)
- `IsPrimitiveRoot.pow_eq_one`
- B4's helper

#### Sources
`TH p 1 T = (1+T)^p − 1` (`HaloWeightH.lean:333`).

#### Generality decision
All `s ∈ ℤ`.

---
### [B9] `LWX.norm_TH_one_weightPoint_sq_lt`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean:117 | **Depends on**: B8 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem norm_TH_one_weightPoint_sq_lt (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    ‖TH p 1 (weightPoint p s ζ)‖ ^ 2 < (p : ℝ)⁻¹ := by
  sorry
```

#### Proof sketch
Mirror `norm_TH_one_classicalPoint_sq_lt` (`ClassicalPoint.lean:305–333`) with `‖(s : K)‖ ≤ 1` in place of `norm_natCast_le_one`: `‖exp(p²s) − 1‖ ≤ ‖p²s‖ ≤ p⁻²`, then `p⁻⁴ < p⁻¹` (`nlinarith`).

#### Mathlib lemmas needed
- as B8
- `LWX.PadicExpLog.norm_padicExp_sub_one_le`

#### Sources
Level-`1` analyticity at the weight point.

#### Generality decision
All `s`.

---
### [CLEANUP-B3] Cleanup `PhD/LWX/TargetPoint.lean`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean | **Depends on**: B7, B8, B9 | **Parallel**: no | **Type**: cleanup

Run `/cleanup` inline on the file (naming, docstrings, `omit`s for unused section variables,
golf, no `set_option maxHeartbeats` left behind), then `lake exe runLinter PhD.LWX.TargetPoint` and
`lake build PhD.LWX.TargetPoint`.  Cadence rule: after every third proof ticket on this file.

---
### [B10] `LWX.haloExponentH_one_weightPoint`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean:123 | **Depends on**: B8 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem haloExponentH_one_weightPoint (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    haloExponentH p 1 (weightPoint p s ζ) = (s : K) := by
  sorry
```

#### Proof sketch
Mirror `haloExponentH_one_classicalPoint` (`ClassicalPoint.lean:360`): `rw [haloExponentH, TH_one_weightPoint hp2 hζ hpK s, add_sub_cancel, PadicExpLog.padicLog_padicExp h3 hp2 hdisc]; field_simp; ring` (`hdisc : ‖p^2 * s‖^2 < ‖p‖` from the helper, `h0 : ((p:ℕ):K) ≠ 0`).

#### Mathlib lemmas needed
- `LWX.PadicExpLog.padicLog_padicExp` (`PadicExpLog.lean:806`)
- `LWX.haloExponentH` (`HaloWeightH.lean:342`)

#### Sources
[LWX, §2.1] `lwx.txt:463`: the exponent `(log x)/p^m` at `x = exp(p²s)`.

#### Generality decision
All `s`.

---
### [B11] `LWX.mk_choose_mul_mk_choose`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean:132 | **Depends on**: — | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem mk_choose_mul_mk_choose (a b x : K) :
    PowerSeries.mk (fun m => Ring.choose a m * x ^ m)
        * PowerSeries.mk (fun m => Ring.choose b m * x ^ m)
      = PowerSeries.mk (fun m => Ring.choose (a + b) m * x ^ m) := by
  sorry
```

#### Proof sketch
1. `refine PowerSeries.ext fun m => ?_`; `rw [PowerSeries.coeff_mul, PowerSeries.coeff_mk, Ring.add_choose_eq m (Commute.all a b), Finset.sum_mul]`.
2. `refine Finset.sum_congr rfl fun ij hij => ?_`; `rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, ← Finset.mem_antidiagonal.1 hij, pow_add]; ring`.

#### Mathlib lemmas needed
- `Ring.add_choose_eq` (mathlib `RingTheory/Binomial.lean:519`)
- `PowerSeries.coeff_mul`, `PowerSeries.coeff_mk`, `Finset.mem_antidiagonal`, `Commute.all`

#### Sources
Vandermonde's identity in a binomial ring.

#### Generality decision
Any `a b x : K`; could live in a `Ring.choose` API file later.

---
### [B12] `LWX.mk_choose_zero`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean:139 | **Depends on**: — | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem mk_choose_zero (x : K) :
    PowerSeries.mk (fun m => Ring.choose (0 : K) m * x ^ m) = 1 := by
  sorry
```

#### Proof sketch
`refine PowerSeries.ext fun m => ?_; rw [PowerSeries.coeff_mk, Ring.choose_zero_ite, PowerSeries.coeff_one]; split_ifs <;> simp`.

#### Mathlib lemmas needed
- `Ring.choose_zero_ite` (`Binomial.lean:422`)
- `PowerSeries.coeff_one`

#### Sources
—

#### Generality decision
—

---
### [CLEANUP-B4] Cleanup `PhD/LWX/TargetPoint.lean`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean | **Depends on**: B10, B11, B12 | **Parallel**: no | **Type**: cleanup

Run `/cleanup` inline on the file (naming, docstrings, `omit`s for unused section variables,
golf, no `set_option maxHeartbeats` left behind), then `lake exe runLinter PhD.LWX.TargetPoint` and
`lake build PhD.LWX.TargetPoint`.  Cadence rule: after every third proof ticket on this file.

---
### [B13] `LWX.mk_choose_neg_natCast_mul_pow`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean:145 | **Depends on**: B11, B12 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem mk_choose_neg_natCast_mul_pow (n : ℕ) (x : K) :
    PowerSeries.mk (fun m => Ring.choose (-(n : K)) m * x ^ m)
        * (1 + PowerSeries.C x * PowerSeries.X) ^ n = 1 := by
  sorry
```

#### Proof sketch
`rw [← mk_choose_natCast_mul_pow, mk_choose_mul_mk_choose, neg_add_cancel, mk_choose_zero]`.

#### Mathlib lemmas needed
- `LWX.mk_choose_natCast_mul_pow` (`ClassicalPoint.lean:378`)
- B11, B12
- `neg_add_cancel`

#### Sources
The binomial series `(1+xz)^{−n}` is the inverse of the polynomial `(1+xz)^n` — the negative-weight analogue of C6.11.

#### Generality decision
`n : ℕ`; B14 supplies the cast.

---
### [B14] `LWX.autFactor_haloWeightH_weightPoint_neg`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean:157 | **Depends on**: B10, B13 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem autFactor_haloWeightH_weightPoint_neg (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (k : ℕ)
    (h0 : (p : ℝ)⁻¹ < ‖weightPoint p (-(k + 2 : ℤ)) ζ‖)
    (h1 : ‖weightPoint p (-(k + 2 : ℤ)) ζ‖ < 1)
    (hT : ‖TH p 1 (weightPoint p (-(k + 2 : ℤ)) ζ)‖ ^ 2 < (p : ℝ)⁻¹) (g : M1Kh 1 ψ) :
    (haloWeightH 1 ψ (weightPoint p (-(k + 2 : ℤ)) ζ) ω hp2 hψ h0 h1 hT).toWeightSeries.autFactor
          g.1 * linX g.1 ^ (k + 2)
      = PowerSeries.C (haloCharFunH 1 ψ (weightPoint p (-(k + 2 : ℤ)) ζ) ω (g.1 1 1)
          * (g.1 1 1) ^ (k + 2)) := by
  sorry
```

#### Proof sketch
Mirror `autFactor_haloWeightH_classicalPoint` (`ClassicalPoint.lean:406–420`).
1. `hd0 : g.1 1 1 ≠ 0 := (levelBounds_M1Kh 1 ψ _ hψ hT).d_ne_zero g.2`; `hlin : linX g.1 = C (g.1 1 1) * (1 + C (g.1 1 0 / g.1 1 1) * X)` (from the `hlin` of C6.12, or directly: `simp only [linX, mul_add, ← map_mul, mul_div_cancel₀ …]`).
2. `rw [autFactor_haloWeightH 1 ψ _ ω hp2 hψ h0 h1 hT g, haloExponentH_one_weightPoint hp2 hζ (norm_natCast_p ψ hψ)]`; `push_cast` so the exponent reads `-((k : K) + 2)`; rewrite it as `-(((k + 2 : ℕ) : K))` (`Nat.cast_add`, `Nat.cast_ofNat`) to match B13.
3. `rw [hlin, mul_pow, ← map_pow, map_mul]` and close with `linear_combination (PowerSeries.C (haloCharFunH 1 ψ _ ω (g.1 1 1)) * PowerSeries.C (g.1 1 1 ^ (k + 2))) * mk_choose_neg_natCast_mul_pow (k + 2) (g.1 1 0 / g.1 1 1)`.

#### Mathlib lemmas needed
- `LWX.autFactor_haloWeightH` (`HaloWeightH.lean:1098`)
- `LWX.levelBounds_M1Kh`
- B10, B13
- `linear_combination`

#### Sources
`autFactor_haloWeightH`: `col·(cz+d)^{−2} = κ(d)·∑ C(s_1, m)(c/d)^m z^m`; at `s_1 = −(k+2)` the series is `(1 + (c/d)z)^{−(k+2)}`.

#### Generality decision
Target exponent `−(k+2)`, matching `IsClassicalShape'`'s `L^{k+2}`.

---
### [B15] `LWX.isClassicalShape'_haloWeightH_weightPoint_neg`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean:175 | **Depends on**: B14 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem isClassicalShape'_haloWeightH_weightPoint_neg (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (k : ℕ)
    (h0 : (p : ℝ)⁻¹ < ‖weightPoint p (-(k + 2 : ℤ)) ζ‖)
    (h1 : ‖weightPoint p (-(k + 2 : ℤ)) ζ‖ < 1)
    (hT : ‖TH p 1 (weightPoint p (-(k + 2 : ℤ)) ζ)‖ ^ 2 < (p : ℝ)⁻¹) :
    IsClassicalShape' θG 1 ψ U hU vRep hvΔ uu
      (haloWeightH 1 ψ (weightPoint p (-(k + 2 : ℤ)) ζ) ω hp2 hψ h0 h1 hT) k
      fun i t a => haloCharFunH 1 ψ (weightPoint p (-(k + 2 : ℤ)) ζ) ω
          (certConj θG 1 ψ U hU vRep hvΔ uu i t a 1 1)
        * (certConj θG 1 ψ U hU vRep hvΔ uu i t a 1 1) ^ (k + 2) := by
  sorry
```

#### Proof sketch
`exact fun i t a => autFactor_haloWeightH_weightPoint_neg ψ ω hp2 hψ hζ k h0 h1 hT (discConjK 1 (certM1 θG U hU vRep hvΔ uu i t) a ψ)` (as `isClassicalShape_haloWeightH_classicalPoint`, `ClassicalPoint.lean:432`).

#### Mathlib lemmas needed
- B14
- `LWX.discConjK`, `LWX.certM1`

#### Sources
`IsClassicalShape'` (`StepThree.lean:196`).

#### Generality decision
—

---
### [CLEANUP-B5] Cleanup `PhD/LWX/TargetPoint.lean`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean | **Depends on**: B13, B14, B15 | **Parallel**: no | **Type**: cleanup

Run `/cleanup` inline on the file (naming, docstrings, `omit`s for unused section variables,
golf, no `set_option maxHeartbeats` left behind), then `lake exe runLinter PhD.LWX.TargetPoint` and
`lake build PhD.LWX.TargetPoint`.  Cadence rule: after every third proof ticket on this file.

---
### [B16] `LWX.certConj_apply_one_one`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean:191 | **Depends on**: — | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem certConj_apply_one_one (h : ℕ) (i : ι) (t : Fin p) (a : ZMod (p ^ h)) :
    certConj θG h ψ U hU vRep hvΔ uu i t a 1 1
      = intHom ψ ((M1.toLocalMat (discConj h (certM1 θG U hU vRep hvΔ uu i t) a)).d : ℤ_[p]) := by
  sorry
```

#### Proof sketch
`rw [certConj, coe_discConjK, RingHom.mapMatrix_apply, Matrix.map_apply, intHom_apply, M1.coe_toLocalMat_d]; rfl` (the last step identifies `(discConj h δ a).1 1 1` with `(discConj h δ a : Matrix _ _ _) 1 1`).

#### Mathlib lemmas needed
- `LWX.coe_discConjK` (`DiscModel.lean:333`)
- `LWX.M1.coe_toLocalMat_d` (`IntegralModel.lean:308`)
- `RingHom.mapMatrix_apply`, `Matrix.map_apply`
- `LWX.intHom_apply`

#### Sources
The `d`-entry of a disc conjugate is a `p`-adic unit (`M1`'s definition).

#### Generality decision
All `h`.

---
### [B17] `LWX.coe_eq_teichRes_mul_oneUnitPart`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean:197 | **Depends on**: — | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem coe_eq_teichRes_mul_oneUnitPart (a : ℤ_[p]ˣ) :
    (a : ℤ_[p]) = (teichRes (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p])
      * oneUnitPart a := by
  sorry
```

#### Proof sketch
`rw [teichRes_toZMod, oneUnitPart, ← Units.val_mul, mul_comm a, mul_inv_cancel_left]`.

#### Mathlib lemmas needed
- `LWX.teichRes_toZMod`
- `LWX.oneUnitPart` (`UnitsLog.lean:193`)
- `Units.val_mul`, `mul_inv_cancel_left`

#### Sources
[LWX, Notation 2.1] `lwx.txt:413–414`.

#### Generality decision
—

---
### [B18] `LWX.continuous_padicExp_mul_intHom`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean:205 | **Depends on**: — | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem continuous_padicExp_mul_intHom (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {c : K}
    (hc : ‖c‖ ≤ (p : ℝ)⁻¹) :
    Continuous fun y : ℤ_[p] => PadicExpLog.padicExp (c * intHom ψ y) := by
  sorry
```

#### Proof sketch
1. `h3`, `hpK := norm_natCast_p ψ hψ`; for every `y`, `hdisc y : ‖c * intHom ψ y‖ ^ 2 < ‖p‖` (`‖c * ψ y‖ ≤ p⁻¹`, `norm_intHom`, `PadicInt.norm_le_one`; `p⁻² < p⁻¹`).
2. `refine (LipschitzWith.of_dist_le_mul (K := ⟨‖c‖, norm_nonneg c⟩) fun y y' => ?_).continuous`; `rw [dist_eq_norm, dist_eq_norm]`.
3. `padicExp (c ψ y) = padicExp (c ψ y') * padicExp (c ψ (y − y'))` (`padicExp_add h3 hp2`, `map_sub`, `mul_sub`), so the difference is `padicExp (cψy') * (padicExp (cψ(y−y')) − 1)`; `norm_mul`, `‖padicExp w‖ = 1` (`norm_eq_one_of_norm_sub_le` + `norm_padicExp_sub_one_le`), `norm_padicExp_sub_one_le h3 hp2 (hdisc _)`, `norm_mul`, `norm_intHom`.

#### Mathlib lemmas needed
- `LWX.PadicExpLog.padicExp_add` (`PadicExpLog.lean:410`)
- `LWX.PadicExpLog.norm_padicExp_sub_one_le`
- `LipschitzWith.of_dist_le_mul`
- `LWX.norm_intHom`, `PadicInt.norm_le_one`

#### Sources
`exp` is `1`-Lipschitz on its disc ([Kob84, Ch. IV §2]).

#### Generality decision
Stated for `‖c‖ ≤ p⁻¹`; could be generalised to the whole disc later.

---
### [CLEANUP-B6] Cleanup `PhD/LWX/TargetPoint.lean`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean | **Depends on**: B16, B17, B18 | **Parallel**: no | **Type**: cleanup

Run `/cleanup` inline on the file (naming, docstrings, `omit`s for unused section variables,
golf, no `set_option maxHeartbeats` left behind), then `lake exe runLinter PhD.LWX.TargetPoint` and
`lake build PhD.LWX.TargetPoint`.  Cadence rule: after every third proof ticket on this file.

---
### [B19] `LWX.intHom_oneUnitPart_eq_padicExp`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean:212 | **Depends on**: — | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem intHom_oneUnitPart_eq_padicExp (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (a : ℤ_[p]ˣ) :
    intHom ψ (oneUnitPart a)
      = PadicExpLog.padicExp (((p : ℕ) : K) * intHom ψ (logQuot a)) := by
  sorry
```

#### Proof sketch
1. `hu := norm_oneUnitPart_sub_one_le a`; `hy : ‖((oneUnitPart a : ℤ_[p]) : ℚ_[p]) - 1‖ ≤ p⁻¹` (cast `((u − 1 : ℤ_p) : ℚ_p)`, `PadicInt.norm_def`).
2. `rw [intHom_apply, intHom_apply, coe_logQuot hp2, qlog, map_div₀, map_natCast, mul_div_cancel₀ _ (h : ((p:ℕ):K) ≠ 0), map_padicLog ψ hp2 hψ hy]` — careful with `(p : ℚ_[p])` vs `((p : ℕ) : ℚ_[p])` (`Nat.cast` forms agree; `push_cast` if needed).
3. `rw [PadicExpLog.padicExp_padicLog h3 hp2 hu']` with `hu' : ‖ψ u − 1‖ ^ 2 < ‖p‖` from `hψ`, `hy`, `p⁻² < p⁻¹`.

#### Mathlib lemmas needed
- `LWX.coe_logQuot` (`IntegralModel.lean:154`)
- `LWX.qlog` (`UnitsLog.lean:203`)
- `LWX.map_padicLog` (`HaloWeight.lean:452`)
- `LWX.PadicExpLog.padicExp_padicLog` (`PadicExpLog.lean:839`)
- `map_div₀`, `map_natCast`, `mul_div_cancel₀`

#### Sources
[LWX, Notation 2.1] `lwx.txt:415–416`: `(1+qℤ_p)^× ≅ ℤ_p` via `(1/q)log`.

#### Generality decision
No `map_padicExp` exists or is needed.

---
### [B20] `LWX.oneAddPow_weightPoint_mul_padicExp`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean:221 | **Depends on**: B7, B18 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem oneAddPow_weightPoint_mul_padicExp (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s t : ℤ) (y : ℤ_[p]) :
    oneAddPow (weightPoint p s ζ) (intHom ψ y)
        * PadicExpLog.padicExp (((p : ℕ) : K) * ((t - s : ℤ) : K) * intHom ψ y)
      = oneAddPow (weightPoint p t ζ) (intHom ψ y) := by
  sorry
```

#### Proof sketch
1. `hc : ‖((p:ℕ):K) * ((t - s : ℤ) : K)‖ ≤ p⁻¹` (`norm_mul`, `hpK`, `norm_intCast_le_one`).
2. `refine congr_fun (PadicInt.denseRange_natCast.equalizer ((continuous_oneAddPow_intHom ψ hψ (norm_weightPoint_lt_one hp2 hζ hpK s)).mul (continuous_padicExp_mul_intHom ψ hp2 hψ hc)) (continuous_oneAddPow_intHom ψ hψ (norm_weightPoint_lt_one hp2 hζ hpK t)) (funext fun n => ?_)) y`.
3. At `n`: `simp only [Function.comp, map_natCast, oneAddPow_natCast]`; `rw [weightPoint, weightPoint, add_sub_cancel, add_sub_cancel, mul_pow, mul_pow, ← PadicExpLog.padicExp_natCast_mul h3 hp2 hdisc_s, ← PadicExpLog.padicExp_natCast_mul h3 hp2 hdisc_t, mul_assoc, ← PadicExpLog.padicExp_add h3 hp2 _ _]; congr 2; push_cast; ring` (disc hypotheses from B4's helper with `‖(n:K)‖ ≤ 1`, `‖(s:K)‖ ≤ 1`, `‖(t−s : K)‖ ≤ 1`).

#### Mathlib lemmas needed
- `PadicInt.denseRange_natCast` (mathlib `RingHoms.lean:501`)
- `DenseRange.equalizer`
- `LWX.continuous_oneAddPow_intHom` (`PowSubOne.lean:67`)
- `LWX.oneAddPow_natCast` (`PowSubOne.lean:50`)
- B7, B18
- `LWX.PadicExpLog.padicExp_natCast_mul`, `padicExp_add`

#### Sources
[LWX, §2.1] `lwx.txt:463` (`χ(exp(p^m))^{(log x)/p^m}`) and the density pattern of `oneAddPow_pow_mul` (`PowSubOne.lean:98`).

#### Generality decision
All `s t ∈ ℤ`, all `y ∈ ℤ_p`.

---
### [B21] `LWX.specialize_univChar_targetChar`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean:232 | **Depends on**: B1, B2, B3, B6, B7, B17, B19, B20 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem specialize_univChar_targetChar (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) (a : ℤ_[p]ˣ) :
    HaloInt.specialize (intHom ψ) (weightPoint p (-(k + 2 : ℤ)) ζ) (univChar (targetChar p ω k) a)
        * intHom ψ (a : ℤ_[p]) ^ (k + 2)
      = HaloInt.specialize (intHom ψ) (classicalPoint p k ζ) (univChar ω a)
        * (intHom ψ (a : ℤ_[p]))⁻¹ ^ k := by
  sorry
```

#### Proof sketch
1. Bounds: `h0₁ h1₁` at `T₁ := weightPoint p (-(k+2)) ζ` (B6, B7); `h0₀ h1₀` at `classicalPoint p k ζ` (`ClassicalPoint.lean` or B6/B7 + B3).
2. `rw [specialize_univChar (intHom ψ) (norm_intHom ψ hψ) h0₁ h1₁, specialize_univChar (intHom ψ) (norm_intHom ψ hψ) h0₀ h1₀, targetChar_apply]`.
3. Name `x := intHom ψ (teichRes (Units.map toZMod a) : ℤ_p)`, `ℓ := intHom ψ (logQuot a)`, `e := padicExp (p * ℓ)`.  Facts: `intHom ψ (a : ℤ_p) = x * e` (`coe_eq_teichRes_mul_oneUnitPart`, `map_mul`, `intHom_oneUnitPart_eq_padicExp`); `intHom ψ ((… ^ (2k+2))⁻¹ : ℤ_pˣ) = (x ^ (2k+2))⁻¹` (`map_units_inv`, `Units.val_pow_eq_pow_val`, `map_pow`); `oneAddPow (classicalPoint p k ζ) ℓ = oneAddPow T₁ ℓ * e ^ (2k+2)` (B20 at `(s, t) = (-(k+2), k)` after `← weightPoint_natCast`; `t − s = 2k+2` by `push_cast; ring` inside the exponent, then `padicExp_natCast_mul`).
4. `x ≠ 0` (`ψ` injective on a unit: `map_ne_zero`/`Units.ne_zero`), `e ≠ 0` (`‖e − 1‖ < 1`, or `padicExp_add` with `−pℓ`); `rw` the facts, then `field_simp; ring`.

#### Mathlib lemmas needed
- `LWX.specialize_univChar` (`Specialize.lean:217`; explicit `ψ hψ h0 h1`)
- B1, B2, B3, B17, B19, B20
- `map_units_inv`, `Units.val_pow_eq_pow_val`, `map_pow`
- `LWX.PadicExpLog.padicExp_natCast_mul`

#### Sources
[LWX, §2.1] `lwx.txt:456–470` (extension formula and classical characters `x ↦ x^kψ(x)`); [LWX] `lwx.txt:2074–2076`.

#### Generality decision
The AG-ζ identity at the unit level; `ω` arbitrary.

---
### [CLEANUP-B7] Cleanup `PhD/LWX/TargetPoint.lean`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean | **Depends on**: B19, B20, B21 | **Parallel**: no | **Type**: cleanup

Run `/cleanup` inline on the file (naming, docstrings, `omit`s for unused section variables,
golf, no `set_option maxHeartbeats` left behind), then `lake exe runLinter PhD.LWX.TargetPoint` and
`lake build PhD.LWX.TargetPoint`.  Cadence rule: after every third proof ticket on this file.

---
### [B22] `LWX.targetConst_eq_classicalData_u`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean:243 | **Depends on**: B16, B21 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem targetConst_eq_classicalData_u (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) (i : ι) (t : Fin p)
    (a : ZMod (p ^ 1)) :
    haloCharFunH 1 ψ (weightPoint p (-(k + 2 : ℤ)) ζ) (targetChar p ω k)
          (certConj θG 1 ψ U hU vRep hvΔ uu i t a 1 1)
        * (certConj θG 1 ψ U hU vRep hvΔ uu i t a 1 1) ^ (k + 2)
      = (classicalData ψ ω θG U hU vRep hvΔ uu hp2 hψ hζ hpK k).u i t a := by
  sorry
```

#### Proof sketch
1. `show haloCharFunH 1 ψ _ (targetChar p ω k) _ * _ ^ (k + 2) = haloCharFunH 1 ψ (classicalPoint p k ζ) ω (certConj θG 1 ψ U hU vRep hvΔ uu i t a 1 1) * (certConj θG 1 ψ U hU vRep hvΔ uu i t a 1 1)⁻¹ ^ k` (unfolds `classicalData`'s `u` by `rfl`).
2. `rw [certConj_apply_one_one]` (both occurrences), then `rw [haloCharFunH_psi 1 ψ _ (targetChar p ω k) hp2 hψ (inv_lt_norm_weightPoint …) (norm_weightPoint_lt_one …) (norm_TH_one_weightPoint_sq_lt …) _, haloCharFunH_psi 1 ψ (classicalPoint p k ζ) ω hp2 hψ (inv_lt_norm_classicalPoint …) (norm_classicalPoint_lt_one …) (norm_TH_one_classicalPoint_sq_lt …) _]`.
3. `exact specialize_univChar_targetChar ψ ω hp2 hψ hζ hpK k _`.

#### Mathlib lemmas needed
- `LWX.haloCharFunH_psi` (`HaloWeightH.lean:731`; explicit `h ψ T₀ ω`)
- B16, B21
- `LWX.classicalData` (`ClassicalPoint.lean:443`, the `u` field)

#### Sources
**AG-ζ** (board `lwx-theta`, deferred there): the constants of the source and target weights agree.

#### Generality decision
—

---
### [B23] `LWX.targetData_classicalPoint`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean:257 | **Depends on**: B6, B7, B9, B15, B22 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem targetData_classicalPoint (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    TargetData (classicalData ψ ω θG U hU vRep hvΔ uu hp2 hψ hζ hpK k) (targetChar p ω k)
      (weightPoint p (-(k + 2 : ℤ)) ζ) where
  ... -- fields as in the skeleton (`sorry` in `shape`)
```

#### Proof sketch
`shape := fun i t a => by rw [← targetConst_eq_classicalData_u ψ ω θG U hU vRep hvΔ uu hp2 hψ hζ hpK k i t a]; exact isClassicalShape'_haloWeightH_weightPoint_neg ψ ω θG U hU vRep hvΔ uu hp2 hψ hζ k _ _ _ i t a` (the other three fields are already in the skeleton).

#### Mathlib lemmas needed
- B15, B22

#### Sources
`TargetData` (`StepThree.lean:354`).

#### Generality decision
End of Part B.

---
### [CLEANUP-B-FINAL] Cleanup `PhD/LWX/TargetPoint.lean`
- **Status**: done
- **File**: PhD/LWX/TargetPoint.lean | **Depends on**: B23 | **Parallel**: no | **Type**: cleanup

Run `/cleanup` inline on the file (naming, docstrings, `omit`s for unused section variables,
golf, no `set_option maxHeartbeats` left behind), then `lake exe runLinter PhD.LWX.TargetPoint` and
`lake build PhD.LWX.TargetPoint`.  Cadence rule: after every third proof ticket on this file.

**Final per-file duties:** decide whether `ClassicalPoint.lean`'s six `classicalPoint` lemmas
should become one-line corollaries of the `weightPoint` ones via `weightPoint_natCast` — record
the decision in `plan.md` but do **not** edit `ClassicalPoint.lean` (protected; file a note for
the user).  `omit`s for unused section variables (`Γ`, `[CharZero K]` where unused).

---
## Assembly — `PhD/LWX/DegreeFormula.lean`

### [D1] `LWX.degX_succ_of_targetData`
- **Status**: done
- **File**: PhD/LWX/DegreeFormula.lean:38 | **Depends on**: A25 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem degX_succ_of_targetData (hp2 : p ≠ 2) [Nonempty ι] [IsAlgClosed K]
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    (hdet : ∀ i t, (certM1 θG U hU vRep hvΔ uu i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p)
    {ω ω' ω₁ ω₁' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' T₁ T₁' : K} {k : ℕ}
    (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (d : TargetData c ω₁ T₁) (d' : TargetData c' ω₁' T₁')
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 k (c.matrix idx) B
      (c'.matrix idx)) :
    degX (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (k + 1)
      = ordDim (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω'
        + ordDim (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω₁ := by
  sorry
```

#### Proof sketch
`exact degX_succ idx hp2 hψ hshape hdet c c' d d' hAL (isThetaExact_classicalData idx hshape hdet c d)`.

#### Mathlib lemmas needed
- `LWX.degX_succ` (`StepThree.lean:925`)
- A25

#### Sources
[LWX, Thm 1.3] with H2 discharged.

#### Generality decision
Any classical data with targets.

---
### [CLEANUP-ALL-1] `/cleanup-all` before the milestone
- **Status**: done
- **File**: all three files | **Depends on**: CLEANUP-A-FINAL, CLEANUP-B-FINAL, D1 | **Parallel**: no | **Type**: cleanup

Whole-board `/cleanup-all` inline: cross-file naming consistency (`weightPoint`, `targetChar`,
`shiftBlock`/`insertBlock`/`diagBlock`), docstrings citing `lwx.txt`/`bu04.txt` locators, module
docstrings updated from "SKELETON" to their final form, `lake exe runLinter` on all three modules,
`lake build PhD` green.  Cadence rule: before every milestone.

---
### [D2] `LWX.degX_succ_classicalPoint`
- **Status**: done
- **File**: PhD/LWX/DegreeFormula.lean:56 | **Depends on**: D1, B23 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem degX_succ_classicalPoint (hp2 : p ≠ 2) [Nonempty ι] [IsAlgClosed K]
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    (hdet : ∀ i t, (certM1 θG U hU vRep hvΔ uu i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p)
    {ζ ζ' : K} (hζ : IsPrimitiveRoot ζ p) (hζ' : IsPrimitiveRoot ζ' p)
    (ω ω' : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ)
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 k
      ((classicalData ψ ω θG U hU vRep hvΔ uu hp2 hψ hζ (norm_natCast_p ψ hψ) k).matrix idx) B
      ((classicalData ψ ω' θG U hU vRep hvΔ uu hp2 hψ hζ' (norm_natCast_p ψ hψ) k).matrix idx)) :
    degX (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (k + 1)
      = ordDim (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω'
        + ordDim (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) (targetChar p ω k) := by
  sorry
```

#### Proof sketch
`exact degX_succ_of_targetData idx hp2 hψ hshape hdet (classicalData ψ ω θG U hU vRep hvΔ uu hp2 hψ hζ (norm_natCast_p ψ hψ) k) (classicalData ψ ω' θG U hU vRep hvΔ uu hp2 hψ hζ' (norm_natCast_p ψ hψ) k) (targetData_classicalPoint ψ ω θG U hU vRep hvΔ uu hp2 hψ hζ (norm_natCast_p ψ hψ) k) (targetData_classicalPoint ψ ω' θG U hU vRep hvΔ uu hp2 hψ hζ' (norm_natCast_p ψ hψ) k) hAL`.

#### Mathlib lemmas needed
- D1, B23
- `LWX.classicalData` (`ClassicalPoint.lean:443`)
- `LWX.norm_natCast_p`

#### Sources
[LWX, Thm 1.3] `lwx.txt:152–155`, `2074–2076`: `deg X_{k+1,ω} = r_ord(ω⁻¹ω₀^{2k}) + r_ord(ωω₀^{−2k−2})`, with `ω'` for the partner's nebentypus (identification out of scope).

#### Generality decision
**MILESTONE.** Granted H1 only.

---
### [CLEANUP-D-FINAL] Cleanup `PhD/LWX/DegreeFormula.lean`
- **Status**: done
- **File**: PhD/LWX/DegreeFormula.lean | **Depends on**: D2 | **Parallel**: no | **Type**: cleanup

Run `/cleanup` inline on the file (naming, docstrings, `omit`s for unused section variables,
golf, no `set_option maxHeartbeats` left behind), then `lake exe runLinter PhD.LWX.DegreeFormula` and
`lake build PhD.LWX.DegreeFormula`.  Cadence rule: after every third proof ticket on this file.

---
### [CLEANUP-FINAL] `/cleanup-all`, board close
- **Status**: done
- **File**: all | **Depends on**: CLEANUP-D-FINAL | **Parallel**: no | **Type**: cleanup

Final `/cleanup-all` inline; `#print axioms LWX.degX_succ_classicalPoint` (expect
`[propext, Classical.choice, Quot.sound]`); `lake build PhD` green; update this board's Summary,
`plan.md` STATUS, the `lwx-theta` board's cross-reference, `JL-AUDIT.md`'s addendum if anything
changed, and the memory file `lwx-theta-h2-board.md`.  Remove
`.mathlib-quality/lwx-theta-h2/beastmode_active` (cat before rm; never any other sentinel).

---
