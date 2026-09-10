# Ticket Board — `newton-product` (the Newton polygon of a product)

**BOARD PATH: `.mathlib-quality/newton-product/`.**  The default `.mathlib-quality/` board is the
completed NewtonPolygons project — NEVER touch it.  Every `/beastmode` run must name this board
path explicitly and use the sentinel `.mathlib-quality/newton-product/beastmode_active` (the
`lwx-theta` board runs concurrently with its own sentinel; never remove a sentinel you did not
create — `cat` it first).

**Files owned by this board**: `PhD/NewtonPolygons/Face.lean`, `PhD/NewtonPolygons/Product.lean`
(both new, skeletoned, building).  **Do not edit any other file** — in particular not
`Height.lean`, `Support.lean`, `Spec.lean`, `SpecConstruction.lean`, `CoeffVal.lean` or
`ForMathlib/…/NegLogNorm.lean` (read-only: `PhD/LWX/*` rebuilds on every change and another
board is building there).  A helper that would belong in one of those files is proved locally
(marked `-- TODO(newton-product): relocate` in a comment) and listed for CLEANUP-FINAL.

**Build**: `lake build PhD.NewtonPolygons.Product` (≈ 30 s warm; builds `Face` first).
Gate every ticket on `lake env lean <file> 2>&1 | grep -i "error\|uses \`sorry\`"` for the
declarations it closes, and `#print axioms` on the ticket's declarations
(`[propext, Classical.choice, Quot.sound]` only).  Do not use `timeout` (absent on this machine).

**Statements are protected.**  They are transcribed verbatim from the compiling skeleton.  If a
statement is wrong, file a B2 in this board's `b2_log.jsonl` (with a counterexample) rather than
editing it silently; the one sanctioned kind of edit is *weakening a hypothesis* that the proof
turns out not to need (record it in `renames.jsonl`/the ticket).

**Read before working any ticket**: `plan.md` (hypothesis discussion, read-only files) and
`decomposition.md` (source quotes, attack logs; the prose proof in six steps).

## Summary

- Total: 43 tickets — 30 proof tickets (F01–F12 on `Face.lean`, P01–P18 on `Product.lean`),
  13 cleanup tickets (CLEANUP-1…10, CLEANUP-ALL-1, CLEANUP-ALL-2, CLEANUP-FINAL).
- Open: 0 | In Progress: 0 | Done: 43 — **BOARD COMPLETE 2026-09-09**.  The five definitions (`SlopesUnbounded`, `faceLeft`,
  `faceRight`, `IsEntireNewtonPolygonOf`, `minkowskiHeight`) are already in place in the skeleton
  and need no ticket.
- Parallel capacity: **7 workers at the start** (F01, F05, F08, F10, P01, P06, P17 have no
  dependencies); the two files are disjoint, but tickets on the same file must be assigned
  explicitly to avoid a pickup race.
- **Milestones**: P12 (`height_mul`, the theorem) and P18 (`height_newtonPolygon₀OfPowerSeries_mul_coe`,
  the LWX-facing polynomial-factor form).

## Dependency order

```
Face.lean:    F01 → F02 → F03 [CLEANUP-1] → F04
              F05 → F06 [CLEANUP-2] → F07 (needs F02, F03)
              F08 → F09 (needs F03) [CLEANUP-3]   F10   F11 (needs F01)   F12 (needs F05, F08, F09)
              [CLEANUP-4 = final Face.lean, after F12]
Product.lean: P01 → P02 (F02) → P03 [CLEANUP-5]
              P04 (F07, P02) → P05 (F05, F06, P04)
              P06 [CLEANUP-6] → P07 → P08 (F08)
              P09 (P01–P03, P08, F10) [CLEANUP-7]     P10 (P04, P07, F12)     P11 (P03, P05, P10, F05)
              [CLEANUP-ALL-1] → P12 (P09, P11) [CLEANUP-8]
              P13 (P12, F01)   P14 (P12, P04, P05, F05, F07)   P15 (F08, F11) [CLEANUP-9]
              P16 (P12–P15)   P17   [CLEANUP-ALL-2] → P18 (P16, P17) [CLEANUP-10 = final Product.lean]
              [CLEANUP-FINAL]
```

## Ready now (no dependencies)

F01, F05, F08, F10, P01, P06, P17.

---

## Face.lean

### [F01] Prove `heightFun_sub_eq_sum`
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Face.lean:79 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma

#### Statement
```lean
theorem heightFun_sub_eq_sum {m n : ℕ} (hmn : m ≤ n) :
    P.heightFun n - P.heightFun m = ∑ i ∈ Ico m n, NewtonPolygon.toReal (P.unitSlope i) := by
  sorry
```
#### Proof sketch
1. `rw [NewtonPolygon₀.heightFun, NewtonPolygon₀.heightFun, Finset.sum_Ico_eq_sub _ hmn]` — the
   height is the anchor plus a `range`-sum of unit slopes.
2. `ring`.
(This is `Height.lean:681`'s private `heightFun_sub`; re-derived because that file is read-only.)
#### Mathlib lemmas needed
`Finset.sum_Ico_eq_sub` (`AddCommGroup ℝ`).
#### Sources
Definition of the polygon as a broken line: [Ked07, §1]; `Height.lean:64` (`heightFun`).
#### Generality decision
Stated over `Γ = ℝ` (the file's standing variable); the `Γ`-general form is the private one in
`Height.lean` — do not generalise here.

### [F02] Prove `line_le_height_of_unitSlope` (the supporting line at an index)
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Face.lean:87 | **Depends on**: F01
- **Parallel**: yes (with F05, F08, F10) | **Type**: lemma

#### Statement
```lean
theorem line_le_height_of_unitSlope (hx : P.starting_point.1 = 0) (hb : ∀ j, P.unitSlope j ≠ ⊥)
    {i₀ : ℕ} {σ : ℝ} (h₁ : ∀ t, t < i₀ → P.unitSlope t ≤ (σ : WithBotTop ℝ))
    (h₂ : ∀ t, i₀ ≤ t → (σ : WithBotTop ℝ) ≤ P.unitSlope t) {y : ℝ}
    (hy : P.height i₀ = (y : WithBotTop ℝ)) (k : ℕ) :
    ((y + σ * ((k : ℝ) - i₀) : ℝ) : WithBotTop ℝ) ≤ P.height k := by
  sorry
```
#### Proof sketch
1. If `P.height k = ⊤`: `le_top`.  Otherwise (`hk`), every unit slope `t < k` is `≠ ⊤`
   (`P.unitSlope_ne_top_of_height_ne_top`, after rewriting `(k : ℤ) = P.starting_point.1 + k` with
   `hx`), and `≠ ⊥` by `hb`; so for `t < k`, `P.unitSlope t = (toReal (P.unitSlope t) : WithBotTop ℝ)`
   (`WithBotTop.rec` on the value, as in `OfSlopes.lean:159` `coe_toReal_eq_self`).
2. Rewrite both heights through `P.height_eq_heightFun` (`hy` gives `y = P.heightFun i₀` by
   `WithBotTop.coe_injective`; note `hy` also gives `P.height i₀ ≠ ⊤`).
3. Case `i₀ ≤ k`: by F01, `heightFun k − heightFun i₀ = ∑_{Ico i₀ k} toReal (unitSlope t) ≥ (k − i₀) σ`
   (`Finset.card_nsmul_le_sum`, each term `≥ σ` from `h₂` and step 1's coercion identity via
   `WithBotTop.coe_le_coe`; `Nat.card_Ico`).  Case `k < i₀`: `heightFun i₀ − heightFun k =
   ∑_{Ico k i₀} … ≤ (i₀ − k) σ` (`Finset.sum_le_card_nsmul`, from `h₁`; these slopes are `≠ ⊤`
   because `height i₀ ≠ ⊤`).
4. Conclude with `WithBotTop.coe_le_coe.2` and `linarith`/`nlinarith` after `push_cast`.
#### Mathlib lemmas needed
`Finset.card_nsmul_le_sum`, `Finset.sum_le_card_nsmul`, `Nat.card_Ico`, `WithBotTop.coe_le_coe`,
`WithBotTop.coe_injective`, `WithBotTop.rec`; project `NewtonPolygon₀.height_eq_heightFun`
(`Height.lean:566`), `unitSlope_ne_top_of_height_ne_top` (`Height.lean:577`), `NewtonPolygon.toReal_coe`.
#### Sources
[Ked07, §2] "`v_r` is the `y`-intercept of the supporting line of the Newton polygon of slope
`r`"; decomposition F02.
#### Generality decision
Hypotheses `hx` (anchor) and `hb` (no `⊥`) are both used (steps 1–2); `⊤` unit slopes are
allowed (they only occur where the conclusion is `le_top`).

### [F03] Prove the strict supporting lines `line_lt_height_of_unitSlope_lt`, `line_lt_height_of_lt_unitSlope`
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Face.lean:96,106 | **Depends on**: F02
- **Parallel**: yes | **Type**: lemma (2)

#### Statement
```lean
theorem line_lt_height_of_unitSlope_lt (hx : P.starting_point.1 = 0)
    (hb : ∀ j, P.unitSlope j ≠ ⊥) {i₀ : ℕ} {σ : ℝ}
    (h₁ : ∀ t, t < i₀ → P.unitSlope t < (σ : WithBotTop ℝ))
    (h₂ : ∀ t, i₀ ≤ t → (σ : WithBotTop ℝ) ≤ P.unitSlope t) {y : ℝ}
    (hy : P.height i₀ = (y : WithBotTop ℝ)) {k : ℕ} (hk : k < i₀) :
    ((y + σ * ((k : ℝ) - i₀) : ℝ) : WithBotTop ℝ) < P.height k := by
  sorry

theorem line_lt_height_of_lt_unitSlope (hx : P.starting_point.1 = 0)
    (hb : ∀ j, P.unitSlope j ≠ ⊥) {i₀ : ℕ} {σ : ℝ}
    (h₁ : ∀ t, t < i₀ → P.unitSlope t ≤ (σ : WithBotTop ℝ))
    (h₂ : ∀ t, i₀ ≤ t → (σ : WithBotTop ℝ) < P.unitSlope t) {y : ℝ}
    (hy : P.height i₀ = (y : WithBotTop ℝ)) {k : ℕ} (hk : i₀ < k) :
    ((y + σ * ((k : ℝ) - i₀) : ℝ) : WithBotTop ℝ) < P.height k := by
  sorry
```
#### Proof sketch
1. Same setup as F02 (steps 1–2).  For the first lemma `height k ≠ ⊤` follows from
   `height i₀ ≠ ⊤` and `k < i₀` (`height_eq_top_mono` contrapositive); for the second, if
   `height k = ⊤` the strict inequality is `WithBotTop.coe_lt_top`-style (`lt_top_iff_ne_top` +
   `WithBotTop.coe_ne_top`) — close immediately.
2. Replace the non-strict sum bound of F02 by a strict one: `Finset.sum_lt_sum_of_nonempty` over
   `Ico k i₀` (resp. `Ico i₀ k`), nonempty by `hk` (`Finset.nonempty_Ico`), each term strictly
   below/above `σ` from `h₁`/`h₂`.
3. `WithBotTop.coe_lt_coe.2` + `linarith`.
#### Mathlib lemmas needed
`Finset.sum_lt_sum_of_nonempty`, `Finset.nonempty_Ico`, `WithBotTop.coe_lt_coe`, `lt_top_iff_ne_top`;
project `height_eq_top_mono` (`Height.lean:556`).
#### Sources
[Kob84, Lemma 6 proof] "If `(i, ord_p a_i)` is a vertex, then `ord_p a_{i+1} > ord_p a_i`";
decomposition F03.
#### Generality decision
As F02; the strict side of each hypothesis is what produces the strict conclusion, the other side
stays non-strict.

### [CLEANUP-1] Run /cleanup on PhD/NewtonPolygons/Face.lean (after F03)
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Face.lean | **Depends on**: F01, F02, F03
- **Parallel**: no | **Type**: cleanup
- Cadence cleanup (3 proof tickets on the file).  Run `/cleanup` on the proved declarations only
  (leave the sorried ones); `lake exe runLinter PhD.NewtonPolygons.Face`.

### [F04] Prove `height_eq_of_forall_unitSlope_eq`
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Face.lean:115 | **Depends on**: CLEANUP-1
- **Parallel**: yes | **Type**: lemma

#### Statement
```lean
theorem height_eq_of_forall_unitSlope_eq (hx : P.starting_point.1 = 0) {i₀ : ℕ} {σ y : ℝ}
    (hy : P.height i₀ = (y : WithBotTop ℝ)) {k : ℕ} (hik : i₀ ≤ k)
    (h : ∀ t, i₀ ≤ t → t < k → P.unitSlope t = (σ : WithBotTop ℝ)) :
    P.height k = ((y + σ * ((k : ℝ) - i₀) : ℝ) : WithBotTop ℝ) := by
  sorry
```
#### Proof sketch
1. Write `k = i₀ + d` (`obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hik`), induct on `d`.
2. Base: `hy` (after `simp`).  Step: `height (i₀ + d + 1) ≠ ⊤` because the unit slope at `i₀ + d`
   is the real `σ` (`unitSlope_eq_top_of_height_eq_top` would force `⊤`); then
   `height_eq_heightFun` at `d` and `d + 1`, `heightFun_succ`, `h`, `NewtonPolygon.toReal_coe`,
   `push_cast; ring`.  (Same telescoping as the private `SpecConstruction.lean:283`.)
#### Mathlib lemmas needed
`Nat.exists_eq_add_of_le`; project `height_eq_heightFun`, `heightFun_succ` (`Height.lean:76`),
`unitSlope_eq_top_of_height_eq_top` (`Height.lean:542`).
#### Sources
[Ked07, §1] the polygon is a broken line; decomposition F04.
#### Generality decision
No `hb`: the hypothesis pins every slope in range to a real.

### [F05] Prove the face-index API (9 lemmas)
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Face.lean:124–164 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma (9)

#### Statement
```lean
theorem SlopesUnbounded.exists_le (hP : P.SlopesUnbounded) (σ : ℝ) :
    ∃ j : ℕ, (σ : WithBotTop ℝ) ≤ P.unitSlope j := by sorry
theorem unitSlope_lt_of_lt_faceLeft {σ : ℝ} {j : ℕ} (hj : j < P.faceLeft σ) :
    P.unitSlope j < (σ : WithBotTop ℝ) := by sorry
theorem le_unitSlope_of_faceLeft_le (hP : P.SlopesUnbounded) {σ : ℝ} {j : ℕ}
    (hj : P.faceLeft σ ≤ j) : (σ : WithBotTop ℝ) ≤ P.unitSlope j := by sorry
theorem faceLeft_le_of_le_unitSlope {σ : ℝ} {j : ℕ} (hj : (σ : WithBotTop ℝ) ≤ P.unitSlope j) :
    P.faceLeft σ ≤ j := by sorry
theorem unitSlope_le_of_lt_faceRight {σ : ℝ} {j : ℕ} (hj : j < P.faceRight σ) :
    P.unitSlope j ≤ (σ : WithBotTop ℝ) := by sorry
theorem lt_unitSlope_of_faceRight_le (hP : P.SlopesUnbounded) {σ : ℝ} {j : ℕ}
    (hj : P.faceRight σ ≤ j) : (σ : WithBotTop ℝ) < P.unitSlope j := by sorry
theorem le_faceRight_of_forall_le (hP : P.SlopesUnbounded) {σ : ℝ} {j : ℕ}
    (hj : ∀ t, t < j → P.unitSlope t ≤ (σ : WithBotTop ℝ)) : j ≤ P.faceRight σ := by sorry
theorem faceLeft_le_faceRight (hP : P.SlopesUnbounded) (σ : ℝ) : P.faceLeft σ ≤ P.faceRight σ := by
  sorry
theorem faceRight_le_faceLeft_of_lt (hP : P.SlopesUnbounded) {σ τ : ℝ} (h : σ < τ) :
    P.faceRight σ ≤ P.faceLeft τ := by sorry
```
#### Proof sketch
1. `exists_le`: `(hP σ).imp fun j hj => hj.le`.
2. `unitSlope_lt_of_lt_faceLeft`: `not_le.1 (Nat.notMem_of_lt_sInf hj)` (membership unfolds by
   `Set.mem_setOf_eq`).  Same for `unitSlope_le_of_lt_faceRight`.
3. `le_unitSlope_of_faceLeft_le`: `Nat.sInf_mem ⟨_, hP.exists_le σ⟩` gives the bound at
   `faceLeft σ`; transport to `j` by `P.unitSlope_mono hj`.  Same for `lt_unitSlope_of_faceRight_le`
   with `hP σ` and `lt_of_lt_of_le`.
4. `faceLeft_le_of_le_unitSlope`: `Nat.sInf_le hj`.
5. `le_faceRight_of_forall_le`: by contradiction, `faceRight σ < j` puts `faceRight σ` in the set
   (`Nat.sInf_mem`, nonempty by `hP σ`), contradicting `hj` (`not_lt.2`).
6. `faceLeft_le_faceRight`: `Nat.sInf_le` with `lt_unitSlope_of_faceRight_le hP le_rfl |>.le`.
7. `faceRight_le_faceLeft_of_lt`: the set for `τ`'s `faceLeft` is contained in the set for `σ`'s
   `faceRight` (`σ < τ ≤ s`), so `Nat.sInf_le` on the member `faceLeft τ` (`Nat.sInf_mem` with
   `hP.exists_le τ`).
#### Mathlib lemmas needed
`Nat.sInf_mem`, `Nat.sInf_le`, `Nat.notMem_of_lt_sInf`, `Set.mem_setOf_eq`, `not_le`, `not_lt`;
project `NewtonPolygon₀.unitSlope_mono` (`Height.lean:421`).
#### Sources
[Ked07, Cor. 2 proof] the endpoints of the segment of slope `r`; decomposition D2/D3, F05.
#### Generality decision
`hP` only where the `sInf` set must be nonempty (`sInf_mem`); the other lemmas are unconditional.

### [F06] Prove `exists_height_faceLeft_eq`, `exists_height_faceRight_eq`, `height_eq_of_mem_face`
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Face.lean:170,175,180 | **Depends on**: F04, F05
- **Parallel**: yes | **Type**: lemma (3)

#### Statement
```lean
theorem exists_height_faceLeft_eq (hx : P.starting_point.1 = 0) (σ : ℝ) :
    ∃ y : ℝ, P.height (P.faceLeft σ) = (y : WithBotTop ℝ) := by sorry
theorem exists_height_faceRight_eq (hx : P.starting_point.1 = 0) (σ : ℝ) :
    ∃ y : ℝ, P.height (P.faceRight σ) = (y : WithBotTop ℝ) := by sorry
theorem height_eq_of_mem_face (hx : P.starting_point.1 = 0) (hP : P.SlopesUnbounded) {σ y : ℝ}
    (hy : P.height (P.faceLeft σ) = (y : WithBotTop ℝ)) {k : ℕ} (h1 : P.faceLeft σ ≤ k)
    (h2 : k ≤ P.faceRight σ) :
    P.height k = ((y + σ * ((k : ℝ) - P.faceLeft σ) : ℝ) : WithBotTop ℝ) := by sorry
```
#### Proof sketch
1. `exists_height_*`: the height at a natural is `≠ ⊥` (`height_eq_bot_iff`, `hx`) and `≠ ⊤`:
   if it were `⊤`, `unitSlope_eq_top_of_height_eq_top` gives a `⊤` unit slope at an index
   `< faceLeft σ` (resp. `< faceRight σ`), contradicting `unitSlope_lt_of_lt_faceLeft`
   (resp. `unitSlope_le_of_lt_faceRight`) since `⊤ < σ`/`⊤ ≤ σ` is false (`not_top_lt`,
   `top_le_iff` + `WithBotTop.coe_ne_top`).  Extract the real with `WithBotTop.rec`.
2. `height_eq_of_mem_face`: F04 with `i₀ := faceLeft σ`; the slope hypothesis on `[faceLeft, k)` is
   `le_antisymm (unitSlope_le_of_lt_faceRight (lt_of_lt_of_le ht h2)) (le_unitSlope_of_faceLeft_le hP hi)`.
#### Mathlib lemmas needed
`not_top_lt`, `top_le_iff`, `WithBotTop.coe_ne_top`, `WithBotTop.rec`; project
`height_eq_bot_iff` (`Height.lean:533`), `unitSlope_eq_top_of_height_eq_top`.
#### Sources
[Ked07, Cor. 2] "the segment of slope `r`"; decomposition F06.
#### Generality decision
The two existence lemmas need neither `hP` nor `hb` (junk `sInf = 0` is the anchor, finite).

### [CLEANUP-2] Run /cleanup on PhD/NewtonPolygons/Face.lean (after F06)
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Face.lean | **Depends on**: F04, F05, F06
- **Parallel**: no | **Type**: cleanup

### [F07] Prove the four face supporting lines
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Face.lean:188–210 | **Depends on**: CLEANUP-2, F02, F03
- **Parallel**: yes | **Type**: lemma (4)

#### Statement
```lean
theorem faceLeft_line_le_height (hx : P.starting_point.1 = 0) (hb : ∀ j, P.unitSlope j ≠ ⊥)
    (hP : P.SlopesUnbounded) {σ y : ℝ} (hy : P.height (P.faceLeft σ) = (y : WithBotTop ℝ))
    (k : ℕ) : ((y + σ * ((k : ℝ) - P.faceLeft σ) : ℝ) : WithBotTop ℝ) ≤ P.height k := by sorry
theorem faceLeft_line_lt_height (hx : P.starting_point.1 = 0) (hb : ∀ j, P.unitSlope j ≠ ⊥)
    (hP : P.SlopesUnbounded) {σ y : ℝ} (hy : P.height (P.faceLeft σ) = (y : WithBotTop ℝ))
    {k : ℕ} (hk : k < P.faceLeft σ) :
    ((y + σ * ((k : ℝ) - P.faceLeft σ) : ℝ) : WithBotTop ℝ) < P.height k := by sorry
theorem faceRight_line_le_height (hx : P.starting_point.1 = 0) (hb : ∀ j, P.unitSlope j ≠ ⊥)
    (hP : P.SlopesUnbounded) {σ y : ℝ} (hy : P.height (P.faceRight σ) = (y : WithBotTop ℝ))
    (k : ℕ) : ((y + σ * ((k : ℝ) - P.faceRight σ) : ℝ) : WithBotTop ℝ) ≤ P.height k := by sorry
theorem faceRight_line_lt_height (hx : P.starting_point.1 = 0) (hb : ∀ j, P.unitSlope j ≠ ⊥)
    (hP : P.SlopesUnbounded) {σ y : ℝ} (hy : P.height (P.faceRight σ) = (y : WithBotTop ℝ))
    {k : ℕ} (hk : P.faceRight σ < k) :
    ((y + σ * ((k : ℝ) - P.faceRight σ) : ℝ) : WithBotTop ℝ) < P.height k := by sorry
```
#### Proof sketch
Each is F02 or F03 at `i₀ := faceLeft σ` (hypotheses `unitSlope_lt_of_lt_faceLeft` (as `≤` via
`.le` for F02) and `le_unitSlope_of_faceLeft_le hP`) or at `i₀ := faceRight σ`
(`unitSlope_le_of_lt_faceRight`, `lt_unitSlope_of_faceRight_le hP`).  Four `exact` lines.
#### Mathlib lemmas needed
None beyond F02/F03/F05.
#### Sources
[Ked07, Cor. 2 proof]; decomposition F07.
#### Generality decision
As F02/F03.

### [F08] Prove the spec basics `starting_point_fst_eq_zero`, `height_zero_eq`, `height_ne_top_of_ne_top`
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Face.lean:237,242,247 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma (3)

#### Statement
```lean
theorem starting_point_fst_eq_zero (h : IsNewtonPolygonOf v P) (h0 : v 0 ≠ ⊤) :
    P.starting_point.1 = 0 := by sorry
theorem height_zero_eq (h : IsNewtonPolygonOf v P) (hx : P.starting_point.1 = 0) :
    P.height 0 = pointHeight v 0 := by sorry
theorem height_ne_top_of_ne_top (h : IsNewtonPolygonOf v P) {k : ℕ} (hk : v k ≠ ⊤) :
    P.height k ≠ ⊤ := by sorry
```
#### Proof sketch
1. `starting_point_fst_eq_zero`: `h.starting_point_fst_le h0` gives `x₀ ≤ 0`; `h.start_mem` gives
   `x₀ = (k : ℤ)` for some `k : ℕ`, so `0 ≤ x₀`; `omega`/`le_antisymm`.
2. `height_zero_eq`: from `h.start_mem` obtain `k, hk : (k : ℤ) = x₀, hv : v k = y₀`; `hx` forces
   `k = 0`; then `P.height 0 = P.height x₀ = y₀` by `NewtonPolygon.height_startingPoint` (through
   `height_toNewtonPolygon`, `startHeight`, `Algebra.algebraMap_self_apply`) and
   `pointHeight_coe hv`.
3. `height_ne_top_of_ne_top`: `h.height_le k` with `pointHeight_eq_top_iff.not.2 hk`
   (`ne_top_of_le_ne_top`).
#### Mathlib lemmas needed
`ne_top_of_le_ne_top`, `Algebra.algebraMap_self_apply`; project `IsNewtonPolygonOf.starting_point_fst_le`
(`Spec.lean:84`), `start_mem`, `height_le`, `pointHeight_coe`, `pointHeight_eq_top_iff` (`Spec.lean:39`),
`NewtonPolygon.height_startingPoint` (`Basic.lean:223`), `NewtonPolygon₀.height_toNewtonPolygon`.
#### Sources
[Kob84, p. 97] the polygon is anchored at `(0, 0)` and lies on/below the points; decomposition F08.
#### Generality decision
Stated for arbitrary `v : ℕ → WithTop ℝ` (spec level, `Γ = ℝ`).

### [F09] Prove `height_eq_pointHeight_of_unitSlope_lt` (a vertex is a point)
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Face.lean:256 | **Depends on**: F03, F08
- **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem height_eq_pointHeight_of_unitSlope_lt (h : IsNewtonPolygonOf v P)
    (hx : P.starting_point.1 = 0) (hb : ∀ j, P.unitSlope j ≠ ⊥) {i : ℕ}
    (hi : P.unitSlope i < P.unitSlope (i + 1)) :
    P.height ((i + 1 : ℕ) : ℤ) = pointHeight v (i + 1) := by
  sorry
```
#### Proof sketch
1. `height (i+1) ≠ ⊤` (`unitSlope i ≠ ⊤` from `hi`, via `unitSlope_ne_top_of_height_ne_top`'s
   contrapositive `unitSlope_eq_top_of_height_eq_top` + `unitSlope_mono`); get the real `hval`.
   `refine le_antisymm (h.height_le _) ?_`; by contradiction assume `height (i+1) < pointHeight v (i+1)`.
2. Pick `σ : ℝ` with `unitSlope i < σ < unitSlope (i+1)` (if `unitSlope (i+1) = ⊤`, take
   `σ := toReal (unitSlope i) + 1`; else `exists_between`), and `δ := min(σ − s_i, s_{i+1} − σ) > 0`
   (`δ := 1` in the `⊤` case).
3. Choose `ε > 0` with `ε ≤ δ` and `hval + ε ≤ pointHeight v (i+1)` (if the point is `⊤` take
   `ε := δ`; else `ε := min δ (p − hval)` where `p` is the real point, positive by the
   contradiction hypothesis).
4. Show the line `L k := hval + ε + σ (k − (i+1))` is `≤ pointHeight v k` for all `k`: at
   `k = i + 1` by choice of `ε`; for `k ≠ i + 1` use F03 (strict lines at `i₀ := i + 1`: hypotheses
   `∀ t < i+1, unitSlope t < σ` by `unitSlope_mono` + `hi`'s left bound, and `∀ t ≥ i+1, σ < unitSlope t`)
   to get `hval + σ (k − (i+1)) < height k ≤ pointHeight v k`, and sharpen by `ε`: the strict
   inequality has slack `≥ |k − (i+1)| δ ≥ δ ≥ ε` (unfold the F03 proof's sum bound, or restate F03
   with the explicit margin — recommended: prove a private `line_add_le_height` giving
   `hval + δ|k − (i+1)| + σ(k − (i+1)) ≤ height k`, same proof as F03 with `Finset.card_nsmul_le_sum`
   on the margin).
5. `h.line_le_height hx` (with `a := hval + ε − σ (i+1)`, `b := σ`) at `k := i + 1` gives
   `hval + ε ≤ height (i+1) = hval` — contradiction.
#### Mathlib lemmas needed
`exists_between`, `lt_min_iff`, `le_min`, `WithBotTop.coe_lt_coe`; project
`IsNewtonPolygonOf.line_le_height` (`Support.lean:151`), `height_le`, F03, F08,
`unitSlope_mono`, `unitSlope_eq_top_of_height_eq_top`.
#### Sources
[Kob84, p. 97] "By the vertices of the Newton polygon we mean the points `(i_j, ord_p a_{i_j})`
where the slopes change"; [Ked07, Cor. 2 proof]; decomposition F09 (with the raised-line argument).
#### Generality decision
Spec level, arbitrary `v`; `hb` needed for a real `σ` below `unitSlope (i+1)`.

### [CLEANUP-3] Run /cleanup on PhD/NewtonPolygons/Face.lean (after F09)
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Face.lean | **Depends on**: F07, F08, F09
- **Parallel**: no | **Type**: cleanup

### [F10] Prove `height_eq_top_of_forall_eq_top` (`⊤` beyond the last point)
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Face.lean:265 | **Depends on**: none
- **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem height_eq_top_of_forall_eq_top (h : IsNewtonPolygonOf v P) (hx : P.starting_point.1 = 0)
    {n : ℕ} (hn : 0 < n) (hv : ∀ k, n ≤ k → v k = ⊤) : P.height n = ⊤ := by
  sorry
```
#### Proof sketch
1. By contradiction: `height n ≠ ⊤`, and `≠ ⊥` (`height_eq_bot_iff`, `hx`), so `height n = hval`.
2. Choose `σ : ℝ` so that for every `k < n` with `v k = (a : ℝ)`, `hval + 1 − σ (n − k) ≤ a`:
   `σ := max 0 (sup over the finite set of such k of (hval + 1 − a)/(n − k))` — build it with
   `Finset.exists_le`/`Finset.sup'` over `range n`, or crudely `σ := hval + 1 + ∑_{k<n} |toReal-ish|`;
   simplest: `σ := max 0 (∑ k ∈ range n, |hval + 1 − a_k|)` where `a_k := 0` if `v k = ⊤`, since
   `n − k ≥ 1`.
3. The line `L k := (hval + 1 − σ n) + σ k` is `≤ pointHeight v k` for all `k`: `k ≥ n` by `hv`
   (`pointHeight_eq_top_iff`, `le_top`); `k < n` by the choice of `σ` (`pointHeight_coe`).
4. `h.line_le_height hx` at `k := n`: `hval + 1 ≤ height n = hval` — `linarith`.
#### Mathlib lemmas needed
`Finset.single_le_sum`, `abs_nonneg`, `le_abs_self`, `Finset.mem_range`; project
`IsNewtonPolygonOf.line_le_height`, `height_eq_bot_iff`, `pointHeight_coe`, `pointHeight_eq_top_iff`.
#### Sources
[Kob84, p. 97] the polygon of a polynomial ends at `(n, ord_p a_n)`; [Ked07, §1] the `+∞`
convention; decomposition F10.
#### Generality decision
No `hb`; `0 < n` is necessary (the anchor is a finite point).

### [F11] Prove `slopesUnbounded_of_forall_line`
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Face.lean:273 | **Depends on**: F01
- **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem slopesUnbounded_of_forall_line (h : IsNewtonPolygonOf v P) (hx : P.starting_point.1 = 0)
    (hb : ∀ j, P.unitSlope j ≠ ⊥)
    (hl : ∀ σ : ℝ, ∃ b : ℝ, ∀ k : ℕ, ((b + σ * k : ℝ) : WithBotTop ℝ) ≤ pointHeight v k) :
    P.SlopesUnbounded := by
  sorry
```
#### Proof sketch
1. Fix `σ`; by contradiction assume `∀ j, P.unitSlope j ≤ σ` (`not_lt`).  Then no unit slope is
   `⊤`, so every `height k` is finite (`unitSlope_eq_top_of_height_eq_top`), and with `hb` each
   `toReal (unitSlope j) ≤ σ`.
2. F01 from `0`: `heightFun k ≤ heightFun 0 + σ k` (`Finset.sum_le_card_nsmul`).
3. `hl (σ + 1)` gives `b`; `h.line_le_height hx` gives `b + (σ + 1) k ≤ height k = heightFun k`
   for all `k` (`height_eq_heightFun`).
4. Combine: `b + (σ + 1) k ≤ heightFun 0 + σ k`, i.e. `k ≤ heightFun 0 − b` for all `k : ℕ` —
   contradiction at `k := ⌈heightFun 0 − b⌉₊ + 1` (`Nat.lt_ceil`/`Nat.le_ceil`).
#### Mathlib lemmas needed
`not_lt`, `Finset.sum_le_card_nsmul`, `Nat.ceil_lt_add_one`/`Nat.le_ceil`, `WithBotTop.coe_le_coe`;
project `line_le_height`, `height_eq_heightFun`, `unitSlope_eq_top_of_height_eq_top`.
#### Sources
[Kob84, §IV.4 Lemma 5, p. 101] (radius of convergence is `p^{sup of slopes}`; `b = +∞` for entire
series); decomposition F11.
#### Generality decision
Spec level; the hypothesis is "affine floor of every slope", which is what restrictedness at every
radius provides (P15) — kept abstract so polynomials and entire series share the lemma.

### [F12] Prove `height_faceLeft_eq_pointHeight`, `height_faceRight_eq_pointHeight`
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Face.lean:280,286 | **Depends on**: CLEANUP-3, F05, F08, F09
- **Parallel**: yes | **Type**: theorem (2)

#### Statement
```lean
theorem height_faceLeft_eq_pointHeight (h : IsNewtonPolygonOf v P) (hx : P.starting_point.1 = 0)
    (hb : ∀ j, P.unitSlope j ≠ ⊥) (hP : P.SlopesUnbounded) (σ : ℝ) :
    P.height (P.faceLeft σ) = pointHeight v (P.faceLeft σ) := by sorry
theorem height_faceRight_eq_pointHeight (h : IsNewtonPolygonOf v P) (hx : P.starting_point.1 = 0)
    (hb : ∀ j, P.unitSlope j ≠ ⊥) (hP : P.SlopesUnbounded) (σ : ℝ) :
    P.height (P.faceRight σ) = pointHeight v (P.faceRight σ) := by sorry
```
#### Proof sketch
1. `cases hf : P.faceLeft σ` — if `0`: `h.height_zero_eq hx` (F08).  If `i + 1`: apply F09 with
   `hi : unitSlope i < unitSlope (i+1)` from `unitSlope_lt_of_lt_faceLeft (by omega)` and
   `le_unitSlope_of_faceLeft_le hP le_rfl` (`lt_of_lt_of_le`), then rewrite `hf`.
2. `faceRight`: same with `unitSlope_le_of_lt_faceRight` and `lt_unitSlope_of_faceRight_le hP`.
#### Mathlib lemmas needed
`lt_of_lt_of_le`, `lt_of_le_of_lt`; F05, F08, F09.
#### Sources
[Ked07, Cor. 2 proof]; decomposition F12.
#### Generality decision
As F09.

### [CLEANUP-4] Run /cleanup on PhD/NewtonPolygons/Face.lean (final per-file)
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Face.lean | **Depends on**: F10, F11, F12
- **Parallel**: no | **Type**: cleanup
- Whole-file `/cleanup` (no sorries should remain); `lake exe runLinter PhD.NewtonPolygons.Face`;
  `#print axioms` on every declaration of the file.

---

## Product.lean

### [P01] Prove the `minkowskiHeight` API (7 lemmas)
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Product.lean:75–103 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma (7)

#### Statement
```lean
theorem minkowskiHeight_le {n i : ℕ} (hi : i ≤ n) :
    P.minkowskiHeight Q n ≤ P.height i + Q.height (n - i) := by sorry
theorem le_minkowskiHeight_iff {n : ℕ} {a : WithBotTop ℝ} :
    a ≤ P.minkowskiHeight Q n ↔ ∀ i, i ≤ n → a ≤ P.height i + Q.height (n - i) := by sorry
theorem exists_minkowskiHeight_eq (n : ℕ) :
    ∃ i, i ≤ n ∧ P.minkowskiHeight Q n = P.height i + Q.height (n - i) := by sorry
theorem minkowskiHeight_comm (n : ℕ) : P.minkowskiHeight Q n = Q.minkowskiHeight P n := by sorry
@[simp] theorem minkowskiHeight_zero : P.minkowskiHeight Q 0 = P.height 0 + Q.height 0 := by sorry
theorem minkowskiHeight_ne_bot (hP : P.starting_point.1 = 0) (hQ : Q.starting_point.1 = 0)
    (n : ℕ) : P.minkowskiHeight Q n ≠ ⊥ := by sorry
theorem minkowskiHeight_eq_top_mono (hP : P.starting_point.1 = 0) (hQ : Q.starting_point.1 = 0)
    {m n : ℕ} (h : P.minkowskiHeight Q m = ⊤) (hmn : m ≤ n) : P.minkowskiHeight Q n = ⊤ := by sorry
```
#### Proof sketch
1. `_le`: `Finset.inf_le (Finset.mem_range.2 (Nat.lt_succ_of_le hi))`.
2. `le_…_iff`: `Finset.le_inf_iff` + `Finset.mem_range` + `Nat.lt_succ_iff`.
3. `exists_…`: `Finset.exists_mem_eq_inf _ Finset.nonempty_range_succ _`.
4. `_comm`: `le_antisymm` twice via `le_minkowskiHeight_iff`, using the split `n − i` and
   `Nat.sub_sub_self`, `add_comm`.
5. `_zero`: `simp [minkowskiHeight]` (`Finset.range_one`, `Finset.inf_singleton`).
6. `_ne_bot`: `Finset.inf` over a linear order is attained (step 3); a sum `P.height i + Q.height j`
   with both `≠ ⊥` (`height_eq_bot_iff`, anchors) is `≠ ⊥` (`WithBot.add_eq_bot`).
7. `_eq_top_mono`: `Finset.inf_eq_top_iff` at `m` gives every split `⊤`; for a split `(i, n − i)`
   of `n`: if `i ≤ m` use the split `(i, m − i)` and `height_eq_top_mono` on `Q` (`m − i ≤ n − i`);
   if `i > m` use the split `(m, 0)` — `Q.height 0 ≠ ⊤` (`NewtonPolygon.height_startingPoint` +
   `hQ`), so `P.height m = ⊤` and `height_eq_top_mono` on `P`.  Sum with a `⊤` term is `⊤`
   (`WithBot.add_eq_top`/`top_add`/`add_top`; heights are `≠ ⊥`).
#### Mathlib lemmas needed
`Finset.inf_le`, `Finset.le_inf_iff`, `Finset.exists_mem_eq_inf`, `Finset.inf_eq_top_iff`,
`Finset.mem_range`, `Finset.nonempty_range_succ`, `Nat.sub_sub_self`, `WithBot.add_eq_bot`,
`WithBot.add_eq_top`, `top_add`, `add_top`; project `height_eq_bot_iff`, `height_eq_top_mono`,
`NewtonPolygon.height_startingPoint`.
#### Sources
Definition D5 (decomposition); [Ked07, (1)] at fixed `i + j`.
#### Generality decision
`_ne_bot`/`_eq_top_mono` need both anchors; the rest are unconditional.

### [P02] Prove `subgradient_line_le_minkowskiHeight`
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Product.lean:111 | **Depends on**: P01, F02
- **Parallel**: yes | **Type**: lemma

#### Statement
```lean
theorem subgradient_line_le_minkowskiHeight (hxP : P.starting_point.1 = 0)
    (hxQ : Q.starting_point.1 = 0) (hbP : ∀ j, P.unitSlope j ≠ ⊥) (hbQ : ∀ j, Q.unitSlope j ≠ ⊥)
    {i₀ j₀ : ℕ} {σ : ℝ} (hP₁ : ∀ t, t < i₀ → P.unitSlope t ≤ (σ : WithBotTop ℝ))
    (hP₂ : ∀ t, i₀ ≤ t → (σ : WithBotTop ℝ) ≤ P.unitSlope t)
    (hQ₁ : ∀ t, t < j₀ → Q.unitSlope t ≤ (σ : WithBotTop ℝ))
    (hQ₂ : ∀ t, j₀ ≤ t → (σ : WithBotTop ℝ) ≤ Q.unitSlope t) {y : ℝ}
    (hy : P.height i₀ + Q.height j₀ = (y : WithBotTop ℝ)) (m : ℕ) :
    ((y + σ * ((m : ℝ) - (i₀ + j₀ : ℕ)) : ℝ) : WithBotTop ℝ) ≤ P.minkowskiHeight Q m := by
  sorry
```
#### Proof sketch
1. From `hy`, both heights are finite reals `yP`, `yQ` with `y = yP + yQ` (a sum in
   `WithBot (WithTop ℝ)` is a coercion only if both summands are: `WithBot.add_eq_coe`,
   `WithTop.add_eq_coe`).
2. `le_minkowskiHeight_iff.2`; for a split `(i, m − i)`: F02 for `P` at `i` and for `Q` at `m − i`,
   add (`add_le_add`, `WithBot.coe_add`), and the two line values sum to
   `y + σ (m − (i₀ + j₀))` — `push_cast; ring_nf`.
#### Mathlib lemmas needed
`WithBot.add_eq_coe`, `WithTop.add_eq_coe`, `WithBot.coe_add`, `add_le_add`, `Nat.cast_sub`.
#### Sources
[Ked07, §2] `v_r(PQ) = v_r(P) + v_r(Q)` as "supporting lines add"; decomposition P02.
#### Generality decision
No unboundedness needed — stated with anchors + no-`⊥` only.

### [P03] Prove `exists_subgradient`
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Product.lean:124 | **Depends on**: P01
- **Parallel**: yes | **Type**: lemma

#### Statement
```lean
theorem exists_subgradient (hxP : P.starting_point.1 = 0) (hxQ : Q.starting_point.1 = 0)
    (hbP : ∀ j, P.unitSlope j ≠ ⊥) (hbQ : ∀ j, Q.unitSlope j ≠ ⊥) {n i₀ : ℕ} (hi₀ : i₀ ≤ n)
    {y : ℝ} (hy : P.minkowskiHeight Q n = (y : WithBotTop ℝ))
    (heq : P.height i₀ + Q.height (n - i₀) = (y : WithBotTop ℝ)) :
    ∃ σ : ℝ, (∀ t, t < i₀ → P.unitSlope t ≤ (σ : WithBotTop ℝ)) ∧
      (∀ t, i₀ ≤ t → (σ : WithBotTop ℝ) ≤ P.unitSlope t) ∧
      (∀ t, t < n - i₀ → Q.unitSlope t ≤ (σ : WithBotTop ℝ)) ∧
      (∀ t, n - i₀ ≤ t → (σ : WithBotTop ℝ) ≤ Q.unitSlope t) := by
  sorry
```
#### Proof sketch
Write `j₀ := n − i₀`.  Both `P.height i₀`, `Q.height j₀` are finite (`heq`), so the unit slopes
`P.unitSlope (i₀ − 1)`, `Q.unitSlope (j₀ − 1)` (when the index exists) are real (`≠ ⊤` by
`unitSlope_ne_top_of_height_ne_top`, `≠ ⊥` by `hb`).
1. **Neighbour comparisons.**  If `j₀ ≥ 1`: `minkowskiHeight_le` at the split `(i₀ + 1, j₀ − 1)`
   with `hy`, `heq` gives `P.height i₀ + Q.height j₀ ≤ P.height (i₀+1) + Q.height (j₀−1)`; read the
   increments as unit slopes (`unitSlope_eq_of_height_eq`, `Support.lean:44`; if
   `P.height (i₀+1) = ⊤` then `P.unitSlope i₀ = ⊤` and the inequality below is trivial) to get
   `Q.unitSlope (j₀−1) ≤ P.unitSlope i₀`.  Symmetrically, if `i₀ ≥ 1`:
   `P.unitSlope (i₀−1) ≤ Q.unitSlope j₀`.
2. **Choice of `σ`.**  `σ := max (toReal (P.unitSlope (i₀−1))) (toReal (Q.unitSlope (j₀−1)))`
   when both `i₀, j₀ ≥ 1`; the single available one when exactly one is `≥ 1`;
   `σ := min (toReal (P.unitSlope 0)) (toReal (Q.unitSlope 0)) − 1` when `i₀ = j₀ = 0`.
3. **Verification** with `unitSlope_mono`: left bounds by monotonicity to the last index below;
   right bounds by step 1 and monotonicity (`le_max_left/right`, `max_le`); in the `⊤` cases
   `le_top`.  In the `i₀ = j₀ = 0` case the only obligations are `σ ≤ unitSlope 0` for both,
   true whether the slope is real (`min_le`, `sub_one_lt`) or `⊤`.
#### Mathlib lemmas needed
`le_max_left`, `le_max_right`, `max_le`, `min_le_left`, `min_le_right`, `sub_one_lt`,
`WithBotTop.coe_le_coe`, `le_top`; project `unitSlope_eq_of_height_eq`, `unitSlope_mono`,
`unitSlope_ne_top_of_height_ne_top`, `NewtonPolygon.toReal_coe`.
#### Sources
Expansion of [Ked07, Cor. 2 proof] (decomposition P03: the discrete optimality condition).
#### Generality decision
Anchors + no-`⊥` only; finiteness of the value `y` is necessary.

### [CLEANUP-5] Run /cleanup on PhD/NewtonPolygons/Product.lean (after P03)
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Product.lean | **Depends on**: P01, P02, P03
- **Parallel**: no | **Type**: cleanup

### [P04] Prove the face of the Minkowski sum (4 lemmas)
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Product.lean:141–166 | **Depends on**: CLEANUP-5, F07, P02
- **Parallel**: yes | **Type**: lemma (4)

#### Statement
```lean
theorem minkowskiHeight_faceLeft (hxP : P.starting_point.1 = 0) (hxQ : Q.starting_point.1 = 0)
    (hbP : ∀ j, P.unitSlope j ≠ ⊥) (hbQ : ∀ j, Q.unitSlope j ≠ ⊥) (hP : P.SlopesUnbounded)
    (hQ : Q.SlopesUnbounded) (σ : ℝ) :
    P.minkowskiHeight Q (P.faceLeft σ + Q.faceLeft σ) =
      P.height (P.faceLeft σ) + Q.height (Q.faceLeft σ) := by sorry
theorem height_faceLeft_add_lt (hxP : P.starting_point.1 = 0) (hxQ : Q.starting_point.1 = 0)
    (hbP : ∀ j, P.unitSlope j ≠ ⊥) (hbQ : ∀ j, Q.unitSlope j ≠ ⊥) (hP : P.SlopesUnbounded)
    (hQ : Q.SlopesUnbounded) {σ : ℝ} {i j : ℕ} (hij : i + j = P.faceLeft σ + Q.faceLeft σ)
    (hne : i ≠ P.faceLeft σ) :
    P.height (P.faceLeft σ) + Q.height (Q.faceLeft σ) < P.height i + Q.height j := by sorry
theorem minkowskiHeight_faceRight (hxP : P.starting_point.1 = 0) (hxQ : Q.starting_point.1 = 0)
    (hbP : ∀ j, P.unitSlope j ≠ ⊥) (hbQ : ∀ j, Q.unitSlope j ≠ ⊥) (hP : P.SlopesUnbounded)
    (hQ : Q.SlopesUnbounded) (σ : ℝ) :
    P.minkowskiHeight Q (P.faceRight σ + Q.faceRight σ) =
      P.height (P.faceRight σ) + Q.height (Q.faceRight σ) := by sorry
theorem height_faceRight_add_lt (hxP : P.starting_point.1 = 0) (hxQ : Q.starting_point.1 = 0)
    (hbP : ∀ j, P.unitSlope j ≠ ⊥) (hbQ : ∀ j, Q.unitSlope j ≠ ⊥) (hP : P.SlopesUnbounded)
    (hQ : Q.SlopesUnbounded) {σ : ℝ} {i j : ℕ} (hij : i + j = P.faceRight σ + Q.faceRight σ)
    (hne : i ≠ P.faceRight σ) :
    P.height (P.faceRight σ) + Q.height (Q.faceRight σ) < P.height i + Q.height j := by sorry
```
#### Proof sketch
1. Get the real face heights `yP`, `yQ` (F06 `exists_height_faceLeft_eq`).
2. `minkowskiHeight_faceLeft`: `le_antisymm (minkowskiHeight_le (by omega))` and P02 with
   `i₀ := faceLeft_P`, `j₀ := faceLeft_Q` (hypotheses from F05: `unitSlope_lt_of_lt_faceLeft |>.le`,
   `le_unitSlope_of_faceLeft_le hP`), at `m := faceLeft_P + faceLeft_Q` (the `σ` term vanishes).
3. `height_faceLeft_add_lt`: `rcases lt_or_gt_of_ne hne`.  If `i < faceLeft_P` then
   `j > faceLeft_Q`: `faceLeft_line_lt_height` for `P` at `i` (strict) and `faceLeft_line_le_height`
   for `Q` at `j`; add (`add_lt_add_of_lt_of_le`); the two line values sum to `yP + yQ` since
   `(i − faceLeft_P) + (j − faceLeft_Q) = 0`.  If `i > faceLeft_P` then `j < faceLeft_Q`: swap roles.
   Handle `⊤` heights (`lt_top` when the right side has a `⊤` summand; the left side is a coercion).
4. `faceRight` versions: identical with `faceRight_line_le_height`/`faceRight_line_lt_height`
   (strict on the *right* side: `i > faceRight_P` uses the strict `P` line, `i < faceRight_P` forces
   `j > faceRight_Q` and uses the strict `Q` line).
#### Mathlib lemmas needed
`lt_or_gt_of_ne`, `add_lt_add_of_lt_of_le`, `add_lt_add_of_le_of_lt`, `WithBot.coe_add`,
`WithBotTop.coe_lt_coe`, `lt_top_iff_ne_top`; F05, F06, F07, P02.
#### Sources
[Ked07, Prop. 1 proof] "the smallest values of `i` and `j` which minimize ... but not for any other";
decomposition P04.
#### Generality decision
All six hypotheses used (faces of both factors).

### [P05] Prove `minkowskiHeight_eq_of_mem_face`
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Product.lean:175 | **Depends on**: P04, F06, F05
- **Parallel**: yes | **Type**: lemma

#### Statement
```lean
theorem minkowskiHeight_eq_of_mem_face (hxP : P.starting_point.1 = 0)
    (hxQ : Q.starting_point.1 = 0) (hbP : ∀ j, P.unitSlope j ≠ ⊥) (hbQ : ∀ j, Q.unitSlope j ≠ ⊥)
    (hP : P.SlopesUnbounded) (hQ : Q.SlopesUnbounded) {σ y : ℝ}
    (hy : P.minkowskiHeight Q (P.faceLeft σ + Q.faceLeft σ) = (y : WithBotTop ℝ)) {m : ℕ}
    (h1 : P.faceLeft σ + Q.faceLeft σ ≤ m) (h2 : m ≤ P.faceRight σ + Q.faceRight σ) :
    P.minkowskiHeight Q m =
      ((y + σ * ((m : ℝ) - (P.faceLeft σ + Q.faceLeft σ : ℕ)) : ℝ) : WithBotTop ℝ) := by
  sorry
```
#### Proof sketch
1. `≥`: P02 at the left endpoints (as in P04 step 2), with `hy` rewritten by
   `minkowskiHeight_faceLeft` to identify `y = yP + yQ`.
2. `≤`: the split `i := faceLeft_P + min (m − (faceLeft_P + faceLeft_Q)) (faceRight_P − faceLeft_P)`,
   `j := m − i`; `omega` (with `faceLeft_le_faceRight` twice) shows `faceLeft_P ≤ i ≤ faceRight_P`
   and `faceLeft_Q ≤ j ≤ faceRight_Q`; `minkowskiHeight_le` and F06 `height_eq_of_mem_face` for both
   factors; `push_cast; ring_nf`.
#### Mathlib lemmas needed
`Nat.cast_sub`, `Nat.cast_min`, `le_antisymm`; F05 `faceLeft_le_faceRight`, F06, P01, P02, P04.
#### Sources
[Ked07, Cor. 2] "the segment of slope `r`" of the product; decomposition P05.
#### Generality decision
As P04.

### [P06] Prove the ultrametric sum lemmas and `pointHeight_eq_coe`
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Product.lean:195,201,222 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma (3)

#### Statement
```lean
theorem inf_negLogNorm_le_negLogNorm_sum [IsUltrametricDist K] {ι : Type*} (s : Finset ι)
    (l : ι → K) : (s.inf fun i => negLogNorm (l i)) ≤ negLogNorm (∑ i ∈ s, l i) := by sorry
theorem negLogNorm_sum_eq_of_forall_lt [IsUltrametricDist K] {ι : Type*} {s : Finset ι}
    {l : ι → K} {k : ι} (hk : k ∈ s) (h : ∀ j ∈ s, j ≠ k → negLogNorm (l k) < negLogNorm (l j)) :
    negLogNorm (∑ i ∈ s, l i) = negLogNorm (l k) := by sorry
theorem pointHeight_eq_coe (v : ℕ → WithTop ℝ) (k : ℕ) :
    pointHeight v k = ((v k : WithTop ℝ) : WithBotTop ℝ) := by sorry
```
#### Proof sketch
1. `inf_…`: `Finset.induction_on s`: empty gives `⊤ ≤ negLogNorm 0 = ⊤` (`negLogNorm_zero`);
   step: `Finset.inf_insert`, `Finset.sum_insert`, `le_negLogNorm_add`, `min_le_min`/`inf_le_inf`.
2. `…_eq_of_forall_lt`: `IsNonarchimedean.apply_sum_eq_of_lt` with `f := (‖·‖ : K → ℝ)`
   (`IsUltrametricDist.isNonarchimedean_norm`, `norm_neg`), `hmax` from `h` via
   `negLogNorm_lt_negLogNorm` (which reverses the order), then `congrArg negLogNorm`… — more
   precisely rewrite `negLogNorm` through `negLogNorm_of_norm_ne_zero`/`negLogNorm_eq_top_iff_norm`
   after establishing `‖∑ l i‖ = ‖l k‖`.
3. `pointHeight_eq_coe`: `cases hv : v k` and `simp [pointHeight, hv, Algebra.algebraMap_self_apply]`
   (the `⊤` case is `WithBot.coe_top`; the coercion `WithBot.some ∘ WithTop.some` is `WithBotTop.coe`
   by `rfl`).
#### Mathlib lemmas needed
`Finset.induction_on`, `Finset.inf_insert`, `Finset.sum_insert`, `inf_le_inf`,
`IsNonarchimedean.apply_sum_eq_of_lt` (`Mathlib/Algebra/Order/Ring/IsNonarchimedean.lean:227`),
`IsUltrametricDist.isNonarchimedean_norm`, `norm_neg`, `WithBot.coe_top`,
`Algebra.algebraMap_self_apply`; project `le_negLogNorm_add` (`NegLogNorm.lean:86`),
`negLogNorm_zero`, `negLogNorm_lt_negLogNorm` (`:82`), `negLogNorm_of_norm_ne_zero`,
`negLogNorm_eq_top_iff_norm`.
#### Sources
[Kob84, Lemma 6 proof] "the isosceles triangle principle"; [Ked07, (1)]; decomposition P06.
#### Generality decision
Stated for a `NontriviallyNormedField K` with `IsUltrametricDist`; the first two are candidates for
`NegLogNorm.lean` (over a `SeminormedAddGroup`), the third for `Spec.lean` — relocation at
CLEANUP-FINAL (user decision), add `-- TODO(newton-product): relocate` comments now.

### [CLEANUP-6] Run /cleanup on PhD/NewtonPolygons/Product.lean (after P06)
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Product.lean | **Depends on**: P04, P05, P06
- **Parallel**: no | **Type**: cleanup

### [P07] Prove `inf_coeffVal_add_le_coeffVal_mul`, `coeffVal_mul_eq_of_forall_lt`
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Product.lean:208,215 | **Depends on**: CLEANUP-6, P06
- **Parallel**: yes | **Type**: lemma (2)

#### Statement
```lean
theorem inf_coeffVal_add_le_coeffVal_mul [IsUltrametricDist K] (f g : PowerSeries K) (n : ℕ) :
    ((range (n + 1)).inf fun i => coeffVal f i + coeffVal g (n - i)) ≤ coeffVal (f * g) n := by
  sorry
theorem coeffVal_mul_eq_of_forall_lt [IsUltrametricDist K] (f g : PowerSeries K) {n i₀ : ℕ}
    (hi₀ : i₀ ≤ n)
    (h : ∀ i, i ≤ n → i ≠ i₀ → coeffVal f i₀ + coeffVal g (n - i₀) < coeffVal f i + coeffVal g (n - i)) :
    coeffVal (f * g) n = coeffVal f i₀ + coeffVal g (n - i₀) := by
  sorry
```
#### Proof sketch
1. `coeffVal_apply`, `PowerSeries.coeff_mul`: the coefficient is `∑ p ∈ antidiagonal n, a_{p.1} b_{p.2}`.
   Reindex to `range (n+1)` by `Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a_i b_j)`
   (or `Finset.Nat.antidiagonal_eq_map` + `Finset.sum_map`).
2. First lemma: P06 `inf_negLogNorm_le_negLogNorm_sum` on the `range` sum, then each term's
   `negLogNorm (a_i * b_{n-i}) = coeffVal f i + coeffVal g (n − i)` by `negLogNorm_mul`
   (`NormMulClass K` from the field); `Finset.inf_congr`.
3. Second lemma: P06 `negLogNorm_sum_eq_of_forall_lt` with `k := i₀ ∈ range (n+1)` and the
   strictness `h` transported through `negLogNorm_mul`; finish with `negLogNorm_mul` at `i₀`.
#### Mathlib lemmas needed
`PowerSeries.coeff_mul`, `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`, `Finset.mem_range`,
`Finset.inf_congr`; project `negLogNorm_mul` (`NegLogNorm.lean:132`), `coeffVal_apply`, P06.
#### Sources
[Ked07, Prop. 1 proof] (1) and the equality clause; decomposition P07.
#### Generality decision
`IsUltrametricDist K` necessary; no polygon hypotheses.

### [P08] Prove `coeff_zero_ne_zero`, `starting_point_fst_mul`, `minkowskiHeight_le_pointHeight_mul`
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Product.lean:231,237,245 | **Depends on**: P07, P01, F08
- **Parallel**: yes | **Type**: lemma (3)

#### Statement
```lean
theorem coeff_zero_ne_zero (hf : IsNewtonPolygonOf (coeffVal f) Pf) (hx : Pf.starting_point.1 = 0) :
    PowerSeries.coeff 0 f ≠ 0 := by sorry
theorem starting_point_fst_mul (hf : IsNewtonPolygonOf (coeffVal f) Pf)
    (hg : IsNewtonPolygonOf (coeffVal g) Pg) (hfg : IsNewtonPolygonOf (coeffVal (f * g)) Pfg)
    (hxf : Pf.starting_point.1 = 0) (hxg : Pg.starting_point.1 = 0) :
    Pfg.starting_point.1 = 0 := by sorry
theorem minkowskiHeight_le_pointHeight_mul [IsUltrametricDist K]
    (hf : IsNewtonPolygonOf (coeffVal f) Pf) (hg : IsNewtonPolygonOf (coeffVal g) Pg) (n : ℕ) :
    Pf.minkowskiHeight Pg n ≤ pointHeight (coeffVal (f * g)) n := by sorry
```
#### Proof sketch
1. `coeff_zero_ne_zero`: `hf.start_mem` with `hx` gives `coeffVal f 0 = (y₀ : WithTop ℝ) ≠ ⊤`;
   `coeffVal_eq_top_iff`.
2. `starting_point_fst_mul`: F08 `starting_point_fst_eq_zero hfg` with
   `coeffVal_eq_top_iff.not.2 (mul_ne_zero …)` after `PowerSeries.coeff_zero_eq_constantCoeff`/
   `map_mul` (`coeff 0 (f * g) = coeff 0 f * coeff 0 g`: `PowerSeries.coeff_zero_mul_X`-free route:
   `PowerSeries.coeff_mul` at `0` + `Finset.Nat.antidiagonal_zero`).
3. `minkowskiHeight_le_pointHeight_mul`: `pointHeight_eq_coe`; P07's inequality coerced to
   `WithBotTop ℝ` (`WithBot.coe_le_coe`, `WithBot.coe_inf`/`Finset.inf` commutes with the
   monotone injective `WithBot.some` — prove via `le_minkowskiHeight_iff` and `Finset.inf_le_iff`
   instead of commuting the `inf`); each split: `hf.height_le i`, `hg.height_le (n − i)` with
   `pointHeight_eq_coe`, `add_le_add`.
#### Mathlib lemmas needed
`mul_ne_zero`, `PowerSeries.coeff_mul`, `Finset.Nat.antidiagonal_zero`, `WithBot.coe_le_coe`,
`WithBot.coe_add`, `Finset.inf_le_iff`; project `coeffVal_eq_top_iff`, `height_le`, F08, P01, P06, P07.
#### Sources
[Kob84, Lemma 6 proof] "so does `(i, ord_p b_{i+1})`" lie on/above the polygon; decomposition P08.
#### Generality decision
`minkowskiHeight_le_pointHeight_mul` needs only the two specs.

### [P09] Prove `minkowskiHeight_le_height_mul` (the polygon of `fg` lies above the sum)
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Product.lean:255 | **Depends on**: P01, P02, P03, P08, F10
- **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem minkowskiHeight_le_height_mul [IsUltrametricDist K]
    (hf : IsNewtonPolygonOf (coeffVal f) Pf) (hg : IsNewtonPolygonOf (coeffVal g) Pg)
    (hfg : IsNewtonPolygonOf (coeffVal (f * g)) Pfg) (hxf : Pf.starting_point.1 = 0)
    (hxg : Pg.starting_point.1 = 0) (hbf : ∀ j, Pf.unitSlope j ≠ ⊥) (hbg : ∀ j, Pg.unitSlope j ≠ ⊥)
    (n : ℕ) : Pf.minkowskiHeight Pg n ≤ Pfg.height n := by
  sorry
```
#### Proof sketch
1. `hxfg := hfg.starting_point_fst_mul hf hg hxf hxg` (P08).
2. `by_cases htop : Pf.minkowskiHeight Pg n = ⊤`.
   - `⊤` case: `n ≠ 0` (`minkowskiHeight_zero` is finite: both anchors' heights are reals).  For
     `k ≥ n`, `minkowskiHeight_eq_top_mono` gives `M k = ⊤`, so by P08
     `pointHeight (coeffVal (f*g)) k = ⊤`, i.e. `coeffVal (f * g) k = ⊤` (`pointHeight_eq_top_iff`).
     F10 `hfg.height_eq_top_of_forall_eq_top hxfg (by omega)` gives `Pfg.height n = ⊤`; `le_top`.
   - Finite case: `M n = y`; `exists_minkowskiHeight_eq` gives the split `i₀`; P03 gives `σ`;
     P02 gives, for every `m`, `y + σ (m − n) ≤ M m ≤ pointHeight (coeffVal (f*g)) m` (P08).
     `hfg.line_le_height hxfg (a := y − σ n) (b := σ)` at `k := n` (rewrite `a + b n = y` by `ring`).
#### Mathlib lemmas needed
`le_top`, `WithBot.coe_ne_top`, `ne_of_gt`; project `line_le_height`, `pointHeight_eq_top_iff`,
P01, P02, P03, P08, F10.
#### Sources
[Ked07, Prop. 1] "This immediately yields `v_r(PQ) ≥ v_r(P) + v_r(Q)`"; decomposition P09.
#### Generality decision
Unboundedness not needed (stated with the weaker hypotheses on purpose).

### [CLEANUP-7] Run /cleanup on PhD/NewtonPolygons/Product.lean (after P09)
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Product.lean | **Depends on**: P07, P08, P09
- **Parallel**: no | **Type**: cleanup

### [P10] Prove `pointHeight_mul_faceLeft`, `pointHeight_mul_faceRight` (exact points)
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Product.lean:270,279 | **Depends on**: CLEANUP-7, P04, P07, F12
- **Parallel**: yes | **Type**: theorem (2)

#### Statement
```lean
theorem pointHeight_mul_faceLeft [IsUltrametricDist K]
    (hf : IsEntireNewtonPolygonOf (coeffVal f) Pf) (hg : IsEntireNewtonPolygonOf (coeffVal g) Pg)
    (σ : ℝ) :
    pointHeight (coeffVal (f * g)) (Pf.faceLeft σ + Pg.faceLeft σ) =
      Pf.height (Pf.faceLeft σ) + Pg.height (Pg.faceLeft σ) := by sorry
theorem pointHeight_mul_faceRight [IsUltrametricDist K]
    (hf : IsEntireNewtonPolygonOf (coeffVal f) Pf) (hg : IsEntireNewtonPolygonOf (coeffVal g) Pg)
    (σ : ℝ) :
    pointHeight (coeffVal (f * g)) (Pf.faceRight σ + Pg.faceRight σ) =
      Pf.height (Pf.faceRight σ) + Pg.height (Pg.faceRight σ) := by sorry
```
#### Proof sketch
1. `pointHeight_eq_coe`; apply P07 `coeffVal_mul_eq_of_forall_lt` with `i₀ := Pf.faceLeft σ`
   (`hi₀` by `omega`).
2. Strictness for `i ≠ i₀`, `i ≤ m₁`: chain `coeffVal f i + coeffVal g (m₁ − i) ≥ Pf.height i +
   Pg.height (m₁ − i)` (`height_le` twice, via `pointHeight_eq_coe` and `WithBot.coe_le_coe`)
   `> Pf.height i₀ + Pg.height j₀` (P04 `height_faceLeft_add_lt`) `= coeffVal f i₀ + coeffVal g j₀`
   (F12 `height_faceLeft_eq_pointHeight` for both factors, with the bundles' fields).
3. Rewrite the conclusion with F12 again.  `faceRight`: identical with the `faceRight` lemmas.
#### Mathlib lemmas needed
`WithBot.coe_lt_coe`, `WithBot.coe_le_coe`, `WithBot.coe_add`, `lt_of_le_of_lt`; F12, P04, P06, P07.
#### Sources
[Ked07, Prop. 1 proof] equality clause; decomposition P10.
#### Generality decision
Both `IsEntire` bundles used in full.

### [P11] Prove `height_mul_le_minkowskiHeight` (the polygon of `fg` lies below the sum)
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Product.lean:290 | **Depends on**: P03, P05, P10, F05
- **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem height_mul_le_minkowskiHeight [IsUltrametricDist K]
    (hf : IsEntireNewtonPolygonOf (coeffVal f) Pf) (hg : IsEntireNewtonPolygonOf (coeffVal g) Pg)
    (hfg : IsNewtonPolygonOf (coeffVal (f * g)) Pfg) (n : ℕ) :
    Pfg.height n ≤ Pf.minkowskiHeight Pg n := by
  sorry
```
#### Proof sketch
1. `by_cases htop : M n = ⊤` — `le_top`.  Otherwise `M n = y`, split `i₀` (P01), `σ` (P03),
   `j₀ := n − i₀`.
2. Bracket: `m₁ := Pf.faceLeft σ + Pg.faceLeft σ ≤ n ≤ m₂ := Pf.faceRight σ + Pg.faceRight σ` from
   F05 `faceLeft_le_of_le_unitSlope` (`σ ≤ Pf.unitSlope i₀` from P03's second clause at `t := i₀`)
   and `le_faceRight_of_forall_le hP` (P03's first clause), for both factors; `omega`.
3. Reals: `a := M m₁`, `c := M m₂` are reals (P04 + F06); `hfg.height_le` at `m₁`, `m₂` with P10
   gives `Pfg.height m₁ ≤ a`, `Pfg.height m₂ ≤ c` (`pointHeight_eq_coe` bookkeeping).
4. `Pfg.height_le_chord (x := m₁) (y := n) (z := m₂)` with `hxs` from
   `hfg.starting_point_fst_mul …` (P08, through the bundles' `toIsNewtonPolygonOf`) and
   `hxy`, `hyz` from step 2.
5. Evaluate the chord: P05 at `m₂` gives `c = a + σ (m₂ − m₁)` and at `n` gives `M n = a + σ (n − m₁)`;
   if `m₁ < m₂`, `(c − a)/(m₂ − m₁) = σ` (`field_simp`); if `m₁ = m₂` then `n = m₁` and the chord
   value is `a` (division by `0` is `0`; `simp`).  `le_of_eq`/`le_trans` to finish.
#### Mathlib lemmas needed
`div_self`, `field_simp`, `Nat.cast_sub`, `le_top`; project `height_le_chord` (`Height.lean:740`),
`height_le`, F05, F06, P01, P03, P04, P05, P08, P10.
#### Sources
[Ked07, Cor. 2 proof] (the face of the sum, its endpoints are touching points); decomposition P11.
#### Generality decision
Both bundles needed.

### [CLEANUP-ALL-1] Run /cleanup-all on the board so far (before the theorem)
- **Status**: done   (finished 2026-09-09) | **File**: (board files) | **Depends on**: P09, P11, CLEANUP-4, CLEANUP-7
- **Parallel**: no | **Type**: cleanup
- Pre-milestone project-wide cleanup on the two board files only (do not touch other files).

### [P12] Prove `height_mul` — **MILESTONE: the Newton polygon of a product**
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Product.lean:299 | **Depends on**: CLEANUP-ALL-1, P09, P11
- **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem height_mul [IsUltrametricDist K] (hf : IsEntireNewtonPolygonOf (coeffVal f) Pf)
    (hg : IsEntireNewtonPolygonOf (coeffVal g) Pg)
    (hfg : IsNewtonPolygonOf (coeffVal (f * g)) Pfg) (n : ℕ) :
    Pfg.height n = Pf.minkowskiHeight Pg n := by
  sorry
```
#### Proof sketch
`le_antisymm (hf.height_mul_le_minkowskiHeight hg hfg n)
  (hf.toIsNewtonPolygonOf.minkowskiHeight_le_height_mul hg.toIsNewtonPolygonOf hfg
    hf.starting_point_fst hg.starting_point_fst hf.unitSlope_ne_bot hg.unitSlope_ne_bot n)`.
Then `#print axioms IsEntireNewtonPolygonOf.height_mul` must show only
`[propext, Classical.choice, Quot.sound]`.
#### Mathlib lemmas needed
`le_antisymm`.
#### Sources
[Ked07, §2] "the slope multiset of `PQ` is the union of the slope multisets of `P` and `Q`",
Cor. 2; [Kob84, Lemma 6]; decomposition R1.
#### Generality decision
See plan.md §Generality: anchors at `0`, no `⊥`, unbounded slopes on both factors (each necessary).

### [CLEANUP-8] Run /cleanup on PhD/NewtonPolygons/Product.lean (after P12)
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Product.lean | **Depends on**: P10, P11, P12
- **Parallel**: no | **Type**: cleanup

### [P13] Prove the initial-segment corollaries `height_mul_of_forall_le`, `unitSlope_mul_of_forall_le`
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Product.lean:310,319 | **Depends on**: CLEANUP-8, P12, F01
- **Parallel**: yes | **Type**: theorem (2)

#### Statement
```lean
theorem height_mul_of_forall_le [IsUltrametricDist K]
    (hf : IsEntireNewtonPolygonOf (coeffVal f) Pf) (hg : IsEntireNewtonPolygonOf (coeffVal g) Pg)
    (hfg : IsNewtonPolygonOf (coeffVal (f * g)) Pfg) {n : ℕ}
    (hle : ∀ i, i < n → ∀ j, Pg.unitSlope i ≤ Pf.unitSlope j) :
    Pfg.height n = Pf.height 0 + Pg.height n := by sorry
theorem unitSlope_mul_of_forall_le [IsUltrametricDist K]
    (hf : IsEntireNewtonPolygonOf (coeffVal f) Pf) (hg : IsEntireNewtonPolygonOf (coeffVal g) Pg)
    (hfg : IsNewtonPolygonOf (coeffVal (f * g)) Pfg) (hbfg : ∀ j, Pfg.unitSlope j ≠ ⊥) {n : ℕ}
    (hle : ∀ i, i < n → ∀ j, Pg.unitSlope i ≤ Pf.unitSlope j) {j : ℕ}
    (hj : j < n) : Pfg.unitSlope j = Pg.unitSlope j := by sorry
```
#### Proof sketch
1. Height form: `rw [hf.height_mul hg hfg]`; `le_antisymm (minkowskiHeight_le (Nat.zero_le n))`
   (split `0`, `n − 0 = n`) and `le_minkowskiHeight_iff.2`: for a split `(i, n − i)` with `i ≥ 1`:
   - if `Pg.height n = ⊤`: some `Pg.unitSlope t = ⊤` with `t < n` (`unitSlope_eq_top_of_height_eq_top`),
     so `hle t` makes every `Pf.unitSlope j = ⊤`, hence `Pf.height i = ⊤` for `i ≥ 1`
     (`unitSlope_eq_top_of_height_eq_top`'s converse: `height (0 + i) = ⊤` since the walk hits a
     `⊤` slope — use `height_eq_heightFun`'s contrapositive or `Height.lean`'s `rightHeight` guard
     via `unitSlope_ne_top_of_height_ne_top`); both sides `⊤`.
   - else all heights finite: F01 gives `Pf.height i − Pf.height 0 = ∑_{t<i} toReal (Pf.unitSlope t)`
     and `Pg.height n − Pg.height (n−i) = ∑_{t ∈ Ico (n−i) n} toReal (Pg.unitSlope t)`; reindex the
     second by `t ↦ (n − i) + t` (`Finset.sum_Ico_eq_sum_range`) and compare termwise
     (`Finset.sum_le_sum`, `hle ((n−i)+t) (by omega) t` read through `toReal` — both sides real by
     `hb` and finiteness); `linarith`.
2. Slope form: apply the height form at `j` and `j + 1` (`hle` restricts), get
   `Pfg.height j = c + Pg.height j`, `Pfg.height (j+1) = c + Pg.height (j+1)` with `c := Pf.height 0`
   real (anchor).  If `Pg.height (j+1)` is real: `unitSlope_eq_of_height_eq` for `Pfg` (needs
   `hbfg`, anchor via P08) and for `Pg` (`hg.unitSlope_ne_bot`), both `= (height (j+1) − height j)`;
   `c` cancels.  If `Pg.height (j+1) = ⊤`: then `Pfg.height (j+1) = ⊤`, and
   `unitSlope_eq_top_of_height_eq_top` at `x := j + 1` gives `unitSlope j = ⊤` on both sides.
#### Mathlib lemmas needed
`Finset.sum_le_sum`, `Finset.sum_Ico_eq_sum_range`, `Nat.sub_add_cancel`, `WithBot.add_eq_coe`;
project P01, P12, F01, `unitSlope_eq_of_height_eq`, `unitSlope_eq_top_of_height_eq_top`,
`height_eq_heightFun`, P08 `starting_point_fst_mul`.
#### Sources
[LWX, p. 25] `lwx.txt:1815–1818` (the first `n_{k+1}` slopes); decomposition P13 (including the
dropped `hn`).
#### Generality decision
No finiteness hypothesis on `Pg.height n` (dropped at planning: the `⊤` case holds).

### [P14] Prove `slopesUnbounded_mul`, `mul`, `faceRight_mul`, `faceLeft_mul` (multiplicities add)
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Product.lean:328–351 | **Depends on**: P12, P04, P05, F05, F07
- **Parallel**: yes | **Type**: theorem (4)

#### Statement
```lean
theorem slopesUnbounded_mul [IsUltrametricDist K]
    (hf : IsEntireNewtonPolygonOf (coeffVal f) Pf) (hg : IsEntireNewtonPolygonOf (coeffVal g) Pg)
    (hfg : IsNewtonPolygonOf (coeffVal (f * g)) Pfg) : Pfg.SlopesUnbounded := by sorry
theorem mul [IsUltrametricDist K] (hf : IsEntireNewtonPolygonOf (coeffVal f) Pf)
    (hg : IsEntireNewtonPolygonOf (coeffVal g) Pg)
    (hfg : IsNewtonPolygonOf (coeffVal (f * g)) Pfg) (hbfg : ∀ j, Pfg.unitSlope j ≠ ⊥) :
    IsEntireNewtonPolygonOf (coeffVal (f * g)) Pfg := by sorry
theorem faceRight_mul [IsUltrametricDist K] (hf : IsEntireNewtonPolygonOf (coeffVal f) Pf)
    (hg : IsEntireNewtonPolygonOf (coeffVal g) Pg)
    (hfg : IsNewtonPolygonOf (coeffVal (f * g)) Pfg) (hbfg : ∀ j, Pfg.unitSlope j ≠ ⊥) (σ : ℝ) :
    Pfg.faceRight σ = Pf.faceRight σ + Pg.faceRight σ := by sorry
theorem faceLeft_mul [IsUltrametricDist K] (hf : IsEntireNewtonPolygonOf (coeffVal f) Pf)
    (hg : IsEntireNewtonPolygonOf (coeffVal g) Pg)
    (hfg : IsNewtonPolygonOf (coeffVal (f * g)) Pfg) (hbfg : ∀ j, Pfg.unitSlope j ≠ ⊥) (σ : ℝ) :
    Pfg.faceLeft σ = Pf.faceLeft σ + Pg.faceLeft σ := by sorry
```
#### Proof sketch
Throughout `H := Pfg.height = M` (P12), `m₁ := faceLeft_f + faceLeft_g`, `m₂ := faceRight_f + faceRight_g`.
1. **Strict growth after `m₂`** (private lemma `minkowskiHeight_succ_faceRight_gt`):
   `M (m₂ + 1) > M m₂ + σ`: `exists_minkowskiHeight_eq (m₂+1)` gives a split `(i, j)`; `i > faceRight_f`
   or `j > faceRight_g` (`omega`); F07 `faceRight_line_lt_height` on that factor (strict) and
   `faceRight_line_le_height` on the other; add; the line values sum to `M m₂ + σ` (P04
   `minkowskiHeight_faceRight`).  (If a height is `⊤`, `M (m₂+1) = ⊤` and the claim is `lt_top`.)
2. **Slack before `m₁`** (private `minkowskiHeight_pred_faceLeft_gt`): if `m₁ ≥ 1`,
   `M (m₁ − 1) > M m₁ − σ` by the same argument with `faceLeft_line_lt_height`.
3. `slopesUnbounded_mul`: given `σ`, take `j := m₂`; from step 1 and
   `unitSlope_eq_of_height_eq`/`unitSlope_eq_top_of_height_eq_top` (anchor from P08), `Pfg.unitSlope m₂ > σ`
   — if `H (m₂+1) = ⊤` the slope is `⊤`; else it is the real increment `> σ`.  (No `hbfg` needed:
   in the finite case `unitSlope_eq_of_height_eq` needs `≠ ⊥`, so instead compare through
   `heightFun_succ` and `toReal`; if the slope were `⊥` its `toReal` is `0`, but the increment is
   `> σ`… — simplest: derive `≠ ⊥` from `slopes_zero_eq_bot_of_unitSlope_eq_bot` (`Height.lean:609`):
   a `⊥` unit slope forces `support = 1`, `slopes 0 = ⊥`, whence every height at `k ≥ 1` is the
   anchor value, contradicting `M 1 > M 0 + σ'` for large `σ'`… — this is the one delicate point;
   if it resists, add `hbfg` to `slopesUnbounded_mul` (sanctioned weakening in reverse: record it).
4. `mul`: `⟨hfg, hfg.starting_point_fst_mul …, hbfg, slopesUnbounded_mul …⟩`.
5. `faceRight_mul`: `le_antisymm (faceLeft_le_of_le_unitSlope … )`-style: `Pfg.faceRight σ ≤ m₂` by
   `Nat.sInf_le` with `σ < Pfg.unitSlope m₂` (step 3); `m₂ ≤ Pfg.faceRight σ` by
   `le_faceRight_of_forall_le (slopesUnbounded_mul …)`: for `t < m₂`, `Pfg.unitSlope t ≤ σ` — for
   `m₁ ≤ t < m₂` the increment is exactly `σ` (P05 at `t`, `t + 1`); for `t < m₁` use monotonicity
   from `t := m₁ − 1` (if `m₁ ≥ 1`), whose increment is `≤ σ` by P02 at the left endpoints
   (`M (m₁ − 1) ≥ M m₁ − σ`).  Read increments as unit slopes with `unitSlope_eq_of_height_eq` (`hbfg`).
6. `faceLeft_mul`: `Pfg.faceLeft σ ≤ m₁` since `σ ≤ Pfg.unitSlope m₁` (increment `≥ σ` by P02 at
   `m₁ + 1`, or `⊤`); `m₁ ≤ Pfg.faceLeft σ` since `Pfg.unitSlope (m₁ − 1) < σ` (step 2) and
   `unitSlope_lt_of_lt_faceLeft`'s converse (`Nat.notMem_of_lt_sInf` direction: an index with slope
   `< σ` is not in the set, and all smaller indices have smaller slopes — `le_faceRight_of_forall_le`'s
   analogue for `faceLeft`; prove inline with `Nat.sInf_mem` + `unitSlope_mono`).
#### Mathlib lemmas needed
`Nat.sInf_le`, `Nat.sInf_mem`, `lt_top_iff_ne_top`, `Nat.sub_add_cancel`; project P01, P02, P04, P05,
P08, P12, F05, F07, `unitSlope_eq_of_height_eq`, `unitSlope_eq_top_of_height_eq_top`, `unitSlope_mono`,
`slopes_zero_eq_bot_of_unitSlope_eq_bot`.
#### Sources
[Ked07, Cor. 2]; [Gou20, Problem 343] (pure × pure = pure); decomposition P14.
#### Generality decision
`hbfg` on the three slope-reading statements; `slopesUnbounded_mul` attempts without it (see step 3).

### [P15] Prove the constructed-polygon hypotheses (3 lemmas)
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Product.lean:366,373,380 | **Depends on**: F08, F11
- **Parallel**: yes | **Type**: theorem (3)

#### Statement
```lean
theorem slopesUnbounded_newtonPolygon₀OfPowerSeries {f : PowerSeries K}
    (hf : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f) (hf0 : PowerSeries.coeff 0 f ≠ 0) :
    (newtonPolygon₀OfPowerSeries negLogNorm f).SlopesUnbounded := by sorry
theorem isEntireNewtonPolygonOf_coeffVal {f : PowerSeries K}
    (hf : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f) (hf0 : PowerSeries.coeff 0 f ≠ 0) :
    IsEntireNewtonPolygonOf (coeffVal f) (newtonPolygon₀OfPowerSeries negLogNorm f) := by sorry
theorem isNewtonPolygonOf_coeffVal_mul [IsUltrametricDist K] {f g : PowerSeries K}
    (hf : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f)
    (hg : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c g) (hf0 : PowerSeries.coeff 0 f ≠ 0)
    (hg0 : PowerSeries.coeff 0 g ≠ 0) :
    IsNewtonPolygonOf (coeffVal (f * g)) (newtonPolygon₀OfPowerSeries negLogNorm (f * g)) := by sorry
```
#### Proof sketch
1. Spec: `hspec := isNewtonPolygonOf_coeffVal_of_isRestricted one_pos (hf 1 one_pos) hne`
   (`CoeffVal.lean:147`; `hne : f ≠ 0` from `hf0`).  Anchor: F08 `starting_point_fst_eq_zero` with
   `coeffVal_eq_top_iff.not.2 hf0`.  No `⊥`: `newtonPolygon₀OfSeq_unitSlope_ne_bot` (`Support.lean:90`)
   with `exists_coeffVal_ne_top`, `isAdmissible_coeffVal_of_isRestricted`.
2. `slopesUnbounded_…`: F11 with the affine floor of slope `σ`: `c := Real.exp σ`,
   `hterm := PowerSeries.le_gaussNorm norm c f (hf c (Real.exp_pos σ)).hasGaussNorm k`, and
   the log computation of `CoeffVal.lean:116–135` verbatim (`b := −Real.log (gaussNorm norm c f)`,
   `Real.log_mul`, `Real.log_pow`, `Real.log_exp`); at `coeff k f = 0` the point is `⊤` (`le_top`).
3. `isEntireNewtonPolygonOf_coeffVal`: `⟨hspec, anchor, no-⊥, slopesUnbounded_…⟩`.
4. `isNewtonPolygonOf_coeffVal_mul`: `isNewtonPolygonOf_coeffVal_of_isRestricted one_pos
   (PowerSeries.isRestricted.mul 1 (hf 1 one_pos) (hg 1 one_pos)) (mul_ne_zero hne hne')`.
#### Mathlib lemmas needed
`Real.exp_pos`, `Real.log_mul`, `Real.log_pow`, `Real.log_exp`, `Real.log_le_log`, `mul_ne_zero`;
project `isNewtonPolygonOf_coeffVal_of_isRestricted`, `isAdmissible_coeffVal_of_isRestricted`,
`exists_coeffVal_ne_top`, `newtonPolygon₀OfSeq_unitSlope_ne_bot`, `PowerSeries.le_gaussNorm`,
`PowerSeries.isRestricted.mul` (`Restricted/Basic.lean:76`), F08, F11.
#### Sources
[Kob84, Lemma 5] (entire ⟺ unbounded slopes); `CoeffVal.lean:114` (the Gauss bound as an affine
floor); decomposition P15.
#### Generality decision
`∀ c > 0, IsRestricted c f` is `PowerSeries.IsEntire f` unfolded (`TateFredholm/Entire.lean:107`),
kept unbundled to avoid importing `TateFredholm`.

### [CLEANUP-9] Run /cleanup on PhD/NewtonPolygons/Product.lean (after P15)
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Product.lean | **Depends on**: P13, P14, P15
- **Parallel**: no | **Type**: cleanup

### [P16] Prove the constructed-polygon corollaries (4 lemmas)
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Product.lean:388–422 | **Depends on**: CLEANUP-9, P12, P13, P14, P15
- **Parallel**: yes | **Type**: theorem (4)

#### Statement
```lean
theorem height_newtonPolygon₀OfPowerSeries_mul [IsUltrametricDist K] {f g : PowerSeries K}
    (hf : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f)
    (hg : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c g) (hf0 : PowerSeries.coeff 0 f ≠ 0)
    (hg0 : PowerSeries.coeff 0 g ≠ 0) (n : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm (f * g)).height n =
      (newtonPolygon₀OfPowerSeries negLogNorm f).minkowskiHeight
        (newtonPolygon₀OfPowerSeries negLogNorm g) n := by sorry
theorem height_newtonPolygon₀OfPowerSeries_mul_of_forall_le [IsUltrametricDist K]
    {f g : PowerSeries K} (hf : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f)
    (hg : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c g) (hf0 : PowerSeries.coeff 0 f = 1)
    (hg0 : PowerSeries.coeff 0 g = 1) {n : ℕ}
    (hle : ∀ i, i < n → ∀ j, (newtonPolygon₀OfPowerSeries negLogNorm g).unitSlope i ≤
      (newtonPolygon₀OfPowerSeries negLogNorm f).unitSlope j) :
    (newtonPolygon₀OfPowerSeries negLogNorm (f * g)).height n =
      (newtonPolygon₀OfPowerSeries negLogNorm g).height n := by sorry
theorem unitSlope_newtonPolygon₀OfPowerSeries_mul_of_forall_le [IsUltrametricDist K]
    {f g : PowerSeries K} (hf : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f)
    (hg : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c g) (hf0 : PowerSeries.coeff 0 f ≠ 0)
    (hg0 : PowerSeries.coeff 0 g ≠ 0) {n : ℕ}
    (hle : ∀ i, i < n → ∀ j, (newtonPolygon₀OfPowerSeries negLogNorm g).unitSlope i ≤
      (newtonPolygon₀OfPowerSeries negLogNorm f).unitSlope j) {j : ℕ} (hj : j < n) :
    (newtonPolygon₀OfPowerSeries negLogNorm (f * g)).unitSlope j =
      (newtonPolygon₀OfPowerSeries negLogNorm g).unitSlope j := by sorry
theorem faceRight_newtonPolygon₀OfPowerSeries_mul [IsUltrametricDist K] {f g : PowerSeries K}
    (hf : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f)
    (hg : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c g) (hf0 : PowerSeries.coeff 0 f ≠ 0)
    (hg0 : PowerSeries.coeff 0 g ≠ 0) (σ : ℝ) :
    (newtonPolygon₀OfPowerSeries negLogNorm (f * g)).faceRight σ =
      (newtonPolygon₀OfPowerSeries negLogNorm f).faceRight σ +
        (newtonPolygon₀OfPowerSeries negLogNorm g).faceRight σ := by sorry
```
#### Proof sketch
1. `hF := isEntireNewtonPolygonOf_coeffVal hf hf0`, `hG := …`, `hFG := isNewtonPolygonOf_coeffVal_mul …`
   (P15); `hbFG := newtonPolygon₀OfSeq_unitSlope_ne_bot _ ⟨0, …⟩ (isAdmissible_coeffVal_of_isRestricted one_pos (isRestricted.mul …))`.
2. First: `hF.height_mul hG hFG n`.  Third: `hF.unitSlope_mul_of_forall_le hG hFG hbFG hle hj`.
   Fourth: `hF.faceRight_mul hG hFG hbFG σ`.
3. Second: `hF.height_mul_of_forall_le hG hFG hle` with `hf0' : coeff 0 f ≠ 0` from `hf0`, then
   `(newtonPolygon₀OfPowerSeries negLogNorm f).height 0 = 0` by
   `newtonPolygon₀_starting_point_of_coeff_zero_eq_one hf0` (`CoeffVal.lean:155`) and
   `NewtonPolygon.height_startingPoint` (`startHeight` of `(0, 0)` is `0`); `zero_add`.
#### Mathlib lemmas needed
`one_ne_zero`, `zero_add`; project P12–P15, `newtonPolygon₀_starting_point_of_coeff_zero_eq_one`,
`NewtonPolygon.height_startingPoint`, `newtonPolygon₀OfSeq_unitSlope_ne_bot`.
#### Sources
As P12–P14.
#### Generality decision
The height form uses `= 1` (to cancel the anchor height), the others `≠ 0`.

### [P17] Prove `height_newtonPolygon₀OfPowerSeries_coe_natDegree_ne_top`
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Product.lean:432 | **Depends on**: none
- **Parallel**: yes | **Type**: lemma

#### Statement
```lean
theorem height_newtonPolygon₀OfPowerSeries_coe_natDegree_ne_top (G : Polynomial K)
    (hG : G ≠ 0) :
    (newtonPolygon₀OfPowerSeries negLogNorm (G : PowerSeries K)).height G.natDegree ≠ ⊤ := by
  sorry
```
#### Proof sketch
`(isNewtonPolygonOf_coeffVal_coe G hG).height_le G.natDegree` (`CoeffVal.lean:138`) and the point is
finite: `coeffVal_eq_top_iff`, `Polynomial.coeff_coe`, `Polynomial.leadingCoeff_ne_zero.2 hG`;
`ne_top_of_le_ne_top` + `pointHeight_eq_top_iff`.  (Or F08 `height_ne_top_of_ne_top` directly.)
#### Mathlib lemmas needed
`Polynomial.coeff_coe`, `Polynomial.leadingCoeff_ne_zero`, `ne_top_of_le_ne_top`.
#### Sources
[Kob84, p. 97]; decomposition P17.
#### Generality decision
Any nonzero polynomial (no constant-term hypothesis).

### [CLEANUP-ALL-2] Run /cleanup-all on the board (before the LWX-facing milestone)
- **Status**: done   (finished 2026-09-09) | **File**: (board files) | **Depends on**: P16, P17, CLEANUP-9
- **Parallel**: no | **Type**: cleanup

### [P18] Prove `height_newtonPolygon₀OfPowerSeries_mul_coe` — **MILESTONE: the finite factor supplies the initial segment**
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Product.lean:441 | **Depends on**: CLEANUP-ALL-2, P16
- **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem height_newtonPolygon₀OfPowerSeries_mul_coe [IsUltrametricDist K] {f : PowerSeries K}
    (hf : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f) (hf0 : PowerSeries.coeff 0 f = 1)
    (G : Polynomial K) (hG0 : G.coeff 0 = 1)
    (hle : ∀ i, i < G.natDegree → ∀ j,
      (newtonPolygon₀OfPowerSeries negLogNorm (G : PowerSeries K)).unitSlope i ≤
        (newtonPolygon₀OfPowerSeries negLogNorm f).unitSlope j) :
    (newtonPolygon₀OfPowerSeries negLogNorm (f * (G : PowerSeries K))).height G.natDegree =
      (newtonPolygon₀OfPowerSeries negLogNorm (G : PowerSeries K)).height G.natDegree := by
  sorry
```
#### Proof sketch
`height_newtonPolygon₀OfPowerSeries_mul_of_forall_le hf (fun c _ => Polynomial.isRestricted_toPowerSeries c G)
  hf0 (by rwa [Polynomial.coeff_coe]) hle` (P16), with `n := G.natDegree`.  Then
`#print axioms` on it and on `height_mul`.
#### Mathlib lemmas needed
`Polynomial.coeff_coe`; project `Polynomial.isRestricted_toPowerSeries` (`Restricted/Basic.lean:201`), P16.
#### Sources
[LWX, p. 25] (quoted in decomposition P13/P18); `lwx-theta` decomposition AG3/S3.
#### Generality decision
Polynomial factor on the right (`f * G`), matching `TateFredholm.charPowerSeries_eq_mul_polynomial`
(`FiniteFactor.lean:46`: `charPowerSeries u = charPowerSeries (u * (1 − pr)) * G`).

### [CLEANUP-10] Run /cleanup on PhD/NewtonPolygons/Product.lean (final per-file)
- **Status**: done   (finished 2026-09-09) | **File**: PhD/NewtonPolygons/Product.lean | **Depends on**: P16, P17, P18
- **Parallel**: no | **Type**: cleanup
- Whole-file `/cleanup`, `lake exe runLinter PhD.NewtonPolygons.Product`, `#print axioms` on every
  declaration.

### [CLEANUP-FINAL] Run /cleanup-all on the whole board
- **Status**: done   (finished 2026-09-09) | **File**: (board files) | **Depends on**: every other ticket
- **Parallel**: no | **Type**: cleanup
- `lake build PhD.NewtonPolygons.Product` clean, zero sorries, standard axioms everywhere,
  `runLinter` zero on both files.  Then **ask the user** about relocating the marked helpers
  (`heightFun_sub_eq_sum` → `Height.lean`; `inf_negLogNorm_le_negLogNorm_sum`,
  `negLogNorm_sum_eq_of_forall_lt` → `NegLogNorm.lean`; `pointHeight_eq_coe` → `Spec.lean`) — do
  not move them without approval (rebuild fallout on the `LWX` tree).  Update
  `PhD/NewtonPolygons` docs / `blueprint/src/chapter/NewtonPolygons.tex` (a "Products" section:
  `height_mul`, `faceRight_mul`, `height_newtonPolygon₀OfPowerSeries_mul_coe`) and tell the
  `lwx-theta` board that T-AG3 is discharged here.  Then `/pre-submit`.

## Cleanup-cadence verification

| File | Proof tickets | Cadence cleanups | Final | Total |
|---|---|---|---|---|
| Face.lean | 12 (F01–F12) | CLEANUP-1 (after F03), CLEANUP-2 (after F06), CLEANUP-3 (after F09) | CLEANUP-4 (after F12) | 4 |
| Product.lean | 18 (P01–P18) | CLEANUP-5 (P03), CLEANUP-6 (P06), CLEANUP-7 (P09), CLEANUP-8 (P12), CLEANUP-9 (P15) | CLEANUP-10 (P18) | 6 |

`⌈30/3⌉ = 10` cadence cleanups required and present (the two finals double as the last cadence
slot on each file); CLEANUP-ALL-1 before milestone P12, CLEANUP-ALL-2 before milestone P18,
CLEANUP-FINAL last.  13 cleanup tickets in total.

---

## Session log — 2026-09-09 beastmode

**Face.lean COMPLETE and sorry-free** (F01–F12 + CLEANUP-1..4). `lake build PhD.NewtonPolygons.Face`
clean (1874 jobs); `#print axioms` on all 17 public results shows exactly
`[propext, Classical.choice, Quot.sound]`; `lake exe runLinter PhD.NewtonPolygons.Face` reports
zero findings on this file (its 11 findings are all in the read-only
`ForMathlib/NumberTheory/NewtonPolygon/{Basic,Construction}.lean`).

Four sanctioned hypothesis weakenings (recorded in `renames.jsonl`):
- `line_lt_height_of_unitSlope_lt` lost `h₂`, `line_lt_height_of_lt_unitSlope` lost `h₁` (each
  strict form only reads the slopes on its own side of `i₀`);
- `faceLeft_line_lt_height` lost `hP` (`unitSlope_lt_of_lt_faceLeft` is unconditional);
- `height_eq_top_of_forall_eq_top` lost `0 < n` (at `n = 0` the spec is unsatisfiable).

Two new private helpers not in the plan, both consumed repeatedly:
- `height_natCast_eq_heightFun` / `unitSlope_ne_top_of_height_natCast` — the `hx`-normalised forms
  of `Height.lean`'s dictionary at natural indices;
- `le_heightFun_sub` / `heightFun_sub_le` / `lt_heightFun_sub` / `heightFun_sub_lt` — the four
  per-step sum bounds that F02/F03 share.

One new **public** helper beyond the plan, needed by F09 and reusable by Product.lean:
- `NewtonPolygon₀.line_add_margin_le_height` — the supporting line with a margin `δ`, clearing
  the polygon by `δ` at every index other than `i₀`. This is the quantitative form the
  vertex characterisation needs (a raised line must beat the strict inequality by a fixed amount).
- `pointHeight_ne_bot` — point heights are never `⊥`.

---

## Session log — 2026-09-09 beastmode, part 2: **BOARD COMPLETE**

**Product.lean COMPLETE and sorry-free** (P01–P18 + CLEANUP-5..10, CLEANUP-ALL-1/2,
CLEANUP-FINAL). `lake build PhD.NewtonPolygons.Product` clean (2084 jobs); `#print axioms` on all
15 headline results shows exactly `[propext, Classical.choice, Quot.sound]`;
`lake exe runLinter PhD.NewtonPolygons.Product` reports **zero findings in either board file**
(its remaining findings are in the read-only `ForMathlib` NewtonPolygon and NegLogNorm files).
No line over 100 characters in either file.

### Milestones

- **P12 `IsEntireNewtonPolygonOf.height_mul`** — the Newton polygon of a product is the Minkowski
  sum of the polygons of the factors.
- **P18 `height_newtonPolygon₀OfPowerSeries_mul_coe`** — the LWX-facing form: for `f` restricted at
  every radius and a polynomial `G`, both with constant coefficient `1`, if every slope of `G` is
  at most every slope of `f` then the polygon of `f · G` agrees with that of `G` at `deg G`.
  This is what `lwx-theta`'s T-AG3 was a placeholder for.

### Declarations beyond the plan (all consumed, none speculative)

In `Face.lean`: `NewtonPolygon.coe_toReal_eq_self`, `NewtonPolygon.toReal_le_toReal` (the
`toReal` order dictionary), `NewtonPolygon₀.line_add_margin_le_height` (the supporting line with a
margin — what the vertex characterisation needs), `height_ne_bot_of_nonneg`,
`height_natCast_ne_bot`, `height_natCast_zero_ne_top`, `height_natCast_eq_heightFun`,
`unitSlope_ne_top_of_height_natCast`, `height_natCast_ne_top_of_unitSlope`,
`exists_height_natCast_eq`, `pointHeight_ne_bot`, plus four private per-step sum bounds.

In `Product.lean`: `add_eq_bot_iff`, `add_eq_top_iff`, `exists_coe_of_ne`, `coe_add_coe`,
`coe_add_coe'`, `coe_add_lt_add_left`, `coe_add_lt_add_right` (junk-value arithmetic in
`WithBotTop ℝ`), `exists_coe_of_add_eq_coe`, `lt_minkowskiHeight_faceRight_succ` and its mirror
`lt_minkowskiHeight_faceLeft_pred` (strict growth just outside a face — what the multiplicity
count rests on), `lt_unitSlope_mul_faceRight`, `height_zero_newtonPolygon₀OfPowerSeries`.

### Sanctioned hypothesis weakenings (all in `renames.jsonl`)

`line_lt_height_of_unitSlope_lt` lost `h₂`; `line_lt_height_of_lt_unitSlope` lost `h₁`;
`faceLeft_line_lt_height` lost `hP`; `height_eq_top_of_forall_eq_top` lost `0 < n`.
No statement was strengthened, and no B2 was needed — every planned statement proved as written.

Notable: `slopesUnbounded_mul` was proved **without** adding the `hbfg` hypothesis the plan
pre-authorised. The degenerate `⊥`-slope representation is refuted from within: a `⊥` unit slope
forces `support = 1`, so with no `⊤` slope every unit slope is `⊥` and the polygon is constant,
contradicting strict growth past the face of slope `1`.

### Design detail worth keeping

`minkowskiHeight P Q n = (range (n+1)).inf fun i => P.height i + Q.height (n - i)` elaborates
`n - i` as **integer** subtraction (both indices are cast into `ℤ` for `height`). That is the
honest reading on `range (n+1)`, where `i ≤ n`, but it means the height helpers had to be stated
for nonneg integers (`height_ne_bot_of_nonneg`) rather than only for natural casts, and every
split-index step carries a `Nat.cast_sub` rewrite.

### Follow-ups left for the user (not actioned)

1. **Relocation of four helpers**, deliberately proved locally because their natural homes are
   read-only for this board (every `PhD/LWX/*` file rebuilds on a change there, and a concurrent
   `lwx-theta` beastmode run was live): `heightFun_sub_eq_sum` → `Height.lean`;
   `inf_negLogNorm_le_negLogNorm_sum`, `negLogNorm_sum_eq_of_forall_lt` → `NegLogNorm.lean`;
   `pointHeight_eq_coe`, `pointHeight_ne_bot` → `Spec.lean`.
2. **`lwx-theta`'s T-AG3 should be pointed at this board.** Not edited from here: that board's
   sentinel `.mathlib-quality/lwx-theta/beastmode_active` was live throughout this session, and
   this board never writes to another board's files.
3. `blueprint/src/chapter/NewtonPolygons.tex` gained a "The polygon of a product" section
   (definitions `SlopesUnbounded`/faces/Minkowski height, the theorem with its proof sketch, and
   the two corollaries). The `\lean{}` references are live declarations; a blueprint rebuild will
   confirm the dep-graph edges.
