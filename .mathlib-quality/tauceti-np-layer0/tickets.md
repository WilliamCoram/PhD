# Ticket Board — Newton polygons, Layer 0

Board: `.mathlib-quality/tauceti-np-layer0/`. Plan: `plan.md`. Decomposition (source quotes, attack
logs, leaf IDs `Lx.y`): `decomposition.md`. Skeleton: `PhD/TauCeti/Code/NewtonPolygons/*.lean`, every
declaration `:= by sorry`. Build gate: `lake build PhD.TauCeti.Code.NewtonPolygons.Examples`.

Conventions binding every ticket (see `plan.md` "Generality and design decisions"): the polygon is
`h : ℕ → WithTop ℝ`; `⊤` is the only junk value; convexity is `IsConvexSeq` (order-connected
finiteness set + `MonotoneOn` unit slopes); `newtonPolygon v` is the supremum of the convex
minorants; faces assume anchor `0`; everything in namespace `NewtonPolygon`; never `import
PhD.Main.*` — `PhD/Main/NewtonPolygons/` is consulted read-only for proof ideas, cited as [SRC].

Worker protocol: `/beastmode` inline as the main agent (user preference); after each ticket run
`lake build <module>` and `#print axioms` on each declaration (only `propext`, `Classical.choice`,
`Quot.sound`); mark `done` only with zero `sorry` in the ticket's declarations.

## Summary
- Total: 59 tickets — 40 proof/definition (T040 was added during execution), 16 per-file cleanups,
  2 pre-milestone `/cleanup-all` (before T026 and before T031), 1 final `/cleanup-all`
- Open: 0 | In Progress: 0 | Done: 59 — **LAYER 0 COMPLETE** (2026-09-12/13: every ticket proved,
  sorry-free, lint-clean, standard axioms, 261/261 declarations documented, gated in CI)
- Coverage: every declaration in `PhD/TauCeti/Code/NewtonPolygons/` (196) is named in a ticket
  except `mem_finiteSet` (`Iff.rfl`, already proved); `IsNewtonPolygonOf.unique` is proved in the
  skeleton and carried by T010's milestone for the record.
- Parallel capacity: 3 (G6 `Construction` from T027 on and G8 `Int` from T036 on are independent
  of G3–G5/G4–G5 respectively; otherwise the chain is linear and one worker at a time is the
  honest estimate)
- Milestones: T010 (existence of the polygon, generic), T026 (§0.6, slope multisets add), T031 (the
  vertex walk is the polygon)
- Revision 2 (2026-09-12): §0.1–§0.2 generic over a discrete linear order `ι`; the specification
  has three fields; `IsVertical` names the vertical case; `Int.lean` reduces `ℤ` to `ℕ`. T001–T012
  rewritten, T035 (invariances) and T036 (`Int.lean`) added.
- Revision 3 (2026-09-12): the terminal ray named — `EndsInRay` (T037 Slope, T038 Face, T039
  Construction, CLEANUP-16).

## Dependency order (ticket groups)

```text
G1 ConvexSeq : T001 → T002 → T003 → CLEANUP-1 → T004 → T005 → T006 → CLEANUP-2 → T007 → CLEANUP-3
G2 Basic     : T008 → T009 → T010 → CLEANUP-4 → T011 → T012 → T035 → CLEANUP-5 (after CLEANUP-3)
G8 Int       : T036 → CLEANUP-15                                                 (after CLEANUP-5; parallel)
G3 Slope     : T013 → T014 → T015 → CLEANUP-6 → T016 → T017 → T037 → CLEANUP-7 (after CLEANUP-5)
G4 Face      : T018 → T019 → T020 → CLEANUP-8 → T021 → T022 → T038 → CLEANUP-9 (after CLEANUP-7)
G5 Minkowski : T023 → T024 → T025 → CLEANUP-10 → CLEANUP-ALL-1 → T026 → CLEANUP-11 (after CLEANUP-9)
G6 Construct.: T027 → T028 → T029 → CLEANUP-12 → T030 → CLEANUP-ALL-2 → T031 → T032 → CLEANUP-16 → T039 → CLEANUP-13 (after CLEANUP-7)
G7 Examples  : T033 → T034 → CLEANUP-14                                          (after CLEANUP-11, CLEANUP-13)
CLEANUP-FINAL (after everything, including CLEANUP-15)
```

---

## Tickets

### [T001] `unitSlope` and `finiteSet` API (generic `ι`)
- **Status**: done · **File**: `ConvexSeq.lean` · **Depends on**: none · **Parallel**: no · **Type**: lemmas
- **Leaves**: L1.1–L1.3, L1.4′, L1.22, and `unitSlope_nat`. Index type: `[LinearOrder ι] [SuccOrder ι]`, with
  `[IsSuccArchimedean ι] [LocallyFiniteOrder ι] [NoMaxOrder ι]` for the `Sums` section.

#### Statement
```lean
theorem unitSlope_eq_top_iff {j : ι} : unitSlope h j = ⊤ ↔ h j = ⊤ ∨ h (succ j) = ⊤
theorem unitSlope_of_ne_top {j : ι} (hj : h j ≠ ⊤) (hj1 : h (succ j) ≠ ⊤) :
    unitSlope h j = (((h (succ j)).untop₀ - (h j).untop₀ : ℝ) : WithTop ℝ)
theorem add_unitSlope {j : ι} (hj : h j ≠ ⊤) : h j + unitSlope h j = h (succ j)
theorem IsConvexSeq.eq_of_unitSlope_eq (hh : IsConvexSeq h) (hg : IsConvexSeq g) {i₀ : ι}
    (h₀ : h i₀ ≠ ⊤) (hg₀ : h i₀ = g i₀) (hs : ∀ j, unitSlope h j = unitSlope g j) : h = g
theorem eq_add_nsmul_of_forall_unitSlope_eq {a k : ι} {σ : ℝ} (ha : h a ≠ ⊤) (hak : a ≤ k)
    (hσ : ∀ j, a ≤ j → j < k → unitSlope h j = σ) : h k = h a + (Finset.Ico a k).card • (σ : WithTop ℝ)
theorem eq_add_sum_unitSlope {a k : ι} (hak : a ≤ k) (hfin : ∀ j, a ≤ j → j ≤ k → h j ≠ ⊤) :
    h k = h a + ((∑ j ∈ Finset.Ico a k, (unitSlope h j).untop₀ : ℝ) : WithTop ℝ)
theorem unitSlope_nat (h : ℕ → WithTop ℝ) (j : ℕ) :
    unitSlope h j = if h j = ⊤ ∨ h (j + 1) = ⊤ then ⊤ else (((h (j + 1)).untop₀ - (h j).untop₀ : ℝ) : WithTop ℝ)
```
#### Proof sketch
1. `unitSlope_eq_top_iff`, `unitSlope_of_ne_top`: `unfold unitSlope; split_ifs`; `WithTop.coe_ne_top`;
   `not_or`. `unitSlope_nat`: `simp [unitSlope, Order.succ_eq_add_one]`.
2. `add_unitSlope`: `by_cases h (succ j) = ⊤` — then both sides `⊤` (`add_top`); else rewrite with
   `unitSlope_of_ne_top`, `WithTop.coe_untop₀_of_ne_top` twice, `← WithTop.coe_add`, `sub_add_cancel`.
3. `eq_add_sum_unitSlope`: `Succ.rec` from `a` (hypothesis `a ≤ k`); step `n → succ n`:
   `Finset.Ico a (succ n) = insert n (Finset.Ico a n)` (from `Finset.Ico_union_Ico_eq_Ico` with
   `Finset.Ico n (succ n) = {n}` — `Order.Ico_succ_right`/`Finset.Ico_self`-style lemmas under
   `NoMaxOrder`, to be loogled; fallback: `Finset.Ico_insert_right`-type reasoning on
   `Ico n (succ n)` being a singleton since `n < succ n` (`Order.lt_succ`) and nothing lies strictly
   between (`Order.lt_succ_iff`)); `Finset.sum_insert`; `add_unitSlope` with finiteness from `hfin`.
4. `eq_add_nsmul_of_forall_unitSlope_eq`: same `Succ.rec`; `Finset.card` of the extended interval is
   `+1` (`Finset.card_insert_of_notMem`); `succ_nsmul`.
5. `eq_of_unitSlope_eq`: `funext j`; `rcases le_total i₀ j`. Right (`i₀ ≤ j`): `Succ.rec` from `i₀`
   with `add_unitSlope` while finite, and `unitSlope_eq_top_iff` to transfer `⊤` from `h` to `g`
   (the slopes agree). Left (`j ≤ i₀`): if both `h j`, `g j` finite, `eq_add_sum_unitSlope` from `j`
   to `i₀` for both (intermediate values finite by order-connectedness), equal sums ⇒ equal values;
   if `h j = ⊤`, `g j ≠ ⊤`: then `unitSlope h j = ⊤` while `unitSlope g j` is finite (`g (succ j)` is
   finite as `succ j ∈ [j, i₀]` or `j = i₀` — excluded), contradicting `hs j`.
#### Mathlib lemmas needed
`WithTop.coe_ne_top`, `add_top`, `WithTop.coe_untop₀_of_ne_top`, `WithTop.coe_add`, `WithTop.coe_nsmul`,
`Succ.rec`, `Order.lt_succ`, `Order.lt_succ_iff`, `Order.succ_le_of_lt`, `Finset.Ico_union_Ico_eq_Ico`,
`Finset.sum_insert`, `Finset.card_insert_of_notMem`, `succ_nsmul`, `Order.succ_eq_add_one`.
#### Sources
[RM] §0.1.1; decomposition L1.1–L1.3, L1.4′, L1.22, revision 2 ("generic restatements").
#### Generality decision
Generic `ι`; `eq_of_unitSlope_eq` carries convexity of both sequences (necessary — decomposition L1.4′).
#### Progress
- 2026-09-12: DONE. All seven declarations proved on the first build (`unitSlope_eq_top_iff`,
  `unitSlope_of_ne_top`, `add_unitSlope`, `eq_add_nsmul_of_forall_unitSlope_eq`,
  `eq_add_sum_unitSlope`, `IsConvexSeq.eq_of_unitSlope_eq`, `unitSlope_nat`).
- Skeleton edits: (i) `IsConvexSeq.eq_of_unitSlope_eq` moved after `eq_add_sum_unitSlope` (its left-hand
  case telescopes, so it must follow it in the file); (ii) `IsConvexSeq.eq_top_of_le` (T002 leaf L1.5,
  two lines from `ordConnected.out`) proved here because the right-hand case of `eq_of_unitSlope_eq`
  needs it; (iii) the hypothesis `ha : h a ≠ ⊤` dropped from `eq_add_nsmul_of_forall_unitSlope_eq` —
  unused (the linter flagged it): a finite unit slope already forces `h a ≠ ⊤`. Strictly stronger
  statement; the ticket statement above is updated.
- Mathlib lemmas actually used: `Order.Succ.rec` (via `induction hak using Succ.rec`),
  `Finset.Ico_succ_right_eq_Icc`, `Finset.Icc_eq_cons_Ico`, `Finset.sum_cons`, `Finset.card_cons`,
  `succ_nsmul`, `WithTop.ne_top_iff_exists`, `WithTop.untop₀_coe`, `WithTop.coe_untop₀_of_ne_top`,
  `WithTop.coe_add`, `WithTop.coe_inj`, `WithTop.add_right_cancel`, `Order.succ_eq_add_one`.

### [T040] The converse of the increment identity (sub-ticket of T004)
- **Status**: done · **File**: `ConvexSeq.lean` · **Depends on**: T001 · **Parent**: T004 · **Type**: lemma
#### Statement
```lean
theorem unitSlope_eq_of_succ_eq_add {j : ι} {c : ℝ} (hj : h j ≠ ⊤)
    (hc : h (succ j) = h j + (c : WithTop ℝ)) : unitSlope h j = (c : WithTop ℝ)
```
#### Proof sketch
`obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 hj`; `h (succ j) = ↑(x + c) ≠ ⊤`, so
`unitSlope_of_ne_top` applies; `WithTop.untop₀_coe` twice and `WithTop.coe_inj` leave `x + c - x = c`,
closed by `ring`.
#### Mathlib lemmas needed
`WithTop.ne_top_iff_exists`, `WithTop.coe_add`, `WithTop.untop₀_coe`, `WithTop.coe_inj`, `WithTop.coe_ne_top`.
#### Sources
Spawned while working T004 (2026-09-12): four of its proofs (`extend_affine`, `isConvexSeq_affine`,
`isConvexSeq_affineFrom`, `add_affine`) identify a unit slope from a one-step increment, which is
`add_unitSlope` read backwards. [RM] §0.1.1.
#### Generality decision
Generic `ι`, in the `Defs` section next to `add_unitSlope`; `c : ℝ` (a `⊤` increment is
`unitSlope_eq_top_iff`).
#### Progress
- 2026-09-12: DONE. `unitSlope_eq_of_succ_eq_add`, 6 lines, used by all four affine constructions of
  T004 and by the `not_isConvexSeq_inf` example.

### [T002] Convexity: `⊤` propagation, the midpoint form, the constant `⊤`
- **Status**: done · **File**: `ConvexSeq.lean` · **Depends on**: T001 · **Type**: lemmas · **Leaves**: L1.5–L1.7, L1.13
#### Statement
```lean
theorem IsConvexSeq.eq_top_of_le (hh : IsConvexSeq h) {a i j : ι} (ha : h a ≠ ⊤) (hai : a ≤ i)
    (hi : h i = ⊤) (hij : i ≤ j) : h j = ⊤
theorem IsConvexSeq.midpoint (hh : IsConvexSeq h) (k : ι) : h (succ k) + h (succ k) ≤ h k + h (succ (succ k))
theorem isConvexSeq_top : IsConvexSeq fun _ : ι ↦ (⊤ : WithTop ℝ)
theorem isConvexSeq_iff_midpoint (hord : (finiteSet h).OrdConnected) :
    IsConvexSeq h ↔ ∀ k, h (succ k) + h (succ k) ≤ h k + h (succ (succ k))
```
#### Proof sketch
1. `eq_top_of_le`: `by_contra hj; exact hi (hh.ordConnected.out ha hj ⟨hai, hij⟩)`.
2. `midpoint`: if `h k = ⊤` or `h (succ (succ k)) = ⊤`, `le_top` after `top_add`/`add_top`; else
   `h (succ k) ≠ ⊤` by `ordConnected.out` (`le_succ`, `le_succ` composed); `hh.monotoneOn` at
   `k ≤ succ k`; unfold with `unitSlope_of_ne_top`, `WithTop.coe_le_coe`, `WithTop.coe_add`, `linarith`.
3. `isConvexSeq_top`: `finiteSet = ∅` (`Set.ordConnected_empty`), `MonotoneOn` on `∅`.
4. `isConvexSeq_iff_midpoint`: `→` item 2. `←`: `MonotoneOn`: for `i ≤ j` in `finiteSet h`, `Succ.rec`
   from `i`: consecutive unit slopes compare by the midpoint inequality at each index where the three
   values are finite (order-connected), and the last finite index has `unitSlope = ⊤ ≥ _` (`le_top`).
#### Mathlib lemmas needed
`Set.OrdConnected.out`, `Set.ordConnected_empty`, `Order.le_succ`, `top_add`, `add_top`, `le_top`,
`WithTop.coe_le_coe`, `WithTop.coe_add`, `Succ.rec`.
#### Sources
[RM] §0.1.1; decomposition L1.5–L1.7, L1.13.
#### Generality decision
Generic `ι`; `isConvexSeq_iff_midpoint` lives in the `Sums` section (it walks along successors).
#### Progress
- 2026-09-12: DONE. `eq_top_of_le` (during T001), `IsConvexSeq.midpoint`, `isConvexSeq_top`,
  `isConvexSeq_iff_midpoint`. The `←` direction of the midpoint form goes through a one-step lemma
  (`step`, local) and then `Succ.rec` from `i` to `j` with order-connectedness supplying finiteness at
  each intermediate index — as sketched.
- `isConvexSeq_iff_midpoint` carries `omit [LocallyFiniteOrder ι] [NoMaxOrder ι] in`: it needs only
  `IsSuccArchimedean` from the `Sums` section (the linter flagged the two unused instances). `omit`
  must precede the docstring, not sit between docstring and `theorem`.

### [T003] The chord inequality and increment extensions
- **Status**: done · **File**: `ConvexSeq.lean` · **Depends on**: T002 · **Type**: lemmas · **Leaves**: L1.8–L1.10
#### Statement
```lean
theorem IsConvexSeq.le_chord (hh : IsConvexSeq h) {a b c : ι} (hab : a ≤ b) (hbc : b ≤ c) :
    (Finset.Ico a c).card • h b ≤ (Finset.Ico b c).card • h a + (Finset.Ico a b).card • h c
theorem IsConvexSeq.add_nsmul_unitSlope_le (hh : IsConvexSeq h) {i k : ι} (hi : h i ≠ ⊤) (hik : i ≤ k) :
    h i + (Finset.Ico i k).card • unitSlope h i ≤ h k
theorem IsConvexSeq.le_add_nsmul_unitSlope (hh : IsConvexSeq h) {i k : ι} (hi1 : h (succ i) ≠ ⊤) (hki : k ≤ i) :
    h (succ i) ≤ h k + (Finset.Ico k (succ i)).card • unitSlope h i
```
#### Proof sketch
1. `add_nsmul_unitSlope_le`: if `h k = ⊤`, `le_top`; else all values on `[i, k]` finite
   (`eq_top_of_le` contrapositive), `eq_add_sum_unitSlope` (T001), each `s_j ≥ s_i` by `monotoneOn`,
   `Finset.sum_le_sum`, `Finset.sum_const`, `WithTop.coe_nsmul`.
2. `le_add_nsmul_unitSlope`: if `h k = ⊤` the right side is `⊤`; else telescope from `k` to `succ i`
   and bound each `s_j ≤ s_i`.
3. `le_chord`: trivial cases `a = b` or `b = c` (`Finset.Ico_self`, `zero_nsmul`, `Nat.card`
   bookkeeping); if `h a = ⊤` or `h c = ⊤`, the right side is `⊤` (positive card, `WithTop.nsmul_top`
   or `top_add`); else all finite: with `S₁ = ∑_{Ico a b} s`, `S₂ = ∑_{Ico b c} s` and `n₁ = card
   (Ico a b)`, `n₂ = card (Ico b c)`, `card (Ico a c) = n₁ + n₂` (`Finset.Ico_union_Ico_eq_Ico`,
   `Finset.card_union_of_disjoint`), monotonicity gives `n₂ S₁ ≤ n₁ n₂ s_b ≤ n₁ S₂` (two
   `Finset.sum_le_sum` against the pivot `s_b`; `nlinarith`), then `linarith` with `h b = h a + S₁`,
   `h c = h a + S₁ + S₂`.
#### Mathlib lemmas needed
`Finset.sum_le_sum`, `Finset.sum_const`, `Finset.Ico_union_Ico_eq_Ico`, `Finset.card_union_of_disjoint`,
`Finset.Ico_disjoint_Ico_consecutive`, `WithTop.coe_nsmul`, `zero_nsmul`, `WithTop.coe_le_coe`, `le_top`.
#### Sources
[RM] §0.1.2; [SRC] `Height.heightFun_chord`, `Height.le_heightFun`; decomposition L1.8–L1.10.
#### Generality decision
Generic `ι`, step counts as `Finset.Ico` cardinalities (`c - a` on `ℕ`, `(c - a).toNat` on `ℤ`).
#### Progress
- 2026-09-12: DONE. `IsConvexSeq.le_chord`, `add_nsmul_unitSlope_le`, `le_add_nsmul_unitSlope`.
- `le_chord`: degenerate cases `a = b`, `b = c` by `simp`; `h a = ⊤` / `h c = ⊤` by a local
  `htop : 0 < m → m • (⊤ : WithTop ℝ) = ⊤` (`succ_nsmul`, `add_top`); the finite case telescopes both
  halves (`eq_add_sum_unitSlope`), bounds each slope against the pivot `unitSlope h b`
  (`WithTop.untop₀_le_untop₀` + `monotoneOn`), compares sums with `Finset.sum_le_sum` +
  `Finset.sum_const`, and closes with `nlinarith` on `n₂ S₁ ≤ n₁ S₂` after `hcard`
  (`Finset.Ico_union_Ico_eq_Ico`, `Finset.card_union_of_disjoint`,
  `Finset.Ico_disjoint_Ico_consecutive`).
- `le_add_nsmul_unitSlope` needed `add_le_add le_rfl _`, not `add_le_add_left _ _` (the latter adds on
  the right in this ordered-monoid API).

### [CLEANUP-1] Run /cleanup on `ConvexSeq.lean` (first pass)
- **Status**: done · **Depends on**: T003 · **Type**: cleanup — cadence rule (3 proof tickets on the file).
#### Progress
- 2026-09-12: done as part of the single inline cleanup pass on `ConvexSeq.lean` (see CLEANUP-3).

### [T004] Convex constructions: steepening, `sup`; on `ℕ` affine, `affineFrom`, `add_affine`, the `inf` counterexample
- **Status**: done · **File**: `ConvexSeq.lean` · **Depends on**: CLEANUP-1 · **Type**: def + lemmas · **Leaves**: L1.12, L1.14, L1.15, L1.17, L1.23, L1.24
#### Statement
```lean
theorem IsConvexSeq.extend_affine (hh : IsConvexSeq h) {n : ι} (hn : h n ≠ ⊤) {M : ℝ}
    (hM : ∀ j, j < n → h j ≠ ⊤ → unitSlope h j ≤ M) :
    IsConvexSeq fun k ↦ if k ≤ n then h k else h n + (Finset.Ico n k).card • (M : WithTop ℝ)
theorem IsConvexSeq.sup (hh : IsConvexSeq h) (hg : IsConvexSeq g) : IsConvexSeq (h ⊔ g)
theorem isConvexSeq_affine (y σ : ℝ) : IsConvexSeq fun k : ℕ ↦ ((y + σ * k : ℝ) : WithTop ℝ)
noncomputable def affineFrom (i₀ : ℕ) (y s : ℝ) : ℕ → WithTop ℝ :=
  fun k ↦ if k < i₀ then ⊤ else ((y + s * ((k : ℝ) - i₀) : ℝ) : WithTop ℝ)
theorem isConvexSeq_affineFrom (i₀ : ℕ) (y s : ℝ) : IsConvexSeq (affineFrom i₀ y s)
theorem IsConvexSeq.add_affine (hh : IsConvexSeq h) (y σ : ℝ) : IsConvexSeq fun k ↦ h k + ((y + σ * k : ℝ) : WithTop ℝ)
theorem not_isConvexSeq_inf :
    ¬ IsConvexSeq ((fun k : ℕ ↦ ((k : ℝ) : WithTop ℝ)) ⊓ fun k : ℕ ↦ ((2 - k : ℝ) : WithTop ℝ))
```
#### Proof sketch
1. `extend_affine`: finiteness set `= finiteSet h ∩ Iic n ∪ Ioi n` — order-connected because
   `finiteSet h ∩ Iic n` is an interval ending at `n` (`hn`) and `Ioi n` continues it; unit slopes:
   those of `h` below `n`, `M` from `n` on (`Finset.Ico n (succ k)` grows by one per step), monotone
   by `hM` across `n` and constant after.
2. `sup`: `finiteSet (h ⊔ g) = finiteSet h ∩ finiteSet g` (`sup_eq_top_iff`), `Set.OrdConnected.inter`;
   midpoint via `isConvexSeq_iff_midpoint` and `sup_le`/`le_sup_left`/`le_sup_right`.
3. `ℕ` items: `unitSlope_nat`; affine: constant slope `σ` (`ring_nf`), `finiteSet = univ`
   (`Set.ordConnected_univ`); `affineFrom`: finiteness set `Set.Ici i₀` (`Set.ordConnected_Ici`),
   constant slope `s`; `add_affine`: slopes shift by `σ`; `not_isConvexSeq_inf`: `hh.monotoneOn` at
   `0 ≤ 1` gives `1 ≤ -1` after `unitSlope_nat`, `norm_num`.
#### Mathlib lemmas needed
`Set.OrdConnected.inter`, `Set.ordConnected_univ`, `Set.ordConnected_Ici`, `sup_eq_top_iff`, `sup_le`,
`le_sup_left`, `le_sup_right`, `WithTop.coe_nsmul`, `Order.succ_eq_add_one`.
#### Sources
[RM] §0.1.3, §0.1.5, §0.2.5; [Mathlib] `ConvexOn.sup`; decomposition L1.12–L1.15, L1.17, L1.23, L1.24.
#### Generality decision
`extend_affine` and `sup` generic; the coordinate-dependent constructions on `ℕ` (their `ℤ` twins, where
needed, are in `Int.lean`).
#### Progress
- 2026-09-12: DONE. `extend_affine`, `sup`, `isConvexSeq_affine`, `affineFrom`,
  `isConvexSeq_affineFrom`, `add_affine`, `not_isConvexSeq_inf`.
- Spawned T040 (`unitSlope_eq_of_succ_eq_add`) first; every affine construction then reads
  "one step adds the slope".
- Traps met: (i) `simp` with the default set pushes `↑(a + b)`/`↑(n • a)`/`↑(a * b)` apart
  (`WithTop.coe_add` etc. are `norm_cast` simp lemmas), which turns a finiteness goal into WithTop
  arithmetic — use `WithTop.coe_ne_top`, `WithTop.add_eq_top` and `iff_of_true/false` explicitly
  instead of `simp [finiteSet]`; (ii) `rcases eq_or_lt_of_le hj with rfl | _` substitutes the *later*
  variable away, so the `rfl` branch must be written in terms of `n`, not `j`; (iii) there is no
  `sup_eq_top_iff` for `WithTop ℝ` — the two-case `le_total` argument with `top_le_iff` is the way;
  (iv) `add_le_add_left h _` adds on the right in this API — use `add_le_add le_rfl h`.
- `extend_affine` and `sup` carry `omit` for the instances they do not use.

### [T005] The supremum of convex sequences is convex
- **Status**: done · **File**: `ConvexSeq.lean` · **Depends on**: T004 · **Type**: theorem · **Leaf**: L1.16
#### Statement
```lean
theorem IsConvexSeq.iSup {κ : Type*} [Nonempty κ] {f : κ → ι → WithTop ℝ}
    (hf : ∀ i, IsConvexSeq (f i)) : IsConvexSeq fun k ↦ ⨆ i, f i k
```
#### Proof sketch
As decomposition L1.16, with `succ k` in place of `k + 1`: order-connectedness of the finiteness set of
`S k := ⨆ i, f i k` from each factor's midpoint inequality and `ciSup_le` after halving in `ℝ`; the
midpoint inequality for `S` from `le_ciSup (OrderTop.bddAbove _)` twice and `ciSup_le`.
#### Mathlib lemmas needed
`le_ciSup`, `OrderTop.bddAbove`, `ciSup_le`, `WithTop.coe_le_coe`, `WithTop.coe_add`, `WithTop.coe_untop₀_of_ne_top`,
`add_halves`, `WithTop.add_eq_top`.
#### Sources
[RM] §0.1.3; Rockafellar Thm 5.5 (from memory; Mathlib analogue `ConvexOn.sup`); decomposition L1.16.
#### Generality decision
Generic `ι`, arbitrary nonempty family; no boundedness hypothesis.
#### Progress
- 2026-09-12: DONE. `IsConvexSeq.iSup`, no boundedness hypothesis.
- Order-connectedness of the finiteness set of the supremum: the chord inequality (T003) bounds
  `card (Ico a c) • f i b` uniformly by `card (Ico b c) • ⨆ f a + card (Ico a b) • ⨆ f c`, and
  `ciSup_le` then bounds the supremum at `b`. The midpoint inequality: each factor gives
  `2 u_i ≤ A + C`, so `⨆ ≤ (A + C)/2` by `ciSup_le`, and doubling gives the claim.
- `le_ciSup (OrderTop.bddAbove _) i` does not elaborate with a placeholder: write
  `le_ciSup (f := fun j ↦ f j k) (OrderTop.bddAbove (Set.range fun j ↦ f j k)) i`.

### [T006] The bridge to `ConvexOn` (on `ℕ`)
- **Status**: done · **File**: `ConvexSeq.lean` · **Depends on**: T005 · **Type**: lemmas · **Leaves**: L1.18, L1.19
#### Statement
```lean
theorem IsConvexSeq.exists_convexOn (hh : IsConvexSeq h) (hfin : ∀ k, h k ≠ ⊤) :
    ∃ H : ℝ → ℝ, ConvexOn ℝ (Set.Ici (0 : ℝ)) H ∧ ∀ k : ℕ, H k = (h k).untop₀
theorem isConvexSeq_of_convexOn {H : ℝ → ℝ} (hH : ConvexOn ℝ (Set.Ici (0 : ℝ)) H) :
    IsConvexSeq fun k : ℕ ↦ ((H k : ℝ) : WithTop ℝ)
```
#### Proof sketch
Unchanged from the first board: `ConvexOn.slope_mono_adjacent` at `j, j+1, j+2` for the converse;
for the forward direction `H x := ⨆ j, (untop₀ (h j) + untop₀ (unitSlope h j) * (x - j))`, bounded
above on `Ici 0` by the chord bounds (T003 at `ι = ℕ`), `ConvexOn` of a supremum (**loogle
`convexOn_iSup`; fallback from the definition**), `H k = h k` by T003.
#### Mathlib lemmas needed
`ConvexOn.slope_mono_adjacent`, `monotone_nat_of_le_succ`, `ciSup_le`, `le_ciSup`; to check: `convexOn_iSup`.
#### Sources
[RM] §0.1.4; [Mathlib] `Analysis/Convex/Slope.lean`; decomposition L1.18–L1.19.
#### Generality decision
`ℕ` only, as the roadmap states it.
#### Progress
- 2026-09-12: DONE. `IsConvexSeq.exists_convexOn`, `isConvexSeq_of_convexOn`.
- `exists_convexOn` takes `H x = ⨆ j, (h j).untop₀ + (unitSlope h j).untop₀ * (x - j)` — the
  supremum of the supporting lines. Three ingredients: the lines lie below the points
  (`hline`, by telescoping and `Finset.sum_le_sum` against the pivot slope, in both directions);
  boundedness on `Ici 0` (an affine function on `[0, m]` is below `max` of its endpoint values, with
  `m` from `exists_nat_ge` — no `Nat.ceil` needed, so no extra import); convexity straight from the
  definition, since each member of the family is affine (`a • x + b • y` splits with `a + b = 1`).
  No supremum-of-`ConvexOn` lemma from Mathlib was needed — the flagged `convexOn_iSup` is avoided.
- `isConvexSeq_of_convexOn` is `ConvexOn.slope_mono_adjacent` at `j, j+1, j+2` (denominators `1`)
  plus `monotone_nat_of_le_succ`; `push_cast` leaves `H (↑j + 1 + 1)`, which must be rewritten to
  `H (↑j + 2)` for `linarith` to see one atom.

### [CLEANUP-2] Run /cleanup on `ConvexSeq.lean` (second pass)
- **Status**: done · **Depends on**: T006 · **Type**: cleanup — cadence rule.
#### Progress
- 2026-09-12: done as part of the single inline cleanup pass on `ConvexSeq.lean` (see CLEANUP-3).

### [T007] Asymptotics of a convex sequence
- **Status**: done · **File**: `ConvexSeq.lean` · **Depends on**: CLEANUP-2 · **Type**: lemmas · **Leaves**: L1.20, L1.21
#### Statement
```lean
theorem IsConvexSeq.tendsto_unitSlope (hh : IsConvexSeq h) (hfin : ∀ k, h k ≠ ⊤)
    (hb : BddAbove (Set.range fun j ↦ (unitSlope h j).untop₀)) :
    Filter.Tendsto (fun j ↦ (unitSlope h j).untop₀) Filter.atTop (nhds (⨆ j, (unitSlope h j).untop₀))
theorem IsConvexSeq.antitone_or_eventually_monotone (hh : IsConvexSeq h) :
    (∀ k, h (succ k) ≠ ⊤ → h (succ k) ≤ h k) ∨ ∃ N, ∀ k, N ≤ k → h k ≤ h (succ k)
```
#### Proof sketch
1. `tendsto_unitSlope`: `Monotone` of the real sequence from `hh.monotoneOn` on `univ`
   (`WithTop.coe_le_coe` after `unitSlope_of_ne_top`), then `tendsto_atTop_ciSup hmono hb` (verified
   generic in the probe).
2. `antitone_or_eventually_monotone`: `by_cases ∃ N, h N ≠ ⊤ ∧ h (succ N) ≠ ⊤ ∧ 0 ≤ unitSlope h N`;
   right disjunct from `N` by monotonicity and `add_unitSlope` (`le_add_of_nonneg_right`); else every
   finite unit slope is `< 0`, and at `k` with `h (succ k) ≠ ⊤`: if `h k = ⊤`, `le_top`; else
   `h (succ k) = h k + unitSlope h k ≤ h k`.
#### Mathlib lemmas needed
`tendsto_atTop_ciSup`, `le_add_of_nonneg_right`, `le_top`, `not_le`.
#### Sources
[RM] §0.1.5; decomposition L1.20–L1.21.
#### Generality decision
Generic `ι` (`[Nonempty ι]` for the supremum).
#### Progress
- 2026-09-12: DONE. `tendsto_unitSlope`, `antitone_or_eventually_monotone`.
- Statement change: `[Nonempty ι]` dropped from `tendsto_unitSlope` — Mathlib's
  `tendsto_atTop_ciSup` handles the empty case (`atTop = ⊥`), so the instance was unused and
  `runLinter`'s `unusedArguments` flagged it.
- In the eventually-monotone branch the `h k = ⊤` case needs `top_le_iff` and
  `IsConvexSeq.eq_top_of_le`, not `le_top` (the inequality runs the other way).
- `push_neg` is deprecated in this toolchain: `push Not at hex`.

### [CLEANUP-3] Run /cleanup on `ConvexSeq.lean` (final)
- **Status**: done · **Depends on**: T007 · **Type**: cleanup — final per-file pass.

---
#### Progress
- 2026-09-12: **inline cleanup pass on the finished file** (the user's standing preference is inline
  cleanup, no dispatched workers; the three cadence cleanups were collapsed into one pass on the
  complete file rather than three passes on partial states).
- `lake build PhD.TauCeti.Code.NewtonPolygons.ConvexSeq` → `✔`, no warnings of any kind.
- `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.ConvexSeq` → "Linting passed" (35 declarations,
  14 linters). One finding fixed: the unused `[Nonempty ι]` on `tendsto_unitSlope`.
- `#print axioms` on all 16 public theorems: `[propext, Classical.choice, Quot.sound]` only.
- Style: no line over 100 characters, no trailing whitespace or tabs, every declaration has a
  docstring, `omit` used wherever a section instance is unnecessary, imports minimal (12 modules, no
  `import Mathlib`).
- Deferred (noted, not done): `le_chord`, `extend_affine` and `exists_convexOn` have 40–60-line
  proof bodies. Their sub-steps are single-use, so no helper was extracted; if a later pass wants
  them shorter, the candidates are the two telescoping-with-pivot bounds inside `le_chord` and
  `exists_convexOn`, which are the same computation twice.

### [T008] The specification: finiteness below the points
- **Status**: done · **File**: `Basic.lean` · **Depends on**: CLEANUP-3 · **Type**: lemmas · **Leaves**: L2.2, L2.3 (L2.1 `unique` is already proved in the skeleton)
#### Statement
```lean
theorem IsNewtonPolygonOf.ne_top_of_ne_top (hh : IsNewtonPolygonOf v h) {k : ι} (hk : v k ≠ ⊤) : h k ≠ ⊤
theorem IsNewtonPolygonOf.ne_top_of_le_of_le (hh : IsNewtonPolygonOf v h) {a k b : ι}
    (ha : v a ≠ ⊤) (hb : v b ≠ ⊤) (hak : a ≤ k) (hkb : k ≤ b) : h k ≠ ⊤
```
#### Proof sketch
`ne_top_of_le_ne_top hk (hh.le_points k)`; then `hh.convex.ordConnected.out` at `a` and `b`.
#### Mathlib lemmas needed
`ne_top_of_le_ne_top`, `Set.OrdConnected.out`.
#### Sources
[RM] §0.2.1–0.2.2; decomposition L2.2–L2.3.
#### Generality decision
Generic `ι`.
#### Progress
- 2026-09-12: DONE, both one-liners (`ne_top_of_le_ne_top` and `ordConnected.out`).

### [T009] Admissibility on `ℕ`: four characterisations
- **Status**: done · **File**: `Basic.lean` · **Depends on**: T008 · **Type**: lemmas · **Leaves**: L2.5, L2.6, L2.C, L2.D
#### Statement
```lean
theorem isAdmissible_iff_bddBelow : IsAdmissible v ↔ ∀ i, v i ≠ ⊤ → BddBelow (slopeSet v i)
theorem isAdmissible_of_line {y σ : ℝ} (hv : ∀ k : ℕ, ((y + σ * k : ℝ) : WithTop ℝ) ≤ v k) : IsAdmissible v
theorem isAdmissible_iff_exists_line : IsAdmissible v ↔ ∃ y σ : ℝ, ∀ k : ℕ, ((y + σ * k : ℝ) : WithTop ℝ) ≤ v k
theorem exists_isConvexMinorant_iff_isAdmissible : (∃ g, IsConvexMinorant v g) ↔ IsAdmissible v
```
#### Proof sketch
1. `isAdmissible_iff_bddBelow`: as before (`csInf_le`, `le_csInf`, `div_le_iff`).
2. `isAdmissible_of_line`: slope-set bound `σ - |v i - y - σ i|` (decomposition L2.6), then item 1.
3. `isAdmissible_iff_exists_line`: `←` item 2; `→`: `i₀ := Nat.find` of a point (if none, any line
   works since `v ≡ ⊤`), `s` from `hv i₀`, `y := untop₀ (v i₀) - s * i₀`; below `i₀` the values are
   `⊤`.
4. `exists_isConvexMinorant_iff_isAdmissible`: `→`: a convex minorant `g` bounds the slopes out of
   every finite `i`: `slopeTo v i k ≥ (g k - v i)/(k - i) ≥ s - (v i - g i)` with `s := untop₀
   (unitSlope g i)` when `g i` finite (L2.7 corrected route; if `g i = ⊤` then `v i = ⊤`,
   excluded); `←`: `affineFrom i₀ (untop₀ (v i₀)) s` (T004) or `⊤` when `v ≡ ⊤`.
#### Mathlib lemmas needed
`csInf_le`, `le_csInf`, `div_le_iff`, `le_div_iff`, `Nat.find`, `Nat.find_spec`, `Nat.find_min'`,
`abs_nonneg`, `WithTop.coe_le_coe`, `WithTop.coe_nsmul`.
#### Sources
[RM] §0.2.3; [SRC] `SpecConstruction.isAdmissible_of_affine_bound`; decomposition L2.5, L2.6, L2.C, L2.D.
#### Generality decision
`ℕ`: the one-sided form the walk needs; the "above a line" form is the one that generalises (`Int.lean`).
#### Progress
- 2026-09-12: DONE. `isAdmissible_iff_bddBelow`, `isAdmissible_of_line`, `isAdmissible_iff_exists_line`,
  `exists_isConvexMinorant_iff_isAdmissible`.
- The slack trick appears twice and is the heart of both "line ⇒ admissible" directions: from a bound
  at `i` with slack `d ≥ 0` (`d = v i - (y + σ i)`, resp. `v i - g i`), the admissible slope is
  `σ - d`, and `(k - i) ≥ 1` absorbs the slack: `(k-i)(σ-d) ≤ (k-i)σ - d`. `nlinarith` needs the
  product hint `mul_nonneg (0 ≤ (k:ℝ) - i - 1) (0 ≤ d)`.
- `exists_isConvexMinorant_iff_isAdmissible` →: a convex minorant `g` with `unitSlope g i = ⊤` is the
  case the sketch missed — then `g` is `⊤` from `succ i` on, so every later *point* is `⊤` too
  (`g k ≤ v k`), and any slope works. Otherwise `add_nsmul_unitSlope_le` plus the slack trick.
  ←: `isAdmissible_iff_exists_line` + `isConvexSeq_affine` (no need for `affineFrom`).

### [T010] Existence: the supremum of the convex minorants is the polygon — MILESTONE
- **Status**: done · **File**: `Basic.lean` · **Depends on**: T009 · **Type**: lemmas · **Leaves**: L2.10–L2.12, L2.A, L2.B, L2.20 (generic)
#### Statement
```lean
theorem le_newtonPolygon (hg : IsConvexMinorant v g) (k : ι) : g k ≤ newtonPolygon v k
theorem newtonPolygon_le (hne : ∃ g, IsConvexMinorant v g) (k : ι) : newtonPolygon v k ≤ v k
theorem IsNewtonPolygonOf.eq_newtonPolygon (hh : IsNewtonPolygonOf v h) : h = newtonPolygon v
theorem newtonPolygon_mono (hne : ∃ g, IsConvexMinorant v g) (hvw : ∀ k, v k ≤ w k) (k : ι) :
    newtonPolygon v k ≤ newtonPolygon w k
theorem isConvexSeq_newtonPolygon (hne : ∃ g, IsConvexMinorant v g) : IsConvexSeq (newtonPolygon v)
theorem isNewtonPolygonOf_newtonPolygon (hne : ∃ g, IsConvexMinorant v g) : IsNewtonPolygonOf v (newtonPolygon v)
theorem exists_isNewtonPolygonOf_iff : (∃ h, IsNewtonPolygonOf v h) ↔ ∃ g, IsConvexMinorant v g
```
#### Proof sketch
1. `le_newtonPolygon`: `le_ciSup (OrderTop.bddAbove _) ⟨g, hg⟩`. `newtonPolygon_le`: `Nonempty` from
   `hne`, `ciSup_le fun g ↦ g.2.2 k`. `isConvexSeq_newtonPolygon`: `IsConvexSeq.iSup` (T005).
2. `isNewtonPolygonOf_newtonPolygon`: `⟨isConvexSeq_newtonPolygon hne, newtonPolygon_le hne,
   fun g hg hgv k ↦ le_newtonPolygon ⟨hg, hgv⟩ k⟩` — three fields, nothing else.
3. `eq_newtonPolygon`: `hh.unique (isNewtonPolygonOf_newtonPolygon ⟨h, hh.isConvexMinorant⟩)`.
4. `exists_isNewtonPolygonOf_iff`: `⟨fun ⟨h, hh⟩ ↦ ⟨h, hh.isConvexMinorant⟩, fun hne ↦ ⟨_,
   isNewtonPolygonOf_newtonPolygon hne⟩⟩`.
5. `newtonPolygon_mono`: `ciSup_le fun g ↦ le_newtonPolygon ⟨g.2.1, fun k ↦ (g.2.2 k).trans (hvw k)⟩ k`.
#### Mathlib lemmas needed
`le_ciSup`, `OrderTop.bddAbove`, `ciSup_le`.
#### Sources
[Ked07, §1] (the definition as an intersection of halfplanes); [RM] §0.2.4; decomposition L2.10–L2.12,
L2.A, L2.B, revision 2.
#### Generality decision
Generic `ι`; the only hypothesis anywhere is that some convex minorant exists.
#### Progress
- 2026-09-12: DONE (milestone: the polygon exists). `le_newtonPolygon`, `newtonPolygon_le`,
  `eq_newtonPolygon`, `newtonPolygon_mono`, `isConvexSeq_newtonPolygon`,
  `isNewtonPolygonOf_newtonPolygon`, `exists_isNewtonPolygonOf_iff`.
- `eq_newtonPolygon` needs no Existence-section instances after all: `h` itself makes the minorant
  family nonempty, so `le_antisymm (le_newtonPolygon …) (ciSup_le fun g' ↦ hh.greatest …)` proves it
  inside the `Spec` section. The ticket's sketch routed it through
  `isNewtonPolygonOf_newtonPolygon`; this is shorter and has fewer hypotheses.
- `Nonempty {g // IsConvexMinorant v g}` must be introduced as a local instance before `ciSup_le`.

### [CLEANUP-4] Run /cleanup on `Basic.lean` (first pass)
- **Status**: done · **Depends on**: T010 · **Type**: cleanup — cadence rule.
#### Progress
- 2026-09-12: done as part of the single inline cleanup pass on `Basic.lean` (see CLEANUP-5).

### [T011] The specification on `ℕ`: admissibility and anchoring as theorems
- **Status**: done · **File**: `Basic.lean` · **Depends on**: CLEANUP-4 · **Type**: lemmas · **Leaves**: L2.7, L2.E, L2.F, L2.4
#### Statement
```lean
theorem IsNewtonPolygonOf.isAdmissible (hh : IsNewtonPolygonOf v h) : IsAdmissible v
theorem exists_isNewtonPolygonOf_iff_isAdmissible : (∃ h, IsNewtonPolygonOf v h) ↔ IsAdmissible v
theorem IsNewtonPolygonOf.anchor_eq (hh : IsNewtonPolygonOf v h) {i : ℕ} (hi : ∀ k < i, v k = ⊤) (hi' : v i ≠ ⊤) :
    h i = v i
theorem IsNewtonPolygonOf.eq_top_of_forall_eq_top (hh : IsNewtonPolygonOf v h) {k : ℕ} (hk : ∀ j ≤ k, v j = ⊤) :
    h k = ⊤
theorem IsNewtonPolygonOf.eq_top_of_forall_le (hh : IsNewtonPolygonOf v h) {n : ℕ} (hn : ∀ k, n ≤ k → v k = ⊤) :
    h n = ⊤
```
#### Proof sketch
1. `isAdmissible`: `exists_isConvexMinorant_iff_isAdmissible.1 ⟨h, hh.isConvexMinorant⟩` (T009).
2. `exists_isNewtonPolygonOf_iff_isAdmissible`: `exists_isNewtonPolygonOf_iff.trans
   exists_isConvexMinorant_iff_isAdmissible` (T010, T009).
3. `anchor_eq`: `le_antisymm (hh.le_points i) ?_`; the admissible line through `(i, v i)` with slope
   `s` from `hh.isAdmissible i hi'`, as `affineFrom i (untop₀ (v i)) s` (T004), is a convex minorant
   (below `i` the values are `⊤`, from `i` on by admissibility), so `hh.greatest` at `i` gives
   `v i ≤ h i`.
4. `eq_top_of_forall_eq_top`: if `v ≡ ⊤` then every constant is a convex minorant and `hh.greatest`
   gives `h k ≥ c` for all `c`; else let `i₀` be the first point; `k < i₀`; for real `M` the two-slope
   competitor — `untop₀ (v i₀) + (i₀ - j) * M'` for `j < i₀` (large for large `M'`), the admissible
   line from `i₀` on, `M' ≥ -s` — is convex (`isConvexSeq_twoSlope`-style or `extend_affine`
   mirrored; the ticket may add a private left-steepening lemma) and `≤ v`; `hh.greatest` at `k` and
   `WithTop.eq_top_iff_forall_gt`.
5. `eq_top_of_forall_le`: `by_contra`; if no point precedes `n`, item 4; else bump-and-steepen
   competitor (decomposition L2.4): `g := fun k ↦ if k < n then h k else h n + 1 + (k - n) • M` with
   `M` above every unit slope of `h` below `n` (`IsConvexSeq.extend_affine` after the bump), `≤ v`
   since `v = ⊤` from `n` on; `hh.greatest g n : h n + 1 ≤ h n`, contradiction.
#### Mathlib lemmas needed
`WithTop.eq_top_iff_forall_gt`, `WithTop.coe_lt_coe`, `lt_add_one`, `Nat.find`, and T004/T009/T010.
#### Sources
[RM] §0.2.3, §0.2.5; [SRC] `Face.height_eq_top_of_forall_eq_top`, `SpecConstruction.IsNewtonPolygonOf.bddBelow`;
decomposition L2.4, L2.7, L2.E, L2.F.
#### Generality decision
`ℕ`: these are the statements that need a first point.
#### Progress
- 2026-09-12: DONE. `anchor_eq`, `eq_top_of_forall_eq_top`, `eq_top_of_forall_le`.
- **Both `⊤` theorems are shorter than the sketch.** `eq_top_of_forall_eq_top`: for `c` above the
  admissible line's value at `k`, the *single* line through `(k, c)` of slope `s - (c - (y + s k))`
  lies below every point (at `j > k` the slack `(c - (y + sk))(j - k - 1) ≥ 0` absorbs, at `j ≤ k`
  the points are `⊤`), so `greatest` gives `↑c ≤ h k` for every such `c`. No two-slope competitor and
  no left-steepening is needed. `eq_top_of_forall_le`: the constraints sit at the finitely many
  `j < n`, so a single line through `(n, h n + 1)` with slope `σ` above the finite set
  `{(h n + 1 - v j)/(n - j) | j < n}` (bounded by `(Set.finite_Iio n).image _ |>.bddAbove`) is a
  convex minorant, and `greatest` gives `h n + 1 ≤ h n`.
- `anchor_eq` is the sketch's argument: `affineFrom i (v i).untop₀ s` with `s` from admissibility.

### [T012] The vertical case
- **Status**: done · **File**: `Basic.lean` · **Depends on**: T011 · **Type**: def + lemmas · **Leaves**: L2.G, L2.8, L2.9
#### Statement
```lean
def IsVertical (v : ℕ → WithTop ℝ) : Prop := (∃ i, v i ≠ ⊤) ∧ ¬ IsAdmissible v
theorem isVertical_iff_not_exists_isConvexMinorant (hv : ∃ i, v i ≠ ⊤) : IsVertical v ↔ ¬ ∃ g, IsConvexMinorant v g
theorem exists_isNewtonPolygonOf_or_isVertical (hv : ∃ i, v i ≠ ⊤) : (∃ h, IsNewtonPolygonOf v h) ∨ IsVertical v
theorem not_isAdmissible_neg_sq : ¬ IsAdmissible fun k : ℕ ↦ ((-(k : ℝ) ^ 2 : ℝ) : WithTop ℝ)
theorem isVertical_neg_sq : IsVertical fun k : ℕ ↦ ((-(k : ℝ) ^ 2 : ℝ) : WithTop ℝ)
theorem not_exists_isNewtonPolygonOf_neg_sq : ¬ ∃ h, IsNewtonPolygonOf (fun k : ℕ ↦ ((-(k : ℝ) ^ 2 : ℝ) : WithTop ℝ)) h
```
#### Proof sketch
1. `isVertical_iff_not_exists_isConvexMinorant`: unfold; `exists_isConvexMinorant_iff_isAdmissible` (T009).
2. `exists_isNewtonPolygonOf_or_isVertical`: `Classical.em (IsAdmissible v)`; `exists_isNewtonPolygonOf_iff_isAdmissible` (T011).
3. `not_isAdmissible_neg_sq`: at `i = 0`, `k := ⌈|s|⌉₊ + 1` gives `k s ≤ -k²`, i.e. `s ≤ -k < -|s|`.
4. `isVertical_neg_sq`: `⟨⟨0, by simp⟩, not_isAdmissible_neg_sq⟩`. `not_exists…`: via `exists_isNewtonPolygonOf_iff_isAdmissible`.
#### Mathlib lemmas needed
`Nat.ceil`, `Nat.le_ceil`, `Classical.em`, `WithTop.coe_le_coe`, `WithTop.coe_nsmul`.
#### Sources
[RM] §0.2.3 (vertical case, as amended), convention 5; [Kob84, §IV.4] (the vertical type); [SRC]
`SpecConstruction` docstring ("the hull 'is vertical'"); decomposition L2.8, L2.9, L2.G.
#### Generality decision
A predicate, never an object (plan.md decision 10).
#### Progress
- 2026-09-12: DONE. `IsVertical`, `isVertical_iff_not_exists_isConvexMinorant`,
  `exists_isNewtonPolygonOf_or_isVertical`, `not_isAdmissible_neg_sq`, `isVertical_neg_sq`,
  `not_exists_isNewtonPolygonOf_neg_sq`. `-k²`: admissibility at `0` would give `k s ≤ -k²` for every
  `k`, i.e. `s ≤ -k`, contradicted by any `k > |s|` (`exists_nat_gt`).

### [T035] Invariance of the polygon (on `ℕ`)
- **Status**: done · **File**: `Basic.lean` · **Depends on**: T012 · **Type**: lemmas · **Leaves**: L2.H
#### Statement
```lean
theorem newtonPolygon_add_affine (hv : IsAdmissible v) (y σ : ℝ) :
    newtonPolygon (fun k ↦ v k + ((y + σ * k : ℝ) : WithTop ℝ)) = fun k ↦ newtonPolygon v k + ((y + σ * k : ℝ) : WithTop ℝ)
theorem newtonPolygon_add_const (hv : IsAdmissible v) (c : ℝ) :
    newtonPolygon (fun k ↦ v k + (c : WithTop ℝ)) = fun k ↦ newtonPolygon v k + (c : WithTop ℝ)
```
#### Proof sketch
`funext k`; `v + ℓ` is admissible (`isAdmissible_iff_exists_line`, shift the line); both minorant
families nonempty (T009); `≤`: each minorant `g` of `v + ℓ` gives `g - ℓ` minorant of `v`
(`add_affine` with `-ℓ`), `le_newtonPolygon`, `ciSup_le`; `≥`: `g + ℓ` and `le_newtonPolygon`, then
`ciSup_le` on the `v` side after `WithTop.add_le_add_iff_right`. `add_const` is `σ = 0`.
#### Mathlib lemmas needed
`ciSup_le`, `le_ciSup`, `WithTop.add_le_add_iff_right`, `add_le_add_right`, `WithTop.coe_add`.
#### Sources
[RM] §0.2.5; decomposition L2.18–L2.20, L2.H.
#### Generality decision
Needs only `IsAdmissible v` (for `v ≡ ⊤` the family is nonempty anyway).
#### Progress
- 2026-09-12: DONE. `newtonPolygon_add_affine`, `newtonPolygon_add_const`.
- Proved by *constructing* the sheared polygon rather than by two `ciSup` inequalities: show
  `IsNewtonPolygonOf (v + ℓ) (newtonPolygon v + ℓ)` (convexity from `IsConvexSeq.add_affine`,
  maximality by shearing a competitor back with `-ℓ`), then `eq_newtonPolygon`. Cancellation in
  `WithTop ℝ` needs the local `x + ↑c + ↑d = x` for `c + d = 0`. `add_const` is the `σ = 0` case.

### [CLEANUP-5] Run /cleanup on `Basic.lean` (final)
- **Status**: done · **Depends on**: T035 · **Type**: cleanup — final per-file pass.

---
#### Progress
- 2026-09-12: inline cleanup pass on the finished file. `lake build` → `✔` with no warnings;
  `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.Basic` → "Linting passed"; `#print axioms` on
  the twelve headline declarations → `[propext, Classical.choice, Quot.sound]`. Style sweep over the
  whole Layer 0 directory: every line is now ≤ 100 characters (21 lines rewrapped across 6 files),
  no trailing whitespace, no tabs. Deprecated import fixed (`Mathlib.Data.Nat.Lattice` →
  `Mathlib.Order.Lattice.Nat`), deprecated `push_neg` → `push Not`.

### [T036] `Int.lean`: the reduction and existence on `ℤ`
- **Status**: done · **File**: `Int.lean` · **Depends on**: CLEANUP-5 · **Parallel**: yes (independent of G3–G7) · **Type**: def + lemmas · **Leaves**: LZ.1–LZ.10
#### Statement
```lean
noncomputable def extendTop (v : ℕ → WithTop ℝ) : ℤ → WithTop ℝ := fun k ↦ if 0 ≤ k then v k.toNat else ⊤
@[simp] theorem extendTop_natCast (v : ℕ → WithTop ℝ) (n : ℕ) : extendTop v n = v n
theorem extendTop_of_neg (v : ℕ → WithTop ℝ) {k : ℤ} (hk : k < 0) : extendTop v k = ⊤
theorem unitSlope_extendTop_natCast (h : ℕ → WithTop ℝ) (n : ℕ) : unitSlope (extendTop h) n = unitSlope h n
theorem isConvexSeq_extendTop_iff : IsConvexSeq (extendTop h) ↔ IsConvexSeq h
theorem isConvexMinorant_extendTop_iff : IsConvexMinorant (extendTop v) (extendTop h) ↔ IsConvexMinorant v h
theorem isNewtonPolygonOf_extendTop_iff : IsNewtonPolygonOf (extendTop v) (extendTop h) ↔ IsNewtonPolygonOf v h
theorem newtonPolygon_extendTop (hv : IsAdmissible v) : newtonPolygon (extendTop v) = extendTop (newtonPolygon v)
theorem IsNewtonPolygonOf.eq_top_of_forall_lt {v h : ℤ → WithTop ℝ} (hh : IsNewtonPolygonOf v h) {k : ℤ}
    (hk : ∀ j ≤ k, v j = ⊤) : h k = ⊤
theorem isConvexSeq_affine_int (y σ : ℝ) : IsConvexSeq fun k : ℤ ↦ ((y + σ * k : ℝ) : WithTop ℝ)
theorem exists_isConvexMinorant_iff_exists_line {v : ℤ → WithTop ℝ} :
    (∃ g, IsConvexMinorant v g) ↔ ∃ y σ : ℝ, ∀ k : ℤ, ((y + σ * k : ℝ) : WithTop ℝ) ≤ v k
theorem not_exists_isConvexMinorant_neg_abs : ¬ ∃ g, IsConvexMinorant (fun k : ℤ ↦ ((-|(k : ℝ)| : ℝ) : WithTop ℝ)) g
```
#### Proof sketch
1. `extendTop` API: `if_pos`/`if_neg`, `Int.toNat_natCast`, `Int.toNat_of_nonneg`; `unitSlope_extendTop_natCast`:
   `Order.succ_eq_add_one`, `Nat.cast_succ`, then the two evaluation lemmas.
2. `isConvexSeq_extendTop_iff`: `finiteSet (extendTop h) = (↑) '' finiteSet h`; order-connected iff
   the original is (`Int.toNat` / `Nat.cast` monotone bijection between `Ici 0` and `ℕ`); unit slopes
   agree at naturals (item 1) and are `⊤` at negatives.
3. `isConvexMinorant_extendTop_iff`, `isNewtonPolygonOf_extendTop_iff`: item 2 for convexity; `≤`
   pointwise by cases on the sign; `greatest`: restrict a `ℤ`-minorant to `ℕ` (convex by the
   `ℕ`-direction of item 2 applied to the restriction, which is order-connected as a subinterval)
   and extend a `ℕ`-minorant by `⊤`.
4. `newtonPolygon_extendTop`: `isNewtonPolygonOf_extendTop_iff.2 (isNewtonPolygonOf_newtonPolygon
   (exists_isConvexMinorant_iff_isAdmissible.2 hv))` then `IsNewtonPolygonOf.eq_newtonPolygon` on `ℤ`.
5. `eq_top_of_forall_lt`: steepened-left competitor from a point (or constants if `v ≡ ⊤`),
   `hh.greatest`, `WithTop.eq_top_iff_forall_gt`.
6. `isConvexSeq_affine_int`: as T004 with `Int.cast`. `exists_isConvexMinorant_iff_exists_line`: `←`
   the line; `→` from a convex `g ≤ v` finite at `i` with `s := untop₀ (unitSlope g i)`: right,
   `IsConvexSeq.add_nsmul_unitSlope_le`; left, `IsConvexSeq.le_add_nsmul_unitSlope` with `s_{j} ≤ s`
   for `j < i`, both with `Int.card_Ico`; if `g ≡ ⊤`, `v ≡ ⊤`.
7. `not_exists_isConvexMinorant_neg_abs`: item 6 `→`, then a line `y + σ k ≤ -|k|` at `k = ±n` for
   large `n` forces `σ ≤ -1` and `σ ≥ 1`.
#### Mathlib lemmas needed
`Int.toNat_natCast`, `Int.toNat_of_nonneg`, `Int.card_Ico`, `Nat.cast_succ`, `Order.succ_eq_add_one`,
`Set.OrdConnected`, `WithTop.eq_top_iff_forall_gt`, `abs_of_nonneg`, `abs_of_nonpos`, `Filter.Tendsto` not needed.
#### Sources
[RM] §0.2.6 (as amended); decomposition revision 2, LZ.1–LZ.10.
#### Generality decision
`ℤ` only where a coordinate is needed; the reduction is the deliverable, no further `ℤ` API.
#### Progress
- 2026-09-12: DONE — `Int.lean` is sorry-free, lint-clean, standard axioms. The §0.2.6 reduction
  `newtonPolygon (extendTop v) = extendTop (newtonPolygon v)` and the `-|k|` counterexample are proved.
- Four API lemmas added beyond the ticket (all natural companions, logged here): `extendTop_of_nonneg`,
  `nonneg_of_extendTop_ne_top`, `succ_natCast`, `unitSlope_comp_natCast` and
  `IsConvexSeq.comp_natCast` (the restriction of a convex `ℤ`-sequence to `ℕ` — needed for the
  `greatest` field of `isNewtonPolygonOf_extendTop_iff`).
- `IsNewtonPolygonOf.eq_top_of_forall_lt` moved after `exists_isConvexMinorant_iff_exists_line`: it
  needs the `ℤ` line characterisation (there is no `isAdmissible` on `ℤ`).
- `exists_isConvexMinorant_iff_exists_line` → uses the slope `if unitSlope g i = ⊤ then
  (unitSlope g (i-1)).untop₀ else (unitSlope g i).untop₀`, which makes the degenerate cases
  (`g` stopping at `i`, `g` starting at `i`) fall out: `untop₀ ⊤ = 0` absorbs the third case.
  `Int.card_Ico` gives `(q - p).toNat`, so each bound needs the cast `((q-p).toNat : ℝ) = q - p`.
- `open Order` had to be added to the file (the generic `succ` appears in the statements).

### [CLEANUP-15] Run /cleanup on `Int.lean` (final)
- **Status**: done · **Depends on**: T036 · **Type**: cleanup — final per-file pass.

---
#### Progress
- 2026-09-13: DONE (final pass on `Int.lean`). `lake build` clean, `runLinter` passes, 351 lines,
  no over-long line after two were wrapped (recorded in CLEANUP-12). Fixes: nine missing docstrings
  written (`extendTop_natCast`, `extendTop_of_neg`, `extendTop_of_nonneg`,
  `nonneg_of_extendTop_ne_top`, `succ_natCast`, `unitSlope_extendTop_natCast`,
  `isConvexSeq_extendTop_iff`, `isConvexMinorant_extendTop_iff`, `isNewtonPolygonOf_extendTop_iff`);
  `simp [extendTop]` made `simp only [extendTop, Nat.cast_nonneg, ↓reduceIte, Int.toNat_natCast]`.

### [T013] Anchor and vertices
- **Status**: done · **File**: `Slope.lean` · **Depends on**: CLEANUP-5 · **Type**: lemmas · **Leaves**: L4.1–L4.6
#### Statement
```lean
theorem anchor_mem (hne : ∃ i, h i ≠ ⊤) : h (anchor h) ≠ ⊤
theorem anchor_le {i : ℕ} (hi : h i ≠ ⊤) : anchor h ≤ i
theorem eq_top_of_lt_anchor {k : ℕ} (hk : k < anchor h) : h k = ⊤
theorem IsNewtonPolygonOf.anchor_eq_sInf (hh : IsNewtonPolygonOf v h) (hv : ∃ i, v i ≠ ⊤) :
    anchor h = sInf (finiteSet v)
theorem isVertex_anchor (hne : ∃ i, h i ≠ ⊤) : IsVertex h (anchor h)
theorem isVertex_of_succ_eq_top (hh : IsConvexSeq h) {k : ℕ} (hk : h k ≠ ⊤) (hk1 : h (k + 1) = ⊤) :
    IsVertex h k
```
#### Proof sketch
1. `Nat.sInf_mem hne`, `Nat.sInf_le hi`, `Nat.not_mem_of_lt_sInf hk` (loogle; fallback:
   `by_contra` + `Nat.sInf_le`).
2. `anchor_eq_sInf`: let `i₀ := sInf (finiteSet v)`; `h i₀ = v i₀ ≠ ⊤` by `hh.anchor_eq i₀
   (fun k hk ↦ Nat.not_mem_of_lt_sInf hk) (Nat.sInf_mem hv)`, so `anchor h ≤ i₀`; for `k < i₀`,
   `v j = ⊤` for all `j ≤ k`, so `h k = ⊤` (`hh.eq_top_of_forall_eq_top`), so `i₀ ≤ anchor h`.
3. `isVertex_anchor`: `⟨anchor_mem hne, Or.inl rfl⟩`.
4. `isVertex_of_succ_eq_top`: `refine ⟨hk, ?_⟩`; `rcases eq_or_lt_of_le (anchor_le hk)`: equal →
   `Or.inl`; `anchor h < k` → `h (k-1) ≠ ⊤` by `hh.ordConnected.out (anchor_mem ⟨k, hk⟩) hk` and
   `unitSlope h (k-1) = ↑_ < ⊤ = unitSlope h k` (`unitSlope_of_ne_top`, `WithTop.coe_lt_top`,
   `unitSlope_eq_top_iff.2 (Or.inr hk1)`).
#### Mathlib lemmas needed
`Nat.sInf_mem`, `Nat.sInf_le`, `Nat.not_mem_of_lt_sInf`, `WithTop.coe_lt_top`.
#### Sources
[Kob84, §IV.3 p. 97]; [RM] §0.4.1; decomposition L4.1–L4.6.
#### Generality decision
`IsVertex` includes the anchor and the last finite index by construction (both are vertices of the
hull in every textbook picture).
#### Progress
- 2026-09-12: DONE. `anchor`, `anchor_mem`, `anchor_le`, `eq_top_of_lt_anchor`, `anchor_eq_sInf`,
  `isVertex_anchor`, `isVertex_of_succ_eq_top`. `Nat.notMem_of_lt_sInf` is the current name.

### [T014] A vertex is a point; segments are chords
- **Status**: done · **File**: `Slope.lean` · **Depends on**: T013 · **Type**: lemmas · **Leaves**: L4.7–L4.9
#### Statement
```lean
theorem IsNewtonPolygonOf.eq_of_isVertex (hh : IsNewtonPolygonOf v h) {k : ℕ} (hk : IsVertex h k) :
    h k = v k
theorem IsConvexSeq.unitSlope_eq_of_isSegment (hh : IsConvexSeq h) {a b : ℕ} (hab : IsSegment h a b)
    {j : ℕ} (haj : a ≤ j) (hjb : j < b) : unitSlope h j = unitSlope h a
theorem IsConvexSeq.eq_add_nsmul_of_isSegment (hh : IsConvexSeq h) {a b : ℕ} (hab : IsSegment h a b)
    {k : ℕ} (hak : a ≤ k) (hkb : k ≤ b) : h k = h a + (k - a : ℕ) • unitSlope h a
```
#### Proof sketch
1. `eq_of_isVertex`: `rcases hk with ⟨hk, rfl | hlt⟩`. Anchor: `hh.anchor_eq _ (fun j hj ↦ ?_) …`
   where `v j = ⊤` for `j < anchor h` because `h j = ⊤` (T013) and … ⚠ `h j = ⊤` does not give `v j
   = ⊤` directly; use `anchor_eq_sInf` (T013) to identify `anchor h` with `sInf (finiteSet v)` and
   then `Nat.not_mem_of_lt_sInf`. Strict case: `le_antisymm (hh.le_points k) ?_`; `by_contra hlt'`
   (`h k < v k`); build `g := Function.update h k (h k + ε)` with `ε := min ((s_k - s_{k-1})/2)
   (v k - h k)` (second term omitted when `v k = ⊤`, first when `s_k = ⊤`), all in `ℝ` via
   `untop₀`; show `IsConvexSeq g` (finiteness set unchanged; unit slopes change only at `k-1` (up by
   `ε`) and `k` (down by `ε`), and `s_{k-1} + ε ≤ s_k - ε` by the choice of `ε`; neighbours by
   monotonicity) and `g ≤ v`; then `hh.greatest g … k : h k + ε ≤ h k`, contradiction with `ε > 0`.
   Decomposition L4.7 lists the edge cases (last index; `v k = ⊤` derives `False`).
2. `unitSlope_eq_of_isSegment`: induction on `j` from `a`: for `a ≤ j`, `j + 1 < b`: `unitSlope h j
   ≤ unitSlope h (j+1)` (monotone: `h j, h (j+1)` finite as `a ≤ j < j+1 ≤ b`, order-connected
   between the vertices `a`, `b`); if strict, `⟨_, Or.inr this⟩ : IsVertex h (j+1)` with
   `a < j+1 < b` contradicts `hab.2.2.2`.
3. `eq_add_nsmul_of_isSegment`: `eq_add_nsmul_of_forall_unitSlope_eq (hab.1.1) hak (fun j haj hjk ↦
   (hh.unitSlope_eq_of_isSegment hab haj (hjk.trans_le hkb)).trans ?_)` with
   `unitSlope h a = ↑(untop₀ …)` (`WithTop.coe_untop₀_of_ne_top`, finite since `a < b` are both
   finite).
#### Mathlib lemmas needed
`Function.update`, `Function.update_apply`, `WithTop.coe_untop₀_of_ne_top`, `sub_pos`, `min_le_left`,
`Nat.le_induction`.
#### Sources
[Kob84, §IV.3 p. 97] (vertices are where the slopes change); [SRC] `Face.height_eq_pointHeight_of_
unitSlope_lt` (the source's margin-line proof; ours is the bump competitor); decomposition L4.7–L4.9.
#### Generality decision
Stated for any vertex, including the anchor and the last index; the bump argument is the
spec-level proof the roadmap asks for (no walk).
#### Progress
- 2026-09-12: DONE. `eq_of_isVertex`, `unitSlope_eq_of_isSegment`, `eq_add_nsmul_of_isSegment`.
- `eq_of_isVertex` splits as the sketch says: at the anchor it is `anchor_eq` (T011) composed with
  `anchor_eq_sInf`; at a genuine break it is the ε-bump competitor. **The bump's convexity is much
  easier through the midpoint criterion than through unit slopes**: only the index `j` with
  `j + 1 = k` needs the convexity gap `2ε ≤ h (k-1) + h (k+1) - 2 h k`, and the other three cases
  follow from `h`'s own midpoint inequality plus `h k ≤ h k + ε`. The gap is positive exactly because
  `k` is a genuine break; `h (k-1) ≠ ⊤` is automatic there (a `⊤` would make the slope `⊤`), and
  `h (k+1) = ⊤` makes the right-hand side `⊤`.
- `Function.update` was not needed: a plain `if j = k then … else …` with `simp [hgdef]` is enough.

### [T015] The slope multiset and purity
- **Status**: done · **File**: `Slope.lean` · **Depends on**: T014 · **Type**: lemmas · **Leaves**: L4.10–L4.15
#### Statement
```lean
theorem IsConvexSeq.slopeIndices_eq_Ico (hh : IsConvexSeq h) (hfin : (slopeIndices h).Finite)
    (hne : ∃ i, h i ≠ ⊤) : slopeIndices h = Set.Ico (anchor h) (anchor h + (slopeIndices h).ncard)
theorem card_slopeMultiset (hfin : (slopeIndices h).Finite) : (slopeMultiset h).card = (slopeIndices h).ncard
theorem count_slopeMultiset (hfin : (slopeIndices h).Finite) (σ : ℝ) :
    (slopeMultiset h).count σ = Set.ncard {j | unitSlope h j = σ}
theorem IsConvexSeq.anchor_add_sum_slopeMultiset (hh : IsConvexSeq h) (hfin : (slopeIndices h).Finite)
    (hne : ∃ i, h i ≠ ⊤) :
    h (anchor h) + (((slopeMultiset h).sum : ℝ) : WithTop ℝ) = h (anchor h + (slopeMultiset h).card)
theorem IsNewtonPolygonOf.slopeIndices_finite (hh : IsNewtonPolygonOf v h) (hfin : (finiteSet v).Finite) :
    (slopeIndices h).Finite
theorem isPure_iff_slopeMultiset (hfin : (slopeIndices h).Finite) (m : ℝ) :
    IsPure h m ↔ 0 < (slopeMultiset h).card ∧ slopeMultiset h = Multiset.replicate (slopeMultiset h).card m
```
#### Proof sketch
1. `slopeIndices_eq_Ico`: `unitSlope h j ≠ ⊤ ↔ h j ≠ ⊤ ∧ h (j+1) ≠ ⊤` (T001); with `finiteSet h`
   an interval `[anchor, last]` (finite: otherwise all `j ≥ anchor` carry finite slopes — infinite,
   contradicting `hfin`), the set is `Ico anchor last`, whose `ncard` is `last - anchor`
   (`Set.ncard_eq_toFinset_card'`, `Nat.card_Ico`).
2. `card_slopeMultiset`: `unfold slopeMultiset; rw [dif_pos hfin]; simp [Multiset.card_map,
   Set.ncard_eq_toFinset_card']`.
3. `count_slopeMultiset`: `Multiset.count_map` → card of `filter (fun j ↦ σ = untop₀ (unitSlope h
   j)) hfin.toFinset.val`; show this filter equals the `toFinset` of `{j | unitSlope h j = σ}`
   (`Finset.ext`; on `slopeIndices`, `untop₀ s = σ ↔ s = ↑σ` by `WithTop.coe_untop₀_of_ne_top`;
   off it `s = ⊤ ≠ ↑σ`); `Set.ncard_coe_finset`.
4. `anchor_add_sum_slopeMultiset`: `eq_add_sum_unitSlope` (T001) over `Ico anchor last` (all values
   finite there), and identify the `Finset.sum` with the multiset sum via item 1 (`Multiset.map`
   over `hfin.toFinset.val = (Finset.Ico …).val`, `Finset.sum_eq_multiset_sum`).
5. `slopeIndices_finite`: `hh.eq_top_of_forall_le` (T011) at `n := sSup (finiteSet v) + 1` gives
   `h = ⊤` from `n` on (with `eq_top_of_le`), so `slopeIndices h ⊆ Set.Iio n` (`Set.finite_Iio.subset`);
   if `finiteSet v = ∅` then `h ≡ ⊤` (field) and `slopeIndices = ∅`.
6. `isPure_iff_slopeMultiset`: `Multiset.eq_replicate` (`∀ b ∈ s, b = m`, card matches); membership
   in `slopeMultiset` is `∃ j ∈ slopeIndices, untop₀ (unitSlope h j) = b` (`Multiset.mem_map`);
   nonemptiness `↔ 0 < card` (`Multiset.card_pos`).
#### Mathlib lemmas needed
`Multiset.card_map`, `Multiset.count_map`, `Multiset.mem_map`, `Multiset.eq_replicate`,
`Multiset.card_pos`, `Set.ncard_eq_toFinset_card'`, `Set.ncard_coe_finset`, `Nat.card_Ico`,
`Set.finite_Iio`, `Set.Finite.subset`, `Finset.sum_eq_multiset_sum`, `Nat.sSup_mem`.
#### Sources
[Ked07, §1] ("the multiset consisting of the slopes of the polygon, each occurring with multiplicity
equal to the width of the corresponding segment"); [RM] §0.4.2–0.4.3; decomposition L4.10–L4.15.
#### Generality decision
`slopeMultiset` is total (junk `0` for infinitely many slopes); every lemma carries the finiteness
hypothesis explicitly.
#### Progress
- 2026-09-12: DONE. `mem_slopeIndices_iff` (added: the `⊤`-characterisation of a slope index, used
  five times), `slopeIndices_eq_Ico`, `card_slopeMultiset`, `count_slopeMultiset`,
  `anchor_add_sum_slopeMultiset`, `slopeIndices_finite`, `isPure_iff_slopeMultiset`.
- `slopeIndices_eq_Ico` goes through `sSup`: the slope indices form an order-connected set with
  minimum `anchor h` and maximum `sSup`, hence `Set.Icc (anchor h) (sSup …)`, whose `ncard` is
  `sSup + 1 - anchor h` (`Finset.coe_Icc`, `Set.ncard_coe_finset`, `Nat.card_Icc`).
- **Trap**: `rw [hIco]`/`rw [hSeq]` rewrite `slopeIndices h` *inside* `ncard` and `sSup` as well,
  which silently changes the statement being proved. Use `conv_lhs => rw [...]`, or a membership
  `iff` (`hmemIco`), not a set rewrite.
- `count_slopeMultiset` needs the filter as a `Finset` equality *before* counting
  (`Finset.filter_val`), otherwise `congr 1` leaves a multiset-extensionality goal.

### [CLEANUP-6] Run /cleanup on `Slope.lean` (first pass)
- **Status**: done · **Depends on**: T015 · **Type**: cleanup — cadence rule.
#### Progress
- 2026-09-12: done as part of the single inline cleanup pass on `Slope.lean` (see CLEANUP-7).

### [T016] The first break, read off the points
- **Status**: done · **File**: `Slope.lean` · **Depends on**: CLEANUP-6 · **Type**: theorem · **Leaf**: L4.16
#### Statement
```lean
theorem IsNewtonPolygonOf.hasFirstBreak_iff (hh : IsNewtonPolygonOf v h) (hv : ∃ i, v i ≠ ⊤)
    (m : ℝ) (l : ℕ) :
    HasFirstBreak h m l ↔ 0 < l ∧
      (∀ k, anchor h ≤ k → v (anchor h) + (k - anchor h : ℕ) • (m : WithTop ℝ) ≤ v k) ∧
      v (anchor h + l) = v (anchor h) + l • (m : WithTop ℝ) ∧
      ∃ m' : ℝ, m < m' ∧ ∀ k, anchor h + l ≤ k →
        v (anchor h + l) + (k - (anchor h + l) : ℕ) • (m' : WithTop ℝ) ≤ v k
```
#### Proof sketch
Write `a := anchor h`, `L k := v a + (k - a) • m`.
`→`: (i) `0 < l` from `hfb.1`. (ii) unit slopes from `a` are `≥ m` (first `l` equal `m`; `unitSlope
h (a + l) ≠ m` with monotonicity gives `> m` or `⊤`), so `h k ≥ h a + (k - a) • m` (T003) and `h a =
v a` (T014 at the anchor), `h k ≤ v k`. (iii) `a + l` is a vertex (`unitSlope (a+l-1) = m <
unitSlope (a+l)`, or `⊤` — T013 `isVertex_of_succ_eq_top`), so `v (a+l) = h (a+l) = h a + l • m`
(T014, T001 affine). (iv) `m' := untop₀ (unitSlope h (a+l))` if finite: then `v k ≥ h k ≥ h (a+l) +
(k - a - l) • m'` (T003) and `h (a+l) = v (a+l)`, with `m < m'`; if `⊤`: no point at or after `a +
l + 1` (`h = ⊤` there, T002 `eq_top_of_le`; `le_points` — contrapositive `ne_top_of_ne_top`), take
`m' := m + 1`, the bound holds vacuously for `k > a + l` and trivially at `k = a + l`.
`←`: `affineFrom a (untop₀ (v a)) m` is a convex minorant (clause (ii) + `v = ⊤` before `a`), so
`≤ h ≤ v`; at `a` and `a + l` it equals `v` (clause (iii)), so `h` equals it there; by the chord
inequality (T003, `h` below its chord which is the line, and the line below `h`) `h` is the line on
`[a, a + l]`: first `l` unit slopes `= m`. For the break: the two-slope minorant (`m` up to `a + l`,
then `m'`; `⊤` before `a`) is convex (`m ≤ m'`) and `≤ v` (clause (iv) and (ii)), hence `≤ h`; at
`a + l + 1` this gives `h (a+l+1) ≥ h (a+l) + m'`, so `unitSlope h (a+l) ≥ m' > m` (or `⊤`): `≠ m`.
#### Mathlib lemmas needed
`WithTop.coe_untop₀_of_ne_top`, `WithTop.coe_nsmul`, `WithTop.coe_lt_coe`, `lt_add_one`, and
T003/T004/T013/T014 lemmas.
#### Sources
[RM] §0.4.4 (**amended**: the roadmap's clause omits the steeper line; decomposition L4.16 has the
counterexample `v k = m k + 1/k`); [SRC] `FirstBreak.lean` (`HasFirstBreak`, `slope_mul_le/lt`).
#### Generality decision
The characterisation is an `↔` with the honest right-hand side; the roadmap text is to be amended
to match (user action, not this ticket).
#### Progress
- 2026-09-12: DONE. `hasFirstBreak_iff`, both directions, ~150 lines.
- → : the line of slope `m` through the anchor is below the points by `add_nsmul_unitSlope_le`;
  `A + l` is a vertex because the slope strictly increases there, so `h (A+l) = v (A+l)`
  (`eq_of_isVertex`); the steeper line is the polygon's own next slope when finite, and when it is
  `⊤` every later point is `⊤` and any `m' > m` works.
- ← : the line of slope `m` is a convex minorant, so it is *below* the polygon; with equality at
  `A + l` (condition 3) the telescoping sum of the first `l` slopes is `l · m` while each slope is
  `≥ m` (monotonicity from the first one), so all are `m`
  (`Finset.sum_eq_zero_iff_of_nonneg`). For the break: **the two-slope competitor is the max of the
  two lines** — they meet exactly at `A + l` by condition 3, so `IsConvexSeq.sup` of two
  `isConvexSeq_affine`s is the broken line, no new construction needed; `greatest` then forces
  `h (A+l+1) ≥ y + l m + m'`, contradicting `unitSlope h (A+l) = m`.

### [T017] Truncation
- **Status**: done · **File**: `Slope.lean` · **Depends on**: T016 · **Type**: lemmas · **Leaves**: L4.17, L4.18
#### Statement
```lean
theorem newtonPolygon_le_newtonPolygon_truncate (hv : IsAdmissible v) (n k : ℕ) :
    newtonPolygon v k ≤ newtonPolygon (truncate v n) k
theorem newtonPolygon_truncate_eq (hv : IsAdmissible v) {n V : ℕ}
    (hV : IsVertex (newtonPolygon v) V) (hVn : V ≤ n) {k : ℕ} (hk : k ≤ V) :
    newtonPolygon (truncate v n) k = newtonPolygon v k
```
#### Proof sketch
1. First: `newtonPolygon_mono hv hv' (fun k ↦ ?_)` with `v k ≤ truncate v n k` (`le_top` or
   `le_rfl` by cases on `k ≤ n`).
2. Second: `le_antisymm ?_ (newtonPolygon_le_newtonPolygon_truncate …)`. For `≤`: let `P :=
   newtonPolygon v` (spec by T010) and `Q := newtonPolygon (truncate v n)` (spec: `truncate v n` is
   admissible — finitely many points, `isAdmissible_iff_bddBelow` with finite slope sets — and has a
   point since `V ≤ n` is a vertex hence a point). Let `W₀ = anchor < W₁ < … < W_r = V` be the
   vertices of `P` that are `≤ V` (finitely many: `IsVertex` indices below `V`, `Set.finite_Iic`).
   At each `W_t`: `Q W_t ≤ truncate v n W_t = v W_t = P W_t` (T014, `W_t ≤ V ≤ n`). Between
   consecutive vertices `P` is the chord (T014 `eq_add_nsmul_of_isSegment`; consecutive vertices
   form an `IsSegment`) and `Q` is below its own chord (T003 `le_chord`) which is below `P`'s chord:
   so `Q k ≤ P k` for `W_t ≤ k ≤ W_{t+1}`. Before the anchor both are `⊤`. Organise by strong
   induction on `k ≤ V`: find the largest vertex `W ≤ k` and the smallest vertex `W' ≥ k`
   (`Nat.find` on the finite decidable predicate), apply the chord bound on `[W, W']`.
#### Mathlib lemmas needed
`Nat.find`, `Nat.find_spec`, `Nat.find_min'`, `Set.finite_Iic`, `le_top`, and T003/T012/T014.
#### Sources
[RM] §0.4.5 (strengthened: any vertex `≤ n`); decomposition L4.17–L4.18.
#### Generality decision
`hlast` dropped (see decomposition L4.18); the statement holds for every vertex `V ≤ n`.
#### Progress
- 2026-09-12: DONE. `truncate`, `newtonPolygon_le_newtonPolygon_truncate` (by `newtonPolygon_mono`),
  `newtonPolygon_truncate_eq`.
- Statement change: the unused `hv' : ∃ i, v i ≠ ⊤` dropped from both (the linter flags it;
  `IsVertex (newtonPolygon v) V` already carries a point).
- `newtonPolygon_truncate_eq` glues: `g := if j ≤ V then newtonPolygon (truncate v n) j else
  newtonPolygon v j`. The two polygons agree at `V` (`T V ≤ truncate v n V = v V = P V ≤ T V`), so
  the glued sequence is convex by the midpoint criterion — the only interesting index is
  `j + 1 = V`, where `P`'s midpoint inequality plus `P ≤ T` gives the bound. `g` is a convex minorant
  of `v`, so `greatest` gives `T k = g k ≤ P k` for `k ≤ V`.

### [T037] The terminal ray, on the slopes
- **Status**: done · **File**: `Slope.lean` · **Depends on**: T017 · **Type**: def + lemmas · **Leaves**: LR.1–LR.4
#### Statement
```lean
def EndsInRay (h : ℕ → WithTop ℝ) (m : ℝ) : Prop := ∃ N, ∀ j, N ≤ j → unitSlope h j = m
theorem EndsInRay.ne_top {m : ℝ} (hm : EndsInRay h m) : ∃ N, ∀ j, N ≤ j → h j ≠ ⊤
theorem IsConvexSeq.endsInRay_iff (hh : IsConvexSeq h) (m : ℝ) :
    EndsInRay h m ↔ (∀ j, h j ≠ ⊤ → unitSlope h j ≤ m) ∧ ∃ j, unitSlope h j = m
theorem EndsInRay.unitSlope_le (hh : IsConvexSeq h) {m : ℝ} (hm : EndsInRay h m) {j : ℕ} (hj : h j ≠ ⊤) :
    unitSlope h j ≤ m
theorem EndsInRay.setOf_lt_unitSlope_eq_empty (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤) {m : ℝ} (hm : EndsInRay h m) :
    {j | (m : WithTop ℝ) < unitSlope h j} = ∅
```
#### Proof sketch
1. `ne_top`: `N` from `hm`; `unitSlope h j = m` and `unitSlope_eq_top_iff` (T001) give `h j ≠ ⊤`
   (`WithTop.coe_ne_top`).
2. `endsInRay_iff` `→`: `N` from `hm`, `h N ≠ ⊤` by item 1; for `j` with `h j ≠ ⊤`: if `N ≤ j` the
   slope is `m`; else `hh.monotoneOn hj hN (le_of_lt h) : unitSlope h j ≤ unitSlope h N = m`. Witness
   `N`. `←`: `j₀` with slope `m`, so `h j₀ ≠ ⊤` and `h (j₀ + 1) ≠ ⊤`; `Nat.le_induction` from `j₀`:
   `h j ≠ ⊤ → h (j + 1) ≠ ⊤` since `unitSlope h j ≤ m < ⊤`; then `m = unitSlope h j₀ ≤ unitSlope h j ≤ m`
   by `hh.monotoneOn` and the bound. Witness `j₀`.
3. `unitSlope_le`: `((hh.endsInRay_iff m).1 hm).1 hj`.
4. `setOf_lt_unitSlope_eq_empty`: `Set.eq_empty_iff_forall_notMem`; for `j`, take a ray index `N' ≥ j`
   (`max N j`, finite by item 1), `hh.ordConnected.out h0 hN' ⟨Nat.zero_le _, le_max_right _ _⟩ : h j ≠ ⊤`,
   then item 3 and `not_lt`.
#### Mathlib lemmas needed
`WithTop.coe_ne_top`, `Nat.le_induction`, `Set.eq_empty_iff_forall_notMem`, `Set.OrdConnected.out`,
`not_lt`, `le_max_right`, `Nat.zero_le`.
#### Sources
[RM] §0.3.2, §0.5.4 (as amended 2026-09-12); decomposition revision 3, LR.1–LR.4.
#### Generality decision
`ℕ`, with the finiteness guard `h j ≠ ⊤` (the unguarded form is false for a polygon anchored past `0`).
#### Progress
- 2026-09-12: DONE. `EndsInRay`, `ne_top`, `IsConvexSeq.endsInRay_iff`, `unitSlope_le`,
  `setOf_lt_unitSlope_eq_empty` — exactly as decomposed in revision 3 (LR.1–LR.4), including the
  finiteness guard `h j ≠ ⊤` that attack [3] forced.

### [CLEANUP-7] Run /cleanup on `Slope.lean` (final)
- **Status**: done · **Depends on**: T037 · **Type**: cleanup — final per-file pass.

---
#### Progress
- 2026-09-12: inline cleanup pass on the finished file. `lake build` → `✔` no warnings;
  `runLinter` → "Linting passed"; lines ≤ 100 characters; one unused hypothesis removed
  (`newtonPolygon_truncate_eq`). `Set.mem_setOf_eq` is deprecated in this toolchain (→
  `Set.mem_ofPred_eq`); the file avoids it by using `show`/membership lemmas instead.

### [T018] Supporting lines and the competitor lemma
- **Status**: done · **File**: `Face.lean` · **Depends on**: CLEANUP-7 · **Type**: lemmas · **Leaves**: L5.1–L5.6
#### Statement
```lean
theorem IsNewtonPolygonOf.line_le (hh : IsNewtonPolygonOf v h) {y σ : ℝ}
    (hle : ∀ k : ℕ, ((y + σ * k : ℝ) : WithTop ℝ) ≤ v k) (k : ℕ) :
    ((y + σ * k : ℝ) : WithTop ℝ) ≤ h k
noncomputable def twoSlope (y σ τ : ℝ) (N : ℕ) : ℕ → WithTop ℝ :=
  fun k ↦ ((y + σ * min (k : ℝ) N + τ * ((k : ℝ) - min (k : ℝ) N) : ℝ) : WithTop ℝ)
theorem isConvexSeq_twoSlope (y : ℝ) {σ τ : ℝ} (hστ : σ ≤ τ) (N : ℕ) : IsConvexSeq (twoSlope y σ τ N)
theorem IsNewtonPolygonOf.twoSlope_le (hh : IsNewtonPolygonOf v h) (y : ℝ) {σ τ : ℝ} (hστ : σ ≤ τ)
    (N : ℕ) (hle : ∀ k, twoSlope y σ τ N k ≤ v k) (k : ℕ) : twoSlope y σ τ N k ≤ h k
theorem IsConvexSeq.line_le_iff (hh : IsConvexSeq h) {n : ℕ} (hn : h n ≠ ⊤) (σ : ℝ) :
    (∀ k : ℕ, (((h n).untop₀ + σ * ((k : ℝ) - n) : ℝ) : WithTop ℝ) ≤ h k) ↔
      (∀ j, j < n → h j ≠ ⊤ → unitSlope h j ≤ σ) ∧ ∀ j, n ≤ j → (σ : WithTop ℝ) ≤ unitSlope h j
theorem IsConvexSeq.line_lt_of_unitSlope_lt (hh : IsConvexSeq h) {n : ℕ} (hn : h n ≠ ⊤) {σ : ℝ}
    (h₁ : ∀ j, j < n → h j ≠ ⊤ → unitSlope h j < σ) {k : ℕ} (hk : k < n) (hkfin : h k ≠ ⊤) :
    (((h n).untop₀ + σ * ((k : ℝ) - n) : ℝ) : WithTop ℝ) < h k
theorem IsConvexSeq.line_lt_of_lt_unitSlope (hh : IsConvexSeq h) {n : ℕ} (hn : h n ≠ ⊤) {σ : ℝ}
    (h₂ : ∀ j, n ≤ j → (σ : WithTop ℝ) < unitSlope h j) {k : ℕ} (hk : n < k) :
    (((h n).untop₀ + σ * ((k : ℝ) - n) : ℝ) : WithTop ℝ) < h k
```
#### Proof sketch
1. `line_le`: `hh.greatest _ (isConvexSeq_affine y σ) hle k`.
2. `isConvexSeq_twoSlope`: `finiteSet = univ`; `unitSlope_of_ne_top`; for `j < N` the increment is
   `σ` (`min (j+1) N = j+1`), for `j ≥ N` it is `τ` (`min = N`); `monotone_nat_of_le_succ` with
   `hστ` at the junction; `ring_nf`/`push_cast` on the `min` arithmetic (`Nat.cast_min`).
3. `twoSlope_le`: `hh.greatest _ (isConvexSeq_twoSlope y hστ N) hle k`.
4. `line_le_iff`: `→`: at `k = n - 1` (if `0 < n` and `h (n-1) ≠ ⊤`): `h n - σ ≤ h (n-1)` gives
   `unitSlope h (n-1) ≤ σ`; monotonicity (`hh.monotoneOn`) spreads it to all finite `j < n`. At
   `k = n + 1`: `h n + σ ≤ h (n+1)` gives `σ ≤ unitSlope h n` (if `h (n+1) = ⊤` the slope is `⊤`),
   spread to `j ≥ n`. `←`: `k ≥ n`: `h k = h n + ∑_{[n,k)} s_j ≥ h n + (k-n) σ` (T001
   `eq_add_sum_unitSlope` with finiteness — or `le_top` if `h k = ⊤`); `k < n` with `h k ≠ ⊤`:
   `h n = h k + ∑_{[k,n)} s_j ≤ h k + (n-k) σ`; `k < n` with `h k = ⊤`: `le_top`.
5. The strict forms: the same sums with `Finset.sum_lt_sum_of_nonempty` (nonempty interval since
   `k < n`, resp. `n < k`); for `line_lt_of_lt_unitSlope` with `h k = ⊤`: `WithTop.coe_lt_top`.
#### Mathlib lemmas needed
`Nat.cast_min`, `monotone_nat_of_le_succ`, `Finset.sum_le_sum`, `Finset.sum_lt_sum_of_nonempty`,
`Finset.nonempty_Ico`, `WithTop.coe_lt_top`, `WithTop.coe_le_coe`, `WithTop.coe_lt_coe`.
#### Sources
[Ked07, §2] (`v_r` is the supporting-line intercept); [SRC] `Support.twoSlope_le_height`,
`Support.line_le_height`, `Face.line_le_height_of_unitSlope`, `line_lt_height_of_unitSlope_lt`,
`line_lt_height_of_lt_unitSlope`; decomposition L5.1–L5.6.
#### Generality decision
`line_le_iff` carries the guard `h j ≠ ⊤` on the left clause — necessary for anchors past `0`.
#### Progress
- 2026-09-12: DONE, first build. `line_le` and `twoSlope_le` are one-liners through `greatest`;
  `isConvexSeq_twoSlope` computes its unit slopes as `if j < N then σ else τ` through T040;
  `line_le_iff` and the two strict versions need only `add_nsmul_unitSlope_le` /
  `le_add_nsmul_unitSlope` (T003) — **no telescoping sums**: the chord bound out of `n` and into `n`
  already says what the averaging argument would.

### [T019] Unbounded slopes
- **Status**: done · **File**: `Face.lean` · **Depends on**: T018 · **Type**: lemmas · **Leaves**: L5.7–L5.10
#### Statement
```lean
theorem slopesUnbounded_of_finite (hfin : (slopeIndices h).Finite) : SlopesUnbounded h
theorem IsNewtonPolygonOf.slopesUnbounded_of_finite (hh : IsNewtonPolygonOf v h)
    (hfin : (finiteSet v).Finite) : SlopesUnbounded h
theorem IsNewtonPolygonOf.slopesUnbounded_of_forall_line (hh : IsNewtonPolygonOf v h)
    (hl : ∀ σ : ℝ, ∃ y : ℝ, ∀ k : ℕ, ((y + σ * k : ℝ) : WithTop ℝ) ≤ v k) : SlopesUnbounded h
theorem IsNewtonPolygonOf.slopesUnbounded_of_tendsto (hh : IsNewtonPolygonOf v h) (hfin : ∀ k, v k ≠ ⊤)
    (hl : Filter.Tendsto (fun k : ℕ ↦ (v k).untop₀ / k) Filter.atTop Filter.atTop) : SlopesUnbounded h
```
#### Proof sketch
1. `slopesUnbounded_of_finite`: `obtain ⟨j, hj⟩ := hfin.infinite_compl.nonempty`; `unitSlope h j = ⊤`
   so `σ < ⊤` (`WithTop.coe_lt_top`).
2. Spec version: T015 `slopeIndices_finite` then item 1.
3. `slopesUnbounded_of_forall_line`: `intro σ; by_contra hall; push_neg at hall` (`∀ j, unitSlope h j
   ≤ σ`); all unit slopes finite; `h k ≤ h a + (k - a) σ` for `k ≥ a := anchor` (T001 sum +
   `Finset.sum_le_sum`); `hl (σ + 1)` gives `y` with `y + (σ+1) k ≤ v k`, hence `≤ h k` (T018
   `line_le`); combine: `y + (σ+1) k ≤ h a + (k - a) σ` for all `k ≥ a`, false for `k` large
   (`linarith` after choosing `k > h a - y - aσ + 1`).
4. `slopesUnbounded_of_tendsto`: `intro σ`; from `hl`, `∃ N, ∀ k ≥ N, (σ + 1) ≤ v k / k`
   (`Filter.tendsto_atTop.1 hl (σ+1)`), so `(σ+1) k ≤ v k` for `k ≥ N` (`k > 0`); `y := min 0
   (Finset.inf' (range N) … (v k - (σ+1) k))`; then `y + (σ+1) k ≤ v k` for all `k`; apply item 3
   for this `σ` (only `σ` needs the line, so prove the `∃ y` for each `σ` inside).
#### Mathlib lemmas needed
`Set.Finite.infinite_compl`, `Set.Infinite.nonempty`, `Filter.tendsto_atTop`, `Finset.inf'_le`,
`div_le_iff`, `WithTop.coe_lt_top`.
#### Sources
[SRC] `Face.slopesUnbounded_of_forall_line` (quoted in decomposition L5.9); [RM] §0.5.4;
decomposition L5.7–L5.10.
#### Generality decision
Both growth criteria are stated on the points `v`, as the roadmap asks.
#### Progress
- 2026-09-12: DONE. `slopesUnbounded_of_finite` (a `⊤` slope exists outside a finite set:
  `Set.Finite.infinite_compl`), the polygon version, `slopesUnbounded_of_forall_line` (bounded slopes
  give `h N ≤ h 0 + N σ` by telescoping, contradicting the line of slope `σ + 1` for large `N`), and
  `slopesUnbounded_of_tendsto` (reduced to the previous one; the finitely many small indices are
  handled by `(Set.finite_Iio _).image _ |>.bddBelow`, the rest by `le_div_iff₀`).
- Inside `theorem IsNewtonPolygonOf.slopesUnbounded_of_finite` the bare name
  `slopesUnbounded_of_finite` resolves to the theorem being declared — qualify it as
  `NewtonPolygon.slopesUnbounded_of_finite`. `push Not` cannot see through the `SlopesUnbounded`
  definition: `simp only [SlopesUnbounded, not_forall, not_exists, not_lt]` first.

### [T020] Face endpoints: definition-level API
- **Status**: done · **File**: `Face.lean` · **Depends on**: T019 · **Type**: lemmas · **Leaves**: L5.11–L5.17, L5.20, L5.21
#### Statement
```lean
theorem le_unitSlope_faceLeft (hu : SlopesUnbounded h) (σ : ℝ) : (σ : WithTop ℝ) ≤ unitSlope h (faceLeft h σ)
theorem lt_unitSlope_faceRight (hu : SlopesUnbounded h) (σ : ℝ) : (σ : WithTop ℝ) < unitSlope h (faceRight h σ)
theorem slopesUnbounded_iff_forall_lt_unitSlope_faceRight :
    SlopesUnbounded h ↔ ∀ σ : ℝ, (σ : WithTop ℝ) < unitSlope h (faceRight h σ)
theorem unitSlope_lt_of_lt_faceLeft {σ : ℝ} {j : ℕ} (hj : j < faceLeft h σ) : unitSlope h j < σ
theorem unitSlope_le_of_lt_faceRight {σ : ℝ} {j : ℕ} (hj : j < faceRight h σ) : unitSlope h j ≤ σ
theorem IsConvexSeq.le_unitSlope_of_faceLeft_le (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤) (hu : SlopesUnbounded h)
    {σ : ℝ} {j : ℕ} (hj : faceLeft h σ ≤ j) : (σ : WithTop ℝ) ≤ unitSlope h j
theorem IsConvexSeq.lt_unitSlope_of_faceRight_le (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤) (hu : SlopesUnbounded h)
    {σ : ℝ} {j : ℕ} (hj : faceRight h σ ≤ j) : (σ : WithTop ℝ) < unitSlope h j
theorem faceLeft_le_faceRight (hu : SlopesUnbounded h) (σ : ℝ) : faceLeft h σ ≤ faceRight h σ
theorem faceRight_le_faceLeft_of_lt (hu : SlopesUnbounded h) {σ τ : ℝ} (hστ : σ < τ) : faceRight h σ ≤ faceLeft h τ
```
#### Proof sketch
1. Membership: `Nat.sInf_mem ⟨j, (hu σ).choose_spec.le⟩` (resp. `.lt`); the `↔`: `←` is a witness.
2. Below the endpoint: `Nat.not_mem_of_lt_sInf hj` and `not_le`/`not_lt` in the linear order
   `WithTop ℝ`.
3. From the endpoint on: first `faceLeft h σ ∈ finiteSet h` — every `j` with `h (j+1) = ⊤` has
   `unitSlope h j = ⊤ ≥ σ`, so `faceLeft h σ ≤` the last finite index (`Nat.sInf_le`), and `h 0 ≠
   ⊤` with order-connectedness makes every index up to the last one finite. Then for `j ≥ faceLeft`:
   if `h j ≠ ⊤`, `hh.monotoneOn` between them (both in `finiteSet h`); if `h j = ⊤`, `unitSlope h j
   = ⊤`. For the strict version the same with `<`.
4. `faceLeft_le_faceRight`: `Nat.sInf_le` applied to `Nat.sInf_mem` of the `<`-set (which lies in
   the `≤`-set). `faceRight_le_faceLeft_of_lt`: `{τ ≤ s} ⊆ {σ < s}`, so `sInf {σ < s} ≤ sInf {τ ≤ s}`
   via `Nat.sInf_le (Nat.sInf_mem …)` (nonempty by `hu τ`).
#### Mathlib lemmas needed
`Nat.sInf_mem`, `Nat.sInf_le`, `Nat.not_mem_of_lt_sInf`, `not_le`, `not_lt`, `le_top`, `WithTop.coe_lt_top`.
#### Sources
[Ked07, proof of Cor. 2] (the face endpoints as touching points of support lines of slightly
smaller/larger slope); [SRC] `Face.lean` §"The face of slope σ" (same lemma family, with `⊥`
hypotheses removed); decomposition L5.11–L5.17, L5.20–L5.21.
#### Generality decision
Anchor `0` (`h 0 ≠ ⊤`) wherever monotonicity from the endpoint is used; the definition-level lemmas
need no hypotheses.
#### Progress
- 2026-09-12: DONE, first build (14 declarations). All face-endpoint facts are `Nat.sInf_mem` /
  `Nat.sInf_le` / `Nat.notMem_of_lt_sInf` plus monotonicity; `faceLeft_eq_ncard` and
  `faceRight_eq_ncard` go through `{j | … } = Set.Iio (face…)` and `Finset.coe_range`.

### [CLEANUP-8] Run /cleanup on `Face.lean` (first pass)
- **Status**: done · **Depends on**: T020 · **Type**: cleanup — cadence rule.
#### Progress
- 2026-09-12: done as part of the single inline cleanup pass on `Face.lean` (see CLEANUP-9).

### [T021] Face geometry
- **Status**: done · **File**: `Face.lean` · **Depends on**: CLEANUP-8 · **Type**: lemmas · **Leaves**: L5.18, L5.19, L5.22–L5.26
#### Statement
```lean
theorem IsConvexSeq.faceLeft_eq_ncard (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤) (hu : SlopesUnbounded h) (σ : ℝ) :
    faceLeft h σ = Set.ncard {j | unitSlope h j < σ}
theorem IsConvexSeq.faceRight_eq_ncard (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤) (hu : SlopesUnbounded h) (σ : ℝ) :
    faceRight h σ = Set.ncard {j | unitSlope h j ≤ σ}
theorem IsConvexSeq.faceLeft_eq_faceRight_iff (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤) (hu : SlopesUnbounded h) (σ : ℝ) :
    faceLeft h σ = faceRight h σ ↔ ∀ j, unitSlope h j ≠ σ
theorem IsConvexSeq.eq_add_nsmul_of_mem_face (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤) (hu : SlopesUnbounded h)
    {σ : ℝ} {k : ℕ} (h1 : faceLeft h σ ≤ k) (h2 : k ≤ faceRight h σ) :
    h k = h (faceLeft h σ) + (k - faceLeft h σ : ℕ) • (σ : WithTop ℝ)
theorem IsConvexSeq.faceLeft_line_le (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤) (hu : SlopesUnbounded h) (σ : ℝ) (k : ℕ) :
    (((h (faceLeft h σ)).untop₀ + σ * ((k : ℝ) - faceLeft h σ) : ℝ) : WithTop ℝ) ≤ h k
theorem IsConvexSeq.faceLeft_line_lt (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤)
    {σ : ℝ} {k : ℕ} (hk : k < faceLeft h σ) :
    (((h (faceLeft h σ)).untop₀ + σ * ((k : ℝ) - faceLeft h σ) : ℝ) : WithTop ℝ) < h k
theorem IsConvexSeq.faceRight_line_lt (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤) (hu : SlopesUnbounded h)
    {σ : ℝ} {k : ℕ} (hk : faceRight h σ < k) :
    (((h (faceRight h σ)).untop₀ + σ * ((k : ℝ) - faceRight h σ) : ℝ) : WithTop ℝ) < h k
```
#### Proof sketch
1. `faceLeft_eq_ncard`: `{j | unitSlope h j < σ} = Set.Iio (faceLeft h σ)` by T020 (both
   inclusions); `Set.ncard_coe_finset` after `Set.Iio … = ↑(Finset.range _)` (`Finset.coe_range`),
   `Finset.card_range`. Same for `faceRight`.
2. `faceLeft_eq_faceRight_iff`: via T022's `faceRight_sub_faceLeft` — ⚠ dependency inversion: T022
   depends on this ticket. Prove directly instead: `←`: the `≤`-set equals the `<`-set when no slope
   equals `σ`, so the `sInf`s agree. `→`: if `unitSlope h j = σ` then `faceLeft ≤ j < faceRight`
   (`Nat.sInf_le` and T020 `unitSlope_le_of_lt_faceRight` contrapositive), contradiction.
3. `eq_add_nsmul_of_mem_face`: on `[faceLeft, faceRight)` the unit slopes are `≥ σ` (T020
   `le_unitSlope_of_faceLeft_le`) and `≤ σ` (`unitSlope_le_of_lt_faceRight`), so `= σ`;
   `eq_add_nsmul_of_forall_unitSlope_eq` (T001) with `h (faceLeft) ≠ ⊤` (T020 item 3).
4. `faceLeft_line_le`: T018 `line_le_iff` `←` at `n = faceLeft`: left slopes `< σ` hence `≤ σ`
   (T020), right slopes `≥ σ` (T020). `faceLeft_line_lt`: T018 `line_lt_of_unitSlope_lt` at `n =
   faceLeft` with `h k ≠ ⊤` for `k < faceLeft` (anchor `0`, finiteness interval). `faceRight_line_lt`:
   T018 `line_lt_of_lt_unitSlope` at `n = faceRight` (slopes from `faceRight` on are `> σ`, T020).
#### Mathlib lemmas needed
`Set.ncard_coe_finset`, `Finset.coe_range`, `Finset.card_range`, `Nat.sInf_le`, `Set.ext`.
#### Sources
[Ked07, proof of Cor. 2]; [SRC] `Face.height_eq_of_mem_face`, `faceLeft_line_le_height`,
`faceLeft_line_lt_height`, `faceRight_line_lt_height`; decomposition L5.18–L5.19, L5.22–L5.26.
#### Generality decision
As T020; the `ncard` forms are the bridge to the roadmap's "number of unit slopes" wording.
#### Progress
- 2026-09-12: DONE. `eq_add_nsmul_of_mem_face`, `faceLeft_line_le`, `faceLeft_line_lt`,
  `faceRight_line_lt`, and two API additions the line lemmas need: `ne_top_faceLeft`,
  `ne_top_faceRight` (a face endpoint is a finite index — the unit slope just before it is finite).
- Statement change: `hu` dropped from `faceLeft_line_lt` (unused; the slope bound to the left of the
  face comes from `unitSlope_lt_of_lt_faceLeft`, which needs no unboundedness).

### [T022] Multiplicity, right-continuity, and the endpoints are points
- **Status**: done · **File**: `Face.lean` · **Depends on**: T021 · **Type**: lemmas · **Leaves**: L5.27–L5.31
#### Statement
```lean
theorem IsConvexSeq.faceRight_sub_faceLeft (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤) (hu : SlopesUnbounded h) (σ : ℝ) :
    faceRight h σ - faceLeft h σ = Set.ncard {j | unitSlope h j = σ}
theorem IsConvexSeq.count_slopeMultiset_eq (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤) (hfin : (slopeIndices h).Finite)
    (σ : ℝ) : (slopeMultiset h).count σ = faceRight h σ - faceLeft h σ
theorem exists_faceRight_eq (hu : SlopesUnbounded h) (σ : ℝ) :
    ∃ δ > 0, ∀ τ, σ ≤ τ → τ < σ + δ → faceRight h τ = faceRight h σ
theorem IsNewtonPolygonOf.eq_of_faceLeft (hh : IsNewtonPolygonOf v h) (h0 : v 0 ≠ ⊤) (hu : SlopesUnbounded h)
    (σ : ℝ) : h (faceLeft h σ) = v (faceLeft h σ)
theorem IsNewtonPolygonOf.eq_of_faceRight (hh : IsNewtonPolygonOf v h) (h0 : v 0 ≠ ⊤) (hu : SlopesUnbounded h)
    (σ : ℝ) : h (faceRight h σ) = v (faceRight h σ)
```
#### Proof sketch
1. `faceRight_sub_faceLeft`: `{j | unitSlope h j = σ} = Set.Ico (faceLeft h σ) (faceRight h σ)`
   (T020 both ways); `Set.ncard_coe_finset` with `Finset.coe_Ico`, `Nat.card_Ico`.
2. `count_slopeMultiset_eq`: T015 `count_slopeMultiset` then item 1 with `hu := slopesUnbounded_of_finite hfin`.
3. `exists_faceRight_eq`: let `s := unitSlope h (faceRight h σ)`, `σ < s` (T020). If `s = ⊤`: `δ :=
   1`; for `τ ∈ [σ, σ+1)`, `{τ < ·}` and `{σ < ·}` agree: a slope `> σ` is either `⊤` or `≥ s = ⊤`
   — i.e. all slopes `> σ` are `⊤`, hence `> τ` too, and slopes `≤ σ` are `≤ τ`. Else `δ := untop₀ s
   - σ > 0`; for `σ ≤ τ < σ + δ = untop₀ s`: a slope `> σ` is `≥ s > τ` (T020 `lt_unitSlope_of_
   faceRight_le` + monotonicity), a slope `≤ σ` is `≤ τ`; so the sets coincide and the `sInf`s agree.
4. `eq_of_faceLeft`: `h 0 ≠ ⊤` from `h0` via `hh.anchor_eq 0 (by simp) h0`; `IsVertex h (faceLeft
   h σ)`: if `faceLeft = 0` it is the anchor (`anchor h = 0`, T013); else `unitSlope h (faceLeft - 1)
   < σ ≤ unitSlope h faceLeft` (T020); then T014 `eq_of_isVertex`. `eq_of_faceRight`: `unitSlope h
   (faceRight - 1) ≤ σ < unitSlope h faceRight`, same.
#### Mathlib lemmas needed
`Finset.coe_Ico`, `Nat.card_Ico`, `Set.ncard_coe_finset`, `sub_pos`, `WithTop.coe_untop₀_of_ne_top`.
#### Sources
[Ked07, Cor. 2] ("the multiplicity of `r` as a slope"); [SRC] `Face.height_faceLeft_eq_pointHeight`,
`height_faceRight_eq_pointHeight`; decomposition L5.27–L5.31.
#### Generality decision
The multiplicity statement is in `ncard` form (valid for infinitely many slopes); the multiset form
is the corollary with `hfin`.
#### Progress
- 2026-09-12: DONE. `faceRight_sub_faceLeft` ({j | slope = σ} = `Set.Ico (faceLeft) (faceRight)`),
  `count_slopeMultiset_eq`, `exists_faceRight_eq`, `eq_of_faceLeft`, `eq_of_faceRight`.
- Statement change: `exists_faceRight_eq` lost `hh` and `h0` (unused — right-continuity is a fact
  about the two `sInf`s alone) and with them the `IsConvexSeq.` namespace prefix.
- The face endpoints are *vertices*: the slope strictly increases across each (at `faceLeft`: `< σ`
  before, `≥ σ` after; at `faceRight`: `≤ σ` before, `> σ` after), so `eq_of_isVertex` (T014) gives
  that they are points of the sequence.

### [T038] The terminal ray and unbounded slopes: the trichotomy
- **Status**: done · **File**: `Face.lean` · **Depends on**: T022, T037 · **Type**: lemmas · **Leaves**: LR.5–LR.7
#### Statement
```lean
theorem EndsInRay.not_slopesUnbounded (hh : IsConvexSeq h) (h0 : h 0 ≠ ⊤) {m : ℝ} (hm : EndsInRay h m) :
    ¬ SlopesUnbounded h
theorem EndsInRay.le_unitSlope_faceLeft {m : ℝ} (hm : EndsInRay h m) : (m : WithTop ℝ) ≤ unitSlope h (faceLeft h m)
theorem IsConvexSeq.slopesUnbounded_or_endsInRay_or_tendsto (hh : IsConvexSeq h) :
    SlopesUnbounded h ∨ (∃ m, EndsInRay h m) ∨
      ∃ m : ℝ, (∀ j, unitSlope h j < m) ∧ Filter.Tendsto (fun j ↦ (unitSlope h j).untop₀) Filter.atTop (nhds m)
```
#### Proof sketch
1. `not_slopesUnbounded`: `intro hu; obtain ⟨j, hj⟩ := hu m`; `hm.setOf_lt_unitSlope_eq_empty hh h0`
   (T037) says the set is empty; `Set.eq_empty_iff_forall_notMem` at `j`.
2. `le_unitSlope_faceLeft`: the set `{j | (m : WithTop ℝ) ≤ unitSlope h j}` contains `N` (from `hm`,
   `le_of_eq`), so `Nat.sInf_mem ⟨N, _⟩` gives the bound at `faceLeft h m`.
3. `slopesUnbounded_or_endsInRay_or_tendsto`: `by_cases hu : SlopesUnbounded h`; `left`. Otherwise
   `push_neg at hu : ∃ σ, ∀ j, unitSlope h j ≤ σ`; every `h j ≠ ⊤` (a `⊤` value gives slope `⊤ > σ` via
   `unitSlope_eq_top_iff`; note `h 0 ≠ ⊤` starts it and the bound propagates as in T037.2); real slopes
   `s j := (unitSlope h j).untop₀` monotone (`hh.monotoneOn` on `Set.univ`, `WithTop.coe_le_coe` after
   `unitSlope_of_ne_top`) and bounded by `σ`; `m := ⨆ j, s j`; `tendsto_atTop_ciSup` (or
   `IsConvexSeq.tendsto_unitSlope`, T007). `by_cases hex : ∃ j, s j = m`: `right; left; exact ⟨m,
   (hh.endsInRay_iff m).2 ⟨fun j _ ↦ by simpa using le_ciSup hb j, hex⟩⟩`; else `right; right;
   exact ⟨m, fun j ↦ lt_of_le_of_ne (le_ciSup hb j) (fun h ↦ hex ⟨j, h⟩), htend⟩` (in `WithTop` via
   `WithTop.coe_lt_coe`).
#### Mathlib lemmas needed
`Nat.sInf_mem`, `le_ciSup`, `ciSup_le`, `tendsto_atTop_ciSup`, `WithTop.coe_lt_coe`, `WithTop.coe_le_coe`,
`lt_of_le_of_ne`, `Set.eq_empty_iff_forall_notMem`, `not_forall`, `not_exists`, `push_neg`.
#### Sources
[RM] §0.5.4 (as amended 2026-09-12); [Kob84, §IV.4] (the three convergence behaviours: entire, finite
radius with or without a boundary face); decomposition revision 3, LR.5–LR.7.
#### Generality decision
`ℕ`, anchored at `0` (`h0`), as every face statement; `SlopesUnbounded` is trivial for a sequence with a
`⊤` value (decomposition LR.5 design note), so `h0` is not removable.
#### Progress
- 2026-09-12: DONE. `EndsInRay.not_slopesUnbounded`, `EndsInRay.le_unitSlope_faceLeft`,
  `IsConvexSeq.slopesUnbounded_or_endsInRay_or_tendsto`.
- Statement change: the trichotomy lost `h0` — bounded slopes already force every value finite
  (a `⊤` value gives a `⊤` slope), so the anchoring hypothesis is unnecessary.

### [CLEANUP-9] Run /cleanup on `Face.lean` (final)
- **Status**: done · **Depends on**: T038 · **Type**: cleanup — final per-file pass.

---
#### Progress
- 2026-09-12: inline cleanup pass on the finished file. `lake build` → `✔` no warnings;
  `runLinter` → "Linting passed"; lines ≤ 100 characters; three unused hypotheses removed
  (`faceLeft_line_lt`'s `hu`, `exists_faceRight_eq`'s `hh`/`h0`, the trichotomy's `h0`) and four
  unused binders renamed to `_`.

### [T023] The Minkowski sum: basic API
- **Status**: done · **File**: `Minkowski.lean` · **Depends on**: CLEANUP-9 · **Type**: lemmas · **Leaves**: L6.1–L6.6
#### Statement
```lean
theorem minkowski_le {n i : ℕ} (hi : i ≤ n) : minkowski h₁ h₂ n ≤ h₁ i + h₂ (n - i)
theorem le_minkowski_iff {n : ℕ} {a : WithTop ℝ} : a ≤ minkowski h₁ h₂ n ↔ ∀ i, i ≤ n → a ≤ h₁ i + h₂ (n - i)
theorem exists_minkowski_eq (n : ℕ) : ∃ i, i ≤ n ∧ minkowski h₁ h₂ n = h₁ i + h₂ (n - i)
theorem minkowski_comm (n : ℕ) : minkowski h₁ h₂ n = minkowski h₂ h₁ n
theorem minkowski_assoc (n : ℕ) : minkowski (minkowski h₁ h₂) h₃ n = minkowski h₁ (minkowski h₂ h₃) n
@[simp] theorem minkowski_zero : minkowski h₁ h₂ 0 = h₁ 0 + h₂ 0
```
#### Proof sketch
1. `Finset.inf_le (Finset.mem_range.2 (Nat.lt_succ_of_le hi))`; `Finset.le_inf_iff` with
   `Finset.mem_range` and `Nat.lt_succ_iff`; `Finset.exists_mem_eq_inf _ Finset.nonempty_range_succ _`.
2. `minkowski_comm`: `unfold minkowski`; `(Finset.range (n+1)).inf f = ((Finset.range (n+1)).image
   (n - ·)).inf f` because the image is the range itself (`Finset.ext`, `Finset.mem_image`,
   `Nat.sub_sub_self`), then `Finset.inf_image` and `add_comm` with `n - (n - i) = i`.
3. `minkowski_assoc`: `le_antisymm`, each by `le_minkowski_iff` twice: a split `(i, j, k)` of `n` on
   one side is a split on the other, `add_assoc`, `Nat.sub_sub`, `Nat.add_sub_cancel`.
4. `minkowski_zero`: `Finset.range_one`, `Finset.inf_singleton`, `Nat.sub_zero`.
#### Mathlib lemmas needed
`Finset.inf_le`, `Finset.le_inf_iff`, `Finset.exists_mem_eq_inf`, `Finset.nonempty_range_succ`,
`Finset.inf_image`, `Finset.mem_image`, `Nat.sub_sub_self`, `Finset.range_one`, `Finset.inf_singleton`.
#### Sources
[Ked07, §2] inequality (1) (the min over `i + j = k`); [SRC] `Product.minkowskiHeight_le`,
`le_minkowskiHeight_iff`, `exists_minkowskiHeight_eq`, `minkowskiHeight_comm`, `minkowskiHeight_zero`;
decomposition L6.1–L6.6.
#### Generality decision
No hypotheses: pure `Finset.inf` bookkeeping on arbitrary `h₁ h₂`.
#### Progress
- 2026-09-12: DONE. `minkowski_le`, `le_minkowski_iff`, `exists_minkowski_eq`, `minkowski_comm`,
  `minkowski_assoc`, `minkowski_zero`, `isConvexSeq_minkowski`.
- The min-convolution is convex by the **midpoint criterion**, via a new ConvexSeq lemma added for
  it: `IsConvexSeq.succ_add_pred_le` (the *sliding inequality* `h (p+1) + h (q-1) ≤ h p + h q` for
  `p < q`). With optimal splits `a` at `n` and `b` at `n + 2`, one slides in `h₁` when `a < b` and in
  `h₂` when `b ≤ a` (the `h₂` indices then satisfy `n - a < n + 2 - b`); `add_add_add_comm` does the
  regrouping. Order-connectedness of the finiteness set is downward closure of `minkowski` (take the
  split `(min q b, b - min q b)`).

### [T024] Subgradients, convexity and unbounded slopes of the Minkowski sum
- **Status**: done · **File**: `Minkowski.lean` · **Depends on**: T023 · **Type**: lemmas · **Leaves**: L6.7–L6.10
#### Statement
```lean
theorem exists_subgradient (hh₁ : IsConvexSeq h₁) (hh₂ : IsConvexSeq h₂) (h0₁ : h₁ 0 ≠ ⊤) (h0₂ : h₂ 0 ≠ ⊤)
    {n i₀ : ℕ} (hi₀ : i₀ ≤ n) (hfin : minkowski h₁ h₂ n ≠ ⊤) (heq : minkowski h₁ h₂ n = h₁ i₀ + h₂ (n - i₀)) :
    ∃ σ : ℝ, (∀ t, t < i₀ → unitSlope h₁ t ≤ σ) ∧ (∀ t, i₀ ≤ t → (σ : WithTop ℝ) ≤ unitSlope h₁ t) ∧
      (∀ t, t < n - i₀ → unitSlope h₂ t ≤ σ) ∧ ∀ t, n - i₀ ≤ t → (σ : WithTop ℝ) ≤ unitSlope h₂ t
theorem subgradient_line_le_minkowski (hh₁ : IsConvexSeq h₁) (hh₂ : IsConvexSeq h₂) (h0₁ : h₁ 0 ≠ ⊤) (h0₂ : h₂ 0 ≠ ⊤)
    {i₀ j₀ : ℕ} {σ : ℝ} (hP₁ : ∀ t, t < i₀ → unitSlope h₁ t ≤ σ) (hP₂ : ∀ t, i₀ ≤ t → (σ : WithTop ℝ) ≤ unitSlope h₁ t)
    (hQ₁ : ∀ t, t < j₀ → unitSlope h₂ t ≤ σ) (hQ₂ : ∀ t, j₀ ≤ t → (σ : WithTop ℝ) ≤ unitSlope h₂ t)
    {y : ℝ} (hy : h₁ i₀ + h₂ j₀ = (y : WithTop ℝ)) (m : ℕ) :
    ((y + σ * ((m : ℝ) - (i₀ + j₀ : ℕ)) : ℝ) : WithTop ℝ) ≤ minkowski h₁ h₂ m
theorem isConvexSeq_minkowski (hh₁ : IsConvexSeq h₁) (hh₂ : IsConvexSeq h₂) (h0₁ : h₁ 0 ≠ ⊤) (h0₂ : h₂ 0 ≠ ⊤) :
    IsConvexSeq (minkowski h₁ h₂)
theorem slopesUnbounded_minkowski (hh₁ : IsConvexSeq h₁) (hh₂ : IsConvexSeq h₂) (h0₁ : h₁ 0 ≠ ⊤) (h0₂ : h₂ 0 ≠ ⊤)
    (hu₁ : SlopesUnbounded h₁) (hu₂ : SlopesUnbounded h₂) : SlopesUnbounded (minkowski h₁ h₂)
```
#### Proof sketch
1. `exists_subgradient` (the neighbour comparison): `j₀ := n - i₀`; from `heq` and `minkowski_le` at
   the splits `(i₀+1, j₀-1)` (if `j₀ > 0`) and `(i₀-1, j₀+1)` (if `i₀ > 0`): `h₁ i₀ + h₂ j₀ ≤ h₁
   (i₀+1) + h₂ (j₀-1)` ⇒ `s₂ (j₀-1) ≤ s₁ i₀` (untop arithmetic; all four values finite since the
   minimum is finite and each factor is finite on `[0, last]`); similarly `s₁ (i₀-1) ≤ s₂ j₀`. Let
   `σ := max (untop₀ (s₁ (i₀-1)) if i₀ > 0 else -∞-substitute) (untop₀ (s₂ (j₀-1)) if j₀ > 0)` —
   concretely: case split on `i₀ = 0`, `j₀ = 0`; in the generic case `σ := max (untop₀ (s₁ (i₀-1)))
   (untop₀ (s₂ (j₀-1)))`; then `σ ≤ s₁ i₀` and `σ ≤ s₂ j₀` (the two cross-inequalities plus the two
   factors' own monotonicity), and monotonicity propagates to all `t`. In the corner `i₀ = j₀ = 0`
   take `σ := min (untop₀ (s₁ 0)) (untop₀ (s₂ 0))` (or `0` if both `⊤`).
2. `subgradient_line_le_minkowski`: `le_minkowski_iff`; for a split `(i, m - i)`: T018 `line_le_iff`
   `←` for `h₁` at `i₀` and for `h₂` at `j₀` give `h₁ i ≥ h₁ i₀ + σ (i - i₀)`, `h₂ (m-i) ≥ h₂ j₀ +
   σ (m - i - j₀)`; add (`add_le_add`), `WithTop.coe_add`, `ring_nf`.
3. `isConvexSeq_minkowski`: order-connected: `minkowski h₁ h₂ n ≠ ⊤ ↔ n ≤ last₁ + last₂` (a split
   of `n` into finite indices exists iff `n ≤ last₁ + last₂`, using that both factors are finite
   exactly on `[0, lastᵢ]` by `h0ᵢ` + order-connectedness), an interval. Monotone unit slopes: at
   each `n` with `M n`, `M (n+1)` finite, take the minimiser `(i₀, n - i₀)` (T023) and its
   subgradient `σ` (item 1); item 2 gives the supporting line at `n`, and T018 `line_le_iff` `→`
   (its `→` half uses only the line inequality, not convexity of `M` — the worker may extract that
   half as a private lemma) yields `unitSlope M (n-1) ≤ σ ≤ unitSlope M n`.
4. `slopesUnbounded_minkowski`: `intro σ`; pick `N₁` with `σ < s₁ N₁` and `N₂` with `σ < s₂ N₂`
   (`hu₁ σ`, `hu₂ σ`); take `n := N₁ + N₂ + 2`; if `M n = ⊤`, `unitSlope M (n-1)` or `M (n-1) = ⊤`…
   — simplest: if `M (n) = ⊤` for some `n` then `unitSlope M (n-1) = ⊤ > σ` (pick the least such
   `n`, `n ≥ 1`); else `M` finite everywhere, the minimiser `(i₀, n - i₀)` of `n := N₁ + N₂ + 2` has
   `i₀ ≥ N₁ + 1` or `n - i₀ ≥ N₂ + 1`, and its subgradient `σ_n ≥ s₁ (i₀ - 1) ≥ s₁ N₁ > σ` or
   `≥ s₂ (n - i₀ - 1) > σ`; `unitSlope M n ≥ σ_n` by item 3's argument.
#### Mathlib lemmas needed
`add_le_add`, `WithTop.coe_add`, `WithTop.coe_le_coe`, `le_max_left`, `le_max_right`, `max_le`,
`WithTop.add_eq_top`, `Set.ordConnected_Iic`/`Set.ordConnected_Icc`.
#### Sources
[Ked07, proof of Prop. 1] ("let `i₀` and `j₀` be the smallest values … which minimize"); [SRC]
`Product.exists_subgradient` ("compare the split with its two neighbours"),
`subgradient_line_le_minkowskiHeight`; decomposition L6.7–L6.10.
#### Generality decision
`exists_subgradient` does not assume the Minkowski sum convex — that is what lets
`isConvexSeq_minkowski` be proved from it.
#### Progress
- 2026-09-12: DONE. `exists_subgradient`, `subgradient_line_le_minkowski`,
  `slopesUnbounded_minkowski`; `IsConvexSeq.faceRight_line_le` added to `Face.lean` (the companion of
  `faceLeft_line_le`, needed here).
- `exists_subgradient` splits on whether `min (unitSlope h₁ i₀) (unitSlope h₂ (n - i₀))` is `⊤`:
  when finite that minimum *is* the subgradient (minimality of the split gives
  `unitSlope h₁ (i₀-1) ≤ unitSlope h₂ (n-i₀)` and symmetrically, so the left slopes are below it);
  when `⊤` both polygons stop at the split, every later slope is `⊤`, and the max of the two left
  slopes works — with `untop₀ ⊤ = 0` making the `i₀ = 0` case fall out.
- Statement change: `h0₁`, `h0₂` dropped from `subgradient_line_le_minkowski` (unused — the
  separation hypotheses already pin the lines).

### [T025] Faces of the Minkowski sum: the endpoints add, the minimiser is unique
- **Status**: done · **File**: `Minkowski.lean` · **Depends on**: T024 · **Type**: lemmas · **Leaves**: L6.11–L6.14
#### Statement
```lean
theorem minkowski_faceLeft_add (hh₁ : IsConvexSeq h₁) (hh₂ : IsConvexSeq h₂) (h0₁ : h₁ 0 ≠ ⊤)
    (h0₂ : h₂ 0 ≠ ⊤) (hu₁ : SlopesUnbounded h₁) (hu₂ : SlopesUnbounded h₂) (σ : ℝ) :
    minkowski h₁ h₂ (faceLeft h₁ σ + faceLeft h₂ σ) = h₁ (faceLeft h₁ σ) + h₂ (faceLeft h₂ σ)
theorem lt_of_ne_faceLeft (hh₁ : IsConvexSeq h₁) (hh₂ : IsConvexSeq h₂) (h0₁ : h₁ 0 ≠ ⊤)
    (h0₂ : h₂ 0 ≠ ⊤) (hu₁ : SlopesUnbounded h₁) (hu₂ : SlopesUnbounded h₂) {σ : ℝ} {i j : ℕ}
    (hij : i + j = faceLeft h₁ σ + faceLeft h₂ σ) (hne : i ≠ faceLeft h₁ σ) :
    h₁ (faceLeft h₁ σ) + h₂ (faceLeft h₂ σ) < h₁ i + h₂ j
theorem minkowski_faceRight_add (hh₁ : IsConvexSeq h₁) (hh₂ : IsConvexSeq h₂) (h0₁ : h₁ 0 ≠ ⊤)
    (h0₂ : h₂ 0 ≠ ⊤) (hu₁ : SlopesUnbounded h₁) (hu₂ : SlopesUnbounded h₂) (σ : ℝ) :
    minkowski h₁ h₂ (faceRight h₁ σ + faceRight h₂ σ) = h₁ (faceRight h₁ σ) + h₂ (faceRight h₂ σ)
theorem lt_of_ne_faceRight (hh₁ : IsConvexSeq h₁) (hh₂ : IsConvexSeq h₂) (h0₁ : h₁ 0 ≠ ⊤)
    (h0₂ : h₂ 0 ≠ ⊤) (hu₁ : SlopesUnbounded h₁) (hu₂ : SlopesUnbounded h₂) {σ : ℝ} {i j : ℕ}
    (hij : i + j = faceRight h₁ σ + faceRight h₂ σ) (hne : i ≠ faceRight h₁ σ) :
    h₁ (faceRight h₁ σ) + h₂ (faceRight h₂ σ) < h₁ i + h₂ j
```
#### Proof sketch
1. `minkowski_faceLeft_add`: `le_antisymm (minkowski_le (Nat.le_add_right _ _))` and, for `≥`,
   T024 `subgradient_line_le_minkowski` at `i₀ := faceLeft h₁ σ`, `j₀ := faceLeft h₂ σ` (the four
   slope conditions are T020 `unitSlope_lt_of_lt_faceLeft`.le and `le_unitSlope_of_faceLeft_le`),
   evaluated at `m = i₀ + j₀` where the line's value is `y` (`sub_self`, `mul_zero`).
2. `lt_of_ne_faceLeft`: `rcases hne.lt_or_lt with hlt | hlt`. If `i < fL₁`: T021
   `faceLeft_line_lt` for `h₁` at `i` (strict) and `faceLeft_line_le` for `h₂` at `j` (non-strict);
   add (`add_lt_add_of_lt_of_le`), and the two line values sum to `h₁ fL₁ + h₂ fL₂` since `(i - fL₁)
   + (j - fL₂) = 0` (from `hij`). If `i > fL₁` then `j < fL₂`: symmetric.
3. `faceRight` versions: the same with `faceRight_line_lt` (strict right of the face) and the
   non-strict bound left of `faceRight` from `line_le_iff` (slopes `≤ σ` before `faceRight`).
#### Mathlib lemmas needed
`add_lt_add_of_lt_of_le`, `add_lt_add_of_le_of_lt`, `Nat.le_add_right`, `WithTop.coe_add`, `lt_or_lt`.
#### Sources
[Ked07, proof of Prop. 1] verbatim in decomposition §0.6 ("then (1) achieves its minimum for … but
not for any other"); [SRC] `Product.minkowskiHeight_faceLeft`, `height_faceLeft_add_lt`;
decomposition L6.11–L6.14.
#### Generality decision
Both endpoints treated; the `faceLeft` statements are Kedlaya's, the `faceRight` ones their mirror.
#### Progress
- 2026-09-12: DONE. `lt_of_ne_faceLeft`, `lt_of_ne_faceRight`, `minkowski_faceLeft_add`,
  `minkowski_faceRight_add` (the uniqueness lemmas had to be *declared first*, the board's order was
  the reverse).
- Each uniqueness proof is the strict supporting-line bound on one factor plus the non-strict one on
  the other; `linarith` needs the σ-scaled cancellation `σ*(i - F₁) + σ*(j - F₂) = 0` handed to it
  explicitly (it cannot multiply the index identity by `σ` itself).

### [CLEANUP-10] Run /cleanup on `Minkowski.lean` (first pass)
- **Status**: done · **Depends on**: T025 · **Type**: cleanup — cadence rule.
#### Progress
- 2026-09-12: done as part of the single inline cleanup pass on `Minkowski.lean` (see CLEANUP-11).

### [CLEANUP-ALL-1] Run /cleanup-all on the project so far (pre-milestone)
- **Status**: done · **Depends on**: CLEANUP-10, CLEANUP-7 · **Type**: cleanup-all — before the §0.6 milestone.
#### Progress
- 2026-09-12: done inline, across the whole Layer 0 development, before the §0.6 milestone:
  `lake build` of the full chain → `✔`; `runLinter` on every finished module → "Linting passed";
  `#print axioms` on the headline declarations of each file → standard axioms only; no line over 100
  characters anywhere in `PhD/TauCeti/Code/NewtonPolygons/`.

### [T026] Faces and slope multisets add — MILESTONE (§0.6)
- **Status**: done · **File**: `Minkowski.lean` · **Depends on**: CLEANUP-ALL-1 · **Type**: theorems · **Leaves**: L6.15–L6.17
#### Statement
```lean
theorem faceLeft_minkowski (hh₁ : IsConvexSeq h₁) (hh₂ : IsConvexSeq h₂) (h0₁ : h₁ 0 ≠ ⊤)
    (h0₂ : h₂ 0 ≠ ⊤) (hu₁ : SlopesUnbounded h₁) (hu₂ : SlopesUnbounded h₂) (σ : ℝ) :
    faceLeft (minkowski h₁ h₂) σ = faceLeft h₁ σ + faceLeft h₂ σ
theorem faceRight_minkowski (hh₁ : IsConvexSeq h₁) (hh₂ : IsConvexSeq h₂) (h0₁ : h₁ 0 ≠ ⊤)
    (h0₂ : h₂ 0 ≠ ⊤) (hu₁ : SlopesUnbounded h₁) (hu₂ : SlopesUnbounded h₂) (σ : ℝ) :
    faceRight (minkowski h₁ h₂) σ = faceRight h₁ σ + faceRight h₂ σ
theorem slopeMultiset_minkowski (hh₁ : IsConvexSeq h₁) (hh₂ : IsConvexSeq h₂) (h0₁ : h₁ 0 ≠ ⊤) (h0₂ : h₂ 0 ≠ ⊤)
    (hfin₁ : (slopeIndices h₁).Finite) (hfin₂ : (slopeIndices h₂).Finite) :
    slopeMultiset (minkowski h₁ h₂) = slopeMultiset h₁ + slopeMultiset h₂
```
#### Proof sketch
1. `faceLeft_minkowski`: `N := fL₁ + fL₂`, `M := minkowski h₁ h₂` (convex by T024, unbounded slopes
   by T024). Show `unitSlope M (N-1) < σ` (if `N > 0`): `M (N-1)` is attained by a split `(i, j)`
   with `i + j = N - 1`, so `i < fL₁` or `j < fL₂`; T025's strict inequality (applied to the split
   `(i, j+1)` or `(i+1, j)` of `N` — or directly: the strict line bounds) gives `M (N-1) > M N - σ`,
   i.e. `unitSlope M (N-1) < σ`. Show `σ ≤ unitSlope M N`: T024 `subgradient_line_le_minkowski` at
   `(fL₁, fL₂)` gives the supporting line of slope `σ` through `(N, M N)` (T025 item 1 for the
   value), and T018 `line_le_iff` `→` gives `σ ≤ unitSlope M N`. Then `faceLeft M σ = N` by
   `Nat.sInf` characterisation: `N ∈ {σ ≤ s}` and every `j < N` has `unitSlope M j ≤ unitSlope M (N-1)
   < σ` (monotone). `N = 0`: `faceLeft M σ = 0` since `σ ≤ unitSlope M 0` and `0` is least.
2. `faceRight_minkowski`: mirror with `N' := fR₁ + fR₂`: `unitSlope M N' > σ` via the strict
   inequality at splits of `N' + 1`, and `unitSlope M (N'-1) ≤ σ` via the line through `(N', M N')`.
3. `slopeMultiset_minkowski`: `Multiset.ext.2 fun σ ↦ ?_`; `Multiset.count_add`; T022
   `count_slopeMultiset_eq` for `M` (needs `slopeIndices M` finite: `M = ⊤` past `last₁ + last₂`,
   T024's finiteness-interval fact) and for each factor (`hu` from `hfin` via T019); then items 1–2
   and `Nat.add_sub_add_*` with `fL ≤ fR` (T020) for the subtraction.
#### Mathlib lemmas needed
`Multiset.ext`, `Multiset.count_add`, `Nat.sInf` lemmas as in T020, `tsub_add_tsub_comm`/`omega`.
#### Sources
[Ked07, Cor. 2] verbatim: "the multiplicity of `r` as a slope of `PQ` is the sum of the
multiplicities of `r` as a slope of `P` and `Q`"; [Ked07, §1] the slope multiset; [SRC]
`Product.faceRight_mul`; decomposition L6.15–L6.17.
#### Generality decision
The multiset statement needs finitely many slopes on both sides (the multiset is junk otherwise);
the face statements hold for unbounded slopes in general.
#### Progress
- 2026-09-12: DONE (milestone §0.6). `faceLeft_minkowski`, `faceRight_minkowski`,
  `slopeMultiset_minkowski`.
- Both face identities have the same shape: the subgradient line through the sum of the two endpoints
  is below the Minkowski sum and **strictly** below it past the face (one factor is strictly above
  its own line there), which pins the slope at the sum of the endpoints and rules out any earlier
  (resp. later) index. The strictness is what makes the `sInf` land exactly on `F₁ + F₂`.
- `slopeMultiset_minkowski` is then counting: `count σ = faceRight σ - faceLeft σ` (T022) on all
  three polygons, plus `Multiset.count_add` and `omega`. The finiteness of `slopeIndices (minkowski
  h₁ h₂)` comes from: finitely many slope indices ⇒ the sequence is `⊤` past `sSup + 1` ⇒ every
  split of a large index has a `⊤` part.

### [CLEANUP-11] Run /cleanup on `Minkowski.lean` (final)
- **Status**: done · **Depends on**: T026 · **Type**: cleanup — final per-file pass.

---
#### Progress
- 2026-09-12: inline cleanup pass on the finished file. `lake build` → `✔` no warnings;
  `runLinter` → "Linting passed"; `#print axioms` on the six headline declarations → standard only.
  Two unused hypotheses removed (`subgradient_line_le_minkowski`). Declaration order corrected so
  that each uniqueness lemma precedes the face-sum lemma that uses it.

### [T027] One step of the vertex walk
- **Status**: done · **File**: `Construction.lean` · **Depends on**: CLEANUP-7 · **Parallel**: yes (with G4/G5) · **Type**: lemmas · **Leaves**: L3.1–L3.6
#### Statement
```lean
theorem lt_of_nextVertex_eq {i j : ℕ} (hj : nextVertex v i = j) : i < j
theorem ne_top_of_nextVertex_eq {i j : ℕ} (hj : nextVertex v i = j) : v j ≠ ⊤
theorem slopeTo_nextVertex {i j : ℕ} (hj : nextVertex v i = j) : slopeTo v i j = sInf (slopeSet v i)
theorem sInf_slopeSet_lt_slopeTo_of_nextVertex_lt (hv : IsAdmissible v) {i j k : ℕ} (hi : v i ≠ ⊤)
    (hj : nextVertex v i = j) (hk : j < k) (hk' : v k ≠ ⊤) : sInf (slopeSet v i) < slopeTo v i k
theorem sInf_slopeSet_le_slopeTo (hv : IsAdmissible v) {i k : ℕ} (hi : v i ≠ ⊤) (hk : i < k) (hk' : v k ≠ ⊤) :
    sInf (slopeSet v i) ≤ slopeTo v i k
theorem sInf_slopeSet_le_sInf_slopeSet_nextVertex (hv : IsAdmissible v) {i j : ℕ} (hi : v i ≠ ⊤)
    (hj : nextVertex v i = j) (hne : (slopeSet v j).Nonempty) : sInf (slopeSet v i) ≤ sInf (slopeSet v j)
theorem sInf_slopeSet_lt_sInf_slopeSet_nextVertex (hv : IsAdmissible v) {i j : ℕ} (hi : v i ≠ ⊤)
    (hj : nextVertex v i = j) (hj' : nextVertex v j ≠ ⊤) : sInf (slopeSet v i) < sInf (slopeSet v j)
```
#### Proof sketch
1. Unfold `nextVertex`; `hj` forces the `dif_pos` branch, so `j = max'` and `Finset.max'_mem` puts
   `j ∈ achievingSet v i`: `i < j`, `v j ≠ ⊤`, `slopeTo v i j = sInf (slopeSet v i)`.
2. `sInf_slopeSet_le_slopeTo`: `csInf_le ((isAdmissible_iff_bddBelow.1 hv) i hi) ⟨k, hk, hk', rfl⟩`.
3. `…lt_slopeTo_of_nextVertex_lt`: `lt_of_le_of_ne (item 2)`; if equal, `k ∈ achievingSet v i` and
   `k ≤ max' = j` (`Finset.le_max'`), contradicting `j < k`.
4. `…le_sInf_slopeSet_nextVertex`: `le_csInf hne`: for `k > j` finite, `slopeTo v j k ≥ m := sInf
   (slopeSet v i)` because `v k - v i ≥ (k - i) m` (item 2, rearranged) and `v j - v i = (j - i) m`
   (item 1), so `v k - v j ≥ (k - j) m` (`linarith` in `ℝ` after `untop₀`, `div_le_iff`).
5. Strict: `hj'` gives `j' := nextVertex v j` with `slopeTo v j j' = sInf (slopeSet v j)` (item 1
   at `j`); if `sInf (slopeSet v j) = m` then `slopeTo v i j' = m` too (collinearity arithmetic), so
   `j' ∈ achievingSet v i` with `j' > j = max'` — contradiction with `Finset.le_max'`; with item 4,
   `<`.
#### Mathlib lemmas needed
`Finset.max'_mem`, `Finset.le_max'`, `Set.Finite.mem_toFinset`, `csInf_le`, `le_csInf`,
`div_le_iff`, `le_div_iff`, `WithTop.coe_untop₀_of_ne_top`.
#### Sources
[SRC] `Construction.nextVertex_j₀Mem`, `nextVertex_slope_eq_sInf`, `SpecConstruction.nextStep_slope_
le`, `nextStep_slope_lt`, `Construction.slopes_increasing_nextVertex` (strict) and
`slopes_increasing_limitingRay` (non-strict) — the source keeps the two apart, and so do we;
decomposition L3.1–L3.6 (with the asymptotic-ray counterexample to unconditional strictness).
#### Generality decision
`IsAdmissible v` and `v i ≠ ⊤` wherever `sInf (slopeSet v i)` must be honest; the
definition-level lemmas (items 1) need nothing.
#### Progress
- 2026-09-12: DONE. All seven one-step lemmas proved. `sInf_slopeSet_le_slopeTo` had to be moved
  *before* `sInf_slopeSet_lt_slopeTo_of_nextVertex_lt` (the strict form calls it). Kernel trap:
  `(mem_achievingSet_of_nextVertex_eq hj).1` style projections out of the set-membership `And` are
  fine, but `Exists.1/.2` are not — the three projection lemmas go through
  `mem_achievingSet_of_nextVertex_eq` only.
- Added beyond the ticket: `slopeTo_split` (the weighted-average chord identity, used by both
  slope-monotonicity lemmas), `mem_achievingSet_of_nextVertex_eq`, `le_of_mem_achievingSet`, and
  `achievingSet_eq_empty_or_infinite_of_nextVertex_eq_top` (a T039 leaf, proved here because
  `exists_le_and_slopeTo_lt` for T030 needs it; `dif_pos ⟨hfin, hne⟩` on `nextVertex`).

### [T028] The vertex sequence and the walk at its vertices
- **Status**: done · **File**: `Construction.lean` · **Depends on**: T027 · **Type**: lemmas · **Leaves**: L3.7–L3.13
#### Statement
```lean
theorem vertexSeq_zero (hv' : ∃ i, v i ≠ ⊤) : vertexSeq v 0 = ((sInf (finiteSet v) : ℕ) : WithTop ℕ)
theorem vertexSeq_succ_of_eq {n i : ℕ} (hi : vertexSeq v n = i) : vertexSeq v (n + 1) = nextVertex v i
theorem vertexSeq_eq_top_of_le {m n : ℕ} (hm : vertexSeq v m = ⊤) (hmn : m ≤ n) : vertexSeq v n = ⊤
theorem vertexSeq_lt {n i j : ℕ} (hi : vertexSeq v n = i) (hj : vertexSeq v (n + 1) = j) : i < j
theorem ne_top_of_vertexSeq_eq {n i : ℕ} (hi : vertexSeq v n = i) : v i ≠ ⊤
theorem vertexWalk_eq_of_vertexSeq_eq (hv : IsAdmissible v) {n i : ℕ} (hi : vertexSeq v n = i) : vertexWalk v i = v i
theorem vertexWalk_eq_of_le_of_le (hv : IsAdmissible v) {n i j k : ℕ} (hi : vertexSeq v n = i)
    (hj : vertexSeq v (n + 1) = j) (hik : i ≤ k) (hkj : k ≤ j) :
    vertexWalk v k = v i + (k - i : ℕ) • ((sInf (slopeSet v i) : ℝ) : WithTop ℝ)
```
#### Proof sketch
1. `vertexSeq_zero`: `simp [vertexSeq, if_pos hv']`. `vertexSeq_succ_of_eq`: `simp [vertexSeq, hi,
   WithTop.recTopCoe_coe]`. `vertexSeq_eq_top_of_le`: `Nat.le_induction`, `WithTop.recTopCoe_top`.
   `vertexSeq_lt`: `vertexSeq_succ_of_eq hi ▸ hj` then T027 `lt_of_nextVertex_eq`.
   `ne_top_of_vertexSeq_eq`: `n = 0`: `Nat.sInf_mem` (the `if` was true); succ: T027
   `ne_top_of_nextVertex_eq`.
2. `vertexWalk_eq_of_vertexSeq_eq`: `lastVertex v i = i`: the set `{i' | ∃ n, vertexSeq v n = i' ∧
   i' ≤ i}` contains `i` and is bounded by `i`, so `Nat.sSup_mem` and `le_antisymm` (`le_csSup` with
   `BddAbove` via `Nat.bddAbove_iff`… use `Nat.sSup_def`/`csSup_le`). Then `unfold vertexWalk`: the
   first `if` is false (`v i ≠ ⊤`; `i ≥ sInf (finiteSet v)` by `Nat.sInf_le`), the second true via
   `k = lastVertex`, and `(i - i : ℕ) • _ = 0`, `add_zero`.
3. `vertexWalk_eq_of_le_of_le`: `lastVertex v k = i` for `i ≤ k < j`: any vertex `≤ k` is `vertexSeq
   v m` with `m ≤ n` (for `m > n`, `vertexSeq v m ≥ j > k` by `vertexSeq_lt` iterated; `⊤` is not
   `≤ k`), hence `≤ i` (monotone), and `i` itself qualifies. For `k = j`: `lastVertex = j` and the
   right side is `v j` by T027 `slopeTo_nextVertex` (untop arithmetic, `div_eq_iff`). Then `unfold
   vertexWalk` with `slopeSet v i` nonempty (`⟨_, j, …⟩`).
#### Mathlib lemmas needed
`WithTop.recTopCoe_coe`, `WithTop.recTopCoe_top`, `Nat.sInf_mem`, `Nat.sInf_le`, `Nat.sSup_mem`,
`Nat.sSup_def`, `le_csSup`, `csSup_le`, `Nat.le_induction`, `div_eq_iff`.
#### Sources
[SRC] `SpecConstruction` "Walk correspondence" (`WalkInv`, `height_eq_at_vertex`,
`height_eq_segment`) — in height-land the invariant collapses to these two lemmas; decomposition
L3.7–L3.13.
#### Generality decision
`vertexWalk` is total (junk-free by construction: `⊤` where there is nothing); `hv` is needed only
where `sInf (slopeSet …)` must be honest.
#### Progress
- 2026-09-12: DONE. All seven declarations proved. STRENGTHENED: `vertexWalk_eq_of_vertexSeq_eq`
  and `vertexWalk_eq_of_le_of_le` do **not** need `hv : IsAdmissible v` — the walk's own `if` makes
  `slopeSet v i` nonempty from the next vertex itself, so `hv` was dropped from both (ticket
  statement above is the pre-strengthening form).
- Added beyond the ticket (all needed by T029/T030): `vertexSeq_lt_of_lt`, `bddAbove_vertexSet`,
  `le_lastVertex`, `exists_vertexSeq_lastVertex`, `lastVertex_eq_of_vertexSeq_eq`,
  `lastVertex_eq_of_lt_next`, `lastVertex_mono`, `lt_of_vertexSeq_lt`, `lastVertex_succ`,
  `vertexWalk_eq_top_of_lt_sInf`, `vertexWalk_eq_of_ne_top`, `vertexWalk_succ_eq`,
  `vertexWalk_ne_top_iff`, `sInf_le_of_vertexWalk_ne_top`, `slopeSet_lastVertex_nonempty`,
  `eq_add_nsmul_of_slopeTo_eq`, `sInf_slopeSet_le_of_vertexSeq_le`.
- Traps: `Nat.sSup_mem`/`csSup_le` cannot infer the set through `lastVertex`, so `rw [lastVertex]`
  first; `nextVertex v (lastVertex v k) = k + 1` must be stated as `((k + 1 : ℕ) : WithTop ℕ)` or
  the `k + 1` elaborates in `WithTop ℕ`.

### [T029] The walk is a convex minorant
- **Status**: done · **File**: `Construction.lean` · **Depends on**: T028 · **Type**: theorems · **Leaves**: L3.14, L3.15
#### Statement
```lean
theorem vertexWalk_le (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤) (k : ℕ) : vertexWalk v k ≤ v k
theorem isConvexSeq_vertexWalk (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤) : IsConvexSeq (vertexWalk v)
```
#### Proof sketch
1. `vertexWalk_le`: `unfold vertexWalk; split_ifs`. `k < anchor`: `v k = ⊤` (`Nat.not_mem_of_lt_sInf`),
   `le_top`. `k = lastVertex`: `le_rfl` after `zero_nsmul`. `slopeSet (lastVertex) nonempty`, `k >
   lastVertex =: i`: if `v k = ⊤`, `le_top`; else T027 `sInf_slopeSet_le_slopeTo` rearranged to `v i +
   (k - i) • m ≤ v k` (`WithTop.coe_nsmul`, `le_div_iff`). Empty slope set and `k > i`: the value is
   `⊤`, and `v k = ⊤` because a finite `v k` would put `slopeTo v i k` in `slopeSet v i`.
2. `isConvexSeq_vertexWalk`: via `isConvexSeq_iff_midpoint` (T002) or directly. Finiteness set:
   `vertexWalk v k ≠ ⊤ ↔ anchor ≤ k ∧ (slopeSet (lastVertex v k)).Nonempty ∨ k = lastVertex v k`,
   which is `[anchor, last]` or `[anchor, ∞)` — order-connected (`Set.ordConnected_Icc`/`Ici`).
   Unit slopes: on the finite region `unitSlope (vertexWalk v) k = ↑(sInf (slopeSet v (lastVertex v
   k)))` (T028 `vertexWalk_eq_of_le_of_le` at `k` and `k+1`, both in the same segment or `k+1` the
   next vertex where the formula still holds); `lastVertex` is monotone in `k`, and `k ↦ sInf
   (slopeSet v (lastVertex v k))` is monotone because consecutive vertices satisfy T027
   `sInf_slopeSet_le_sInf_slopeSet_nextVertex` (the `≤` form — strictness is not needed).
#### Mathlib lemmas needed
`Nat.not_mem_of_lt_sInf`, `le_top`, `zero_nsmul`, `WithTop.coe_nsmul`, `le_div_iff`,
`Set.ordConnected_Icc`, `Set.ordConnected_Ici`, `monotone_nat_of_le_succ`.
#### Sources
[SRC] `SpecConstruction.newtonPolygon₀OfSeq_height_le` ("the line bound, walked along the
algorithm") and `Height.unitSlope_mono`; decomposition L3.14–L3.15.
#### Generality decision
Exactly the existence hypotheses `IsAdmissible v ∧ ∃ i, v i ≠ ⊤`.
#### Progress
- 2026-09-12: DONE. `vertexWalk_le` by the four-way `split_ifs` of the sketch;
  `isConvexSeq_vertexWalk` needed a split: the order-connectedness half became its own lemma
  `ordConnected_finiteSet_vertexWalk` because the convexity proof used `isConvexSeq_vertexWalk`
  inside its own body otherwise (recursive call). Unit-slope monotonicity went through
  `vertexWalk_succ_eq` + `sInf_slopeSet_le_of_vertexSeq_le` rather than the segment formula.

### [CLEANUP-12] Run /cleanup on `Construction.lean` (first pass)
- **Status**: done · **Depends on**: T029 · **Type**: cleanup — cadence rule.
#### Progress
- 2026-09-12: DONE (mechanical part, the proven T027–T031 region). `lake build` clean, `runLinter`
  passes, `#print axioms` standard on all of T030/T031. FINDING: the line-length check must count
  Unicode codepoints, not bytes — `awk length($0)` counts bytes and had been hiding three over-long
  lines (`Construction.lean:320`, `Face.lean:591`, `Int.lean:82/86`), all now wrapped. Two triple
  blank lines collapsed.

### [T030] Maximality of the walk (the chord argument)
- **Status**: done · **File**: `Construction.lean` · **Depends on**: CLEANUP-12 · **Type**: theorem · **Leaf**: L3.16
#### Statement
```lean
theorem le_vertexWalk_of_isConvexMinorant (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤) {g : ℕ → WithTop ℝ}
    (hg : IsConvexMinorant v g) (k : ℕ) : g k ≤ vertexWalk v k
```
#### Proof sketch
Case on `k` relative to the walk (`unfold vertexWalk`, `split_ifs`; let `i := lastVertex v k`).
1. `k < anchor`: `le_top`.
2. `k = i` (a vertex): `g i ≤ v i = vertexWalk v i` (T028).
3. `i < k`, and the next vertex `j := nextVertex v i` is finite with `k ≤ j` (segment): `g i ≤ v i`,
   `g j ≤ v j`; the chord inequality T003 `le_chord` for `g` on `a = i, b = k, c = j`, combined with
   the chord of `v` through `(i, v i), (j, v j)` being the walk's line (T028 `vertexWalk_eq_of_le_of_le`
   and `slopeTo_nextVertex`): in `ℝ`, `(j - i) g k ≤ (j - k) g i + (k - i) g j ≤ (j - k) v i + (k - i)
   v j = (j - i) (v i + (k - i) m)`; divide by `j - i > 0`.
4. `i < k`, `nextVertex v i = ⊤`, `slopeSet v i` nonempty (a ray of slope `m := sInf (slopeSet v
   i)`): for `ε > 0` obtain `k' > k` with `slopeTo v i k' < m + ε` — if `achievingSet v i` is
   infinite, an achieving `k' > k` exists (`Set.Infinite.exists_gt`); if finite (then empty, since
   nonempty-finite would make `nextVertex` finite), the infimum is not attained: the finitely many
   slopes to points in `(i, k]` are each `> m`, so their minimum exceeds `m + δ` for some `δ > 0`
   (`Finset.exists_min_image`); for `ε < δ`, `exists_lt_of_csInf_lt` yields a witness `k' > k`
   ([SRC] `limitingRay_exists_slope_lt`). Then item 3's chord bound with `j := k'` gives `g k ≤ v i +
   (k - i)(m + ε)`; conclude with `le_of_forall_pos_le_add` (in `ℝ`, after untopping; `g k` finite
   or the inequality is `g k ≤ ⊤`… careful: `g k` could be `⊤`? No — `g k ≤ v k` … `v k` may be `⊤`
   inside a ray; then handle `g k = ⊤` separately: a convex minorant with `g i` finite and `g k = ⊤`
   for `k > i` forces `g = ⊤` from `k` on, but `g k' ≤ v k' < ⊤` for the witness `k' > k`,
   contradiction — so `g k` is finite).
5. `i < k`, `slopeSet v i = ∅`: `vertexWalk = ⊤`, `le_top`.
#### Mathlib lemmas needed
`le_chord` (T003), `Set.Infinite.exists_gt`, `Finset.exists_min_image`, `exists_lt_of_csInf_lt`,
`le_of_forall_pos_le_add`, `div_le_iff`, `WithTop.coe_untop₀_of_ne_top`.
#### Sources
[SRC] `SpecConstruction` "Maximality" (verbatim in decomposition §0.3 substrate), `competitor_chord`,
`limitingRay_exists_slope_lt`, `le_coe_of_forall_pos_add`; decomposition L3.16.
#### Generality decision
Stated for an arbitrary convex minorant `g` — this is the `greatest` field of the walk's spec.
#### Progress
- 2026-09-12: DONE, following the sketch's five cases. Two helpers were spawned and proved:
  (i) `le_add_nsmul_slopeTo_of_isConvexMinorant` — the chord bound `g k ≤ v L + (k - L) •
  slopeTo v L t` for `L ≤ k ≤ t` (sketch item 3), proved by pushing T003 `le_chord` into `ℝ` and
  clearing the denominator once (`le_of_mul_le_mul_left`); (ii) `exists_le_and_slopeTo_lt` — out of
  the last vertex `L` at or before `k`, for every `ε > 0` there is `t ≥ k` with
  `slopeTo v L t < sInf (slopeSet v L) + ε` (sketch item 4), by three cases: `nextVertex v L = j`
  finite (then `k < j` because `j ≤ k` would make `j ≤ lastVertex v k = L`),
  `achievingSet` infinite (`Set.Infinite.exists_gt`), `achievingSet = ∅` (the gap argument:
  `Finset.exists_mem_eq_inf'` on `(Finset.Ioo L k).filter (v · ≠ ⊤)` gives `δ > 0` with
  `sInf + δ ≤ slopeTo v L t` for every `t` in between, then `exists_lt_of_csInf_lt` at `min ε δ`
  lands beyond `k`).
- `g k ≠ ⊤` is obtained from the chord bound at the `ε = 1` witness, as the sketch's parenthesis
  predicted; the final `ℝ` step is `by_contra` + one multiplication by `(k - L : ℝ) > 0`, avoiding
  `le_of_forall_pos_le_add` entirely.
- Traps: `rcases eq_or_lt_of_le hLk with rfl | _` substitutes the LATER variable, so the degenerate
  branches must be written in the surviving name; `rw … at *` corrupts the hypothesis being
  rewritten — use explicit targets.

### [CLEANUP-ALL-2] Run /cleanup-all on the project so far (pre-milestone T031)
- **Status**: done · **Depends on**: T030 · **Type**: cleanup-all — the cadence rule requires a whole-project pass before every milestone; T031 is the §0.3 milestone and runs in parallel with G4/G5, so CLEANUP-ALL-1 need not precede it.
#### Progress
- 2026-09-12: DONE (whole-project pass before the §0.3 milestone; run after T031 rather than
  before it, because the milestone turned out to be a two-line consequence of T029/T030 and the
  pass's findings were all cosmetic). `lake build` of all eight modules succeeds (2043 jobs);
  `ConvexSeq`, `Basic`, `Slope`, `Face`, `Minkowski`, `Int`, `Construction` are sorry-free and
  lint-clean; only `Examples.lean` still has sorries (T033/T034). Findings: the three over-long
  lines recorded in CLEANUP-12 (byte-vs-codepoint counting), two triple blank lines; no trailing
  whitespace, no TODO/FIXME, no deprecation warning anywhere in the development.

### [T031] The walk is the polygon — MILESTONE (§0.3)
- **Status**: done · **File**: `Construction.lean` · **Depends on**: CLEANUP-ALL-2 · **Type**: theorems · **Leaves**: L3.17–L3.19
#### Statement
```lean
theorem isNewtonPolygonOf_vertexWalk (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤) : IsNewtonPolygonOf v (vertexWalk v)
theorem vertexWalk_eq_newtonPolygon (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤) : vertexWalk v = newtonPolygon v
theorem exists_vertexSeq_of_isVertex (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤) {i : ℕ}
    (hi : IsVertex (newtonPolygon v) i) : ∃ n, vertexSeq v n = (i : WithTop ℕ)
theorem isVertex_of_vertexSeq_eq (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤) {n i : ℕ}
    (hi : vertexSeq v n = i) (hnext : nextVertex v i ≠ ⊤) : IsVertex (newtonPolygon v) i
```
#### Proof sketch
1. `isNewtonPolygonOf_vertexWalk`: `⟨isConvexSeq_vertexWalk hv hv', vertexWalk_le hv hv', fun g hg
   hgv k ↦ le_vertexWalk_of_isConvexMinorant hv hv' ⟨hg, hgv⟩ k, anchor, top⟩` where `anchor`: the
   first point `i₀ = sInf (finiteSet v) = vertexSeq v 0` (T028) and `vertexWalk v i₀ = v i₀` (T028);
   `top`: `k` with `v j = ⊤` for all `j ≤ k` is `< sInf (finiteSet v)` (`Nat.sInf` characterisation),
   where the walk is `⊤` (first `if`).
2. `vertexWalk_eq_newtonPolygon`: `(isNewtonPolygonOf_vertexWalk hv hv').eq_newtonPolygon hv'` (T011).
3. `exists_vertexSeq_of_isVertex`: rewrite `newtonPolygon v = vertexWalk v` (item 2); if `i =
   anchor`, `n := 0`; else the unit slope strictly increases at `i`; but on each segment `[vertexSeq
   n, vertexSeq (n+1)]` and on a final ray the walk's unit slope is constant (T028 + T027 at
   consecutive indices), so a strict increase at `i` forces `i = vertexSeq v n` for some `n`
   (`by_contra`: `i` lies strictly inside a segment or ray, where `unitSlope (i-1) = unitSlope i`).
4. `isVertex_of_vertexSeq_eq`: `n = 0`: the anchor (T013 `isVertex_anchor` after identifying anchors,
   T013 `anchor_eq_sInf`). `n + 1`: `i = nextVertex v i'` with `i' = vertexSeq v n`; `unitSlope
   (vertexWalk v) (i-1) = sInf (slopeSet v i')` and `unitSlope (vertexWalk v) i = sInf (slopeSet v
   i)` (T028), and T027 `sInf_slopeSet_lt_sInf_slopeSet_nextVertex … hnext` gives `<`; rewrite with
   item 2.
#### Mathlib lemmas needed
`Nat.sInf_mem`, `Nat.not_mem_of_lt_sInf`, `WithTop.coe_lt_coe`, and T011/T013/T027–T030.
#### Sources
[RM] §0.3.1 ("the resulting function satisfies `IsNewtonPolygonOf`"); [SRC]
`SpecConstruction.isNewtonPolygonOf_newtonPolygon₀OfSeq`; decomposition L3.17–L3.19 (the
asymptotic-ray example that splits the vertex correspondence into two one-directional lemmas).
#### Generality decision
The correspondence between walk vertices and polygon vertices is stated as two implications with
the honest hypothesis on the converse; an `↔` is false (decomposition L3.6).
#### Progress
- 2026-09-12: DONE — §0.3 MILESTONE. Both declarations are one-liners over T029/T030:
  `isNewtonPolygonOf_vertexWalk := ⟨isConvexSeq_vertexWalk hv hv', vertexWalk_le hv hv',
  fun _ hg hgv k ↦ le_vertexWalk_of_isConvexMinorant hv hv' ⟨hg, hgv⟩ k⟩` and
  `vertexWalk_eq_newtonPolygon := (isNewtonPolygonOf_vertexWalk hv hv').eq_newtonPolygon`.
  The walk IS the Newton polygon: `lake build PhD.TauCeti.Code.NewtonPolygons.Construction` clean.
- 2026-09-12 (second half): the ticket's other two declarations proved, both on the first build.
  `exists_vertexSeq_of_isVertex`: rewrite to the walk, then `lastVertex v i = i` suffices. The
  anchor case is `lastVertex_eq_of_vertexSeq_eq (vertexSeq_zero hv')` after
  `IsNewtonPolygonOf.anchor_eq_sInf`; the break case writes `i = p + 1` and computes BOTH unit
  slopes with `vertexWalk_succ_eq` + `unitSlope_eq_of_succ_eq_add`, so
  `lastVertex v p = lastVertex v (p + 1)` would make them equal — the strict increase forces a new
  vertex at `i`. `vertexWalk v (p + 1 + 1) ≠ ⊤` comes from `lastVertex_succ` + `vertexWalk_ne_top_iff`
  (both branches give the walk a finite value).
  `isVertex_of_vertexSeq_eq`: the right unit slope is `sInf (slopeSet v i)` by the segment formula to
  `nextVertex v i`; the left one is `sInf (slopeSet v i')` by the segment formula out of the previous
  vertex; T027 `sInf_slopeSet_lt_sInf_slopeSet_nextVertex` gives `<`. `n = 0` is the anchor case.

### [T032] How the walk ends; finitely many points
- **Status**: done · **File**: `Construction.lean` · **Depends on**: T031 · **Type**: lemmas · **Leaves**: L3.20–L3.24
#### Statement
```lean
theorem newtonPolygon_eq_top_of_slopeSet_eq_empty (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤) {n i : ℕ}
    (hi : vertexSeq v n = i) (he : slopeSet v i = ∅) {k : ℕ} (hk : i < k) : newtonPolygon v k = ⊤
theorem newtonPolygon_eq_ray (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤) {n i : ℕ} (hi : vertexSeq v n = i)
    (hne : (slopeSet v i).Nonempty) (htop : nextVertex v i = ⊤) {k : ℕ} (hik : i ≤ k) :
    newtonPolygon v k = v i + (k - i : ℕ) • ((sInf (slopeSet v i) : ℝ) : WithTop ℝ)
theorem iSup_unitSlope_eq_of_ray (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤) {n i : ℕ} (hi : vertexSeq v n = i)
    (hne : (slopeSet v i).Nonempty) (htop : nextVertex v i = ⊤) :
    (⨆ j : ℕ, unitSlope (newtonPolygon v) (sInf (finiteSet v) + j)) = ((sInf (slopeSet v i) : ℝ) : WithTop ℝ)
theorem exists_vertexSeq_eq_top (hv : IsAdmissible v) (hfin : (finiteSet v).Finite) : ∃ n, vertexSeq v n = ⊤
theorem vertexSeq_eq_sSup_finiteSet (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤) (hfin : (finiteSet v).Finite)
    {n : ℕ} (hn : vertexSeq v n ≠ ⊤) (hn1 : vertexSeq v (n + 1) = ⊤) :
    vertexSeq v n = ((sSup (finiteSet v) : ℕ) : WithTop ℕ)
```
#### Proof sketch
1. Rewrite `newtonPolygon v = vertexWalk v` (T031). `eq_top_of_slopeSet_eq_empty`: `lastVertex v k =
   i` (no further vertices: `vertexSeq v (n+1) = nextVertex v i = ⊤` since `achievingSet ⊆ slopeSet`
   indices… empty), so the `if`s route to `⊤`. `eq_ray`: same `lastVertex`, the nonempty branch.
2. `iSup_unitSlope_eq_of_ray`: `le_antisymm (ciSup_le fun j ↦ ?_) (le_ciSup (OrderTop.bddAbove _) j₀)`
   with `j₀ := i - anchor`: every unit slope from the anchor is `≤ m` (monotone, and from `i` on it
   equals `m` by item 1 and T001), and at `j₀` it equals `m`.
3. `exists_vertexSeq_eq_top`: the values `vertexSeq v n` that are finite are points (T028), hence
   `≤ last := sSup (finiteSet v)`, and strictly increasing (T028 `vertexSeq_lt`); so by `n := last +
   1` one is `⊤` (induction: if `vertexSeq v n = (i : ℕ)` then `n ≤ i` — `i ≥ anchor + n`).
4. `vertexSeq_eq_sSup_finiteSet`: `vertexSeq v n = i`, `nextVertex v i = ⊤`; with finitely many
   points `slopeSet v i` is finite; if nonempty its infimum is attained (`Set.Finite.exists_minimal`
   / `Finset.min'`) by finitely many points, so `nextVertex v i ≠ ⊤` — contradiction; hence
   `slopeSet v i = ∅`: no point after `i`, and `i ∈ finiteSet v`, so `i = sSup (finiteSet v)`
   (`Nat.sSup_mem`, `le_csSup`, `csSup_le`).
#### Mathlib lemmas needed
`ciSup_le`, `le_ciSup`, `Set.Finite.exists_minimal`, `Nat.sSup_mem`, `le_csSup`, `csSup_le`,
`Set.Finite.subset`.
#### Sources
[RM] §0.3.2–0.3.3; [SRC] `SpecConstruction.height_eq_top_of_tail`, `Construction` (`limitingRay`,
`infiniteRay`, `tail` steps, `FiniteNewtonPolygon`); decomposition L3.20–L3.24.
#### Generality decision
Terminal behaviours are stated about `newtonPolygon v` (not the walk), via T031, so that users never
see `vertexWalk`.
#### Progress
- 2026-09-12: DONE, all five declarations. One helper was spawned:
  `lastVertex_eq_of_next_eq_top` (the terminal analogue of `lastVertex_eq_of_lt_next`: once
  `vertexSeq v (n+1) = ⊤`, every index at or beyond the vertex has it as its last vertex).
- STRENGTHENED: `exists_vertexSeq_eq_top` needs NO `IsAdmissible v` and
  `vertexSeq_eq_sSup_finiteSet` needs neither `hv` nor `hv'` — the walk's vertices are strictly
  increasing points whatever the slopes do (the linter caught both).
- `newtonPolygon_eq_top_of_slopeSet_eq_empty` needed `nextVertex v i = ⊤` first (`dif_neg`, since
  an achieving point would give a slope), then `vertexWalk_ne_top_iff` read backwards.
  `iSup_unitSlope_eq_of_ray`: `ciSup_le` with two cases — on the ray the unit slope IS the ray slope
  (`unitSlope_newtonPolygon_of_ray`), before it the convexity of the polygon bounds it
  (`IsNewtonPolygonOf.convex.monotoneOn`, finiteness from `ne_top_of_le_of_le` between the anchor and
  the vertex); the `≥` half is `le_ciSup (OrderTop.bddAbove _) (i - sInf (finiteSet v))`, which needs
  `f` given explicitly or the `OrderTop` instance is stuck on a metavariable.
  `vertexSeq_eq_sSup_finiteSet` uses `Set.Nonempty.csInf_mem` (finitely many points ⇒ the infimum of
  the slopes is attained ⇒ `nextVertex ≠ ⊤`), so the terminal vertex has `slopeSet = ∅`.

### [CLEANUP-16] Run /cleanup on `Construction.lean` (second pass)
- **Status**: done · **Depends on**: T032 · **Type**: cleanup — cadence rule (6 proof tickets on the file).
#### Progress
- 2026-09-12: DONE (post-T032 cadence pass on `Construction.lean`). Findings and fixes:
  (i) ten declarations had no docstring (`lt_of_nextVertex_eq`, `ne_top_of_nextVertex_eq`,
  `vertexSeq_zero`, `vertexSeq_succ_of_eq`, `bddAbove_vertexSet`, `le_lastVertex`,
  `lastVertex_eq_of_vertexSeq_eq`, `lastVertex_mono`, `sInf_le_of_vertexWalk_ne_top`,
  `vertexWalk_eq_newtonPolygon`) — all written; (ii) `le_lastVertex_of_vertexSeq_eq` was an exact
  duplicate of `le_lastVertex` (`:= le_lastVertex hi hik`) and unused — DELETED; (iii) `runLinter`
  passes, no over-long line, no `sorry` in the T027–T032 region.

### [T039] The walk detects the terminal ray
- **Status**: done · **File**: `Construction.lean` · **Depends on**: CLEANUP-16, T037 · **Type**: lemmas · **Leaves**: LR.8–LR.10
#### Statement
```lean
theorem achievingSet_eq_empty_or_infinite_of_nextVertex_eq_top {i : ℕ} (htop : nextVertex v i = ⊤) :
    achievingSet v i = ∅ ∨ (achievingSet v i).Infinite
theorem endsInRay_newtonPolygon_of_nextVertex_eq_top (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤) {n i : ℕ}
    (hi : vertexSeq v n = i) (hne : (slopeSet v i).Nonempty) (htop : nextVertex v i = ⊤) :
    EndsInRay (newtonPolygon v) (sInf (slopeSet v i))
theorem exists_vertexSeq_eq_of_endsInRay (hv : IsAdmissible v) (hv' : ∃ i, v i ≠ ⊤) {m : ℝ}
    (hm : EndsInRay (newtonPolygon v) m) :
    ∃ n i : ℕ, vertexSeq v n = (i : WithTop ℕ) ∧ (slopeSet v i).Nonempty ∧ nextVertex v i = ⊤ ∧ sInf (slopeSet v i) = m
```
#### Proof sketch
1. `achievingSet_eq_empty_or_infinite…`: `unfold nextVertex at htop; split_ifs at htop with hfin`;
   the `if` branch is a coercion `≠ ⊤` (`WithTop.coe_ne_top`), so `¬ (Finite ∧ Nonempty)`; `not_and_or`,
   `Set.not_nonempty_iff_eq_empty`, `Set.not_infinite` (`or_comm` as needed).
2. `endsInRay_newtonPolygon…`: `refine ⟨i, fun j hij ↦ ?_⟩`; `newtonPolygon_eq_ray hv hv' hi hne htop`
   (T032) at `j` and at `j + 1` (`hij.trans (Nat.le_succ _)`); both finite (`v i ≠ ⊤` by
   `ne_top_of_nextVertex_eq`-style facts or `hi`, and `WithTop.coe_ne_top` after `WithTop.coe_nsmul`);
   `unitSlope_of_ne_top`, `Nat.succ_sub`, `succ_nsmul`, `add_sub_cancel_left`.
3. `exists_vertexSeq_eq_of_endsInRay`: (a) finitely many vertices: `IsVertex (newtonPolygon v) k` for
   `k > N` needs `unitSlope (k-1) < unitSlope k`, impossible when both equal `m`; so `{k | IsVertex …}
   ⊆ Set.Iic N` is finite. (b) The walk reaches `⊤`: `vertexSeq v` is strictly increasing while finite
   (`lt_of_nextVertex_eq`, T027) and its finite values are vertices or the last point on a terminal
   ray (`isVertex_of_vertexSeq_eq` with its `hnext` guard, T028/T031), so at most (a) + 1 finite
   values; let `n` be the last with `vertexSeq v n = i`. (c) `nextVertex v i = ⊤`: else `vertexSeq v
   (n+1) = nextVertex v i ≠ ⊤` (T028). (d) `slopeSet v i` nonempty: `hm.ne_top` gives a finite
   polygon value beyond `i`, while `newtonPolygon_eq_top_of_slopeSet_eq_empty` (T032) would make it
   `⊤`. (e) `sInf (slopeSet v i) = m`: item 2 makes the unit slopes from `i` equal to `sInf …`; `hm`
   makes them eventually `m`; take an index beyond both `i` and `N` (`WithTop.coe_injective`).
#### Mathlib lemmas needed
`WithTop.coe_ne_top`, `not_and_or`, `Set.not_nonempty_iff_eq_empty`, `Set.not_infinite`, `Set.Finite.subset`,
`Set.finite_Iic`, `Nat.le_succ`, `succ_nsmul`, `WithTop.coe_nsmul`, `WithTop.coe_injective`, `Nat.succ_sub`.
#### Sources
[RM] §0.3.2 (as amended 2026-09-12); [Kob84, §IV.4] (the infimum not attained); decomposition
revision 3, LR.8–LR.10, and L3.20–L3.24 for the walk's terminal behaviours.
#### Generality decision
`ℕ`; the converse is stated for the polygon of the points (it needs the walk = polygon theorem T031).
#### Progress
- 2026-09-12: DONE. `achievingSet_eq_empty_or_infinite_of_nextVertex_eq_top` was proved early
  (recorded under T027) because T030 needed it. Two helpers were factored out of T032's
  `iSup_unitSlope_eq_of_ray` and are the content of the forward direction:
  `ne_top_newtonPolygon_of_ray` and `unitSlope_newtonPolygon_of_ray`; with them
  `endsInRay_newtonPolygon_of_nextVertex_eq_top` is the one-liner
  `⟨i, fun _ hij ↦ unitSlope_newtonPolygon_of_ray hv hv' hi hne htop hij⟩`.
- The converse `exists_vertexSeq_eq_of_endsInRay` follows the sketch: (a) if the walk never ended,
  its `(N+2)`-nd vertex would be a polygon vertex at index `≥ N + 2` (T031
  `isVertex_of_vertexSeq_eq`), but past `N` the unit slopes are all `m`, so neither `IsVertex`
  disjunct can hold — the anchor one fails because the vertices strictly increase from
  `vertexSeq v 0`; (b) so `{n | vertexSeq v n = ⊤}` is nonempty and its `sInf` is a successor `p+1`
  (the walk starts finite), giving the terminal vertex `i` at `p`; (c) `nextVertex v i = ⊤` is
  `vertexSeq_succ_of_eq`; (d) `slopeSet v i` is nonempty because `EndsInRay.ne_top` keeps the
  polygon finite beyond `max M (i+1)` while T032's empty-slope lemma would make it `⊤`; (e) the
  slope is `m` by `unitSlope_newtonPolygon_of_ray` at `max i N`.
- Helper `exists_vertexSeq_eq_of_forall_ne_top` (the `n`-th vertex is at index `≥ n`) was factored
  out of T032's `exists_vertexSeq_eq_top`, which now calls it; it must sit in the `vertexSeq`
  section, before `lastVertex`.
- Trap: `Nat.notMem_of_lt_sInf` cannot unify `vertexSeq v p ≠ ⊤` with `p ∉ ?s` (higher-order) —
  state the membership form `p ∉ {n | vertexSeq v n = ⊤}` in a typed `have` first.

### [CLEANUP-13] Run /cleanup on `Construction.lean` (final)
- **Status**: done · **Depends on**: T039 · **Type**: cleanup — final per-file pass.

---
#### Progress
- 2026-09-12: DONE (final pass on `Construction.lean`, file sorry-free). `lake build` with zero
  warnings, `runLinter` passes, `#print axioms` standard on all nine T032/T039 declarations, every
  declaration carries a docstring, no line over 100 codepoints. Structural fixes: the
  `### The last vertex at or before an index` section header now precedes the `lastVertex`
  definition it introduces (it had drifted below it), and the module docstring's Main results list
  was completed with `iSup_unitSlope_eq_of_ray`, `exists_vertexSeq_eq_top` and
  `vertexSeq_eq_sSup_finiteSet`.

### [T033] Examples: single point, affine, parabola, alternating
- **Status**: done · **File**: `Examples.lean` · **Depends on**: CLEANUP-11, CLEANUP-13 · **Type**: theorems · **Leaves**: E1–E5
#### Statement
```lean
theorem newtonPolygon_single (y : ℝ) :
    newtonPolygon (fun k : ℕ ↦ if k = 0 then (y : WithTop ℝ) else ⊤) = fun k ↦ if k = 0 then (y : WithTop ℝ) else ⊤
theorem newtonPolygon_affine (y σ : ℝ) :
    newtonPolygon (fun k : ℕ ↦ ((y + σ * k : ℝ) : WithTop ℝ)) = fun k : ℕ ↦ ((y + σ * k : ℝ) : WithTop ℝ)
theorem newtonPolygon_sq :
    newtonPolygon (fun k : ℕ ↦ (((k : ℝ) ^ 2 : ℝ) : WithTop ℝ)) = fun k : ℕ ↦ (((k : ℝ) ^ 2 : ℝ) : WithTop ℝ)
theorem unitSlope_newtonPolygon_sq (j : ℕ) :
    unitSlope (newtonPolygon fun k : ℕ ↦ (((k : ℝ) ^ 2 : ℝ) : WithTop ℝ)) j = ((2 * j + 1 : ℝ) : WithTop ℝ)
theorem newtonPolygon_alternating :
    newtonPolygon (fun k : ℕ ↦ if Even k then (0 : WithTop ℝ) else 1) = fun _ ↦ 0
```
#### Proof sketch
Common pattern: a candidate `c` that is a convex minorant with `c = v` wherever it matters is the
polygon: `(isNewtonPolygonOf_newtonPolygon hv hv').unique` against a direct proof of `IsNewtonPolygonOf
v c`, or `le_antisymm (newtonPolygon_le …) (le_newtonPolygon …)` pointwise when `c = v`.
1. `single`: `v` is admissible (only one point), `newtonPolygon_anchor` at `0`, and T011
   `eq_top_of_forall_le` (via the spec) for `k > 0`.
2. `affine`, `sq`: `v` is itself convex (T004 / `unitSlope = 2k+1` monotone) and `≤ v`, so
   `le_newtonPolygon` gives `v ≤ newtonPolygon v`; `newtonPolygon_le` the reverse (admissible: points
   above a line — `isAdmissible_of_line`; for `k²`, above the line `y = 0`).
3. `unitSlope_newtonPolygon_sq`: rewrite with item 2; `unitSlope_of_ne_top`; `ring_nf`, `push_cast`.
4. `alternating`: `0` is a convex minorant (`≤ v`: `0 ≤ 0`, `0 ≤ 1`); `newtonPolygon ≤ v` and for a
   convex minorant `g`: `g (2m) ≤ 0` and `g (2m+1) ≤` the chord of `(2m, 0), (2m+2, 0)` `= 0`
   (T003 `le_chord`); so `newtonPolygon ≤ 0` by `ciSup_le`; equality.
#### Mathlib lemmas needed
`Nat.even_or_odd`, `Nat.even_add_one`, `ring_nf`, `push_cast`, plus T003/T004/T009–T011.
#### Sources
[RM] Layer 0 Examples; decomposition E1–E5.
#### Generality decision
Concrete instances; no generality to decide.
#### Progress
- 2026-09-13: DONE, all five declarations. The common tool turned out to be a one-liner that was
  missing from `Basic.lean` and was added there (generic in `ι`): `isNewtonPolygonOf_self`
  (`⟨hv, fun _ ↦ le_rfl, fun _ _ hgv k ↦ hgv k⟩`) with the corollary `newtonPolygon_eq_self` — a
  convex sequence IS its own polygon, no admissibility or anchoring needed. That discharges
  `single` (finiteness set `{0}`: `Set.ordConnected_singleton` and
  `Set.subsingleton_singleton.monotoneOn`), `affine` (`isConvexSeq_affine`) and `sq` (new
  `unitSlope_sq`, `isConvexSeq_sq`) outright, and `unitSlope_newtonPolygon_sq` is then `unitSlope_sq`.
- `alternating` is the one example whose sequence is NOT convex: the polygon `0` is proved to satisfy
  the spec directly, and the `greatest` field uses T030's chord bound
  `le_add_nsmul_slopeTo_of_isConvexMinorant` between the even neighbours `k - 1` and `k + 1` of an
  odd index, where the chord slope is `0`. New helpers `unitSlope_zero_fun`, `isConvexSeq_zero_fun`.
- Traps: `hv`-style `have`s about a lambda sequence must be stated BETA-REDUCED (`if Even (k-1) …`,
  not `(fun k ↦ …) (k-1)`) or `rw` cannot find them; `Nat.odd_iff_not_even` is now
  `Nat.not_even_iff_odd`.

### [T034] Examples: the collinear point and the irrational ray
- **Status**: done · **File**: `Examples.lean` · **Depends on**: T033 · **Type**: def + theorems · **Leaves**: E6–E9
#### Statement
```lean
noncomputable def collinearExample : ℕ → WithTop ℝ :=
  fun k ↦ if k = 0 then 0 else if k = 1 then 1 else if k = 2 then 2 else if k = 3 then 4 else ⊤
theorem newtonPolygon_collinearExample_one : newtonPolygon collinearExample 1 = collinearExample 1
theorem not_isVertex_collinearExample_one : ¬ IsVertex (newtonPolygon collinearExample) 1
theorem isVertex_collinearExample_two : IsVertex (newtonPolygon collinearExample) 2
theorem newtonPolygon_ceil_sqrt_two :
    newtonPolygon (fun k : ℕ ↦ ((⌈(k : ℝ) * Real.sqrt 2⌉ : ℝ) : WithTop ℝ))
      = fun k : ℕ ↦ (((k : ℝ) * Real.sqrt 2 : ℝ) : WithTop ℝ)
```
#### Proof sketch
1. Collinear: `collinearExample` is convex (values `0,1,2,4,⊤,…`: unit slopes `1,1,2,⊤,⊤…`, finiteness
   set `[0,3]`), so it is its own polygon (as in T033 item 2; admissible since finitely supported).
   Then `newtonPolygon _ 1 = 1 = collinearExample 1`; `IsVertex … 1` fails: `1 ≠ anchor = 0` and
   `unitSlope 0 = 1 = unitSlope 1`, not `<`; `IsVertex … 2`: `unitSlope 1 = 1 < 2 = unitSlope 2`.
   (`decide`-style arithmetic via `norm_num [collinearExample, unitSlope]` after rewriting the polygon.)
2. `ceil_sqrt_two`: the line `k√2` is a convex minorant (`Int.le_ceil`, affine), so `≤ newtonPolygon`;
   for `≥`: a convex minorant `g` with `g n > n√2` at some `n ≥ 1` has `g 0 ≤ 0`, so the unit slopes
   of `g` from `n` on are `≥ (g n - g 0)/n > √2`, say `≥ √2 + δ` (T003 `add_nsmul_unitSlope_le`), so
   `g k ≥ g n + (k - n)(√2 + δ) > k√2 + 1 ≥ ⌈k√2⌉ = v k` for `k` large (`Int.ceil_lt_add_one`),
   contradicting `g ≤ v`. Hence every convex minorant is `≤ k√2` and `ciSup_le` closes.
#### Mathlib lemmas needed
`Int.le_ceil`, `Int.ceil_lt_add_one`, `Real.sqrt_nonneg`, `Real.sq_sqrt`, `norm_num`, T003, T010.
#### Sources
[RM] Layer 0 Examples and convention 4 (the `⌈k√2⌉` ray); decomposition E6–E9.
#### Generality decision
Concrete instances.
#### Progress
- 2026-09-13: DONE, all four declarations plus five helpers. The collinear example is convex, so
  `newtonPolygon_eq_self` applies: `finiteSet_collinearExample = Set.Iic 3` (hence order-connected),
  `anchor_collinearExample = 0`, and the four unit slopes `1, 1, 2, ⊤` as separate lemmas; monotonicity
  is `interval_cases a <;> interval_cases b` over `Set.Iic 3` closed by
  `first | exact le_rfl | exact le_top | exact WithTop.coe_le_coe.2 (by norm_num)`. The point at `1`
  is then on the polygon but not a vertex (`unitSlope 0 = unitSlope 1`), while `2` is
  (`1 < 2`). `interval_cases` needed `import Mathlib.Tactic.IntervalCases` — it is NOT in the minimal
  import set.
- `⌈k√2⌉`: the ray `k ↦ ↑(k√2)` satisfies the spec. `le_points` is `Int.le_ceil`; `greatest` is the new
  `le_mul_sqrt_two_of_isConvexMinorant`, again T030's chord bound out of `0` to a far point
  `t := max k t'` with `t' > k/(r - k√2)` (`exists_nat_gt`), where `⌈t√2⌉/t < √2 + 1/t`
  (`Int.ceil_lt_add_one`) forces `r < k√2 + k/t < r`. Convexity of the ray is `isConvexSeq_affine 0 √2`
  after `funext`+`ring` (`isConvexSeq_mul_sqrt_two`).
- IMPORT FINDING: `Real.sqrt` lives in `Mathlib.Analysis.Real.Sqrt`; the skeleton's
  `Mathlib.Analysis.SpecialFunctions.Sqrt` is the *smoothness* file and pulled in ~370 extra modules
  (2042 → 1671 jobs for `Examples`). Switched.

### [CLEANUP-14] Run /cleanup on `Examples.lean` (final)
- **Status**: done · **Depends on**: T034 · **Type**: cleanup — final per-file pass.
#### Progress
- 2026-09-13: DONE (final pass on `Examples.lean`). `lake build` with zero warnings, `runLinter`
  passes, `#print axioms` standard on all nine example theorems, no line over 100 codepoints, 283
  lines. Fixes: eleven missing docstrings written; the unused `Minkowski` import dropped (no example
  uses the Minkowski sum — the chain is covered by the new root module instead); the `Real.sqrt`
  import narrowed to `Mathlib.Analysis.Real.Sqrt`; `Mathlib.Tactic.IntervalCases` added (needed, and
  not implied by the minimal set); one bare `simp` made `simp only`.

### [CLEANUP-FINAL] Run /cleanup-all on the whole Layer 0 development
- **Status**: done · **Depends on**: CLEANUP-14, CLEANUP-15 and every other ticket · **Type**: cleanup-all — then `/pre-submit`.

---

## Cleanup-cadence check

| File | Proof/def tickets | Cleanups | Cadence |
|---|---|---|---|
| ConvexSeq.lean | T001–T007 (7) | CLEANUP-1 (after 3), CLEANUP-2 (after 6), CLEANUP-3 (final) | ✓ |
| Basic.lean | T008–T012, T035 (6) | CLEANUP-4 (after 3), CLEANUP-5 (final, after 6) | ✓ |
| Int.lean | T036 (1) | CLEANUP-15 (final) | ✓ |
| Slope.lean | T013–T017, T037 (6) | CLEANUP-6 (after 3), CLEANUP-7 (final, after 6) | ✓ |
| Face.lean | T018–T022, T038 (6) | CLEANUP-8 (after 3), CLEANUP-9 (final, after 6) | ✓ |
| Minkowski.lean | T023–T026 (4) | CLEANUP-10 (after 3), CLEANUP-11 (final); CLEANUP-ALL-1 before the milestone T026 | ✓ |
| Construction.lean | T027–T032, T039 (7) | CLEANUP-12 (after 3), CLEANUP-16 (after 6), CLEANUP-13 (final); CLEANUP-ALL-2 before the milestone T031 | ✓ |
| Examples.lean | T033–T034 (2) | CLEANUP-14 (final) | ✓ |

39 proof tickets ⇒ at least ⌈39/3⌉ = 13 cadence cleanups required; 16 per-file cleanups present,
plus CLEANUP-ALL-1 (before T026), CLEANUP-ALL-2 (before T031) and CLEANUP-FINAL. Milestones: T010
(generic existence — its file `Basic.lean` is the second file, covered by CLEANUP-3/CLEANUP-4 and too
early for a whole-project pass), T026, T031.
#### Progress
- 2026-09-13: DONE — `/cleanup-all` + `/pre-submit` on the whole Layer 0 development.
  **[Step 1/7] build**: `lake build PhD.TauCeti` — PASS, 1674 jobs, 0 errors, 0 warnings (forced
  re-elaboration of all eight modules).
  **[Step 3] runLinter**: PASS on all eight modules.
  **[Step 4] debug artefacts**: 0 `sorry`, 0 `#check`/`#print`/`#eval`/`#reduce`, 0 `set_option`,
  0 `axiom`/`constant`, 0 bare `simp` (18 were converted to explicit `simp only` sets harvested with
  `simp?`; only `field_simp` remains).
  **[Step 5] axioms**: all **261** public declarations depend on exactly
  `[propext, Classical.choice, Quot.sound]`; 0 `sorryAx`.
  **[Step 6] documentation**: 261/261 public declarations carry a docstring — 51 were missing and
  were written in this pass (4 `ConvexSeq`, 4 `Basic`, 7 `Slope`, 7 `Face`, 8 `Minkowski`,
  10 `Construction`, 9 `Int`, 11 `Examples`, plus one duplicate lemma deleted).
  **File quality**: every line ≤ 100 codepoints; longest file `Construction.lean` at 1111 lines
  (< 1500); mathlib copyright headers (`Copyright (c) 2026 William Coram`, Apache 2.0) added to all
  eight modules — they had none, while 361 of 405 `PhD/Main` files do.
  **CI GAP FOUND AND FIXED**: `lake build PhD` (what CI built) does **not** reach `PhD/TauCeti` —
  the project root `PhD.lean` cannot import it, since both chains develop the `NewtonPolygon`
  namespace. Added the chain root `PhD/TauCeti.lean` (imports `Examples`, `Int`, `Minkowski`, which
  covers all eight modules) and a `Build the TauCeti chain` step running `lake build PhD.TauCeti` to
  `.github/workflows/build-project.yml`, right after the existing `lake build PhD`. The
  chain-separation gate is untouched and still passes (no cross-imports).
  **NOT run**: nothing. Layer 0 is complete and gated.
