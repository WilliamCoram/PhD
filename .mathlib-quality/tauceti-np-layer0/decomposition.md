# Decomposition: Newton polygons, Layer 0

Companion to `plan.md`. Every leaf below is a `:= by sorry` declaration in the skeleton; the pointer
is `File.lean · declaration name` (names are stable, line numbers are not). Sources: [RM] = the
roadmap clause the leaf discharges; [Ked07] / [Kob84] / [Mathlib] = literature and library, quoted
verbatim; [SRC] = the read-only reference development `PhD/Main/…` at `fdc44e2`, cited by
`File.decl` for the *proof idea* only (never imported). Discharge lines name the Mathlib lemmas a
worker will call — every name below was checked by elaboration (`scratchpad/names.lean`, 60/63;
the three misses are replaced by their existing forms `Nat.card_Ico`,
`WithTop.eq_top_iff_forall_gt`, `Finset.max'_mem`).

## Skeleton location

- `PhD/TauCeti/Code/NewtonPolygons/ConvexSeq.lean` (§0.1)
- `PhD/TauCeti/Code/NewtonPolygons/Basic.lean` (§0.2)
- `PhD/TauCeti/Code/NewtonPolygons/Slope.lean` (§0.4)
- `PhD/TauCeti/Code/NewtonPolygons/Face.lean` (§0.5)
- `PhD/TauCeti/Code/NewtonPolygons/Minkowski.lean` (§0.6)
- `PhD/TauCeti/Code/NewtonPolygons/Construction.lean` (§0.3)
- `PhD/TauCeti/Code/NewtonPolygons/Examples.lean` (Examples)

Build status: recorded in the "Gate" section at the end of this file.

## Prior-B2 consultation (Step 4.6), once for the whole tree

`b2_log.jsonl` has 8 entries; two concern Newton polygons:

- `NewtonPolygon₀.unitSlope_cases` (T002, 2026-08-03): *"False for the degenerate polygon
  support=1, lengths≡0, slopes 0 = real: all vertexX n = x₀ (no bracket) yet unitSlope 0 =
  slopes 0 ≠ ⊤"* — a zero-width segment carrying a real slope, representable in the
  segment-decorated structure.
- `NewtonPolygon₀.lengths_final` (T002-followup): resolved by outlawing the phantom.

**Addressed by design (plan.md decision 1).** No leaf in this tree has segment data: a one-point
polygon is `h = (⊤, …, ⊤, y, ⊤, …)` and every unit slope is `⊤`. Nothing named `unitSlope_cases`
exists; the closest statements, `isVertex_of_succ_eq_top` and `IsConvexSeq.slopeIndices_eq_Ico`,
were instantiated at the one-point polygon in their attack logs below. No other leaf matches the
log by name or shape.

---

## §0.1 Convex sequences (`ConvexSeq.lean`)

### Plain-English proof substrate

A convex sequence is a function `h : ℕ → WithTop ℝ` that is finite exactly on an interval and whose
increments are non-decreasing there. All of §0.1 is elementary: the chord inequality is the
statement that the average of the first `b - a` increments is at most the average of the next
`c - b`, which holds termwise because every increment of the first block is at most every increment
of the second; the supremum of a family of convex sequences is convex because the midpoint
inequality `2 g(k+1) ≤ g k + g(k+2)` passes to suprema; the `ConvexOn` bridge exhibits the
piecewise-linear interpolation as a supremum of the supporting lines.

### Leaves

- **L1.1** `unitSlope_eq_top_iff` — [RM] §0.1.1 "fix the convention for its value outside the
  finiteness interval". Lean: `unitSlope h j = ⊤ ↔ h j = ⊤ ∨ h (j + 1) = ⊤`. Match: the convention
  is *definitional* (the `if`); this lemma is its API form. Discharge: `unfold unitSlope; split_ifs`
  + `WithTop.coe_ne_top`. Attacks: [2] edge `h ≡ ⊤`: both sides true ✓; `h` finite at `j` and
  `j+1`: LHS is a real coercion `≠ ⊤` ✓, RHS false ✓. [3] no hypotheses to weaken. [5] `simp`
  lemma `WithTop.coe_ne_top` exists ✓. Verdict: SURVIVED.

- **L1.2** `unitSlope_of_ne_top` — companion; the value when both ends are finite. Discharge:
  `unfold unitSlope; rw [if_neg]` with `not_or`. Attacks: [2] `j` at the last finite index — needs
  `h (j+1) ≠ ⊤` so excluded by hypothesis ✓. [3] both hypotheses necessary (drop either and the
  `if` fires). [5] trivial. SURVIVED.

- **L1.3** `add_unitSlope` — the increment identity `h j + unitSlope h j = h (j + 1)` for `h j ≠ ⊤`.
  Match: this is what "increment" means. Discharge: case on `h (j+1) = ⊤` (then both sides `⊤` by
  `add_top`); else `unitSlope_of_ne_top`, `WithTop.coe_untop₀_of_ne_top`, `← WithTop.coe_add`,
  `sub_add_cancel`. Attacks: [2] `h (j+1) = ⊤`: LHS `h j + ⊤ = ⊤` ✓ RHS `⊤` ✓. [3] `h j ≠ ⊤` is
  necessary: with `h j = ⊤` and `h (j+1)` finite, LHS `⊤ + ⊤ = ⊤ ≠ h (j+1)` ✗ — so the hypothesis is
  exactly right. [5] all four lemmas verified. SURVIVED.

- **L1.4** `eq_of_unitSlope_eq` — [RM] §0.1.3 "determined by its value at one point together with its
  increments". Lean: one common finite value + equal unit slopes ⇒ `h = g`. No convexity needed.
  Sketch: `funext k`; induct outward from `i₀` in both directions using `add_unitSlope` (right) and,
  to the left, `unitSlope_eq_top_iff` to transfer `⊤`-ness and `add_unitSlope` at `k-1` otherwise.
  Attacks: [2] `i₀ = 0` (no left induction) ✓; `h` finite only at `i₀`: unit slopes `⊤` on both
  sides, so `g` is `⊤` there too ✓. [3] `h i₀ ≠ ⊤` cannot be dropped: `h ≡ ⊤`, `g = (⊤,⊤,0,⊤,…)`
  hmm — then `unitSlope g 1 = ⊤ = unitSlope h 1` but `unitSlope g 2 = ⊤` too; all unit slopes of
  `g` are `⊤` (single finite point), all of `h` are `⊤`, `h 0 = g 0 = ⊤` — hypotheses hold with
  `h ≠ g`. So `h i₀ ≠ ⊤` is **necessary** ✓ (kept). [4] roadmap wording "value at one point": the
  point must be finite, which the roadmap leaves implicit — recorded. SURVIVED.

- **L1.5** `IsConvexSeq.eq_top_of_le` — once `⊤` right of a finite value, stays `⊤`. Match:
  order-connectedness read from the right. Discharge: by contradiction, `hh.ordConnected.out ha hj
  ⟨hai, hij⟩` gives `h i ≠ ⊤`. Attacks: [2] `i = j`: trivial ✓; `a = i`: hypotheses contradictory
  (`h a ≠ ⊤`, `h i = ⊤`) so vacuous ✓. [3] `h a ≠ ⊤` with `a ≤ i` is necessary: `(⊤, 0, ⊤)` is not
  order-connected-violating — `h 0 = ⊤`, `h 2 = ⊤`, `h 1 = 0`: with `a = 1, i = 2, j = 3` fine;
  without a finite `a` to the left, `(⊤, 0)` has `h 0 = ⊤` but `h 1 ≠ ⊤` ✓ necessary. [5]
  `Set.OrdConnected.out` verified. SURVIVED.

- **L1.6** `IsConvexSeq.midpoint` — [RM] §0.1.1/§0.1.3. Lean: `h (k+1) + h (k+1) ≤ h k + h (k+2)`.
  Sketch: if `h k = ⊤` or `h (k+2) = ⊤` the RHS is `⊤` (`top_add`/`add_top`). Else both finite, so
  by order-connectedness `h (k+1)` finite; `hh.monotoneOn` at `k ≤ k+1` (both in `finiteSet`) gives
  `unitSlope h k ≤ unitSlope h (k+1)`; unfold via `unitSlope_of_ne_top`, `WithTop.coe_le_coe`,
  and `linarith` after `← WithTop.coe_add`. Attacks: [1] searched for a contradicting shape — none;
  the statement is the standard midpoint convexity. [2] `h (k+1) = ⊤` with `h k`, `h (k+2)` finite:
  impossible under `ordConnected` ✓ (this is exactly why the field is needed). [2'] one-point
  polygon: RHS `⊤` ✓. [3] neither field can be dropped: `(0, ⊤, 0)` satisfies `monotoneOn` on
  `{0,2}` vacuously but fails midpoint at `k = 0` — so `ordConnected` is necessary; `(0, 1, 0)` is
  order-connected but fails — `monotoneOn` necessary. SURVIVED.

- **L1.7** `isConvexSeq_iff_midpoint` — the converse packaging. Sketch: `←`: `monotoneOn` from
  midpoint at each `k` in the interval, chaining with `monotone_nat_of_le_succ` restricted to the
  interval (`MonotoneOn` via `Nat.le_induction`); the last-index case `unitSlope = ⊤` is `le_top`.
  Attacks: [2] finiteness set a singleton: `MonotoneOn` on a singleton trivial ✓. [3] `hord` cannot
  be dropped: `(0, ⊤, ⊤, 0)` is midpoint-convex (checked: `k=0`: `⊤ ≤ 0 + ⊤ = ⊤`; `k=1`: `⊤ ≤ ⊤`;
  `k=2`: `0 ≤ ⊤`) but not order-connected — recorded in plan.md decision 3. [4] roadmap says
  "increments are monotone on that interval" — the iff is exactly that, with the interval condition
  carried by `hord`. SURVIVED.

- **L1.8** `IsConvexSeq.le_chord` — [RM] §0.1.2 "a convex sequence lies on or below the chord joining
  any two of its points". Lean (division-free): `(c-a) • h b ≤ (c-b) • h a + (b-a) • h c`.
  [SRC] `Height.heightFun_chord` is the same statement in real form. Sketch: if `h a = ⊤` or
  `h c = ⊤`, RHS `⊤` (unless a coefficient is `0`, in which case the sides coincide — case split
  `a = b`, `b = c`). Else all three finite (L1.5-style via `ordConnected`); telescope
  `h b - h a = ∑_{[a,b)} s_j` and `h c - h b = ∑_{[b,c)} s_j` (`Finset.sum_Ico_consecutive`); by
  monotonicity `∑_{[a,b)} s ≤ (b-a) s_{b-1} ≤ (b-a) s_b ≤ …`, giving
  `(c-b) ∑_{[a,b)} s ≤ (b-a)(c-b) s_b ≤ (b-a) ∑_{[b,c)} s`; rearrange (`nlinarith`/`linarith`
  after `WithTop.coe_nsmul`, `WithTop.coe_le_coe`). Attacks: [2] `a = b = c`: `0 • x ≤ 0 • x + 0 • x`
  i.e. `0 ≤ 0` ✓ (nsmul by `0` is `0`, including `0 • ⊤ = 0`); `a = b < c`: LHS `(c-a) • h a`, RHS
  `(c-a) • h a + 0` ✓. [3] convexity necessary (`(0,1,0)` fails at `a=0,b=1,c=2`: `2•1 ≤ 1•0+1•0`
  ✗) ✓. [5] `WithTop.coe_nsmul` verified; `zero_nsmul`. SURVIVED.

- **L1.9** `IsConvexSeq.add_nsmul_unitSlope_le` — "on or above every extension of one of its
  increments" (right). Sketch: telescoping + monotonicity: `h k = h i + ∑_{[i,k)} s_j ≥ h i + (k-i) s_i`.
  If `h k = ⊤`, trivial. Attacks: [2] `k = i`: `0 • s = 0` ✓. [3] `h i ≠ ⊤` necessary (`⊤ + … ≤ h k`
  would fail for finite `h k`). SURVIVED.

- **L1.10** `IsConvexSeq.le_add_nsmul_unitSlope` — the left version. Same sketch mirrored. Attacks:
  [2] `k = i`: `h (i+1) ≤ h i + 1 • s_i` is `add_unitSlope` ✓ (equality). [3] `h (i+1) ≠ ⊤` needed
  (else `unitSlope h i = ⊤` and RHS `⊤` anyway — actually then the statement is trivially true;
  hypothesis is convenience, kept for the real-arithmetic proof; over-specification noted but
  harmless: the `⊤` case is one line). SURVIVED with note.

- **L1.11** `IsConvexSeq.eq_add_nsmul_of_forall_unitSlope_eq` — affine on a stretch of equal unit
  slopes. Sketch: induction on `k` from `a` with `add_unitSlope` and the hypothesis. Attacks: [2]
  `k = a` ✓. [3] convexity not actually used (pure telescoping) — over-specified: the `hh` argument
  can be dropped; **flagged for the ticket: state without `hh`** (a strengthening, no risk). [4]
  matches [RM] §0.4.1 "on which the polygon is affine". SURVIVED (with strengthening).

- **L1.12** `isConvexSeq_affine`, **L1.13** `isConvexSeq_top`, **L1.14** `IsConvexSeq.add_affine`
  — [RM] §0.1.5 "affine sequences are convex" and the invariance needed by §0.2.5. Sketch: unit
  slopes of an affine sequence are the constant `σ` (`unitSlope_of_ne_top` + `ring`); `finiteSet =
  univ` (`Set.ordConnected_univ`); for `⊤`: `finiteSet = ∅`; for `add_affine`: unit slopes shift by
  `σ`, finiteness set unchanged. Attacks: [2] `σ = 0` ✓; [3] none. SURVIVED.

- **L1.15** `IsConvexSeq.sup` — [Mathlib] `ConvexOn.sup` is the real-function analogue (verified
  signature). Sketch: `finiteSet (h ⊔ g) = finiteSet h ∩ finiteSet g` (`⊤` iff either is `⊤`:
  `sup_eq_top_iff`), intersection of order-connected is order-connected (`Set.OrdConnected.inter`);
  midpoint: `2 max(h,g)(k+1) ≤ max(h k + h(k+2), g k + g(k+2)) ≤ max h k + max h (k+2)…` — cleaner
  via `isConvexSeq_iff_midpoint` and `sup_le`/`le_sup`. Attacks: [2] `g ≡ ⊤`: `h ⊔ ⊤ = ⊤` convex ✓.
  [3] both convex needed. SURVIVED.

- **L1.16** `IsConvexSeq.iSup` — [RM] §0.1.3 "the pointwise supremum of any family of convex
  sequences … is convex … what makes the greatest convex minorant of §0.2 exist". Literature:
  Rockafellar, *Convex Analysis*, Thm 5.5 (pointwise supremum of convex functions is convex) —
  cited from memory, **not quoted verbatim**; the Mathlib two-function form `ConvexOn.sup` is the
  verified analogue. Sketch (midpoint route, `isConvexSeq_iff_midpoint`): let `S k = ⨆ i, f i k`.
  (i) order-connected: if `S a, S c` finite and `a ≤ b ≤ c` then each `f i a, f i c` finite (below
  a finite sup), so each `f i b` finite (order-connected) and `2 f i b ≤ f i a + f i c ≤ S a + S c`,
  so the family is bounded at `b` — `S b ≠ ⊤` by `ciSup_le` after halving in `ℝ`. (ii) midpoint:
  for each `i`, `f i (k+1) + f i (k+1) ≤ f i k + f i (k+2) ≤ S k + S (k+2)` (`le_ciSup` twice); if
  `S k + S (k+2) = ⊤` done; else untop to `ℝ`, get `f i (k+1) ≤ C/2` for all `i`, so
  `S (k+1) ≤ C/2` (`ciSup_le`), so `2 S(k+1) ≤ C`. Attacks: [2] constant family ✓; family
  unbounded at every index: `S ≡ ⊤` convex ✓ (L1.13). [3] `Nonempty ι` is needed only because
  `ciSup_le` needs it; the empty family gives the constant `sSup ∅` which is also convex, so the
  statement is not false without it, merely harder — kept. [4] [RM] says "bounded above at each
  index"; in `WithTop ℝ` unboundedness gives `⊤`, so the hypothesis is *not needed* — the Lean form
  is stronger than the roadmap's, recorded. [5] `le_ciSup`, `ciSup_le`, `WithTop.coe_le_coe`,
  `WithTop.coe_add` verified. SURVIVED.

- **L1.17** `not_isConvexSeq_inf` — [RM] §0.1.3 "the pointwise minimum … is not convex in general,
  and the counterexample is to be recorded". Lean: `k ↦ min k (2 - k)` is not convex. Sketch:
  values `0, 1, 0` at `0, 1, 2`; `unitSlope 0 = 1`, `unitSlope 1 = -1`; `MonotoneOn` at `0 ≤ 1`
  fails (`norm_num`). Attacks: [2] direct computation ✓. SURVIVED.

- **L1.18** `IsConvexSeq.exists_convexOn` — [RM] §0.1.4, direction "discrete ⇒ `ConvexOn`".
  [Mathlib] `ConvexOn` docstring: convexity on a set as the two-point inequality. Sketch: define
  `H x := ⨆ j : ℕ, (h j + s_j (x - j))` (supporting lines; bounded above on `[0,∞)` since the lines
  are dominated by the chord through the neighbours of `x` — needs the chord inequality L1.8 in
  real form); each line is affine hence `ConvexOn`; the supremum of a family of `ConvexOn`
  functions is `ConvexOn` — **Mathlib check: `ConvexOn.sup` covers two; for an indexed family search
  `convexOn_iSup` / prove from `ConvexOn` definition (two-point inequality passes to `ciSup`)**;
  `H k = h k` because the `k`-th line attains and the others lie below (L1.9/L1.10). Attacks: [2]
  affine `h`: `H` is the line ✓. [3] `hfin` needed: `ConvexOn ℝ (Ici 0)` requires a real value at
  every `k`. [5] `convexOn_iSup` **unverified** — ticket must first `lean_loogle` it; fallback
  proof from the definition is ≤ 20 lines. SURVIVED, with an explicit API check in the ticket.

- **L1.19** `isConvexSeq_of_convexOn` — the converse. [Mathlib] `ConvexOn.slope_mono_adjacent`
  (verified): for `x < y < z` in `s`, `(f y - f x)/(y - x) ≤ (f z - f y)/(z - y)`. Sketch: apply at
  `x = j, y = j+1, z = j+2` (denominators `1`) to get `unitSlope` monotone on consecutive indices,
  chain; `finiteSet = univ`. Attacks: [2] constant `H` ✓. [4] Mathlib's hypothesis set
  (`Field 𝕜`, `LinearOrder`, `IsStrictOrderedRing`) is satisfied by `ℝ` ✓. SURVIVED.

- **L1.20** `IsConvexSeq.tendsto_unitSlope` — [RM] §0.1.5 "a convex sequence with a bounded
  increment sequence has a limiting slope". Discharge: `tendsto_atTop_ciSup` (verified) applied to
  the monotone real sequence `j ↦ (unitSlope h j).untop₀` (monotone from `hh.monotoneOn` and
  `hfin`, via `WithTop.coe_le_coe` after `unitSlope_of_ne_top`). Attacks: [2] constant slopes ✓.
  [3] `hb` necessary (`k²` has unbounded slopes, no finite limit). SURVIVED.

- **L1.21** `IsConvexSeq.antitone_or_eventually_monotone` — [RM] §0.1.5 "eventually monotone".
  Sketch: by cases on `∃ N, 0 ≤ unitSlope h N` (with `h N`, `h (N+1)` finite): if so, from `N` on
  every unit slope is `≥ 0` (monotone) so `h k ≤ h (k+1)` (`add_unitSlope`); if not, every finite
  unit slope is `< 0`, so `h (k+1) ≤ h k` on the finite part, and off it the inequality holds
  because `⊤` is on the correct side (`h k = ⊤` gives `h (k+1) ≤ ⊤`; `h (k+1) = ⊤` with `h k`
  finite means `k` is the last index — then `h (k+1) = ⊤ ≤ h k` is **false**). **Attack [2]
  succeeds on the second disjunct as stated**: a decreasing finite polygon `(1, 0, ⊤, ⊤, …)` has
  `h 2 = ⊤ ≰ h 1 = 0`. FIX: the antitone disjunct must be restricted to the finiteness interval,
  or the statement reordered as "monotone from some index on, or antitone on the finiteness set".
  **Corrected statement for the skeleton**: `(∀ k, h (k+1) ≠ ⊤ → h (k+1) ≤ h k) ∨ ∃ N, ∀ k, N ≤ k
  → h k ≤ h (k+1)`. Re-attack: `(1,0,⊤,…)`: first disjunct now vacuous at `k = 1` ✓; `(0,1,⊤,…)`:
  second disjunct with `N = 0` ✓ (`h 1 ≤ h 2 = ⊤`). SURVIVED after correction — **skeleton edit
  required** (recorded in the Gate section).

- **L1.22** `eq_add_sum_unitSlope` (helper added at Step 2.5) — telescoping: `h k = h a + ∑_{[a,k)}
  untop₀ (unitSlope h j)` when every `h j`, `a ≤ j ≤ k`, is finite. Discharge: `Nat.le_induction`,
  `Finset.sum_Ico_succ_top`, `add_unitSlope`, `WithTop.coe_add`. Attacks: [2] `a = k`: empty sum ✓.
  [3] **the first draft hypothesised only `h k ≠ ⊤`, and attack [2] succeeded**: `(0, ⊤, 5)` at
  `a = 0, k = 2` has `h 2 = 5 ≠ ⊤`, `untop₀`-slopes `0, 0`, and `h 0 + 0 = 0 ≠ 5`. The hypothesis
  is now finiteness of every intermediate value (weaker than convexity; for convex `h` it follows
  from L1.5). SURVIVED after correction — **skeleton edit recorded in the Gate section**.

- **L1.23** `affineFrom` / `isConvexSeq_affineFrom` (helper) — the affine sequence of slope `s`
  through `(i₀, y)`, `⊤` before `i₀`: the basic convex minorant of a sequence whose first point is
  `(i₀, y)` (L2.13) and the base of the steepened competitors (L2.15). Discharge: finiteness set
  `Set.Ici i₀` (`Set.ordConnected_Ici`), constant unit slope on it. Attacks: [2] `i₀ = 0`: the
  affine sequence L1.12 ✓. [3] none. SURVIVED.

- **L1.24** `IsConvexSeq.extend_affine` (helper) — a convex sequence cut at a finite index `n` and
  continued affinely with slope `M ≥` every earlier finite unit slope is convex. This is [SRC]
  `Face.height_eq_top_of_forall_eq_top`'s "steep line" competitor, made reusable (L2.4, L4.14).
  Discharge: finiteness set = (finiteness set of `h`) ∩ `Iic n` ∪ `Ioi n`, order-connected as the
  union of an interval ending at `n` and `Ioi n`; unit slopes: those of `h` below `n`, then `M`.
  Attacks: [2] `n = anchor h` (cut at the first point): slopes are just the constant `M` ✓. [3] `hM`
  is necessary: continuing with a slope below the last unit slope breaks monotonicity ✓; `hn`
  necessary (cutting at a `⊤` index leaves a gap). SURVIVED.

---

## §0.2 The Newton polygon of a sequence (`Basic.lean`)

### Plain-English proof substrate

[Ked07, §1], verbatim: *"Then form the lower convex hull of these points, i.e., take the
intersection of every closed halfplane lying above some nonvertical line containing all the points.
The boundary of this region is called the Newton polygon of P."* The intersection of the halfplanes
above the affine minorants is the region above the supremum of the affine minorants; the roadmap
takes the supremum of the *convex* minorants, which is the same function because every convex
minorant is below the polygon (`greatest`) and the polygon is above every affine minorant
(`line_le`, §0.5). So `newtonPolygon v k = ⨆ g, g k` over convex minorants `g` is the definition.

Uniqueness: two functions each `greatest` among convex minorants are each `≤` the other.
Existence: the supremum is convex (L1.16), `≤ v` (each `g ≤ v`), greatest (`le_ciSup`); at the
first point `i₀` the admissible line through `(i₀, v i₀)` is a convex minorant, so the supremum is
`≥ v i₀` there, hence `= v i₀`; before `i₀`, and past the last point, the admissible line can be
steepened arbitrarily (down-left, up-right) while remaining a convex minorant, so the supremum is
`⊤`. Admissibility is necessary: [SRC] `SpecConstruction` docstring, verbatim: *"`IsAdmissible v` —
every slope set is bounded below. Without it no polygon lies below the points at all (e.g.
`v k = -k²` over `Γ = ℝ`): the hull 'is vertical'."*

### Leaves

- **L2.1** `IsNewtonPolygonOf.unique` — [RM] §0.2.2. Discharge: `funext k; exact le_antisymm
  (h₂.greatest h h₁.convex h₁.le_points k) (h₁.greatest g h₂.convex h₂.le_points k)`. Attacks:
  [2] any `v` ✓ (no hypotheses on `v`). [3] uses only `convex`, `le_points`, `greatest` — the
  `anchor_eq` and `eq_top…` fields are not needed for uniqueness, as [RM] §0.2.1 intended ("each
  can be used alone"). [4] [SRC] `Spec.height_eq` needed the anchoring hypothesis; ours does not,
  because of decision 2. SURVIVED. (3 lines.)

- **L2.2** `IsNewtonPolygonOf.ne_top_of_ne_top` — `le_points` + `ne_top_of_le_ne_top`. SURVIVED.

- **L2.3** `IsNewtonPolygonOf.ne_top_of_le_of_le` — L2.2 at `a` and `b`, then
  `hh.convex.ordConnected.out`. Attacks: [2] `a = k = b` ✓. SURVIVED.

- **L2.4** `IsNewtonPolygonOf.eq_top_of_forall_le` — [RM] §0.3.2 "`h` is `⊤` beyond the last point"
  and [SRC] `Face.height_eq_top_of_forall_eq_top`, docstring verbatim: *"a steep line through a
  finite height at `n`, raised by `1`, would lie below every point."* Sketch (steepened
  competitor): suppose `h n ≠ ⊤`. If no point precedes `n`, `eq_top_of_forall_eq_top` at `n`
  contradicts. Else let `g := fun k ↦ if k < n then h k else h n + (k - n) • M` for a real `M`
  larger than every finite unit slope of `h` below `n` (finitely many; take `M := untop₀ (unitSlope
  h (n-1)) + 1`, using monotonicity) — `g` is convex (unit slopes of `h` below `n`, then constant
  `M ≥` them), and `g ≤ v` (equal to `h` below `n`, and `v = ⊤` from `n` on); so `g ≤ h` by
  `greatest`, giving `h n + M ≤ h (n+1)`, and iterating `h (n+1) ≤ … `; but also `h (n+1) ≤ v (n+1)
  = ⊤` is no constraint — contradiction comes instead from convexity of `h` at `n`: `unitSlope h n
  ≥ M` for every such `M`, impossible for a real. Cleaner: take `g n := h n + 1` only (bump at `n`
  and steep afterwards); then `g ≤ h` forces `h n + 1 ≤ h n`, contradiction. Attacks: [2] `n = 0`
  with `v ≡ ⊤`: the field gives `h 0 = ⊤` ✓. [2'] `n` = last point + 1: `g` as above ✓. [3] the
  hypothesis "no point at or after `n`" is exactly what makes `g ≤ v` there; with a point at `n`
  the claim is false (`h n = v n ≠ ⊤`) ✓ sharp. SURVIVED. **Helper worth declaring**: convexity of
  "convex minorant, then affine with a larger slope" — recorded as skeleton addition
  `IsConvexSeq.extend_affine_of_le` (Gate section).

- **L2.5** `isAdmissible_iff_bddBelow` — [RM] §0.2.3 "equivalently, that the slopes … are bounded
  below". Sketch: `→`: `s` bounds `slopeSet v i` below (rearrange `v i + (k-i) s ≤ v k` to
  `s ≤ slopeTo v i k`, division by `k - i > 0`). `←`: take `s := sInf (slopeSet v i)` if nonempty
  (`csInf_le` for each `k`), any `s` if empty. Attacks: [2] `slopeSet = ∅` (no later point): `∃ s`
  trivially, `BddBelow ∅` ✓. [3] `v i ≠ ⊤` guard needed on both sides (junk `untop₀`). [5]
  `csInf_le`, `le_csInf` verified. SURVIVED.

- **L2.6** `isAdmissible_of_line` — points above one line ⇒ admissible: from `y + σ k ≤ v k` for all
  `k`, at each finite `i`: `v i + (k-i) σ ≤ v k`? Not directly — `v i` may exceed `y + σ i`. Use
  `s := σ`: `v i + (k - i) σ ≤ v k` needs `v i ≤ y + σ i + …` ✗. **Attack [2] succeeds as
  sketched**: `v = (5, 0, 0, …)` lies above `y = -1, σ = 0`, but from `i = 0`, `v 0 + (k) • 0 = 5 ≰ 0`.
  The *statement* is still true (`IsAdmissible` needs *some* `s` per `i`, and `s := σ - (v i - y -
  σ i)` — no: slopes from `(i, v i)` to `(k, v k)` are `≥ (y + σ k - v i)/(k - i) → σ` and are
  bounded below by `min` over the finitely many `k ≤ i + N` and the tail bound). Correct sketch:
  `slopeTo v i k ≥ (y + σ k - v i)/(k - i) = σ - (v i - y - σ i)/(k - i) ≥ σ - |v i - y - σ i|`
  for `k ≥ i + 1`; so `BddBelow (slopeSet v i)` with bound `σ - |v i - y - σ i|`, then L2.5.
  Attacks after fix: [2] `v = (5,0,0,…)`, `i = 0`: slopes `-5, -5/2, …` bounded below by `-5` ✓.
  SURVIVED with corrected sketch (statement unchanged).

- **L2.7** `IsNewtonPolygonOf.isAdmissible` — [RM] §0.2.3 "IsNewtonPolygonOf v h … implies
  IsAdmissible v"; [SRC] `SpecConstruction.IsNewtonPolygonOf.bddBelow` docstring: *"slopes out of
  the starting vertex are bounded below by the first unit slope."* Sketch: at a finite `i`, `h i`
  finite (L2.2); if `unitSlope h i = ⊤` there is no later point, any `s`; else with `s := untop₀
  (unitSlope h i)`, `v k ≥ h k ≥ h i + (k - i) • s` (L1.9) — but `h i ≤ v i` may be strict (`i`
  need not be a vertex), so the line through `(i, v i)` of slope `s` need **not** lie below the
  points. **Attack [2] on the naive route succeeds** (`v = (0, 5, 2)`: `h = (0, 1, 2)`, at `i = 1`,
  `s = 1`, but `v 1 + 1 = 6 > v 2 = 2`). Correct route: the slope-set form L2.5 — `slopeTo v i k ≥
  (h k - v i)/(k - i) ≥ s - (v i - h i)/(k - i) ≥ s - (v i - h i)`, a lower bound. Attacks after
  fix: [2] the example: slopes from `1` are `-3`, bounded ✓. [3] only `convex` and `le_points` are
  used. SURVIVED with corrected sketch (statement unchanged; T009 carries the corrected route).

- **L2.8** `not_isAdmissible_neg_sq` — [RM] §0.2.3 and [SRC] quote above. Sketch: at `i = 0`, any
  `s` fails at `k > max 0 (-s)`: `0 + k s ≤ -k²` iff `s ≤ -k`, false for `k > -s`. Attacks: [2]
  numeric ✓. SURVIVED.

- **L2.9** `not_exists_isNewtonPolygonOf_neg_sq` — L2.7 + L2.8. SURVIVED.

- **L2.10** `le_newtonPolygon` — `le_ciSup (OrderTop.bddAbove _) ⟨g, hg⟩`. Verified by the probe
  (exact term). SURVIVED.

- **L2.11** `newtonPolygon_le` — `ciSup_le fun g ↦ g.2.2 k` with `Nonempty` from `hne`. Attacks:
  [3] `hne` necessary: empty family gives junk `sSup ∅`, not `≤ v k` in general — sharp ✓.
  SURVIVED.

- **L2.12** `isConvexSeq_newtonPolygon` — L1.16 with `ι := {g // IsConvexMinorant v g}`, nonempty
  from `hne`. SURVIVED.

- **L2.13** `exists_isConvexMinorant` — the admissible line through the first point, extended by
  `⊤` before it: `g k := if k < i₀ then ⊤ else v i₀ + (k - i₀) • s`. Convex: finiteness set
  `[i₀, ∞)` order-connected, unit slopes constant `s` (and `⊤` before `i₀`, outside the set).
  `≤ v`: before `i₀` trivially (`v = ⊤`... no — `g = ⊤ ≤ v k` needs `v k = ⊤`, true since `i₀` is
  the first point), from `i₀` by admissibility. Attacks: [2] `i₀ = 0` ✓. [3] both hypotheses
  necessary. SURVIVED. (**Helper**: this `g` is also the base of the steepened competitors; declare
  `affineFrom i₀ y s` as a `def` with `isConvexSeq_affineFrom` — Gate section.)

- **L2.14** `newtonPolygon_anchor` — `le_antisymm (newtonPolygon_le …) (le_newtonPolygon (L2.13's g))`
  at `i₀`, where `g i₀ = v i₀`. SURVIVED.

- **L2.15** `newtonPolygon_eq_top_of_forall_eq_top` — steepened to the left: for real `M`, the
  minorant `g_M k := if k < i₀ then v i₀ + (k - i₀) • (-M) … ` — careful, `(k - i₀)` truncates in
  `ℕ`; write the left branch as `v i₀ + (i₀ - k) • M` (larger for larger `M`, since `i₀ - k > 0`).
  Convex: slopes `-M` then `s` with `-M ≤ s` for `M ≥ -s`; `≤ v` since `v = ⊤` left of `i₀`. Then
  `newtonPolygon v k ≥ v i₀ + (i₀ - k) • M` for all large `M`, so `= ⊤` by
  `WithTop.eq_top_iff_forall_gt` (verified). Attacks: [2] `k = i₀ - 1` ✓; `i₀ = 0`: hypothesis
  `∀ j ≤ k, v j = ⊤` contradicts `v 0 ≠ ⊤` unless no `k`, vacuous ✓. SURVIVED.

- **L2.16** `isNewtonPolygonOf_newtonPolygon` — assembly of L2.12 (`convex`), L2.11 (`le_points`),
  L2.10 (`greatest`), L2.14 (`anchor_eq`), L2.15 (`eq_top_of_forall_eq_top`). One-line
  constructor — an assembly node in the sense of `statement-splitting.md`. SURVIVED.

- **L2.17** `IsNewtonPolygonOf.eq_newtonPolygon` — L2.1 with L2.16 (admissibility from L2.7, a
  point from `anchor_eq`… no: a point is needed; from `hh`, if `v ≡ ⊤` then `h ≡ ⊤` by the field
  and `newtonPolygon v` is junk — **attack [2] succeeds**: for `v ≡ ⊤`, `IsNewtonPolygonOf v (⊤)`
  holds (all fields vacuous/true: convex ✓, `⊤ ≤ ⊤` ✓, greatest: `g ≤ ⊤` ✓, anchor vacuous ✓,
  `eq_top` ✓) but `newtonPolygon v = sSup ∅`-junk `≠ ⊤` possibly. FIX: add hypothesis
  `(hv' : ∃ i, v i ≠ ⊤)` to `eq_newtonPolygon`, and correspondingly `exists_isNewtonPolygonOf_iff`
  is fine as stated (its RHS includes `∃ i, v i ≠ ⊤`; its `→` direction must produce a point from
  the spec: from `IsNewtonPolygonOf v h` with `v ≡ ⊤` we get `h ≡ ⊤` and no contradiction — so the
  `→` direction is **false** for `v ≡ ⊤`!). FIX both: `exists_isNewtonPolygonOf_iff` becomes
  `(∃ h, IsNewtonPolygonOf v h) ↔ IsAdmissible v` (admissibility of `v ≡ ⊤` is vacuous ✓, and
  `⊤` witnesses the spec ✓; for `v` with a point, L2.16). Re-attack: `v ≡ ⊤`: LHS true (`h = ⊤`),
  RHS true ✓; `-k²`: both false ✓; admissible with a point: both true ✓. SURVIVED after correction
  — **skeleton edit required**: drop `∃ i, v i ≠ ⊤` from the RHS of `exists_isNewtonPolygonOf_iff`
  (and from `isNewtonPolygonOf_newtonPolygon`? no — there the definition needs a nonempty family;
  keep `hv'` there) and add `hv'` to `eq_newtonPolygon`. Recorded in the Gate section.

- **L2.18** `newtonPolygon_add_affine`, **L2.19** `newtonPolygon_add_const`, **L2.20**
  `newtonPolygon_mono` — [RM] §0.2.5. Sketch: L2.18: `g ↦ g + ℓ` is a bijection between convex
  minorants of `v` and of `v + ℓ` (L1.14 both ways), and `⨆ (g + ℓ) = (⨆ g) + ℓ` in `WithTop ℝ`
  — **by both inequalities** via `le_ciSup`/`ciSup_le` rather than an `iSup_add` lemma (none
  verified for `WithTop ℝ`). L2.19 = L2.18 at `σ = 0`. L2.20: every convex minorant of `v` is one
  of `w`, so `le_newtonPolygon` + `ciSup_le`. Attacks: [3] L2.20 needs `hne` for `v` (junk
  otherwise) ✓ present via `hv, hv'`. SURVIVED.

---

## §0.4 Slopes, vertices, segments and the slope multiset (`Slope.lean`)

### Plain-English proof substrate

[Kob84, §IV.3 p. 97], verbatim (as quoted in [SRC] `Face.lean`): *"By the vertices of the Newton
polygon we mean the points `(i_j, ord_p a_{i_j})` where the slopes change."* A vertex is where the
unit slope strictly increases (or the anchor); the polygon is affine between consecutive vertices,
and every vertex is a point of the sequence: if the polygon sat strictly below the point at a vertex,
raising it there by a small amount would keep it convex (the slopes strictly increase there, so
there is room) and below the points, contradicting maximality. [Ked07, §1], verbatim: *"form the
multiset consisting of the slopes of the polygon, each occurring with multiplicity equal to the
width of the corresponding segment"* — the slope multiset is the multiset of unit slopes.

### Leaves

- **L4.1** `anchor_mem`, **L4.2** `anchor_le`, **L4.3** `eq_top_of_lt_anchor` — `Nat.sInf_mem`,
  `Nat.sInf_le`, `Nat.not_mem_of_lt_sInf` (all standard; `Nat.not_mem_of_lt_sInf` to be
  loogled — fallback `Nat.sInf_le` contrapositive). Attacks: [2] `h ≡ ⊤`: `anchor = 0` junk,
  L4.1's hypothesis fails, L4.3 vacuous ✓. SURVIVED.

- **L4.4** `IsNewtonPolygonOf.anchor_eq_sInf` — `h` finite exactly where `v` first is: at `i₀ :=
  sInf (finiteSet v)`, `anchor_eq` gives `h i₀ = v i₀ ≠ ⊤`; below `i₀`, `eq_top_of_forall_eq_top`
  gives `⊤`; so `anchor h = i₀` by `le_antisymm` with L4.2/L4.3. SURVIVED.

- **L4.5** `isVertex_anchor` — `⟨anchor_mem, Or.inl rfl⟩`. **L4.6** `isVertex_of_succ_eq_top` — if
  `k = anchor h`, done; else `anchor h < k`, so `h (k-1) ≠ ⊤` (order-connected between anchor and
  `k`), `unitSlope h (k-1)` is a real `< ⊤ = unitSlope h k`. Attacks: [2] one-point polygon: `k =
  anchor` ✓ (this is the prior-B2 shape — the one-point polygon is a vertex and nothing else, with
  no phantom slope). SURVIVED.

- **L4.7** `IsNewtonPolygonOf.eq_of_isVertex` — [RM] §0.4.1; [SRC] `Face.height_eq_pointHeight_of_
  unitSlope_lt`, docstring verbatim: *"where the unit slope strictly increases, the polygon's
  height is the point's height — otherwise a slightly raised supporting line would still lie below
  every point."* Sketch (bump competitor, simpler than the source's margin lemma): case `k =
  anchor h`: `anchor_eq` (after L4.4). Case `unitSlope h (k-1) < unitSlope h k`: both
  `h (k-1), h k` finite; if `unitSlope h k = ⊤` (last index) and `v k = ⊤`, then no point at or
  after `k`, so `h k = ⊤` by L2.4 — contradiction; so either `v k ≠ ⊤` or `unitSlope h k` finite.
  Let `ε > 0` with `2ε ≤ s_k - s_{k-1}` (or any `ε` if `s_k = ⊤`) and `ε ≤ v k - h k` if `v k`
  finite. `g := Function.update h k (h k + ε)` is convex (unit slopes `s_{k-1} + ε ≤ s_k - ε`,
  neighbours unchanged) and `≤ v`, so `g k ≤ h k` by `greatest`: `h k + ε ≤ h k`, contradiction
  unless `h k = v k` was already forced (the `ε ≤ v k - h k` bound is vacuous exactly when
  `h k = v k`). Attacks: [2] `k` the last index with `v k ≠ ⊤`: bump with any `ε ≤ v k - h k` ✓.
  [2'] interior `k` with `v k = ⊤`: the argument derives `False` — an interior vertex is always a
  point, consistent. [3] `IsVertex` is the right hypothesis: without strictness (`s_{k-1} = s_k`)
  the bump breaks convexity and the conclusion is false (`(0,1,2,4)` at `k = 1`: `h 1 = v 1`
  happens to hold, but `(0, ⊤, 2)` at `k = 1`: `h 1 = 1 ≠ ⊤ = v 1`) ✓. SURVIVED.

- **L4.8** `IsConvexSeq.unitSlope_eq_of_isSegment` — induction from `a`: `unitSlope h (j+1) ≥
  unitSlope h j` (monotone; all of `h j, h (j+1), h (j+2)` finite as `j+2 ≤ b`), and strict would
  make `j+1` a vertex in `(a, b)`. Attacks: [2] `b = a + 1` ✓ vacuous induction. SURVIVED.
- **L4.9** `IsConvexSeq.eq_add_nsmul_of_isSegment` — L4.8 + `eq_add_nsmul_of_forall_unitSlope_eq`.
  SURVIVED.

- **L4.10** `IsConvexSeq.slopeIndices_eq_Ico` — unit slope finite iff both ends finite iff
  `anchor ≤ j < last`; finiteness of `slopeIndices` forces a last index (else every `j ≥ anchor`
  carries a finite slope, infinitely many). Attacks: [2] one-point: `∅ = Ico a a` ✓. SURVIVED.
- **L4.11** `card_slopeMultiset` — `Multiset.card_map`, `Set.ncard_eq_toFinset_card'`. **L4.12**
  `count_slopeMultiset` — `Multiset.count_map` gives the card of the filter `σ = untop₀ (unitSlope
  h j)` over `slopeIndices`; on `slopeIndices`, `untop₀ s = σ ↔ s = ↑σ`, and off it `s = ⊤ ≠ ↑σ`,
  so the filter is `{j | unitSlope h j = σ}` (finite). Attacks: [2] `σ` not a slope: `0 = 0` ✓.
  SURVIVED.
- **L4.13** `IsConvexSeq.anchor_add_sum_slopeMultiset` — `eq_add_sum_unitSlope` over `Ico anchor
  last`, with L4.10 identifying the multiset sum with the `Finset.sum`. Attacks: [2] one-point:
  `h a + 0 = h (a + 0)` ✓. SURVIVED.
- **L4.14** `IsNewtonPolygonOf.slopeIndices_finite` — L2.4 makes `h = ⊤` past the last point, so
  `slopeIndices h ⊆ Set.Iio (last + 1)`, `Set.finite_Iio.subset`. Attacks: [2] `v ≡ ⊤`: `h ≡ ⊤`,
  `slopeIndices = ∅` ✓. SURVIVED.

- **L4.15** `isPure_iff_slopeMultiset` — `Multiset.eq_replicate` (every element `= m` and the card),
  nonemptiness `↔ 0 < card`. SURVIVED.

- **L4.16** `IsNewtonPolygonOf.hasFirstBreak_iff` — [RM] §0.4.4, **corrected** (see the skeleton
  docstring and the Gate section). `→`: unit slopes from the anchor are `≥ m` (first `l` equal `m`,
  then `unitSlope (anchor + l) ≠ m` so `> m` or `⊤`), giving the line bound by L1.9 and
  `le_points`; `anchor + l` is a vertex (strict increase, or last index), so `h = v` there (L4.7)
  and `h (anchor + l) = h anchor + l • m` (affine, L1.11); the steeper line: `m' :=
  untop₀ (unitSlope h (anchor + l))` if finite (then `v k ≥ h k ≥ h (anchor+l) + (k - anchor - l) • m'`
  by L1.9), else (`⊤`, no later points) any `m' > m` vacuously. `←`: `affineFrom anchor (v anchor) m`
  is a convex minorant (L2.13's `g`), so it is `≤ h ≤ v`; equality at `anchor` and at `anchor + l`,
  hence (chord, L1.8) `h` is the line on `[anchor, anchor + l]`: first `l` unit slopes `= m`. For
  the break: the two-slope competitor `m` on `[anchor, anchor+l]`, then `m'` (convex as `m ≤ m'`,
  `≤ v` by the hypotheses) is `≤ h`, so `unitSlope h (anchor + l) ≥ m' > m`. Attacks: [2] the
  asymptotic example `v k = m k + 1/k` (`k ≥ 1`), `v 0 = 0`: old RHS held, new RHS fails (no
  `m' > m` works since slopes `→ m`) ✓ and `HasFirstBreak` is false ✓ — consistent. [2'] a genuine
  break `(0, 1, 2, 4)` with `m = 1, l = 2`: `m' = 2` works ✓. [4] **roadmap drift**: [RM] §0.4.4
  states the characterisation without the steeper line; the Lean statement is the correct one and
  the roadmap text needs the same amendment (flagged for the user; not edited here). SURVIVED
  after correction.

- **L4.17** `newtonPolygon_le_newtonPolygon_truncate` — L2.20 with `w := truncate v n ≥ v`.
  SURVIVED. **L4.18** `newtonPolygon_truncate_eq` — `≥` is L4.17; `≤`: `newtonPolygon (truncate v
  n)` is a convex minorant of `truncate v n = v` on `[0, n]`, so at every vertex `W ≤ V` of
  `newtonPolygon v` (which are points, L4.7, and `≤ n`) it is `≤ v W = newtonPolygon v W`; between
  consecutive vertices `newtonPolygon v` is the chord (L4.9) and the truncated polygon is below its
  own chord (L1.8) hence below it; before the anchor both are `⊤`. Attacks: [2] `V = anchor`: only
  the anchor, equality there ✓. [3] the former `hlast` hypothesis was unnecessary — dropped
  (strengthening). SURVIVED.

---

## §0.3 Existence by construction (`Construction.lean`)

### Plain-English proof substrate

[SRC] `SpecConstruction` docstring, verbatim: *"The proof of `height_le` ("below the points") is the
segment-by-segment line bound … The proof of `isGreatest` is the chord argument: a competitor is
convex (`heightFun_chord`), sits below the points, and the constructed polygon touches the points at
its vertices, so on each segment the competitor is below its own chord, which is below the
constructed segment; final rays are handled by an ε-approximation along slopes tending to the
infimum."* The walk: from the current vertex take the infimum of the slopes to the later points
(bounded below by admissibility) and move to the furthest point achieving it; the next minimal slope
is strictly larger (a later point on the same line would have achieved the old one). The walk is
affine between consecutive vertices and touches the points there; a convex minorant is below the
points at the vertices and below its chords between them, hence below the walk; on a final ray the
chords to far points approximate the ray within any `ε`. Uniqueness then identifies the walk with
`newtonPolygon`.

### Leaves

- **L3.1** `lt_of_nextVertex_eq`, **L3.2** `ne_top_of_nextVertex_eq`, **L3.3** `slopeTo_nextVertex`
  — `Finset.max'_mem` puts `j` in `achievingSet v i`, which carries `i < j`, `v j ≠ ⊤`, and the
  slope equation. Attacks: [2] `achievingSet = ∅`: `nextVertex = ⊤ ≠ ↑j`, hypotheses false ✓.
  SURVIVED.
- **L3.4** `sInf_slopeSet_lt_slopeTo_of_nextVertex_lt` — `k > j = max'` so `k ∉ achievingSet`, i.e.
  `slopeTo v i k ≠ sInf`; and `sInf ≤ slopeTo v i k` by L3.5. Attacks: [3] **`hv` is necessary**:
  for inadmissible `v`, `sInf` of an unbounded set is junk and a spurious `achievingSet` element
  could exist; the hypothesis was added by the adversarial pass. SURVIVED after correction.
- **L3.5** `sInf_slopeSet_le_slopeTo` — `csInf_le` with `BddBelow` from `isAdmissible_iff_bddBelow`.
  SURVIVED.
- **L3.6** `sInf_slopeSet_lt_sInf_slopeSet_nextVertex` — [SRC] `Construction.slopes_increasing_
  nextVertex` (strict). Let `m := sInf (slopeSet v i)`, `j = nextVertex v i`. For `k > j` with
  `v k ≠ ⊤`: `slopeTo v i k > m` (L3.4) and `v j = v i + (j - i) m` (L3.3), so `slopeTo v j k =
  (v k - v j)/(k - j) > m` by the two-point computation (`(v k - v i) > (k - i) m` and `(v j - v i)
  = (j - i) m`). Hence `m < sInf (slopeSet v j)` — **strictness**: `le_csInf` gives `≤`; for `<`
  the infimum over `k > j` of `slopeTo v j k` is attained or approached; if approached with limit
  `m`, then `slopeTo v i k → m` from above along `k → ∞` … but the points `k` would then have
  `slopeTo v i k` arbitrarily close to `m` with `k > j`, which does not contradict `j` being the
  furthest *achiever*. **Attack [2] succeeds against strictness**: `v 0 = 0`, `v 1 = 1`, `v k =
  k + 1/k` for `k ≥ 2`: `slopeSet 0` has infimum `1` attained only at `k = 1` (slopes `1, 1.25,
  1.11, …` all `> 1` beyond), so `nextVertex 0 = 1`; from `1`: `slopeTo 1 k = (k + 1/k - 1)/(k-1)
  = 1 + 1/(k(k-1)) → 1`, infimum `1`, not attained: `sInf (slopeSet v 1) = 1 = sInf (slopeSet v
  0)`. **Strictness is false**; the source's strict lemma is for the case where the next step is
  again a `nextVertex` (attained), which is exactly when it holds (`slopes_increasing_limitingRay`
  in [SRC] is `≤`, `slopes_increasing_nextVertex` is `<` — the source distinguishes them). FIX:
  revert to `≤` as the general statement, and add the strict form under the extra hypothesis that
  the next step is attained (`nextVertex v j ≠ ⊤`) — `sInf_slopeSet_lt_sInf_slopeSet_nextVertex
  (hj') (hj'' : nextVertex v j ≠ ⊤)`. For `isVertex_iff_exists_vertexSeq` the strict form is only
  needed at vertices followed by another vertex; a vertex followed by a ray of the *same* slope is
  not a vertex of the polygon (the slope does not change there) — so the `←` direction of
  `isVertex_iff_exists_vertexSeq` is **also false** in that example: `vertexSeq v 1 = 1` but the
  polygon `h = k` (the line) has no vertex at `1`. FIX: `isVertex_iff_exists_vertexSeq` must exclude
  this: state `→` only (`IsVertex → ∃ n, vertexSeq v n = i`), and `←` under `nextVertex v i ≠ ⊤`
  or `i = anchor`. **Skeleton edits recorded in the Gate section.** SURVIVED after correction.

- **L3.7** `vertexSeq_zero`, **L3.8** `vertexSeq_succ_of_eq` (`WithTop.recTopCoe_coe`), **L3.9**
  `vertexSeq_eq_top_of_le` (induction, `recTopCoe_top`), **L3.10** `vertexSeq_lt` (L3.1), **L3.11**
  `ne_top_of_vertexSeq_eq` (`n = 0`: `Nat.sInf_mem`; succ: L3.2). Attacks: [2] `v ≡ ⊤`: `vertexSeq
  0 = ⊤`, so hypotheses of L3.10/L3.11 false ✓. SURVIVED.

- **L3.12** `vertexWalk_eq_of_vertexSeq_eq` — `lastVertex v i = i` (`Nat.sSup_mem` of the set of
  vertices `≤ i`, which contains `i` and is bounded by `i`); the outer `if` is false (`v i ≠ ⊤` and
  `i ≥ sInf (finiteSet v)`), the inner is true by `k = lastVertex`, and `0 • _ = 0`. SURVIVED.
- **L3.13** `vertexWalk_eq_of_le_of_le` — for `i ≤ k < j`, `lastVertex v k = i` (vertices are
  strictly increasing, L3.10, so those `≤ k` are `≤ i`); for `k = j`, `lastVertex = j` and `v j =
  v i + (j - i) • m` by L3.3 (untop arithmetic). Attacks: [2] `k = i` ✓ `0 • m`. SURVIVED.
- **L3.14** `vertexWalk_le` — `k < anchor`: `⊤ ≤ v k = ⊤`; `k = lastVertex`: `v k ≤ v k`; `k >
  lastVertex =: i` with `slopeSet v i` nonempty: `v i + (k - i) • sInf ≤ v k` by L3.5 if `v k ≠ ⊤`,
  else `≤ ⊤`; with `slopeSet v i = ∅`: `vertexWalk = ⊤` and `v k = ⊤` (no point after `i`).
  SURVIVED.
- **L3.15** `isConvexSeq_vertexWalk` — finiteness set `[anchor, last]` or `[anchor, ∞)` (order-
  connected); `unitSlope (vertexWalk v) k = sInf (slopeSet v (lastVertex v k))` on the finite
  region (L3.13), `lastVertex` is monotone in `k`, and `sInf (slopeSet v ·)` is monotone along
  `vertexSeq` by the **`≤` form** of L3.6 (the strict form is not needed here — this is why the
  `≤` statement must stay). SURVIVED (~80 lines).
- **L3.16** `le_vertexWalk_of_isConvexMinorant` — the chord argument above. Segment `[i, j]` (L3.13):
  `g i ≤ v i`, `g j ≤ v j`, `g` convex, so `g k ≤` chord (L1.8 in real form) `= vertexWalk v k`.
  Ray from `i` with `nextVertex v i = ⊤` and `slopeSet v i` nonempty: for `ε > 0` there is `k' > k`
  with `slopeTo v i k' < m + ε` ([SRC] `limitingRay_exists_slope_lt`: only finitely many points lie
  at or below `k`, each with slope strictly above the unattained infimum, so their minimum exceeds
  `m` by some `δ`; taking `ε < δ`, a witness within `ε` of `m` lies beyond `k`) — or an achieving
  `k' > k` if infinitely many points achieve `m`; then `g k ≤` chord to `k'` `≤ v i + (k - i)(m +
  ε)`, and `le_of_forall_pos_le_add`. Dead end (`slopeSet v i = ∅`, `k > i`): `vertexWalk = ⊤`.
  Attacks: [2] `g ≡ ⊤`… `g ≤ v` fails unless `v ≡ ⊤` ✓ excluded by `hv'`. SURVIVED (~120 lines).
- **L3.17** `isNewtonPolygonOf_vertexWalk` — assembly: L3.15, L3.14, L3.16, `anchor_eq` from L3.12
  at `n = 0`, `eq_top_of_forall_eq_top`: `k` with no point at or before it is `< anchor`, where the
  walk is `⊤`. SURVIVED. **L3.18** `vertexWalk_eq_newtonPolygon` — L3.17 + `eq_newtonPolygon`
  (with `hv'`). SURVIVED.
- **L3.19** `isVertex_iff_exists_vertexSeq` — **corrected** per L3.6: `→` (a polygon vertex is a
  walk vertex): the walk's unit slope is constant between consecutive walk vertices (L3.13), so a
  strict increase at `i` forces `i ∈ vertexSeq` (or `i = anchor = vertexSeq 0`). `←` only under
  `nextVertex v i ≠ ⊤ ∨ i = anchor`: then the slope strictly increases at `i` (strict L3.6) or `i`
  is the anchor. Skeleton: split into `exists_vertexSeq_of_isVertex` and
  `isVertex_of_vertexSeq_eq (hnext : nextVertex v i ≠ ⊤)`. SURVIVED after correction.
- **L3.20** `newtonPolygon_eq_top_of_slopeSet_eq_empty`, **L3.21** `newtonPolygon_eq_ray` — read
  off `vertexWalk` (L3.18, L3.13/dead-end case). SURVIVED.
- **L3.22** `iSup_unitSlope_eq_of_ray` — the unit slopes from the anchor are `≤ m` (monotone, and
  equal to `m` on the ray), and equal `m` from `i` on: `le_antisymm (ciSup_le …) (le_ciSup … j₀)`.
  Attacks: [2] `i = anchor` (ray from the start): all unit slopes `= m` ✓. SURVIVED.
- **L3.23** `exists_vertexSeq_eq_top` — `vertexSeq` is strictly increasing while finite (L3.10) and
  bounded by `last` (vertices are points), so it is `⊤` by step `last + 1` (pigeonhole /
  `Nat.lt_irrefl` after `last + 1` strict increases). SURVIVED. **L3.24** `vertexSeq_eq_sSup_
  finiteSet` — with finitely many points every nonempty `slopeSet v i` has its infimum attained by
  finitely many points (`Set.Finite` of the achieving set), so `nextVertex v i = ⊤` forces
  `slopeSet v i = ∅`, i.e. no point after `i`: `i = sSup (finiteSet v)` (`Nat.sSup_mem`, and `i ≤
  sSup`, `sSup ≤ i` since no point exceeds `i`). SURVIVED.

---

## §0.5 Supporting lines, faces, and the competitor lemma (`Face.lean`)

### Plain-English proof substrate

[Ked07, §2], verbatim: *"For `r ∈ ℝ`, define the sloped valuation function `v_r` on `F{T}` as
`v_r(Σ P_i T^i) = min_i {v(P_i) + ri}`. That is, `v_r` is the `y`-intercept of the supporting line
of the Newton polygon of slope `r`."* A line below all the points is a convex minorant, hence below
the polygon (`greatest`) — the supporting-line lemma; a two-slope broken line with increasing slopes
is convex, so the same argument gives the competitor lemma. From convexity alone, the line of slope
`σ` through `(n, h n)` is below `h` exactly when `σ` separates the unit slopes at `n`. [Ked07, proof
of Cor. 2], verbatim: *"the left and right endpoints of the segment of slope `r` in the Newton polygon
are the points where the support lines of slightly smaller and slightly larger slope, respectively,
touch the polygon"* — so the face of slope `σ` runs from the first unit interval of slope `≥ σ` to
the first of slope `> σ`, and its width is the multiplicity of `σ`.

### Leaves

- **L5.1** `IsNewtonPolygonOf.line_le` — `hh.greatest _ (isConvexSeq_affine y σ) hle k`. One line.
  Attacks: [3] none to weaken. [4] this is [Ked07]'s `v_r` statement in height form. SURVIVED.
- **L5.2** `isConvexSeq_twoSlope` — unit slopes `σ` for `j < N`, `τ` for `j ≥ N` (`min`/`max`
  arithmetic, `ring_nf`), monotone since `σ ≤ τ`; finiteness set `univ`. Attacks: [2] `N = 0`:
  constant slope `τ` ✓; `σ = τ`: affine ✓. SURVIVED.
- **L5.3** `IsNewtonPolygonOf.twoSlope_le` — `greatest` with L5.2. SURVIVED. ([SRC]
  `Support.twoSlope_le_height` is the same statement with `⊥`-hypotheses we no longer need.)
- **L5.4** `IsConvexSeq.line_le_iff` — `→`: evaluate the line inequality at `n - 1` (if finite) and
  `n + 1`, rearrange to `unitSlope h (n-1) ≤ σ ≤ unitSlope h n`, extend by monotonicity. `←`: for
  `k ≥ n`, `h k ≥ h n + (k - n) • σ` (L1.9-style sum with each slope `≥ σ`); for `k < n` finite,
  `h k ≥ h n - (n - k) σ` (slopes `≤ σ` on `[k, n)`); for `k < n` with `h k = ⊤` trivial. Attacks:
  [2] `n = anchor`: left clause vacuous ✓; `n` the last finite index: `unitSlope h n = ⊤ ≥ σ` ✓.
  [3] the guard `h j ≠ ⊤` on the left clause is necessary (unit slopes before the anchor are `⊤`,
  not `≤ σ`); found by the attack on the prototype's global-monotonicity claim. SURVIVED.
- **L5.5** `IsConvexSeq.line_lt_of_unitSlope_lt`, **L5.6** `IsConvexSeq.line_lt_of_lt_unitSlope` —
  the strict sums; for L5.6 the case `h k = ⊤` is `WithTop.coe_lt_top`. Attacks: [2] `k = n ± 1`:
  single strict term ✓. SURVIVED.

- **L5.7** `slopesUnbounded_of_finite` — `slopeIndices h` finite ⇒ some `j` with `unitSlope h j =
  ⊤ > σ` (`Set.Finite.infinite_compl` + `Set.Infinite.nonempty`). SURVIVED. **L5.8**
  `IsNewtonPolygonOf.slopesUnbounded_of_finite` — L4.14 + L5.7. SURVIVED.
- **L5.9** `IsNewtonPolygonOf.slopesUnbounded_of_forall_line` — [SRC] `Face.slopesUnbounded_of_
  forall_line` docstring verbatim: *"If all unit slopes were `≤ σ`, the polygon would grow at most
  linearly with slope `σ`, but `line_le_height` at slope `σ + 1` forces faster growth."* Sketch: fix
  `σ`; if some unit slope is `⊤`, done; else all finite and suppose all `≤ σ`; then `h k ≤ h anchor
  + (k - anchor) σ` (sum bound) while `y + (σ+1) k ≤ h k` (L5.1 at slope `σ + 1`) — impossible for
  large `k`. SURVIVED.
- **L5.10** `IsNewtonPolygonOf.slopesUnbounded_of_tendsto` — from `v k / k → ∞`: for `σ`, `v k ≥
  (σ + 1) k` for `k ≥ N`; set `y := min (0, min_{k<N} (v k - (σ+1) k))` (finitely many finite
  values), then `y + (σ+1) k ≤ v k` for all `k`; apply L5.9. Attacks: [3] `hfin` needed for the
  finite minimum. SURVIVED.

- **L5.11** `le_unitSlope_faceLeft`, **L5.12** `lt_unitSlope_faceRight` — `Nat.sInf_mem` of the
  nonempty defining set (nonempty from `hu`: `σ < s → σ ≤ s`). **L5.13**
  `slopesUnbounded_iff_forall_lt_unitSlope_faceRight` — `←` is a witness. SURVIVED.
- **L5.14** `unitSlope_lt_of_lt_faceLeft`, **L5.15** `unitSlope_le_of_lt_faceRight` —
  `Nat.not_mem_of_lt_sInf` + `not_le`/`not_lt` (linear order on `WithTop ℝ`); no hypotheses.
  SURVIVED.
- **L5.16** `IsConvexSeq.le_unitSlope_of_faceLeft_le`, **L5.17** `…lt_unitSlope_of_faceRight_le` —
  `faceLeft h σ ≤ last` (the defining set meets every index `≥ last`, so its `sInf` is `≤ last`),
  hence `faceLeft ∈ finiteSet`; for `j ≥ faceLeft` in `finiteSet`, `monotoneOn`; for `j ∉
  finiteSet`, `unitSlope = ⊤`. Attacks: [3] `h 0 ≠ ⊤` is needed: with anchor `> 0` the `sInf` is
  `0` (junk) and the claim fails — the anchored-at-0 convention (plan.md decision 5). SURVIVED.
- **L5.18** `IsConvexSeq.faceLeft_eq_ncard`, **L5.19** `…faceRight_eq_ncard` — `{j | unitSlope h j <
  σ} = Set.Iio (faceLeft h σ)` by L5.14 and L5.16; `Set.ncard_coe_finset` with `Finset.range`
  (`Finset.card_range`). SURVIVED.
- **L5.20** `faceLeft_le_faceRight` — `{σ < s} ⊆ {σ ≤ s}`, `Nat.sInf_le (Nat.sInf_mem …)`.
  **L5.21** `faceRight_le_faceLeft_of_lt` — `{τ ≤ s} ⊆ {σ < s}` for `σ < τ`. SURVIVED.
- **L5.22** `IsConvexSeq.faceLeft_eq_faceRight_iff` — L5.27 (width = count) with `Set.ncard_eq_zero`.
  SURVIVED.
- **L5.23** `IsConvexSeq.eq_add_nsmul_of_mem_face` — on `[faceLeft, faceRight)` the unit slopes are
  `≥ σ` (L5.16) and `≤ σ` (L5.15), so `= σ`; `eq_add_nsmul_of_forall_unitSlope_eq`. SURVIVED.
- **L5.24** `IsConvexSeq.faceLeft_line_le` — L5.4 `←` at `n = faceLeft`: left slopes `< σ` (L5.14),
  right `≥ σ` (L5.16). **L5.25** `…faceLeft_line_lt` — L5.5 at `n = faceLeft`, with `h k ≠ ⊤` for
  `0 ≤ k < faceLeft ≤ last`. **L5.26** `…faceRight_line_lt` — L5.6 at `n = faceRight` (slopes from
  `faceRight` on are `> σ`, L5.17). SURVIVED.
- **L5.27** `IsConvexSeq.faceRight_sub_faceLeft` — `{j | unitSlope h j = σ} = Set.Ico (faceLeft)
  (faceRight)` (L5.14–L5.17), `Nat.card_Ico`. **L5.28** `…count_slopeMultiset_eq` — L4.12 + L5.27
  (`hu` from L5.7). Attacks: [2] `σ` not a slope: both `0` ✓ (with `faceLeft = faceRight`).
  SURVIVED.
- **L5.29** `IsConvexSeq.exists_faceRight_eq` — let `s := unitSlope h (faceRight h σ) > σ`; if `s =
  ⊤` any `δ`; else `δ := untop₀ s - σ`; for `σ ≤ τ < σ + δ` no unit slope lies in `(σ, τ]` (they
  are `≤ σ` before `faceRight` and `≥ s > τ` from it), so `{τ < ·} = {σ < ·}`. SURVIVED.
- **L5.30** `IsNewtonPolygonOf.eq_of_faceLeft`, **L5.31** `…eq_of_faceRight` — the endpoints are
  vertices (`faceLeft = 0 = anchor`, or `unitSlope (faceLeft - 1) < σ ≤ unitSlope faceLeft`;
  `faceRight = 0`, or `unitSlope (faceRight - 1) ≤ σ < unitSlope faceRight`), then L4.7; `h 0 ≠ ⊤`
  from `v 0 ≠ ⊤` via `anchor_eq`. [Ked07, Cor. 2]: the endpoints are "where the support lines …
  touch the polygon". SURVIVED.

---

## §0.6 Minkowski sums (`Minkowski.lean`)

### Plain-English proof substrate

[Ked07, proof of Prop. 1], verbatim: *"`v_r(PQ) ≥ min_{h,i,j} {v(P_{i+h}) + v(Q_j) + r(i+h+j)}`
(1). This immediately yields `v_r(PQ) ≥ v_r(P) + v_r(Q)`. To establish equality, let `i_0` and
`j_0` be the smallest values of `i` and `j` which minimize `ri + v(P_i)` and `rj + v(Q_j)`,
respectively; then (1) achieves its minimum for `h = 0, i = i_0, j = j_0` but not for any other
`h, i, j` with `i + j = i_0 + j_0`."* In height form: the Minkowski sum `M n = min_{i+j=n} (h₁ i +
h₂ j)` of two convex sequences is convex; at a minimising split the two unit-slope pairs interleave,
so a common slope `σ` separates both (the subgradient), and the sum of the two supporting lines of
slope `σ` supports `M`; the smallest minimisers of `v_r` are the left endpoints of the faces of
slope `r`, and at their sum the minimising split is unique because every other split moves one
factor strictly off its face. [Ked07, Cor. 2], verbatim: *"the multiplicity of `r` as a slope of
`PQ` is the sum of the multiplicities of `r` as a slope of `P` and `Q`."*

### Leaves

- **L6.1** `minkowski_le` — `Finset.inf_le (Finset.mem_range.2 (Nat.lt_succ_of_le hi))`. **L6.2**
  `le_minkowski_iff` — `Finset.le_inf_iff`. **L6.3** `exists_minkowski_eq` — `Finset.exists_mem_eq_inf`
  (`range (n+1)` nonempty). SURVIVED.
- **L6.4** `minkowski_comm` — `Finset.inf_image` along `i ↦ n - i`, with `(range (n+1)).image (n - ·)
  = range (n+1)` (**API check in the ticket**: `Finset.range_image_pred_top_sub` or prove by
  `Finset.ext` + `Nat.sub_sub_self`). **L6.5** `minkowski_assoc` — both sides are the infimum over
  `i + j + k = n` of `h₁ i + h₂ j + h₃ k`; two applications of L6.2 each way. **L6.6**
  `minkowski_zero` — `Finset.range_one`, `Finset.inf_singleton`. SURVIVED.
- **L6.7** `isConvexSeq_minkowski` — via the subgradient (L6.8/L6.9, which do not assume `M`
  convex): at each `n` with `M n` finite, the supporting line of slope `σ_n` through `(n, M n)`
  gives `unitSlope M (n-1) ≤ σ_n ≤ unitSlope M n` (L5.4 `→`, which needs only the line
  inequality — stated for convex `h` but its `→` half uses no convexity; the ticket may factor it
  out), hence monotone; finiteness set: `M n ≠ ⊤ ↔ n ≤ last₁ + last₂` (both anchored at `0`), an
  interval. Attacks: [2] one factor a single point `(y, ⊤, …)`: `M = h₂ + y` ✓ convex. [3]
  `h 0 ≠ ⊤` for both: without anchoring at `0` the splits `(i, n - i)` with `i < anchor₁` are `⊤`
  and the finiteness set is still an interval — the hypothesis is for the face statements, harmless
  here. SURVIVED.
- **L6.8** `exists_subgradient` — [SRC] `Product.exists_subgradient` docstring verbatim: *"(compare
  the split with its two neighbours)"*. At the minimiser `(i₀, j₀)`: `h₁ (i₀+1) + h₂ (j₀-1) ≥ h₁
  i₀ + h₂ j₀` gives `s₂ (j₀-1) ≤ s₁ i₀`; `h₁ (i₀-1) + h₂ (j₀+1) ≥ …` gives `s₁ (i₀-1) ≤ s₂ j₀`;
  with convexity of each factor the interval `[max (s₁(i₀-1), s₂(j₀-1)), min (s₁ i₀, s₂ j₀)]` is
  nonempty; any real `σ` in it (take the left end, `untop₀`, or `0` if the left end is absent)
  separates both slope sequences by monotonicity. Edge cases `i₀ = 0`, `j₀ = 0`, `⊤` slopes handled
  by dropping the absent constraints. Attacks: [2] `n = 0`: `i₀ = j₀ = 0`; `σ := min (s₁ 0, s₂ 0)`
  untopped (or any `σ` if both `⊤`) ✓. [3] `hfin` is needed for the untop arithmetic. SURVIVED.
- **L6.9** `subgradient_line_le_minkowski` — for each split `(i, m - i)`: `h₁ i ≥ h₁ i₀ + σ (i -
  i₀)` and `h₂ (m-i) ≥ h₂ j₀ + σ (m - i - j₀)` (L5.4 `←` for each factor), add, then L6.2. SURVIVED.
- **L6.10** `slopesUnbounded_minkowski` — if `M n = ⊤` eventually, done; else for `n` large the
  minimiser has `i₀ ≥ N₁` or `j₀ ≥ N₂` where beyond `N₁` (resp. `N₂`) the factor's unit slopes
  exceed `σ` (unbounded + monotone), and the subgradient `σ_n ≥ s₁ (i₀ - 1)` or `≥ s₂ (j₀ - 1)`, so
  `unitSlope M n ≥ σ_n > σ`. SURVIVED.
- **L6.11** `minkowski_faceLeft_add` — at `N = fL₁ + fL₂` the split `(fL₁, fL₂)` has the common
  subgradient `σ` (L5.14/L5.16 for each factor), so L6.9 gives `h₁ fL₁ + h₂ fL₂ ≤ M N`, and L6.1
  gives `≥`. SURVIVED. **L6.12** `lt_of_ne_faceLeft` — if `i > fL₁` then `j < fL₂` and `h₂ j >
  h₂ fL₂ + σ (j - fL₂)` strictly (L5.25) while `h₁ i ≥ h₁ fL₁ + σ (i - fL₁)` (L5.24); add: strict.
  Symmetric if `i < fL₁`. This is exactly [Ked07]'s "not for any other `h, i, j`". Attacks: [2] `fL₁
  = fL₂ = 0`, split `(1, -)`: impossible (`i + j = 0`), vacuous ✓. SURVIVED.
- **L6.13** `minkowski_faceRight_add`, **L6.14** `lt_of_ne_faceRight` — mirror images with L5.26
  (strict right of the face) and slopes `≤ σ` left of `faceRight` (non-strict). SURVIVED.
- **L6.15** `faceLeft_minkowski` — `unitSlope M (N-1) < σ`: every split of `N - 1` has `i < fL₁` or
  `j < fL₂`, so by L6.12's strict inequality `M (N-1) > M N - σ`; `unitSlope M N ≥ σ` from the
  supporting line (L6.9 at `N`); hence `faceLeft M σ = N` (`Nat.sInf` characterisation with
  monotonicity of `unitSlope M`, L6.7). **L6.16** `faceRight_minkowski` — mirror: `unitSlope M (N')
  > σ` at `N' = fR₁ + fR₂` via L6.14, `unitSlope M (N'-1) ≤ σ` via the face value L6.13 and L6.1.
  Attacks: [2] `σ` not a slope of either factor: `fL = fR` for both, `M` has no slope `σ` ✓
  consistent with L5.22. SURVIVED.
- **L6.17** `slopeMultiset_minkowski` — `Multiset.ext` on counts: `count σ (slopeMultiset M) =
  fR_M - fL_M` (L5.28, with `slopeIndices M` finite since `M = ⊤` past `last₁ + last₂`) `= (fR₁ -
  fL₁) + (fR₂ - fL₂)` (L6.15, L6.16, and `fL ≤ fR` for the subtraction) `= count σ (sm h₁) +
  count σ (sm h₂)` (`Multiset.count_add`). This is [Ked07, Cor. 2] in multiset form. SURVIVED.

---

## Examples (`Examples.lean`)

Each is an acceptance test from [RM] Layer 0 "Examples"; all are proved against the specification:
exhibit the candidate, check it is a convex minorant (`le_newtonPolygon`) and that the polygon is
below it (`newtonPolygon_le` + the candidate's maximality), or use `eq_newtonPolygon`.

- **E1** `newtonPolygon_single` — candidate `(y, ⊤, ⊤, …)` = `affineFrom 0 y 0` cut at `0`; it is the
  polygon by L2.14 at `0` and L2.4 beyond. **E2** `newtonPolygon_affine` — the affine sequence is a
  convex minorant of itself and `le_points` gives the reverse. **E3** `newtonPolygon_sq` — `k²` is
  convex (`unitSlope = 2k + 1`, monotone), same argument; **E4** `unitSlope_newtonPolygon_sq` — by
  E3 and arithmetic. **E5** `newtonPolygon_alternating` — `0` is a convex minorant; any convex
  minorant `g` is `≤ 0` at even indices and at odd `k` is below the chord of its even neighbours,
  `≤ 0`. **E6–E8** the collinear example — by E3-style computation: the polygon of `(0,1,2,4)` is
  `(0,1,2,4)` itself (convex), `unitSlope 0 = unitSlope 1 = 1 < 2 = unitSlope 2`, so `1` is not a
  vertex and `2` is. **E9** `newtonPolygon_ceil_sqrt_two` — `k√2` is a convex minorant (`Int.le_ceil`);
  a convex minorant `g` with `g n > n√2` for some `n ≥ 1` has, by convexity from `(0, g 0 ≤ 0)`, unit
  slopes eventually `> √2 + δ`, so `g k > k√2 + 1 ≥ ⌈k√2⌉` for large `k` (`Int.ceil_lt_add_one`),
  contradiction; so `g ≤ k√2` and `newtonPolygon = k√2`. Attacks: [2] `k = 0` ✓; [4] matches [RM]
  convention 4's example exactly. SURVIVED.

---

## Gate (Step 5): the seven conditions

1. **Every leaf discharged or sketched from named ingredients.** Every leaf above names the Mathlib
   lemmas and earlier leaves its proof composes; 60 of the 63 lemma names cited were verified by
   elaboration (`scratchpad/names.lean`), the three misses replaced by their existing forms. Two
   Mathlib names are flagged *to be verified at ticket time* rather than asserted: a
   supremum-of-`ConvexOn` lemma (L1.18, with a definition-level fallback) and
   `Finset.range_image_pred_top_sub` (L6.4, with a two-line fallback). No API gap needing its own
   sub-development was found: Layer 0 rests on Mathlib's `WithTop`, `Finset.inf`, `Nat.sInf`,
   `Multiset` and `ConvexOn` alone.
2. **The Lean skeleton compiles.** `lake build PhD.TauCeti.Code.NewtonPolygons.Examples` (which
   imports every other file) reported `Build completed successfully (8690 jobs)` for the skeleton
   with all corrections below except the last (L1.22); the final build after that edit is recorded
   at the end of this section.
3. **Verbatim quotes.** Section-level substrates quote [Ked07] (definition as the intersection of
   halfplanes; slope multiset; `v_r`; Prop. 1 with inequality (1) and the unique-minimiser sentence;
   Cor. 2 and its face-endpoint sentence), [Kob84] (vertices), and [SRC] docstrings (existence
   proof structure, steepened competitor, subgradient, unbounded slopes). Leaf-level "sources" are
   the roadmap clauses they discharge — the roadmap is a *specification*, and most of Layer 0 is
   elementary discrete convexity whose only literature is a specification plus Mathlib; where a
   textbook fact is invoked from memory (Rockafellar Thm 5.5 for L1.16) this is said explicitly and
   the verified Mathlib two-function analogue is cited instead.
4. **Adversarial pass.** Every leaf has an attack block. Attacks that **succeeded** and changed a
   statement: L1.21 (antitone disjunct off the finiteness set), L1.22 (telescoping needs all
   intermediate values finite), L2.17 (`v ≡ ⊤` satisfies the spec with `⊤`; `eq_newtonPolygon` needs
   a point; the existence `↔` has RHS `IsAdmissible v` only), L3.6 (strict slope increase fails into
   an asymptotic ray of the same slope — split into `≤` and a conditional `<`), L3.19 (the vertex
   correspondence is two implications, not an `↔`), L4.16 (the roadmap's first-break
   characterisation omits the steeper line — **roadmap defect, to be amended by the user**), L4.18
   (`hlast` unnecessary, dropped), L1.11 (convexity unnecessary, dropped). Attacks that changed a
   *sketch* only: L2.6, L2.7, L2.4 (bump-and-steepen), L6.7 (convexity of the Minkowski sum via the
   subgradient, avoiding a parity argument).
5. **Prior-B2 log.** Consulted (8 entries, 2 relevant); the `unitSlope_cases` phantom is
   unrepresentable in the height-function design (recorded at the top of this file).
6. **Structure.** The tree is the roadmap's own numbered milestones (§0.1.1–§0.6.4 plus the
   Examples), one or a few leaves per clause; where [SRC] proves the same statement its proof
   structure is mirrored (existence: line bound + chord/ε-argument; faces; subgradient). Size
   estimates are given only for the two long proofs (L3.15 ≈ 80 lines, L3.16 ≈ 120 lines) and are
   *relative to [SRC]* (`SpecConstruction.lean`'s corresponding sections are ~250 and ~300 lines,
   most of it segment-structure bookkeeping that the height function removes); they are not
   commitments.
7. **Single conclusion per declaration.** `IsNewtonPolygonOf` has five single-conclusion fields; the
   only multi-clause statements are biconditionals (`isAdmissible_iff_bddBelow`, `line_le_iff`,
   `hasFirstBreak_iff`, `isPure_iff_slopeMultiset`, `faceLeft_eq_faceRight_iff`) whose right-hand
   sides are the roadmap's own characterisations; `exists_subgradient` is a shared-witness
   existential (one `σ` separating four slope sequences — splitting it would lose the common
   witness, the documented exception); the `∧`-conclusions found (`eq_of_isSegment`, the collinear
   example) were removed or split.

No leaf is REVIEW-PENDING.

### Skeleton edits made by the adversarial pass (all applied)

| Leaf | Edit |
|---|---|
| L1.11 | `eq_add_nsmul_of_forall_unitSlope_eq`: convexity hypothesis dropped (root-namespace theorem) |
| L1.21 | `antitone_or_eventually_monotone`: first disjunct restricted to `h (k+1) ≠ ⊤` |
| L1.22 | `eq_add_sum_unitSlope`: hypothesis `∀ j, a ≤ j → j ≤ k → h j ≠ ⊤` |
| L1.23–24 | helpers `affineFrom`, `isConvexSeq_affineFrom`, `IsConvexSeq.extend_affine` added |
| L2.17 | `eq_newtonPolygon` gains `hv'`; `exists_isNewtonPolygonOf_iff` RHS is `IsAdmissible v` |
| L3.4 | `sInf_slopeSet_lt_slopeTo_of_nextVertex_lt` gains `hv`, `hi` |
| L3.6 | `sInf_slopeSet_le_sInf_slopeSet_nextVertex` (`≤`) kept; strict form under `nextVertex v j ≠ ⊤` |
| L3.19 | `isVertex_iff_exists_vertexSeq` → `exists_vertexSeq_of_isVertex` + `isVertex_of_vertexSeq_eq` |
| L4.16 | `hasFirstBreak_iff`: RHS gains `∃ m' > m` with the steeper line beyond the break |
| L4.18 | `newtonPolygon_truncate_eq`: `hlast` dropped |
| (build) | `IsNewtonPolygonOf.anchor` field renamed `anchor_eq` (it shadowed `NewtonPolygon.anchor`); `eq_of_isSegment` removed; the collinear example split into a `def` and three theorems; three `fun k ↦` binders typed |

### Roadmap amendments surfaced (all applied to the README on 2026-09-12 — full list in the revision 2 Gate)

- §0.4.4: the first-break characterisation must add "and some strictly steeper line through that
  point lies on or below every later point" (L4.16).
- §0.1.1: state explicitly that the increment sequence is monotone *on the finiteness interval*
  (global monotonicity is false past index 0; the prototype `Suggested.lean` has this wrong).
- §0.2.3: existence holds for `v ≡ ⊤` with the polygon `⊤`; the clause "and has a finite value" in
  §0.2.4 is about the junk value of the definition, not about existence of the specification.

**Final build** (after the L1.22 edit): `lake build PhD.TauCeti.Code.NewtonPolygons.Examples` — `Build completed successfully`, sorry warnings only, 146 `sorry` bodies across 7 files, 177 declarations. Gate passed 2026-09-12.

---

# Revision 2 (2026-09-12): generic index type, three-field specification, the vertical case

User decisions: (1) the vertical case is a predicate, no `⊥`; (2) the core is generic over a discrete
linear order `ι` with `ℕ` and `ℤ` as instances. Probe `scratchpad/generic.lean` (elaborated clean):
generic `unitSlope`/`IsConvexSeq`/chord with `Finset.Ico` cards/telescoping/spec/`newtonPolygon`;
`unique` proves generically; `ℕ`, `ℤ` carry `SuccOrder`, `IsSuccArchimedean`, `LocallyFiniteOrder`;
`Order.succ_eq_add_one`, `Nat.card_Ico`, `Int.card_Ico` collapse the generic statements to the
familiar ones; `Succ.rec` is the induction principle; `tendsto_atTop_ciSup` works on `ι` with
`[Nonempty ι]`.

## What changed in the skeleton

| File | Change |
|---|---|
| `ConvexSeq.lean` | §0.1 restated for `ι` (`succ j`, `(Finset.Ico a c).card •`). Sections: `Defs` (`[LinearOrder ι] [SuccOrder ι]`) and `Sums` (adds `[IsSuccArchimedean ι] [LocallyFiniteOrder ι] [NoMaxOrder ι]`). `eq_of_unitSlope_eq` now `IsConvexSeq.eq_of_unitSlope_eq` with **both sequences convex** (see L1.4′). `unitSlope_nat` added. Affine/`ConvexOn`/min-counterexample kept on `ℕ`. |
| `Basic.lean` | Spec reduced to **three fields**; `unique` proved in place; `newtonPolygon`, `le_newtonPolygon`, `newtonPolygon_le`, `isConvexSeq_newtonPolygon`, `isNewtonPolygonOf_newtonPolygon`, `exists_isNewtonPolygonOf_iff` (↔ `∃ g, IsConvexMinorant v g`), `eq_newtonPolygon` (unconditional), `newtonPolygon_mono` generic. `ℕ` section: `slopeTo`, `slopeSet`, `IsAdmissible`, `isAdmissible_iff_bddBelow`, `isAdmissible_of_line`, **`isAdmissible_iff_exists_line`**, **`exists_isConvexMinorant_iff_isAdmissible`**, `IsNewtonPolygonOf.isAdmissible`, `exists_isNewtonPolygonOf_iff_isAdmissible`; anchoring as theorems `anchor_eq`, `eq_top_of_forall_eq_top`, `eq_top_of_forall_le`; **`IsVertical`**, `isVertical_iff_not_exists_isConvexMinorant`, `exists_isNewtonPolygonOf_or_isVertical`, `isVertical_neg_sq`; invariances now need only `IsAdmissible v`. |
| `Int.lean` (new) | `extendTop`, `extendTop_natCast`, `extendTop_of_neg`, `unitSlope_extendTop_natCast`, `isConvexSeq_extendTop_iff`, `isConvexMinorant_extendTop_iff`, `isNewtonPolygonOf_extendTop_iff`, `newtonPolygon_extendTop`, `IsNewtonPolygonOf.eq_top_of_forall_lt` (ℤ), `isConvexSeq_affine_int`, `exists_isConvexMinorant_iff_exists_line` (ℤ), `not_exists_isConvexMinorant_neg_abs`. |
| `Suggested.lean` (roadmap prototype) | `IsConvexSeq` corrected to the two-field form, the false `unitSlope_mono` replaced by `IsConvexSeq.midpoint`, the spec reduced to three fields, `IsVertical` added. |
| `Slope`, `Face`, `Minkowski`, `Construction`, `Examples` | unchanged: their statements are on `ℕ`, where the generic definitions are the previous ones. Sketches that said "by the `anchor_eq` field" now read "by `IsNewtonPolygonOf.anchor_eq` (theorem)". |

Superseded entries above: L2.1 (now proved), L2.4/L2.14/L2.15 (anchoring is no longer in the
spec: the same arguments prove the theorems `anchor_eq`, `eq_top_of_forall_eq_top`,
`eq_top_of_forall_le` from the three fields plus admissibility), L2.16 (assembly now needs only a
minorant), L2.17 (existence iff a convex minorant exists, generic; `eq_newtonPolygon` unconditional
because `h` itself is a minorant).

## New and changed leaves

- **L1.4′** `IsConvexSeq.eq_of_unitSlope_eq` — **attack [2] succeeded on the old statement**:
  `h = (0, ⊤, 3)`, `g = (5, ⊤, 3)` share the finite value at `2` and have all unit slopes `⊤`, yet
  differ. Fix: both sequences convex (order-connected). Proof: for `j ≥ i₀`, `Succ.rec` with
  `add_unitSlope`; for `j < i₀`, right-induction from `j` to `i₀` via `eq_add_sum_unitSlope`: if
  `h j` and `g j` are both finite the sums agree so the values do; if exactly one is `⊤`, the unit
  slopes at `j` differ (`⊤` against a real). No `PredOrder` needed. Attacks: [2] `i₀` the only finite
  index ✓; [3] convexity of *both* is necessary (the example). SURVIVED after correction.

- **L1.x (generic restatements)** — every §0.1 leaf keeps its attack log; the only new attack
  surface is the index type: [2] `ι` with a maximal element would make `succ j = j` and
  `unitSlope h j = 0` at the top — excluded by `[NoMaxOrder ι]` in the `Sums` section, where it
  matters for `Finset.Ico n (succ n)` having one element; the `Defs` section statements hold
  regardless. [5] `Succ.rec`, `Finset.Ico_union_Ico_eq_Ico`, `Order.succ_le_of_lt`,
  `Order.le_of_lt_succ` verified by `#check`; the ℕ/ℤ collapse lemmas verified by `example`.
  SURVIVED.

- **L2.A** `exists_isNewtonPolygonOf_iff` (generic) — `→`: `h` is a convex minorant. `←`: L2.12/L2.16
  generic (sup of a nonempty family of convex minorants is a convex minorant and greatest). Attacks:
  [2] `v ≡ ⊤`: both sides true (`⊤` is a minorant) ✓; `-k²`: both false ✓. SURVIVED.
- **L2.B** `IsNewtonPolygonOf.eq_newtonPolygon` (generic, unconditional) — `hh.unique
  (isNewtonPolygonOf_newtonPolygon ⟨h, hh.isConvexMinorant⟩)`. The former `v ≡ ⊤` attack no longer
  applies: the family is nonempty (`h` itself), so the supremum is honest and equals `h` (every
  minorant is `≤ h` by `greatest`, and `h` is in the family). SURVIVED.
- **L2.C** `isAdmissible_iff_exists_line` (ℕ) — `←` is L2.6; `→`: the admissible line through the
  first point `i₀` lies below all later points and trivially below the `⊤` values before it
  (`y := untop₀ (v i₀) - s i₀`). Attacks: [2] `v ≡ ⊤`: both sides true ✓. SURVIVED.
- **L2.D** `exists_isConvexMinorant_iff_isAdmissible` (ℕ) — `←`: `affineFrom i₀ (untop₀ (v i₀)) s`
  (L2.13), or `⊤` if `v ≡ ⊤`. `→`: L2.7's corrected argument (slope-set form). SURVIVED.
- **L2.E** `IsNewtonPolygonOf.anchor_eq` (ℕ, theorem) — as L2.14 with `hh.greatest` in place of
  `le_newtonPolygon`: the admissible line (from `hh.isAdmissible`) through `(i₀, v i₀)`, extended by
  `⊤`, is a convex minorant, so `v i₀ ≤ h i₀ ≤ v i₀`. SURVIVED.
- **L2.F** `IsNewtonPolygonOf.eq_top_of_forall_eq_top` (ℕ, theorem) — as L2.15 with the steepened
  left line as the competitor against `hh.greatest`, and `WithTop.eq_top_iff_forall_gt`. SURVIVED.
- **L2.G** `IsVertical`, `isVertical_iff_not_exists_isConvexMinorant` (L2.D negated),
  `exists_isNewtonPolygonOf_or_isVertical` (`Classical.em (IsAdmissible v)` with L2.A/L2.D),
  `isVertical_neg_sq` (L2.8 + the point at `0`). Attacks: [2] `v ≡ ⊤`: not vertical (no point) and
  has the polygon `⊤` ✓ dichotomy holds; `v` a single point: admissible, not vertical ✓. [4] the
  roadmap now says "named, not represented" (convention 5, §0.2.3). SURVIVED.
- **L2.H** `newtonPolygon_add_affine`, `newtonPolygon_add_const` with only `IsAdmissible v`:
  admissibility is preserved by adding an affine sequence (slopes shift by `σ`), the minorant family
  is nonempty on both sides (L2.D), and `⨆ (g + ℓ) = (⨆ g) + ℓ` by two `ciSup`/`le_ciSup`
  inequalities. Attacks: [2] `v ≡ ⊤`: both sides `⊤` ✓. SURVIVED.

### `Int.lean` (§0.2.6)

- **LZ.1** `extendTop_natCast`, `extendTop_of_neg` — `if_pos`/`if_neg` with `Int.toNat_natCast`.
  **LZ.2** `unitSlope_extendTop_natCast` — `succ (n : ℤ) = ((n + 1 : ℕ) : ℤ)`
  (`Order.succ_eq_add_one`, `Nat.cast_succ`), then LZ.1 twice. SURVIVED.
- **LZ.3** `isConvexSeq_extendTop_iff` — finiteness set of the extension is the image of `finiteSet h`
  under the cast (negatives are `⊤`), order-connected iff the original is; unit slopes agree at
  naturals (LZ.2) and are `⊤` at negatives (outside the set). Attacks: [2] `h ≡ ⊤` ✓ both sides.
  SURVIVED.
- **LZ.4** `isConvexMinorant_extendTop_iff`, **LZ.5** `isNewtonPolygonOf_extendTop_iff` — LZ.3 plus:
  `≤` at naturals is the original, at negatives `⊤ ≤ ⊤`; for `greatest`, a `ℤ`-minorant `g` of
  `extendTop v` restricts to a `ℕ`-minorant `g ∘ (↑)` of `v` (convex: LZ.3-style), and a `ℕ`-minorant
  extends. Attacks: [2] a `ℤ`-minorant finite on negatives: it is `≤ ⊤ = extendTop h` there
  trivially, so `greatest` for the extension reduces to the naturals ✓ (this is the point of `⊤` as
  "no polygon here"). SURVIVED.
- **LZ.6** `newtonPolygon_extendTop (hv)` — LZ.5 applied to `isNewtonPolygonOf_newtonPolygon` on
  `ℕ` (minorant from `hv`, L2.D) gives `IsNewtonPolygonOf (extendTop v) (extendTop (newtonPolygon
  v))`, then L2.B on `ℤ`. **This is the reduction the user asked for.** Attacks: [2] `v ≡ ⊤`: both
  sides `⊤` ✓. SURVIVED.
- **LZ.7** `IsNewtonPolygonOf.eq_top_of_forall_lt` (ℤ) — the steepened-left competitor needs a
  finite value to steepen from; if `v ≡ ⊤` then `h ≡ ⊤` (any convex `g` is a minorant of `⊤`, so
  constants `c` force `h ≥ c` for all `c`). SURVIVED.
- **LZ.8** `isConvexSeq_affine_int` — as L1.12 with `Int.cast`. **LZ.9**
  `exists_isConvexMinorant_iff_exists_line` (ℤ) — `←`: the line is a convex minorant. `→`: a convex
  `g ≤ v` finite at some `i` satisfies `g k ≥ g i + (k - i) s` for all `k ∈ ℤ` with `s := untop₀
  (unitSlope g i)` (right: L1.9 generic; left: `s_{i-1} ≤ s` makes the left extension weaker, L1.10
  generic — note `(k - i) s` for `k < i` is `≥ (k - i) s_{i-1}`); if `g ≡ ⊤` then `v ≡ ⊤` and any
  line works. Attacks: [2] `v k = |k|`: line `y = 0` ✓; `v k = -|k|`: no line (slopes `-1` right,
  `+1` left — a line below both arms would need slope `≤ -1` and `≥ 1`) ✓ consistent with LZ.10.
  SURVIVED.
- **LZ.10** `not_exists_isConvexMinorant_neg_abs` — by LZ.9: a line `y + σ k ≤ -|k|` for all `k`
  forces `σ ≤ -1` (from `k → +∞`) and `σ ≥ 1` (from `k → -∞`). This is the counterexample that
  killed the pointwise two-sided condition (design note in `Int.lean`). SURVIVED.

## Gate (revision 2)

Conditions 1, 3–7 as before, with the new leaves above.

Condition 2 — **the skeleton compiles**: `lake build PhD.TauCeti.Code.NewtonPolygons.Examples
PhD.TauCeti.Code.NewtonPolygons.Int PhD.TauCeti.Roadmaps.NewtonPolygons.Suggested` →
`Build completed successfully (8692 jobs)`, no errors, no non-`sorry` warnings (the one
"automatically included section variable" warning on `mem_finiteSet` was removed with
`omit [LinearOrder ι] [SuccOrder ι] in`). `sorry` bodies: ConvexSeq 25, Basic 25, Int 11, Slope 18,
Face 31, Minkowski 17, Construction 26, Examples 9 — 162 across 8 files, 196 declarations; the
roadmap prototype `Suggested.lean` has 45. Declaration coverage: every declaration is named in a
ticket except `mem_finiteSet` (`Iff.rfl`, proved). Gate (revision 2) passed 2026-09-12.

Roadmap amendments made in this revision (all in `PhD/TauCeti/Roadmaps/NewtonPolygons/README.md`):
- Layer 0 preamble, §0.1, §0.2 (items 1–6), convention 5: generic index type, three-field
  specification, `IsVertical`, the doubly-infinite case with the `-|k|` warning.
- §0.4.4: the first break needs a strictly steeper line (`v k = m k + 1/k`).
- §4.4.5: `radiusOfConvergence f = 0 ↔ IsVertical (coeffVal f)`.
- §4.3.2 and the Layer 4 examples: the closed-ball zero count `faceRight m` presupposes a bounded
  face of slope `m`; when the polygon ends in the ray of slope `m` and `f` is restricted at `b ^ m`
  the count is the Weierstrass degree at `b ^ m` (the last point on the ray), and "no zero of
  valuation `-m`" was false — heights `(0, m, 2m + √2, 3m + √3, …)` give a series restricted at
  `b ^ m` with polygon the ray of slope `m` and one zero of valuation `-m`. Found 2026-09-12 while
  answering how infinite faces enter the slope multiset; Layer 0 unaffected (`faceRight` junk is
  documented, `faceRight_sub_faceLeft` carries `SlopesUnbounded`, the walk's `lastVertex` is `d`).
- `Suggested.lean`: two-field `IsConvexSeq`, `IsConvexSeq.midpoint` in place of the false
  `unitSlope_mono`, three-field `IsNewtonPolygonOf` with `unique` proved, existence from
  `IsAdmissible` alone, `IsVertical`, `extendTop` and the §0.2.6 forms.

---

# Revision 3 (2026-09-12): the terminal ray is named — `EndsInRay`

User request, after asking how an infinite-length face enters the slope multiset and how it is
detected. Added: `EndsInRay h m := ∃ N, ∀ j, N ≤ j → unitSlope h j = m` (`Slope.lean`), its
characterisation and `faceRight`-junk lemma, the `SlopesUnbounded` relations and the trichotomy
(`Face.lean`), and the walk detecting it in both directions (`Construction.lean`). Roadmap §0.3.2,
§0.5.4 and §4.3.2 name the predicate. Import graph unchanged (`Slope` is imported by both `Face` and
`Construction`; `Construction` still does not import `Face`).

## Leaves

- **LR.1** `EndsInRay.ne_top` — `unitSlope h j = m ≠ ⊤` forces `h j ≠ ⊤` (`unitSlope_eq_top_iff`,
  `WithTop.coe_ne_top`). Attacks: [2] `h ≡ ⊤`: hypothesis false ✓. SURVIVED.
- **LR.2** `IsConvexSeq.endsInRay_iff` : `EndsInRay h m ↔ (∀ j, h j ≠ ⊤ → unitSlope h j ≤ m) ∧
  ∃ j, unitSlope h j = m`. `→`: `N` from the ray; for `h j ≠ ⊤` with `j < N`, `monotoneOn` against
  `N` (finite by LR.1); `j ≥ N` is equality. `←`: from `j₀` with slope `m`, `Nat.le_induction`: if
  `h j ≠ ⊤` then `unitSlope h j ≤ m < ⊤` gives `h (j+1) ≠ ⊤`; then `m = unitSlope h j₀ ≤ unitSlope
  h j ≤ m`. **Attack [3] succeeded on the first draft** `∀ j, unitSlope h j ≤ m` (no finiteness
  guard): a polygon anchored at `1` has `unitSlope h 0 = ⊤`, so the unguarded form is false while
  the ray is genuine. Fixed by the guard `h j ≠ ⊤`. [2] finitely supported `h`: both sides false
  (the last finite index has slope `⊤ ≰ m`) ✓; `h ≡ ⊤`: both false ✓. SURVIVED after correction.
- **LR.3** `EndsInRay.unitSlope_le` — LR.2 `→`, first conjunct. SURVIVED.
- **LR.4** `EndsInRay.setOf_lt_unitSlope_eq_empty` (with `h0 : h 0 ≠ ⊤`) — every index is finite
  (order-connected between `0` and a ray index), then LR.3 and `not_lt`. **Attack [3] on the
  version without `h0`**: indices before the anchor carry slope `⊤ > m` — false. `h0` is the same
  convention as every face lemma. SURVIVED with `h0`.
- **LR.5** `EndsInRay.not_slopesUnbounded` (with `h0`) — `hu m` gives `m < unitSlope h j`,
  contradicting LR.4. Design note surfaced by the attack: `SlopesUnbounded` as defined (`⊤` counts)
  holds trivially for any sequence with a `⊤` value — anchored past `0`, or finitely supported — so
  it is meaningful only for sequences anchored at `0` that are finite everywhere or finitely
  supported; consistent with the face lemmas' `h0` and recorded in the trichotomy. SURVIVED.
- **LR.6** `EndsInRay.le_unitSlope_faceLeft` — `{j | m ≤ unitSlope h j}` is nonempty (`N`), and
  `Nat.sInf_mem`. No convexity needed. SURVIVED.
- **LR.7** `IsConvexSeq.slopesUnbounded_or_endsInRay_or_tendsto` (with `h0`) — `by_cases`
  `SlopesUnbounded`; otherwise `∃ σ, ∀ j, unitSlope h j ≤ σ`, so every value is finite, the real
  slopes are monotone (`monotoneOn` on `univ`) and bounded, `m := ⨆ j, s j`, `tendsto_atTop_ciSup`
  (L1.20); if `∃ j, s j = m` then `EndsInRay` by LR.2 (`le_ciSup` for the bound); else `s j < m` for
  all `j` (`lt_of_le_of_ne`), and `unitSlope h j = s j < m` in `WithTop`. Attacks: [2] finitely
  supported `h`: first disjunct (a `⊤` slope) ✓; `h ≡ ⊤`: excluded by `h0` ✓; ray: second disjunct,
  and the third fails at the attained index ✓ (the disjuncts are exclusive though this is not
  claimed). [4] the roadmap §0.5.4 now states the trichotomy. SURVIVED.
- **LR.8** `achievingSet_eq_empty_or_infinite_of_nextVertex_eq_top` — `nextVertex` is `⊤` exactly
  when `¬ (Finite ∧ Nonempty)`: `dif_neg`, `not_and_or`, `Set.not_nonempty_iff_eq_empty`,
  `Set.not_infinite`. No `hne` needed (no later point gives `∅`). SURVIVED.
- **LR.9** `endsInRay_newtonPolygon_of_nextVertex_eq_top` — `N := i`; for `j ≥ i`,
  `newtonPolygon_eq_ray` (L3.21) at `j` and `j + 1`, `unitSlope_of_ne_top`, `succ_nsmul`: the
  increment is `sInf (slopeSet v i)`. Attacks: [2] infinitely many points on the minimal line
  (`achievingSet` infinite): `newtonPolygon_eq_ray` applies (`nextVertex = ⊤`) and the polygon is
  that line ✓. SURVIVED.
- **LR.10** `exists_vertexSeq_eq_of_endsInRay` — the polygon has finitely many vertices (a vertex is
  a strict increase of the unit slope, impossible from `N` on), so the walk's vertex sequence
  (L3.x: its finite values are the polygon's vertices, plus possibly the last point on a terminal
  ray, which is not a vertex) reaches `⊤`; the last finite value `i` has `nextVertex v i = ⊤`;
  `slopeSet v i` is nonempty because the polygon is finite beyond `i` (LR.1) while
  `newtonPolygon_eq_top_of_slopeSet_eq_empty` (L3.20) would make it `⊤`; the minimal slope is `m`
  because LR.9 makes the unit slopes from `i` equal to it while `hm` makes them eventually `m`.
  Attacks: [2] could the walk stop before the ray starts? Its terminal point is either the last
  polygon vertex `a` (no later point on the ray) or the last point on the ray; both have the ray's
  slope as minimal slope ✓. [2] `⌈k√2⌉`: `i = 0`, `slopeSet` nonempty, `nextVertex v 0 = ⊤`
  (infimum `√2` not attained), `sInf = √2` ✓. [5] depends on T028/T031 (walk = polygon) — ordered
  after them by the ticket chain. SURVIVED.

## Gate (revision 3)

Condition 2 — **the skeleton compiles**: `lake build PhD.TauCeti.Code.NewtonPolygons.Examples
PhD.TauCeti.Code.NewtonPolygons.Int PhD.TauCeti.Roadmaps.NewtonPolygons.Suggested` →
`Build completed successfully (8692 jobs)`, no errors, no non-`sorry` warnings. (One elaboration
error on the first attempt, fixed in place: the binder `∃ n i, vertexSeq v n = (i : WithTop ℕ) ∧ …`
inferred `i : WithTop ℕ`; now `∃ n i : ℕ`.) 207 declarations, 172 `sorry` bodies across the 8 files,
every declaration named in a ticket except `mem_finiteSet` (proved). Conditions 1, 3–7 hold for
LR.1–LR.10 as above (every leaf names its Mathlib and project ingredients; sources are roadmap
§0.3.2/§0.5.4 as amended and [Kob84, §IV.4] for the three convergence behaviours). Gate (revision 3)
passed 2026-09-12. Board: 58 tickets (39 proof/definition, 16 per-file cleanups, CLEANUP-ALL-1
before T026, CLEANUP-ALL-2 before T031, CLEANUP-FINAL).
