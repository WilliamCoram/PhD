# Ticket Board — IsNewtonPolygonOf: Newton polygon as lower convex hull

Project: geometric spec `IsNewtonPolygonOf` + uniqueness + existence for the Newton polygon
construction. All new code in `PhD/NewtonPolygons/` (Height.lean / Spec.lean /
SpecConstruction.lean). The skeleton exists and compiles (37 sorries, no errors); every proof
ticket is "fill the sorries at the named declarations". Leaf ids (L1–L18), verbatim source
quotes, and attack logs live in `.mathlib-quality/decomposition.md`. Blueprint source:
`blueprint/src/chapter/NP.tex` ([BP]).

## Summary
- Total: 26 tickets (17 proof/def + 7 per-file cleanups + 1 cleanup-all + 1 final)
- Open: 0 | In Progress: 0 | Done: 26 (board completed 2026-08-03T20:15Z)
  (as of 2026-08-03T19:16Z; all 17 proof tickets DONE, milestone T017 assembled,
  all 6 endpoints axiom-checked standard)
- Milestone: T017 (existence theorem `isNewtonPolygonOf_newtonPolygon₀OfSeq`) — **DONE**
- Statement corrections during execution (both recorded in b2_log.jsonl / ticket notes):
  `unitSlope_cases` gained hypothesis `(P.support = 1 → P.lengths 0 ≠ 0)` (unconditional form
  refuted, machine-checked); `height_le_chord` gained `(hxs : P.starting_point.1 ≤ x)`
  (pre-authorized in T005's off-script note; unconditional form refuted).
- Cleanup merges (same file, adjacent cadence slots): 1+2, 3+4, 6+7.

## Build/verify
`lake build PhD.NewtonPolygons.SpecConstruction` (builds the whole chain).
No new axioms: `#print axioms isNewtonPolygonOf_newtonPolygon₀OfSeq` at milestone — only
`propext`, `Quot.sound`, `Classical.choice`.

---

### [T001] vertexX + heightFun basic API
- **Status**: done (2026-08-03T11:25Z; 5/5 lemmas, lake env lean clean; per-decl cleanup
  deferred to CLEANUP-1 by design — one-line simp lemmas, file cleanup 2 tickets away) |
  **File**: PhD/NewtonPolygons/Height.lean | **Depends on**: none | **Parallel**: yes |
  **Type**: API lemmas | **Leaves**: L5
- **Progress**: 2026-08-03T11:25Z: all five proved (simp/sum_range_succ/
  monotone_nat_of_le_succ + le_add_of_nonneg_right + WithTop.map_coe); added
  `omit [CommSemiring Γ] [Algebra Γ ℝ]` on the three vertexX lemmas (unused-section-vars
  linter).

#### Statement (fill these sorries; Height.lean:52–66)
```lean
@[simp] lemma vertexX_zero : P.vertexX 0 = (P.starting_point.1 : WithTop ℤ)

lemma vertexX_succ (n : ℕ) :
    P.vertexX (n + 1) = P.vertexX n + (P.lengths n).map (fun l : ℕ => (l : ℤ))

lemma vertexX_mono : Monotone P.vertexX

@[simp] lemma heightFun_zero : P.heightFun 0 = algebraMap Γ ℝ P.starting_point.2

lemma heightFun_succ (k : ℕ) :
    P.heightFun (k + 1) = P.heightFun k + NewtonPolygon.toReal (P.unitSlope k)
```

#### Proof sketch
1. `vertexX_zero`: unfold; `Finset.range 0` sum is 0; `add_zero`. Likely `simp [vertexX]`.
2. `vertexX_succ`: `Finset.sum_range_succ` + `add_assoc`.
3. `vertexX_mono`: `monotone_nat_of_le_succ`; by `vertexX_succ` each step adds a nonneg
   `WithTop ℤ` term — use `le_add_of_nonneg_right`; nonnegativity: `(⊤ or (l:ℤ)) ≥ 0` since
   `l : ℕ` (case on `P.lengths n`; `WithTop.map`).
4. `heightFun_zero`/`heightFun_succ`: `simp [heightFun]`, `Finset.sum_range_succ`.

#### Mathlib lemmas needed
`Finset.sum_range_zero`, `Finset.sum_range_succ`, `monotone_nat_of_le_succ`,
`le_add_of_nonneg_right`, `WithTop.map` case lemmas (`WithTop.map_top`, `WithTop.map_coe`).

#### Sources
decomposition.md L5. No external source (definitional API).

#### Generality decision
`{Γ} [CommSemiring Γ] [Algebra Γ ℝ]` throughout the project (matches `NewtonPolygon₀`);
`vertexX_mono` non-strict deliberately (junk lengths are 0).

### [T002] Walk correspondence: unitSlope_eq_slopes + unitSlope_cases
- **Status**: done (2026-08-03T14:40Z; unitSlope_eq_slopes proved via entryStep/STAY/CROSS/ENTER invariants; unitSlope_cases was FALSE as stated - degenerate support=1,lengths 0=0 counterexample, machine-checked; corrected statement adopted with hypothesis (support = 1 → lengths 0 ≠ 0), proved; b2_log.jsonl entry added; ForMathlib lengths_final strengthening noted as user-decision alternative) | **File**: PhD/NewtonPolygons/Height.lean | **Depends on**: T001 |
  **Parallel**: after T001 | **Type**: lemma (hard) | **Leaves**: L6

#### Statement (Height.lean:73–89)
```lean
lemma unitSlope_eq_slopes {n j : ℕ}
    (h1 : P.vertexX n ≤ ((P.starting_point.1 + j : ℤ) : WithTop ℤ))
    (h2 : ((P.starting_point.1 + j : ℤ) : WithTop ℤ) < P.vertexX (n + 1)) :
    P.unitSlope j = P.slopes n

lemma unitSlope_cases (j : ℕ) :
    (∃ n : ℕ, P.vertexX n ≤ ((P.starting_point.1 + j : ℤ) : WithTop ℤ) ∧
      ((P.starting_point.1 + j : ℤ) : WithTop ℤ) < P.vertexX (n + 1)) ∨
    P.unitSlope j = ⊤
```

#### Proof sketch
1. Private invariant helper on `rightSlopeAux` mirroring its docstring
   (`Basic.lean:100–127`): if the token state (n, r) is *consistent* — segment n has
   `lengths n = w + 1` finite with `r ≤ w` and the token sits at absolute offset
   `vertexX (n+1) − (r + 1)` (equivalently `vertexX n ≤ pos ∧ pos < vertexX (n+1)`), or
   `lengths n = ⊤` — then `rightSlopeAux n r j` returns `slopes n'` for the segment n'
   containing offset pos + j (statement by induction on j, splitting the three aux branches).
2. Base j = 0: aux returns `slopes n`; consistency says pos is in segment n.
3. Step r+1 → r: pos+1 still in segment n (r units still ahead). Step r = 0: cross into
   segment n+1; case on `lengths (n+1)` (⊤ short-circuit = "pos+1.. all in segment n+1",
   consistent since `vertexX (n+2) = ⊤`; w+1 re-establishes invariant; 0 only in junk —
   `lengths_nonFinal` rules it out while `n + 1 + 1 < support`, else we are past the
   support and every later slope is `⊤` (`slopes_junk`) which yields the ⊤ arm of
   `unitSlope_cases`).
4. `rightSlope` (Basic.lean:158) seeds the invariant at n = 0 with the same three-way match —
   discharge each branch.
5. `unitSlope_cases`: same induction, tracking that failure of the in-segment condition only
   happens past `ofRight support`, where `slopes_junk`/`lengths_junk` give ⊤.

Off-script risk: the `WithTop ℤ` inequalities in the invariant are cast-heavy; keep them as
`omega`-dischargeable ℤ facts by destructing `vertexX` finiteness first.

#### Mathlib lemmas needed
`WithTop.coe_lt_coe`, `WithTop.coe_le_coe`, `WithTop.lt_top_iff_ne_top`, `Nat.rec` /
structural induction on the aux (no extra mathlib).

#### Sources
[BP] algorithm picture; `Basic.lean:119–125` worked example (the invariant IS the docstring).
Sizing: aux + docstring ~50 lines → expect 120–180 LOC incl. private helper.

#### Generality decision
Stated on arbitrary `NewtonPolygon₀` (not just constructed ones) — the maximality proof needs
it for competitors Q.

### [T003] unitSlope_mono
- **Status**: done (2026-08-03T15:55Z; degenerate-polygon case split + bracket ordering, worker) | **File**: PhD/NewtonPolygons/Height.lean | **Depends on**: T002 |
  **Parallel**: no | **Type**: lemma | **Leaves**: L7 (first part)

#### Statement (Height.lean:92)
```lean
lemma unitSlope_mono : Monotone P.unitSlope
```

#### Proof sketch
1. `monotone_nat_of_le_succ`; fix j.
2. `unitSlope_cases` at j and j+1: four combinations. ⊤ at j+1 arm: `le_top`. ⊤ at j only:
   show impossible or fine — need "⊤ is upward-closed": if `unitSlope j = ⊤` then j is past
   the support (cases lemma's proof content); then j+1 too — extract as a private corollary
   of T002's invariant (⊤ arm is monotone), or directly: segments to the right of junk are
   junk (`slopes_junk`).
3. Both in segments n ≤ n': `unitSlope_eq_slopes` twice + `slopes_increasing` chained
   (`Monotone` of `P.slopes` on ℕ via `monotone_nat_of_le_succ` inline).

#### Mathlib lemmas needed
`monotone_nat_of_le_succ`, `le_top`.

#### Sources
decomposition.md L7; convexity is `slopes_increasing` (structure field).

#### Generality decision
As T002.

### [CLEANUP-1] /cleanup on Height.lean (cadence)
- **Status**: done (2026-08-03T18:30Z; merged CLEANUP-1+2 golf: 833→741 lines, signatures byte-identical, axioms standard) | **File**: PhD/NewtonPolygons/Height.lean | **Depends on**: T003 |
  **Parallel**: no | **Type**: cleanup
- Run `/cleanup` (or `/clnup`) on the file; golf T001–T003, naming, docstrings. Blocks T004.

### [T004] Domain lemmas: height junk regions
- **Status**: done (2026-08-03T15:55Z; 4/4 domain lemmas incl. leftSlope-⊥ induction and rightSlope-⊤ upward closure, worker) | **File**: PhD/NewtonPolygons/Height.lean | **Depends on**: CLEANUP-1
  (math: T001) | **Parallel**: no | **Type**: lemmas | **Leaves**: L7 (rest)

#### Statement (Height.lean:95–113)
```lean
lemma height_eq_bot_iff (x : ℤ) : P.height x = ⊥ ↔ x < P.starting_point.1

lemma height_eq_top_mono {x y : ℤ} (hx : P.height x = ⊤) (hxy : x ≤ y) : P.height y = ⊤

lemma height_eq_heightFun (k : ℕ) (h : P.height (P.starting_point.1 + k) ≠ ⊤) :
    P.height (P.starting_point.1 + k) = (P.heightFun k : WithBotTop ℝ)

lemma unitSlope_ne_top_of_height_ne_top {c : ℕ}
    (h : P.height (P.starting_point.1 + c) ≠ ⊤) {i : ℕ} (hic : i < c) :
    P.unitSlope i ≠ ⊤
```

#### Proof sketch
1. `height_eq_bot_iff` ←: unfold `height`/`leftHeight`; show the embedded polygon's
   `leftSlope j = ⊥` for all j: `leftSlopeAux` on negative segments always reads `slopes n`
   with n < 0 = ⊥ (`toNewtonPolygon_slopes_of_neg`) — induction on j sliding through the
   width-0 negative segments (`toNewtonPolygon_lengths_of_neg`). →: right of start,
   `rightHeight` is `⊤` or a real coe, never ⊥ (both branches of the `if`).
2. `height_eq_top_mono`: `rightHeight k = ⊤` iff its guard fired iff `rightSlope (k−1) = ⊤`;
   ⊤ unit slopes are upward-closed (T002 ⊤-arm corollary); guard then fires for all later k.
   For y left of start: hypothesis `hx` is impossible there (step 1) — kill by cases.
3. `height_eq_heightFun`: unfold `height` (the `0 ≤ x − start` branch, `Int.toNat` of the
   difference = k); `rightHeight`'s else-branch IS `heightFun` (definitional: same sum,
   `startHeight` = `algebraMap … starting_point.2` by `toNewtonPolygon_startingPoint`);
   the guard is off by `h`.
4. `unitSlope_ne_top_of_height_ne_top`: contrapositive of step 2's mechanism: `unitSlope i = ⊤`
   with i < c makes the guard fire at c (upward closure again).

#### Mathlib lemmas needed
`Int.toNat_of_nonneg`, `Int.toNat_natCast`, `WithBotTop` coe disequalities (`coe_ne_top`,
`coe_ne_bot`, `bot_ne_top` family), `Finset.range` sums (already via heightFun).

#### Sources
decomposition.md L7; `Basic.lean:196–217` (`rightHeight`/`leftHeight`/`height` definitions).

#### Generality decision
Arbitrary `NewtonPolygon₀`. The ⊤-guard's exact firing condition is deliberately NOT exposed
as an iff at this stage (T005 only needs these four).

### [T005] Chord lemmas (discrete Jensen)
- **Status**: done (2026-08-03T15:55Z; 3/3 chords; height_le_chord landed WITH pre-authorized extra hypothesis (hxs : P.starting_point.1 ≤ x) - skeleton form false without it, counterexample in ticket note) | **File**: PhD/NewtonPolygons/Height.lean | **Depends on**: T003, T004 |
  **Parallel**: no | **Type**: lemmas | **Leaves**: L8

#### Statement (Height.lean:118–139)
```lean
lemma heightFun_chord {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (hc : P.height (P.starting_point.1 + c) ≠ ⊤) :
    ((c : ℝ) - a) * P.heightFun b ≤
      ((c : ℝ) - b) * P.heightFun a + ((b : ℝ) - a) * P.heightFun c

lemma le_heightFun (k : ℕ) (hk : P.height (P.starting_point.1 + k) ≠ ⊤) :
    (k : ℝ) * NewtonPolygon.toReal (P.unitSlope 0) ≤ P.heightFun k - P.heightFun 0

lemma height_le_chord {x y z : ℤ} (hxy : x ≤ y) (hyz : y ≤ z) {a c : ℝ}
    (hx : P.height x ≤ (a : WithBotTop ℝ)) (hz : P.height z ≤ (c : WithBotTop ℝ)) :
    P.height y ≤
      ((a + (c - a) / ((z : ℝ) - (x : ℝ)) * ((y : ℝ) - (x : ℝ)) : ℝ) : WithBotTop ℝ)
```

#### Proof sketch
1. Real increments `s i := toReal (P.unitSlope i)` are monotone on `i < c`: T003 +
   `unitSlope_ne_top_of_height_ne_top` (T004) + toReal respects ≤ on non-⊤ values — the ⊥
   case is the all-⊥ polygon where every increment is 0 (constant, monotone). Private helper.
2. `heightFun_chord`: heightFun b − heightFun a = Σ_{i∈[a,b)} s i ≤ (b−a)·s(b−1)? No —
   standard form: (c−b)·Σ_{[a,b)} s ≤ (b−a)·Σ_{[b,c)} s since every term of the left sum
   ≤ every term of the right (monotone). Rearrange (`nlinarith`/`linarith` after
   `Finset.sum` bounds via `Finset.sum_le_card_nsmul` / `Finset.card_nsmul_le_sum`).
3. `le_heightFun`: heightFun k − heightFun 0 = Σ_{i<k} s i ≥ k · s 0 by
   `Finset.card_nsmul_le_sum` with monotone s.
4. `height_le_chord`: if y < start: height y = ⊥ (T004), done. Else write x' := max x start;
   note height x' ≤ a still (if x < start ≤ x' … careful: use start as left endpoint only
   when x < start, in which case height start ≤ height-values… simplest: case split
   x ≥ start / x < start; in the second case replace (x, a) by (start, heightFun 0) and note
   the chord through (start, h0) and (z, c) at y is ≤ the stated chord because h0 ≤ a is NOT
   available — instead keep x: hx with height x = ⊥ gives no info, but the target chord line
   at y vs. the [start,z] chord: the stated RHS at y ≥ value of chord from (start, heightFun
   start-relative) … resolve numerically: from hz and heightFun_chord on [start, y', z'] the
   bound follows with h0 in place of a, and h0 enters the target via: heightFun 0 appears on
   both sides of the [start,z]-chord instance; conclude by transitivity + linarith over the
   two chords sharing the right endpoint (z, c). Work the algebra in ℝ; only at the end coe.
5. z = x degeneracy: y = x, `/0 = 0`, RHS = a, LHS ≤ a by hx. Explicit case.

Off-script risk: step 4's ⊥-left-endpoint algebra; if it fights, strengthen the statement
with `(hxs : P.starting_point.1 ≤ x)` and add a thin wrapper doing the case split — the
maximality proof (T016) always has integer endpoints ≥ start anyway. Allowed deviation,
record it.

#### Mathlib lemmas needed
`Finset.card_nsmul_le_sum`, `Finset.sum_le_card_nsmul` (verify exact names; alternatives
`Finset.sum_le_sum` + constant), `div_le_iff₀`, `le_div_iff₀`, `WithBotTop.coe_le_coe`.

#### Sources
decomposition.md L8 (attack log records why `hc` is load-bearing).

#### Generality decision
Division-free `heightFun_chord`; divided `height_le_chord` for consumer ergonomics.

### [CLEANUP-2] /cleanup on Height.lean (final per-file)
- **Status**: done (2026-08-03T18:30Z; see CLEANUP-1 merged pass) | **File**: PhD/NewtonPolygons/Height.lean | **Depends on**: T005 |
  **Parallel**: yes (with Spec/SpecConstruction work) | **Type**: cleanup

### [T006] pointHeight API
- **Status**: done (2026-08-03T11:34Z; 2/2, lake env lean clean, axioms standard) | **File**: PhD/NewtonPolygons/Spec.lean | **Depends on**: none |
  **Parallel**: yes | **Type**: def API | **Leaves**: L1

#### Statement (Spec.lean:39–43)
```lean
lemma pointHeight_eq_top_iff {v : ℕ → WithTop Γ} {k : ℕ} :
    pointHeight v k = ⊤ ↔ v k = ⊤

lemma pointHeight_coe {v : ℕ → WithTop Γ} {k : ℕ} {a : Γ} (h : v k = (a : WithTop Γ)) :
    pointHeight v k = ((algebraMap Γ ℝ a : ℝ) : WithBotTop ℝ)
```

#### Proof sketch
1. Both: unfold `pointHeight`, `cases hv : v k` / `rw [h]`; coe ≠ ⊤ via `WithBotTop` API.
2. Consider tagging `pointHeight_coe` `@[simp]`; leave `_eq_top_iff` untagged (loops with ⊤
   normal forms) — worker's judgement.

#### Mathlib lemmas needed
`WithBotTop.coe_ne_top` (exists — used in test.lean), match-reduction `rfl`s.

#### Sources
decomposition.md L1.

#### Generality decision
No `algebraMap` injectivity anywhere.

### [T007] Uniqueness cluster
- **Status**: done (2026-08-03T11:34Z; 3/3, term-mode via isBelow_iff_height; by_contra+not_le instead of deprecated push_neg) | **File**: PhD/NewtonPolygons/Spec.lean | **Depends on**: T006 |
  **Parallel**: yes | **Type**: theorems | **Leaves**: L3, L4

#### Statement (Spec.lean:79–96)
```lean
lemma starting_point_fst_eq (h₁ : IsNewtonPolygonOf v P₁) (h₂ : IsNewtonPolygonOf v P₂) :
    P₁.starting_point.1 = P₂.starting_point.1

lemma isBelow (h₁ : IsNewtonPolygonOf v P₁) (h₂ : IsNewtonPolygonOf v P₂) : P₁.IsBelow P₂

theorem height_eq (h₁ : IsNewtonPolygonOf v P₁) (h₂ : IsNewtonPolygonOf v P₂) (x : ℤ) :
    P₁.height x = P₂.height x
```

#### Proof sketch
1. `starting_point_fst_eq`: `h₁.start_mem` gives k₁ with `v k₁ ≠ ⊤` (coe); if
   `(k₁:ℤ) < P₂.start` then `h₂.start_le` forces `v k₁ = ⊤` — contradiction; so
   `P₂.start ≤ k₁ = P₁.start`; symmetrise; `le_antisymm`.
2. `isBelow`: `h₂.isGreatest P₁ (starting_point_fst_eq h₁ h₂) h₁.height_le`.
3. `height_eq`: `le_antisymm ((isBelow h₁ h₂) x) ((isBelow h₂ h₁) x)`.

#### Mathlib lemmas needed
`le_antisymm`; `WithTop.coe_ne_top`. (≤ 3-step proofs throughout.)

#### Sources
[BP] Definition 1 (uniqueness of "the lower boundary"); decomposition.md R1 prose.

#### Generality decision
Height-level equality only — structure-level uniqueness is FALSE (decomposition.md L2,
counterexample recorded). Do not attempt `P₁ = P₂`.

### [T008] Spec-level extraction: unitSlope_zero_mul_le
- **Status**: done (2026-08-03T16:25Z; height_le_chord pattern reuse, axioms standard) | **File**: PhD/NewtonPolygons/Spec.lean | **Depends on**: T005, T006 |
  **Parallel**: no | **Type**: theorem | **Leaves**: L17

#### Statement (Spec.lean:105–110)
```lean
theorem unitSlope_zero_mul_le (h : IsNewtonPolygonOf v P) {k : ℕ} {a : Γ}
    (hk : P.starting_point.1 < (k : ℤ)) (ha : v k = (a : WithTop Γ)) :
    NewtonPolygon.toReal (P.unitSlope 0) * ((k : ℝ) - (P.starting_point.1 : ℝ)) ≤
      algebraMap Γ ℝ a - algebraMap Γ ℝ P.starting_point.2
```

#### Proof sketch
1. `h.height_le k` + `pointHeight_coe ha`: `P.height k ≤ coe (algebraMap a)`, hence ≠ ⊤.
2. Write k = start + d, d : ℕ, d ≥ 1 (from hk; `Int.toNat` bookkeeping).
3. `height_eq_heightFun` (T004) turns step 1 into `P.heightFun d ≤ algebraMap a` in ℝ
   (`WithBotTop.coe_le_coe`).
4. `le_heightFun` (T005): `d * toReal (unitSlope 0) ≤ heightFun d − heightFun 0`;
   `heightFun_zero` = `algebraMap start.2`. `linarith` + cast `(d:ℝ) = k − start`.

#### Mathlib lemmas needed
`WithBotTop.coe_le_coe`, `Int.toNat_of_nonneg`, `push_cast` machinery.

#### Sources
[BP]: "We know all points are on or above the line y = mx" (quote at decomposition.md R3).
Replaces `firstBreak_slope_le` (`Test/test.lean:207`).

#### Generality decision
Stated via `toReal (unitSlope 0)`, NOT `P.slopes 0` — survives the ⊥-representation edge
case (decomposition.md L2 attack 3 / L17).

### [CLEANUP-3] /cleanup on Spec.lean (cadence)
- **Status**: done (2026-08-03T16:25Z; merged into CLEANUP-4 final Spec golf - T008 landed clean, file small) | **File**: PhD/NewtonPolygons/Spec.lean | **Depends on**: T008 |
  **Parallel**: no | **Type**: cleanup. Blocks T009.

### [T009] IsPure lemmas
- **Status**: done (2026-08-03T16:40Z; case chase on support with decide/coe_lt_coe casts; omit added; main context) | **File**: PhD/NewtonPolygons/Spec.lean | **Depends on**: CLEANUP-3 |
  **Parallel**: no | **Type**: lemmas | **Leaves**: L18

#### Statement (Spec.lean:124–133)
```lean
lemma IsPure.support_eq_one {P : NewtonPolygon₀ (Γ := Γ)} {m : ℝ} (h : P.IsPure m) :
    P.support = 1

lemma isPure_of_support_eq_one {P : NewtonPolygon₀ (Γ := Γ)} {m : ℝ}
    (hs : P.support = 1) (hm : P.slopes 0 = (m : WithBotTop ℝ)) : P.IsPure m
```

#### Proof sketch
1. `support_eq_one`: support = 0 impossible (`slopes_junk` at 0 vs `h.1` coe ≠ ⊤). If
   `2 ≤ support`: `1 + 1 < support` gives slopes 1 real (`slopes_nonFinal`) contra `h.2`;
   `1 + 1 = support` gives `slopes_final 1 ⟨rfl-ish, Or.inl h.2⟩` forcing support = 1,
   contra. `WithTop ℕ` trichotomy via `Nat.cast` cases / `interval_cases`-style on the coe.
2. Converse: `slopes_junk 1 (by rw [hs]; exact_mod_cast one_le_one)` gives slopes 1 = ⊤;
   pair with hm.

#### Mathlib lemmas needed
`WithTop.coe_le_coe`, `WithTop` `one` numerals (`Nat.cast_ofNat` normalisation); `le_refl`.

#### Sources
[BP]: "A polynomial f(x) is pure if its Newton polygon has only one slope" (quote at L18).
Replaces `NewtonPolygon.IsPure` of `Test/test.lean:402`.

#### Generality decision
Representation-dependent by design; consumed on constructed polygons (recorded limitation,
L18).

### [CLEANUP-4] /cleanup on Spec.lean (final per-file)
- **Status**: done (2026-08-03T18:20Z; -17 lines, 4 gates pass, new helper starting_point_fst_le, pointHeight_eq_top_iff simp-tag deferred until SpecConstruction quiescent) | **File**: PhD/NewtonPolygons/Spec.lean | **Depends on**: T009 |
  **Parallel**: yes | **Type**: cleanup

### [T010] Admissibility lemmas
- **Status**: done (2026-08-03T19:05Z; 2/2 - affine witness needs no max (anchor on the line), bddBelow via unitSlope_zero_mul_le alone) | **File**: PhD/NewtonPolygons/SpecConstruction.lean | **Depends on**:
  T008 | **Parallel**: yes (with T011–T013) | **Type**: lemmas | **Leaves**: L16 (two of
  three)

#### Statement (SpecConstruction.lean:45–57)
```lean
lemma isAdmissible_of_affine_bound {m b : ℝ}
    (h : ∀ (k : ℕ) (a : Γ), v k = (a : WithTop Γ) → m * k + b ≤ algebraMap Γ ℝ a) :
    IsAdmissible v

lemma IsNewtonPolygonOf.bddBelow {P : NewtonPolygon₀ (Γ := Γ)} (h : IsNewtonPolygonOf v P)
    {k : ℕ} (hk : (k : ℤ) = P.starting_point.1) :
    BddBelow (slopeSet v k P.starting_point.2)
```

#### Proof sketch
1. Affine bound: fix point (i₀,i₁); for (k,a) with k > i₀: slopeReal = (A−I)/(k−i₀) where
   A ≥ m·k+b and I = algebraMap i₁ (I ≥ m·i₀+b too — i₁ is itself a point). Then
   slopeReal ≥ m − max 0 (I − m·i₀ − b) (since k − i₀ ≥ 1 and numerator ≥ m(k−i₀) − (I −
   m·i₀ − b)). Witness `m − max 0 (I − m·i₀ − b)`; `div` bounds via `le_div_iff₀`
   (k − i₀ > 0).
2. `bddBelow`: witness `toReal (P.unitSlope 0)`. Member slopeReal k' a with k' > k:
   T008 (`unitSlope_zero_mul_le`, using `hk` to rewrite the anchor and `h.start_mem` to
   identify `v k = coe start.2`) gives the line bound; divide.

#### Mathlib lemmas needed
`bddBelow_iff` / `BddBelow` via `lowerBounds` membership, `le_div_iff₀`, `div_le_iff₀`,
`le_max_left/right`.

#### Sources
decomposition.md L16 (witness arithmetic checked both signs in attack log).

#### Generality decision
`IsAdmissible` over all points (design note in plan.md).

### [T011] Algorithm line bounds
- **Status**: done (2026-08-03T12:55Z; 4/4 line bounds, csInf argument as sketched, axioms standard) | **File**: PhD/NewtonPolygons/SpecConstruction.lean | **Depends on**:
  none | **Parallel**: yes | **Type**: lemmas | **Leaves**: L9 (bounds)

#### Statement (SpecConstruction.lean:66–100)
```lean
lemma nextStep_slope_le {i₀ : ℕ} {i₁ : Γ} {j₀ l : ℕ} {j₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .nextVertex j₀ j₁ l m) {k : ℕ} (hk : i₀ < k) {a : Γ}
    (ha : v k = (a : WithTop Γ)) :
    m * ((k : ℝ) - i₀) ≤ algebraMap Γ ℝ a - algebraMap Γ ℝ i₁

lemma nextStep_slope_lt … (hk : j₀ < k) … :
    m * ((k : ℝ) - i₀) < algebraMap Γ ℝ a - algebraMap Γ ℝ i₁

lemma limitingRay_slope_lt … (h : nextStep v i₀ i₁ = .limitingRay m) (hk : i₀ < k) … : … < …

lemma infiniteRay_slope_le … (h : nextStep v i₀ i₁ = .infiniteRay m) (hk : i₀ < k) … : … ≤ …
```
(full statements in the skeleton; conclusions as first lemma with </≤ as shown)

#### Proof sketch
1. `nextStep_slope_le`: port of `Test/test.lean:184` `step_slope_le` at Γ-generality:
   membership `slopeReal i₀ k i₁ a ∈ slopeSet v i₀ i₁`, then
   `nextVertex_slope_eq_sInf'' + csInf_le (nextVertex_bddBelow …)`, then `le_div_iff₀`
   ((k:ℝ) − i₀ > 0) and rearrange (`linarith`).
2. `nextStep_slope_lt`: as 1, plus: equality would put k in
   `achievingSet v i₀ i₁ (sInf …)`; `nextVertex_j₀_eq_max` + `Finset.le_max'` forces k ≤ j₀,
   contra `hk`.
3. `limitingRay_slope_lt`: `limitingRay_slope_eq_sInf` + `csInf_le (limitingRay_bddBelow …)`
   for ≤; equality would witness attainment, contra the `limitingRay` branch condition
   (extract via `nextStep` split as in `Test/test.lean:245`
   `not_attained_of_nextStep_limitingRay` — re-prove locally at Γ-generality, ~10 LOC).
4. `infiniteRay_slope_le`: `infiniteRay_slope_eq_sInf` + `csInf_le (infiniteRay_bddBelow …)`.

#### Mathlib lemmas needed
`csInf_le`, `le_div_iff₀`, `Finset.le_max'`, `Set.Finite.mem_toFinset`.

#### Sources
[BP] algorithm items 3a–3c (quotes at decomposition.md R2); proved model:
`Test/test.lean:184–203` (20 lines) and `:227–251` (inversions). Expect ~30 LOC each.

#### Generality decision
Γ-generic (test.lean's versions are specialised to `coeffVal K f`; these supersede them).

### [T012] Ray approximation lemmas
- **Status**: done (2026-08-03T12:55Z; 2/2 + 4 private step-inversion/gap helpers ported from test.lean at generic v; Set-level finiteness to dodge decidability) | **File**: PhD/NewtonPolygons/SpecConstruction.lean | **Depends on**:
  none | **Parallel**: yes | **Type**: lemmas | **Leaves**: L9a, L9b

#### Statement (SpecConstruction.lean:105–115)
```lean
lemma limitingRay_exists_slope_lt {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .limitingRay m) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ k > N, ∃ a : Γ, v k = (a : WithTop Γ) ∧ slopeReal i₀ k i₁ a < m + ε

lemma infiniteRay_exists_achieving_gt {i₀ : ℕ} {i₁ : Γ} {m : ℝ}
    (h : nextStep v i₀ i₁ = .infiniteRay m) (N : ℕ) :
    ∃ k > N, k ∈ achievingSet v i₀ i₁ m
```

#### Proof sketch
1. L9b first (easy): `achievingSet_infinite_of_nextStep_infiniteRay` (re-prove locally from
   the `nextStep` split, as `Test/test.lean:253`) + `Set.Infinite.exists_gt`; note
   `infiniteRay_slope_eq_sInf` aligns m.
2. L9a: let S := slopes from points with index ≤ max N i₀+1 — a finite set (image of a
   finite index set). Each element > m (attainment fails: `limitingRay` branch). If S = ∅
   take δ := ε else δ := min ε (S.min' − m) > 0. `Real.lt_sInf_add`-style: since
   m = sInf (slopeSet …) (`limitingRay_slope_eq_sInf`) and δ > 0, obtain a member slope
   < m + δ (`csInf_lt_iff`/`Real.add_pos` variant: `exists_lt_of_csInf_lt` on m + δ). Its
   index k cannot be ≤ max N i₀+1 (its slope would be in S, ≥ m + δ ≥ … contradiction), so
   k > N; unpack membership for a.

#### Mathlib lemmas needed
`Set.Infinite.exists_gt` (verified), `exists_lt_of_csInf_lt` (verify name; fallback:
`csInf_lt_iff` with `limitingRay_bddBelow`), `Finset.min'` API, `Set.Finite.image`,
`Set.Finite.subset (Set.finite_Iic _)`.

#### Sources
decomposition.md L9 attack log ("no points beyond N" refuted: the slope set would be finite
and its inf attained).

#### Generality decision
Γ-generic; `k > N` (not ≥) for direct use in T016's "beyond every x" step.

### [CLEANUP-5] /cleanup on SpecConstruction.lean (cadence)
- **Status**: done (2026-08-03T14:05Z; golfed -22 lines, 4 gates pass, helpers renamed to Construction.lean convention: limitingRay_sInf_not_mem, limitingRay_lt_of_mem_slopeSet, exists_pos_add_le_of_finite, infiniteRay_achievingSet_infinite) | **File**: PhD/NewtonPolygons/SpecConstruction.lean | **Depends on**:
  T012 | **Parallel**: no | **Type**: cleanup. Blocks T013.

### [T013] Anchor lemmas for the constructed polygon
- **Status**: done (2026-08-03T14:50Z; 2/2 + private starting_point_eq helper stated via findFirstFinite = some to dodge DecidablePred-in-statement; axioms standard) | **File**: PhD/NewtonPolygons/SpecConstruction.lean | **Depends on**:
  CLEANUP-5 | **Parallel**: yes (with T014) | **Type**: lemmas | **Leaves**: L10

#### Statement (SpecConstruction.lean:109–115)
```lean
lemma newtonPolygon₀OfSeq_start_mem (h : ∃ i, v i ≠ ⊤) :
    ∃ k : ℕ, (k : ℤ) = (newtonPolygon₀OfSeq v).starting_point.1 ∧
      v k = ((newtonPolygon₀OfSeq v).starting_point.2 : WithTop Γ)

lemma newtonPolygon₀OfSeq_start_le (h : ∃ i, v i ≠ ⊤) :
    ∀ k : ℕ, (k : ℤ) < (newtonPolygon₀OfSeq v).starting_point.1 → v k = ⊤
```

#### Proof sketch
1. `findFirstFinite v 0 = some (Nat.find hex, choose)` under h (rewrite `hex : ∃ i ≥ 0, …`
   from h via `⟨i, Nat.zero_le _, hi⟩`); the `starting_point` match reduces.
2. `start_mem`: k := Nat.find hex; y-coordinate: `(Option.ne_none_iff_exists.mp …).choose_spec`
   gives `v k = coe choose` — the exact pattern of `Test/test.lean:156–173`
   (`findFirstFinite_zero`), reusable nearly verbatim.
3. `start_le`: `Nat.find_min hex` (indices below Nat.find are not finite) after casting
   `(k:ℤ) < (Nat.find hex : ℤ)` to ℕ.

#### Mathlib lemmas needed
`Nat.find_spec`, `Nat.find_min`, `Option.ne_none_iff_exists`, `Int.natCast_lt`.

#### Sources
Model: `Test/test.lean:156–173` (proved). decomposition.md L10.

#### Generality decision
The ONLY tickets that unfold `findFirstFinite`'s `Nat.find`/`choose` — keep it contained
here.

### [T014] Walk correspondence for the constructed polygon
- **Status**: done (2026-08-03T17:35Z; WalkInv structure invariant + walk_step induction, axioms standard) | **File**: PhD/NewtonPolygons/SpecConstruction.lean | **Depends on**:
  T001, T004, T011, T013 (and CLEANUP-5) | **Parallel**: yes (with T013 once its deps done) |
  **Type**: lemmas (hard) | **Leaves**: L11, L12

#### Statement (SpecConstruction.lean:120–130)
```lean
lemma newtonPolygon₀OfSeq_vertexX {n j₀ l : ℕ} {j₁ : Γ} {m : ℝ}
    (h : newtonPolygon v n = some (.nextVertex j₀ j₁ l m)) :
    (newtonPolygon₀OfSeq v).vertexX (n + 1) = ((j₀ : ℤ) : WithTop ℤ)

lemma newtonPolygon₀OfSeq_height_vertex {n j₀ l : ℕ} {j₁ : Γ} {m : ℝ}
    (h : newtonPolygon v n = some (.nextVertex j₀ j₁ l m)) :
    (newtonPolygon₀OfSeq v).height (j₀ : ℤ) = ((algebraMap Γ ℝ j₁ : ℝ) : WithBotTop ℝ)
```

#### Proof sketch
1. Strong induction on n carrying BOTH conclusions plus "input vertex of step n = vertexX n
   as anchor data (x = i₀, height = algebraMap i₁)" — a private combined invariant is
   allowed; the two public lemmas project from it (they stay single-conclusion).
2. Base n = 0: input vertex = anchor (T013); `newtonPolygon_lengths 0 = l = j₀ − i₀`
   (`nextVertex_l_eq`, `nextVertex_lt`); `vertexX_succ` + `vertexX_zero` (T001).
3. Step: `newtonPolygon_nextVertex_of_lt` gives step n's `nextVertex`; `nextStep_nextVertex''`
   identifies step n+1's input with step n's output; lengths sequence at n+1 is l'
   (`newtonPolygon_lengths` unfolds on the `some`).
4. Heights: within segment n the unit slopes are `slopes n = m` (T002 `unitSlope_eq_slopes`
   via the vertexX brackets from step 2/3); telescope `heightFun` over the l units
   (`Finset.sum_const`-style after rewriting each term); point recurrence: `nextVertex_slope_eq_sInf'`
   gives m = (algebraMap j₁ − algebraMap i₁)/(j₀ − i₀), so algebraMap j₁ = algebraMap i₁ +
   m·l; `height_eq_heightFun` (T004) with the ⊤-guard discharged by
   `unitSlope_ne_top`-style reasoning (interior slopes real: the segment's slope is the real
   m).

#### Mathlib lemmas needed
`Finset.sum_congr` / `Finset.sum_const`, `nextVertex_l_eq`, `nextVertex_lt`,
`nextVertex_slope_eq_sInf'`, `newtonPolygon_nextVertex_of_lt`, `nextStep_nextVertex''`,
`eq_div_iff` + casts.

#### Sources
decomposition.md L11/L12; sizing vs. `Construction.lean:574–628` chain (~55 lines) → expect
60–90 LOC per lemma incl. shared private invariant.

#### Generality decision
Stated per-step (hypothesis `newtonPolygon v n = some (.nextVertex …)`) rather than
quantified over segments — matches how T015/T016 consume them.

### [T015] Below: newtonPolygon₀OfSeq_height_le
- **Status**: done (2026-08-03T17:35Z; fuel induction height_le_aux over steps; unboundedBelow killed by IsAdmissible directly; tail via slopeSet-empty port) | **File**: PhD/NewtonPolygons/SpecConstruction.lean | **Depends on**:
  T011, T014 | **Parallel**: no | **Type**: theorem (hard) | **Leaves**: L13

#### Statement (SpecConstruction.lean:136–138)
```lean
theorem newtonPolygon₀OfSeq_height_le (h1 : ∃ i, v i ≠ ⊤) (h2 : IsAdmissible v) (k : ℕ) :
    (newtonPolygon₀OfSeq v).height (k : ℤ) ≤ pointHeight v k
```

#### Proof sketch
1. If `v k = ⊤`: RHS ⊤, `le_top`. If k < anchor: height ⊥ (T004 `height_eq_bot_iff` + T013),
   `bot_le`. Else locate k: strong induction / case on the step-n bracket containing k
   (T014's vertexX chain: brackets increase to cover [anchor, ∞) or terminate).
2. In-segment k (step n from (i₀,i₁), nextVertex slope m): height at k = algebraMap i₁ +
   m·(k − i₀) (T014 step-4 machinery: unit slopes constant on the segment); T011
   `nextStep_slope_le` bounds it by algebraMap a. `unboundedBelow` step: killed by h2 +
   `unboundedBelow` inversion (`Construction.lean:474`).
3. Final rays: height along the ray = line of slope m (T002: bracket is [vertexX, ⊤));
   `limitingRay_slope_lt` / `infiniteRay_slope_le` (T011) bound by the point.
4. Past a `tail`: no finite points remain — `slopeSet = ∅` inversion (port
   `slopeSet_eq_empty_of_nextStep_tail`, `Test/test.lean:227`, ~15 LOC, include here as a
   private lemma): all later `v k = ⊤`, so case 1 applies. (Heights there are ⊤ anyway.)

#### Mathlib lemmas needed
`le_top`, `bot_le`, `WithBotTop.coe_le_coe`; the T011/T014 clusters.

#### Sources
decomposition.md L13 (attack log: induction must carry "below on [anchor, current vertex]",
not just the last segment).

#### Generality decision
Hypotheses h1, h2 exactly as the milestone (no hidden strengthening).

### [CLEANUP-6] /cleanup on SpecConstruction.lean (cadence)
- **Status**: done (2026-08-03T20:10Z; merged CLEANUP-6+7: 853→778 lines, dedup of =/≤ height layers + 5 shared unfold helpers, 18 public signatures byte-identical, endpoints axiom-clean) | **File**: PhD/NewtonPolygons/SpecConstruction.lean | **Depends on**:
  T015 | **Parallel**: no | **Type**: cleanup. Blocks T016.

### [T016] Greatest: newtonPolygon₀OfSeq_isGreatest
- **Status**: done (2026-08-03T19:05Z; 7-helper private layer + isGreatest_aux fuel walk; tail handled positively via height_eq_top_of_tail; epsilon-criterion helper le_coe_of_forall_pos_add replaces ENNReal-only mathlib lemma; axioms standard) | **File**: PhD/NewtonPolygons/SpecConstruction.lean | **Depends on**:
  CLEANUP-6 (math: T005, T012, T014) | **Parallel**: no | **Type**: theorem (hardest) |
  **Leaves**: L14

#### Statement (SpecConstruction.lean:142–148)
```lean
theorem newtonPolygon₀OfSeq_isGreatest (h1 : ∃ i, v i ≠ ⊤) (h2 : IsAdmissible v)
    (Q : NewtonPolygon₀ (Γ := Γ))
    (hQ : Q.starting_point.1 = (newtonPolygon₀OfSeq v).starting_point.1)
    (hle : ∀ k : ℕ, Q.height (k : ℤ) ≤ pointHeight v k) :
    Q.IsBelow (newtonPolygon₀OfSeq v)
```

#### Proof sketch
Fix x : ℤ; show Q.height x ≤ P.height x (P := constructed).
1. x < anchor: Q.height x = ⊥ (T004 via hQ). x = anchor: hle + T013 (P touches its anchor;
   pointHeight there = P.height by T014-base/T013).
2. x inside segment n, endpoints Xₙ < Xₙ₊₁ (T014): both endpoints touch points (T014 +
   `nextVertex_j₁_eq`), so `hle` bounds Q at the endpoints by P's endpoint heights;
   `height_le_chord` (T005) on Q over [Xₙ, Xₙ₊₁] bounds Q at x by the chord = P at x
   (P affine on the segment: T002/T014). Induction over n to reach the segment containing x
   is the same bracket walk as T015.
3. x on a final `infiniteRay` from (X, Y): T012 L9b gives an on-ray point k > x;
   `height_le_chord` over [X, k] with endpoint bounds Y (touching) and pointHeight k
   (= Y + m(k−X), on the ray via `achievingSet` membership + `infiniteRay_slope_eq_sInf`);
   chord at x = Y + m(x−X) = P.height x.
4. x on a final `limitingRay` from (X, Y): for ε > 0, T012 L9a gives k > x with slope
   < m + ε; chord over [X, k] bounds Q.height x ≤ Y + (m+ε)(x−X); conclude
   ≤ Y + m(x−X) = P.height x by `le_of_forall_pos_le_add` (coe-compat: work in ℝ after
   noting Q.height x ≠ ⊤ from the ε-bound, then `WithBotTop.coe_le_coe`; the ⊥ case is
   trivial).
5. x past a `tail`: P.height x = ⊤ (T004 `height_eq_top_mono` from the first ⊤), `le_top`.

#### Mathlib lemmas needed
ε-limit step: NOTE `le_of_forall_pos_le_add` exists only for ENNReal — for the ℝ-valued
bound use `by_contra` + instantiate ε := (LHS − RHS)/2 + `linarith` (or
`le_of_forall_lt`-family, Order/Basic.lean:354). `Set.Infinite.exists_gt` confirmed at
Order/Interval/Finset/Basic.lean:908. `le_top`, `bot_le`; T005/T012/T014 clusters.

#### Sources
decomposition.md L14 + R2 "Greatest" prose (the full argument, including why near-inf slopes
occur beyond every x).

#### Generality decision
Competitor Q is an arbitrary `NewtonPolygon₀` — this is why the Height layer (T002/T005) is
stated generically and not just for constructed polygons.

### [CLEANUP-ALL-1] /cleanup-all (pre-milestone)
- **Status**: done (2026-08-03T19:15Z; realized as the three per-file golf passes (CLEANUP-1+2, 3+4, 5) all gated before the milestone assembly; note: T016 landed before the SpecConstruction golf - covered by post-hoc CLEANUP-6+7) | **Depends on**: T007, T009, T010, T016 (all proof tickets except the
  assembly) | **Parallel**: no | **Type**: cleanup-all
- Project-wide pass over PhD/NewtonPolygons/ before the milestone assembly.

### [T017] MILESTONE — assembly: existence + corollaries
- **Status**: done (2026-08-03T19:15Z; anonymous-constructor assembly exactly as planned - 4 fields one line each, powerSeries corollary definitional, not_forall 4-liner; oleans rebuilt; all 6 endpoints axiom-checked standard) | **File**: PhD/NewtonPolygons/SpecConstruction.lean | **Depends on**:
  T013, T015, T016, CLEANUP-ALL-1 | **Parallel**: no | **Type**: theorem (assembly) |
  **Leaves**: L15, L16 (last one)

#### Statement (SpecConstruction.lean:153–168)
```lean
theorem isNewtonPolygonOf_newtonPolygon₀OfSeq (h1 : ∃ i, v i ≠ ⊤) (h2 : IsAdmissible v) :
    IsNewtonPolygonOf v (newtonPolygon₀OfSeq v)

theorem isNewtonPolygonOf_powerSeries {R : Type*} [Semiring R] (val : R → WithTop Γ)
    (f : PowerSeries R) (h1 : ∃ i, coeffSeq val f i ≠ ⊤) (h2 : IsAdmissible (coeffSeq val f)) :
    IsNewtonPolygonOf (coeffSeq val f) (newtonPolygon₀OfPowerSeries val f)

lemma not_isNewtonPolygonOf_of_forall_eq_top (h : ∀ i, v i = ⊤) (P : NewtonPolygon₀ (Γ := Γ)) :
    ¬ IsNewtonPolygonOf v P
```

#### Proof sketch
1. Existence: `⟨newtonPolygon₀OfSeq_start_le v h1, newtonPolygon₀OfSeq_start_mem v h1,
   newtonPolygon₀OfSeq_height_le v h1 h2, newtonPolygon₀OfSeq_isGreatest v h1 h2⟩`
   (field order per structure).
2. Power series: `isNewtonPolygonOf_newtonPolygon₀OfSeq` at `coeffSeq val f`
   (`newtonPolygon₀OfPowerSeries` unfolds definitionally).
3. `not_…`: intro spec; `spec.start_mem` gives `v k = coe …`; `h k` says ⊤; `WithTop.coe_ne_top`.
4. Then `#print axioms isNewtonPolygonOf_newtonPolygon₀OfSeq` — expect only propext /
   Quot.sound / Classical.choice.

#### Mathlib lemmas needed
`WithTop.coe_ne_top`. Anonymous constructor.

#### Sources
[BP] "It should be clear that by construction this constructs the lower convex hull…" — this
ticket IS that sentence, proved.

#### Generality decision
Marked assembly node (decomposition.md L15): if the constructor takes more than a line per
field, the split upstream is wrong — hard-stop and report rather than inline new math.

### [CLEANUP-7] /cleanup on SpecConstruction.lean (final per-file)
- **Status**: done (2026-08-03T20:10Z; see CLEANUP-6 merged pass) | **File**: PhD/NewtonPolygons/SpecConstruction.lean | **Depends on**:
  T017 | **Type**: cleanup

### [CLEANUP-FINAL] /cleanup-all (project)
- **Status**: done (2026-08-03T20:15Z; final sweep: full build 1871 jobs clean, 0 sorries in all 3 files, all 6 endpoints standard axioms only, line length ≤100 unicode-verified) | **Depends on**: everything | **Type**: cleanup-all
- Final pass; then `/pre-submit` when the user wants to consider promotion of
  PhD/NewtonPolygons/ into ForMathlib.
