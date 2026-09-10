/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/

import PhD.ForMathlib.NumberTheory.NewtonPolygon.Basic

/-!
# Height API for one-sided Newton polygons

Discrete convexity infrastructure for `NewtonPolygon₀.height`, with no reference to the
construction algorithm.

* `NewtonPolygon₀.unitSlope` — the slope of the polygon on the `j`-th unit interval right of the
  starting vertex (`rightSlope` of the embedded polygon).
* `NewtonPolygon₀.vertexX` — the `x`-coordinate of the `n`-th vertex (partial sums of `lengths`).
* `NewtonPolygon₀.heightFun` — the real-valued height `k` steps right of the start (the honest
  value carried by `height` on the non-junk region).
* `NewtonPolygon₀.unitSlope_mono` — unit slopes are monotone: the polygon is convex.
* `NewtonPolygon₀.heightFun_chord`, `NewtonPolygon₀.height_le_chord` — a convex polygon lies
  on/below each of its chords (discrete Jensen).

These are the workhorses for the lower-convex-hull specification in `Spec.lean`: both the
"polygon below the points" and the "greatest such polygon" halves reduce to chord comparisons.
-/

variable {Γ : Type*} [CommSemiring Γ] [Algebra Γ ℝ]

namespace NewtonPolygon₀

variable (P : NewtonPolygon₀ (Γ := Γ))

/-- The slope of the polygon on the unit interval `[x₀ + j, x₀ + j + 1]`, `j` steps to the right
of the starting vertex: `rightSlope` of the embedded doubly-infinite polygon. -/
noncomputable def unitSlope (j : ℕ) : WithBotTop ℝ :=
  P.toNewtonPolygon.rightSlope j

/-- The `x`-coordinate of the `n`-th vertex of a one-sided polygon: the starting `x`-coordinate
plus the first `n` segment lengths. `⊤` once an infinite segment has been passed. -/
def vertexX (n : ℕ) : WithTop ℤ :=
  (P.starting_point.1 : WithTop ℤ) + ∑ i ∈ Finset.range n, (P.lengths i).map (fun l : ℕ => (l : ℤ))

section
omit [CommSemiring Γ] [Algebra Γ ℝ]

/-- The `0`-th vertex is the starting vertex. -/
@[simp] lemma vertexX_zero : P.vertexX 0 = (P.starting_point.1 : WithTop ℤ) := by
  simp [vertexX]

/-- Passing segment `n` moves the vertex to the right by that segment's length. -/
lemma vertexX_succ (n : ℕ) :
    P.vertexX (n + 1) = P.vertexX n + (P.lengths n).map (fun l : ℕ => (l : ℤ)) := by
  rw [vertexX, vertexX, Finset.sum_range_succ, add_assoc]

/-- The vertices march to the right. -/
lemma vertexX_mono : Monotone P.vertexX :=
  monotone_nat_of_le_succ fun n => by
    rw [vertexX_succ]
    exact le_add_of_nonneg_right (by cases h : P.lengths n <;> simp)

end

/-- The real-valued height of the polygon `k` integer steps to the right of the starting vertex:
starting height plus the accumulated unit slopes. On the honest (non-junk) region this is the
value carried by `height`; past the right end it is junk. -/
noncomputable def heightFun (k : ℕ) : ℝ :=
  algebraMap Γ ℝ P.starting_point.2 +
    ∑ i ∈ Finset.range k, NewtonPolygon.toReal (P.unitSlope i)

/-- At the starting vertex the height is the starting height. -/
@[simp] lemma heightFun_zero : P.heightFun 0 = algebraMap Γ ℝ P.starting_point.2 := by
  simp [heightFun]

/-- One step to the right adds the unit slope crossed. -/
lemma heightFun_succ (k : ℕ) :
    P.heightFun (k + 1) = P.heightFun k + NewtonPolygon.toReal (P.unitSlope k) := by
  rw [heightFun, heightFun, Finset.sum_range_succ, add_assoc]

/-! ### The walk versus the vertex positions

`unitSlope` is defined by the structural walk `NewtonPolygon.rightSlopeAux`, which carries the
number `r` of unit intervals of the current segment still lying ahead of the token, while
`vertexX` records absolute positions. The private lemmas below bridge the two: `entryStep` names
the state the walk is in on arriving at the left end of a segment, `rightSlopeAux_of_le` says the
walk stays inside a segment while units of it remain, and `rightSlopeAux_cross` says it enters the
next segment once they run out. `rightSlope_offset` then propagates the entry state from vertex to
vertex. -/

section
omit [CommSemiring Γ] [Algebra Γ ℝ]

/-- The value returned by the right-walk on arriving at the left end of segment `n` with `j` unit
steps still to take, as a function of the length of that segment: an infinite segment covers
everything to its right, a segment of width `w + 1` is entered on its first unit with `w` units
ahead, and a segment of width `0` is stepped over (only possible in the junk region). This is both
the state `rightSlope` starts in and the state `rightSlopeAux` enters at each vertex. -/
private def entryStep (NP : NewtonPolygon (Γ := Γ)) (n : ℤ) : WithTop ℕ → ℕ → WithBotTop ℝ
  | ⊤, _ => NP.slopes n
  | ((w + 1 : ℕ) : WithTop ℕ), j => NP.rightSlopeAux n w j
  | ((0 : ℕ) : WithTop ℕ), j => NP.rightSlopeAux n 0 j

/-- A segment of width `w + 1` is entered on its first unit, with `w` units ahead. -/
private lemma entryStep_coe_succ (NP : NewtonPolygon (Γ := Γ)) (n : ℤ) (w j : ℕ) :
    entryStep NP n ((w + 1 : ℕ) : WithTop ℕ) j = NP.rightSlopeAux n w j := rfl

/-- A segment of width `0` is entered with no units of it ahead. -/
private lemma entryStep_zero (NP : NewtonPolygon (Γ := Γ)) (n : ℤ) (j : ℕ) :
    entryStep NP n 0 j = NP.rightSlopeAux n 0 j := rfl

/-- The walk is seeded at the left end of segment `0`. -/
private lemma rightSlope_eq_entryStep (NP : NewtonPolygon (Γ := Γ)) (j : ℕ) :
    NP.rightSlope j = entryStep NP 0 (NP.lengths 0) j := by
  rw [NewtonPolygon.rightSlope]
  cases h : NP.lengths 0 with
  | top => rfl
  | coe w => cases w <;> rfl

/-- While units of the current segment remain ahead of the token, the walk stays in it. -/
private lemma rightSlopeAux_of_le (NP : NewtonPolygon (Γ := Γ)) (n : ℤ) :
    ∀ {r j : ℕ}, j ≤ r → NP.rightSlopeAux n r j = NP.slopes n := by
  intro r j
  induction j generalizing r with
  | zero => intro _; rfl
  | succ j ih =>
    intro h
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    exact ih (by omega)

/-- Once the `r` units of segment `n` ahead of the token are used up, the next step enters
segment `n + 1` at its left end. -/
private lemma rightSlopeAux_cross (NP : NewtonPolygon (Γ := Γ)) (n : ℤ) (j : ℕ) :
    ∀ r : ℕ, NP.rightSlopeAux n r (j + r + 1) = entryStep NP (n + 1) (NP.lengths (n + 1)) j := by
  intro r
  induction r with
  | zero =>
    show NP.rightSlopeAux n 0 (j + 1) = _
    rw [NewtonPolygon.rightSlopeAux]
    cases h : NP.lengths (n + 1) with
    | top => rfl
    | coe w => cases w <;> rfl
  | succ r ih =>
    show NP.rightSlopeAux n (r + 1) ((j + r + 1) + 1) = _
    rw [NewtonPolygon.rightSlopeAux]
    exact ih

/-- In `WithTop ℕ`, a natural number strictly below `s` is below `s` by at least one. -/
private lemma coe_add_one_le_of_lt {i : ℕ} {s : WithTop ℕ} (h : (i : WithTop ℕ) < s) :
    (i : WithTop ℕ) + 1 ≤ s := by
  induction s using WithTop.recTopCoe with
  | top => exact le_top
  | coe k =>
    rw [show ((i : WithTop ℕ) + 1) = ((i + 1 : ℕ) : WithTop ℕ) by push_cast; ring]
    exact WithTop.coe_le_coe.2 (WithTop.coe_lt_coe.1 h)

/-- An index inside the support whose successor is not pins the support: it is exactly `i + 1`. -/
private lemma support_eq_add_one {i : ℕ} (h1 : (i : WithTop ℕ) < P.support)
    (h2 : ¬ (i : WithTop ℕ) + 1 < P.support) : (i : WithTop ℕ) + 1 = P.support :=
  le_antisymm (coe_add_one_le_of_lt h1) (not_lt.1 h2)

/-- A segment of length `0` occurs only past the support (where all lengths are junk `0`), or in
the degenerate one-point polygon `support = 1` whose single segment has length `0` — and then that
segment's slope is junk (`⊤` or `⊥`), by `lengths_final`. -/
private lemma lengths_eq_zero_cases {i : ℕ} (h : P.lengths i = 0) :
    P.support ≤ (i : WithTop ℕ) ∨
      (P.support = 1 ∧ i = 0 ∧ (P.slopes 0 = ⊤ ∨ P.slopes 0 = ⊥)) := by
  rcases le_or_gt P.support (i : WithTop ℕ) with hs | hs
  · exact Or.inl hs
  refine Or.inr ?_
  by_cases h1 : (i : WithTop ℕ) + 1 < P.support
  · obtain ⟨a, ha, ha'⟩ := P.lengths_nonFinal i h1
    rw [ha'] at h
    exact absurd (WithTop.coe_injective h) ha
  · have hsupp := P.support_eq_add_one hs h1
    obtain ⟨h11, hjunk⟩ := P.lengths_final i ⟨hsupp, h⟩
    obtain rfl : i = 0 := by simpa [h11] using hsupp
    exact ⟨h11, rfl, hjunk⟩

/-- Once a segment has length `0`, so has every later one. -/
private lemma lengths_eq_zero_of_le {i k : ℕ} (h : P.lengths i = 0) (hik : i ≤ k) :
    P.lengths k = 0 := by
  rcases P.lengths_eq_zero_cases h with hs | ⟨h1, rfl, -⟩
  · exact P.lengths_junk k (hs.trans (by exact_mod_cast hik))
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact h
    · exact P.lengths_junk k (by rw [h1]; exact_mod_cast hk)

/-- A finite vertex sits at a natural offset from the starting vertex. -/
private lemma exists_vertexX_eq {n : ℕ} (h : P.vertexX n ≠ ⊤) :
    ∃ m : ℕ, P.vertexX n = ((P.starting_point.1 + m : ℤ) : WithTop ℤ) := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨m, hm⟩ := ih (ne_top_of_le_ne_top h (P.vertexX_mono (Nat.le_succ n)))
    rw [P.vertexX_succ, hm]
    cases hl : P.lengths n with
    | top =>
      rw [P.vertexX_succ, hm, hl, WithTop.map_top, add_top] at h
      exact absurd rfl h
    | coe w =>
      refine ⟨m + w, ?_⟩
      rw [WithTop.map_coe, ← WithTop.coe_add]
      congr 1
      push_cast
      ring

/-- Destructure a finite vertex one step at a time: the previous vertex is finite too, and the
segment between them has a finite length accounting for the difference. -/
private lemma vertexX_succ_eq {n m : ℕ}
    (h : P.vertexX (n + 1) = ((P.starting_point.1 + m : ℤ) : WithTop ℤ)) :
    ∃ m' w : ℕ, P.vertexX n = ((P.starting_point.1 + m' : ℤ) : WithTop ℤ) ∧
      P.lengths n = (w : WithTop ℕ) ∧ m = m' + w := by
  have hne : P.vertexX (n + 1) ≠ ⊤ := by rw [h]; exact WithTop.coe_ne_top
  obtain ⟨m', hm'⟩ :=
    P.exists_vertexX_eq (ne_top_of_le_ne_top hne (P.vertexX_mono (Nat.le_succ n)))
  cases hl : P.lengths n with
  | top =>
    rw [P.vertexX_succ, hl, WithTop.map_top, add_top] at h
    exact absurd h.symm WithTop.coe_ne_top
  | coe w =>
    refine ⟨m', w, hm', rfl, ?_⟩
    rw [P.vertexX_succ, hm', hl, WithTop.map_coe, ← WithTop.coe_add] at h
    have := WithTop.coe_injective h
    omega

/-- **Propagation of the entry state**: if the `n`-th vertex is `m` steps right of the starting
vertex and no earlier segment is degenerate, then the walk at offset `m + j` is exactly the walk
entering segment `n` with `j` steps to go. -/
private lemma rightSlope_offset (n : ℕ) :
    ∀ (m : ℕ), P.vertexX n = ((P.starting_point.1 + m : ℤ) : WithTop ℤ) →
      (∀ i < n, P.lengths i ≠ 0) → ∀ j : ℕ,
        P.toNewtonPolygon.rightSlope (m + j) =
          entryStep P.toNewtonPolygon (n : ℤ) (P.lengths n) j := by
  induction n with
  | zero =>
    intro m hm _ j
    rw [P.vertexX_zero] at hm
    obtain rfl : m = 0 := by
      have := WithTop.coe_injective hm
      omega
    rw [Nat.cast_zero, zero_add, rightSlope_eq_entryStep,
      show ((0 : ℤ)) = ((0 : ℕ) : ℤ) from rfl, P.toNewtonPolygon_lengths_natCast]
  | succ n ih =>
    intro m hm hne j
    obtain ⟨m', w, hm', hw, hmm⟩ := P.vertexX_succ_eq hm
    obtain ⟨w0, rfl⟩ : ∃ w0, w = w0 + 1 := by
      rcases Nat.eq_zero_or_pos w with rfl | hwpos
      · exact absurd hw (hne n (by omega))
      · exact ⟨w - 1, by omega⟩
    have key := ih m' hm' (fun i hi => hne i (by omega)) (j + w0 + 1)
    rw [hw, entryStep_coe_succ] at key
    rw [show m + j = m' + (j + w0 + 1) by omega, key, rightSlopeAux_cross,
      show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring,
      P.toNewtonPolygon_lengths_natCast]

/-- Past the support every segment is empty and every slope is junk, so the walk returns `⊤`. -/
private lemma rightSlopeAux_junk : ∀ (k : ℕ) {i : ℕ}, P.support ≤ (i : WithTop ℕ) →
    P.toNewtonPolygon.rightSlopeAux (i : ℤ) 0 k = ⊤ := by
  intro k
  induction k with
  | zero =>
    intro i hs
    exact (P.toNewtonPolygon_slopes_natCast i).trans (P.slopes_junk i hs)
  | succ k ih =>
    intro i hs
    have hnext : P.support ≤ ((i + 1 : ℕ) : WithTop ℕ) :=
      hs.trans (by exact_mod_cast Nat.le_succ i)
    rw [show k + 1 = k + 0 + 1 from rfl, rightSlopeAux_cross,
      show ((i : ℤ) + 1) = ((i + 1 : ℕ) : ℤ) by push_cast; ring,
      P.toNewtonPolygon_lengths_natCast, P.lengths_junk (i + 1) hnext, entryStep_zero]
    exact ih hnext

/-- On the unit intervals of segment `n` — that is, at offsets `j` with
`vertexX n ≤ x₀ + j < vertexX (n + 1)` — the unit slope is the slope of segment `n`.
This is the correspondence between the walked `rightSlope` and the structure field `slopes`. -/
lemma unitSlope_eq_slopes {n j : ℕ}
    (h1 : P.vertexX n ≤ ((P.starting_point.1 + j : ℤ) : WithTop ℤ))
    (h2 : ((P.starting_point.1 + j : ℤ) : WithTop ℤ) < P.vertexX (n + 1)) :
    P.unitSlope j = P.slopes n := by
  obtain ⟨m, hm⟩ := P.exists_vertexX_eq (ne_top_of_le_ne_top WithTop.coe_ne_top h1)
  rw [hm] at h1
  have hmj : m ≤ j := by
    have := WithTop.coe_le_coe.1 h1
    omega
  have hne : ∀ i < n, P.lengths i ≠ 0 := by
    intro i hi hz
    have hzn : P.lengths n = 0 := P.lengths_eq_zero_of_le hz (by omega)
    rw [P.vertexX_succ, hzn, hm,
      show WithTop.map (fun l : ℕ => (l : ℤ)) (0 : WithTop ℕ) = 0 from rfl, add_zero] at h2
    have := WithTop.coe_lt_coe.1 h2
    omega
  have key := P.rightSlope_offset n m hm hne (j - m)
  rw [show m + (j - m) = j by omega] at key
  show P.toNewtonPolygon.rightSlope j = P.slopes n
  rw [key]
  cases hl : P.lengths n with
  | top => exact P.toNewtonPolygon_slopes_natCast n
  | coe w =>
    rw [P.vertexX_succ, hm, hl, WithTop.map_coe, ← WithTop.coe_add] at h2
    have hjw : j < m + w := by
      have := WithTop.coe_lt_coe.1 h2
      omega
    obtain ⟨w0, rfl⟩ : ∃ w0, w = w0 + 1 := ⟨w - 1, by omega⟩
    show P.toNewtonPolygon.rightSlopeAux (n : ℤ) w0 (j - m) = P.slopes n
    rw [rightSlopeAux_of_le P.toNewtonPolygon (n : ℤ) (show j - m ≤ w0 by omega)]
    exact P.toNewtonPolygon_slopes_natCast n

/-- If the first segment is empty the walk reads its slope without moving: the `0`-th unit slope
is the slope of segment `0`. -/
private lemma unitSlope_zero_of_lengths_eq_zero (h : P.lengths 0 = 0) :
    P.unitSlope 0 = P.slopes 0 := by
  have hl0 : P.toNewtonPolygon.lengths 0 = 0 := (P.toNewtonPolygon_lengths_natCast 0).trans h
  show P.toNewtonPolygon.rightSlope 0 = P.slopes 0
  rw [rightSlope_eq_entryStep, hl0, entryStep_zero,
    rightSlopeAux_of_le P.toNewtonPolygon 0 (le_refl 0)]
  exact P.toNewtonPolygon_slopes_natCast 0

/-- For the degenerate one-point polygon (`support = 1` with its single segment empty) every unit
slope but the first is `⊤`: the walk steps straight out of segment `0` into the junk region. -/
private lemma unitSlope_succ_eq_top_of_degenerate (h1 : P.support = 1) (h0 : P.lengths 0 = 0)
    (j : ℕ) : P.unitSlope (j + 1) = ⊤ := by
  have hs1 : P.support ≤ ((1 : ℕ) : WithTop ℕ) := by rw [h1]; exact le_of_eq (by norm_num)
  have hl0 : P.toNewtonPolygon.lengths 0 = 0 := (P.toNewtonPolygon_lengths_natCast 0).trans h0
  have hl1 : P.toNewtonPolygon.lengths ((0 : ℤ) + 1) = 0 :=
    (P.toNewtonPolygon_lengths_natCast 1).trans (P.lengths_junk 1 hs1)
  have hcross := rightSlopeAux_cross P.toNewtonPolygon 0 j 0
  simp only [Nat.add_zero] at hcross
  show P.toNewtonPolygon.rightSlope (j + 1) = ⊤
  rw [rightSlope_eq_entryStep, hl0, entryStep_zero, hcross, hl1, entryStep_zero,
    show ((0 : ℤ) + 1) = ((1 : ℕ) : ℤ) by norm_num]
  exact P.rightSlopeAux_junk j hs1

/-- Every unit interval of a non-degenerate polygon lies in some segment, or in the right-hand
junk region (where the unit slope is `⊤`). This is the sharp form of `unitSlope_cases`, available
once the degenerate one-point polygon (`support = 1` with its single segment of length `0`) has
been excluded; it is what the internal convexity arguments run on. -/
private lemma unitSlope_cases_of_nondeg (hdeg : P.support = 1 → P.lengths 0 ≠ 0) (j : ℕ) :
    (∃ n : ℕ, P.vertexX n ≤ ((P.starting_point.1 + j : ℤ) : WithTop ℤ) ∧
      ((P.starting_point.1 + j : ℤ) : WithTop ℤ) < P.vertexX (n + 1)) ∨
    P.unitSlope j = ⊤ := by
  classical
  by_cases hb : ∃ n : ℕ, P.vertexX n ≤ ((P.starting_point.1 + j : ℤ) : WithTop ℤ) ∧
      ((P.starting_point.1 + j : ℤ) : WithTop ℤ) < P.vertexX (n + 1)
  · exact Or.inl hb
  right
  -- No bracket contains the offset `j`, so *every* vertex is at or left of `x₀ + j`.
  have hall : ∀ n : ℕ, P.vertexX n ≤ ((P.starting_point.1 + j : ℤ) : WithTop ℤ) := by
    intro n
    induction n with
    | zero =>
      rw [P.vertexX_zero]
      exact WithTop.coe_le_coe.2 (by omega)
    | succ n ih => exact not_lt.1 fun hlt => hb ⟨n, ih, hlt⟩
  have hoff : ∀ n : ℕ, ∃ m : ℕ,
      P.vertexX n = ((P.starting_point.1 + m : ℤ) : WithTop ℤ) ∧ m ≤ j := by
    intro n
    obtain ⟨m, hm⟩ := P.exists_vertexX_eq (ne_top_of_le_ne_top WithTop.coe_ne_top (hall n))
    refine ⟨m, hm, ?_⟩
    have := WithTop.coe_le_coe.1 (hm ▸ hall n)
    omega
  -- Honest segments advance by at least one unit, so the vertices could not all stay left of
  -- `x₀ + j` unless some segment is empty.
  have hgrow : ∀ n : ℕ, (∀ i < n, P.lengths i ≠ 0) → ∀ m : ℕ,
      P.vertexX n = ((P.starting_point.1 + m : ℤ) : WithTop ℤ) → n ≤ m := by
    intro n
    induction n with
    | zero => intro _ m _; omega
    | succ n ih =>
      intro hne m hm
      obtain ⟨m', w, hm', hw, hmm⟩ := P.vertexX_succ_eq hm
      have hw0 : w ≠ 0 := fun hc => hne n (by omega) (by rw [hw, hc]; rfl)
      have := ih (fun i hi => hne i (by omega)) m' hm'
      omega
  have hzero : ∃ i : ℕ, P.lengths i = 0 := by
    by_contra hc
    obtain ⟨m, hm, hmj⟩ := hoff (j + 1)
    have := hgrow (j + 1) (fun i _ hz => hc ⟨i, hz⟩) m hm
    omega
  -- The first empty segment is past the support (the degenerate alternative is excluded), so the
  -- walk enters the junk region there and returns `⊤`.
  obtain ⟨i, hi, hlt⟩ : ∃ i : ℕ, P.lengths i = 0 ∧ ∀ t < i, P.lengths t ≠ 0 :=
    ⟨Nat.find hzero, Nat.find_spec hzero, fun t ht => Nat.find_min hzero ht⟩
  have hsupp : P.support ≤ (i : WithTop ℕ) := by
    rcases P.lengths_eq_zero_cases hi with hs | ⟨h1, rfl, -⟩
    · exact hs
    · exact absurd hi (hdeg h1)
  obtain ⟨m, hm, hmj⟩ := hoff i
  have key := P.rightSlope_offset i m hm hlt (j - m)
  rw [show m + (j - m) = j by omega, hi, entryStep_zero] at key
  show P.toNewtonPolygon.rightSlope j = ⊤
  rw [key]
  exact P.rightSlopeAux_junk (j - m) hsupp

/-- Every unit interval lies in some segment, or in the right-hand junk region, where the unit
slope is `⊤` — or is the single unit-less interval of the degenerate one-point polygon
(`support = 1` with its single segment of length `0`), where the unit slope is `⊥`.

No hypothesis is needed: the `2026-08-03` strengthening of `NewtonPolygon₀.lengths_final`
(recorded in `.mathlib-quality/b2_log.jsonl`) forces a zero-width final segment to carry a junk
slope (`⊤` or `⊥`), outlawing the phantom "zero-width segment with a real slope". The `⊥` arm
covers the residual zero-width representation of an `unboundedBelow` end, which — every vertex of
such a polygon sitting at `x₀` — is reachable only at offset `j = 0`. -/
lemma unitSlope_cases (j : ℕ) :
    (∃ n : ℕ, P.vertexX n ≤ ((P.starting_point.1 + j : ℤ) : WithTop ℤ) ∧
      ((P.starting_point.1 + j : ℤ) : WithTop ℤ) < P.vertexX (n + 1)) ∨
    P.unitSlope j = ⊤ ∨ P.unitSlope j = ⊥ := by
  classical
  by_cases hd : P.support = 1 ∧ P.lengths 0 = 0
  · refine Or.inr ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [P.unitSlope_zero_of_lengths_eq_zero hd.2]
      exact (P.lengths_final 0 ⟨by rw [hd.1]; simp, hd.2⟩).2
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      exact Or.inl (P.unitSlope_succ_eq_top_of_degenerate hd.1 hd.2 j')
  · exact (P.unitSlope_cases_of_nondeg (fun h1 h0 => hd ⟨h1, h0⟩) j).imp id Or.inl

/-- The segment slopes are monotone (the structure field, unfolded from successors). -/
private lemma slopes_mono : Monotone P.slopes := monotone_nat_of_le_succ P.slopes_increasing

/-- **Convexity of the polygon**: the unit slopes are monotone. -/
lemma unitSlope_mono : Monotone P.unitSlope := by
  refine monotone_nat_of_le_succ fun j => ?_
  by_cases hd : P.support = 1 ∧ P.lengths 0 = 0
  · rw [P.unitSlope_succ_eq_top_of_degenerate hd.1 hd.2 j]
    exact le_top
  have hdeg : P.support = 1 → P.lengths 0 ≠ 0 := fun h1 h0 => hd ⟨h1, h0⟩
  rcases (P.unitSlope_cases_of_nondeg hdeg (j + 1)).symm with htop | ⟨n', h1', h2'⟩
  · rw [htop]
    exact le_top
  rcases P.unitSlope_cases_of_nondeg hdeg j with ⟨n, h1, h2⟩ | htopj
  · -- Both offsets are bracketed: compare the two segment indices.
    rw [P.unitSlope_eq_slopes h1 h2, P.unitSlope_eq_slopes h1' h2']
    refine P.slopes_mono ?_
    by_contra hlt
    have hchain : P.vertexX (n' + 1) ≤ ((P.starting_point.1 + j : ℤ) : WithTop ℤ) :=
      (P.vertexX_mono (show n' + 1 ≤ n by omega)).trans h1
    have := WithTop.coe_lt_coe.1 (lt_of_lt_of_le h2' hchain)
    push_cast at this
    omega
  -- The offset `j` is in the junk region: then so is `j + 1`, i.e. `slopes n' = ⊤`.
  rw [htopj, P.unitSlope_eq_slopes h1' h2', top_le_iff]
  obtain ⟨m, hm⟩ := P.exists_vertexX_eq (ne_top_of_le_ne_top WithTop.coe_ne_top h1')
  have hmj : m ≤ j + 1 := by
    have := WithTop.coe_le_coe.1 (hm ▸ h1')
    push_cast at this
    omega
  rcases le_or_gt m j with hmle | hmgt
  · -- Segment `n'` already covers the offset `j`, so its slope is the junk value there.
    have hb1 : P.vertexX n' ≤ ((P.starting_point.1 + j : ℤ) : WithTop ℤ) := by
      rw [hm]; exact WithTop.coe_le_coe.2 (by omega)
    have hb2 : ((P.starting_point.1 + j : ℤ) : WithTop ℤ) < P.vertexX (n' + 1) :=
      lt_trans (WithTop.coe_lt_coe.2 (by push_cast; omega)) h2'
    rw [← P.unitSlope_eq_slopes hb1 hb2, htopj]
  · -- The vertex `n'` sits exactly at `x₀ + j + 1`; back up one segment.
    obtain ⟨n'', rfl⟩ : ∃ n'', n' = n'' + 1 := by
      rcases Nat.eq_zero_or_pos n' with rfl | hpos
      · rw [P.vertexX_zero] at hm
        have := WithTop.coe_injective hm
        omega
      · exact ⟨n' - 1, by omega⟩
    obtain ⟨m', w, hm', hw, hmm⟩ := P.vertexX_succ_eq hm
    rcases Nat.eq_zero_or_pos w with rfl | hwpos
    · -- The segment before the vertex is empty: we are past the support, so the slope is junk.
      have hw0 : P.lengths n'' = 0 := by rw [hw]; rfl
      rcases P.lengths_eq_zero_cases hw0 with hs | ⟨hsupp1, rfl, -⟩
      · exact P.slopes_junk (n'' + 1) (hs.trans (by exact_mod_cast Nat.le_succ n''))
      · exact absurd hw0 (hdeg hsupp1)
    · -- The previous segment is honest, hence covers the offset `j`.
      have hb1 : P.vertexX n'' ≤ ((P.starting_point.1 + j : ℤ) : WithTop ℤ) := by
        rw [hm']; exact WithTop.coe_le_coe.2 (by omega)
      have hb2 : ((P.starting_point.1 + j : ℤ) : WithTop ℤ) < P.vertexX (n'' + 1) := by
        rw [hm]; exact WithTop.coe_lt_coe.2 (by omega)
      have hj : P.slopes n'' = ⊤ := by rw [← P.unitSlope_eq_slopes hb1 hb2, htopj]
      exact top_le_iff.1 (hj ▸ P.slopes_increasing n'')

/-- `unitSlope` is, by definition, the right-hand walk of the embedded polygon. -/
private lemma unitSlope_eq_rightSlope (j : ℕ) :
    P.unitSlope j = P.toNewtonPolygon.rightSlope j := rfl

/-- Left of the starting vertex the embedded polygon is pure junk: the left walk never leaves the
negative segment indices, where every length is `0` and every slope is `⊥`. -/
private lemma leftSlopeAux_eq_bot (j : ℕ) :
    ∀ {n : ℤ} {r : ℕ}, n < 0 → P.toNewtonPolygon.leftSlopeAux n r j = ⊥ := by
  induction j with
  | zero =>
    intro n r hn
    show P.toNewtonPolygon.slopes n = ⊥
    exact P.toNewtonPolygon_slopes_of_neg hn
  | succ j ih =>
    intro n r hn
    match r with
    | (r + 1) => exact ih hn
    | 0 =>
      show P.toNewtonPolygon.leftSlopeAux n 0 (j + 1) = ⊥
      rw [NewtonPolygon.leftSlopeAux,
        P.toNewtonPolygon_lengths_of_neg (show n - 1 < 0 by omega)]
      exact ih (show n - 1 < 0 by omega)

/-- Every left unit slope of the embedded polygon is `⊥`. -/
private lemma leftSlope_eq_bot (j : ℕ) : P.toNewtonPolygon.leftSlope j = ⊥ := by
  rw [NewtonPolygon.leftSlope,
    P.toNewtonPolygon_lengths_of_neg (show (-1 : ℤ) < 0 by norm_num)]
  exact P.leftSlopeAux_eq_bot j (by norm_num)

end

/-- Strictly left of the starting vertex the height is `⊥`. -/
private lemma leftHeight_eq_bot {k : ℕ} (hk : 1 ≤ k) : P.toNewtonPolygon.leftHeight k = ⊥ := by
  rw [NewtonPolygon.leftHeight, if_pos ⟨hk, P.leftSlope_eq_bot (k - 1)⟩]

/-- Right of the starting vertex the height is never `⊥`. -/
private lemma rightHeight_ne_bot (k : ℕ) : P.toNewtonPolygon.rightHeight k ≠ ⊥ := by
  rw [NewtonPolygon.rightHeight]
  split
  · exact WithBotTop.top_ne_bot
  · exact WithBotTop.coe_ne_bot _

/-- At or right of the starting vertex the height is the right-hand walk. -/
private lemma height_eq_rightHeight {x : ℤ} (hx : P.starting_point.1 ≤ x) :
    P.height x = P.toNewtonPolygon.rightHeight (x - P.starting_point.1).toNat := by
  show P.toNewtonPolygon.height x = _
  rw [NewtonPolygon.height, toNewtonPolygon_startingPoint,
    if_pos (show (0 : ℤ) ≤ x - P.starting_point.1 by omega)]

/-- Strictly left of the starting vertex the height is the left-hand walk. -/
private lemma height_eq_leftHeight {x : ℤ} (hx : x < P.starting_point.1) :
    P.height x = P.toNewtonPolygon.leftHeight (P.starting_point.1 - x).toNat := by
  show P.toNewtonPolygon.height x = _
  rw [NewtonPolygon.height, toNewtonPolygon_startingPoint,
    if_neg (show ¬ (0 : ℤ) ≤ x - P.starting_point.1 by omega)]

/-- The height is `⊥` exactly strictly left of the starting vertex. -/
lemma height_eq_bot_iff (x : ℤ) : P.height x = ⊥ ↔ x < P.starting_point.1 := by
  constructor
  · intro h
    by_contra hx
    rw [P.height_eq_rightHeight (by omega)] at h
    exact P.rightHeight_ne_bot _ h
  · exact fun hx => (P.height_eq_leftHeight hx).trans (P.leftHeight_eq_bot (by omega))

/-- A `⊤` height forces the junk guard of the right-hand walk. -/
lemma unitSlope_eq_top_of_height_eq_top {x : ℤ} (hx : P.height x = ⊤) :
    P.starting_point.1 ≤ x ∧ 1 ≤ (x - P.starting_point.1).toNat ∧
      P.unitSlope ((x - P.starting_point.1).toNat - 1) = ⊤ := by
  have hxs : P.starting_point.1 ≤ x := by
    by_contra hc
    rw [(P.height_eq_bot_iff x).2 (by omega)] at hx
    exact absurd hx (by simp)
  refine ⟨hxs, ?_⟩
  rw [P.height_eq_rightHeight hxs, NewtonPolygon.rightHeight] at hx
  by_contra hc
  rw [if_neg (by simpa [unitSlope_eq_rightSlope] using hc)] at hx
  exact absurd hx (by simp)

/-- Once the height is `⊤` (right-hand junk region) it stays `⊤`. -/
lemma height_eq_top_mono {x y : ℤ} (hx : P.height x = ⊤) (hxy : x ≤ y) :
    P.height y = ⊤ := by
  obtain ⟨hxs, hk, htop⟩ := P.unitSlope_eq_top_of_height_eq_top hx
  have htop' : P.unitSlope ((y - P.starting_point.1).toNat - 1) = ⊤ :=
    top_le_iff.1 (htop ▸ P.unitSlope_mono (show (x - P.starting_point.1).toNat - 1 ≤
      (y - P.starting_point.1).toNat - 1 by omega))
  rw [P.height_eq_rightHeight (by omega), NewtonPolygon.rightHeight,
    if_pos ⟨by omega, htop'⟩]

/-- On the honest region the height is the real value `heightFun`. -/
lemma height_eq_heightFun (k : ℕ) (h : P.height (P.starting_point.1 + k) ≠ ⊤) :
    P.height (P.starting_point.1 + k) = (P.heightFun k : WithBotTop ℝ) := by
  have hk : P.height (P.starting_point.1 + (k : ℤ)) = P.toNewtonPolygon.rightHeight k := by
    rw [P.height_eq_rightHeight (by omega)]
    congr 1
    omega
  rw [hk, NewtonPolygon.rightHeight] at h ⊢
  rw [if_neg fun hc => h (by rw [if_pos hc])]
  rfl

/-- Left of a non-`⊤` height all unit slopes are non-`⊤`. -/
lemma unitSlope_ne_top_of_height_ne_top {c : ℕ}
    (h : P.height (P.starting_point.1 + c) ≠ ⊤) {i : ℕ} (hic : i < c) :
    P.unitSlope i ≠ ⊤ := by
  intro hi
  refine h ?_
  have htop : P.unitSlope (c - 1) = ⊤ :=
    top_le_iff.1 (hi ▸ P.unitSlope_mono (show i ≤ c - 1 by omega))
  rw [P.height_eq_rightHeight (by omega),
    show (P.starting_point.1 + (c : ℤ) - P.starting_point.1).toNat = c by omega,
    NewtonPolygon.rightHeight, if_pos ⟨by omega, htop⟩]

section
omit [CommSemiring Γ] [Algebra Γ ℝ]

/-- A `⊥` slope can only occur as the single slope of a one-segment polygon. -/
private lemma eq_one_of_slopes_eq_bot {n : ℕ} (h : P.slopes n = ⊥) : P.support = 1 ∧ n = 0 := by
  have hlt : (n : WithTop ℕ) < P.support := by
    by_contra hcon
    rw [P.slopes_junk n (not_lt.1 hcon)] at h
    exact absurd h (by simp)
  have hnf : ¬ (n : WithTop ℕ) + 1 < P.support := by
    intro hcon
    obtain ⟨a, ha⟩ := P.slopes_nonFinal n hcon
    rw [ha] at h
    exact absurd h (by simp)
  have hsupp := P.support_eq_add_one hlt hnf
  have h1 := (P.slopes_final n ⟨hsupp, Or.inr h⟩).1
  exact ⟨h1, by simpa [h1] using hsupp⟩

/-- A `⊥` unit slope pins the shape of the polygon: it can only be read off the single segment of
a one-segment polygon whose slope is `⊥` (an `unboundedBelow` end, of zero or positive width).
This is the bridge that lets a caller refute the `⊥` arm of `unitSlope_cases`. -/
lemma slopes_zero_eq_bot_of_unitSlope_eq_bot {j : ℕ} (h : P.unitSlope j = ⊥) :
    P.slopes 0 = ⊥ ∧ P.support = 1 := by
  by_cases hd : P.support = 1 ∧ P.lengths 0 = 0
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact ⟨(P.unitSlope_zero_of_lengths_eq_zero hd.2).symm.trans h, hd.1⟩
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [P.unitSlope_succ_eq_top_of_degenerate hd.1 hd.2 j'] at h
      exact absurd h.symm (by simp)
  · rcases P.unitSlope_cases_of_nondeg (fun h1 h0 => hd ⟨h1, h0⟩) j with ⟨n, h1, h2⟩ | htop
    · rw [P.unitSlope_eq_slopes h1 h2] at h
      obtain ⟨hsupp, rfl⟩ := P.eq_one_of_slopes_eq_bot h
      exact ⟨h, hsupp⟩
    · rw [htop] at h
      exact absurd h.symm (by simp)

/-- Right of a `⊥` unit slope the polygon carries no honest real values: the only segment is the
one with the `⊥` slope, and past it everything is junk. -/
private lemma unitSlope_eq_bot_cases {i j : ℕ} (hi : P.unitSlope i = ⊥) (hij : i ≤ j) :
    P.unitSlope j = ⊥ ∨ P.unitSlope j = ⊤ := by
  by_cases hd : P.support = 1 ∧ P.lengths 0 = 0
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · obtain rfl : i = 0 := by omega
      exact Or.inl hi
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      exact Or.inr (P.unitSlope_succ_eq_top_of_degenerate hd.1 hd.2 j')
  have hdeg : P.support = 1 → P.lengths 0 ≠ 0 := fun h1 h0 => hd ⟨h1, h0⟩
  rcases (P.unitSlope_cases_of_nondeg hdeg j).symm with htop | ⟨n', h1', h2'⟩
  · exact Or.inr htop
  rcases (P.unitSlope_cases_of_nondeg hdeg i).symm with htopi | ⟨n, h1, h2⟩
  · rw [htopi] at hi
    exact absurd hi.symm (by simp)
  rw [P.unitSlope_eq_slopes h1 h2] at hi
  obtain ⟨hsupp, rfl⟩ := P.eq_one_of_slopes_eq_bot hi
  rcases Nat.eq_zero_or_pos n' with rfl | hn'
  · exact Or.inl (by rw [P.unitSlope_eq_slopes h1' h2']; exact hi)
  · refine Or.inr ?_
    rw [P.unitSlope_eq_slopes h1' h2']
    exact P.slopes_junk n' (by rw [hsupp]; exact_mod_cast (show (1 : ℕ) ≤ n' by omega))

/-- A `WithBotTop ℝ` which is neither `⊥` nor `⊤` carries a real number. -/
private lemma exists_coe {v : WithBotTop ℝ} (hb : v ≠ ⊥) (ht : v ≠ ⊤) :
    ∃ r : ℝ, v = (r : WithBotTop ℝ) := by
  induction v using WithBotTop.rec with
  | bot => exact absurd rfl hb
  | coe r => exact ⟨r, rfl⟩
  | top => exact absurd rfl ht

/-- Below the right-hand junk region the real-valued unit slopes are monotone: `toReal` is
order-preserving there, the `⊥` case being constant `0` by `unitSlope_eq_bot_cases`. -/
lemma toReal_unitSlope_le {i j : ℕ} (hij : i ≤ j) (hj : P.unitSlope j ≠ ⊤) :
    NewtonPolygon.toReal (P.unitSlope i) ≤ NewtonPolygon.toReal (P.unitSlope j) := by
  have hmono := P.unitSlope_mono hij
  have hi : P.unitSlope i ≠ ⊤ := by
    intro hcon
    rw [hcon] at hmono
    exact hj (top_le_iff.1 hmono)
  by_cases hib : P.unitSlope i = ⊥
  · rcases P.unitSlope_eq_bot_cases hib hij with hjb | hjt
    · rw [hib, hjb]
    · exact absurd hjt hj
  · have hjb : P.unitSlope j ≠ ⊥ := by
      intro hcon
      rw [hcon] at hmono
      exact hib (le_bot_iff.1 hmono)
    obtain ⟨r, hr⟩ := exists_coe hib hi
    obtain ⟨s, hs⟩ := exists_coe hjb hj
    rw [hr, hs] at hmono ⊢
    simpa using WithBotTop.coe_le_coe.1 hmono

end

/-- The increment of `heightFun` over `[m, n)` is the sum of the unit slopes there. -/
private lemma heightFun_sub {m n : ℕ} (hmn : m ≤ n) :
    P.heightFun n - P.heightFun m =
      ∑ i ∈ Finset.Ico m n, NewtonPolygon.toReal (P.unitSlope i) := by
  rw [heightFun, heightFun, Finset.sum_Ico_eq_sub _ hmn]
  ring

/-- **Chord inequality (discrete Jensen), division-free form**: on the honest region, for
`a ≤ b ≤ c` the height at `b` lies on/below the chord from `(a, heightFun a)` to
`(c, heightFun c)`. -/
lemma heightFun_chord {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (hc : P.height (P.starting_point.1 + c) ≠ ⊤) :
    ((c : ℝ) - a) * P.heightFun b ≤
      ((c : ℝ) - b) * P.heightFun a + ((b : ℝ) - a) * P.heightFun c := by
  rcases eq_or_lt_of_le hbc with rfl | hbc'
  · linarith
  have hne : ∀ i, i < c → P.unitSlope i ≠ ⊤ := fun _ hi =>
    P.unitSlope_ne_top_of_height_ne_top hc hi
  have hcasta : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hcastb : (b : ℝ) ≤ c := by exact_mod_cast hbc
  have h1 : ∑ i ∈ Finset.Ico a b, NewtonPolygon.toReal (P.unitSlope i)
      ≤ ((b : ℝ) - a) * NewtonPolygon.toReal (P.unitSlope b) := by
    have hsum := Finset.sum_le_card_nsmul (Finset.Ico a b)
      (fun i => NewtonPolygon.toReal (P.unitSlope i)) (NewtonPolygon.toReal (P.unitSlope b))
      (fun i hi => P.toReal_unitSlope_le (le_of_lt (Finset.mem_Ico.1 hi).2) (hne b hbc'))
    rwa [Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hab] at hsum
  have h2 : ((c : ℝ) - b) * NewtonPolygon.toReal (P.unitSlope b)
      ≤ ∑ i ∈ Finset.Ico b c, NewtonPolygon.toReal (P.unitSlope i) := by
    have hsum := Finset.card_nsmul_le_sum (Finset.Ico b c)
      (fun i => NewtonPolygon.toReal (P.unitSlope i)) (NewtonPolygon.toReal (P.unitSlope b))
      (fun i hi => P.toReal_unitSlope_le (Finset.mem_Ico.1 hi).1 (hne i (Finset.mem_Ico.1 hi).2))
    rwa [Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hbc] at hsum
  rw [← P.heightFun_sub hab] at h1
  rw [← P.heightFun_sub hbc] at h2
  have k1 : ((c : ℝ) - b) * (P.heightFun b - P.heightFun a)
      ≤ ((c : ℝ) - b) * (((b : ℝ) - a) * NewtonPolygon.toReal (P.unitSlope b)) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  have k2 : ((b : ℝ) - a) * (((c : ℝ) - b) * NewtonPolygon.toReal (P.unitSlope b))
      ≤ ((b : ℝ) - a) * (P.heightFun c - P.heightFun b) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  linarith [k1, k2]

/-- The first unit slope bounds the average slope from below: the height at `k` is at least the
line of slope `unitSlope 0` through the starting vertex. -/
lemma le_heightFun (k : ℕ) (hk : P.height (P.starting_point.1 + k) ≠ ⊤) :
    (k : ℝ) * NewtonPolygon.toReal (P.unitSlope 0) ≤ P.heightFun k - P.heightFun 0 := by
  rw [P.heightFun_sub (Nat.zero_le k)]
  have hsum := Finset.card_nsmul_le_sum (Finset.Ico 0 k)
    (fun i => NewtonPolygon.toReal (P.unitSlope i)) (NewtonPolygon.toReal (P.unitSlope 0))
    (fun i hi => P.toReal_unitSlope_le (Nat.zero_le i)
      (P.unitSlope_ne_top_of_height_ne_top hk (Finset.mem_Ico.1 hi).2))
  rwa [Nat.card_Ico, nsmul_eq_mul, Nat.sub_zero] at hsum

/-- **Chord comparison for `height`**: if the height at `x` and `z` is bounded by reals `a` and
`c`, then at any `y` between them it is bounded by the chord through `(x, a)` and `(z, c)`.

The left endpoint must lie at or right of the starting vertex: strictly left of it the height is
`⊥`, so `hx` carries no information there while the chord through `(x, a)` can be dragged
arbitrarily low (for the horizontal polygon starting at `(0, 0)`, taking `x = -1`, `a = -100`,
`z = 2`, `c = 0` the chord at `y = 0` is `-200/3 < 0 = height 0`). -/
lemma height_le_chord {x y z : ℤ} (hxs : P.starting_point.1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    {a c : ℝ} (hx : P.height x ≤ (a : WithBotTop ℝ)) (hz : P.height z ≤ (c : WithBotTop ℝ)) :
    P.height y ≤
      ((a + (c - a) / ((z : ℝ) - (x : ℝ)) * ((y : ℝ) - (x : ℝ)) : ℝ) : WithBotTop ℝ) := by
  obtain ⟨kx, rfl⟩ : ∃ kx : ℕ, x = P.starting_point.1 + (kx : ℤ) :=
    ⟨(x - P.starting_point.1).toNat, by omega⟩
  obtain ⟨ky, rfl⟩ : ∃ ky : ℕ, y = P.starting_point.1 + (ky : ℤ) :=
    ⟨(y - P.starting_point.1).toNat, by omega⟩
  obtain ⟨kz, rfl⟩ : ∃ kz : ℕ, z = P.starting_point.1 + (kz : ℤ) :=
    ⟨(z - P.starting_point.1).toNat, by omega⟩
  have hkxy : kx ≤ ky := by omega
  have hkyz : ky ≤ kz := by omega
  have hztop : P.height (P.starting_point.1 + (kz : ℤ)) ≠ ⊤ := by
    intro hcon
    rw [hcon] at hz
    exact absurd (top_le_iff.1 hz) (by simp)
  have hytop : P.height (P.starting_point.1 + (ky : ℤ)) ≠ ⊤ := fun hcon =>
    hztop (P.height_eq_top_mono hcon (by omega))
  have hxtop : P.height (P.starting_point.1 + (kx : ℤ)) ≠ ⊤ := fun hcon =>
    hztop (P.height_eq_top_mono hcon (by omega))
  rw [P.height_eq_heightFun kx hxtop, WithBotTop.coe_le_coe] at hx
  rw [P.height_eq_heightFun kz hztop, WithBotTop.coe_le_coe] at hz
  rw [P.height_eq_heightFun ky hytop, WithBotTop.coe_le_coe]
  have hDeq : ((P.starting_point.1 + (kz : ℤ) : ℤ) : ℝ) - ((P.starting_point.1 + (kx : ℤ) : ℤ) : ℝ)
      = (kz : ℝ) - (kx : ℝ) := by push_cast; ring
  have hYeq : ((P.starting_point.1 + (ky : ℤ) : ℤ) : ℝ) - ((P.starting_point.1 + (kx : ℤ) : ℤ) : ℝ)
      = (ky : ℝ) - (kx : ℝ) := by push_cast; ring
  rw [hDeq, hYeq]
  rcases eq_or_lt_of_le (hkxy.trans hkyz) with heq | hlt
  · obtain rfl : ky = kx := by omega
    simpa using hx
  · have hD : (0 : ℝ) < (kz : ℝ) - kx := by
      have : (kx : ℝ) < kz := by exact_mod_cast hlt
      linarith
    have hD' : ((kz : ℝ) - kx) ≠ 0 := ne_of_gt hD
    have hcast1 : (kx : ℝ) ≤ ky := by exact_mod_cast hkxy
    have hcast2 : (ky : ℝ) ≤ kz := by exact_mod_cast hkyz
    have chord := P.heightFun_chord hkxy hkyz hztop
    have b1 : ((kz : ℝ) - ky) * P.heightFun kx ≤ ((kz : ℝ) - ky) * a :=
      mul_le_mul_of_nonneg_left hx (by linarith)
    have b2 : ((ky : ℝ) - kx) * P.heightFun kz ≤ ((ky : ℝ) - kx) * c :=
      mul_le_mul_of_nonneg_left hz (by linarith)
    have key : P.heightFun ky * ((kz : ℝ) - kx)
        ≤ a * ((kz : ℝ) - kx) + (c - a) * ((ky : ℝ) - kx) := by linarith [chord, b1, b2]
    calc P.heightFun ky ≤ (a * ((kz : ℝ) - kx) + (c - a) * ((ky : ℝ) - kx)) / ((kz : ℝ) - kx) :=
          (le_div_iff₀ hD).2 key
      _ = a + (c - a) / ((kz : ℝ) - kx) * ((ky : ℝ) - kx) := by field_simp

end NewtonPolygon₀
