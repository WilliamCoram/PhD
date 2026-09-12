/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.NewtonPolygons.SpecConstruction

/-!
# Newton polygons from a prescribed slope sequence

For a monotone sequence of slopes `s : ℕ → ℝ` and a starting height `y₀`, this file builds the
explicit one-sided Newton polygon `NewtonPolygon₀.ofSlopes s hs y₀` — starting vertex `(0, y₀)`,
infinitely many unit-length segments, slope `s j` on segment `j` — and proves that it *is* the
Newton polygon, in the sense of the geometric specification `IsNewtonPolygonOf`, of the
partial-sum sequence `v m = y₀ + ∑_{i<m} s i`.

This is the "explicit witness against the spec" half of a Newton-polygon slope reading: the
valuations of the coefficients of a power series give the *points*, and the polygon those points
determine is identified by exhibiting a witness and checking it against the specification. The
spec's `isGreatest` field is nearly immediate here because `IsBelow` compares heights at
*integers*, where the witness's height equals the points themselves.

Uniqueness (`IsNewtonPolygonOf.height_eq`) plus existence for the constructed polygon
(`isNewtonPolygonOf_newtonPolygon₀OfSeq`) then transport the result to the polygon produced by
the step algorithm, `newtonPolygon₀OfSeq`: same heights, and its unit slopes are the prescribed
`s j`.

This ordering is deliberate (design decision, 2026-08-04): the spec-level statement is the
canonical one — it certifies that the polygon we *believe* the Newton polygon to be is the
correct one, against the geometric definition itself; the algorithm-facing statements are
derived corollaries.

## Main declarations

* `NewtonPolygon₀.ofSlopes` — the explicit polygon with prescribed slopes.
* `NewtonPolygon₀.height_ofSlopes` — its height at an integer is the partial sum.
* `isNewtonPolygonOf_ofSlopes` — it is the Newton polygon of the partial-sum sequence.
* `isAdmissible_of_partial_sums` — partial-sum sequences of monotone slopes are admissible.
* `height_newtonPolygon₀OfSeq_ofSlopes`, `unitSlope_newtonPolygon₀OfSeq_ofSlopes` — transport
  to the constructed polygon.

## Sources

[Kob84, Ch. IV §3] (the classical Newton-polygon reading); [Jacobs, *Slopes of Compact Hecke
Operators*, proof of Thm 2.12, pp. 34–35] (the "points on a parabola ⇒ vertices ⇒ slopes" step
this API was extracted from); the blueprint Definition 1 via `PhD.Main.NewtonPolygons.Spec`.
-/

open Finset

namespace NewtonPolygon₀

/-- The explicit one-sided Newton polygon with starting vertex `(0, y₀)`, infinitely many
unit-length segments, and slope `s j` on the `j`-th segment.  For monotone `s` this is the
graph of the greatest convex minorant of the partial-sum points `(m, y₀ + ∑_{i<m} s i)`. -/
noncomputable def ofSlopes (s : ℕ → ℝ) (hs : Monotone s) (y₀ : ℝ) :
    NewtonPolygon₀ (Γ := ℝ) where
  support := ⊤
  slopes n := ((s n : ℝ) : WithBotTop ℝ)
  slopes_junk n h := absurd (top_le_iff.1 h) (by simp)
  slopes_nonFinal n _ := ⟨s n, rfl⟩
  slopes_final n h := absurd h.1 (by simp)
  slopes_increasing n := WithBotTop.coe_le_coe.2 (hs (Nat.le_succ n))
  lengths _ := 1
  lengths_junk n h := absurd (top_le_iff.1 h) (by simp)
  lengths_nonFinal n _ := ⟨1, one_ne_zero, rfl⟩
  lengths_final n h := absurd h.1 (by simp)
  starting_point := (0, y₀)

variable {s : ℕ → ℝ} {hs : Monotone s} {y₀ : ℝ}

/-- The slope of `ofSlopes s hs y₀` on its `n`-th segment is `s n`. -/
@[simp] theorem ofSlopes_slopes (n : ℕ) :
    (ofSlopes s hs y₀).slopes n = ((s n : ℝ) : WithBotTop ℝ) := rfl

/-- Every segment of `ofSlopes s hs y₀` has length `1`. -/
@[simp] theorem ofSlopes_lengths (n : ℕ) : (ofSlopes s hs y₀).lengths n = 1 := rfl

/-- The starting vertex of `ofSlopes s hs y₀` is `(0, y₀)`. -/
@[simp] theorem ofSlopes_starting_point :
    (ofSlopes s hs y₀).starting_point = (0, y₀) := rfl

/-- The polygon `ofSlopes s hs y₀` has infinitely many segments: its support is `⊤`. -/
@[simp] theorem ofSlopes_support : (ofSlopes s hs y₀).support = ⊤ := rfl

/-- The `n`-th vertex of the unit-length polygon sits at `x = n`. -/
theorem vertexX_ofSlopes (n : ℕ) : (ofSlopes s hs y₀).vertexX n = (n : WithTop ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [vertexX_succ, ih, ofSlopes_lengths,
      show WithTop.map (fun l : ℕ => (l : ℤ)) (1 : WithTop ℕ) = (1 : WithTop ℤ) from rfl]
    push_cast
    rfl

/-- The unit slope on `[j, j+1]` is `s j`. -/
theorem unitSlope_ofSlopes (j : ℕ) :
    (ofSlopes s hs y₀).unitSlope j = ((s j : ℝ) : WithBotTop ℝ) := by
  have h1 : (ofSlopes s hs y₀).vertexX j ≤
      (((ofSlopes s hs y₀).starting_point.1 + j : ℤ) : WithTop ℤ) := by
    rw [vertexX_ofSlopes]
    show (j : WithTop ℤ) ≤ (((0 : ℤ) + (j : ℤ) : ℤ) : WithTop ℤ)
    exact_mod_cast WithTop.coe_le_coe.2 (show (j : ℤ) ≤ 0 + (j : ℤ) by omega)
  have h2 : (((ofSlopes s hs y₀).starting_point.1 + j : ℤ) : WithTop ℤ) <
      (ofSlopes s hs y₀).vertexX (j + 1) := by
    rw [vertexX_ofSlopes]
    show (((0 : ℤ) + (j : ℤ) : ℤ) : WithTop ℤ) < ((j + 1 : ℕ) : WithTop ℤ)
    exact_mod_cast WithTop.coe_lt_coe.2 (show (0 : ℤ) + (j : ℤ) < (j : ℤ) + 1 by omega)
  exact (ofSlopes s hs y₀).unitSlope_eq_slopes h1 h2

/-- The walked height of `ofSlopes` is the partial sum of the slopes. -/
theorem heightFun_ofSlopes (k : ℕ) :
    (ofSlopes s hs y₀).heightFun k = y₀ + ∑ i ∈ range k, s i := by
  rw [heightFun, ofSlopes_starting_point]
  refine congrArg₂ _ (Algebra.algebraMap_self_apply y₀) (Finset.sum_congr rfl fun i _ => ?_)
  rw [unitSlope_ofSlopes, NewtonPolygon.toReal_coe]

/-- On a stretch of honest (non-`⊤`) unit slopes the height is the real-valued `heightFun`: the
junk guard of the right-hand walk is exactly a `⊤` incoming unit slope.  (Private copy, from
public `Height` API only, of the criterion used inside `PhD.Main.NewtonPolygons.SpecConstruction`.) -/
private lemma height_eq_heightFun_of_unitSlope_ne_top {Γ : Type*} [CommSemiring Γ]
    [Algebra Γ ℝ] (P : NewtonPolygon₀ (Γ := Γ)) {c : ℕ} (h : ∀ t < c, P.unitSlope t ≠ ⊤) :
    P.height (P.starting_point.1 + c) = ((P.heightFun c : ℝ) : WithBotTop ℝ) := by
  refine P.height_eq_heightFun c fun hc => ?_
  have hx : P.height (P.starting_point.1 + (c : ℤ)) = P.toNewtonPolygon.rightHeight c := by
    show P.toNewtonPolygon.height _ = _
    rw [NewtonPolygon.height, toNewtonPolygon_startingPoint,
      if_pos (show (0 : ℤ) ≤ P.starting_point.1 + (c : ℤ) - P.starting_point.1 by omega)]
    congr 1
    omega
  rw [hx, NewtonPolygon.rightHeight] at hc
  split_ifs at hc with hcond
  · exact h (c - 1) (by have := hcond.1; omega) hcond.2
  · exact absurd hc (by simp)

/-- The height of `ofSlopes` at the integer `k ≥ 0` is the `k`-th partial-sum point:
the polygon passes through every point of the partial-sum sequence. -/
theorem height_ofSlopes (k : ℕ) :
    (ofSlopes s hs y₀).height (k : ℤ) =
      ((y₀ + ∑ i ∈ range k, s i : ℝ) : WithBotTop ℝ) := by
  have hk : (k : ℤ) = (ofSlopes s hs y₀).starting_point.1 + (k : ℤ) := by
    rw [ofSlopes_starting_point]
    omega
  rw [hk, height_eq_heightFun_of_unitSlope_ne_top _ (fun t _ => ?_), heightFun_ofSlopes]
  rw [unitSlope_ofSlopes]
  exact WithBotTop.coe_ne_top _

end NewtonPolygon₀

/-! ### Junk-value exclusion for the constructed polygon

Two small private facts used to read an honest real slope off the constructed polygon: a
`WithBotTop ℝ` value which is neither `⊥` nor `⊤` is the coercion of its `toReal`, and the
polygon built by the step algorithm from an *admissible* sequence never carries the slope `⊥`
(the only step emitting `⊥` is `unboundedBelow`, which is precisely the failure of
admissibility at the anchor). -/

/-- A `WithBotTop ℝ` value that is neither junk value is the coercion of its `toReal`. -/
private lemma coe_toReal_eq_self {x : WithBotTop ℝ} (h1 : x ≠ ⊥) (h2 : x ≠ ⊤) :
    ((NewtonPolygon.toReal x : ℝ) : WithBotTop ℝ) = x := by
  induction x using WithBotTop.rec with
  | bot => exact absurd rfl h1
  | coe a => rw [NewtonPolygon.toReal_coe]
  | top => exact absurd rfl h2

/-- **The `⊥`-exclusion.** The first slope of the polygon constructed from an admissible
sequence is not `⊥`: `⊥` is the slope of the `unboundedBelow` step only, and that step is taken
exactly when the slope set out of the anchor is unbounded below — which `IsAdmissible` forbids.
(Stated here, against the construction, rather than in the Newton-polygon files.) -/
lemma slopes_zero_ne_bot {Γ : Type*} [CommSemiring Γ] [Algebra Γ ℝ] (v : ℕ → WithTop Γ)
    (h1 : ∃ i, v i ≠ ⊤) (h2 : IsAdmissible v) : (newtonPolygon₀OfSeq v).slopes 0 ≠ ⊥ := by
  intro hbot
  have h0 : slopes' (newtonPolygon v 0) = (⊥ : WithBotTop ℝ) := hbot
  cases hff : findFirstFinite v 0 with
  | none =>
    rw [show newtonPolygon v 0 = some Step.tail by simp only [newtonPolygon, hff]] at h0
    exact absurd h0 (by simp [slopes', slopes])
  | some p =>
    obtain ⟨i, c⟩ := p
    rw [show newtonPolygon v 0 = some (nextStep v i c) by simp only [newtonPolygon, hff]] at h0
    have hub : nextStep v i c = Step.unboundedBelow := by
      cases hnx : nextStep v i c with
      | tail => rw [hnx] at h0; exact absurd h0 (by simp [slopes', slopes])
      | unboundedBelow => rfl
      | limitingRay m => rw [hnx] at h0; exact absurd h0 (by simp [slopes', slopes])
      | infiniteRay m => rw [hnx] at h0; exact absurd h0 (by simp [slopes', slopes])
      | nextVertex j₀ j₁ l m => rw [hnx] at h0; exact absurd h0 (by simp [slopes', slopes])
    have hvi : v i = (c : WithTop Γ) := by
      obtain ⟨k, hk, hvk⟩ := newtonPolygon₀OfSeq_start_mem v h1
      have hsp : (newtonPolygon₀OfSeq v).starting_point = ((i : ℤ), c) := by
        simp only [newtonPolygon₀OfSeq, hff]
      rw [hsp] at hk hvk
      obtain rfl : k = i := by simpa using hk
      exact hvk
    exact unboundedBelow v hub (h2 i c hvi)


open NewtonPolygon₀

/-- **The slope reading, general form** ([Jacobs, proof of Thm 2.12, pp. 34–35]; blueprint
Definition 1): if `v` is the partial-sum sequence of a monotone slope sequence `s`, then the
explicit polygon with slopes `s` *is* the Newton polygon of `v` in the sense of the geometric
specification.  Consequently (by `IsNewtonPolygonOf.height_eq` and
`isNewtonPolygonOf_newtonPolygon₀OfSeq`) the polygon constructed by the step algorithm from
`v` has the same heights, and its slopes are `s` — see the transport lemmas below. -/
theorem isNewtonPolygonOf_ofSlopes (s : ℕ → ℝ) (hs : Monotone s) (y₀ : ℝ)
    (v : ℕ → WithTop ℝ)
    (hv : ∀ m, v m = ((y₀ + ∑ i ∈ range m, s i : ℝ) : WithTop ℝ)) :
    IsNewtonPolygonOf v (ofSlopes s hs y₀) := by
  -- The polygon passes through every point, so `height_le` holds with equality.
  have hpt : ∀ k : ℕ, (ofSlopes s hs y₀).height (k : ℤ) = pointHeight v k := fun k => by
    rw [height_ofSlopes, pointHeight_coe (hv k), Algebra.algebraMap_self_apply]
  refine ⟨fun k hk => ?_, ⟨0, ?_, ?_⟩, fun k => (hpt k).le, fun Q hQ0 hQle => ?_⟩
  · rw [ofSlopes_starting_point] at hk
    exact absurd hk (by simp)
  · rw [ofSlopes_starting_point]
    rfl
  · rw [hv 0, ofSlopes_starting_point]
    simp
  · refine isBelow_iff_height.2 fun x => ?_
    rcases le_or_gt 0 x with hx | hx
    · lift x to ℕ using hx with k
      exact (hQle k).trans (hpt k).ge
    · rw [(Q.height_eq_bot_iff x).2 (by rw [hQ0, ofSlopes_starting_point]; exact hx)]
      exact bot_le

/-- Partial-sum sequences of nonneg-starting monotone slopes are admissible (affine bound
through the minimum slope). -/
theorem isAdmissible_of_partial_sums (s : ℕ → ℝ) (hs : Monotone s) (y₀ : ℝ)
    (v : ℕ → WithTop ℝ)
    (hv : ∀ m, v m = ((y₀ + ∑ i ∈ range m, s i : ℝ) : WithTop ℝ)) :
    IsAdmissible v := by
  refine isAdmissible_of_affine_bound v (m := s 0) (b := y₀) fun k a hk => ?_
  have ha : a = y₀ + ∑ i ∈ range k, s i := by
    have h := hk.symm.trans (hv k)
    exact_mod_cast h
  have hsum : (range k).card • s 0 ≤ ∑ i ∈ range k, s i :=
    Finset.card_nsmul_le_sum _ _ _ fun i _ => hs (Nat.zero_le i)
  rw [Finset.card_range, nsmul_eq_mul] at hsum
  rw [Algebra.algebraMap_self_apply, ha]
  linarith

/-- **Transport by uniqueness**: the polygon constructed by the step algorithm from a
partial-sum sequence has the same height, at every integer, as the explicit slope polygon. -/
theorem height_newtonPolygon₀OfSeq_ofSlopes (s : ℕ → ℝ) (hs : Monotone s) (y₀ : ℝ)
    (v : ℕ → WithTop ℝ)
    (hv : ∀ m, v m = ((y₀ + ∑ i ∈ range m, s i : ℝ) : WithTop ℝ)) (x : ℤ) :
    (newtonPolygon₀OfSeq v).height x = (ofSlopes s hs y₀).height x :=
  (isNewtonPolygonOf_newtonPolygon₀OfSeq v ⟨0, by rw [hv 0]; exact WithTop.coe_ne_top⟩
    (isAdmissible_of_partial_sums s hs y₀ v hv)).height_eq
      (isNewtonPolygonOf_ofSlopes s hs y₀ v hv) x

/-- **Slope transport**: the constructed polygon's unit slopes are the prescribed slopes.
(The unit-interval slopes are the height increments; `⊤`/`⊥` junk values are excluded on the
honest region.) -/
theorem unitSlope_newtonPolygon₀OfSeq_ofSlopes (s : ℕ → ℝ) (hs : Monotone s) (y₀ : ℝ)
    (v : ℕ → WithTop ℝ)
    (hv : ∀ m, v m = ((y₀ + ∑ i ∈ range m, s i : ℝ) : WithTop ℝ)) (j : ℕ) :
    (newtonPolygon₀OfSeq v).unitSlope j = ((s j : ℝ) : WithBotTop ℝ) := by
  have h1 : ∃ i, v i ≠ ⊤ := ⟨0, by rw [hv 0]; exact WithTop.coe_ne_top⟩
  have h2 := isAdmissible_of_partial_sums s hs y₀ v hv
  -- Both polygons are anchored at `0`, so the transported heights are the partial sums.
  have hstart : (newtonPolygon₀OfSeq v).starting_point.1 = 0 :=
    (isNewtonPolygonOf_newtonPolygon₀OfSeq v h1 h2).starting_point_fst_eq
      (isNewtonPolygonOf_ofSlopes s hs y₀ v hv)
  have H : ∀ k : ℕ, (newtonPolygon₀OfSeq v).height
      ((newtonPolygon₀OfSeq v).starting_point.1 + (k : ℤ))
        = ((y₀ + ∑ i ∈ range k, s i : ℝ) : WithBotTop ℝ) := fun k => by
    rw [hstart, zero_add, height_newtonPolygon₀OfSeq_ofSlopes s hs y₀ v hv, height_ofSlopes]
  have hne : ∀ k : ℕ, (newtonPolygon₀OfSeq v).height
      ((newtonPolygon₀OfSeq v).starting_point.1 + (k : ℤ)) ≠ ⊤ := fun k => by
    rw [H k]
    exact WithBotTop.coe_ne_top _
  have hfun : ∀ k : ℕ, (newtonPolygon₀OfSeq v).heightFun k = y₀ + ∑ i ∈ range k, s i := fun k =>
    WithBotTop.coe_injective
      (((newtonPolygon₀OfSeq v).height_eq_heightFun k (hne k)).symm.trans (H k))
  -- The height increment over `[j, j + 1]` pins the real value of the unit slope.
  have hincr : NewtonPolygon.toReal ((newtonPolygon₀OfSeq v).unitSlope j) = s j := by
    have hsucc := (newtonPolygon₀OfSeq v).heightFun_succ j
    rw [hfun (j + 1), hfun j, Finset.sum_range_succ] at hsucc
    linarith
  -- Neither junk value can occur: `⊤` by finiteness of the height, `⊥` by admissibility.
  have htop : (newtonPolygon₀OfSeq v).unitSlope j ≠ ⊤ :=
    (newtonPolygon₀OfSeq v).unitSlope_ne_top_of_height_ne_top (hne (j + 1)) (Nat.lt_succ_self j)
  have hbot : (newtonPolygon₀OfSeq v).unitSlope j ≠ ⊥ := fun hb =>
    slopes_zero_ne_bot v h1 h2
      ((newtonPolygon₀OfSeq v).slopes_zero_eq_bot_of_unitSlope_eq_bot hb).1
  rw [← hincr, coe_toReal_eq_self hbot htop]
