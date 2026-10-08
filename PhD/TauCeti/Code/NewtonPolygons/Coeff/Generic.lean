/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.NewtonPolygons.Slope

/-!
# Transforms of a polygon of a sequence

Generic facts about the Newton polygon of a sequence `v : ℕ → WithTop ℝ` that the polygons of
polynomials and power series need (roadmap §2.2.3 and §2.2.7–§2.2.8) and that Layer 0 does not
provide: the polygon of a sequence **shifted right** by `n` is the shifted polygon (multiplication
by `X ^ n`), the polygon of a sequence **reflected** in `[0, d]` is the reflected polygon
(`Polynomial.reverse`), the polygon of a sequence whose heights are **scaled** by a positive
constant is the scaled polygon (changing the normed additive valuation), a finitely supported
sequence is admissible, and every unit slope of a polygon with finitely many slopes lies in a
segment between two vertices, where it is the quotient of a height difference by the length.

Each transport is proved through the specification `IsNewtonPolygonOf` and uniqueness, never
through the construction (roadmap §0.2.4).

Roadmap: Layer 2, §2.2.3, §2.2.7, §2.2.8. Tau Ceti home: Layer 0's
`TauCeti/NumberTheory/NewtonPolygon/{Basic,Slope}.lean`, to be merged there at upstreaming.

## Main definitions

* `NewtonPolygon.shiftRight n v`, `NewtonPolygon.reflect d v`, `NewtonPolygon.scaleHeight c v`.

## Main results

* `NewtonPolygon.newtonPolygon_shiftRight`, `NewtonPolygon.newtonPolygon_reflect`,
  `NewtonPolygon.newtonPolygon_scaleHeight` — the three transports;
* `NewtonPolygon.exists_isSegment_of_mem_slopeIndices`,
  `NewtonPolygon.IsConvexSeq.unitSlope_eq_div_of_isSegment` — slopes as quotients.
-/

open Order

namespace NewtonPolygon

variable {v h : ℕ → WithTop ℝ}

/-- A finitely supported sequence is admissible: a horizontal line below its finitely many finite
values lies below every point. -/
theorem isAdmissible_of_finite (hfin : (finiteSupport v).Finite) : IsAdmissible v := by sorry

/-! ### Shifting right -/

/-- The sequence shifted right by `n`: `⊤` on `[0, n)`, then `v`. -/
def shiftRight (n : ℕ) (v : ℕ → WithTop ℝ) : ℕ → WithTop ℝ :=
  fun k ↦ if n ≤ k then v (k - n) else ⊤

@[simp] theorem shiftRight_add (n : ℕ) (v : ℕ → WithTop ℝ) (k : ℕ) :
    shiftRight n v (k + n) = v k := by sorry

theorem shiftRight_of_le {n k : ℕ} (hk : n ≤ k) (v : ℕ → WithTop ℝ) :
    shiftRight n v k = v (k - n) := by sorry

theorem shiftRight_of_lt {n k : ℕ} (hk : k < n) (v : ℕ → WithTop ℝ) : shiftRight n v k = ⊤ := by
  sorry

@[simp] theorem shiftRight_zero (v : ℕ → WithTop ℝ) : shiftRight 0 v = v := by sorry

theorem unitSlope_shiftRight (n : ℕ) (h : ℕ → WithTop ℝ) (k : ℕ) :
    unitSlope (shiftRight n h) (k + n) = unitSlope h k := by sorry

theorem isConvexSeq_shiftRight_iff (n : ℕ) : IsConvexSeq (shiftRight n h) ↔ IsConvexSeq h := by
  sorry

theorem isNewtonPolygonOf_shiftRight_iff (n : ℕ) :
    IsNewtonPolygonOf (shiftRight n v) (shiftRight n h) ↔ IsNewtonPolygonOf v h := by sorry

theorem isAdmissible_shiftRight_iff (n : ℕ) : IsAdmissible (shiftRight n v) ↔ IsAdmissible v := by
  sorry

/-- **The polygon of a shifted sequence is the shifted polygon.** -/
theorem newtonPolygon_shiftRight (hv : IsAdmissible v) (n : ℕ) :
    newtonPolygon (shiftRight n v) = shiftRight n (newtonPolygon v) := by sorry

/-! ### Reflecting in `[0, d]` -/

/-- The sequence reflected in `[0, d]`: `k ↦ v (d - k)` on `[0, d]`, `⊤` beyond. -/
def reflect (d : ℕ) (v : ℕ → WithTop ℝ) : ℕ → WithTop ℝ :=
  fun k ↦ if k ≤ d then v (d - k) else ⊤

theorem reflect_of_le {d k : ℕ} (hk : k ≤ d) (v : ℕ → WithTop ℝ) : reflect d v k = v (d - k) := by
  sorry

theorem reflect_of_lt {d k : ℕ} (hk : d < k) (v : ℕ → WithTop ℝ) : reflect d v k = ⊤ := by sorry

theorem reflect_reflect {d : ℕ} (hv : ∀ k, d < k → v k = ⊤) : reflect d (reflect d v) = v := by
  sorry

/-- Reflection reverses and negates the unit slopes. -/
theorem unitSlope_reflect {d k : ℕ} (hk : k < d) (h : ℕ → WithTop ℝ) :
    unitSlope (reflect d h) k = -unitSlope h (d - (k + 1)) := by sorry

theorem IsConvexSeq.reflect (hh : IsConvexSeq h) {d : ℕ} (hd : ∀ k, d < k → h k = ⊤) :
    IsConvexSeq (reflect d h) := by sorry

theorem IsNewtonPolygonOf.reflect (hh : IsNewtonPolygonOf v h) {d : ℕ}
    (hv : ∀ k, d < k → v k = ⊤) : IsNewtonPolygonOf (reflect d v) (reflect d h) := by sorry

/-- **The polygon of a reflected sequence is the reflected polygon**, for a sequence supported in
`[0, d]`. -/
theorem newtonPolygon_reflect {d : ℕ} (hv : ∀ k, d < k → v k = ⊤) :
    newtonPolygon (reflect d v) = reflect d (newtonPolygon v) := by sorry

/-! ### Scaling heights -/

/-- The sequence with heights multiplied by `c` (`⊤` stays `⊤`). -/
def scaleHeight (c : ℝ) (v : ℕ → WithTop ℝ) : ℕ → WithTop ℝ :=
  fun k ↦ WithTop.map (fun t : ℝ ↦ c * t) (v k)

theorem scaleHeight_apply (c : ℝ) (v : ℕ → WithTop ℝ) (k : ℕ) :
    scaleHeight c v k = WithTop.map (fun t : ℝ ↦ c * t) (v k) := rfl

theorem scaleHeight_eq_top_iff (c : ℝ) {k : ℕ} : scaleHeight c v k = ⊤ ↔ v k = ⊤ := by sorry

theorem finiteSupport_scaleHeight (c : ℝ) : finiteSupport (scaleHeight c v) = finiteSupport v := by
  sorry

theorem unitSlope_scaleHeight (c : ℝ) (h : ℕ → WithTop ℝ) (k : ℕ) :
    unitSlope (scaleHeight c h) k = WithTop.map (fun t : ℝ ↦ c * t) (unitSlope h k) := by sorry

theorem isConvexSeq_scaleHeight_iff {c : ℝ} (hc : 0 < c) :
    IsConvexSeq (scaleHeight c h) ↔ IsConvexSeq h := by sorry

theorem isNewtonPolygonOf_scaleHeight_iff {c : ℝ} (hc : 0 < c) :
    IsNewtonPolygonOf (scaleHeight c v) (scaleHeight c h) ↔ IsNewtonPolygonOf v h := by sorry

theorem isAdmissible_scaleHeight_iff {c : ℝ} (hc : 0 < c) :
    IsAdmissible (scaleHeight c v) ↔ IsAdmissible v := by sorry

/-- **The polygon of a scaled sequence is the scaled polygon**, for a positive scalar. -/
theorem newtonPolygon_scaleHeight {c : ℝ} (hc : 0 < c) (hv : IsAdmissible v) :
    newtonPolygon (scaleHeight c v) = scaleHeight c (newtonPolygon v) := by sorry

theorem slopeMultiset_scaleHeight {c : ℝ} (hc : 0 < c) (hfin : (slopeIndices h).Finite) :
    slopeMultiset (scaleHeight c h) = (slopeMultiset h).map (fun t : ℝ ↦ c * t) := by sorry

/-! ### Segments of a polygon with finitely many slopes -/

/-- Every slope index of a convex sequence with finitely many slopes lies in a segment between two
consecutive vertices. -/
theorem exists_isSegment_of_mem_slopeIndices (hh : IsConvexSeq h) (hfin : (slopeIndices h).Finite)
    {j : ℕ} (hj : j ∈ slopeIndices h) : ∃ a b, IsSegment h a b ∧ a ≤ j ∧ j < b := by sorry

/-- On a segment the unit slope is the height difference of the endpoints over the length. -/
theorem IsConvexSeq.unitSlope_eq_div_of_isSegment (hh : IsConvexSeq h) {a b : ℕ}
    (hab : IsSegment h a b) {j : ℕ} (haj : a ≤ j) (hjb : j < b) :
    unitSlope h j = ((((h b).untop₀ - (h a).untop₀) / ((b : ℝ) - a) : ℝ) : WithTop ℝ) := by sorry

end NewtonPolygon
