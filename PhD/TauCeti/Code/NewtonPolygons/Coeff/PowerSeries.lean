/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Topology.Order.WithTop
import PhD.TauCeti.Code.NewtonPolygons.Face
import PhD.TauCeti.Code.NewtonPolygons.Coeff.CoeffVal
import PhD.TauCeti.Code.NewtonPolygons.Coeff.Generic

/-!
# The Newton polygon of a power series

`PowerSeries.newtonPolygon v f` is the Newton polygon (Layer 0) of the coefficient valuation
sequence of `f` with respect to the normed additive valuation `v` (roadmap §2.2.1). It satisfies the
specification whenever `f` is restricted at some positive radius; the heights at its vertices lie in
the image of `e`, and its unit slopes on a segment between two vertices are quotients of such heights
by the length (§2.2.3); an entire series has unbounded slopes tending to `+∞`, and a unit slope
exceeding `σ` forces restrictedness at the radius `b ^ σ` (§2.2.4, corrected direction — see the
board's plan); the normalisation `coeff 0 f = 1` anchors the polygon at the origin and dividing by
the constant term translates it (§2.2.6); the polygon of `f (cX)` is sheared, that of `X ^ n * f` is
shifted right by `n`, and the polygon is unchanged under a compatible base change (§2.2.7); and two
normed additive valuations on the same field give polygons differing by the positive scalar
`log b / log b'` in height (§2.2.8).

Roadmap: §2.2.1, §2.2.3, §2.2.4, §2.2.6, §2.2.7, §2.2.8. Tau Ceti home:
`TauCeti/NumberTheory/NewtonPolygon/PowerSeries.lean`.

## Main definitions

* `PowerSeries.newtonPolygon v f`.

## Main results

* `PowerSeries.isNewtonPolygonOf_newtonPolygon_of_isRestricted` — the specification holds;
* `PowerSeries.exists_eq_embed_of_isVertex`, `PowerSeries.exists_unitSlope_eq_div_of_isSegment` —
  integrality and rationality;
* `PowerSeries.slopesUnbounded_newtonPolygon_of_forall_isRestricted`,
  `PowerSeries.isRestricted_rpow_of_lt_unitSlope`;
* `PowerSeries.newtonPolygon_C_mul`, `newtonPolygon_rescale`, `newtonPolygon_X_pow_mul`,
  `newtonPolygon_map`, `newtonPolygon_eq_scaleHeight`.
-/

open NormedField Filter Topology
open NewtonPolygon (IsAdmissible IsNewtonPolygonOf IsConvexSeq unitSlope finiteSupport IsVertex
  IsSegment slopeIndices SlopesUnbounded shiftRight scaleHeight)

variable {K : Type*} [NormedField K] {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] (v : NormedAddValuation K Γ)

namespace PowerSeries

variable (f : PowerSeries K)

/-- **The Newton polygon of a power series** with respect to the normed additive valuation `v`:
the polygon of its coefficient valuation sequence (roadmap §2.2.1). -/
noncomputable def newtonPolygon : ℕ → WithTop ℝ := NewtonPolygon.newtonPolygon (coeffVal v f)

lemma newtonPolygon_def : newtonPolygon v f = NewtonPolygon.newtonPolygon (coeffVal v f) := rfl

variable {f}

/-- The specification holds when the coefficient valuation sequence is admissible. -/
theorem isNewtonPolygonOf_newtonPolygon (hf : IsAdmissible (coeffVal v f)) :
    IsNewtonPolygonOf (coeffVal v f) (newtonPolygon v f) := by sorry

/-- **The specification holds** for a series restricted at some positive radius (roadmap §2.2.1). -/
theorem isNewtonPolygonOf_newtonPolygon_of_isRestricted {c : ℝ} (hc : 0 < c)
    (hf : IsRestricted c f) : IsNewtonPolygonOf (coeffVal v f) (newtonPolygon v f) := by sorry

theorem newtonPolygon_le (hf : IsAdmissible (coeffVal v f)) (k : ℕ) :
    newtonPolygon v f k ≤ coeffVal v f k := by sorry

theorem isConvexSeq_newtonPolygon (hf : IsAdmissible (coeffVal v f)) :
    IsConvexSeq (newtonPolygon v f) := by sorry

@[simp] theorem newtonPolygon_zero : newtonPolygon v (0 : PowerSeries K) = fun _ ↦ ⊤ := by sorry

/-- The polygon passes through the first point `(0, e (v (coeff 0 f)))` when `coeff 0 f ≠ 0`. -/
theorem newtonPolygon_zero_eq (hf : IsAdmissible (coeffVal v f)) (h0 : coeff 0 f ≠ 0) :
    newtonPolygon v f 0 = coeffVal v f 0 := by sorry

/-- **Normalisation** (roadmap §2.2.6): if `coeff 0 f = 1` the polygon is anchored at `(0, 0)`. -/
theorem newtonPolygon_zero_of_coeff_zero_eq_one (hf : IsAdmissible (coeffVal v f))
    (h0 : coeff 0 f = 1) : newtonPolygon v f 0 = 0 := by sorry

/-! ### Integrality and rationality (roadmap §2.2.3) -/

/-- **Integrality**: the height at a vertex is `e γ` for the value `γ` of the coefficient there. -/
theorem exists_eq_embed_of_isVertex (hf : IsAdmissible (coeffVal v f)) {k : ℕ}
    (hk : IsVertex (newtonPolygon v f) k) :
    ∃ γ : Γ, v (coeff k f) = (γ : WithTop Γ) ∧ newtonPolygon v f k = (v.embed γ : WithTop ℝ) := by
  sorry

/-- **Rationality on a segment**: a unit slope lying in the segment `[a, b]` between two vertices is
`e γ / (b - a)` for some `γ : Γ`. -/
theorem exists_unitSlope_eq_div_of_isSegment (hf : IsAdmissible (coeffVal v f)) {a b : ℕ}
    (hab : IsSegment (newtonPolygon v f) a b) {j : ℕ} (haj : a ≤ j) (hjb : j < b) :
    ∃ γ : Γ, unitSlope (newtonPolygon v f) j = ((v.embed γ / ((b : ℝ) - a) : ℝ) : WithTop ℝ) := by
  sorry

/-- **Rationality for `Γ = ℤ`**: with the embedding the cast, a unit slope on the segment `[a, b]`
is a rational number with denominator dividing `b - a`. -/
theorem exists_int_unitSlope_eq_div_of_isSegment {w : NormedAddValuation K ℤ}
    (he : ∀ n : ℤ, w.embed n = n) (hf : IsAdmissible (coeffVal w f)) {a b : ℕ}
    (hab : IsSegment (newtonPolygon w f) a b) {j : ℕ} (haj : a ≤ j) (hjb : j < b) :
    ∃ n : ℤ, unitSlope (newtonPolygon w f) j = (((n : ℚ) / ((b - a : ℕ) : ℚ) : ℚ) : ℝ) := by sorry

/-! ### Entire series and the radius (roadmap §2.2.4) -/

/-- **An entire series has unbounded slopes.** -/
theorem slopesUnbounded_newtonPolygon_of_forall_isRestricted (hf : ∀ c : ℝ, 0 < c → IsRestricted c f) :
    SlopesUnbounded (newtonPolygon v f) := by sorry

/-- The unit slopes of an entire series tend to `+∞`. -/
theorem tendsto_unitSlope_newtonPolygon (hf : ∀ c : ℝ, 0 < c → IsRestricted c f) :
    Tendsto (unitSlope (newtonPolygon v f)) atTop (𝓝 ⊤) := by sorry

/-- A unit slope exceeding `σ`, at a finite index of the polygon, forces restrictedness at the
radius `b ^ σ`. (At an index before the anchor the unit slope is `⊤` and says nothing.) -/
theorem isRestricted_rpow_of_lt_unitSlope (hf : IsAdmissible (coeffVal v f)) {σ : ℝ} {j : ℕ}
    (hjf : newtonPolygon v f j ≠ ⊤) (hj : (σ : WithTop ℝ) < unitSlope (newtonPolygon v f) j) :
    IsRestricted (v.base ^ σ) f := by sorry

/-- A series not restricted at the radius `b ^ σ` has all its unit slopes at finite indices at most
`σ`. -/
theorem unitSlope_le_of_not_isRestricted (hf : IsAdmissible (coeffVal v f)) {σ : ℝ}
    (hσ : ¬ IsRestricted (v.base ^ σ) f) {j : ℕ} (hjf : newtonPolygon v f j ≠ ⊤) :
    unitSlope (newtonPolygon v f) j ≤ σ := by sorry

/-! ### Multiplying by a constant (roadmap §2.2.6) -/

theorem coeffVal_C_mul {c : K} {γ : Γ} (hc : v c = (γ : WithTop Γ)) :
    coeffVal v (C c * f) = fun k ↦ coeffVal v f k + (v.embed γ : WithTop ℝ) := by sorry

/-- Multiplying by a nonzero constant translates the polygon by the constant's valuation. -/
theorem newtonPolygon_C_mul (hf : IsAdmissible (coeffVal v f)) {c : K} {γ : Γ}
    (hc : v c = (γ : WithTop Γ)) :
    newtonPolygon v (C c * f) = fun k ↦ newtonPolygon v f k + (v.embed γ : WithTop ℝ) := by sorry

theorem coeff_zero_C_inv_mul (h0 : coeff 0 f ≠ 0) : coeff 0 (C ((coeff 0 f)⁻¹) * f) = 1 := by sorry

/-- **Dividing by the constant term** translates the polygon down by its valuation (roadmap
§2.2.6). -/
theorem newtonPolygon_C_inv_mul (hf : IsAdmissible (coeffVal v f)) {γ : Γ}
    (h0 : v (coeff 0 f) = (γ : WithTop Γ)) :
    newtonPolygon v (C ((coeff 0 f)⁻¹) * f) =
      fun k ↦ newtonPolygon v f k + ((-v.embed γ : ℝ) : WithTop ℝ) := by sorry

/-! ### Rescaling and shifting (roadmap §2.2.7) -/

theorem coeffVal_rescale {c : K} {γ : Γ} (hc : v c = (γ : WithTop Γ)) :
    coeffVal v (rescale c f) = fun k ↦ coeffVal v f k + ((v.embed γ * k : ℝ) : WithTop ℝ) := by
  sorry

/-- **The polygon of `f (cX)` is sheared by `e (v c)`.** -/
theorem newtonPolygon_rescale (hf : IsAdmissible (coeffVal v f)) {c : K} {γ : Γ}
    (hc : v c = (γ : WithTop Γ)) :
    newtonPolygon v (rescale c f) =
      fun k ↦ newtonPolygon v f k + ((v.embed γ * k : ℝ) : WithTop ℝ) := by sorry

theorem coeffVal_X_pow_mul (n : ℕ) : coeffVal v (X ^ n * f) = shiftRight n (coeffVal v f) := by
  sorry

/-- **The polygon of `X ^ n * f` is translated right by `n`.** -/
theorem newtonPolygon_X_pow_mul (hf : IsAdmissible (coeffVal v f)) (n : ℕ) :
    newtonPolygon v (X ^ n * f) = shiftRight n (newtonPolygon v f) := by sorry

/-! ### Compatible base change (roadmap §2.2.7) -/

variable {L : Type*} [NormedField L]

theorem coeffVal_map (w : NormedAddValuation L Γ) (φ : K →+* L) (hφ : ∀ x, w (φ x) = v x)
    (he : w.embed = v.embed) : coeffVal w (map φ f) = coeffVal v f := by sorry

/-- **The polygon is unchanged under a compatible base change.** -/
theorem newtonPolygon_map (w : NormedAddValuation L Γ) (φ : K →+* L) (hφ : ∀ x, w (φ x) = v x)
    (he : w.embed = v.embed) : newtonPolygon w (map φ f) = newtonPolygon v f := by sorry

/-! ### Changing the normed additive valuation (roadmap §2.2.8) -/

variable {Γ' : Type*} [AddCommGroup Γ'] [LinearOrder Γ'] [IsOrderedAddMonoid Γ']
  (w : NormedAddValuation K Γ')

theorem coeffVal_eq_scaleHeight : coeffVal w f = scaleHeight (v.scale w) (coeffVal v f) := by sorry

/-- Admissibility does not depend on the normed additive valuation. -/
theorem isAdmissible_coeffVal_iff : IsAdmissible (coeffVal w f) ↔ IsAdmissible (coeffVal v f) := by
  sorry

/-- **The polygons for two normed additive valuations differ by the positive scalar
`log b / log b'` in height.** -/
theorem newtonPolygon_eq_scaleHeight (hf : IsAdmissible (coeffVal v f)) :
    newtonPolygon w f = scaleHeight (v.scale w) (newtonPolygon v f) := by sorry

end PowerSeries
