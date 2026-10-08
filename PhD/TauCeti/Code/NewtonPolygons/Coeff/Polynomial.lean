/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.NewtonPolygons.Coeff.PowerSeries

/-!
# The Newton polygon of a polynomial

`Polynomial.newtonPolygon v f` is the Newton polygon of the coefficient valuation sequence of `f`
(roadmap §2.2.1). It always satisfies the specification, it coincides with the polygon of `f` viewed
as a power series (§2.2.5), it is anchored at the order of vanishing `natTrailingDegree f`, its last
vertex is at `natDegree f`, it has exactly `natDegree f - natTrailingDegree f` unit slopes and its
slopes are unbounded (§2.2.2); `Polynomial.newtonSlopes v f` is the multiset of its unit slopes.
Every unit slope is `e γ / l` for a segment length `l ≥ 1`, and for `Γ = ℤ` a rational number whose
denominator divides the length of its segment (§2.2.3). The polygon of `reverse f` is the reflection
`i ↦ h (d - i)` (§2.2.7), and the operations of `PowerSeries.lean` are restated for polynomials.

Roadmap: §2.2.1–§2.2.3, §2.2.5–§2.2.8. Tau Ceti home:
`TauCeti/NumberTheory/NewtonPolygon/Polynomial.lean`.

## Main definitions

* `Polynomial.newtonPolygon v f`, `Polynomial.newtonSlopes v f : Multiset ℝ`.

## Main results

* `Polynomial.newtonPolygon_coe` — the polygon of the coerced power series is the polygon;
* `Polynomial.anchor_newtonPolygon`, `isVertex_natDegree`, `slopeIndices_newtonPolygon`,
  `card_newtonSlopes`, `slopesUnbounded_newtonPolygon`;
* `Polynomial.exists_unitSlope_eq_div`, `Polynomial.exists_int_unitSlope_eq_div` — rationality;
* `Polynomial.newtonPolygon_reverse` — the reflection (a milestone for §6.2).
-/

open NormedField
open NewtonPolygon (IsAdmissible IsNewtonPolygonOf IsConvexSeq unitSlope finiteSupport anchor
  IsVertex IsSegment slopeIndices slopeMultiset SlopesUnbounded shiftRight scaleHeight)

variable {K : Type*} [NormedField K] {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] (v : NormedAddValuation K Γ)

namespace Polynomial

variable (f : Polynomial K)

/-- **The Newton polygon of a polynomial** with respect to the normed additive valuation `v`
(roadmap §2.2.1). -/
noncomputable def newtonPolygon : ℕ → WithTop ℝ := NewtonPolygon.newtonPolygon (coeffVal v f)

lemma newtonPolygon_def : newtonPolygon v f = NewtonPolygon.newtonPolygon (coeffVal v f) := rfl

variable {f}

/-- **The polygon of a polynomial, viewed as a power series, is the polygon of the polynomial**
(roadmap §2.2.5). -/
theorem newtonPolygon_coe : PowerSeries.newtonPolygon v (f : PowerSeries K) = newtonPolygon v f := by
  sorry

/-- The specification holds for every polynomial (roadmap §2.2.1). -/
theorem isNewtonPolygonOf_newtonPolygon : IsNewtonPolygonOf (coeffVal v f) (newtonPolygon v f) := by
  sorry

theorem newtonPolygon_le (k : ℕ) : newtonPolygon v f k ≤ coeffVal v f k := by sorry

theorem isConvexSeq_newtonPolygon : IsConvexSeq (newtonPolygon v f) := by sorry

@[simp] theorem newtonPolygon_zero : newtonPolygon v (0 : Polynomial K) = fun _ ↦ ⊤ := by sorry

/-! ### Anchoring (roadmap §2.2.2) -/

theorem newtonPolygon_eq_top_of_lt_natTrailingDegree {k : ℕ} (hk : k < f.natTrailingDegree) :
    newtonPolygon v f k = ⊤ := by sorry

theorem newtonPolygon_eq_top_of_natDegree_lt {k : ℕ} (hk : f.natDegree < k) :
    newtonPolygon v f k = ⊤ := by sorry

theorem newtonPolygon_ne_top (hf : f ≠ 0) {k : ℕ} (h₁ : f.natTrailingDegree ≤ k)
    (h₂ : k ≤ f.natDegree) : newtonPolygon v f k ≠ ⊤ := by sorry

/-- The finiteness interval of the polygon is `[natTrailingDegree f, natDegree f]`. -/
theorem newtonPolygon_eq_top_iff (hf : f ≠ 0) {k : ℕ} :
    newtonPolygon v f k = ⊤ ↔ k < f.natTrailingDegree ∨ f.natDegree < k := by sorry

/-- The polygon is anchored at the order of vanishing at `0`. -/
theorem newtonPolygon_natTrailingDegree (hf : f ≠ 0) :
    newtonPolygon v f f.natTrailingDegree = coeffVal v f f.natTrailingDegree := by sorry

/-- The polygon passes through the last point. -/
theorem newtonPolygon_natDegree (hf : f ≠ 0) :
    newtonPolygon v f f.natDegree = coeffVal v f f.natDegree := by sorry

theorem anchor_newtonPolygon (hf : f ≠ 0) : anchor (newtonPolygon v f) = f.natTrailingDegree := by
  sorry

theorem isVertex_natTrailingDegree (hf : f ≠ 0) :
    IsVertex (newtonPolygon v f) f.natTrailingDegree := by sorry

/-- The last vertex is at the degree. -/
theorem isVertex_natDegree (hf : f ≠ 0) : IsVertex (newtonPolygon v f) f.natDegree := by sorry

/-- The slope indices are `[natTrailingDegree f, natDegree f)`. -/
theorem slopeIndices_newtonPolygon (hf : f ≠ 0) :
    slopeIndices (newtonPolygon v f) = Set.Ico f.natTrailingDegree f.natDegree := by sorry

theorem slopeIndices_newtonPolygon_finite : (slopeIndices (newtonPolygon v f)).Finite := by sorry

/-- A polynomial's polygon has unbounded slopes. -/
theorem slopesUnbounded_newtonPolygon : SlopesUnbounded (newtonPolygon v f) := by sorry

/-- **Normalisation** (roadmap §2.2.6): if `coeff 0 f = 1` the polygon is anchored at `(0, 0)`. -/
theorem newtonPolygon_zero_of_coeff_zero_eq_one (h0 : f.coeff 0 = 1) : newtonPolygon v f 0 = 0 := by
  sorry

/-! ### The slope multiset (roadmap §2.2.2) -/

variable (f) in
/-- **The slope multiset of a polynomial**: its unit slopes with multiplicity. -/
noncomputable def newtonSlopes : Multiset ℝ := slopeMultiset (newtonPolygon v f)

lemma newtonSlopes_def : newtonSlopes v f = slopeMultiset (newtonPolygon v f) := rfl

/-- A polynomial has exactly `natDegree f - natTrailingDegree f` unit slopes. -/
theorem card_newtonSlopes : (newtonSlopes v f).card = f.natDegree - f.natTrailingDegree := by sorry

theorem count_newtonSlopes (σ : ℝ) :
    (newtonSlopes v f).count σ = Set.ncard {j | unitSlope (newtonPolygon v f) j = σ} := by sorry

/-! ### Rationality (roadmap §2.2.3) -/

/-- Every slope index lies in a segment between two consecutive vertices. -/
theorem exists_isSegment_of_mem_slopeIndices {j : ℕ} (hj : j ∈ slopeIndices (newtonPolygon v f)) :
    ∃ a b, IsSegment (newtonPolygon v f) a b ∧ a ≤ j ∧ j < b := by sorry

/-- **Every unit slope of a polynomial is `e γ / l`** for some `γ : Γ` and some segment length
`l ≥ 1`. -/
theorem exists_unitSlope_eq_div {j : ℕ} (hj : j ∈ slopeIndices (newtonPolygon v f)) :
    ∃ (γ : Γ) (l : ℕ), 0 < l ∧
      unitSlope (newtonPolygon v f) j = ((v.embed γ / l : ℝ) : WithTop ℝ) := by sorry

/-- **For `Γ = ℤ` every slope is a rational number whose denominator divides the length of its
segment.** -/
theorem exists_int_unitSlope_eq_div {w : NormedAddValuation K ℤ} (he : ∀ n : ℤ, w.embed n = n)
    {j : ℕ} (hj : j ∈ slopeIndices (newtonPolygon w f)) :
    ∃ (a b : ℕ) (n : ℤ), IsSegment (newtonPolygon w f) a b ∧ a ≤ j ∧ j < b ∧
      unitSlope (newtonPolygon w f) j = (((n : ℚ) / ((b - a : ℕ) : ℚ) : ℚ) : ℝ) := by sorry

/-! ### The reflection (roadmap §2.2.7) -/

theorem coeffVal_reverse : coeffVal v f.reverse = NewtonPolygon.reflect f.natDegree (coeffVal v f) := by sorry

/-- **The polygon of `reverse f` is the reflection `i ↦ h (d - i)`**, `d = natDegree f`. -/
theorem newtonPolygon_reverse :
    newtonPolygon v f.reverse = NewtonPolygon.reflect f.natDegree (newtonPolygon v f) := by sorry

/-! ### Operations, for polynomials (roadmap §2.2.6–§2.2.7) -/

/-- `f (cX)`, as a power series, is the rescaled coerced series. -/
theorem coe_comp_C_mul_X (c : K) :
    ((f.comp (C c * X) : Polynomial K) : PowerSeries K) = PowerSeries.rescale c (f : PowerSeries K) := by
  sorry

/-- **The polygon of `f (cX)` is sheared by `e (v c)`.** -/
theorem newtonPolygon_comp_C_mul_X {c : K} {γ : Γ} (hc : v c = (γ : WithTop Γ)) :
    newtonPolygon v (f.comp (C c * X)) =
      fun k ↦ newtonPolygon v f k + ((v.embed γ * k : ℝ) : WithTop ℝ) := by sorry

/-- **The polygon of `X ^ n * f` is translated right by `n`.** -/
theorem newtonPolygon_X_pow_mul (n : ℕ) :
    newtonPolygon v (X ^ n * f) = shiftRight n (newtonPolygon v f) := by sorry

theorem newtonPolygon_C_mul {c : K} {γ : Γ} (hc : v c = (γ : WithTop Γ)) :
    newtonPolygon v (C c * f) = fun k ↦ newtonPolygon v f k + (v.embed γ : WithTop ℝ) := by sorry

/-- Dividing by the constant term translates the polygon down by its valuation. -/
theorem newtonPolygon_C_inv_mul {γ : Γ} (h0 : v (f.coeff 0) = (γ : WithTop Γ)) :
    newtonPolygon v (C ((f.coeff 0)⁻¹) * f) =
      fun k ↦ newtonPolygon v f k + ((-v.embed γ : ℝ) : WithTop ℝ) := by sorry

variable {L : Type*} [NormedField L]

/-- **The polygon is unchanged under a compatible base change.** -/
theorem newtonPolygon_map (w : NormedAddValuation L Γ) (φ : K →+* L) (hφ : ∀ x, w (φ x) = v x)
    (he : w.embed = v.embed) : newtonPolygon w (f.map φ) = newtonPolygon v f := by sorry

variable {Γ' : Type*} [AddCommGroup Γ'] [LinearOrder Γ'] [IsOrderedAddMonoid Γ']
  (w : NormedAddValuation K Γ')

/-- **The polygons for two normed additive valuations differ by the scalar `log b / log b'`.** -/
theorem newtonPolygon_eq_scaleHeight :
    newtonPolygon w f = scaleHeight (v.scale w) (newtonPolygon v f) := by sorry

/-- The slope multisets differ by the same scalar. -/
theorem newtonSlopes_eq_map : newtonSlopes w f = (newtonSlopes v f).map (fun t : ℝ ↦ v.scale w * t) := by
  sorry

end Polynomial
