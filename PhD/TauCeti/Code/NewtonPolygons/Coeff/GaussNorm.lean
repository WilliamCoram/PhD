/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.NewtonPolygons.Coeff.Polynomial
import PhD.TauCeti.Code.NewtonPolygons.Coeff.SupportValue

/-!
# The Gauss norm as the supporting value

For the radius `c = b ^ m`, the Gauss norm `PowerSeries.gaussNorm norm c f = ⨆ k, ‖aₖ‖ cᵏ` of a
series is `b ^ (-s)` where `s = supportValue (coeffVal v f) m = ⨅ k, (e (v aₖ) - m k)` is the
supporting value of its points at the slope `m` — the Gauss norm is the Legendre transform of the
polygon (roadmap §2.3.1). The series is bounded at the radius exactly when `s ≠ ⊥` (§2.3.2), the
Gauss norm is attained at an index exactly when the polygon has a vertex on the supporting line,
and for a polynomial it is always attained (§2.3.3); `m ↦ -log_b ‖f‖_{b^m}` is concave and
piecewise affine with the unit slopes as its breakpoints, and the polygon is recovered from it
(§2.3.4). The attained form, used by the later layers, reads the Gauss norm off the right endpoint
of the face of slope `m`.

⚠ Sign check ([RM] §2.3.1): for `1 - pX` over `ℚ_p` at `m = 2` (`c = p²`) the Gauss norm is `p`,
and `h 1 - 1·2 = -1`, giving `p ^ 1`.

Mathlib's `Polynomial.gaussNorm` takes a bundled `v : F` with `[FunLike F K ℝ]`; every statement
here is phrased for `PowerSeries.gaussNorm norm c` and polynomials go through the coercion, with
`Polynomial.gaussNorm_toAbsoluteValue` — Mathlib's `NormedField.toAbsoluteValue K` bundles the
norm — as the single bridge (roadmap convention 11).

Roadmap: §2.3. Tau Ceti home: `TauCeti/NumberTheory/NewtonPolygon/GaussNorm.lean`.

## Main results

* `PowerSeries.gaussNorm_rpow_eq_of_supportValue_eq` — `‖f‖_{b^m} = b ^ (-s)`;
* `PowerSeries.hasGaussNorm_rpow_iff` — bounded iff `s ≠ ⊥`;
* `PowerSeries.gaussNorm_rpow_eq_norm_coeff_faceRight` — the attained form;
* `PowerSeries.exists_gaussNorm_rpow_eq_iff` — attained iff a vertex lies on the supporting line;
* `PowerSeries.concaveOn_neg_logb_gaussNorm`, `PowerSeries.neg_logb_gaussNorm_eq_of_unitSlope_le_le`.
-/

open NormedField
open NewtonPolygon (IsAdmissible IsNewtonPolygonOf IsConvexSeq unitSlope IsVertex SlopesUnbounded
  faceLeft faceRight supportValue toEReal)

variable {K : Type*} [NormedField K] {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] (v : NormedAddValuation K Γ)

namespace Polynomial

/-- **The bridge** between Mathlib's polynomial Gauss norm and the power-series Gauss norm of the
coerced polynomial (roadmap convention 11). -/
theorem gaussNorm_toAbsoluteValue {c : ℝ} (hc : 0 ≤ c) (f : Polynomial K) :
    f.gaussNorm (toAbsoluteValue K) c = PowerSeries.gaussNorm norm c (f : PowerSeries K) := by sorry

/-- The Gauss norm of a polynomial is always attained (roadmap §2.3.3). -/
theorem exists_gaussNorm_coe_eq {c : ℝ} (hc : 0 ≤ c) (f : Polynomial K) :
    ∃ k, PowerSeries.gaussNorm norm c (f : PowerSeries K) = ‖f.coeff k‖ * c ^ k := by sorry

end Polynomial

namespace PowerSeries

variable {f : PowerSeries K}

/-- The Gauss-norm term at the radius `b ^ m` as a power of the base. -/
theorem norm_coeff_mul_rpow_pow_eq_rpow {k : ℕ} {γ : Γ} (hγ : v (coeff k f) = (γ : WithTop Γ))
    (m : ℝ) : ‖coeff k f‖ * (v.base ^ m) ^ k = v.base ^ (m * k - v.embed γ) := by sorry

/-! ### Boundedness is finiteness of the supporting value (roadmap §2.3.2) -/

/-- **`f` is bounded at the radius `b ^ m` exactly when the supporting value at `m` is finite.** -/
theorem hasGaussNorm_rpow_iff (m : ℝ) :
    HasGaussNorm norm (v.base ^ m) f ↔ supportValue (coeffVal v f) m ≠ ⊥ := by sorry

/-- The radius form: `f` is bounded at `c > 0` exactly when the supporting value at `log_b c` is
finite. -/
theorem hasGaussNorm_iff_supportValue_ne_bot {c : ℝ} (hc : 0 < c) :
    HasGaussNorm norm c f ↔ supportValue (coeffVal v f) (Real.logb v.base c) ≠ ⊥ := by sorry

/-! ### The Gauss norm is `b ^ (-s)` (roadmap §2.3.1) -/

/-- **The infimum form**: if the supporting value at `m` is the real `s`, the Gauss norm at `b ^ m`
is `b ^ (-s)`. -/
theorem gaussNorm_rpow_eq_of_supportValue_eq {m s : ℝ} (hs : supportValue (coeffVal v f) m = (s : EReal)) :
    gaussNorm norm (v.base ^ m) f = v.base ^ (-s) := by sorry

/-- The Gauss norm of a nonzero bounded series at `b ^ m` is `b ^ (-s)`, `s` the supporting value. -/
theorem gaussNorm_rpow_eq_rpow_neg_toReal {m : ℝ} (hs : supportValue (coeffVal v f) m ≠ ⊥) (hf : f ≠ 0) :
    gaussNorm norm (v.base ^ m) f = v.base ^ (-(supportValue (coeffVal v f) m).toReal) := by sorry

/-- The supporting value is `-log_b` of the Gauss norm. -/
theorem supportValue_coeffVal_eq_neg_logb {m : ℝ} (hs : supportValue (coeffVal v f) m ≠ ⊥) (hf : f ≠ 0) :
    supportValue (coeffVal v f) m =
      ((-Real.logb v.base (gaussNorm norm (v.base ^ m) f) : ℝ) : EReal) := by sorry

/-- **The polygon form**: the supporting value of the polygon is that of the points. -/
theorem supportValue_newtonPolygon_eq (hf : IsAdmissible (coeffVal v f)) (m : ℝ) :
    supportValue (newtonPolygon v f) m = supportValue (coeffVal v f) m := by sorry

/-- **The attained form**: the Gauss norm at `b ^ m` is the term at the right endpoint of the face
of slope `m`. -/
theorem gaussNorm_rpow_eq_norm_coeff_faceRight (hf : IsAdmissible (coeffVal v f)) (h0 : coeff 0 f ≠ 0)
    (hu : SlopesUnbounded (newtonPolygon v f)) (m : ℝ) :
    gaussNorm norm (v.base ^ m) f =
      ‖coeff (faceRight (newtonPolygon v f) m) f‖ * (v.base ^ m) ^ faceRight (newtonPolygon v f) m := by
  sorry

/-- The Gauss norm at `b ^ m` is also the term at the left endpoint of the face of slope `m`. -/
theorem gaussNorm_rpow_eq_norm_coeff_faceLeft (hf : IsAdmissible (coeffVal v f)) (h0 : coeff 0 f ≠ 0)
    (hu : SlopesUnbounded (newtonPolygon v f)) (m : ℝ) :
    gaussNorm norm (v.base ^ m) f =
      ‖coeff (faceLeft (newtonPolygon v f) m) f‖ * (v.base ^ m) ^ faceLeft (newtonPolygon v f) m := by
  sorry

/-! ### Attainment (roadmap §2.3.3) -/

/-- **The Gauss norm is attained at an index exactly when the polygon has a vertex on the supporting
line.** -/
theorem exists_gaussNorm_rpow_eq_iff {m : ℝ} (hs : supportValue (coeffVal v f) m ≠ ⊥) (hf : f ≠ 0) :
    (∃ k, gaussNorm norm (v.base ^ m) f = ‖coeff k f‖ * (v.base ^ m) ^ k) ↔
      ∃ k, IsVertex (newtonPolygon v f) k ∧
        toEReal (newtonPolygon v f k) - ((m * k : ℝ) : EReal) = supportValue (coeffVal v f) m := by
  sorry

/-! ### The Gauss norm as a function of the slope (roadmap §2.3.4) -/

/-- **`m ↦ -log_b ‖f‖_{b^m}` is concave** on the slopes where `f` is bounded. -/
theorem concaveOn_neg_logb_gaussNorm (hf : f ≠ 0) :
    ConcaveOn ℝ {m : ℝ | HasGaussNorm norm (v.base ^ m) f}
      (fun m ↦ -Real.logb v.base (gaussNorm norm (v.base ^ m) f)) := by sorry

/-- **`m ↦ -log_b ‖f‖_{b^m}` is piecewise affine with the unit slopes as breakpoints**: between the
unit slopes at `j` and `j + 1` it is `h (j + 1) - m (j + 1)`. -/
theorem neg_logb_gaussNorm_eq_of_unitSlope_le_le (hf : IsAdmissible (coeffVal v f)) {j : ℕ} {m : ℝ}
    (hj : newtonPolygon v f (j + 1) ≠ ⊤) (h₁ : unitSlope (newtonPolygon v f) j ≤ m)
    (h₂ : (m : WithTop ℝ) ≤ unitSlope (newtonPolygon v f) (j + 1)) :
    -Real.logb v.base (gaussNorm norm (v.base ^ m) f) =
      (newtonPolygon v f (j + 1)).untop₀ - m * (j + 1 : ℕ) := by sorry

/-- **The polygon is recovered from the supporting values**: the polygon and the Gauss norm function
determine each other. -/
theorem toEReal_newtonPolygon_eq_iSup (hf : IsAdmissible (coeffVal v f)) (k : ℕ) :
    toEReal (newtonPolygon v f k) = ⨆ m : ℝ, (supportValue (coeffVal v f) m + ((m * k : ℝ) : EReal)) := by
  sorry

end PowerSeries

namespace Polynomial

variable {f : Polynomial K}

/-- A polynomial has a finite supporting value at every slope. -/
theorem supportValue_coeffVal_ne_bot (f : Polynomial K) (m : ℝ) : supportValue (coeffVal v f) m ≠ ⊥ := by
  sorry

/-- **The attained form for a polynomial**: the Gauss norm at `b ^ m` is the term at the right
endpoint of the face of slope `m`. -/
theorem gaussNorm_rpow_eq_norm_coeff_faceRight (h0 : f.coeff 0 ≠ 0) (m : ℝ) :
    PowerSeries.gaussNorm norm (v.base ^ m) (f : PowerSeries K) =
      ‖f.coeff (faceRight (newtonPolygon v f) m)‖ * (v.base ^ m) ^ faceRight (newtonPolygon v f) m := by
  sorry

end Polynomial
