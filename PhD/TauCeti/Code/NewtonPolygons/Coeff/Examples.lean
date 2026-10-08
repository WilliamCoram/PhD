/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import PhD.TauCeti.Code.NewtonPolygons.Examples
import PhD.TauCeti.Code.NewtonPolygons.Coeff.Padic
import PhD.TauCeti.Code.NewtonPolygons.Coeff.Distinguished
import PhD.TauCeti.Code.NewtonPolygons.Coeff.Extension

/-!
# Examples: polygons over `ℚ_p` with `v p = 1`

The worked examples of roadmap Layer 2 and the corresponding acceptance examples, all with respect
to `Padic.normedAddValuation p` (so that `v p = 1` and slopes are honest rational numbers):
`1 - X` (slope `0`) and `1 - pX` (slope `1`); `1 + pX + p³X²` (slopes `1, 2`); `1 + pX + p²X²`,
whose middle point lies on the polygon without being a vertex; `1 + 3^{2j+1} X²` over `ℚ_3`, pure
of slope `j + ½`; `Φ_p` with polygon flat at height `0`, against `Φ_p(X + 1) / p`, pure of slope
`-1/(p-1)`; the pure series `1 + pX + p²X² + ⋯` of slope `1`; the entire series `∑ pⁱ² Xⁱ` with unit
slopes `1, 3, 5, …`; the series `1 + pX + pX² + ⋯` bounded but not restricted at radius `1`
(separating `HasGaussNorm` from `IsRestricted`, roadmap §2.3.2); and the rescaling of the polygon
between `normAddValZ` and `normAddVal` by `log p` (roadmap §2.2.8).

Roadmap: Layer 2 Examples, Acceptance examples. Tau Ceti home: a test file.
-/

open NormedField
open NewtonPolygon (IsVertex unitSlope SlopesUnbounded scaleHeight)

variable {p : ℕ} [Fact p.Prime]

local notation "𝓥" => Padic.normedAddValuation p

namespace Polynomial

/-! ### `1 - X` and `1 - pX` -/

/-- `1 - X` is pure of slope `0`. -/
theorem isPure_one_sub_X : IsPure 𝓥 (1 - X : Polynomial ℚ_[p]) 0 := by sorry

/-- The slope multiset of `1 - X` is `{0}`. -/
theorem newtonSlopes_one_sub_X : newtonSlopes 𝓥 (1 - X : Polynomial ℚ_[p]) = {0} := by sorry

/-- `1 - pX` is pure of slope `1`. -/
theorem isPure_one_sub_p_mul_X : IsPure 𝓥 (1 - C (p : ℚ_[p]) * X) 1 := by sorry

/-- The slope multiset of `1 - pX` is `{1}`. -/
theorem newtonSlopes_one_sub_p_mul_X : newtonSlopes 𝓥 (1 - C (p : ℚ_[p]) * X) = {1} := by sorry

/-! ### `1 + pX + p³X²` and the collinear `1 + pX + p²X²` -/

/-- The slope multiset of `1 + pX + p³X²` is `{1, 2}`. -/
theorem newtonSlopes_one_add_p_mul_X_add_p_cube_mul_X_sq :
    newtonSlopes 𝓥 (1 + C (p : ℚ_[p]) * X + C ((p : ℚ_[p]) ^ 3) * X ^ 2) = {1, 2} := by sorry

/-- The middle point of `1 + pX + p²X²` lies on its polygon. -/
theorem newtonPolygon_one_add_p_mul_X_add_p_sq_mul_X_sq_one :
    newtonPolygon 𝓥 (1 + C (p : ℚ_[p]) * X + C ((p : ℚ_[p]) ^ 2) * X ^ 2) 1 =
      coeffVal 𝓥 (1 + C (p : ℚ_[p]) * X + C ((p : ℚ_[p]) ^ 2) * X ^ 2) 1 := by sorry

/-- … but it is not a vertex. -/
theorem not_isVertex_one_add_p_mul_X_add_p_sq_mul_X_sq_one :
    ¬ IsVertex (newtonPolygon 𝓥 (1 + C (p : ℚ_[p]) * X + C ((p : ℚ_[p]) ^ 2) * X ^ 2)) 1 := by sorry

/-- The slope multiset of `1 + pX + p²X²` is nevertheless `{1, 1}`. -/
theorem newtonSlopes_one_add_p_mul_X_add_p_sq_mul_X_sq :
    newtonSlopes 𝓥 (1 + C (p : ℚ_[p]) * X + C ((p : ℚ_[p]) ^ 2) * X ^ 2) = {1, 1} := by sorry

/-! ### `1 + 3^{2j+1} X²` over `ℚ_3` -/

/-- **`1 + 3^{2j+1} X²` is pure of slope `j + ½`** over `ℚ_3`, as an equality of rational numbers. -/
theorem isPure_one_add_three_pow_mul_X_sq (j : ℕ) :
    IsPure (Padic.normedAddValuation 3) (1 + C ((3 : ℚ_[3]) ^ (2 * j + 1)) * X ^ 2)
      ((j : ℝ) + 1 / 2) := by sorry

/-- Its slope multiset is `{j + ½, j + ½}`. -/
theorem newtonSlopes_one_add_three_pow_mul_X_sq (j : ℕ) :
    newtonSlopes (Padic.normedAddValuation 3) (1 + C ((3 : ℚ_[3]) ^ (2 * j + 1)) * X ^ 2) =
      Multiset.replicate 2 ((j : ℝ) + 1 / 2) := by sorry

/-! ### The cyclotomic polynomial -/

/-- The polygon of `Φ_p` is flat at height `0`. -/
theorem newtonPolygon_cyclotomic {k : ℕ} (hk : k < p) : newtonPolygon 𝓥 (cyclotomic p ℚ_[p]) k = 0 := by
  sorry

/-- `Φ_p` is pure of slope `0`. -/
theorem isPure_cyclotomic : IsPure 𝓥 (cyclotomic p ℚ_[p]) 0 := by sorry

/-- The coefficients of `Φ_p(X + 1)` are the binomial coefficients `C(p, i + 1)`. -/
theorem coeff_cyclotomic_comp_X_add_one (i : ℕ) :
    ((cyclotomic p ℚ_[p]).comp (X + 1)).coeff i = (p.choose (i + 1) : ℚ_[p]) := by sorry

/-- **`Φ_p(X + 1) / p` is pure of slope `-1/(p-1)`.** -/
theorem isPure_C_inv_mul_cyclotomic_comp_X_add_one :
    IsPure 𝓥 (C ((p : ℚ_[p])⁻¹) * (cyclotomic p ℚ_[p]).comp (X + 1)) (-1 / ((p : ℝ) - 1)) := by sorry

/-! ### Rescaling between the two valuations of `ℚ_p` (roadmap §2.2.8) -/

/-- The polygon for `normAddVal` is `log p` times the polygon for `normAddValZ`. -/
theorem newtonPolygon_ofNormAddVal_eq_scaleHeight (f : Polynomial ℚ_[p]) :
    newtonPolygon (NormedAddValuation.ofNormAddVal ℚ_[p]) f =
      scaleHeight (Real.log p) (newtonPolygon 𝓥 f) := by sorry

end Polynomial

namespace PowerSeries

/-! ### The pure series `1 + pX + p²X² + ⋯` -/

/-- `∑ pⁱ Xⁱ` is pure of slope `1`. -/
theorem isPure_mk_p_pow : IsPure 𝓥 (mk fun i : ℕ ↦ (p : ℚ_[p]) ^ i) 1 := by sorry

/-! ### The entire series `∑ pⁱ² Xⁱ` -/

/-- `∑ pⁱ² Xⁱ` is restricted at every positive radius: it is entire. -/
theorem isRestricted_mk_p_pow_sq {c : ℝ} (hc : 0 < c) :
    IsRestricted c (mk fun i : ℕ ↦ (p : ℚ_[p]) ^ (i ^ 2)) := by sorry

/-- Its points are the parabola `k ↦ k²`. -/
theorem coeffVal_mk_p_pow_sq :
    coeffVal 𝓥 (mk fun i : ℕ ↦ (p : ℚ_[p]) ^ (i ^ 2)) = fun k : ℕ ↦ (((k : ℝ) ^ 2 : ℝ) : WithTop ℝ) := by
  sorry

/-- Its polygon is the parabola itself. -/
theorem newtonPolygon_mk_p_pow_sq :
    newtonPolygon 𝓥 (mk fun i : ℕ ↦ (p : ℚ_[p]) ^ (i ^ 2)) =
      fun k : ℕ ↦ (((k : ℝ) ^ 2 : ℝ) : WithTop ℝ) := by sorry

/-- **Its unit slopes are `1, 3, 5, …`.** -/
theorem unitSlope_newtonPolygon_mk_p_pow_sq (j : ℕ) :
    unitSlope (newtonPolygon 𝓥 (mk fun i : ℕ ↦ (p : ℚ_[p]) ^ (i ^ 2))) j =
      ((2 * j + 1 : ℝ) : WithTop ℝ) := by sorry

theorem slopesUnbounded_newtonPolygon_mk_p_pow_sq :
    SlopesUnbounded (newtonPolygon 𝓥 (mk fun i : ℕ ↦ (p : ℚ_[p]) ^ (i ^ 2))) := by sorry

/-! ### Bounded but not restricted (roadmap §2.3.2) -/

/-- `1 + pX + pX² + ⋯` is bounded at radius `1`. -/
theorem hasGaussNorm_one_mk_ite :
    HasGaussNorm norm 1 (mk fun i : ℕ ↦ if i = 0 then (1 : ℚ_[p]) else (p : ℚ_[p])) := by sorry

/-- … but not restricted at radius `1`: boundedness is strictly weaker than restrictedness. -/
theorem not_isRestricted_one_mk_ite :
    ¬ IsRestricted 1 (mk fun i : ℕ ↦ if i = 0 then (1 : ℚ_[p]) else (p : ℚ_[p])) := by sorry

end PowerSeries
