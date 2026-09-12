/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# Coefficientwise maps commute with inversion of multivariate power series

Mathlib has `MvPowerSeries.map` and the inverse `φ⁻¹` of a multivariate power series over a
field (zero when the constant coefficient vanishes), but not their compatibility.  Over
fields, a ring homomorphism is injective, so the two cases (`constantCoeff φ = 0` or not)
transport along `f`.

## Main declarations

* `MvPowerSeries.map_inv₀` — `map f φ⁻¹ = (map f φ)⁻¹`.
-/

namespace MvPowerSeries

variable {σ K L : Type*} [Field K] [Field L]

/-- Coefficientwise maps between fields commute with inversion. -/
theorem map_inv₀ (f : K →+* L) (φ : MvPowerSeries σ K) :
    MvPowerSeries.map f φ⁻¹ = (MvPowerSeries.map f φ)⁻¹ := by
  by_cases h : MvPowerSeries.constantCoeff φ = 0
  · rw [MvPowerSeries.inv_eq_zero.mpr h, map_zero, eq_comm, MvPowerSeries.inv_eq_zero,
      MvPowerSeries.constantCoeff_map, h, map_zero]
  · have h' : MvPowerSeries.constantCoeff (MvPowerSeries.map f φ) ≠ 0 := by
      rwa [MvPowerSeries.constantCoeff_map, f.injective.ne_iff' (map_zero f)]
    rw [eq_comm, MvPowerSeries.inv_eq_iff_mul_eq_one h', ← map_mul,
      MvPowerSeries.inv_mul_cancel φ h, map_one]

end MvPowerSeries
