/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.ForMathlib.RingTheory.MvPowerSeries.Restricted.Units
import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.Residue

/-! # Units of restricted power series

Let `R` be a complete normed commutative ring with ultrametric distance and multiplicative
norm.  This file restates the unit criterion of `MvPowerSeries.Restricted` for univariate
restricted power series, with `ℕ`-indexed coefficients.

For an arbitrary strictly positive radius `c`:

* `PowerSeries.Restricted.constantCoeff`: the constant coefficient, as a ring homomorphism
  `Restricted R c →+* R`.
* `PowerSeries.Restricted.norm_constantCoeff_of_isUnit`: the constant coefficient of a unit
  achieves the Gauss norm, and `eq_zero_of_achievesGaussNorm_of_isUnit`: no other index
  achieves it.
* `PowerSeries.Restricted.isUnit_iff`: a restricted power series is a unit if and only if its
  constant coefficient is a unit of `R` and strictly dominates all other weighted
  coefficients, with the two directions available separately as
  `isUnit_of_norm_lt_norm_constantCoeff` and `norm_coeff_lt_norm_constantCoeff_of_isUnit`.

For the Tate algebra radius `c = 1` (with `‖1‖ = 1` and non-isolated origin):

* `PowerSeries.Restricted.isUnit_powerBounded_iff`: an element of the power-bounded subring
  `T°` is a unit if and only if its constant coefficient is a unit of `R°` and all its other
  coefficients are topologically nilpotent.
-/

open Filter PowerBounded
open scoped Topology

namespace PowerSeries.Restricted

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R]

section ConstantCoeff

variable (c : ℝ)

/-- The constant coefficient of a restricted power series, as a ring homomorphism; inherited
from the multivariate case. -/
noncomputable def constantCoeff : Restricted R c →+* R :=
  MvPowerSeries.Restricted.constantCoeff (fun _ ↦ c)

omit [NormMulClass R] in
@[simp]
lemma constantCoeff_apply (f : Restricted R c) :
    constantCoeff c f = PowerSeries.constantCoeff f.1 := rfl

omit [NormMulClass R] in
lemma constantCoeff_eq_coeff_zero (f : Restricted R c) :
    constantCoeff c f = coeff 0 f.1 := by
  rw [constantCoeff_apply, coeff_zero_eq_constantCoeff_apply]

variable [Fact (0 < c)]

omit [NormMulClass R] in
/-- The constant coefficient is bounded by the Gauss norm. -/
lemma norm_constantCoeff_le (f : Restricted R c) : ‖constantCoeff c f‖ ≤ ‖f‖ :=
  MvPowerSeries.Restricted.norm_constantCoeff_le (fun _ ↦ c) f

variable [NormOneClass R]

/-- The constant coefficient of a unit achieves the Gauss norm. -/
theorem norm_constantCoeff_of_isUnit {f : Restricted R c} (hf : IsUnit f) :
    ‖constantCoeff c f‖ = ‖f‖ :=
  MvPowerSeries.Restricted.norm_constantCoeff_of_isUnit (fun _ ↦ c) hf

/-- If the constant coefficient of `f` is a unit of `R` and strictly dominates all other
weighted coefficients, then `f` is a unit. -/
theorem isUnit_of_norm_lt_norm_constantCoeff [CompleteSpace R] {f : Restricted R c}
    (hu : IsUnit (constantCoeff c f))
    (hlt : ∀ n ≠ 0, ‖coeff n f.1‖ * c ^ n < ‖constantCoeff c f‖) : IsUnit f :=
  MvPowerSeries.Restricted.isUnit_of_norm_lt_norm_constantCoeff (fun _ ↦ c) hu fun t ht ↦ by
    obtain ⟨n, rfl⟩ : ∃ n, t = Finsupp.single () n := ⟨t (), Finsupp.unique_single t⟩
    rw [Finsupp.prod_single_index (h := fun _ n ↦ c ^ n) (pow_zero c)]
    exact hlt n (by simpa [Finsupp.single_eq_zero] using ht)

/-- Every index achieving the Gauss norm of a unit is `0`. -/
theorem eq_zero_of_achievesGaussNorm_of_isUnit {f : Restricted R c} (hf : IsUnit f) {n : ℕ}
    (hn : AchievesGaussNorm norm c f.1 n) : n = 0 := by
  have h := MvPowerSeries.Restricted.eq_zero_of_achievesGaussNorm_of_isUnit (fun _ ↦ c) hf
    ((achievesGaussNorm_iff_single norm c f.1 n).mp hn)
  simpa [Finsupp.single_eq_zero] using h

/-- The constant coefficient of a unit strictly dominates every other weighted coefficient. -/
theorem norm_coeff_lt_norm_constantCoeff_of_isUnit {f : Restricted R c} (hf : IsUnit f) {n : ℕ}
    (hn : n ≠ 0) : ‖coeff n f.1‖ * c ^ n < ‖constantCoeff c f‖ := by
  have h := MvPowerSeries.Restricted.norm_coeff_lt_norm_constantCoeff_of_isUnit (fun _ ↦ c) hf
    (t := Finsupp.single () n) (by simpa [Finsupp.single_eq_zero] using hn)
  rwa [Finsupp.prod_single_index (h := fun _ n ↦ c ^ n) (pow_zero c)] at h

/-- **Units of restricted power series**, at an arbitrary radius: `f` is a unit if and only if
its constant coefficient is a unit of `R` and strictly dominates all other weighted
coefficients. -/
theorem isUnit_iff [CompleteSpace R] {f : Restricted R c} :
    IsUnit f ↔ IsUnit (constantCoeff c f) ∧
      ∀ n ≠ 0, ‖coeff n f.1‖ * c ^ n < ‖constantCoeff c f‖ :=
  ⟨fun hf ↦ ⟨hf.map _, fun _ hn ↦ norm_coeff_lt_norm_constantCoeff_of_isUnit c hf hn⟩,
    fun ⟨hu, hlt⟩ ↦ isUnit_of_norm_lt_norm_constantCoeff c hu hlt⟩

end ConstantCoeff

section TateAlgebra

variable [NormOneClass R] [NeBot (𝓝[≠] (0 : R))] [CompleteSpace R]

/-- `R°`, the power-bounded subring of the base ring `R`. -/
local notation "R°" => PowerBounded.subring R (S := ℤ)
/-- `T°`, the power-bounded subring of the Tate algebra `Restricted R 1`. -/
local notation "T°" => PowerBounded.subring (PowerSeries.Restricted R 1) (S := ℤ)

/-- **Units of the power-bounded subring of the Tate algebra**: `f ∈ T°` is a unit if and only
if its constant coefficient is a unit of `R°` and all its other coefficients are topologically
nilpotent; inherited from the multivariate case. -/
theorem isUnit_powerBounded_iff (f : ↥T°) :
    IsUnit f ↔ IsUnit (powerBoundedCoeff f 0) ∧
      ∀ n ≠ 0, IsTopologicallyNilpotent (coeff n f.1.1) := by
  refine (MvPowerSeries.Restricted.isUnit_powerBounded_iff f).trans (and_congr ?_ ?_)
  · have h : MvPowerSeries.Restricted.powerBoundedCoeff f 0 = powerBoundedCoeff f 0 :=
      Subtype.ext (by
        rw [MvPowerSeries.Restricted.powerBoundedCoeff_coe, powerBoundedCoeff_coe]
        show MvPowerSeries.coeff 0 f.1.1 = MvPowerSeries.coeff (Finsupp.single () 0) f.1.1
        rw [Finsupp.single_zero])
    rw [h]
  · constructor
    · intro h n hn
      exact h (Finsupp.single () n) (by simpa [Finsupp.single_eq_zero] using hn)
    · intro h t ht
      obtain ⟨n, rfl⟩ : ∃ n, t = Finsupp.single () n := ⟨t (), Finsupp.unique_single t⟩
      exact h n (by simpa [Finsupp.single_eq_zero] using ht)

end TateAlgebra

end PowerSeries.Restricted
