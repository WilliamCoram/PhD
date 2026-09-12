/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.ForMathlib.RingTheory.MvPowerSeries.Restricted.PowerBoundedIso
import PhD.Main.ForMathlib.RingTheory.PowerSeries.Restricted.PowerBounded

/-! # The power-bounded subring of a Tate algebra is the Tate algebra over the integers

Let `R` be a normed commutative ring with ultrametric distance, multiplicative norm, `‖1‖ = 1`
and non-isolated origin, and write `R°` for its power-bounded subring.  Write `T°` for the
power-bounded subring of the Tate algebra `Restricted R 1`.

This file restates the structural identity `T° = R°⟨X⟩` of
`MvPowerSeries.Restricted.powerBoundedEquiv` for univariate restricted power series, with
`ℕ`-indexed coefficients:

* `PowerSeries.Restricted.ofRestrictedRes : Restricted ↥R° 1 →+* ↥T°`, the coefficientwise
  inclusion.
* `PowerSeries.Restricted.powerBoundedEquiv : ↥T° ≃+* Restricted ↥R° 1`, with
  `norm_powerBoundedEquiv` showing it is an isometry.

`PowerSeries.Restricted R c` is a reducible specialisation of the multivariate construction at
`σ := Unit`, so each declaration is definitionally the multivariate one; this file only fixes
the univariate spellings (`Restricted R 1` at the scalar radius, `PowerSeries.coeff`).
-/

open Filter PowerBounded
open scoped Topology

namespace PowerSeries.Restricted

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] [NormOneClass R]
  [NeBot (𝓝[≠] (0 : R))]

/-- `R°`, the power-bounded subring of the base ring `R`. -/
local notation "R°" => PowerBounded.subring R (S := ℤ)
/-- `T°`, the power-bounded subring of the Tate algebra `Restricted R 1`. -/
local notation "T°" => PowerBounded.subring (PowerSeries.Restricted R 1) (S := ℤ)

/-- A restricted power series over `R°`, viewed coefficientwise in `R`, is a power-bounded
restricted power series over `R`: the ring homomorphism `R°⟨X⟩ →+* T°`.  This is the inverse of
`powerBoundedEquiv`. -/
noncomputable def ofRestrictedRes : Restricted ↥R° 1 →+* ↥T° :=
  MvPowerSeries.Restricted.ofRestrictedRes

@[simp]
lemma coe_ofRestrictedRes (g : Restricted ↥R° 1) :
    (ofRestrictedRes g).1.1 = PowerSeries.map R°.subtype g.1 := rfl

lemma ofRestrictedRes_injective : Function.Injective (ofRestrictedRes (R := R)) :=
  MvPowerSeries.Restricted.ofRestrictedRes_injective

lemma ofRestrictedRes_surjective : Function.Surjective (ofRestrictedRes (R := R)) :=
  MvPowerSeries.Restricted.ofRestrictedRes_surjective

/-- **The power-bounded subring of the Tate algebra is the Tate algebra over `R°`.**  The
isometric ring isomorphism `(R⟨X⟩)° ≃+* R°⟨X⟩`. -/
noncomputable def powerBoundedEquiv : ↥T° ≃+* Restricted ↥R° 1 :=
  MvPowerSeries.Restricted.powerBoundedEquiv

lemma ofRestrictedRes_powerBoundedEquiv (f : ↥T°) : ofRestrictedRes (powerBoundedEquiv f) = f :=
  MvPowerSeries.Restricted.ofRestrictedRes_powerBoundedEquiv f

/-- The coefficients of `powerBoundedEquiv f` are the coefficients of `f`, viewed in `R°`. -/
@[simp]
lemma coe_coeff_powerBoundedEquiv (f : ↥T°) (v : ℕ) :
    ((coeff v (powerBoundedEquiv f).1 : ↥R°) : R) = coeff v f.1.1 :=
  MvPowerSeries.Restricted.coe_coeff_powerBoundedEquiv f (Finsupp.single () v)

/-- Mapping a restricted power series over `R°` into `R` preserves the Gauss norm: `R° ↪ R` is
an isometry. -/
lemma norm_ofRestrictedRes (g : Restricted ↥R° 1) : ‖ofRestrictedRes g‖ = ‖g‖ :=
  MvPowerSeries.Restricted.norm_ofRestrictedRes g

/-- `powerBoundedEquiv` is an isometry. -/
lemma norm_powerBoundedEquiv (f : ↥T°) : ‖powerBoundedEquiv f‖ = ‖f‖ :=
  MvPowerSeries.Restricted.norm_powerBoundedEquiv f

end PowerSeries.Restricted
