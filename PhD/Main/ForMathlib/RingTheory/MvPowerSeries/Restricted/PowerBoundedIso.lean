/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.ForMathlib.Analysis.Normed.Ring.PowerBounded
import PhD.Main.ForMathlib.RingTheory.MvPowerSeries.Restricted.PowerBounded

/-! # The power-bounded subring of a Tate algebra is the Tate algebra over the integers

Let `R` be a normed commutative ring with ultrametric distance, multiplicative norm, `‖1‖ = 1`
and non-isolated origin, and write `R°` for its power-bounded subring.  Write `T°` for the
power-bounded subring of the multivariate Tate algebra `Restricted R 1`.

This file proves the structural identity `T° = R°⟨X⟩`: the power-bounded subring of the Tate
algebra over `R` is (isometrically, ring-isomorphically) the Tate algebra over `R°`.

* `MvPowerSeries.Restricted.ofRestrictedRes`: a restricted power series over `R°`, mapped
  coefficientwise into `R`, is a power-bounded restricted power series over `R`.
* `MvPowerSeries.Restricted.powerBoundedEquiv : ↥T° ≃+* Restricted ↥R° 1`, with
  `norm_powerBoundedEquiv` showing it is an isometry.

The radius is fixed at `1`: coefficients of power-bounded series are power-bounded when the
radii are at least `1`, while monomials with power-bounded coefficients are power-bounded when
the radii are at most `1`, so both directions coincide exactly at the Tate radii `c = 1`.
-/

open Filter PowerBounded
open scoped Topology

namespace MvPowerSeries.Restricted

/-- Strict positivity of the Tate algebra radii `(1 : σ → ℝ)`. -/
instance {σ : Type*} : Fact (∀ i : σ, (0 : ℝ) < (1 : σ → ℝ) i) :=
  ⟨fun i ↦ by rw [Pi.one_apply]; exact one_pos⟩

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] [NormOneClass R]
  [NeBot (𝓝[≠] (0 : R))] {σ : Type*}

/-- `R°`, the power-bounded subring of the base ring `R`. -/
local notation "R°" => PowerBounded.subring R (S := ℤ)
/-- `T°`, the power-bounded subring of the Tate algebra `Restricted R 1`. -/
local notation "T°" =>
  PowerBounded.subring (MvPowerSeries.Restricted R (1 : σ → ℝ)) (S := ℤ)

/-- A restricted power series over `R°`, viewed coefficientwise in `R`, is a power-bounded
restricted power series over `R`: the ring homomorphism `R°⟨X⟩ →+* T°`.  This is the inverse of
`powerBoundedEquiv`. -/
noncomputable def ofRestrictedRes : Restricted ↥R° (1 : σ → ℝ) →+* ↥T° :=
  RingHom.codRestrict
    (Restricted.map (1 : σ → ℝ) (φ := R°.subtype) (fun _ ↦ le_rfl))
    (PowerBounded.subring (MvPowerSeries.Restricted R (1 : σ → ℝ)) (S := ℤ))
    fun g ↦ isPowerBounded_of_forall_isPowerBounded_coeff (1 : σ → ℝ) (fun _ ↦ le_rfl)
      fun t ↦ (MvPowerSeries.coeff t g.1).2

@[simp]
lemma coe_ofRestrictedRes (g : Restricted ↥R° (1 : σ → ℝ)) :
    (ofRestrictedRes g : Restricted R (1 : σ → ℝ))
      = Restricted.map (1 : σ → ℝ) (φ := R°.subtype) (fun _ ↦ le_rfl) g := rfl

lemma ofRestrictedRes_injective : Function.Injective (ofRestrictedRes (R := R) (σ := σ)) :=
  fun _ _ h ↦ Restricted.map_injective (1 : σ → ℝ) (φ := R°.subtype) (fun _ ↦ le_rfl)
    Subtype.val_injective (congrArg Subtype.val h)

lemma ofRestrictedRes_surjective : Function.Surjective (ofRestrictedRes (R := R) (σ := σ)) :=
  fun f ↦ ⟨⟨fun t ↦ ⟨MvPowerSeries.coeff t f.1.1,
      isPowerBounded_coeff (1 : σ → ℝ) (fun _ ↦ le_rfl) f.2 t⟩, f.1.2⟩,
    Subtype.ext (Restricted.ext (MvPowerSeries.ext fun _ ↦ rfl))⟩

/-- **The power-bounded subring of the Tate algebra is the Tate algebra over `R°`.**  The
isometric ring isomorphism `(R⟨X⟩)° ≃+* R°⟨X⟩`. -/
noncomputable def powerBoundedEquiv : ↥T° ≃+* Restricted ↥R° (1 : σ → ℝ) :=
  (RingEquiv.ofBijective ofRestrictedRes
    ⟨ofRestrictedRes_injective, ofRestrictedRes_surjective⟩).symm

lemma ofRestrictedRes_powerBoundedEquiv (f : ↥T°) : ofRestrictedRes (powerBoundedEquiv f) = f :=
  (RingEquiv.ofBijective ofRestrictedRes
    ⟨ofRestrictedRes_injective, ofRestrictedRes_surjective⟩).apply_symm_apply f

/-- The coefficients of `powerBoundedEquiv f` are the coefficients of `f`, viewed in `R°`. -/
@[simp]
lemma coe_coeff_powerBoundedEquiv (f : ↥T°) (t : σ →₀ ℕ) :
    ((MvPowerSeries.coeff t (powerBoundedEquiv f).1 : ↥R°) : R) = MvPowerSeries.coeff t f.1.1 :=
  calc ((MvPowerSeries.coeff t (powerBoundedEquiv f).1 : ↥R°) : R)
      = MvPowerSeries.coeff t (ofRestrictedRes (powerBoundedEquiv f)).1.1 := rfl
    _ = MvPowerSeries.coeff t f.1.1 := by rw [ofRestrictedRes_powerBoundedEquiv]

/-- Mapping a restricted power series over `R°` into `R` preserves the Gauss norm: `R° ↪ R` is
an isometry. -/
lemma norm_ofRestrictedRes (g : Restricted ↥R° (1 : σ → ℝ)) :
    ‖ofRestrictedRes g‖ = ‖g‖ :=
  Restricted.norm_map (1 : σ → ℝ) (φ := R°.subtype) (fun _ ↦ rfl) g

/-- `powerBoundedEquiv` is an isometry. -/
lemma norm_powerBoundedEquiv (f : ↥T°) : ‖powerBoundedEquiv f‖ = ‖f‖ := by
  rw [← norm_ofRestrictedRes (powerBoundedEquiv f), ofRestrictedRes_powerBoundedEquiv]

end MvPowerSeries.Restricted
