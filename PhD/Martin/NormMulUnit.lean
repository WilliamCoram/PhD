/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.Normed.Field.Basic

/-! # Multiplicative units of a normed ring

`IsNormMulUnit u`: `u` is a unit and multiplication by `u` is norm-multiplicative,
`‖u * a‖ = ‖u‖ * ‖a‖` for every `a`.  This is the notion of *multiplicative unit* of
[Mar16, Definition 1.20], the hypothesis under which Weierstrass division works over an
arbitrary ultrametric complete normed ring at an arbitrary radius.

Source: F. Martin, *Overconvergent subanalytic subsets in the framework of Berkovich
spaces*, J. EMS 18 (2016), §1.3.
-/

variable {A : Type*} [NormedRing A]

/-- A **multiplicative unit** of a normed ring: a unit `u` with `‖u * a‖ = ‖u‖ * ‖a‖` for
every `a`.  Source: [Mar16, Definition 1.20]. -/
def IsNormMulUnit (u : A) : Prop :=
  IsUnit u ∧ ∀ a : A, ‖u * a‖ = ‖u‖ * ‖a‖

namespace IsNormMulUnit

lemma isUnit {u : A} (hu : IsNormMulUnit u) : IsUnit u := hu.1

lemma norm_mul {u : A} (hu : IsNormMulUnit u) (a : A) : ‖u * a‖ = ‖u‖ * ‖a‖ := hu.2 a

/-- Products of multiplicative units are multiplicative units.
Source: [Mar16, note after Definition 1.20]. -/
lemma mul {u v : A} (hu : IsNormMulUnit u) (hv : IsNormMulUnit v) :
    IsNormMulUnit (u * v) :=
  ⟨hu.isUnit.mul hv.isUnit, fun a => by
    rw [mul_assoc, hu.norm_mul, hv.norm_mul, hu.norm_mul, mul_assoc]⟩

end IsNormMulUnit

lemma isNormMulUnit_one [NormOneClass A] : IsNormMulUnit (1 : A) :=
  ⟨isUnit_one, fun a => by rw [one_mul, norm_one, one_mul]⟩

/-- A multiplicative unit satisfies `‖u⁻¹‖ = ‖u‖⁻¹`.
Source: [Mar16, Lemma 1.21], forward direction. -/
lemma IsNormMulUnit.norm_coe_inv_units [NormOneClass A] {u : Aˣ}
    (hu : IsNormMulUnit (u : A)) : ‖((u⁻¹ : Aˣ) : A)‖ = ‖(u : A)‖⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← hu.norm_mul, Units.mul_inv, norm_one])

/-- A unit with `‖u⁻¹‖ = ‖u‖⁻¹` is a multiplicative unit.
Source: [Mar16, Lemma 1.21], converse direction. -/
lemma isNormMulUnit_of_norm_coe_inv_units {u : Aˣ}
    (hn : ‖((u⁻¹ : Aˣ) : A)‖ = ‖(u : A)‖⁻¹) : IsNormMulUnit (u : A) := by
  refine ⟨u.isUnit, fun a => le_antisymm (norm_mul_le _ _) ?_⟩
  by_cases h0 : ‖(u : A)‖ = 0
  · rw [h0, zero_mul]
    exact norm_nonneg _
  · have hpos : 0 < ‖(u : A)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have hcancel : ‖a‖ = ‖((u⁻¹ : Aˣ) : A) * ((u : A) * a)‖ := by
      rw [Units.inv_mul_cancel_left]
    have key : ‖a‖ ≤ ‖(u : A)‖⁻¹ * ‖(u : A) * a‖ := by
      rw [hcancel, ← hn]
      exact norm_mul_le _ _
    exact (le_inv_mul_iff₀ hpos).mp key

/-- The inverse of a multiplicative unit is a multiplicative unit.
Source: [Mar16, Lemma 1.21] applied twice. -/
lemma IsNormMulUnit.coe_inv_units [NormOneClass A] {u : Aˣ}
    (hu : IsNormMulUnit (u : A)) : IsNormMulUnit ((u⁻¹ : Aˣ) : A) :=
  isNormMulUnit_of_norm_coe_inv_units (by rw [inv_inv, hu.norm_coe_inv_units, inv_inv])

/-- In a complete ultrametric normed ring, `1 + x` is a multiplicative unit whenever
`‖x‖ < 1`.  Source: [Mar16, Remark 1.22]. -/
lemma isNormMulUnit_one_add [IsUltrametricDist A] [NormOneClass A] [CompleteSpace A]
    {x : A} (hx : ‖x‖ < 1) : IsNormMulUnit (1 + x) := by
  have hne1 : ‖(1 : A)‖ ≠ ‖x‖ := by rw [norm_one]; exact hx.ne'
  have h1x : ‖(1 : A) + x‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne1, norm_one, max_eq_left hx.le]
  refine ⟨?_, fun a => ?_⟩
  · have h := isUnit_one_sub_of_norm_lt_one (x := -x) (by simpa using hx)
    simpa only [sub_neg_eq_add] using h
  · rw [h1x, one_mul]
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · have hpos : 0 < ‖a‖ := norm_pos_iff.mpr ha
      have hxa : ‖x * a‖ < ‖a‖ :=
        calc ‖x * a‖ ≤ ‖x‖ * ‖a‖ := norm_mul_le x a
          _ < 1 * ‖a‖ := mul_lt_mul_of_pos_right hx hpos
          _ = ‖a‖ := one_mul _
      rw [add_mul, one_mul, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hxa.ne',
        max_eq_left hxa.le]

/-- When the norm is multiplicative, every unit is a multiplicative unit.  This is the
bridge to the project's `NormMulClass`-based Weierstrass theory. -/
lemma IsUnit.isNormMulUnit [NormMulClass A] {u : A} (hu : IsUnit u) :
    IsNormMulUnit u := ⟨hu, fun a => norm_mul u a⟩
