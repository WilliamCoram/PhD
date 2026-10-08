/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.MulAction

/-!
# Multiplicative elements of a normed ring

An element `a` of a normed ring is *multiplicative* if `‖a * x‖ = ‖a‖ * ‖x‖` for every `x`: the
single-element form of `NormMulClass`. A unit is multiplicative exactly when `‖u⁻¹‖ = ‖u‖⁻¹`, and a
multiplicative unit scales the norm of every normed module exactly. This is the notion that lets a
ring element play the role of a scalar of a ground field.

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, §0.2.4. Tau Ceti home:
`TauCeti/Analysis/Normed/Ring/Ultra/Multiplicative.lean`.

## Main definitions

* `NormedRing.IsMultiplicative a` — `‖a * x‖ = ‖a‖ * ‖x‖` for all `x`.

## Main results

* `NormedRing.isMultiplicative_units_iff` — a unit is multiplicative iff `‖u⁻¹‖ = ‖u‖⁻¹`.
* `NormedRing.IsMultiplicative.norm_smul` — `‖u • m‖ = ‖u‖ * ‖m‖` for a multiplicative unit.
-/

namespace NormedRing

/-- An element `a` is *multiplicative* if `‖a * x‖ = ‖a‖ * ‖x‖` for all `x`. Source:
Johansson–Newton, §2.1 (before Definition 2.1.2); Bellaïche, Exercise II.1.1. -/
def IsMultiplicative {R : Type*} [Norm R] [Mul R] (a : R) : Prop := ∀ x : R, ‖a * x‖ = ‖a‖ * ‖x‖

namespace IsMultiplicative

section Basic

variable {R : Type*} [SeminormedRing R] {a b : R}

/-- Source: roadmap §0.2.4. -/
theorem norm_mul (ha : IsMultiplicative a) (x : R) : ‖a * x‖ = ‖a‖ * ‖x‖ := ha x

/-- Source: roadmap §0.2.4. -/
theorem mul (ha : IsMultiplicative a) (hb : IsMultiplicative b) : IsMultiplicative (a * b) := by
  intro x
  rw [mul_assoc, ha, hb, ha, mul_assoc]

/-- Source: roadmap §0.2.4. -/
theorem norm_pow_mul (ha : IsMultiplicative a) (n : ℕ) (x : R) :
    ‖a ^ n * x‖ = ‖a‖ ^ n * ‖x‖ := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_assoc, ih, ha, pow_succ, mul_assoc]

variable [NormOneClass R]

/-- Source: roadmap §0.2.4. -/
theorem one : IsMultiplicative (1 : R) := by
  intro x
  rw [one_mul, norm_one, one_mul]

/-- Source: roadmap §0.2.4. -/
theorem norm_pow (ha : IsMultiplicative a) (n : ℕ) : ‖a ^ n‖ = ‖a‖ ^ n := by
  simpa using ha.norm_pow_mul n 1

/-- Source: roadmap §0.2.4. -/
theorem pow (ha : IsMultiplicative a) (n : ℕ) : IsMultiplicative (a ^ n) := by
  intro x
  rw [ha.norm_pow_mul, ha.norm_pow]

end Basic

end IsMultiplicative

/-- Source: roadmap §0.2.4 (every element is multiplicative for a multiplicative norm). -/
theorem isMultiplicative_of_normMulClass {R : Type*} [Norm R] [Mul R] [NormMulClass R] (a : R) :
    IsMultiplicative a := by
  exact fun x ↦ _root_.norm_mul a x

section Units

variable {R : Type*} [SeminormedRing R] [NormOneClass R]

/-- Source: Johansson–Newton, §2.1: "a unit `ϖ` in a normed ring `R` is multiplicative if and only
if `|ϖ⁻¹| = |ϖ|⁻¹`"; Bellaïche, Exercise II.1.1. -/
theorem isMultiplicative_units_iff (u : Rˣ) :
    IsMultiplicative (u : R) ↔ ‖((u⁻¹ : Rˣ) : R)‖ = ‖(u : R)‖⁻¹ := by
  constructor
  · intro hu
    have h := hu ((u⁻¹ : Rˣ) : R)
    rw [Units.mul_inv, norm_one] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  · intro h x
    have h1 : (1 : ℝ) ≤ ‖(u : R)‖ * ‖(u : R)‖⁻¹ := by
      calc (1 : ℝ) = ‖(u : R) * ((u⁻¹ : Rˣ) : R)‖ := by rw [Units.mul_inv, norm_one]
        _ ≤ ‖(u : R)‖ * ‖((u⁻¹ : Rˣ) : R)‖ := _root_.norm_mul_le _ _
        _ = _ := by rw [h]
    have hpos : 0 < ‖(u : R)‖ := by
      rcases (norm_nonneg (u : R)).eq_or_lt with h0 | h0
      · rw [← h0] at h1
        norm_num at h1
      · exact h0
    refine le_antisymm (_root_.norm_mul_le _ _) ?_
    have h2 : ‖x‖ ≤ ‖(u : R)‖⁻¹ * ‖(u : R) * x‖ := by
      calc ‖x‖ = ‖((u⁻¹ : Rˣ) : R) * ((u : R) * x)‖ := by rw [Units.inv_mul_cancel_left]
        _ ≤ ‖((u⁻¹ : Rˣ) : R)‖ * ‖(u : R) * x‖ := _root_.norm_mul_le _ _
        _ = _ := by rw [h]
    rwa [le_inv_mul_iff₀ hpos] at h2

namespace IsMultiplicative

variable {u : Rˣ}

/-- Source: roadmap §0.2.4. -/
theorem norm_pos (hu : IsMultiplicative (u : R)) : 0 < ‖(u : R)‖ := by
  have h := hu ((u⁻¹ : Rˣ) : R)
  rw [Units.mul_inv, norm_one] at h
  refine (norm_nonneg _).lt_of_ne fun h0 ↦ ?_
  rw [← h0, zero_mul] at h
  exact one_ne_zero h

/-- Source: roadmap §0.2.4. -/
theorem norm_inv (hu : IsMultiplicative (u : R)) : ‖((u⁻¹ : Rˣ) : R)‖ = ‖(u : R)‖⁻¹ := by
  exact (isMultiplicative_units_iff u).1 hu

/-- Source: roadmap §0.2.4. -/
theorem inv (hu : IsMultiplicative (u : R)) : IsMultiplicative ((u⁻¹ : Rˣ) : R) := by
  exact (isMultiplicative_units_iff u⁻¹).2 (by rw [inv_inv, hu.norm_inv, inv_inv])

/-- Source: roadmap §0.2.4. -/
theorem zpow (hu : IsMultiplicative (u : R)) (n : ℤ) : IsMultiplicative ((u ^ n : Rˣ) : R) := by
  have hnat : ∀ k : ℕ, IsMultiplicative ((u ^ k : Rˣ) : R) := fun k ↦ by
    rw [Units.val_pow_eq_pow_val]
    exact hu.pow k
  rcases n with k | k
  · rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact hnat k
  · rw [zpow_negSucc]
    exact (hnat (k + 1)).inv

/-- Source: roadmap §0.2.4. -/
theorem norm_zpow (hu : IsMultiplicative (u : R)) (n : ℤ) :
    ‖((u ^ n : Rˣ) : R)‖ = ‖(u : R)‖ ^ n := by
  have hnat : ∀ k : ℕ, IsMultiplicative ((u ^ k : Rˣ) : R) := fun k ↦ by
    rw [Units.val_pow_eq_pow_val]
    exact hu.pow k
  rcases n with k | k
  · rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val, hu.norm_pow]
  · rw [zpow_negSucc, zpow_negSucc, (hnat (k + 1)).norm_inv, Units.val_pow_eq_pow_val,
      hu.norm_pow]

variable {M : Type*} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]

/-- Source: Johansson–Newton, Definition 2.1.4: "if `r ∈ R` is a multiplicative unit, then one sees
easily that `‖rm‖ = |r|·‖m‖` for all `m ∈ M`"; Bellaïche, proof of Lemma II.1.12. -/
theorem norm_smul (hu : IsMultiplicative (u : R)) (m : M) : ‖(u : R) • m‖ = ‖(u : R)‖ * ‖m‖ := by
  refine le_antisymm (norm_smul_le _ _) ?_
  have h2 : ‖m‖ ≤ ‖(u : R)‖⁻¹ * ‖(u : R) • m‖ := by
    calc ‖m‖ = ‖((u⁻¹ : Rˣ) : R) • ((u : R) • m)‖ := by rw [smul_smul, Units.inv_mul, one_smul]
      _ ≤ ‖((u⁻¹ : Rˣ) : R)‖ * ‖(u : R) • m‖ := norm_smul_le _ _
      _ = _ := by rw [hu.norm_inv]
  rwa [le_inv_mul_iff₀ hu.norm_pos] at h2

/-- Source: roadmap §0.2.4, §0.4.2. -/
theorem norm_zpow_smul (hu : IsMultiplicative (u : R)) (n : ℤ) (m : M) :
    ‖((u ^ n : Rˣ) : R) • m‖ = ‖(u : R)‖ ^ n * ‖m‖ := by
  rw [(hu.zpow n).norm_smul, hu.norm_zpow]

end IsMultiplicative

end Units

end NormedRing
