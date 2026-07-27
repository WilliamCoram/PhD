/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.ForMathlib.RingTheory.MvPowerSeries.GaussNorm
import Mathlib.RingTheory.PowerSeries.GaussNorm

/-!
# Achieving indices and explicit computations for the Gauss norm on power series

`PowerSeries.AchievesGaussNorm` is the `ℕ`-indexed analogue of
`MvPowerSeries.AchievesGaussNorm`: it records that the Gauss norm of a power series is achieved
at a given index.  The lemma `achievesGaussNorm_iff_single` identifies it with the multivariate
predicate at `Finsupp.single () i`.

Since `PowerSeries.gaussNorm` is by definition the multivariate Gauss norm for the constant
radius tuple, the explicit computations (`gaussNorm_C`, `gaussNorm_monomial`, `gaussNorm_X`,
`gaussNorm_one`, `gaussNorm_zero_right`) and `hasGaussNorm_of_finite_support` are direct
specialisations of the `MvPowerSeries` lemmas.
-/

namespace PowerSeries

section Semiring

variable {R : Type*} [Semiring R] (v : R → ℝ) (c : ℝ) (f : PowerSeries R)

/-- Predicate for when the Gauss norm is achieved by an index. -/
abbrev AchievesGaussNorm (i : ℕ) : Prop :=
  v (coeff i f) * c ^ i = gaussNorm v c f

end Semiring

section Ring

variable {R : Type*} [Ring R] (v : R → ℝ) (c : ℝ) (f : PowerSeries R)

lemma achievesGaussNorm_iff_single (i : ℕ) :
    AchievesGaussNorm v c f i ↔
      MvPowerSeries.AchievesGaussNorm v (fun _ ↦ c) f (Finsupp.single () i) := by
  unfold AchievesGaussNorm MvPowerSeries.AchievesGaussNorm
  rw [show ((Finsupp.single () i).prod fun x1 x2 ↦ (fun _ : Unit ↦ c) x1 ^ x2) = c ^ i by
    simp]
  rfl

end Ring

section Semiring

variable {R : Type*} [Semiring R] (v : R → ℝ) (c : ℝ)

/-- A power series with finitely many nonzero coefficients has a finite Gauss norm. -/
lemma hasGaussNorm_of_finite_support (vZero : v 0 = 0) {f : PowerSeries R}
    (hf : (Function.support fun n ↦ coeff n f).Finite) : HasGaussNorm v c f := by
  refine ((hf.image fun n ↦ v (coeff n f) * c ^ n).union
    (Set.finite_singleton 0)).bddAbove.mono ?_
  rintro x ⟨n, rfl⟩
  by_cases hn : coeff n f = 0
  · exact Or.inr (by simp [hn, vZero])
  · exact Or.inl ⟨n, Function.mem_support.mpr hn, rfl⟩

/-- The Gauss norm of a monomial. -/
lemma gaussNorm_monomial (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0) (hc : 0 ≤ c) (n : ℕ)
    (r : R) : gaussNorm v c (monomial n r) = v r * c ^ n :=
  (MvPowerSeries.gaussNorm_monomial v (fun _ ↦ c) vZero vNonneg (fun _ ↦ hc)
    (Finsupp.single () n) r).trans <| by simp

/-- The Gauss norm of a constant. -/
lemma gaussNorm_C (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0) (r : R) :
    gaussNorm v c (C r) = v r :=
  MvPowerSeries.gaussNorm_C v (fun _ ↦ c) vZero vNonneg r

/-- The Gauss norm of `1` is `v 1`. -/
lemma gaussNorm_one (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0) :
    gaussNorm v c (1 : PowerSeries R) = v 1 :=
  MvPowerSeries.gaussNorm_one v (fun _ ↦ c) vZero vNonneg

/-- The Gauss norm of the variable `X` is `v 1 * c`. -/
lemma gaussNorm_X (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0) (hc : 0 ≤ c) :
    gaussNorm v c (X : PowerSeries R) = v 1 * c :=
  MvPowerSeries.gaussNorm_X v (fun _ ↦ c) vZero vNonneg () hc

/-- For the zero radius, the Gauss norm is the value of `v` on the constant coefficient. -/
lemma gaussNorm_zero_right (vNonneg : ∀ a, v a ≥ 0) (f : PowerSeries R) :
    gaussNorm v 0 f = v (f.coeff 0) :=
  (MvPowerSeries.gaussNorm_zero_right v vNonneg f).trans <| by
    rw [← Finsupp.single_zero (), coeff_coeToMvPowerSeries]

/-- The Gauss norm is preserved by coefficientwise base change along a ring hom `φ` that
preserves the value function termwise: if `w (φ a) = v a` for all `a`, then mapping `f` along
`φ` leaves the Gauss norm unchanged.  Univariate specialisation of
`MvPowerSeries.gaussNorm_map`. -/
lemma gaussNorm_map {S : Type*} [Semiring S] (w : S → ℝ) (φ : R →+* S)
    (hφ : ∀ a, w (φ a) = v a) (f : PowerSeries R) :
    gaussNorm w c (map φ f) = gaussNorm v c f :=
  MvPowerSeries.gaussNorm_map v (fun _ ↦ c) w φ hφ f

end Semiring

end PowerSeries
