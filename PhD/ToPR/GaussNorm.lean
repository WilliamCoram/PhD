/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/

import Mathlib.Data.Real.Archimedean
import Mathlib.RingTheory.PowerSeries.Order

import PhD.ToPR.MvGaussNorm

/-!
# Gauss norm for power series
This file defines the Gauss norm for power series using the gaussNorm for multivariate power series.
Given a power series `f` in `R⟦X⟧`, a function `v : R → ℝ` and a real number `c`, the Gauss norm is
defined as the supremum of the set of all values of `v (f.coeff i) * c ^ i` for all `i : ℕ`.

In case `f` is a polynomial, `v` is a non-negative function with `v 0 = 0` and `c ≥ 0`,
`f.gaussNorm v c` reduces to the Gauss norm defined in
`Mathlib/RingTheory/Polynomial/GaussNorm.lean`, see `Polynomial.gaussNorm_coe_powerSeries`.

## Main Definitions and Results
* Using `PowerSeries.gaussNorm_eq`, `PowerSeries.gaussNorm` is the supremum of the set of all values
  of `v (f.coeff i) * c ^ i` for all `i : ℕ`, where `f` is a power series in `R⟦X⟧`, `v : R → ℝ` is
  a function and `c` is a real number.

* `PowerSeries.gaussNorm_nonneg`: if `v` is a non-negative function, then the Gauss norm is
  non-negative.

* `PowerSeries.gaussNorm_eq_zero_iff`: if `v` is a non-negative function and `v x = 0 ↔ x = 0` for
  all `x : R` and `c` is positive, then the Gauss norm is zero if and only if the power series is
  zero.

* `PowerSeries.gaussNormC_eq_zero_iff`: if `v` is a non-negative function and `v x = 0 ↔ x = 0`
  for all `x : R` and `c` is positive, then the Gauss norm is zero if and only if the power series
  is zero.

* `PowerSeries.gaussNorm_add_le_max`: if `v` is a non-negative non-archimedean function and the
  set of values `v (coeff t f) * c ^ t` is bounded above (similarily for `g`), then
  the Gauss norm has the non-archimedean property.
-/

public section

namespace PowerSeries

variable {R : Type*} (v : R → ℝ) (c : ℝ)

section Semiring

variable [Semiring R] (f : PowerSeries R)

/-- Given a power series `f` in, a function `v : R → ℝ` and a real number `c`, the Gauss norm is
  defined as the supremum of the set of all values of `v (coeff t f) * c ^ t` for all `t : ℕ`. -/
noncomputable
abbrev gaussNorm : ℝ := MvPowerSeries.gaussNorm v (fun _ => c) f

lemma gaussNorm_eq : gaussNorm v c f = ⨆ i : ℕ, v (f.coeff i) * c ^ i := by
  refine Equiv.iSup_congr Equiv.finsuppUnique ?_
  intro x
  simp only [coeff, Equiv.finsuppUnique_apply, PUnit.default_eq_unit, Finsupp.prod_pow,
    Finset.univ_unique, Finset.prod_singleton, show (Finsupp.single () (x PUnit.unit)) = x by grind]

abbrev HasGaussNorm := MvPowerSeries.HasGaussNorm v (fun _ ↦ c) f

lemma hasGaussNorm_iff :
    HasGaussNorm v c f ↔ BddAbove (Set.range (fun (t : ℕ) ↦ (v (coeff t f) * c ^ t))) := by
  constructor
  all_goals
  intro hf
  suffices (Set.range (fun (t : ℕ) ↦ (v (coeff t f) * c ^ t))) =
      Set.range fun t ↦ v ((MvPowerSeries.coeff t) f) * t.prod fun _ x2 ↦ c ^ x2 by
    simpa only [HasGaussNorm, MvPowerSeries.HasGaussNorm, ← this] using hf
  refine Set.ext (fun _ ↦ ?_)
  simp only [Set.mem_range, Finsupp.prod_pow, Finset.univ_unique, PUnit.default_eq_unit,
    Finset.prod_singleton]
  constructor
  · intro h
    obtain ⟨y, _⟩ := h
    use Finsupp.single () y
    aesop
  · intro h
    obtain ⟨y, hy⟩ := h
    use (y PUnit.unit)
    simpa [coeff, show (Finsupp.single () (y PUnit.unit)) = y by grind]

theorem gaussNorm_zero (vZero : v 0 = 0) : gaussNorm v c 0 = 0 :=
  MvPowerSeries.gaussNorm_zero v (fun _ ↦ c) vZero

lemma le_gaussNorm (hbd : HasGaussNorm v c f) (t : ℕ) :
    v (coeff t f) * c ^ t ≤ gaussNorm v c f := by
  rw [gaussNorm_eq]
  apply le_ciSup ((hasGaussNorm_iff v c f).mp hbd)

lemma gaussNorm_nonneg (vNonneg : ∀ a, v a ≥ 0) : 0 ≤ gaussNorm v c f :=
  MvPowerSeries.gaussNorm_nonneg v (fun _ ↦ c) f vNonneg

lemma gaussNorm_eq_zero_iff (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0)
    (h_eq_zero : ∀ x : R, v x = 0 → x = 0) (hc : 0 < c) (hbd : HasGaussNorm v c f) :
    gaussNorm v c f = 0 ↔ f = 0 :=
  MvPowerSeries.gaussNorm_eq_zero_iff v (fun _ ↦ c) f vZero vNonneg h_eq_zero
    (by grind) hbd

lemma gaussNorm_add_le_max (g : PowerSeries R) (hc : 0 ≤ c)
    (vNonneg : ∀ a, v a ≥ 0) (hv : ∀ x y, v (x + y) ≤ max (v x) (v y))
    (hbfd : HasGaussNorm v c f) (hbgd : HasGaussNorm v c g) :
    gaussNorm v c (f + g) ≤ max (gaussNorm v c f) (gaussNorm v c g) :=
  MvPowerSeries.gaussNorm_add_le_max v (fun _ ↦ c) f g (fun _ => by simp [hc]) vNonneg hv hbfd hbgd

lemma gaussNorm_neg [Ring R] (vNeg : ∀ x, v (-x) = v x) :
    gaussNorm v c (-f) = gaussNorm v c f  :=
  MvPowerSeries.gaussNorm_neg v (fun _ ↦ c) vNeg f

end Semiring

variable [Ring R] (f : PowerSeries R)

lemma gaussNorm_mul_le (f g : PowerSeries R) (hc : 0 ≤ c) (vNonneg : ∀ a, v a ≥ 0)
    (vMul : ∀ a b, v (a * b) ≤ v a * v b) (vUltra : ∀ a b, v (a + b) ≤ max (v a) (v b))
    (vZero : v 0 = 0) (hbfd : HasGaussNorm v c f) (hbgd : HasGaussNorm v c g) :
    gaussNorm v c (f * g) ≤ gaussNorm v c f * gaussNorm v c g :=
  MvPowerSeries.gaussNorm_mul_le v (fun _ ↦ c) f g (fun _ => by simp [hc]) vNonneg vMul vUltra vZero
    hbfd hbgd

section absoluteValue

abbrev achievesGaussNorm (i : ℕ) : Prop :=
  MvPowerSeries.AchievesGaussNorm v (fun _ ↦ c) f (Finsupp.single () i)

lemma achievesGaussNorm_iff (i : ℕ) : achievesGaussNorm v c f i ↔
    v (coeff i f) * c ^ i = gaussNorm v c f := by
  simp [achievesGaussNorm, MvPowerSeries.AchievesGaussNorm, PowerSeries.coeff]

lemma exists_antidiagDom_iff_exists_mvAntidiagDom (f g : PowerSeries R) :
    (∃ i j,
    achievesGaussNorm v c f i ∧ achievesGaussNorm v c g j ∧
    ∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
    v (coeff p.1 f * coeff p.2 g) < v (coeff i f) * v (coeff j g)) ↔
    (∃ i j, MvPowerSeries.AchievesGaussNorm v (fun _ ↦ c) f i ∧
    MvPowerSeries.AchievesGaussNorm v (fun _ ↦ c) g j ∧∀ p ∈ Finset.antidiagonal (i + j),
    p ≠ (i, j) → v ((MvPowerSeries.coeff p.1) f * (MvPowerSeries.coeff p.2) g) <
    v ((MvPowerSeries.coeff i) f) * v ((MvPowerSeries.coeff j) g)) := by
  constructor
  · intro hdom
    obtain ⟨i, j, hi, hj, hdom'⟩ := hdom
    refine ⟨Finsupp.single () i, Finsupp.single () j, hi, hj,
      ?_⟩
    intro p hp _
    have hp1 : p.1 = Finsupp.single () (p.1 ()) := by grind
    have hp2 : p.2 = Finsupp.single () (p.2 ()) := by grind
    rw [hp1, hp2]
    exact hdom' (p.1 (), p.2 ()) (Finset.mem_antidiagonal.mpr
      (by simpa using congrArg (· ()) (Finset.mem_antidiagonal.mp hp))) (by grind)
  · intro hdom
    obtain ⟨i, j, hi, hj, hdom'⟩ := hdom
    refine ⟨i PUnit.unit, j PUnit.unit, by simpa [achievesGaussNorm,
      show (Finsupp.single () (i PUnit.unit)) = i by grind],
      by simpa [achievesGaussNorm, show (Finsupp.single () (j PUnit.unit)) = j by grind], ?_⟩
    intro p hp _
    simpa [coeff, show (Finsupp.single () (i PUnit.unit)) = i by grind, show (Finsupp.single ()
      (j PUnit.unit)) = j by grind] using hdom' (Finsupp.single () p.1, (Finsupp.single () p.2))
      (Finset.mem_antidiagonal.mpr (by aesop)) (by grind)

lemma gaussNorm_le_mul (f g : PowerSeries R)
    (vMulEq : ∀ a b, v (a * b) = v a * v b) (vUltra : ∀ a b, v (a + b) ≤ max (v a) (v b))
    (vNeg : ∀ a, v a = v (-a)) (hbfg : HasGaussNorm v c (f * g))
    (hdom : ∃ i j, achievesGaussNorm v c f i ∧ achievesGaussNorm v c g j ∧
      ∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
        v (coeff p.1 f * coeff p.2 g) < v (coeff i f) * v (coeff j g)) :
    gaussNorm v c f * gaussNorm v c g ≤ gaussNorm v c (f * g) :=
  MvPowerSeries.gaussNorm_le_mul v (fun _ ↦ c) f g vMulEq vUltra vNeg hbfg
    ((exists_antidiagDom_iff_exists_mvAntidiagDom v c f g).mp hdom)

lemma gaussNorm_mul_eq_mul (f g : PowerSeries R)
    (hf : HasGaussNorm v c f) (hg : HasGaussNorm v c g) (hfg : HasGaussNorm v c (f * g))
    (vNonneg : ∀ a, v a ≥ 0) (vZero : v 0 = 0) (vNA : IsNonarchimedean v)
    (vMulEq : ∀ (a b : R), v (a * b) = v a * v b) (vNeg : ∀ (a : R), v (-a) = v a)
    (h_eq_zero : ∀ (x : R), v x = 0 → x = 0) (hc :  0 < c)
    (hdom : ∃ i j, achievesGaussNorm v c f i ∧ achievesGaussNorm v c g j ∧
      ∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) → v (coeff p.1 f * coeff p.2 g) <
      v (coeff i f) * v (coeff j g)) :
    gaussNorm v c (f * g) = gaussNorm v c f * gaussNorm v c g :=
  MvPowerSeries.gaussNorm_mul_eq_mul v (fun _ ↦ c) f g hf hg
    hfg vNonneg vZero vNA vMulEq vNeg h_eq_zero (by grind)
    ((exists_antidiagDom_iff_exists_mvAntidiagDom v c f g).mp hdom)

end absoluteValue

end PowerSeries
