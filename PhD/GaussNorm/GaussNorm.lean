/-
 Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: Fabrizio Barroero
 -/
 import Mathlib.Analysis.Normed.Ring.Basic
 import Mathlib.RingTheory.PowerSeries.Order

 /-!
 # Gauss norm for power series
 This file defines the Gauss norm for power series. Given a power series `f` in `R⟦X⟧`, a function
 `v : R → ℝ` and a real number `c`, the Gauss norm is defined as the supremum of the set of all
 values of `v (f.coeff R i) * c ^ i` for all `i : ℕ`.
 ## Main Definitions and Results
 * `PowerSeries.gaussNormC` is the supremum of the set of all values of `v (f.coeff R i) * c ^ i`
   for all `i : ℕ`, where `f` is a power series in `R⟦X⟧`, `v : R → ℝ` is a function and `c` is a
   real number.
 * `PowerSeries.gaussNormC_nonneg`: if `v` is a non-negative function, then the Gauss norm is
   non-negative.
 * `PowerSeries.gaussNormC_eq_zero_iff`: if `v` is a non-negative function and `v x = 0 ↔ x = 0` for
   all `x : R` and `c` is positive, then the Gauss norm is zero if and only if the power series is
   zero.
 -/

 namespace PowerSeries

 variable {R F : Type*} [Semiring R] [FunLike F R ℝ] (v : F) (c : ℝ) (f : R⟦X⟧)

 /-- Given a power series `f` in `R⟦X⟧`, a function `v : R → ℝ` and a real number `c`, the Gauss norm
 is defined as the supremum of the set of all values of `v (f.coeff R i) * c ^ i` for all `i : ℕ`. -/
 noncomputable def gaussNormC : ℝ := sSup {v (f.coeff i) * c ^ i | (i : ℕ)}

 @[simp]
 theorem gaussNormC_zero [ZeroHomClass F R ℝ] : gaussNormC v c 0 = 0 := by simp [gaussNormC]

 private lemma gaussNormC_nonempty : {x | ∃ i, v (f.coeff i) * c ^ i = x}.Nonempty := by
   use v (f.coeff 0) * c ^ 0, 0

 lemma le_gaussNormC (hbd : BddAbove {x | ∃ i, v (f.coeff  i) * c ^ i = x}) (i : ℕ) :
   v (f.coeff i) * c ^ i ≤ f.gaussNormC v c := by
   apply le_csSup hbd
   simp

 theorem gaussNormC_nonneg [NonnegHomClass F R ℝ] : 0 ≤ f.gaussNormC v c := by
   rw [gaussNormC]
   by_cases h : BddAbove {x | ∃ i, v (f.coeff i) * c ^ i = x}
   · rw [Real.le_sSup_iff h <| gaussNormC_nonempty v c f]
     simp only [Set.mem_setOf_eq, zero_add, exists_exists_eq_and]
     intro ε hε
     use 0
     simpa using lt_of_lt_of_le hε <| apply_nonneg v (f.constantCoeff)
   · simp [h]

 @[simp]
 theorem gaussNormC_eq_zero_iff [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ] {v : F}
     (h_eq_zero : ∀ x : R, v x = 0 → x = 0) {f : R⟦X⟧} {c : ℝ} (hc : 0 < c)
     (hbd : BddAbove {x | ∃ i, v (f.coeff i) * c ^ i = x})  :
     f.gaussNormC v c = 0 ↔ f = 0 := by
   refine ⟨?_, fun hf ↦ by simp [hf]⟩
   contrapose!
   intro hf
   apply ne_of_gt
   obtain ⟨n, hn⟩ := exists_coeff_ne_zero_iff_ne_zero.mpr hf
   calc
   0 < v (f.coeff n) * c ^ n := by
     apply mul_pos _ (pow_pos hc _)
     specialize h_eq_zero (f.coeff n)
     simp_all only [ne_eq]
     positivity
   _ ≤ sSup {x | ∃ i, v (f.coeff i) * c ^ i = x} := by
     rw [Real.le_sSup_iff hbd <| gaussNormC_nonempty v c f]
     simp only [Set.mem_setOf_eq, exists_exists_eq_and]
     intro ε hε
     use n
     simp [hε]



--- All the above is what has been put into Mathlib... I want to generalise this to MVPowerSeries
--- Then show it forms a norm (absolute value...?) on restricted power series by the below work

/-
section RestrictedPowerSeries

variable [NormedRing R]

lemma gaussNormC_bddabove: BddAbove {x | ∃ i, v (f.coeff i) * c ^ i = x} := by
  sorry


lemma gaussNormC_existence (hf : IsRestricted R f c) : ∃ j : ℕ,
    gaussNormC v c f = v (f.coeff R j) * c ^ j := by
  sorry



/-- The Gauss norm of the sum of two restricted power series is less than or equal to the maximum
of the Gauss norms of the two series. -/
@[simp]
theorem gaussNormC_nonarchimedean (hf : IsRestricted R f c) (hg : IsRestricted R g c) (hc : 0 < c)
    (hv : ∀ x y, v (x + y) ≤ max (v x) (v y)) : gaussNormC v c (f + g) ≤ max (gaussNormC v c f)
    (gaussNormC v c g) := by
  obtain ⟨i, hi⟩ := gaussNormC_existence v c f hf
  obtain ⟨j, hj⟩ := gaussNormC_existence v c g hg
  obtain ⟨l, hl⟩ := gaussNormC_existence v c (f + g) (PowerSeries.Restricted.add R c hf hg)
  simp_rw [hi, hj, hl]
  have final : v ((coeff R l) f + (coeff R l) g) * c^l ≤ max (v ((coeff R l) f) * c^l)
      (v ((coeff R l) g) * c^l) := by
    simpa only [le_sup_iff, hc, pow_pos, mul_le_mul_right, Rat.cast_le] using (hv (f.coeff R l)
      (g.coeff R l))
  have hf2 (a : ℝ) (ha : a ∈ {x | ∃ i, v (f.coeff R i) * c ^ i = x}) :=
    le_csSup (gaussNormC_bddabove v c f) ha
  simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at hf2
  have hg2 (a : ℝ) (ha : a ∈ {x | ∃ i, v (g.coeff R i) * c ^ i = x}) :=
    le_csSup (gaussNormC_bddabove v c g) ha
  simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at hg2
  have h (a : ℝ) (q : PowerSeries R) (ha : a ∈ {x | ∃ i, v (q.coeff R i) * c ^ i = x}) :=
    le_csSup (gaussNormC_bddabove v c q) ha
  simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at h
  simp_rw [gaussNormC] at hi hj hl
  rw [hi] at hf2
  rw [hj] at hg2
  rw [hl] at hl
  simp only [le_sup_iff] at final ⊢
  rcases final with le1 | le2
  · left
    exact le_trans le1 (hf2 l)
  · right
    exact le_trans le2 (hg2 l)

end RestrictedPowerSeries

-/

end PowerSeries
