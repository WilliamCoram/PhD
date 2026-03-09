/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic

public import PhD.RPS.mathlib

/-!
# Gauss norm for multivariate power series

This file defines the Gauss norm for power series. Given a multivariate power series `f`, a
function `v : R → ℝ` and a tuple `c` of real numbers, the Gauss norm is defined as the supremum of
the set of all values of `v (coeff t f) * ∏ i : t.support, c i` for all `t : σ →₀ ℕ`.

## Main Definitions and Results

* `MvPowerSeries.gaussNormC` is the supremum of the set of all values of
  `v (coeff t f) * ∏ i : t.support, c i`for all `t : σ →₀ ℕ`, where `f` is a multivariate power
  series, `v : R → ℝ` is a function and `c` is a tuple of real numbers.

* `MvPowerSeries.gaussNormC_nonneg`: if `v` is a non-negative function, then the Gauss norm is
  non-negative.

* `MvPowerSeries.gaussNormC_eq_zero_iff`: if `v` is a non-negative function and `v x = 0 ↔ x = 0`
  for all `x : R` and `c` is positive, then the Gauss norm is zero if and only if the power series
  is zero.

* `Mv.gaussNormC_nonarchimedean`: if `v` is a non-negative non-archimedean function and the set of
  values `v (coeff t f) * ∏ i : t.support, c i` is bounded above (similarily for `g`), then the
  Gauss norm is non-archimedean.
-/

@[expose] public section

namespace MvPowerSeries

variable {R σ : Type*} [Semiring R] (v : R → ℝ) (c : σ → ℝ) (f : MvPowerSeries σ R)

/-- Given a multivariate power series `f` in, a function `v : R → ℝ` and a tuple `c` of real
  numbers, the Gauss norm is defined as the supremum of the set of all values of
  `v (coeff t f) * ∏ i : t.support, c i` for all `t : σ →₀ ℕ`. -/
noncomputable def gaussNorm : ℝ :=
   ⨆ t : σ →₀ ℕ, v (coeff t f) * t.prod (c · ^ ·)

/-- We say `f` HasGaussNorm if the values `v (coeff t f) * ∏ i : t.support, c i` is bounded above,
  that is `gaussNormC f` is finite. -/
abbrev HasGaussNorm := BddAbove (Set.range (fun (t : σ →₀ ℕ) ↦ (v (coeff t f) * t.prod (c · ^ ·))))

@[simp]
theorem gaussNorm_zero (vZero : v 0 = 0) : gaussNorm v c 0 = 0 := by simp [gaussNorm, vZero]

lemma le_gaussNorm (hbd : HasGaussNorm v c f) (t : σ →₀ ℕ) :
    v (coeff t f) * t.prod (c · ^ ·) ≤ gaussNorm v c f := by
  apply le_ciSup hbd

theorem gaussNorm_nonneg (vNonneg : ∀ a, v a ≥ 0) : 0 ≤ gaussNorm v c f := by
  rw [gaussNorm]
  by_cases h : HasGaussNorm v c f
  · trans v (constantCoeff f)
    · simp [vNonneg]
    · convert (le_gaussNorm v c f h 0)
      simp
  · simp [h]

theorem gaussNorm_neg [Ring R] (vNeg : ∀ x, v x = v (-x)) :
    gaussNorm v c (-f) = gaussNorm v c f := by
  simp_rw [gaussNorm]
  have (t : σ →₀ ℕ) : (coeff t) (-f) = - (coeff t) (f) := by rfl
  simp_rw [this, ← vNeg]

theorem gaussNorm_eq_zero_iff (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0)
    (h_eq_zero : ∀ x : R, v x = 0 → x = 0) (hc : ∀ i, 0 < c i) (hbd : HasGaussNorm v c f) :
    gaussNorm v c f = 0 ↔ f = 0 := by
  refine ⟨?_, fun hf ↦ by simp [hf, vZero]⟩
  contrapose!
  intro hf
  apply ne_of_gt
  obtain ⟨n, hn⟩ := (MvPowerSeries.ne_zero_iff_exists_coeff_ne_zero f).mp hf
  calc
  0 < v (f.coeff n) * ∏ i ∈ n.support, (c i) ^ (n i) := by
    apply mul_pos _ (by exact Finset.prod_pos fun i a ↦ (fun i ↦ pow_pos (hc i) (n i)) i)
    specialize h_eq_zero (f.coeff n)
    grind
  _ ≤ _ := le_gaussNorm v c f hbd n

theorem gaussNorm_add_le_max (f g : MvPowerSeries σ R) (hc : 0 ≤ c)
    (vNonneg : ∀ a, v a ≥ 0) (hv : ∀ x y, v (x + y) ≤ max (v x) (v y))
    (hbfd : HasGaussNorm v c f) (hbgd : HasGaussNorm v c g) :
    gaussNorm v c (f + g) ≤ max (gaussNorm v c f) (gaussNorm v c g) := by
  have H (t : σ →₀ ℕ) : 0 ≤ ∏ i ∈ t.support, c i ^ t i :=
    Finset.prod_nonneg (fun i hi ↦ pow_nonneg (hc i) (t i))
  have Final (t : σ →₀ ℕ) : v ((coeff t) (f + g)) * ∏ i ∈ t.support, c ↑i ^ t ↑i ≤
      max (v ((coeff t) f) * ∏ i ∈ t.support, c ↑i ^ t ↑i)
      (v ((coeff t) g) * ∏ i ∈ t.support, c ↑i ^ t ↑i) := by
    specialize hv (coeff t f) (coeff t g)
    rcases max_choice (v ((coeff t) f)) (v ((coeff t) g)) with h | h
    · have : max (v ((coeff t) f) * ∏ i ∈ t.support, c ↑i ^ t ↑i)
          (v ((coeff t) g) * ∏ i ∈ t.support, c ↑i ^ t ↑i) =
          (v ((coeff t) f) * ∏ i ∈ t.support, c ↑i ^ t ↑i) := by
        simp only [sup_eq_left]
        exact mul_le_mul_of_nonneg (by aesop) (by aesop) (by aesop) (H t)
      simp_rw [this]
      exact mul_le_mul_of_nonneg (by aesop) (by aesop) (by aesop) (H t)
    · have : max (v ((coeff t) f) * ∏ i ∈ t.support, c ↑i ^ t ↑i)
          (v ((coeff t) g) * ∏ i ∈ t.support, c ↑i ^ t ↑i) =
          (v ((coeff t) g) * ∏ i ∈ t.support, c ↑i ^ t ↑i) := by
        simp only [sup_eq_right]
        exact mul_le_mul_of_nonneg (by aesop) (by aesop) (by aesop) (H t)
      simp_rw [this]
      exact mul_le_mul_of_nonneg (by aesop) (by aesop) (by aesop) (H t)
  refine Real.iSup_le ?_ ?_
  · refine fun t ↦ calc
    _ ≤ _ := Final t
    _ ≤ max (gaussNorm v c f) (gaussNorm v c g) := by
      simp only [le_sup_iff]
      rcases max_choice (v ((coeff t) f) * ∏ i ∈ t.support, c i ^ t i)
        (v ((coeff t) g) * ∏ i ∈ t.support, c i ^ t i) with h | h
      · left
        simpa [h] using le_gaussNorm v c f hbfd t
      · right
        simpa [h] using le_gaussNorm v c g hbgd t
  · simp only [le_sup_iff]
    left
    exact gaussNorm_nonneg v c f vNonneg


-- What I need to do:
-- It is a semi-norm on MvPowerseries (not gaussNorm x = 0 ↔ x = 0) -- would also need to adapt add_le_max
-- It is an absolute value on polynomials
-- It is an absolute value on powerseries

lemma restricted.HasGaussNorm [NormedRing R] [IsUltrametricDist R] (c : σ → ℝ) (f : Restricted R c) :
    HasGaussNorm norm c f.1 := by
  exact Filter.Tendsto.bddAbove_range_of_cofinite f.2

section norm

variable {R σ : Type*} (c : σ → ℝ)

-- it seems like this may not be the best way to do things:
-- I maybe should show they are just seminorms etc
-- then have a seperate thing saying it is nonarchimedean
-- e.g. this is how they do p-adic norm
-- they show it is an absolute value then include the




--prev work using nonarch properties first

noncomputable
instance isNonarchAddGroupSeminorm [NormedRing R] [IsUltrametricDist R] (hc : 0 ≤ c) :
    NonarchAddGroupSeminorm (Restricted R c) where
  toFun f := gaussNorm norm c f.1
  map_zero' := gaussNorm_zero norm c norm_zero
  add_le_max' f g := gaussNorm_add_le_max norm c f.1 g.1 hc norm_nonneg
    IsUltrametricDist.norm_add_le_max (restricted.HasGaussNorm c f) (restricted.HasGaussNorm c g)
  neg' f := gaussNorm_neg norm c f.1 (by aesop)

noncomputable
instance [NormedRing R] [IsUltrametricDist R] (hc : 0 ≤ c) :
    AddGroupSeminorm (Restricted R c) := by
  have := isNonarchAddGroupSeminorm (R := R) c hc

  sorry

noncomputable
instance [NormedRing R] [IsUltrametricDist R] (hc : 0 ≤ c) :
   SeminormedAddGroup (Restricted R c) :=
  AddGroupSeminorm.toSeminormedAddGroup (isNonarchAddGroupSeminorm c hc)

lemma test (hc : ∀ (i : σ), 0 < c i) : 0 ≤ c := by
  intro i
  exact Std.le_of_lt (hc i)

noncomputable
instance [NormedRing R] [IsUltrametricDist R] (hc : ∀ (i : σ), 0 < c i) :
    NonarchAddGroupNorm (Restricted R c) where
  __ := isNonarchAddGroupSeminorm c (test c hc)
  eq_zero_of_map_eq_zero' f := by
    simp_rw [isNonarchAddGroupSeminorm]
    convert (gaussNorm_eq_zero_iff norm c f.1 norm_zero norm_nonneg (by aesop)
      hc (restricted.HasGaussNorm c f)).mp
    aesop

-/

end norm

end MvPowerSeries
