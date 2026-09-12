/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.ForMathlib.RingTheory.MvPowerSeries.Restricted.GaussNorm

/-!
# Completeness of restricted multivariate power series

If `R` is a complete normed ring with ultrametric norm and `c : σ → ℝ` is a strictly positive
tuple of radii (recorded as `[Fact (∀ i, 0 < c i)]`), then `MvPowerSeries.Restricted R c` is
complete with respect to the Gauss norm.

The proof takes coefficient-wise limits of a Cauchy sequence (using completeness of `R`),
shows the candidate limit is restricted via the triangle inequality, and upgrades the
coefficient-wise convergence to convergence in the Gauss norm.
-/

namespace MvPowerSeries.Restricted

open Filter
open scoped Topology

variable {R σ : Type*} (c : σ → ℝ) [NormedRing R] [IsUltrametricDist R]
  [hc : Fact (∀ i, 0 < c i)]

private lemma prod_pow_pos (t : σ →₀ ℕ) : 0 < t.prod (c · ^ ·) :=
  Finset.prod_pos fun i _ ↦ pow_pos (hc.out i) _

lemma norm_coeff_sub_mul_prod_le (f g : Restricted R c) (t : σ →₀ ℕ) :
    ‖coeff t f.1 - coeff t g.1‖ * t.prod (c · ^ ·) ≤ ‖f - g‖ :=
  le_gaussNorm norm c (f - g).1 (hasGaussNorm c (f - g)) t

/-
Compelteness is proved in the following steps:
· Let u be a cauchy sequence of restricted power series, then for a given index the sequence of
  coefficients is also a cauchy sequence
· If we take the powerseries with coefficients the limits, then this is restricted
  and the original sequence tends to this

This is developed in more generality ... see ha assumption in eventually_norm_coeff_sub_le
and the later lemmas h
The application is just choosing a as stated above and show we have the conditions
-/


lemma cauchySeq_coeff {u : ℕ → Restricted R c} (hu : CauchySeq u) (t : σ →₀ ℕ) :
    CauchySeq fun i ↦ coeff t (u i).1 := by
  refine Metric.cauchySeq_iff.mpr fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (ε * t.prod (c · ^ ·))
    (mul_pos hε (prod_pow_pos c t))
  simp only [dist_eq_norm] at hN ⊢
  exact ⟨N, fun i hi j hj ↦ lt_of_mul_lt_mul_right
    ((norm_coeff_sub_mul_prod_le c (u i) (u j) t).trans_lt (hN i hi j hj)) (prod_pow_pos c t).le⟩

lemma eventually_norm_coeff_sub_le {u : ℕ → Restricted R c} (hu : CauchySeq u)
    {a : MvPowerSeries σ R} (ha : ∀ t, Tendsto (fun i ↦ coeff t (u i).1) atTop (𝓝 (coeff t a)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ t, ‖coeff t (u i).1 - coeff t a‖ * t.prod (c · ^ ·) ≤ ε := by
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
  simp only [dist_eq_norm] at hN
  filter_upwards [eventually_ge_atTop N] with i hi t
  refine le_of_tendsto (((ha t).const_sub _).norm.mul_const _) ?_
  filter_upwards [eventually_ge_atTop N] with j hj
  exact ((norm_coeff_sub_mul_prod_le c (u i) (u j) t).trans_lt (hN i hi j hj)).le

lemma isRestricted_of_eventually_norm_coeff_sub_le {u : ℕ → Restricted R c}
    {a : MvPowerSeries σ R}
    (h : ∀ ε, 0 < ε → ∀ᶠ i in atTop, ∀ t, ‖coeff t (u i).1 - coeff t a‖ * t.prod (c · ^ ·) ≤ ε) :
    IsRestricted c a := by
  refine tendsto_order.mpr ⟨fun b hb ↦ .of_forall
    fun t ↦ hb.trans_le (mul_nonneg (norm_nonneg _) (prod_pow_pos c t).le), fun ε hε ↦ ?_⟩
  obtain ⟨i, hi⟩ := (h (ε / 2) (half_pos hε)).exists
  filter_upwards [Filter.Tendsto.eventually_lt_const (half_pos hε) (u i).2] with t ht
  linarith [hi t, mul_le_mul_of_nonneg_right
    (norm_le_norm_add_norm_sub (coeff t (u i).1) (coeff t a)) (prod_pow_pos c t).le]

lemma tendsto_of_eventually_norm_coeff_sub_le {u : ℕ → Restricted R c} {F : Restricted R c}
    (h : ∀ ε, 0 < ε → ∀ᶠ i in atTop, ∀ t, ‖coeff t (u i).1 - coeff t F.1‖ * t.prod (c · ^ ·) ≤ ε) :
    Tendsto u atTop (𝓝 F) := by
  refine Metric.nhds_basis_closedBall.tendsto_right_iff.mpr fun ε hε ↦ ?_
  filter_upwards [h ε hε] with i hi
  rw [Metric.mem_closedBall, dist_eq_norm, norm_def]
  exact ciSup_le hi

variable [CompleteSpace R]

instance : CompleteSpace (Restricted R c) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  choose a ha using fun t ↦ cauchySeq_tendsto_of_complete (cauchySeq_coeff c hu t)
  have h_unif := eventually_norm_coeff_sub_le c hu (a := (a : MvPowerSeries σ R)) ha
  refine ⟨⟨a, isRestricted_of_eventually_norm_coeff_sub_le c h_unif⟩, ?_⟩
  exact tendsto_of_eventually_norm_coeff_sub_le c h_unif

end MvPowerSeries.Restricted
