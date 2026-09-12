/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.ForMathlib.RingTheory.MvPowerSeries.Restricted.Complete
import PhD.Main.ForMathlib.RingTheory.PowerSeries.Restricted.GaussNorm

/-!
# Completeness of restricted univariate power series

Since `PowerSeries.Restricted R c` is by definition
`MvPowerSeries.Restricted R (fun _ : Unit ↦ c)`, the `CompleteSpace` instance is inherited
from the multivariate case via the `Fact` bridge (checked below by an `example`).  This file
restates the coefficient estimates for Cauchy sequences and their limits in `ℕ`-indexed form.
-/

namespace PowerSeries.Restricted

open Filter
open scoped Topology

variable {R : Type*} (c : ℝ) [NormedRing R] [IsUltrametricDist R] [hc : Fact (0 < c)]

lemma norm_coeff_sub_mul_pow_le (f g : Restricted R c) (n : ℕ) :
    ‖coeff n f.1 - coeff n g.1‖ * c ^ n ≤ ‖f - g‖ :=
  le_gaussNorm norm c (f - g).1 (hasGaussNorm c (f - g)) n

lemma cauchySeq_coeff {u : ℕ → Restricted R c} (hu : CauchySeq u) (n : ℕ) :
    CauchySeq fun i ↦ coeff n (u i).1 :=
  MvPowerSeries.Restricted.cauchySeq_coeff (fun _ ↦ c) hu (Finsupp.single () n)

lemma eventually_norm_coeff_sub_le {u : ℕ → Restricted R c} (hu : CauchySeq u) {a : ℕ → R}
    (ha : ∀ n, Tendsto (fun i ↦ coeff n (u i).1) atTop (𝓝 (a n))) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ n, ‖coeff n (u i).1 - a n‖ * c ^ n ≤ ε := by
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
  simp only [dist_eq_norm] at hN
  filter_upwards [eventually_ge_atTop N] with i hi n
  refine le_of_tendsto (((ha n).const_sub _).norm.mul_const _) ?_
  filter_upwards [eventually_ge_atTop N] with j hj
  exact ((norm_coeff_sub_mul_pow_le c (u i) (u j) n).trans_lt (hN i hi j hj)).le

lemma isRestricted_mk {u : ℕ → Restricted R c} {a : ℕ → R}
    (h : ∀ ε, 0 < ε → ∀ᶠ i in atTop, ∀ n, ‖coeff n (u i).1 - a n‖ * c ^ n ≤ ε) :
    IsRestricted c (mk a) := by
  simp only [isRestricted_iff, coeff_mk]
  refine tendsto_order.mpr ⟨fun b hb ↦ .of_forall
    fun n ↦ hb.trans_le (mul_nonneg (norm_nonneg _) (pow_pos hc.out n).le), fun ε hε ↦ ?_⟩
  obtain ⟨i, hi⟩ := (h (ε / 2) (half_pos hε)).exists
  filter_upwards [((isRestricted_iff c (u i).1).mp (u i).2).eventually_lt_const (half_pos hε)]
    with n hn
  linarith [hi n, mul_le_mul_of_nonneg_right (norm_le_norm_add_norm_sub (coeff n (u i).1) (a n))
    (pow_pos hc.out n).le]

lemma tendsto_of_eventually_norm_coeff_sub_le {u : ℕ → Restricted R c} {F : Restricted R c}
    (h : ∀ ε, 0 < ε → ∀ᶠ i in atTop, ∀ n, ‖coeff n (u i).1 - coeff n F.1‖ * c ^ n ≤ ε) :
    Tendsto u atTop (𝓝 F) := by
  refine Metric.nhds_basis_closedBall.tendsto_right_iff.mpr fun ε hε ↦ ?_
  filter_upwards [h ε hε] with i hi
  rw [Metric.mem_closedBall, dist_eq_norm, norm_def, gaussNorm_eq]
  exact ciSup_le hi

variable [CompleteSpace R]

example : CompleteSpace (Restricted R c) := inferInstance

end PowerSeries.Restricted
