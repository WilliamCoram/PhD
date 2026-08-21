/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.BirkovichWP.RingTheory.MvPowerSeries.GaussNorm
import PhD.ForMathlib.RingTheory.MvPowerSeries.Restricted.GaussNorm

/-!
# The lex-maximal dominant pair for restricted multivariate power series

The restricted-power-series form of
`MvPowerSeries.exists_achievesGaussNorm_dominant_lexMax`, obtained by discharging its
attainment hypotheses with restrictedness exactly as
`MvPowerSeries.IsRestricted.exists_achievesGaussNorm_dominant` does for the order-free version
in `PhD/ForMathlib/`.

## Main results

* `MvPowerSeries.IsRestricted.exists_achievesGaussNorm_dominant_lexMax`: for an ordered index
  type, the dominant pair of achieving indices is the lex-maximal one.
-/

namespace MvPowerSeries

variable {R : Type*} {σ : Type*} [NormedRing R]

namespace IsRestricted

variable {c : σ → ℝ} {f g : MvPowerSeries σ R}

/-- Strengthening of `exists_achievesGaussNorm_dominant` for an ordered index type: the
dominant pair `(i, j)` consists of the lex-maximal achieving indices, and the last two
conjuncts expose this maximality. -/
lemma exists_achievesGaussNorm_dominant_lexMax [LinearOrder σ] [DecidableEq σ] (hc : 0 ≤ c)
    (hf : IsRestricted c f) (hg : IsRestricted c g) (hf0 : gaussNorm norm c f ≠ 0)
    (hg0 : gaussNorm norm c g ≠ 0) :
    ∃ i j, AchievesGaussNorm norm c f i ∧ AchievesGaussNorm norm c g j ∧
      (∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
        ‖coeff p.1 f * coeff p.2 g‖ < ‖coeff i f‖ * ‖coeff j g‖) ∧
      (∀ t, AchievesGaussNorm norm c f t → toLex t ≤ toLex i) ∧
      ∀ t, AchievesGaussNorm norm c g t → toLex t ≤ toLex j :=
  MvPowerSeries.exists_achievesGaussNorm_dominant_lexMax norm c (fun _ ↦ norm_nonneg _)
    norm_mul_le hc hf.hasGaussNorm hg.hasGaussNorm (hf.finite_setOfPred_achievesGaussNorm hf0)
    (hg.finite_setOfPred_achievesGaussNorm hg0) hf.exists_achievesGaussNorm
    hg.exists_achievesGaussNorm hf0 hg0

end IsRestricted

end MvPowerSeries
