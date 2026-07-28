import PhD.PR'd.MvGaussNorm

import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.WithAbs

namespace MvPowerSeries

variable {R σ : Type*} (v : R → ℝ) (c : σ → ℝ)

lemma gaussNorm_neg [Ring R] (vNeg : ∀ x, v (-x) = v x) (f : MvPowerSeries σ R) :
    gaussNorm v c (-f) = gaussNorm v c f  := by
  simp_rw [gaussNorm]
  have (t : σ →₀ ℕ) : (coeff t) (-f) = - (coeff t) (f) := by rfl
  simp_rw [this, vNeg]

lemma gaussNorm_mul_eq_mul [Ring R] [DecidableEq σ] (f g : MvPowerSeries σ R)
    (hf : HasGaussNorm v c f) (hg : HasGaussNorm v c g) (hfg : HasGaussNorm v c (f * g))
    (vNonneg : ∀ a, v a ≥ 0) (vZero : v 0 = 0) (vNA : IsNonarchimedean v)
    (vMulEq : ∀ (a b : R), v (a * b) = v a * v b) (vNeg : ∀ (a : R), v (-a) = v a)
    (h_eq_zero : ∀ (x : R), v x = 0 → x = 0) (hc : ∀ (i : σ), 0 < c i)
    (hdom : ∃ i j, AchievesGaussNorm v c f i ∧ AchievesGaussNorm v c g j ∧
      ∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) → v (coeff p.1 f * coeff p.2 g) <
      v (coeff i f) * v (coeff j g)) :
    gaussNorm v c (f * g) = gaussNorm v c f * gaussNorm v c g := by
  by_cases hf' : f = 0
  · simp [hf', gaussNorm_zero v c vZero]
  by_cases hg' : g = 0
  · simp [hg', gaussNorm_zero v c vZero]
  have hf1 : gaussNorm v c f ≠ 0 := by
    convert gaussNorm_eq_zero_iff v c f vZero vNonneg h_eq_zero hc hf
    grind
  have hg1 : gaussNorm v c g ≠ 0 := by
    convert gaussNorm_eq_zero_iff v c g vZero vNonneg h_eq_zero hc hg
    grind
  apply ge_antisymm_iff.mpr
  constructor
  · exact gaussNorm_le_mul v c f g vMulEq vNA (by grind) hfg hdom
  · exact gaussNorm_mul_le v c f g (StrongLT.le hc) vNonneg (by grind) vNA vZero hf hg

end MvPowerSeries
