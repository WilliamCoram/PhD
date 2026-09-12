/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.ForMathlib.RingTheory.MvPowerSeries.GaussNorm

/-!
# The lex-maximal dominant pair of achieving indices

`MvPowerSeries.exists_achievesGaussNorm_dominant` produces a dominant pair of achieving indices
without reference to any order on `σ`, since that is all its consumers (multiplicativity of the
Gauss norm, the unit criterion) need.  Its proof does pick the achieving indices that are
maximal for the lex order of an arbitrary well-order on `σ`, and the Gauss-extension route to
Weierstrass division needs that maximality exposed: for `σ = Unit` it identifies the dominant
index of a distinguished series with its distinguished degree.

This file records the maximality-exposing form.  It is deliberately kept out of
`PhD/Main/ForMathlib/`, which carries only the order-free statement; the proof below is therefore a
duplicate of the one there, up to keeping `hi_max` and `hj_max` instead of using them.

## Main results

* `MvPowerSeries.exists_achievesGaussNorm_dominant_lexMax`: the dominant pair of
  `MvPowerSeries.exists_achievesGaussNorm_dominant` for a given linear order on `σ`, with the
  lex-maximality of the two indices among the achieving indices exposed.
-/

namespace MvPowerSeries

section Ring

variable {R σ : Type*} [Ring R] (v : R → ℝ) (c : σ → ℝ)

/-- If the Gauss norms of `f` and `g` are nonzero and are achieved by (nonempty) finite sets of
indices, then for any linear order on `σ` the *lex-maximal* achieving indices `i`, `j` give a
term of `f * g` at `(i, j)` strictly dominating all other terms on the antidiagonal of `i + j`.
The last two conjuncts expose the lex-maximality of the pair; for an order-free index type see
`exists_achievesGaussNorm_dominant`. -/
lemma exists_achievesGaussNorm_dominant_lexMax [LinearOrder σ] [DecidableEq σ]
    (vNonneg : ∀ a, v a ≥ 0)
    (vMul : ∀ a b, v (a * b) ≤ v a * v b) (hc : 0 ≤ c) {f g : MvPowerSeries σ R}
    (hbf : HasGaussNorm v c f) (hbg : HasGaussNorm v c g)
    (hf_fin : {a | AchievesGaussNorm v c f a}.Finite)
    (hg_fin : {a | AchievesGaussNorm v c g a}.Finite)
    (hf_ex : ∃ a, AchievesGaussNorm v c f a) (hg_ex : ∃ a, AchievesGaussNorm v c g a)
    (hf0 : gaussNorm v c f ≠ 0) (hg0 : gaussNorm v c g ≠ 0) :
    ∃ i j, AchievesGaussNorm v c f i ∧ AchievesGaussNorm v c g j ∧
      (∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
        v (coeff p.1 f * coeff p.2 g) < v (coeff i f) * v (coeff j g)) ∧
      (∀ t, AchievesGaussNorm v c f t → toLex t ≤ toLex i) ∧
      ∀ t, AchievesGaussNorm v c g t → toLex t ≤ toLex j := by
  have hpow_nonneg (t : σ →₀ ℕ) : 0 ≤ t.prod (c · ^ ·) :=
    Finset.prod_nonneg fun i _ ↦ pow_nonneg (hc i) (t i)
  obtain ⟨i, hi : AchievesGaussNorm v c f i, hi_max⟩ := Set.exists_max_image _ toLex hf_fin hf_ex
  obtain ⟨j, hj : AchievesGaussNorm v c g j, hj_max⟩ := Set.exists_max_image _ toLex hg_fin hg_ex
  refine ⟨i, j, hi, hj, fun p hp hpne ↦ ?_, hi_max, hj_max⟩
  have hsump : p.1 + p.2 = i + j := Finset.mem_antidiagonal.1 hp
  have hle1 : v (coeff p.1 f) * p.1.prod (c · ^ ·) ≤ v (coeff i f) * i.prod (c · ^ ·) :=
    (le_gaussNorm v c f hbf p.1).trans_eq hi.symm
  have hle2 : v (coeff p.2 g) * p.2.prod (c · ^ ·) ≤ v (coeff j g) * j.prod (c · ^ ·) :=
    (le_gaussNorm v c g hbg p.2).trans_eq hj.symm
  have hi_pos : 0 < v (coeff i f) * i.prod (c · ^ ·) :=
    ((gaussNorm_nonneg v c f vNonneg).lt_of_ne' hf0).trans_eq hi.symm
  have hj_pos : 0 < v (coeff j g) * j.prod (c · ^ ·) :=
    ((gaussNorm_nonneg v c g vNonneg).lt_of_ne' hg0).trans_eq hj.symm
  have hmul_strict :
      (v (coeff p.1 f) * p.1.prod (c · ^ ·)) * (v (coeff p.2 g) * p.2.prod (c · ^ ·)) <
      (v (coeff i f) * i.prod (c · ^ ·)) * (v (coeff j g) * j.prod (c · ^ ·)) := by
    rcases hle1.lt_or_eq with h1 | h1eq
    · exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos h1 hle2
        (mul_nonneg (vNonneg _) (hpow_nonneg p.1)) hj_pos
    rcases hle2.lt_or_eq with h2 | h2eq
    · exact mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hle1 h2
        (mul_nonneg (vNonneg _) (hpow_nonneg p.2)) hi_pos
    obtain ⟨h1, h2⟩ := (add_eq_add_iff_eq_and_eq (hi_max p.1 (h1eq.trans hi))
      (hj_max p.2 (h2eq.trans hj))).mp (congrArg toLex hsump)
    exact absurd (Prod.ext (toLex_inj.mp h1) (toLex_inj.mp h2)) hpne
  have hprod : p.1.prod (c · ^ ·) * p.2.prod (c · ^ ·) = i.prod (c · ^ ·) * j.prod (c · ^ ·) := by
    simp [← Finsupp.prod_add_index' (h := (c · ^ ·)) (fun _ ↦ pow_zero _)
      (fun _ _ _ ↦ pow_add _ _ _), hsump]
  rw [mul_mul_mul_comm, mul_mul_mul_comm (v (coeff i f)), hprod] at hmul_strict
  exact (vMul _ _).trans_lt
    (lt_of_mul_lt_mul_right hmul_strict (mul_nonneg (hpow_nonneg i) (hpow_nonneg j)))

end Ring

end MvPowerSeries
