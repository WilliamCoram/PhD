/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Data.Finsupp.Lex
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.RingTheory.MvPowerSeries.GaussNorm

/-!
# Explicit computations of the Gauss norm on multivariate power series

This file computes the Gauss norm of monomials, constants and variables in `MvPowerSeries σ R`,
and provides the master lemmas from which the polynomial and restricted power series theories
specialise:

* `MvPowerSeries.hasGaussNorm_of_finite_support`: a power series with finitely many nonzero
  coefficients has a (finite) Gauss norm.
* `MvPowerSeries.gaussNorm_zero_right`: for the zero radius tuple the Gauss norm is the value on
  the constant coefficient.
* `MvPowerSeries.exists_achievesGaussNorm_dominant`: for series whose Gauss norms are nonzero and
  achieved by finitely many indices, the achieving indices that are maximal for the lex order of
  an arbitrary well-order on `σ` give a strictly dominant term on the antidiagonal.  This
  discharges the `hdom` hypothesis of
  `MvPowerSeries.gaussNorm_mul_eq_mul`; both `MvPolynomial` (finite support) and
  `MvPowerSeries.Restricted` (restrictedness) discharge its attainment hypotheses.

The corresponding results for multivariate polynomials are in
`PhD/Main/ForMathlib/RingTheory/MvPolynomial/GaussNorm.lean`.
-/

namespace MvPowerSeries

section Semiring

variable {R σ : Type*} [Semiring R] (v : R → ℝ) (c : σ → ℝ)

/-- A power series with finitely many nonzero coefficients has a finite Gauss norm. -/
lemma hasGaussNorm_of_finite_support (vZero : v 0 = 0) {f : MvPowerSeries σ R}
    (hf : (Function.support fun t ↦ coeff t f).Finite) : HasGaussNorm v c f := by
  refine ((hf.image fun t ↦ v (coeff t f) * t.prod (c · ^ ·)).union
    (Set.finite_singleton 0)).bddAbove.mono ?_
  rintro x ⟨t, rfl⟩
  by_cases ht : coeff t f = 0
  · exact Or.inr (by simp [ht, vZero])
  · exact Or.inl ⟨t, Function.mem_support.mpr ht, rfl⟩

/-- A monomial has a finite Gauss norm. -/
lemma hasGaussNorm_monomial (vZero : v 0 = 0) (t : σ →₀ ℕ) (r : R) :
    HasGaussNorm v c (monomial t r) :=
  hasGaussNorm_of_finite_support v c vZero <| (Set.finite_singleton t).subset fun s hs ↦ by
    by_contra h
    exact Function.mem_support.mp hs (coeff_monomial_ne h r)

/-- The Gauss norm of a monomial, for a general weight `t.prod (c · ^ ·)` known to be
nonnegative.  See `gaussNorm_monomial` for the version with nonnegative radii. -/
lemma gaussNorm_monomial_of_nonneg (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0) (t : σ →₀ ℕ)
    (r : R) (hprod : 0 ≤ t.prod (c · ^ ·)) :
    gaussNorm v c (monomial t r) = v r * t.prod (c · ^ ·) := by
  refine le_antisymm (ciSup_le fun s ↦ ?_) ?_
  · rcases eq_or_ne s t with rfl | hs
    · rw [coeff_monomial_same]
    · rw [coeff_monomial_ne hs, vZero, zero_mul]
      exact mul_nonneg (vNonneg r) hprod
  · simpa [coeff_monomial_same] using
      le_gaussNorm v c (monomial t r) (hasGaussNorm_monomial v c vZero t r) t

/-- The Gauss norm of a monomial. -/
lemma gaussNorm_monomial (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0) (hc : 0 ≤ c) (t : σ →₀ ℕ)
    (r : R) : gaussNorm v c (monomial t r) = v r * t.prod (c · ^ ·) :=
  gaussNorm_monomial_of_nonneg v c vZero vNonneg t r <|
    Finset.prod_nonneg fun i _ ↦ pow_nonneg (hc i) (t i)

/-- The Gauss norm of a constant. -/
lemma gaussNorm_C (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0) (r : R) :
    gaussNorm v c (C r) = v r := by
  simpa using gaussNorm_monomial_of_nonneg v c vZero vNonneg 0 r (by simp)

/-- The Gauss norm of `1` is `v 1`. -/
lemma gaussNorm_one (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0) :
    gaussNorm v c 1 = v 1 := by
  simpa using gaussNorm_C v c vZero vNonneg 1

/-- The Gauss norm of the variable `X s` is `v 1 * c s`. -/
lemma gaussNorm_X (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0) (s : σ) (hc : 0 ≤ c s) :
    gaussNorm v c (X s) = v 1 * c s := by
  rw [X_def]
  simpa using gaussNorm_monomial_of_nonneg v c vZero vNonneg (Finsupp.single s 1) 1 (by simpa)

/-- For the zero radius tuple, the Gauss norm is the value of `v` on the constant
coefficient. -/
lemma gaussNorm_zero_right (vNonneg : ∀ a, v a ≥ 0) (f : MvPowerSeries σ R) :
    gaussNorm v 0 f = v (coeff 0 f) := by
  classical
  have hprod (t : σ →₀ ℕ) : t.prod ((0 : σ → ℝ) · ^ ·) = if t = 0 then 1 else 0 := by
    split_ifs with h
    · simp [h]
    · obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp h
      have hi' : t i ≠ 0 := by simpa using hi
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hi') (by simp [zero_pow hi'])
  have hbdd : HasGaussNorm v (0 : σ → ℝ) f := by
    refine ((Set.finite_singleton (v (coeff 0 f))).union
      (Set.finite_singleton 0)).bddAbove.mono ?_
    rintro x ⟨t, rfl⟩
    rcases eq_or_ne t 0 with rfl | ht
    · exact Or.inl (by simp only [Set.mem_singleton_iff]; rw [hprod, if_pos rfl, mul_one])
    · exact Or.inr (by simp only [Set.mem_singleton_iff]; rw [hprod, if_neg ht, mul_zero])
  refine le_antisymm (ciSup_le fun t ↦ ?_) ?_
  · rw [hprod]
    rcases eq_or_ne t 0 with rfl | ht
    · rw [if_pos rfl, mul_one]
    · rw [if_neg ht, mul_zero]
      exact vNonneg _
  · simpa using le_gaussNorm v 0 f hbdd 0

/-- The Gauss norm is preserved by coefficientwise base change along a ring hom `φ` that
preserves the value function termwise: if `w (φ a) = v a` for all `a`, then mapping `f` along
`φ` leaves the Gauss norm unchanged. -/
lemma gaussNorm_map {S : Type*} [Semiring S] (w : S → ℝ) (φ : R →+* S)
    (hφ : ∀ a, w (φ a) = v a) (f : MvPowerSeries σ R) :
    gaussNorm w c (map φ f) = gaussNorm v c f := by
  simp only [gaussNorm, coeff_map, hφ]

end Semiring

section Ring

variable {R σ : Type*} [Ring R] (v : R → ℝ) (c : σ → ℝ)

/-- If the Gauss norms of `f` and `g` are nonzero and are achieved by (nonempty) finite sets of
indices, there are indices `i`, `j` achieving the Gauss norms of `f` and `g` such that the term
of `f * g` at `(i, j)` strictly dominates all other terms on the antidiagonal of `i + j`.  This
discharges the `hdom` hypothesis of `MvPowerSeries.gaussNorm_mul_eq_mul`.

The pair `(i, j)` consists of the maximal achieving indices for the lex order attached to an
arbitrary well-order on `σ`; the final conjunct records the consequence of maximality needed for
the unit criterion of restricted power series: if `i + j = 0` then every achieving index of `f`
and of `g` is `0`. -/
lemma exists_achievesGaussNorm_dominant [DecidableEq σ] (vNonneg : ∀ a, v a ≥ 0)
    (vMul : ∀ a b, v (a * b) ≤ v a * v b) (hc : 0 ≤ c) {f g : MvPowerSeries σ R}
    (hbf : HasGaussNorm v c f) (hbg : HasGaussNorm v c g)
    (hf_fin : {a | AchievesGaussNorm v c f a}.Finite)
    (hg_fin : {a | AchievesGaussNorm v c g a}.Finite)
    (hf_ex : ∃ a, AchievesGaussNorm v c f a) (hg_ex : ∃ a, AchievesGaussNorm v c g a)
    (hf0 : gaussNorm v c f ≠ 0) (hg0 : gaussNorm v c g ≠ 0) :
    ∃ i j, AchievesGaussNorm v c f i ∧ AchievesGaussNorm v c g j ∧
      (∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
        v (coeff p.1 f * coeff p.2 g) < v (coeff i f) * v (coeff j g)) ∧
      (i + j = 0 → (∀ t, AchievesGaussNorm v c f t → t = 0) ∧
        ∀ t, AchievesGaussNorm v c g t → t = 0) := by
  -- `σ` carries no order; fix an arbitrary well-order so that lex-maximal indices make sense
  have : LinearOrder σ := IsWellOrder.linearOrder WellOrderingRel
  have hpow_nonneg (t : σ →₀ ℕ) : 0 ≤ t.prod (c · ^ ·) :=
    Finset.prod_nonneg fun i _ ↦ pow_nonneg (hc i) (t i)
  obtain ⟨i, hi : AchievesGaussNorm v c f i, hi_max⟩ := Set.exists_max_image _ toLex hf_fin hf_ex
  obtain ⟨j, hj : AchievesGaussNorm v c g j, hj_max⟩ := Set.exists_max_image _ toLex hg_fin hg_ex
  refine ⟨i, j, hi, hj, fun p hp hpne ↦ ?_, fun hij ↦ ?_⟩
  · -- the lex-maximal pair strictly dominates every other pair on the antidiagonal
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
    have hprod :
        p.1.prod (c · ^ ·) * p.2.prod (c · ^ ·) = i.prod (c · ^ ·) * j.prod (c · ^ ·) := by
      simp [← Finsupp.prod_add_index' (h := (c · ^ ·)) (fun _ ↦ pow_zero _)
        (fun _ _ _ ↦ pow_add _ _ _), hsump]
    rw [mul_mul_mul_comm, mul_mul_mul_comm (v (coeff i f)), hprod] at hmul_strict
    exact (vMul _ _).trans_lt
      (lt_of_mul_lt_mul_right hmul_strict (mul_nonneg (hpow_nonneg i) (hpow_nonneg j)))
  · -- lex-maximality: if the maximal achieving indices sum to zero they are both zero, and then
    -- every achieving index lies below `0` in the lex order, hence equals `0`
    have hi0 : i = 0 := Finsupp.ext fun s ↦
      (Nat.add_eq_zero_iff.mp (by simpa using DFunLike.congr_fun hij s)).1
    have hj0 : j = 0 := Finsupp.ext fun s ↦
      (Nat.add_eq_zero_iff.mp (by simpa using DFunLike.congr_fun hij s)).2
    exact ⟨fun t ht ↦ toLex_inj.mp (le_antisymm (hi0 ▸ hi_max t ht)
        (Finsupp.toLex_monotone ((Finsupp.le_iff _ _).mpr fun s hs ↦ by simp at hs))),
      fun t ht ↦ toLex_inj.mp (le_antisymm (hj0 ▸ hj_max t ht)
        (Finsupp.toLex_monotone ((Finsupp.le_iff _ _).mpr fun s hs ↦ by simp at hs)))⟩

end Ring

end MvPowerSeries
