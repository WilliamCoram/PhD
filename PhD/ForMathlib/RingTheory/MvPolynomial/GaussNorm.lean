/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import PhD.ForMathlib.RingTheory.MvPowerSeries.GaussNorm

/-!
# Gauss norm for multivariate polynomials

This file defines the Gauss norm for multivariate polynomials.  Given a polynomial `p` in
`MvPolynomial σ R`, a function `v : R → ℝ` and a tuple `c : σ → ℝ` of real numbers, the Gauss
norm is the maximum of `v (coeff t p) * t.prod (c · ^ ·)` over the support of `p`.

This is the finite (polynomial) counterpart of `MvPowerSeries.gaussNorm`, and the two agree on
polynomials (`MvPolynomial.gaussNorm_coe`).  Everything beyond the finite computations is a
specialisation of the multivariate power series API through this bridge: the attainment
hypotheses of the master lemmas in `PhD/ForMathlib/RingTheory/MvPowerSeries/GaussNorm.lean` are
discharged using that polynomials have finite support.

## Main definitions

* `MvPolynomial.gaussNorm`: the Gauss norm of a multivariate polynomial, defined as the maximum
  of `v (coeff t p) * t.prod (c · ^ ·)` over the support of `p`.
* `MvPolynomial.AchievesGaussNorm`: the Gauss norm is achieved at a given index; it is achieved
  (`exists_achievesGaussNorm`), at finitely many indices when nonzero
  (`finite_setOfPred_achievesGaussNorm`), and `achievesGaussNorm_iff_coe` identifies it with the
  power series predicate.

## Main results

* `MvPolynomial.gaussNorm_monomial`, `MvPolynomial.gaussNorm_C`, `MvPolynomial.gaussNorm_X`:
  explicit values of the Gauss norm on monomials, constants and variables.
* `MvPolynomial.gaussNorm_coe`: the Gauss norm of a coerced polynomial is
  `MvPolynomial.gaussNorm`, reducing power-series Gauss norms of polynomials to finite
  computations.
* `MvPolynomial.gaussNorm_eq_zero_iff`: for positive radii the Gauss norm vanishes only at `0`.
* `MvPolynomial.isNonarchimedean_gaussNorm`: the Gauss norm is nonarchimedean when `v` is.
* `MvPolynomial.gaussNorm_mul`: the Gauss norm is multiplicative when `v` is a nonarchimedean
  absolute value.
* `MvPolynomial.gaussNorm_isAbsoluteValue`: the Gauss norm is an absolute value when `v` is a
  nonarchimedean absolute value.

There is no multivariate analogue of `Polynomial.exists_min_eq_gaussNorm`: minimal achieving
indices need the order on `ℕ`.  Its role in the proof of multiplicativity is played by
lex-maximal achieving indices (`MvPowerSeries.exists_achievesGaussNorm_dominant`).
-/

namespace MvPolynomial

variable {R σ : Type*} [CommSemiring R] (v : R → ℝ) (c : σ → ℝ) (p : MvPolynomial σ R)

/-- Given a multivariate polynomial `p`, a function `v : R → ℝ` and a tuple `c` of real numbers,
the Gauss norm is the maximum of `v (coeff t p) * t.prod (c · ^ ·)` over the support of `p`. -/
noncomputable def gaussNorm : ℝ :=
  if h : p.support.Nonempty then p.support.sup' h fun t ↦ v (coeff t p) * t.prod (c · ^ ·) else 0

@[simp]
lemma gaussNorm_zero : gaussNorm v c 0 = 0 := by simp [gaussNorm]

lemma exists_eq_gaussNorm (vZero : v 0 = 0) :
    ∃ t, p.gaussNorm v c = v (coeff t p) * t.prod (c · ^ ·) := by
  by_cases h : p.support.Nonempty
  · obtain ⟨t, _, ht⟩ := Finset.exists_mem_eq_sup' h fun t ↦ v (coeff t p) * t.prod (c · ^ ·)
    exact ⟨t, by rwa [gaussNorm, dif_pos h]⟩
  · refine ⟨0, ?_⟩
    rw [Finset.not_nonempty_iff_eq_empty, support_eq_empty] at h
    simp [h, gaussNorm, vZero]

lemma gaussNorm_monomial (vZero : v 0 = 0) (t : σ →₀ ℕ) (r : R) :
    (monomial t r).gaussNorm v c = v r * t.prod (c · ^ ·) := by
  classical
  rcases eq_or_ne r 0 with rfl | hr <;> simp [gaussNorm, support_monomial, *]

lemma gaussNorm_C (vZero : v 0 = 0) (r : R) : (C r).gaussNorm v c = v r := by
  simpa using gaussNorm_monomial v c vZero 0 r

lemma gaussNorm_one (vZero : v 0 = 0) : (1 : MvPolynomial σ R).gaussNorm v c = v 1 := by
  simpa using gaussNorm_C v c vZero 1

lemma gaussNorm_X (vZero : v 0 = 0) (s : σ) : (X s).gaussNorm v c = v 1 * c s := by
  rw [X]
  simpa using gaussNorm_monomial v c vZero (Finsupp.single s 1) 1

variable {c} in
lemma gaussNorm_nonneg (vNonneg : ∀ a, v a ≥ 0) (hc : 0 ≤ c) : 0 ≤ p.gaussNorm v c := by
  by_cases h : p.support.Nonempty
  · rw [gaussNorm, dif_pos h]
    obtain ⟨t, ht⟩ := h
    exact Finset.le_sup'_of_le _ ht <| mul_nonneg (vNonneg _) <|
      Finset.prod_nonneg fun i _ ↦ pow_nonneg (hc i) (t i)
  · rw [gaussNorm, dif_neg h]

/-- Predicate for when the Gauss norm is achieved by an index. -/
abbrev AchievesGaussNorm (i : σ →₀ ℕ) : Prop :=
  v (coeff i p) * i.prod (c · ^ ·) = p.gaussNorm v c

/-- The Gauss norm of a polynomial is achieved by some index. -/
lemma exists_achievesGaussNorm (vZero : v 0 = 0) : ∃ a, p.AchievesGaussNorm v c a :=
  (p.exists_eq_gaussNorm v c vZero).imp fun _ ht ↦ ht.symm

/-- A polynomial with nonzero Gauss norm has only finitely many indices achieving the Gauss
norm. -/
lemma finite_setOfPred_achievesGaussNorm (vZero : v 0 = 0) (h0 : p.gaussNorm v c ≠ 0) :
    {a | p.AchievesGaussNorm v c a}.Finite :=
  p.support.finite_toSet.subset fun a ha ↦ Finset.mem_coe.mpr <| mem_support_iff.mpr fun h ↦
    h0 <| by rw [← ha, h, vZero, zero_mul]

/-! ### The bridge to multivariate power series -/

/-- A multivariate polynomial, coerced to a power series, has a finite Gauss norm. -/
lemma hasGaussNorm_toMvPowerSeries (vZero : v 0 = 0) :
    MvPowerSeries.HasGaussNorm v c (p : MvPowerSeries σ R) :=
  MvPowerSeries.hasGaussNorm_of_finite_support v c vZero <| p.support.finite_toSet.subset
    fun t ht ↦ by simpa [mem_support_iff, coeff_coe] using Function.mem_support.mp ht

/-- The Gauss norm of a multivariate polynomial, coerced to a power series, is its Gauss norm as
a polynomial. -/
lemma gaussNorm_coe (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0) (hc : 0 ≤ c) :
    MvPowerSeries.gaussNorm v c (p : MvPowerSeries σ R) = p.gaussNorm v c := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [vZero]
  · have hne : p.support.Nonempty := support_nonempty.mpr hp
    refine le_antisymm (ciSup_le fun t ↦ ?_) ?_
    · rw [coeff_coe]
      by_cases ht : t ∈ p.support
      · rw [gaussNorm, dif_pos hne]
        exact Finset.le_sup' (fun t ↦ v (coeff t p) * t.prod (c · ^ ·)) ht
      · rw [notMem_support_iff.mp ht, vZero, zero_mul]
        exact p.gaussNorm_nonneg v vNonneg hc
    · obtain ⟨t, ht⟩ := p.exists_eq_gaussNorm v c vZero
      rw [ht, ← coeff_coe]
      exact MvPowerSeries.le_gaussNorm v c _ (p.hasGaussNorm_toMvPowerSeries v c vZero) t

variable {c} in
lemma le_gaussNorm (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0) (hc : 0 ≤ c) (t : σ →₀ ℕ) :
    v (coeff t p) * t.prod (c · ^ ·) ≤ p.gaussNorm v c := by
  rw [← p.gaussNorm_coe v c vZero vNonneg hc, ← coeff_coe]
  exact MvPowerSeries.le_gaussNorm v c _ (p.hasGaussNorm_toMvPowerSeries v c vZero) t

/-- For the zero radius tuple, the Gauss norm is the value of `v` on the constant
coefficient. -/
lemma gaussNorm_zero_right (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0) :
    p.gaussNorm v 0 = v (coeff 0 p) := by
  rw [← p.gaussNorm_coe v 0 vZero vNonneg le_rfl,
    MvPowerSeries.gaussNorm_zero_right v vNonneg, coeff_coe]

/-- For positive radii, the Gauss norm of a polynomial is zero iff the polynomial is zero. -/
lemma gaussNorm_eq_zero_iff (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0)
    (h_eq_zero : ∀ x : R, v x = 0 → x = 0) (hc : ∀ i, 0 < c i) :
    p.gaussNorm v c = 0 ↔ p = 0 := by
  rw [← p.gaussNorm_coe v c vZero vNonneg fun i ↦ (hc i).le,
    MvPowerSeries.gaussNorm_eq_zero_iff v c _ vZero vNonneg h_eq_zero hc
      (p.hasGaussNorm_toMvPowerSeries v c vZero)]
  exact coe_eq_zero_iff

variable {c} in
/-- If `v` is a nonnegative nonarchimedean function with `v 0 = 0` and `c` is nonnegative, the
Gauss norm is nonarchimedean. -/
theorem isNonarchimedean_gaussNorm (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0)
    (hna : IsNonarchimedean v) (hc : 0 ≤ c) :
    IsNonarchimedean fun p : MvPolynomial σ R ↦ p.gaussNorm v c := by
  intro p q
  have h := MvPowerSeries.gaussNorm_add_le_max v c (p : MvPowerSeries σ R) q hc vNonneg hna
    (p.hasGaussNorm_toMvPowerSeries v c vZero) (q.hasGaussNorm_toMvPowerSeries v c vZero)
  rwa [← coe_add, gaussNorm_coe v c _ vZero vNonneg hc, gaussNorm_coe v c _ vZero vNonneg hc,
    gaussNorm_coe v c _ vZero vNonneg hc] at h

variable {c} in
/-- If `v` is a nonnegative nonarchimedean submultiplicative function with `v 0 = 0` and `c` is
nonnegative, then the Gauss norm is submultiplicative. -/
theorem gaussNorm_mul_le (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0)
    (vMul : ∀ a b, v (a * b) ≤ v a * v b) (hna : IsNonarchimedean v) (hc : 0 ≤ c)
    (p q : MvPolynomial σ R) :
    (p * q).gaussNorm v c ≤ p.gaussNorm v c * q.gaussNorm v c := by
  have h := MvPowerSeries.gaussNorm_mul_le v c (p : MvPowerSeries σ R) q hc vNonneg vMul hna
    vZero (p.hasGaussNorm_toMvPowerSeries v c vZero) (q.hasGaussNorm_toMvPowerSeries v c vZero)
  rwa [← coe_mul, gaussNorm_coe v c _ vZero vNonneg hc, gaussNorm_coe v c _ vZero vNonneg hc,
    gaussNorm_coe v c _ vZero vNonneg hc] at h

end MvPolynomial

/-! ### Multiplicativity

Multiplicativity of the Gauss norm is inherited from `MvPowerSeries.gaussNorm_mul_eq_mul`; the
attainment hypotheses of `MvPowerSeries.exists_achievesGaussNorm_dominant` are discharged using
that a polynomial has finite support. -/

namespace MvPolynomial

variable {R σ : Type*} [CommRing R] (v : R → ℝ) (c : σ → ℝ) (p : MvPolynomial σ R)

lemma gaussNorm_neg (vNeg : ∀ a, v (-a) = v a) : (-p).gaussNorm v c = p.gaussNorm v c := by
  by_cases hs : p.support.Nonempty
  · have hs' : (-p).support.Nonempty := by rwa [support_neg]
    rw [gaussNorm, gaussNorm, dif_pos hs, dif_pos hs']
    exact Finset.sup'_congr hs' (support_neg σ) fun t _ ↦ by rw [coeff_neg, vNeg]
  · have hs' : ¬(-p).support.Nonempty := by rwa [support_neg]
    rw [gaussNorm, gaussNorm, dif_neg hs, dif_neg hs']

/-- A polynomial achieves its Gauss norm at an index iff the associated power series does. -/
lemma achievesGaussNorm_iff_coe (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0) (hc : 0 ≤ c)
    (i : σ →₀ ℕ) : p.AchievesGaussNorm v c i ↔
      MvPowerSeries.AchievesGaussNorm v c (p : MvPowerSeries σ R) i := by
  unfold AchievesGaussNorm MvPowerSeries.AchievesGaussNorm
  rw [coeff_coe, p.gaussNorm_coe v c vZero vNonneg hc]

/-- If `p` and `q` have nonzero Gauss norm, there are indices `i`, `j` achieving the Gauss norms
of `p` and `q` such that the term of `p * q` at `(i, j)` strictly dominates all other terms on
the antidiagonal of `i + j`. -/
lemma exists_achievesGaussNorm_dominant [DecidableEq σ] (vZero : v 0 = 0)
    (vNonneg : ∀ a, v a ≥ 0) (vMul : ∀ a b, v (a * b) ≤ v a * v b) (hc : 0 ≤ c)
    (p q : MvPolynomial σ R) (hp0 : p.gaussNorm v c ≠ 0) (hq0 : q.gaussNorm v c ≠ 0) :
    ∃ i j, p.AchievesGaussNorm v c i ∧ q.AchievesGaussNorm v c j ∧
      ∀ r ∈ Finset.antidiagonal (i + j), r ≠ (i, j) →
        v (coeff r.1 p * coeff r.2 q) < v (coeff i p) * v (coeff j q) := by
  have hp0' : MvPowerSeries.gaussNorm v c (p : MvPowerSeries σ R) ≠ 0 := by
    rw [p.gaussNorm_coe v c vZero vNonneg hc]; exact hp0
  have hq0' : MvPowerSeries.gaussNorm v c (q : MvPowerSeries σ R) ≠ 0 := by
    rw [q.gaussNorm_coe v c vZero vNonneg hc]; exact hq0
  obtain ⟨i, j, hi, hj, hdom, -⟩ := MvPowerSeries.exists_achievesGaussNorm_dominant v c vNonneg
    vMul hc (p.hasGaussNorm_toMvPowerSeries v c vZero) (q.hasGaussNorm_toMvPowerSeries v c vZero)
    ((p.finite_setOfPred_achievesGaussNorm v c vZero hp0).subset fun a ha ↦
      (p.achievesGaussNorm_iff_coe v c vZero vNonneg hc a).mpr ha)
    ((q.finite_setOfPred_achievesGaussNorm v c vZero hq0).subset fun a ha ↦
      (q.achievesGaussNorm_iff_coe v c vZero vNonneg hc a).mpr ha)
    ((p.exists_achievesGaussNorm v c vZero).imp fun a ha ↦
      (p.achievesGaussNorm_iff_coe v c vZero vNonneg hc a).mp ha)
    ((q.exists_achievesGaussNorm v c vZero).imp fun a ha ↦
      (q.achievesGaussNorm_iff_coe v c vZero vNonneg hc a).mp ha) hp0' hq0'
  refine ⟨i, j, (p.achievesGaussNorm_iff_coe v c vZero vNonneg hc i).mpr hi,
    (q.achievesGaussNorm_iff_coe v c vZero vNonneg hc j).mpr hj, fun r hr hrne ↦ ?_⟩
  simpa only [coeff_coe] using hdom r hr hrne

/-- If `v` is a nonarchimedean absolute value, then the Gauss norm is multiplicative. -/
theorem gaussNorm_mul (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0) (hna : IsNonarchimedean v)
    (vMulEq : ∀ a b, v (a * b) = v a * v b) (vNeg : ∀ a, v (-a) = v a)
    (h_eq_zero : ∀ x : R, v x = 0 → x = 0) (hc : ∀ i, 0 < c i) (p q : MvPolynomial σ R) :
    (p * q).gaussNorm v c = p.gaussNorm v c * q.gaussNorm v c := by
  classical
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have hc' : 0 ≤ c := fun i ↦ (hc i).le
  have hp0 : p.gaussNorm v c ≠ 0 := fun h ↦
    hp ((gaussNorm_eq_zero_iff v c p vZero vNonneg h_eq_zero hc).mp h)
  have hq0 : q.gaussNorm v c ≠ 0 := fun h ↦
    hq ((gaussNorm_eq_zero_iff v c q vZero vNonneg h_eq_zero hc).mp h)
  obtain ⟨i, j, hi, hj, hdom⟩ := exists_achievesGaussNorm_dominant v c vZero vNonneg
    (fun a b ↦ (vMulEq a b).le) hc' p q hp0 hq0
  rw [← gaussNorm_coe v c _ vZero vNonneg hc', ← gaussNorm_coe v c _ vZero vNonneg hc',
    ← gaussNorm_coe v c _ vZero vNonneg hc', coe_mul]
  exact MvPowerSeries.gaussNorm_mul_eq_mul v c _ _ (p.hasGaussNorm_toMvPowerSeries v c vZero)
    (q.hasGaussNorm_toMvPowerSeries v c vZero)
    (by rw [← coe_mul]; exact (p * q).hasGaussNorm_toMvPowerSeries v c vZero)
    vNonneg vZero hna vMulEq vNeg h_eq_zero hc
    ⟨i, j, (p.achievesGaussNorm_iff_coe v c vZero vNonneg hc' i).mp hi,
      (q.achievesGaussNorm_iff_coe v c vZero vNonneg hc' j).mp hj,
      fun r hr hrne ↦ by simpa only [coeff_coe] using hdom r hr hrne⟩

/-- If `v` is a nonarchimedean absolute value, then the Gauss norm is an absolute value. -/
theorem gaussNorm_isAbsoluteValue (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0)
    (hna : IsNonarchimedean v) (vMulEq : ∀ a b, v (a * b) = v a * v b)
    (vNeg : ∀ a, v (-a) = v a) (h_eq_zero : ∀ x : R, v x = 0 → x = 0) (hc : ∀ i, 0 < c i) :
    IsAbsoluteValue fun p : MvPolynomial σ R ↦ p.gaussNorm v c where
  abv_nonneg' p := p.gaussNorm_nonneg v vNonneg fun i ↦ (hc i).le
  abv_eq_zero' {p} := gaussNorm_eq_zero_iff v c p vZero vNonneg h_eq_zero hc
  abv_add' p q :=
    (isNonarchimedean_gaussNorm v vZero vNonneg hna (fun i ↦ (hc i).le) p q).trans <|
      max_le_add_of_nonneg (p.gaussNorm_nonneg v vNonneg fun i ↦ (hc i).le)
        (q.gaussNorm_nonneg v vNonneg fun i ↦ (hc i).le)
  abv_mul' p q := gaussNorm_mul v c vZero vNonneg hna vMulEq vNeg h_eq_zero hc p q

end MvPolynomial
