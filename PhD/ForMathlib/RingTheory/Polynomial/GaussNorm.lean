/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero, William Coram
-/
import Mathlib.Algebra.MvPolynomial.Equiv
import PhD.ForMathlib.RingTheory.MvPolynomial.GaussNorm
import PhD.ForMathlib.RingTheory.PowerSeries.GaussNorm

/-!
# Gauss norm for polynomials

This file is a local replacement of `Mathlib/RingTheory/Polynomial/GaussNorm.lean` with the
`FunLike` hypotheses replaced by a plain function `v : R → ℝ` and explicit hypotheses, matching
the conventions of `MvPowerSeries.gaussNorm`.

**Never import `Mathlib.RingTheory.Polynomial.GaussNorm` (or the files importing it:
`Mathlib.Analysis.Polynomial.Norm`, `Mathlib.Analysis.Polynomial.MahlerMeasure`,
`Mathlib.RingTheory.DedekindDomain.GaussLemma`) together with this file**: the declarations
here reuse the mathlib names.

Given a polynomial `p` in `R[X]`, a function `v : R → ℝ` and a real number `c`, the Gauss norm
is the maximum of `v (p.coeff i) * c ^ i` over the support of `p`.  As in the multivariate
polynomial file, everything beyond the finite computations is a specialisation of the
(multivariate) power series API through the bridge `gaussNorm_coe_powerSeries`; the attainment
hypotheses of `MvPowerSeries.exists_achievesGaussNorm_dominant` are discharged using that
polynomials have finite support.  This keeps the results at full `Semiring`/`Ring` generality
(no commutativity is needed).

## Main definitions and results

* `Polynomial.gaussNorm`: the maximum of `v (p.coeff i) * c ^ i` over the support of `p`.
* `Polynomial.AchievesGaussNorm`: the Gauss norm is achieved at a given index; it is achieved
  (`exists_achievesGaussNorm`), at finitely many indices when nonzero
  (`finite_setOfPred_achievesGaussNorm`), and `achievesGaussNorm_iff_coe` identifies it with the
  power series predicate.
* `Polynomial.gaussNorm_C`, `gaussNorm_monomial`, `gaussNorm_X`, `gaussNorm_one`: explicit
  values of the Gauss norm.
* `Polynomial.gaussNorm_coe_powerSeries`: the Gauss norm of a polynomial is equal to its Gauss
  norm as a power series.
* `Polynomial.exists_min_eq_gaussNorm`: there is a minimal index at which the Gauss norm is
  attained.
* `Polynomial.isNonarchimedean_gaussNorm`: the Gauss norm is nonarchimedean when `v` is.
* `Polynomial.gaussNorm_mul`: the Gauss norm is multiplicative when `v` is a nonarchimedean
  absolute value.
* `Polynomial.gaussNorm_isAbsoluteValue`: the Gauss norm is an absolute value when `v` is a
  nonarchimedean absolute value.
* `Polynomial.gaussNorm_uniqueAlgEquiv`: the Gauss norm of a multivariate polynomial in a
  single variable agrees with the Gauss norm of the corresponding univariate polynomial.
-/

namespace Polynomial

section Semiring

variable {R : Type*} [Semiring R] (v : R → ℝ) (c : ℝ) (p : R[X])

/-- Given a polynomial `p` in `R[X]`, a function `v : R → ℝ` and a real number `c`, the Gauss
norm is the maximum of `v (p.coeff i) * c ^ i` over the support of `p`. -/
noncomputable def gaussNorm : ℝ :=
  if h : p.support.Nonempty then p.support.sup' h fun i ↦ v (p.coeff i) * c ^ i else 0

@[simp]
lemma gaussNorm_zero : gaussNorm v c 0 = 0 := by simp [gaussNorm]

lemma exists_eq_gaussNorm (vZero : v 0 = 0) :
    ∃ i, p.gaussNorm v c = v (p.coeff i) * c ^ i := by
  by_cases h : p.support.Nonempty
  · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' h fun i ↦ v (p.coeff i) * c ^ i
    exact ⟨i, by rwa [gaussNorm, dif_pos h]⟩
  · refine ⟨0, ?_⟩
    rw [Finset.not_nonempty_iff_eq_empty, support_eq_empty] at h
    simp [h, gaussNorm, vZero]

lemma gaussNorm_monomial (vZero : v 0 = 0) (n : ℕ) (r : R) :
    (monomial n r).gaussNorm v c = v r * c ^ n := by
  classical
  rcases eq_or_ne r 0 with rfl | hr <;> simp [gaussNorm, support_monomial, *]

lemma gaussNorm_C (vZero : v 0 = 0) (r : R) : (C r).gaussNorm v c = v r := by
  simpa using gaussNorm_monomial v c vZero 0 r

lemma gaussNorm_one (vZero : v 0 = 0) : (1 : R[X]).gaussNorm v c = v 1 := by
  simpa using gaussNorm_C v c vZero 1

lemma gaussNorm_X (vZero : v 0 = 0) : (X : R[X]).gaussNorm v c = v 1 * c := by
  rw [← monomial_one_one_eq_X]
  simpa using gaussNorm_monomial v c vZero 1 1

variable {c} in
lemma gaussNorm_nonneg (vNonneg : ∀ a, 0 ≤ v a) (hc : 0 ≤ c) : 0 ≤ p.gaussNorm v c := by
  by_cases h : p.support.Nonempty
  · rw [gaussNorm, dif_pos h]
    obtain ⟨i, hi⟩ := h
    exact Finset.le_sup'_of_le _ hi <| mul_nonneg (vNonneg _) (pow_nonneg hc i)
  · rw [gaussNorm, dif_neg h]

/-- Predicate for when the Gauss norm is achieved by an index. -/
abbrev AchievesGaussNorm (i : ℕ) : Prop :=
  v (p.coeff i) * c ^ i = p.gaussNorm v c

/-- The Gauss norm of a polynomial is achieved by some index. -/
lemma exists_achievesGaussNorm (vZero : v 0 = 0) : ∃ i, p.AchievesGaussNorm v c i :=
  (p.exists_eq_gaussNorm v c vZero).imp fun _ hi ↦ hi.symm

/-- A polynomial with nonzero Gauss norm has only finitely many indices achieving the Gauss
norm. -/
lemma finite_setOfPred_achievesGaussNorm (vZero : v 0 = 0) (h0 : p.gaussNorm v c ≠ 0) :
    {i | p.AchievesGaussNorm v c i}.Finite :=
  p.support.finite_toSet.subset fun i hi ↦ Finset.mem_coe.mpr <| mem_support_iff.mpr fun h ↦
    h0 <| by rw [← hi, h, vZero, zero_mul]

/-- A polynomial, coerced to a power series, has a finite Gauss norm. -/
lemma hasGaussNorm_toPowerSeries (vZero : v 0 = 0) :
    PowerSeries.HasGaussNorm v c (p : PowerSeries R) :=
  PowerSeries.hasGaussNorm_of_finite_support v c vZero <| p.support.finite_toSet.subset
    fun n hn ↦ by simpa [mem_support_iff, coeff_coe] using Function.mem_support.mp hn

/-- The Gauss norm of a polynomial is equal to its Gauss norm as a power series. -/
theorem gaussNorm_coe_powerSeries (vZero : v 0 = 0) (vNonneg : ∀ a, 0 ≤ v a) (hc : 0 ≤ c) :
    (p : PowerSeries R).gaussNorm v c = p.gaussNorm v c := by
  rcases eq_or_ne p 0 with rfl | hp
  · rw [coe_zero, gaussNorm_zero, PowerSeries.gaussNorm_zero v c vZero]
  · have hne : p.support.Nonempty := support_nonempty.mpr hp
    rw [PowerSeries.gaussNorm_eq]
    refine le_antisymm (ciSup_le fun n ↦ ?_) ?_
    · rw [coeff_coe]
      by_cases hn : n ∈ p.support
      · rw [gaussNorm, dif_pos hne]
        exact Finset.le_sup' (fun i ↦ v (p.coeff i) * c ^ i) hn
      · rw [notMem_support_iff.mp hn, vZero, zero_mul]
        exact p.gaussNorm_nonneg v vNonneg hc
    · obtain ⟨i, hi⟩ := p.exists_eq_gaussNorm v c vZero
      rw [hi, ← coeff_coe]
      exact le_ciSup (p.hasGaussNorm_toPowerSeries v c vZero) i

variable {c} in
lemma le_gaussNorm (vZero : v 0 = 0) (vNonneg : ∀ a, 0 ≤ v a) (hc : 0 ≤ c) (i : ℕ) :
    v (p.coeff i) * c ^ i ≤ p.gaussNorm v c := by
  rw [← p.gaussNorm_coe_powerSeries v c vZero vNonneg hc, ← coeff_coe]
  exact PowerSeries.le_gaussNorm v c _ (p.hasGaussNorm_toPowerSeries v c vZero) i

/-- For the zero radius, the Gauss norm is the value of `v` on the constant coefficient. -/
lemma gaussNorm_zero_right (vZero : v 0 = 0) (vNonneg : ∀ a, 0 ≤ v a) :
    p.gaussNorm v 0 = v (p.coeff 0) := by
  rw [← p.gaussNorm_coe_powerSeries v 0 vZero vNonneg le_rfl,
    PowerSeries.gaussNorm_zero_right v vNonneg, coeff_coe]

/-- For positive radii, the Gauss norm of a polynomial is zero iff the polynomial is zero. -/
theorem gaussNorm_eq_zero_iff (vZero : v 0 = 0) (vNonneg : ∀ a, 0 ≤ v a)
    (h_eq_zero : ∀ x : R, v x = 0 → x = 0) (hc : 0 < c) :
    p.gaussNorm v c = 0 ↔ p = 0 := by
  rw [← p.gaussNorm_coe_powerSeries v c vZero vNonneg hc.le,
    PowerSeries.gaussNorm_eq_zero_iff v c _ vZero vNonneg h_eq_zero hc
      (p.hasGaussNorm_toPowerSeries v c vZero)]
  exact coe_eq_zero_iff

variable {c} in
/-- There is a minimal index at which the Gauss norm of `p` is attained. -/
lemma exists_min_eq_gaussNorm (vZero : v 0 = 0) (vNonneg : ∀ a, 0 ≤ v a) (hc : 0 ≤ c) :
    ∃ i, p.gaussNorm v c = v (p.coeff i) * c ^ i ∧
      ∀ j, j < i → v (p.coeff j) * c ^ j < p.gaussNorm v c := by
  have h_nonempty := p.exists_eq_gaussNorm v c vZero
  refine ⟨Nat.find h_nonempty, Nat.find_spec h_nonempty, fun j hj_lt ↦ ?_⟩
  simp only [Nat.lt_find_iff] at hj_lt
  exact lt_of_le_of_ne (p.le_gaussNorm v vZero vNonneg hc j) fun a ↦ hj_lt j le_rfl a.symm

variable {c} in
/-- If `v` is a nonnegative nonarchimedean function with `v 0 = 0` and `c` is nonnegative, the
Gauss norm is nonarchimedean. -/
theorem isNonarchimedean_gaussNorm (vZero : v 0 = 0) (vNonneg : ∀ a, 0 ≤ v a)
    (hna : IsNonarchimedean v) (hc : 0 ≤ c) :
    IsNonarchimedean fun p : R[X] ↦ p.gaussNorm v c := by
  intro p q
  have h := PowerSeries.gaussNorm_add_le_max v c (p : PowerSeries R) q hc vNonneg hna
    (p.hasGaussNorm_toPowerSeries v c vZero) (q.hasGaussNorm_toPowerSeries v c vZero)
  rwa [← coe_add, gaussNorm_coe_powerSeries v c _ vZero vNonneg hc,
    gaussNorm_coe_powerSeries v c _ vZero vNonneg hc,
    gaussNorm_coe_powerSeries v c _ vZero vNonneg hc] at h

variable {c} in
/-- If `v` is a nonnegative nonarchimedean submultiplicative function with `v 0 = 0` and `c` is
nonnegative, then the Gauss norm is submultiplicative. -/
theorem gaussNorm_mul_le (vZero : v 0 = 0) (vNonneg : ∀ a, 0 ≤ v a)
    (vMul : ∀ a b, v (a * b) ≤ v a * v b) (hna : IsNonarchimedean v) (hc : 0 ≤ c)
    (p q : R[X]) : (p * q).gaussNorm v c ≤ p.gaussNorm v c * q.gaussNorm v c := by
  rw [← gaussNorm_coe_powerSeries v c _ vZero vNonneg hc,
    ← gaussNorm_coe_powerSeries v c _ vZero vNonneg hc,
    ← gaussNorm_coe_powerSeries v c _ vZero vNonneg hc, coe_mul]
  exact MvPowerSeries.gaussNorm_mul_le v (fun _ ↦ c) (p : PowerSeries R) q (fun _ ↦ hc) vNonneg
    vMul hna vZero (p.hasGaussNorm_toPowerSeries v c vZero).hasMvGaussNorm
    (q.hasGaussNorm_toPowerSeries v c vZero).hasMvGaussNorm

end Semiring

section Ring

variable {R : Type*} [Ring R] (v : R → ℝ) (c : ℝ) (p : R[X])

lemma gaussNorm_neg (vNeg : ∀ a, v (-a) = v a) : (-p).gaussNorm v c = p.gaussNorm v c := by
  by_cases hs : p.support.Nonempty
  · have hs' : (-p).support.Nonempty := by rwa [support_neg]
    rw [gaussNorm, gaussNorm, dif_pos hs, dif_pos hs']
    exact Finset.sup'_congr hs' support_neg fun i _ ↦ by rw [coeff_neg, vNeg]
  · have hs' : ¬(-p).support.Nonempty := by rwa [support_neg]
    rw [gaussNorm, gaussNorm, dif_neg hs, dif_neg hs']

/-- A polynomial achieves its Gauss norm at an index iff the associated power series does. -/
lemma achievesGaussNorm_iff_coe (vZero : v 0 = 0) (vNonneg : ∀ a, 0 ≤ v a) (hc : 0 ≤ c)
    (i : ℕ) : p.AchievesGaussNorm v c i ↔
      PowerSeries.AchievesGaussNorm v c (p : PowerSeries R) i := by
  unfold AchievesGaussNorm PowerSeries.AchievesGaussNorm
  rw [coeff_coe, p.gaussNorm_coe_powerSeries v c vZero vNonneg hc]

private lemma exists_achievesGaussNorm_dominant_aux (vZero : v 0 = 0) (vNonneg : ∀ a, 0 ≤ v a)
    (vMul : ∀ a b, v (a * b) ≤ v a * v b) (hc : 0 ≤ c) (p q : R[X])
    (hp0 : p.gaussNorm v c ≠ 0) (hq0 : q.gaussNorm v c ≠ 0) :
    ∃ i j, MvPowerSeries.AchievesGaussNorm v (fun _ ↦ c) (p : PowerSeries R) i ∧
      MvPowerSeries.AchievesGaussNorm v (fun _ ↦ c) (q : PowerSeries R) j ∧
      ∀ r ∈ Finset.antidiagonal (i + j), r ≠ (i, j) →
        v (MvPowerSeries.coeff r.1 (p : PowerSeries R) *
            MvPowerSeries.coeff r.2 (q : PowerSeries R)) <
          v (MvPowerSeries.coeff i (p : PowerSeries R)) *
            v (MvPowerSeries.coeff j (q : PowerSeries R)) := by
  have key : ∀ r : R[X], r.gaussNorm v c ≠ 0 →
      (∃ a, MvPowerSeries.AchievesGaussNorm v (fun _ ↦ c) (r : PowerSeries R) a) ∧
      {a | MvPowerSeries.AchievesGaussNorm v (fun _ ↦ c) (r : PowerSeries R) a}.Finite := by
    intro r hr0
    refine ⟨?_, ?_⟩
    · obtain ⟨n, hn⟩ := r.exists_achievesGaussNorm v c vZero
      exact ⟨Finsupp.single () n, (PowerSeries.achievesGaussNorm_iff_single v c _ n).mp
        ((r.achievesGaussNorm_iff_coe v c vZero vNonneg hc n).mp hn)⟩
    · refine ((r.finite_setOfPred_achievesGaussNorm v c vZero hr0).image
        (Finsupp.single ())).subset fun a ha ↦ ?_
      obtain ⟨n, rfl⟩ : ∃ n, a = Finsupp.single () n := ⟨a (), Finsupp.unique_single a⟩
      exact ⟨n, (r.achievesGaussNorm_iff_coe v c vZero vNonneg hc n).mpr
        ((PowerSeries.achievesGaussNorm_iff_single v c _ n).mpr ha), rfl⟩
  have hp0' : PowerSeries.gaussNorm v c (p : PowerSeries R) ≠ 0 := by
    rwa [p.gaussNorm_coe_powerSeries v c vZero vNonneg hc]
  have hq0' : PowerSeries.gaussNorm v c (q : PowerSeries R) ≠ 0 := by
    rwa [q.gaussNorm_coe_powerSeries v c vZero vNonneg hc]
  obtain ⟨i, j, hi, hj, hdom, -⟩ :=
    MvPowerSeries.exists_achievesGaussNorm_dominant v (fun _ ↦ c) vNonneg vMul (fun _ ↦ hc)
      (p.hasGaussNorm_toPowerSeries v c vZero).hasMvGaussNorm
      (q.hasGaussNorm_toPowerSeries v c vZero).hasMvGaussNorm
      (key p hp0).2 (key q hq0).2 (key p hp0).1 (key q hq0).1 hp0' hq0'
  exact ⟨i, j, hi, hj, hdom⟩

/-- If `p` and `q` have nonzero Gauss norm, there are indices `i`, `j` achieving the Gauss norms
of `p` and `q` such that the term of `p * q` at `(i, j)` strictly dominates all other terms on
the antidiagonal of `i + j`. -/
lemma exists_achievesGaussNorm_dominant (vZero : v 0 = 0) (vNonneg : ∀ a, 0 ≤ v a)
    (vMul : ∀ a b, v (a * b) ≤ v a * v b) (hc : 0 ≤ c) (p q : R[X])
    (hp0 : p.gaussNorm v c ≠ 0) (hq0 : q.gaussNorm v c ≠ 0) :
    ∃ i j, p.AchievesGaussNorm v c i ∧ q.AchievesGaussNorm v c j ∧
      ∀ r ∈ Finset.antidiagonal (i + j), r ≠ (i, j) →
        v (p.coeff r.1 * q.coeff r.2) < v (p.coeff i) * v (q.coeff j) := by
  obtain ⟨i, j, hi, hj, hdom⟩ :=
    exists_achievesGaussNorm_dominant_aux v c vZero vNonneg vMul hc p q hp0 hq0
  obtain ⟨n, rfl⟩ : ∃ n, i = Finsupp.single () n := ⟨i (), Finsupp.unique_single i⟩
  obtain ⟨m, rfl⟩ : ∃ m, j = Finsupp.single () m := ⟨j (), Finsupp.unique_single j⟩
  refine ⟨n, m, (p.achievesGaussNorm_iff_coe v c vZero vNonneg hc n).mpr
    ((PowerSeries.achievesGaussNorm_iff_single v c _ n).mpr hi),
    (q.achievesGaussNorm_iff_coe v c vZero vNonneg hc m).mpr
      ((PowerSeries.achievesGaussNorm_iff_single v c _ m).mpr hj), fun r hr hrne ↦ ?_⟩
  have h := hdom (Finsupp.single () r.1, Finsupp.single () r.2)
    (by rw [Finset.mem_antidiagonal, ← Finsupp.single_add, ← Finsupp.single_add,
      Finset.mem_antidiagonal.mp hr])
    fun h ↦ hrne (Prod.ext (Finsupp.single_injective () (congrArg Prod.fst h))
      (Finsupp.single_injective () (congrArg Prod.snd h)))
  simpa only [PowerSeries.coeff_coeToMvPowerSeries, coeff_coe] using h

/-- If `v` is a nonarchimedean absolute value, then the Gauss norm is multiplicative. -/
theorem gaussNorm_mul (vZero : v 0 = 0) (vNonneg : ∀ a, 0 ≤ v a) (hna : IsNonarchimedean v)
    (vMulEq : ∀ a b, v (a * b) = v a * v b) (vNeg : ∀ a, v (-a) = v a)
    (h_eq_zero : ∀ x : R, v x = 0 → x = 0) (hc : 0 < c) (p q : R[X]) :
    (p * q).gaussNorm v c = p.gaussNorm v c * q.gaussNorm v c := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have hp0 : p.gaussNorm v c ≠ 0 := fun h ↦
    hp ((gaussNorm_eq_zero_iff v c p vZero vNonneg h_eq_zero hc).mp h)
  have hq0 : q.gaussNorm v c ≠ 0 := fun h ↦
    hq ((gaussNorm_eq_zero_iff v c q vZero vNonneg h_eq_zero hc).mp h)
  rw [← gaussNorm_coe_powerSeries v c _ vZero vNonneg hc.le,
    ← gaussNorm_coe_powerSeries v c _ vZero vNonneg hc.le,
    ← gaussNorm_coe_powerSeries v c _ vZero vNonneg hc.le, coe_mul]
  exact MvPowerSeries.gaussNorm_mul_eq_mul v (fun _ ↦ c) _ _
    (p.hasGaussNorm_toPowerSeries v c vZero).hasMvGaussNorm
    (q.hasGaussNorm_toPowerSeries v c vZero).hasMvGaussNorm
    (by rw [← coe_mul]; exact ((p * q).hasGaussNorm_toPowerSeries v c vZero).hasMvGaussNorm)
    vNonneg vZero hna vMulEq vNeg h_eq_zero (fun _ ↦ hc)
    (exists_achievesGaussNorm_dominant_aux v c vZero vNonneg (fun a b ↦ (vMulEq a b).le) hc.le
      p q hp0 hq0)

/-- If `v` is a nonarchimedean absolute value, then the Gauss norm is an absolute value. -/
theorem gaussNorm_isAbsoluteValue (vZero : v 0 = 0) (vNonneg : ∀ a, 0 ≤ v a)
    (hna : IsNonarchimedean v) (vMulEq : ∀ a b, v (a * b) = v a * v b)
    (vNeg : ∀ a, v (-a) = v a) (h_eq_zero : ∀ x : R, v x = 0 → x = 0) (hc : 0 < c) :
    IsAbsoluteValue fun p : R[X] ↦ p.gaussNorm v c where
  abv_nonneg' p := p.gaussNorm_nonneg v vNonneg hc.le
  abv_eq_zero' {p} := gaussNorm_eq_zero_iff v c p vZero vNonneg h_eq_zero hc
  abv_add' p q :=
    (isNonarchimedean_gaussNorm v vZero vNonneg hna hc.le p q).trans <|
      max_le_add_of_nonneg (p.gaussNorm_nonneg v vNonneg hc.le)
        (q.gaussNorm_nonneg v vNonneg hc.le)
  abv_mul' p q := gaussNorm_mul v c vZero vNonneg hna vMulEq vNeg h_eq_zero hc p q

end Ring

section UniqueAlgEquiv

variable {R σ : Type*} [CommSemiring R] [Unique σ] (v : R → ℝ) (c : ℝ)

/-- The Gauss norm of a multivariate polynomial in a single variable agrees with the Gauss norm
of the corresponding univariate polynomial. -/
theorem gaussNorm_uniqueAlgEquiv (P : MvPolynomial σ R) :
    (MvPolynomial.uniqueAlgEquiv R σ P).gaussNorm v c = P.gaussNorm v fun _ ↦ c := by
  have hcoeff (d : σ →₀ ℕ) :
      (MvPolynomial.uniqueAlgEquiv R σ P).coeff (d default) = MvPolynomial.coeff d P := by
    rw [MvPolynomial.coeff_uniqueAlgEquiv, ← Finsupp.unique_single d]
  have hprod (d : σ →₀ ℕ) : (d.prod fun _ n ↦ c ^ n) = c ^ (d default) := by
    conv_lhs => rw [Finsupp.unique_single d]
    rw [Finsupp.prod_single_index (h := fun _ n ↦ c ^ n) (pow_zero c)]
  by_cases h : P.support.Nonempty
  · have h' : (MvPolynomial.uniqueAlgEquiv R σ P).support.Nonempty := by
      obtain ⟨d, hd⟩ := h
      exact ⟨d default, mem_support_iff.mpr
        (by rw [hcoeff]; exact MvPolynomial.mem_support_iff.mp hd)⟩
    rw [gaussNorm, dif_pos h', MvPolynomial.gaussNorm, dif_pos h]
    refine le_antisymm (Finset.sup'_le _ _ fun n hn ↦ ?_) (Finset.sup'_le _ _ fun d hd ↦ ?_)
    · have hn' : Finsupp.single default n ∈ P.support := by
        rw [MvPolynomial.mem_support_iff, ← MvPolynomial.coeff_uniqueAlgEquiv]
        exact mem_support_iff.mp hn
      refine Finset.le_sup'_of_le _ hn' (le_of_eq ?_)
      rw [MvPolynomial.coeff_uniqueAlgEquiv, hprod (Finsupp.single default n),
        Finsupp.single_eq_same]
    · have hd' : d default ∈ (MvPolynomial.uniqueAlgEquiv R σ P).support :=
        mem_support_iff.mpr (by rw [hcoeff]; exact MvPolynomial.mem_support_iff.mp hd)
      refine Finset.le_sup'_of_le _ hd' (le_of_eq ?_)
      rw [hcoeff, hprod]
  · have h' : ¬(MvPolynomial.uniqueAlgEquiv R σ P).support.Nonempty := fun ⟨n, hn⟩ ↦ h
      ⟨Finsupp.single default n, by
        rw [MvPolynomial.mem_support_iff, ← MvPolynomial.coeff_uniqueAlgEquiv]
        exact mem_support_iff.mp hn⟩
    rw [gaussNorm, dif_neg h', MvPolynomial.gaussNorm, dif_neg h]

end UniqueAlgEquiv

end Polynomial
