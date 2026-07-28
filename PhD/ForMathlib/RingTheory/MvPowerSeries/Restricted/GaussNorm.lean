/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

import PhD.ForMathlib.Analysis.Normed.Ring.Ultra
import PhD.ForMathlib.RingTheory.MvPolynomial.GaussNorm
import PhD.ForMathlib.RingTheory.MvPowerSeries.Restricted.Basic
import PhD.ForMathlib.Topology.Algebra.Nonarchimedean.LinearTopology

/-!
# The Gauss norm on restricted multivariate power series

For a normed ring `R` with ultrametric norm and radii `c : σ → ℝ` that are strictly positive
(recorded as `[Fact (∀ i, 0 < c i)]`), the Gauss norm makes `MvPowerSeries.Restricted R c` a
normed ring with ultrametric norm.  If the norm on `R` is multiplicative, so is the Gauss norm
(`NormMulClass`).

Attainment of the Gauss norm is developed at the level of the `IsRestricted` predicate
(`MvPowerSeries.IsRestricted.exists_achievesGaussNorm` and friends), where it needs neither the
ultrametric hypothesis nor the subring; the subtype versions are corollaries.

The `NormedRing` instance defined here is the canonical source of the norm, metric, uniformity
and topology on `MvPowerSeries.Restricted R c`; further structure should be derived from it,
never constructed independently.

## Main definitions

* `MvPowerSeries.Restricted.gaussNorm`: the Gauss norm on `Restricted R c`, as a bare function.
* `MvPowerSeries.Restricted.gaussNormRingNorm`: the Gauss norm as a bundled `RingNorm`, giving
  the `NormedRing` instance on `Restricted R c`.

## Main results

* `MvPowerSeries.IsRestricted.exists_achievesGaussNorm_dominant`: for restricted power series
  with nonzero Gauss norm there is a dominant pair of achieving indices; this discharges the
  `hdom` hypothesis of `MvPowerSeries.gaussNorm_mul_eq_mul`.
* `MvPowerSeries.Restricted.isNonarchimedean_norm`: the Gauss norm is nonarchimedean, giving
  the `IsUltrametricDist` instance.
* The `NormMulClass` instance: the Gauss norm is multiplicative when the norm on `R` is.
* `MvPowerSeries.Restricted.norm_monomial`, `norm_C`, `norm_X`: explicit values of the norm on
  monomials, constants and variables, and the `NormOneClass` instance.
* `MvPolynomial.norm_toRestricted`: the norm of a polynomial in the restricted power series ring
  is its polynomial Gauss norm `MvPolynomial.gaussNorm`, a finite computation.
-/

namespace MvPowerSeries

variable {R : Type*} {σ : Type*} [NormedRing R]

namespace IsRestricted

variable {c : σ → ℝ} {f g : MvPowerSeries σ R}

/-- A restricted power series has a finite Gauss norm: the terms `‖coeff t f‖ * t.prod (c · ^ ·)`
are bounded above. -/
lemma hasGaussNorm (hf : IsRestricted c f) : HasGaussNorm norm c f :=
  hf.bddAbove_range_of_cofinite

/-- For a restricted power series, only finitely many weighted coefficients exceed any positive
threshold. -/
lemma finite_setOfPred_le_norm_mul_prod (hf : IsRestricted c f) {ε : ℝ} (hε : 0 < ε) :
    {t | ε ≤ ‖coeff t f‖ * t.prod (c · ^ ·)}.Finite :=
  (Filter.eventually_cofinite.mp (hf.eventually_lt_const hε)).subset fun _ ht ↦ not_lt.mpr ht

/-- The Gauss norm of a restricted power series is achieved by some index. -/
lemma exists_achievesGaussNorm (hf : IsRestricted c f) : ∃ a, AchievesGaussNorm norm c f a := by
  by_cases hG : gaussNorm norm c f = 0
  · exact ⟨0, le_antisymm (le_gaussNorm norm c f hf.hasGaussNorm 0)
      (hG.trans_le (mul_nonneg (norm_nonneg _) (by simp)))⟩
  · have hpos : 0 < gaussNorm norm c f := (gaussNorm_nonneg norm c f norm_nonneg).lt_of_ne' hG
    obtain ⟨m, hm, hmax⟩ := Set.exists_max_image _ (fun t ↦ ‖coeff t f‖ * t.prod (c · ^ ·))
      (hf.finite_setOfPred_le_norm_mul_prod (half_pos hpos))
      ((exists_lt_of_lt_ciSup (half_lt_self hpos)).imp fun _ ht ↦ ht.le)
    refine ⟨m, le_antisymm (le_gaussNorm norm c f hf.hasGaussNorm m) (ciSup_le fun t ↦ ?_)⟩
    exact (le_or_gt (gaussNorm norm c f / 2) _).elim (hmax t) fun h ↦ h.le.trans hm

/-- A restricted power series with nonzero Gauss norm has only finitely many indices achieving
the Gauss norm. -/
lemma finite_setOfPred_achievesGaussNorm (hf : IsRestricted c f) (h : gaussNorm norm c f ≠ 0) :
    {a | AchievesGaussNorm norm c f a}.Finite :=
  have hpos : 0 < gaussNorm norm c f := (gaussNorm_nonneg norm c f norm_nonneg).lt_of_ne' h
  (hf.finite_setOfPred_le_norm_mul_prod (half_pos hpos)).subset
    fun _ ha ↦ (half_le_self hpos.le).trans ha.ge

/-- If `f` and `g` are restricted with nonzero Gauss norm, there are indices `i`, `j` achieving
the Gauss norms of `f` and `g` such that the term of `f * g` at `(i, j)` strictly dominates all
other terms on the antidiagonal of `i + j`.  This discharges the `hdom` hypothesis of
`MvPowerSeries.gaussNorm_mul_eq_mul`.  The final conjunct records the lex-maximality of the
pair: if `i + j = 0` then every achieving index of `f` and of `g` is `0`. -/
lemma exists_achievesGaussNorm_dominant [DecidableEq σ] (hc : 0 ≤ c) (hf : IsRestricted c f)
    (hg : IsRestricted c g) (hf0 : gaussNorm norm c f ≠ 0) (hg0 : gaussNorm norm c g ≠ 0) :
    ∃ i j, AchievesGaussNorm norm c f i ∧ AchievesGaussNorm norm c g j ∧
      (∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
        ‖coeff p.1 f * coeff p.2 g‖ < ‖coeff i f‖ * ‖coeff j g‖) ∧
      (i + j = 0 → (∀ t, AchievesGaussNorm norm c f t → t = 0) ∧
        ∀ t, AchievesGaussNorm norm c g t → t = 0) :=
  MvPowerSeries.exists_achievesGaussNorm_dominant norm c (fun _ ↦ norm_nonneg _) norm_mul_le hc
    hf.hasGaussNorm hg.hasGaussNorm (hf.finite_setOfPred_achievesGaussNorm hf0)
    (hg.finite_setOfPred_achievesGaussNorm hg0) hf.exists_achievesGaussNorm
    hg.exists_achievesGaussNorm hf0 hg0

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

namespace Restricted

variable (c : σ → ℝ) [IsUltrametricDist R]

variable (R) in
/-- The Gauss norm on `Restricted R c`, as a bare function. -/
noncomputable abbrev gaussNorm (f : Restricted R c) : ℝ :=
  MvPowerSeries.gaussNorm (norm : R → ℝ) c f.1

/-- A restricted power series has a finite Gauss norm: the terms `‖coeff t f.1‖ * t.prod (c · ^ ·)`
are bounded above. -/
lemma hasGaussNorm (f : Restricted R c) : HasGaussNorm norm c f.1 := f.2.hasGaussNorm

variable (R) in
/-- For nonnegative radii, the Gauss norm on `Restricted R c` is nonarchimedean. -/
lemma isNonarchimedean_gaussNorm (hc : 0 ≤ c) : IsNonarchimedean (gaussNorm R c) :=
  fun f g ↦ gaussNorm_add_le_max norm c f.1 g.1 hc norm_nonneg
    IsUltrametricDist.norm_add_le_max f.hasGaussNorm g.hasGaussNorm

/-- The Gauss norm of a restricted power series is zero iff the power series is zero. -/
lemma gaussNorm_eq_zero_iff (hc : ∀ i, 0 < c i) {f : Restricted R c} :
    gaussNorm R c f = 0 ↔ f = 0 :=
  ⟨fun h ↦ Subtype.ext ((MvPowerSeries.gaussNorm_eq_zero_iff norm c f.1 norm_zero norm_nonneg
    (fun _ ↦ norm_eq_zero.mp) hc f.hasGaussNorm).mp h), fun h ↦ by simp [h, gaussNorm]⟩

/-- The Gauss norm of a restricted power series is achieved by some index. -/
lemma exists_achievesGaussNorm (f : Restricted R c) : ∃ a, AchievesGaussNorm norm c f.1 a :=
  f.2.exists_achievesGaussNorm

/-- A restricted power series with nonzero Gauss norm has only finitely many indices achieving
the Gauss norm. -/
lemma finite_setOfPred_achievesGaussNorm (f : Restricted R c) (h : gaussNorm R c f ≠ 0) :
    {a | AchievesGaussNorm norm c f.1 a}.Finite :=
  f.2.finite_setOfPred_achievesGaussNorm h

/-- If `f` and `g` have nonzero Gauss norm, there are indices `i`, `j` achieving the Gauss norms
of `f` and `g` such that the term of `f * g` at `(i, j)` strictly dominates all other terms on
the antidiagonal of `i + j`.  This is the key step in the multiplicativity of the Gauss norm.
The final conjunct records the lex-maximality of the pair: if `i + j = 0` then every achieving
index of `f` and of `g` is `0`. -/
lemma exists_achievesGaussNorm_dominant [DecidableEq σ] (hc : 0 ≤ c) (f g : Restricted R c)
    (hf : gaussNorm R c f ≠ 0) (hg : gaussNorm R c g ≠ 0) :
    ∃ i j, AchievesGaussNorm norm c f.1 i ∧ AchievesGaussNorm norm c g.1 j ∧
      (∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
        ‖coeff p.1 f.1 * coeff p.2 g.1‖ < ‖coeff i f.1‖ * ‖coeff j g.1‖) ∧
      (i + j = 0 → (∀ t, AchievesGaussNorm norm c f.1 t → t = 0) ∧
        ∀ t, AchievesGaussNorm norm c g.1 t → t = 0) :=
  IsRestricted.exists_achievesGaussNorm_dominant hc f.2 g.2 hf hg

section

variable [hc : Fact (∀ i, 0 < c i)]

/-- The Gauss norm on `Restricted R c` as a bundled `RingNorm`. -/
noncomputable def gaussNormRingNorm : RingNorm (Restricted R c) where
  toFun := gaussNorm R c
  map_zero' := gaussNorm_zero norm c norm_zero
  add_le' _ _ :=
    IsNonarchimedean.add_le (fun f : Restricted R c ↦ gaussNorm_nonneg norm c f.1 norm_nonneg)
      (isNonarchimedean_gaussNorm R c (StrongLT.le hc.out))
  neg' f := gaussNorm_neg norm c norm_neg f.1
  mul_le' f g := gaussNorm_mul_le norm c f.1 g.1 (StrongLT.le hc.out) norm_nonneg
    norm_mul_le IsUltrametricDist.norm_add_le_max norm_zero f.hasGaussNorm g.hasGaussNorm
  eq_zero_of_map_eq_zero' _ h := (gaussNorm_eq_zero_iff c hc.out).mp h

noncomputable instance : NormedRing (Restricted R c) := RingNorm.toNormedRing (gaussNormRingNorm c)

/-- The norm on `Restricted R c` is by definition the Gauss norm of the underlying power series. -/
lemma norm_def (f : Restricted R c) : ‖f‖ = MvPowerSeries.gaussNorm (norm : R → ℝ) c f.1 := rfl

/-- The Gauss norm of a nonzero restricted multivariate power series is realised by a nonzero
coefficient: some exponent `t` satisfies `coeff t f ≠ 0` and
`‖f‖ = ‖coeff t f‖ * ∏ᵢ (c i) ^ (t i)`. -/
lemma exists_coeff_ne_zero_norm_eq (f : Restricted R c) (hf : f ≠ 0) :
    ∃ t, coeff t f.1 ≠ 0 ∧ ‖f‖ = ‖coeff t f.1‖ * t.prod (fun i e ↦ c i ^ e) := by
  obtain ⟨t, ht⟩ := exists_achievesGaussNorm c f
  have hnorm : ‖f‖ = ‖coeff t f.1‖ * t.prod (fun i e ↦ c i ^ e) := (norm_def c f).trans ht.symm
  exact ⟨t, norm_ne_zero_iff.mp (left_ne_zero_of_mul (hnorm ▸ norm_ne_zero_iff.mpr hf)), hnorm⟩

/-- The Gauss norm is at most `ε` if and only if every term `‖coeff t f.1‖ * ∏ᵢ (c i) ^ (t i)`
is. -/
lemma norm_le_iff {ε : ℝ} (f : Restricted R c) :
    ‖f‖ ≤ ε ↔ ∀ t, ‖coeff t f.1‖ * t.prod (c · ^ ·) ≤ ε :=
  ⟨fun h t ↦ (le_gaussNorm norm c f.1 (hasGaussNorm c f) t).trans h, fun h ↦ ciSup_le h⟩

/-- The Gauss norm is less than `ε` if and only if every term `‖coeff t f.1‖ * ∏ᵢ (c i) ^ (t i)`
is; the nontrivial direction holds because the Gauss norm of a restricted power series is
achieved. -/
lemma norm_lt_iff {ε : ℝ} (f : Restricted R c) :
    ‖f‖ < ε ↔ ∀ t, ‖coeff t f.1‖ * t.prod (c · ^ ·) < ε := by
  refine ⟨fun h t ↦ (le_gaussNorm norm c f.1 (hasGaussNorm c f) t).trans_lt h, fun h ↦ ?_⟩
  obtain ⟨a, ha⟩ := exists_achievesGaussNorm c f
  rw [norm_def, ← ha]
  exact h a

variable {S : Type*} [NormedRing S] [IsUltrametricDist S]

/-- Applying a norm-nonincreasing ring homomorphism to a restricted power series does not
increase its Gauss norm. -/
lemma norm_map_le {φ : R →+* S} (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) (f : Restricted R c) :
    ‖map c hφ f‖ ≤ ‖f‖ := by
  rw [norm_le_iff]
  intro t
  rw [val_map, MvPowerSeries.coeff_map]
  refine (mul_le_mul_of_nonneg_right (hφ _)
    (Finset.prod_nonneg fun i _ ↦ pow_nonneg (hc.out i).le _)).trans ((norm_le_iff c f).mp le_rfl t)

/-- Applying a norm-preserving ring homomorphism preserves the Gauss norm; inherited from
`MvPowerSeries.gaussNorm_map`. -/
lemma norm_map {φ : R →+* S} (hφ : ∀ x, ‖φ x‖ = ‖x‖) (f : Restricted R c) :
    ‖map c (fun x ↦ (hφ x).le) f‖ = ‖f‖ := by
  rw [norm_def, norm_def, val_map]
  exact MvPowerSeries.gaussNorm_map norm c norm φ hφ f.1

/-- The norm of a monomial in `Restricted R c`. -/
@[simp]
lemma norm_monomial (t : σ →₀ ℕ) (a : R) : ‖monomial c t a‖ = ‖a‖ * t.prod (c · ^ ·) :=
  MvPowerSeries.gaussNorm_monomial norm c norm_zero (fun _ ↦ norm_nonneg _)
    (StrongLT.le hc.out) t a

/-- The norm of a constant in `Restricted R c`. -/
@[simp]
lemma norm_C (a : R) : ‖C c a‖ = ‖a‖ :=
  MvPowerSeries.gaussNorm_C norm c norm_zero (fun _ ↦ norm_nonneg _) a

variable (R) in
/-- The norm of the variable `X s` in `Restricted R c` is `‖1‖ * c s`; with `NormOneClass R`,
`simp` further reduces this to `c s`. -/
@[simp]
lemma norm_X (s : σ) : ‖X R c s‖ = ‖(1 : R)‖ * c s :=
  MvPowerSeries.gaussNorm_X norm c norm_zero (fun _ ↦ norm_nonneg _) s (hc.out s).le

/-- When the norm on `R` is one on `1`, so is the Gauss norm on `Restricted R c`. -/
instance [NormOneClass R] : NormOneClass (Restricted R c) where
  norm_one := (MvPowerSeries.gaussNorm_one norm c norm_zero (fun _ ↦ norm_nonneg _)).trans norm_one

variable (R) in
/-- The norm on `Restricted R c` (the Gauss norm) is nonarchimedean. -/
lemma isNonarchimedean_norm : IsNonarchimedean (norm : Restricted R c → ℝ) :=
  isNonarchimedean_gaussNorm R c (StrongLT.le hc.out)

instance : IsUltrametricDist (Restricted R c) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (isNonarchimedean_norm R c)

/-- When the norm on `R` is multiplicative, so is the Gauss norm on `Restricted R c`. -/
instance [NormMulClass R] : NormMulClass (Restricted R c) where
  norm_mul f g := by
    classical
    obtain rfl | hf := eq_or_ne f 0
    · simp
    obtain rfl | hg := eq_or_ne g 0
    · simp
    obtain ⟨i, j, hi, hj, hdom, -⟩ := exists_achievesGaussNorm_dominant c (StrongLT.le hc.out) f g
      ((gaussNorm_eq_zero_iff c hc.out).ne.mpr hf) ((gaussNorm_eq_zero_iff c hc.out).ne.mpr hg)
    exact gaussNorm_mul_eq_mul norm c f.1 g.1 f.hasGaussNorm g.hasGaussNorm (f * g).hasGaussNorm
      norm_nonneg norm_zero IsUltrametricDist.isNonarchimedean_norm norm_mul norm_neg
      (fun _ ↦ norm_eq_zero.mp) hc.out ⟨i, j, hi, hj, hdom⟩

section
open Filter
open scoped Topology

/-- If `0` is not isolated in `R`, then it is not isolated in `Restricted R c`: the constants
embed isometrically via `C`. -/
instance [NeBot (𝓝[≠] (0 : R))] : NeBot (𝓝[≠] (0 : Restricted R c)) := by
  rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨r, hr_ne, hr⟩ : ∃ r : R, r ≠ 0 ∧ ‖r‖ < ε := by
    obtain ⟨r, hr_mem, hr_dist⟩ := Metric.mem_closure_iff.mp
      (mem_closure_iff_nhdsWithin_neBot.mpr ‹_›) ε hε
    exact ⟨r, hr_mem, by rwa [dist_comm, dist_zero_right] at hr_dist⟩
  have hCne : (C c r : Restricted R c) ≠ 0 :=
    norm_pos_iff.mp (by rw [norm_C]; exact norm_pos_iff.mpr hr_ne)
  exact ⟨C c r, hCne, by rwa [dist_comm, dist_zero_right, norm_C]⟩

/-- A restricted power series is the sum of its monomials: the partial sums over finite sets of
exponents converge to it in the Gauss norm, since the remaining tail has small norm. -/
lemma hasSum_monomial (f : Restricted R c) :
    HasSum (fun t ↦ monomial c t (coeff t f.1)) f := by
  classical
  rw [HasSum, SummationFilter.unconditional_filter, Metric.tendsto_atTop]
  intro ε hε
  have hfin : {t | ¬ ‖coeff t f.1‖ * t.prod (c · ^ ·) < ε / 2}.Finite :=
    Filter.eventually_cofinite.mp (Filter.Tendsto.eventually_lt_const (by linarith) f.2)
  refine ⟨hfin.toFinset, fun s hs ↦ ?_⟩
  rw [dist_eq_norm, norm_def]
  refine lt_of_le_of_lt (ciSup_le fun t ↦ ?_) (half_lt_self hε)
  rw [show (∑ u ∈ s, monomial c u (coeff u f.1) - f : Restricted R c).1
      = (∑ u ∈ s, MvPowerSeries.monomial u (coeff u f.1)) - f.1 by simp,
    map_sub, map_sum]
  simp_rw [MvPowerSeries.coeff_monomial, Finset.sum_ite_eq]
  by_cases ht : t ∈ s
  · rw [if_pos ht, sub_self, norm_zero, zero_mul]
    linarith
  · rw [if_neg ht, zero_sub, norm_neg]
    by_contra hP
    exact ht (hs (hfin.mem_toFinset.mpr fun h ↦ hP h.le))

end

/-- The canonical `ℤ`-module structure on `Restricted R c`, as a shortcut instance.  There are
two defeq derivations (`AddCommGroup.toIntModule` and `Algebra.toModule ∘ Ring.toIntAlgebra`),
and instance search cannot reconcile mixed spellings through the opaque `Restricted` type
synonym; declaring one of them as a shortcut makes every downstream search site — in
particular the instance arguments of `PowerBounded.subring` — record the same spelling. -/
noncomputable instance : Module ℤ (Restricted R c) := AddCommGroup.toIntModule _

/-- The Gauss-norm topology on `Restricted R c` is `ℤ`-linear, since it is ultrametric and
hence nonarchimedean.  Declared as an instance at the `Restricted` level — at the canonical
`ℤ`-module spelling above — so that instance search never needs to unfold the `Restricted`
type synonym. -/
instance : IsLinearTopology ℤ (Restricted R c) := by
  exact NonarchimedeanAddGroup.isLinearTopology_int

end

/-- When `R` is a normed commutative ring, the Gauss norm makes `Restricted R c` a normed
commutative ring. -/
noncomputable instance {S : Type*} [NormedCommRing S] [IsUltrametricDist S] {τ : Type*}
    {d : τ → ℝ} [Fact (∀ i, 0 < d i)] : NormedCommRing (Restricted S d) :=
  { (inferInstance : NormedRing (Restricted S d)) with
    mul_comm := fun f g ↦ ext (mul_comm f.1 g.1) }

end Restricted

end MvPowerSeries

namespace MvPolynomial

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {σ : Type*} (c : σ → ℝ)
  [hc : Fact (∀ i, 0 < c i)]

/-- The norm of a polynomial in the restricted power series ring is its polynomial Gauss norm,
a finite computation over the support. -/
@[simp]
lemma norm_toRestricted (p : MvPolynomial σ R) : ‖toRestricted c p‖ = p.gaussNorm norm c :=
  p.gaussNorm_coe norm c norm_zero (fun _ ↦ norm_nonneg _) (StrongLT.le hc.out)

end MvPolynomial
