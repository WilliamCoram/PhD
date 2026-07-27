/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.ForMathlib.RingTheory.MvPowerSeries.Restricted.GaussNorm
import PhD.ForMathlib.RingTheory.Polynomial.GaussNorm
import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.Basic

/-!
# The Gauss norm on restricted univariate power series

For a normed ring `R` with ultrametric norm and a strictly positive radius `c : ℝ` (recorded as
`[Fact (0 < c)]`), the Gauss norm makes `PowerSeries.Restricted R c` a normed ring with
ultrametric norm.  If the norm on `R` is multiplicative, so is the Gauss norm (`NormMulClass`).

Since `PowerSeries.Restricted R c` is by definition
`MvPowerSeries.Restricted R (fun _ : Unit ↦ c)`, the `NormedRing`, `IsUltrametricDist` and
`NormMulClass` instances are inherited from the multivariate case; this file provides the `Fact`
instance that makes them fire, and restates the multivariate lemmas with `ℕ`-indexed
coefficients.  As in the multivariate file, attainment of the Gauss norm is developed at the
level of the `IsRestricted` predicate, with the subtype versions as corollaries.

## Main definitions

* `PowerSeries.Restricted.gaussNorm`: the Gauss norm on `Restricted R c`, as a bare function.
* `PowerSeries.Restricted.gaussNormRingNorm`: the Gauss norm as a bundled `RingNorm`.

## Main results

* `PowerSeries.IsRestricted.exists_achievesGaussNorm_dominant`: the `ℕ`-indexed dominant-term
  lemma, transported from the multivariate case.
* `PowerSeries.Restricted.isNonarchimedean_norm`: the Gauss norm is nonarchimedean.
* `PowerSeries.Restricted.norm_monomial`, `norm_C`, `norm_X`: explicit values of the norm on
  monomials, constants and the variable.
* `Polynomial.norm_toRestricted`: the norm of a polynomial in the restricted power series ring
  is its polynomial Gauss norm `Polynomial.gaussNorm`, a finite computation.
-/

namespace PowerSeries

variable {R : Type*} [NormedRing R]

namespace IsRestricted

variable {c : ℝ} {f g : PowerSeries R}

/-- A restricted power series has a finite Gauss norm: the terms `‖coeff i f‖ * c ^ i` are
bounded above. -/
lemma hasGaussNorm (hf : IsRestricted c f) : HasGaussNorm norm c f :=
  ((isRestricted_iff c f).mp hf).bddAbove_range_of_cofinite

/-- The Gauss norm of a restricted power series is achieved by some index. -/
lemma exists_achievesGaussNorm (hf : IsRestricted c f) : ∃ a, AchievesGaussNorm norm c f a := by
  obtain ⟨a, ha⟩ := MvPowerSeries.IsRestricted.exists_achievesGaussNorm hf
  obtain ⟨n, rfl⟩ : ∃ n, a = Finsupp.single () n := ⟨a (), Finsupp.unique_single a⟩
  exact ⟨n, (achievesGaussNorm_iff_single norm c f n).mpr ha⟩

/-- A restricted power series with nonzero Gauss norm has only finitely many indices achieving
the Gauss norm. -/
lemma finite_setOfPred_achievesGaussNorm (hf : IsRestricted c f) (h : gaussNorm norm c f ≠ 0) :
    {a | AchievesGaussNorm norm c f a}.Finite := by
  have hMv := MvPowerSeries.IsRestricted.finite_setOfPred_achievesGaussNorm hf h
  refine (hMv.image (fun t ↦ t ())).subset fun a ha ↦ ?_
  exact ⟨Finsupp.single () a, (achievesGaussNorm_iff_single norm c f a).mp ha, by simp⟩

/-- If `f` and `g` are restricted with nonzero Gauss norm, there are indices `i`, `j` achieving
the Gauss norms of `f` and `g` such that the term of `f * g` at `(i, j)` strictly dominates all
other terms on the antidiagonal of `i + j`.  The final conjunct records the maximality of the
pair: if `i + j = 0` then every achieving index of `f` and of `g` is `0`. -/
lemma exists_achievesGaussNorm_dominant (hc : 0 ≤ c) (hf : IsRestricted c f)
    (hg : IsRestricted c g) (hf0 : gaussNorm norm c f ≠ 0) (hg0 : gaussNorm norm c g ≠ 0) :
    ∃ i j, AchievesGaussNorm norm c f i ∧ AchievesGaussNorm norm c g j ∧
      (∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
        ‖coeff p.1 f * coeff p.2 g‖ < ‖coeff i f‖ * ‖coeff j g‖) ∧
      (i + j = 0 → (∀ n, AchievesGaussNorm norm c f n → n = 0) ∧
        ∀ n, AchievesGaussNorm norm c g n → n = 0) := by
  obtain ⟨i, j, hi, hj, hdom, hzero⟩ :=
    MvPowerSeries.IsRestricted.exists_achievesGaussNorm_dominant (fun _ ↦ hc) hf hg hf0 hg0
  obtain ⟨n, rfl⟩ : ∃ n, i = Finsupp.single () n := ⟨i (), Finsupp.unique_single i⟩
  obtain ⟨m, rfl⟩ : ∃ m, j = Finsupp.single () m := ⟨j (), Finsupp.unique_single j⟩
  refine ⟨n, m, (achievesGaussNorm_iff_single norm c f n).mpr hi,
    (achievesGaussNorm_iff_single norm c g m).mpr hj, fun p hp hpne ↦ ?_, fun hnm ↦ ?_⟩
  · exact hdom (Finsupp.single () p.1, Finsupp.single () p.2)
      (by rw [Finset.mem_antidiagonal, ← Finsupp.single_add, ← Finsupp.single_add,
        Finset.mem_antidiagonal.mp hp])
      fun h ↦ hpne (Prod.ext (Finsupp.single_injective () (congrArg Prod.fst h))
        (Finsupp.single_injective () (congrArg Prod.snd h)))
  · obtain ⟨hzf, hzg⟩ := hzero (by rw [← Finsupp.single_add, hnm, Finsupp.single_zero])
    refine ⟨fun k hk ↦ ?_, fun k hk ↦ ?_⟩
    · simpa [Finsupp.single_eq_zero] using
        hzf _ ((achievesGaussNorm_iff_single norm c f k).mp hk)
    · simpa [Finsupp.single_eq_zero] using
        hzg _ ((achievesGaussNorm_iff_single norm c g k).mp hk)

/-- On `Unit`-indexed finsupps the lex order compares the single values. -/
private lemma le_of_toLex_single_le {m n : ℕ}
    (h : toLex (Finsupp.single () m) ≤ toLex (Finsupp.single () n)) : m ≤ n := by
  by_contra hmn
  have hlt : Finsupp.single () n < Finsupp.single () m := by
    refine lt_of_le_of_ne (Finsupp.le_def.mpr fun u ↦ ?_) fun heq ↦
      hmn (Finsupp.single_injective () heq).ge
    simpa [Finsupp.single_apply] using (not_le.mp hmn).le
  exact absurd h (not_le.mpr (Finsupp.toLex_monotone.strictMono_of_injective toLex.injective hlt))

/-- Strengthening of `exists_achievesGaussNorm_dominant`: the dominant pair `(i, j)` consists
of the *largest* achieving indices, and the last two conjuncts expose this maximality. -/
lemma exists_achievesGaussNorm_dominant_max (hc : 0 ≤ c) (hf : IsRestricted c f)
    (hg : IsRestricted c g) (hf0 : gaussNorm norm c f ≠ 0) (hg0 : gaussNorm norm c g ≠ 0) :
    ∃ i j, AchievesGaussNorm norm c f i ∧ AchievesGaussNorm norm c g j ∧
      (∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
        ‖coeff p.1 f * coeff p.2 g‖ < ‖coeff i f‖ * ‖coeff j g‖) ∧
      (∀ t, AchievesGaussNorm norm c f t → t ≤ i) ∧
      ∀ t, AchievesGaussNorm norm c g t → t ≤ j := by
  obtain ⟨i, j, hi, hj, hdom, hi_max, hj_max⟩ :=
    MvPowerSeries.IsRestricted.exists_achievesGaussNorm_dominant_lexMax (fun _ ↦ hc) hf hg
      hf0 hg0
  obtain ⟨n, rfl⟩ : ∃ n, i = Finsupp.single () n := ⟨i (), Finsupp.unique_single i⟩
  obtain ⟨m, rfl⟩ : ∃ m, j = Finsupp.single () m := ⟨j (), Finsupp.unique_single j⟩
  refine ⟨n, m, (achievesGaussNorm_iff_single norm c f n).mpr hi,
    (achievesGaussNorm_iff_single norm c g m).mpr hj, fun p hp hpne ↦ ?_,
    fun t ht ↦ le_of_toLex_single_le
      (hi_max _ ((achievesGaussNorm_iff_single norm c f t).mp ht)),
    fun t ht ↦ le_of_toLex_single_le
      (hj_max _ ((achievesGaussNorm_iff_single norm c g t).mp ht))⟩
  exact hdom (Finsupp.single () p.1, Finsupp.single () p.2)
    (by rw [Finset.mem_antidiagonal, ← Finsupp.single_add, ← Finsupp.single_add,
      Finset.mem_antidiagonal.mp hp])
    fun h ↦ hpne (Prod.ext (Finsupp.single_injective () (congrArg Prod.fst h))
      (Finsupp.single_injective () (congrArg Prod.snd h)))

end IsRestricted

namespace Restricted

variable (c : ℝ) [IsUltrametricDist R]

/-- Strict positivity of `c : ℝ` gives strict positivity of the constant tuple `fun _ : Unit ↦ c`,
so that the instances on `MvPowerSeries.Restricted R (fun _ ↦ c)` apply to `Restricted R c`. -/
instance [hc : Fact (0 < c)] : Fact (∀ _ : Unit, 0 < c) := ⟨fun _ ↦ hc.out⟩

variable (R) in
/-- The Gauss norm on `Restricted R c`, as a bare function. -/
noncomputable abbrev gaussNorm (f : Restricted R c) : ℝ :=
  PowerSeries.gaussNorm (norm : R → ℝ) c f.1

/-- A restricted power series has a finite Gauss norm: the terms `‖coeff i f.1‖ * c ^ i` are
bounded above. -/
lemma hasGaussNorm (f : Restricted R c) : HasGaussNorm norm c f.1 :=
  IsRestricted.hasGaussNorm f.2

variable (R) in
/-- For a nonnegative radius, the Gauss norm on `Restricted R c` is nonarchimedean. -/
lemma isNonarchimedean_gaussNorm (hc : 0 ≤ c) : IsNonarchimedean (gaussNorm R c) :=
  MvPowerSeries.Restricted.isNonarchimedean_gaussNorm R (fun _ ↦ c) fun _ ↦ hc

/-- The Gauss norm of a restricted power series is zero iff the power series is zero. -/
lemma gaussNorm_eq_zero_iff (hc : 0 < c) {f : Restricted R c} :
    gaussNorm R c f = 0 ↔ f = 0 :=
  MvPowerSeries.Restricted.gaussNorm_eq_zero_iff (fun _ ↦ c) fun _ ↦ hc

/-- The Gauss norm of a restricted power series is achieved by some index. -/
lemma exists_achievesGaussNorm (f : Restricted R c) : ∃ a, AchievesGaussNorm norm c f.1 a :=
  IsRestricted.exists_achievesGaussNorm f.2

/-- A restricted power series with nonzero Gauss norm has only finitely many indices achieving
the Gauss norm. -/
lemma finite_setOfPred_achievesGaussNorm (f : Restricted R c) (h : gaussNorm R c f ≠ 0) :
    {a | AchievesGaussNorm norm c f.1 a}.Finite :=
  IsRestricted.finite_setOfPred_achievesGaussNorm f.2 h

/-- If `f` and `g` have nonzero Gauss norm, there are indices `i`, `j` achieving the Gauss norms
of `f` and `g` such that the term of `f * g` at `(i, j)` strictly dominates all other terms on
the antidiagonal of `i + j`.  This is the key step in the multiplicativity of the Gauss norm.
The final conjunct records the maximality of the pair: if `i + j = 0` then every achieving
index of `f` and of `g` is `0`. -/
lemma exists_achievesGaussNorm_dominant (hc : 0 ≤ c) (f g : Restricted R c)
    (hf : gaussNorm R c f ≠ 0) (hg : gaussNorm R c g ≠ 0) :
    ∃ i j, AchievesGaussNorm norm c f.1 i ∧ AchievesGaussNorm norm c g.1 j ∧
      (∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
        ‖coeff p.1 f.1 * coeff p.2 g.1‖ < ‖coeff i f.1‖ * ‖coeff j g.1‖) ∧
      (i + j = 0 → (∀ n, AchievesGaussNorm norm c f.1 n → n = 0) ∧
        ∀ n, AchievesGaussNorm norm c g.1 n → n = 0) :=
  IsRestricted.exists_achievesGaussNorm_dominant hc f.2 g.2 hf hg

/-- Strengthening of `exists_achievesGaussNorm_dominant`: the dominant pair `(i, j)` consists
of the *largest* achieving indices, and the last two conjuncts expose this maximality. -/
lemma exists_achievesGaussNorm_dominant_max (hc : 0 ≤ c) (f g : Restricted R c)
    (hf : gaussNorm R c f ≠ 0) (hg : gaussNorm R c g ≠ 0) :
    ∃ i j, AchievesGaussNorm norm c f.1 i ∧ AchievesGaussNorm norm c g.1 j ∧
      (∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
        ‖coeff p.1 f.1 * coeff p.2 g.1‖ < ‖coeff i f.1‖ * ‖coeff j g.1‖) ∧
      (∀ t, AchievesGaussNorm norm c f.1 t → t ≤ i) ∧
      ∀ t, AchievesGaussNorm norm c g.1 t → t ≤ j :=
  IsRestricted.exists_achievesGaussNorm_dominant_max hc f.2 g.2 hf hg

section

variable [Fact (0 < c)]

/-- The Gauss norm on `Restricted R c` as a bundled `RingNorm`. -/
noncomputable def gaussNormRingNorm : RingNorm (Restricted R c) :=
  MvPowerSeries.Restricted.gaussNormRingNorm (fun _ ↦ c)

noncomputable example : NormedRing (Restricted R c) := inferInstance

/-- The norm on `Restricted R c` is by definition the Gauss norm of the underlying power
series. -/
lemma norm_def (f : Restricted R c) : ‖f‖ = PowerSeries.gaussNorm (norm : R → ℝ) c f.1 := rfl

/-- Every weighted coefficient norm `‖coeff n f.1‖ * c ^ n` is at most the norm. -/
lemma norm_coeff_mul_pow_le (f : Restricted R c) (n : ℕ) : ‖coeff n f.1‖ * c ^ n ≤ ‖f‖ := by
  rw [norm_def]
  exact PowerSeries.le_gaussNorm norm c f.1 (hasGaussNorm c f) n

/-- The Gauss norm is at most `ε` if and only if every term `‖coeff i f.1‖ * c ^ i` is. -/
lemma norm_le_iff {ε : ℝ} (f : Restricted R c) : ‖f‖ ≤ ε ↔ ∀ i, ‖coeff i f.1‖ * c ^ i ≤ ε := by
  rw [MvPowerSeries.Restricted.norm_le_iff]
  refine ⟨fun h i ↦ ?_, fun h t ↦ ?_⟩
  · simpa [Finsupp.prod_single_index] using h (Finsupp.single () i)
  · obtain ⟨i, rfl⟩ : ∃ i, t = Finsupp.single () i := ⟨t (), Finsupp.unique_single t⟩
    simpa [Finsupp.prod_single_index] using h i

/-- The Gauss norm is less than `ε` if and only if every term `‖coeff i f.1‖ * c ^ i` is; the
nontrivial direction holds because the Gauss norm of a restricted power series is achieved. -/
lemma norm_lt_iff {ε : ℝ} (f : Restricted R c) : ‖f‖ < ε ↔ ∀ i, ‖coeff i f.1‖ * c ^ i < ε := by
  rw [MvPowerSeries.Restricted.norm_lt_iff]
  refine ⟨fun h i ↦ ?_, fun h t ↦ ?_⟩
  · simpa [Finsupp.prod_single_index] using h (Finsupp.single () i)
  · obtain ⟨i, rfl⟩ : ∃ i, t = Finsupp.single () i := ⟨t (), Finsupp.unique_single t⟩
    simpa [Finsupp.prod_single_index] using h i

section Map

variable {S : Type*} [NormedRing S] [IsUltrametricDist S]

/-- Applying a norm-nonincreasing ring homomorphism to a restricted power series does not
increase its Gauss norm; inherited from the multivariate case. -/
lemma norm_map_le {φ : R →+* S} (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) (f : Restricted R c) :
    ‖map c hφ f‖ ≤ ‖f‖ :=
  MvPowerSeries.Restricted.norm_map_le (fun _ ↦ c) hφ f

/-- Applying a norm-preserving ring homomorphism preserves the Gauss norm; inherited from the
multivariate case. -/
lemma norm_map {φ : R →+* S} (hφ : ∀ x, ‖φ x‖ = ‖x‖) (f : Restricted R c) :
    ‖map c (fun x ↦ (hφ x).le) f‖ = ‖f‖ :=
  MvPowerSeries.Restricted.norm_map (fun _ ↦ c) hφ f

end Map

/-- The norm of a monomial in `Restricted R c`. -/
@[simp]
lemma norm_monomial (n : ℕ) (a : R) : ‖monomial c n a‖ = ‖a‖ * c ^ n :=
  (MvPowerSeries.Restricted.norm_monomial (fun _ ↦ c) (Finsupp.single () n) a).trans <| by simp

/-- The norm of a constant in `Restricted R c`. -/
@[simp]
lemma norm_C (a : R) : ‖C c a‖ = ‖a‖ :=
  MvPowerSeries.Restricted.norm_C (fun _ ↦ c) a

variable (R) in
/-- The norm of the variable `X` in `Restricted R c` is `‖1‖ * c`; with `NormOneClass R`,
`simp` further reduces this to `c`. -/
@[simp]
lemma norm_X : ‖X R c‖ = ‖(1 : R)‖ * c :=
  MvPowerSeries.Restricted.norm_X R (fun _ ↦ c) ()

/-- When the norm on `R` is one on `1`, so is the norm on `Restricted R c`; the instance is
inherited from the multivariate case. -/
example [NormOneClass R] : NormOneClass (Restricted R c) := inferInstance

variable (R) in
/-- The norm on `Restricted R c` (the Gauss norm) is nonarchimedean. -/
lemma isNonarchimedean_norm : IsNonarchimedean (norm : Restricted R c → ℝ) :=
  MvPowerSeries.Restricted.isNonarchimedean_norm R (fun _ ↦ c)

example : IsUltrametricDist (Restricted R c) := inferInstance

/-- When the norm on `R` is multiplicative, so is the Gauss norm on `Restricted R c`; the
instance is inherited from the multivariate case. -/
example [NormMulClass R] : NormMulClass (Restricted R c) := inferInstance

section
open Filter
open scoped Topology

/-- A restricted power series is the sum of its monomials; inherited from the multivariate case
by reindexing along `ℕ ≃ (Unit →₀ ℕ)`. -/
lemma hasSum_monomial (f : Restricted R c) :
    HasSum (fun n ↦ monomial c n (coeff n f.1)) f :=
  ((Finsupp.uniqueEquiv (M := ℕ) ()).symm.hasSum_iff).mpr
    (MvPowerSeries.Restricted.hasSum_monomial (fun _ ↦ c) f)

/-- The partial sums of the monomials of a restricted power series converge to it in the Gauss
norm. -/
lemma tendsto_sum_range_monomial (f : Restricted R c) :
    Tendsto (fun n ↦ ∑ i ∈ Finset.range n, monomial c i (coeff i f.1)) atTop (𝓝 f) :=
  (hasSum_monomial c f).tendsto_sum_nat

end

end

/-- When `R` is a normed commutative ring, so is `Restricted R c`; the instance is inherited
from the multivariate case. -/
noncomputable example {S : Type*} [NormedCommRing S] [IsUltrametricDist S] {d : ℝ}
    [Fact (0 < d)] : NormedCommRing (Restricted S d) := inferInstance

open scoped Topology in
/-- If `0` is not isolated in `S`, it is not isolated in `Restricted S d`; the instance is
inherited from the multivariate case. -/
example {S : Type*} [NormedRing S] [IsUltrametricDist S] {d : ℝ} [Fact (0 < d)]
    [Filter.NeBot (𝓝[≠] (0 : S))] : Filter.NeBot (𝓝[≠] (0 : Restricted S d)) :=
  inferInstance

/-- The Gauss-norm topology on `Restricted S d` is `ℤ`-linear; the instance is inherited from
the multivariate case. -/
example {S : Type*} [NormedRing S] [IsUltrametricDist S] {d : ℝ} [Fact (0 < d)] :
    IsLinearTopology ℤ (Restricted S d) := inferInstance

end Restricted

end PowerSeries

namespace Polynomial

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] (c : ℝ) [Fact (0 < c)]

/-- The norm of a polynomial in the restricted power series ring is its polynomial Gauss norm,
a finite computation over the support. -/
@[simp]
lemma norm_toRestricted (p : R[X]) : ‖toRestricted c p‖ = p.gaussNorm norm c :=
  p.gaussNorm_coe_powerSeries norm c norm_zero (fun _ ↦ norm_nonneg _) (Fact.out (p := 0 < c)).le

end Polynomial
