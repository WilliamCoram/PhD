/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.RingTheory.MvPowerSeries.Basic

public import PhD.RPS.mathlib

/-!
# Gauss norm for multivariate power series

This file defines the Gauss norm for power series. Given a multivariate power series `f`, a
function `v : R → ℝ` and a tuple `c` of real numbers, the Gauss norm is defined as the supremum of
the set of all values of `v (coeff t f) * ∏ i : t.support, c i` for all `t : σ →₀ ℕ`.

## Main Definitions and Results

* `MvPowerSeries.gaussNormC` is the supremum of the set of all values of
  `v (coeff t f) * ∏ i : t.support, c i`for all `t : σ →₀ ℕ`, where `f` is a multivariate power
  series, `v : R → ℝ` is a function and `c` is a tuple of real numbers.

* `MvPowerSeries.gaussNormC_nonneg`: if `v` is a non-negative function, then the Gauss norm is
  non-negative.

* `MvPowerSeries.gaussNormC_eq_zero_iff`: if `v` is a non-negative function and `v x = 0 ↔ x = 0`
  for all `x : R` and `c` is positive, then the Gauss norm is zero if and only if the power series
  is zero.

* `Mv.gaussNormC_nonarchimedean`: if `v` is a non-negative non-archimedean function and the set of
  values `v (coeff t f) * ∏ i : t.support, c i` is bounded above (similarily for `g`), then the
  Gauss norm is non-archimedean.
-/

@[expose] public section

namespace MvPowerSeries

variable {R σ : Type*} (v : R → ℝ) (c : σ → ℝ) (f : MvPowerSeries σ R)

/-- Given a multivariate power series `f` in, a function `v : R → ℝ` and a tuple `c` of real
  numbers, the Gauss norm is defined as the supremum of the set of all values of
  `v (coeff t f) * ∏ i : t.support, c i` for all `t : σ →₀ ℕ`. -/
noncomputable def gaussNorm [Semiring R] : ℝ :=
   ⨆ t : σ →₀ ℕ, v (coeff t f) * t.prod (c · ^ ·)

/-- We say `f` HasGaussNorm if the values `v (coeff t f) * ∏ i : t.support, c i` is bounded above,
  that is `gaussNormC f` is finite. -/
abbrev HasGaussNorm [Semiring R] :=
  BddAbove (Set.range (fun (t : σ →₀ ℕ) ↦ (v (coeff t f) * t.prod (c · ^ ·))))

@[simp]
theorem gaussNorm_zero [Semiring R] (vZero : v 0 = 0) : gaussNorm v c 0 = 0 := by simp [gaussNorm, vZero]

lemma le_gaussNorm [Semiring R] (hbd : HasGaussNorm v c f) (t : σ →₀ ℕ) :
    v (coeff t f) * t.prod (c · ^ ·) ≤ gaussNorm v c f := by
  apply le_ciSup hbd

theorem gaussNorm_nonneg [Semiring R] (vNonneg : ∀ a, v a ≥ 0) : 0 ≤ gaussNorm v c f := by
  rw [gaussNorm]
  by_cases h : HasGaussNorm v c f
  · trans v (constantCoeff f)
    · simp [vNonneg]
    · convert (le_gaussNorm v c f h 0)
      simp
  · simp [h]

theorem gaussNorm_neg [Ring R] (vNeg : ∀ x, v x = v (-x)) :
    gaussNorm v c (-f) = gaussNorm v c f := by
  simp_rw [gaussNorm]
  have (t : σ →₀ ℕ) : (coeff t) (-f) = - (coeff t) (f) := by rfl
  simp_rw [this, ← vNeg]

theorem gaussNorm_eq_zero_iff [Semiring R] (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0)
    (h_eq_zero : ∀ x : R, v x = 0 → x = 0) (hc : ∀ i, 0 < c i) (hbd : HasGaussNorm v c f) :
    gaussNorm v c f = 0 ↔ f = 0 := by
  refine ⟨?_, fun hf ↦ by simp [hf, vZero]⟩
  contrapose!
  intro hf
  apply ne_of_gt
  obtain ⟨n, hn⟩ := (MvPowerSeries.ne_zero_iff_exists_coeff_ne_zero f).mp hf
  calc
  0 < v (f.coeff n) * ∏ i ∈ n.support, (c i) ^ (n i) := by
    apply mul_pos _ (by exact Finset.prod_pos fun i a ↦ (fun i ↦ pow_pos (hc i) (n i)) i)
    specialize h_eq_zero (f.coeff n)
    grind
  _ ≤ _ := le_gaussNorm v c f hbd n

theorem gaussNorm_add_le_max [Semiring R] (f g : MvPowerSeries σ R) (hc : 0 ≤ c)
    (vNonneg : ∀ a, v a ≥ 0) (hv : ∀ x y, v (x + y) ≤ max (v x) (v y))
    (hbfd : HasGaussNorm v c f) (hbgd : HasGaussNorm v c g) :
    gaussNorm v c (f + g) ≤ max (gaussNorm v c f) (gaussNorm v c g) := by
  have H (t : σ →₀ ℕ) : 0 ≤ ∏ i ∈ t.support, c i ^ t i :=
    Finset.prod_nonneg (fun i hi ↦ pow_nonneg (hc i) (t i))
  have Final (t : σ →₀ ℕ) : v ((coeff t) (f + g)) * ∏ i ∈ t.support, c ↑i ^ t ↑i ≤
      max (v ((coeff t) f) * ∏ i ∈ t.support, c ↑i ^ t ↑i)
      (v ((coeff t) g) * ∏ i ∈ t.support, c ↑i ^ t ↑i) := by
    specialize hv (coeff t f) (coeff t g)
    rcases max_choice (v ((coeff t) f)) (v ((coeff t) g)) with h | h
    · have : max (v ((coeff t) f) * ∏ i ∈ t.support, c ↑i ^ t ↑i)
          (v ((coeff t) g) * ∏ i ∈ t.support, c ↑i ^ t ↑i) =
          (v ((coeff t) f) * ∏ i ∈ t.support, c ↑i ^ t ↑i) := by
        simp only [sup_eq_left]
        exact mul_le_mul_of_nonneg (by aesop) (by aesop) (by aesop) (H t)
      simp_rw [this]
      exact mul_le_mul_of_nonneg (by aesop) (by aesop) (by aesop) (H t)
    · have : max (v ((coeff t) f) * ∏ i ∈ t.support, c ↑i ^ t ↑i)
          (v ((coeff t) g) * ∏ i ∈ t.support, c ↑i ^ t ↑i) =
          (v ((coeff t) g) * ∏ i ∈ t.support, c ↑i ^ t ↑i) := by
        simp only [sup_eq_right]
        exact mul_le_mul_of_nonneg (by aesop) (by aesop) (by aesop) (H t)
      simp_rw [this]
      exact mul_le_mul_of_nonneg (by aesop) (by aesop) (by aesop) (H t)
  refine Real.iSup_le ?_ ?_
  · refine fun t ↦ calc
    _ ≤ _ := Final t
    _ ≤ max (gaussNorm v c f) (gaussNorm v c g) := by
      simp only [le_sup_iff]
      rcases max_choice (v ((coeff t) f) * ∏ i ∈ t.support, c i ^ t i)
        (v ((coeff t) g) * ∏ i ∈ t.support, c i ^ t i) with h | h
      · left
        simpa [h] using le_gaussNorm v c f hbfd t
      · right
        simpa [h] using le_gaussNorm v c g hbgd t
  · simp only [le_sup_iff]
    left
    exact gaussNorm_nonneg v c f vNonneg

lemma foo (hc : 0 ≤ c) (t : σ →₀ ℕ) : 0 ≤ t.prod (c · ^ ·) :=
  Finset.prod_nonneg (fun i _ ↦ pow_nonneg (hc i) (t i))

-- The following three are allowing me to state a version of `exists_norm_finset_prod_le` where
-- we weaken the need of Seminormedcommgroup

-- I could probably weaken R from a semiRing too...

-- this is a weakening of `Finset.Nonempty.norm_sum_le_sup'_norm`
lemma help'' [Semiring R] {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → R)
    (vUltra : ∀ a b, v (a + b) ≤ max (v a) (v b)) :
    v (∑ i ∈ s, f i) ≤ s.sup' hs fun x ↦ v (f x) := by
  simp only [Finset.le_sup'_iff]
  induction hs using Finset.Nonempty.cons_induction with
  | singleton j => simp only [Finset.mem_singleton, Finset.sum_singleton, exists_eq_left, le_refl]
  | cons j s hj _ IH =>
      simp only [Finset.sum_cons, Finset.mem_cons, exists_eq_or_imp]
      refine (le_total (v (∑ i ∈ s, f i)) (v (f j))).imp ?_ ?_ <;> intro h
      · exact (vUltra _ _).trans (max_eq_left h).le
      · exact ⟨_, IH.choose_spec.left, (vUltra _ _).trans <|
          ((max_eq_right h).le.trans IH.choose_spec.right)⟩

-- this is a weakening of `exists_norm_finset_prod_le_of_nonempty`
lemma help' [Semiring R] {ι : Type*} (vUltra : ∀ a b, v (a + b) ≤ max (v a) (v b)) {t : Finset ι}
    (ht : t.Nonempty) (f : ι → R) : ∃ i ∈ t, v (∑ j ∈ t, f j) ≤ v (f i) := by
  simpa [Finset.le_sup'_iff] using help'' v ht f vUltra

-- this is a weakening of `exists_norm_multiset_prod_le`
lemma help [Semiring R] {ι : Type*} (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0)
    (vUltra : ∀ a b, v (a + b) ≤ max (v a) (v b)) (t : Finset ι) [Nonempty ι]
    (f : ι → R) : ∃ i, (t.Nonempty → i ∈ t) ∧ v (∑ j ∈ t, f j) ≤ v (f i) := by
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simp [vZero, vNonneg]
  exact (fun ⟨i, h, h'⟩ => ⟨i, fun _ ↦ h, h'⟩) <| help' v vUltra ht f

lemma gaussNorm_le_mul [Semiring R] (f g : MvPowerSeries σ R) (hc : 0 ≤ c)  (vNonneg : ∀ a, v a ≥ 0)
    (vMul : ∀ a b, v (a * b) ≤ v a * v b) (vUltra : ∀ a b, v (a + b) ≤ max (v a) (v b))
    (vZero : v 0 = 0) (hbfd : HasGaussNorm v c f) (hbgd : HasGaussNorm v c g) :
    gaussNorm v c (f * g) ≤ gaussNorm v c f * gaussNorm v c g := by
  classical
  simp_rw [gaussNorm]
  refine Real.iSup_le ?_ ?_
  · intro t
    change (v (coeff t (f * g)) * t.prod fun x1 x2 ↦ c x1 ^ x2) ≤
      (⨆ t, v (coeff t f) * t.prod fun x1 x2 ↦ c x1 ^ x2) *
      ⨆ t, v (coeff t g) * t.prod fun x1 x2 ↦ c x1 ^ x2
    rw [coeff_mul]
    obtain ⟨k, hk, hsum⟩ := help v vZero vNonneg vUltra (Finset.antidiagonal t)
      (fun a ↦ coeff a.1 f * coeff a.2 g)
    have hk' : k.1 + k.2 = t := by
      simpa [Finset.mem_antidiagonal] using hk
        (Finset.nonempty_def.mpr ⟨(t, 0), by simp⟩)
    have hprod : t.prod (c · ^ ·) = k.1.prod (c · ^ ·) * k.2.prod (c · ^ ·) := by
      simp_rw [← hk']
      simp [Finsupp.prod_add_index', pow_add]
    simp_rw [hprod]
    have : v (∑ p ∈ Finset.antidiagonal t, (coeff p.1) f * (coeff p.2) g) *
        (k.1.prod (c · ^ ·) * k.2.prod (c · ^ ·)) ≤
        v ((coeff k.1) f * (coeff k.2) g) * (k.1.prod (c · ^ ·) * k.2.prod (c · ^ ·)) :=
      mul_le_mul hsum (by rfl) (mul_nonneg (foo c hc k.1) (foo c hc k.2)) (vNonneg _)
    refine this.trans ?_
    have : v ((coeff k.1) f * (coeff k.2) g) * (k.1.prod (c · ^ ·) * k.2.prod (c · ^ ·)) ≤
        (v (coeff k.1 f) * k.1.prod (c · ^ ·)) * (v (coeff k.2 g) * k.2.prod (c · ^ ·)) := by
      calc
      _ ≤ v (coeff k.1 f) * v (coeff k.2 g) * (k.1.prod (c · ^ ·) * k.2.prod (c · ^ ·)) :=
        mul_le_mul (vMul _ _) (by rfl) (mul_nonneg (foo c hc k.1) (foo c hc k.2))
          (mul_nonneg (vNonneg _) (vNonneg _))
      _ = _ := by ring
    refine this.trans ?_
    refine mul_le_mul ?_ ?_ ?_ ?_
    · exact le_gaussNorm v c f hbfd k.1
    · exact le_gaussNorm v c g hbgd k.2
    · exact mul_nonneg (vNonneg _) (foo c hc k.2)
    · exact gaussNorm_nonneg v c f vNonneg
  exact mul_nonneg (gaussNorm_nonneg v c f vNonneg) (gaussNorm_nonneg v c g vNonneg)

lemma restricted.HasGaussNorm [NormedRing R] [IsUltrametricDist R] (c : σ → ℝ) (f : Restricted R c) :
    HasGaussNorm norm c f.1 := by
  exact Filter.Tendsto.bddAbove_range_of_cofinite f.2

lemma ultrametric_strict [Ring R] (vUltra : ∀ a b, v (a + b) ≤ max (v a) (v b))
    (vNeg : ∀ a, v a = v (-a)) {a b : R}
    (hne : v a ≠ v b) : v (a + b) = max (v a) (v b) := by
  wlog hab : v a > v b generalizing a b with H
  · have hba : v b > v a := (not_lt.mp hab).lt_of_ne hne
    rw [add_comm, max_comm]
    exact H hne.symm hba
  apply le_antisymm (vUltra a b)
  rw [max_eq_left (le_of_lt hab)]
  have h1 : a = (a + b) + (-b) := by abel
  have h2 : v ((a + b) + (-b)) ≤ max (v (a + b)) (v (-b)) := vUltra _ _
  rw [← h1, ← vNeg b] at h2
  rcases le_max_iff.mp h2 with h | h
  · exact h
  · exact absurd h (not_le.mpr hab)

/-- An index achieves the Gauss norm supremum -/
def AchievesGaussNorm [Semiring R] (i : σ →₀ ℕ) : Prop :=
  v (coeff i f) * i.prod (c · ^ ·) = gaussNorm v c f

lemma antidiagonal_dominant' [Ring R] [DecidableEq σ] (f g : MvPowerSeries σ R) (i j : σ →₀ ℕ)
    (hc : 0 ≤ c) (vUltra : ∀ a b, v (a + b) ≤ max (v a) (v b))
    (vMulEq : ∀ a b, v (a * b) = v a * v b)
    (vNeg : ∀ a, v a = v (-a))
    (hdom : ∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
        v (coeff p.1 f * coeff p.2 g) * (p.1 + p.2).prod (c · ^ ·) <
        v (coeff i f) * v (coeff j g) * (i + j).prod (c · ^ ·)) :
    v (coeff (i + j) (f * g)) * (i + j).prod (c · ^ ·) =
    v (coeff i f * coeff j g) * (i + j).prod (c · ^ ·) := by
  let K : ℝ := (i + j).prod (c · ^ ·)
  have hKnonneg : 0 ≤ K := by
    simpa [K] using foo c hc (i + j)
  by_cases hK0 : K = 0
  · simp [K, hK0]
  · have hKpos : 0 < K := lt_of_le_of_ne hKnonneg (Ne.symm hK0)
    have hdom' : ∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
        v (coeff p.1 f * coeff p.2 g) < v (coeff i f * coeff j g) := by
      intro p hp hpne
      have hsump : p.1 + p.2 = i + j := by
        simpa [Finset.mem_antidiagonal] using hp
      have hltK : v (coeff p.1 f * coeff p.2 g) * K <
          (v (coeff i f) * v (coeff j g)) * K := by
        simpa [K, hsump] using hdom p hp hpne
      have hlt : v (coeff p.1 f * coeff p.2 g) < v (coeff i f) * v (coeff j g) :=
        lt_of_mul_lt_mul_right hltK (le_of_lt hKpos)
      simpa [vMulEq] using hlt
    have hcoeff :  v (coeff (i + j) (f * g)) = v (coeff i f * coeff j g) := by
      rw [coeff_mul]
      have hmem : (i, j) ∈ Finset.antidiagonal (i + j) := by simp [Finset.mem_antidiagonal]
      -- Check if antidiagonal has only one element
      by_cases hcard : (Finset.antidiagonal (i + j)).card = 1
      · -- Singleton case
        have hsing : Finset.antidiagonal (i + j) = {(i, j)} := by
          apply Finset.eq_singleton_iff_unique_mem.mpr
          exact ⟨hmem, fun y hy => by
            obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
            simp only [ha, Finset.mem_singleton] at hy hmem ⊢
            exact hy.trans hmem.symm⟩
        simp only [hsing, Finset.sum_singleton]
      · -- Multiple elements: use strict ultrametric
        have heq : ∑ p ∈ Finset.antidiagonal (i + j), coeff p.1 f * coeff p.2 g =
            coeff i f * coeff j g +
            ∑ p ∈ (Finset.antidiagonal (i + j)).erase (i, j), coeff p.1 f * coeff p.2 g := by
          rw [← Finset.add_sum_erase _ _ hmem]
        rw [heq]
        -- Erased set is nonempty since card ≥ 2
        have hemp : ((Finset.antidiagonal (i + j)).erase (i, j)).Nonempty := by
          have hne : Finset.antidiagonal (i + j) ≠ ∅ := Finset.ne_empty_of_mem hmem
          have hnsing : Finset.antidiagonal (i + j) ≠ {(i, j)} := fun h => by simp [h] at hcard
          rw [Finset.nonempty_iff_ne_empty, ne_eq, Finset.erase_eq_empty_iff, not_or]
          exact ⟨hne, hnsing⟩
        -- Get max element in erased set
        have hmax := Finset.exists_max_image _ (fun p => v (coeff p.1 f * coeff p.2 g)) hemp
        obtain ⟨m, hm, hvm⟩ := hmax
        -- The rest term's v-value is bounded by max element's v-value (ultrametric)
        have hrest_le : v (∑ p ∈ (Finset.antidiagonal (i + j)).erase (i, j), coeff p.1 f * coeff p.2 g)
            ≤ v (coeff m.1 f * coeff m.2 g) := by
          have hle := help'' v hemp (fun p => coeff p.1 f * coeff p.2 g) vUltra
          have hsup_le : ((Finset.antidiagonal (i + j)).erase (i, j)).sup' hemp
              (fun x => v (coeff x.1 f * coeff x.2 g)) ≤ v (coeff m.1 f * coeff m.2 g) :=
            Finset.sup'_le hemp _ (fun x hx => hvm x hx)
          exact hle.trans hsup_le
        have hrest_lt : v (∑ p ∈ (Finset.antidiagonal (i + j)).erase (i, j),
            coeff p.1 f * coeff p.2 g) < v (coeff i f * coeff j g) :=
          hrest_le.trans_lt (hdom' m (Finset.mem_of_mem_erase hm) (Finset.ne_of_mem_erase hm))
        have hne : v (coeff i f * coeff j g) ≠
            v (∑ p ∈ (Finset.antidiagonal (i + j)).erase (i, j), coeff p.1 f * coeff p.2 g) :=
          ne_of_gt hrest_lt
        rw [ultrametric_strict v vUltra vNeg hne, max_eq_left (le_of_lt hrest_lt)]
    simpa [K] using congrArg (fun x : ℝ => x * K) hcoeff

lemma gaussNorm_mul_le [Ring R] [DecidableEq σ] (f g : MvPowerSeries σ R)
    (hc : 0 ≤ c)
    (vMulEq : ∀ a b, v (a * b) = v a * v b) (vUltra : ∀ a b, v (a + b) ≤ max (v a) (v b))
    (vNeg : ∀ a, v a = v (-a)) (hbfg : HasGaussNorm v c (f * g))
    (hdom : ∃ i j, AchievesGaussNorm v c f i ∧ AchievesGaussNorm v c g j ∧
      ∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
        v (coeff p.1 f * coeff p.2 g) * (p.1 + p.2).prod (c · ^ ·) <
        v (coeff i f) * v (coeff j g) * (i + j).prod (c · ^ ·)) :
    gaussNorm v c f * gaussNorm v c g ≤ gaussNorm v c (f * g) := by
  obtain ⟨i₀, j₀, hi₀, hj₀, hdom'⟩ := hdom
  have hcoeff_eq :=
    antidiagonal_dominant' v c f g i₀ j₀ hc vUltra vMulEq vNeg hdom'
  unfold AchievesGaussNorm at hi₀ hj₀
  calc
    _  = (v (coeff i₀ f) * i₀.prod (c · ^ ·)) * (v (coeff j₀ g) * j₀.prod (c · ^ ·)) := by
          rw [← hi₀, ← hj₀]
    _ = v (coeff i₀ f) * v (coeff j₀ g) * ((i₀ + j₀).prod (c · ^ ·)) := by
          have hprod : (i₀ + j₀).prod (c · ^ ·) = i₀.prod (c · ^ ·) * j₀.prod (c · ^ ·) := by
            simp [Finsupp.prod_add_index', pow_add]
          rw [hprod]; ring
    _ = v (coeff i₀ f * coeff j₀ g) * (i₀ + j₀).prod (c · ^ ·) := by rw [vMulEq]
    _ = v (coeff (i₀ + j₀) (f * g)) * (i₀ + j₀).prod (c · ^ ·) := by rw [hcoeff_eq]
    _ ≤ gaussNorm v c (f * g) := le_gaussNorm v c (f * g) hbfg (i₀ + j₀)


lemma gaussNorm_achieved [NormedRing R] [IsUltrametricDist R] (hc : 0 ≤ c) (f : Restricted R c) :
    ∃ a, ‖coeff a f.1‖ * a.prod (c · ^ ·) = gaussNorm norm c f.1 := by
  by_cases hG : gaussNorm norm c f.1 = 0
  · use 0
    have := le_gaussNorm norm c f.1 (restricted.HasGaussNorm c f) 0
    simp only [hG] at this ⊢
    exact le_antisymm this (mul_nonneg (norm_nonneg _) (foo c hc 0))
  · have hpos : 0 < gaussNorm norm c f.1 :=
      (gaussNorm_nonneg norm c f.1 norm_nonneg).lt_of_ne' hG
    have hfin : {t | gaussNorm norm c f.1 / 2 ≤ ‖coeff t f.1‖ * t.prod (c · ^ ·)}.Finite := by
      have : IsRestricted R c f.1 := f.2
      simp_rw [IsRestricted, NormedAddCommGroup.tendsto_nhds_zero] at this
      have := this (gaussNorm norm c f.1 / 2) (by aesop)
      simp only [norm_mul, Real.norm_eq_abs, Filter.eventually_cofinite, not_lt, abs_norm] at this
      convert this with t
      grind [foo c hc t]
    have hne : {t | gaussNorm norm c f.1 / 2 ≤ ‖coeff t f.1‖ * t.prod (c · ^ ·)}.Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have hlt : gaussNorm norm c f.1 ≤ gaussNorm norm c f.1 / 2 := by
        apply ciSup_le
        intro t
        have : t ∉ {t | gaussNorm norm c f.1 / 2 ≤ ‖coeff t f.1‖ * t.prod (c · ^ ·)} := by
          simp [hemp]
        grind
      linarith
    obtain ⟨m, hm_mem, hm_max⟩ := hfin.toFinset.exists_max_image
      (fun t ↦ ‖coeff t f.1‖ * t.prod (c · ^ ·)) (by aesop)
    use m
    apply le_antisymm (le_gaussNorm norm c f.1 (restricted.HasGaussNorm c f) m)
    apply ciSup_le
    intro t
    by_cases ht : t ∈ {t | gaussNorm norm c f.1 / 2 ≤ ‖coeff t f.1‖ * t.prod (c · ^ ·)}
    · exact hm_max t (by aesop)
    · exact le_trans (le_of_lt (by aesop)) (by aesop)

-- now want a lemma saying that the set of achieving points is finite (guarenteed by restricted condition)

lemma achievingPoints_finite [NormedRing R] [IsUltrametricDist R] (hc : 0 ≤ c) (f : Restricted R c)
    (h : gaussNorm norm c f.1 ≠ 0) :
    {a | ‖coeff a f.1‖ * a.prod (c · ^ ·) = gaussNorm norm c f.1}.Finite := by
  have hpos : 0 < gaussNorm norm c f.1 :=
      (gaussNorm_nonneg norm c f.1 norm_nonneg).lt_of_ne' h
  have hfin : {t | gaussNorm norm c f.1 / 2 ≤ ‖coeff t f.1‖ * t.prod (c · ^ ·)}.Finite := by
      have : IsRestricted R c f.1 := f.2
      simp_rw [IsRestricted, NormedAddCommGroup.tendsto_nhds_zero] at this
      have := this (gaussNorm norm c f.1 / 2) (by aesop)
      simp only [norm_mul, Real.norm_eq_abs, Filter.eventually_cofinite, not_lt, abs_norm] at this
      convert this with t
      grind [foo c hc t]
  refine Set.Finite.subset hfin ?_
  grind

lemma test (hc : ∀ (i : σ), 0 < c i) : 0 ≤ c := by
  intro i
  exact Std.le_of_lt (hc i)

lemma bar [NormedRing R] [IsUltrametricDist R] [LinearOrder σ]
    (hc : ∀ i, 0 < c i) (f g : Restricted R c)
    (hf : gaussNorm norm c f.1 ≠ 0) (hg : gaussNorm norm c g.1 ≠ 0) :
    ∃ i j, AchievesGaussNorm norm c f.1 i ∧ AchievesGaussNorm norm c g.1 j ∧
      ∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
        norm (coeff p.1 f.1 * coeff p.2 g.1) * (p.1 + p.2).prod (c · ^ ·) <
        norm (coeff i f.1) * norm (coeff j g.1) * (i + j).prod (c · ^ ·) := by
  classical
  let Sf : Set (σ →₀ ℕ) := {a | ‖coeff a f.1‖ * a.prod (c · ^ ·) = gaussNorm norm c f.1}
  let Sg : Set (σ →₀ ℕ) := {a | ‖coeff a g.1‖ * a.prod (c · ^ ·) = gaussNorm norm c g.1}
  have hSf_fin : Sf.Finite :=
    achievingPoints_finite (R := R) (σ := σ) (c := c) (hc := test c hc) f hf
  have hSg_fin : Sg.Finite :=
    achievingPoints_finite (R := R) (σ := σ) (c := c) (hc := test c hc) g hg
  obtain ⟨if0, hif0⟩ :=
    gaussNorm_achieved (R := R) (σ := σ) (c := c) (hc := test c hc) f
  obtain ⟨ig0, hig0⟩ :=
    gaussNorm_achieved (R := R) (σ := σ) (c := c) (hc := test c hc) g
  have hSf_ne : (hSf_fin.toFinset).Nonempty := by
    refine ⟨if0, ?_⟩
    exact (Set.Finite.mem_toFinset hSf_fin).2 (by simpa [Sf] using hif0)
  have hSg_ne : (hSg_fin.toFinset).Nonempty := by
    refine ⟨ig0, ?_⟩
    exact (Set.Finite.mem_toFinset hSg_fin).2 (by simpa [Sg] using hig0)
  obtain ⟨i, hi_mem, hi_max⟩ :=
    (hSf_fin.toFinset).exists_max_image (fun a : σ →₀ ℕ ↦ toLex a) hSf_ne
  obtain ⟨j, hj_mem, hj_max⟩ :=
    (hSg_fin.toFinset).exists_max_image (fun a : σ →₀ ℕ ↦ toLex a) hSg_ne
  have hi : AchievesGaussNorm norm c f.1 i := by
    exact (Set.Finite.mem_toFinset hSf_fin).1 (by simpa [Sf] using hi_mem)
  have hj : AchievesGaussNorm norm c g.1 j := by
    exact (Set.Finite.mem_toFinset hSg_fin).1 (by simpa [Sg] using hj_mem)
  refine ⟨i, j, hi, hj, ?_⟩
  intro p hp hpne
  have hsump : p.1 + p.2 = i + j := by
    simpa [Finset.mem_antidiagonal] using hp
  have hc0 : 0 ≤ c := test c hc
  have hfoo1 (t : σ →₀ ℕ) : 0 ≤ t.prod (c · ^ ·) := foo c hc0 t
  have hle1 : ‖coeff p.1 f.1‖ * p.1.prod (c · ^ ·) ≤ ‖coeff i f.1‖ * i.prod (c · ^ ·) := by
    calc
      ‖coeff p.1 f.1‖ * p.1.prod (c · ^ ·) ≤ gaussNorm norm c f.1 :=
        le_gaussNorm norm c f.1 (restricted.HasGaussNorm c f) p.1
      _ = ‖coeff i f.1‖ * i.prod (c · ^ ·) := by
        simpa [AchievesGaussNorm] using hi.symm
  have hle2 : ‖coeff p.2 g.1‖ * p.2.prod (c · ^ ·) ≤ ‖coeff j g.1‖ * j.prod (c · ^ ·) := by
    calc
      ‖coeff p.2 g.1‖ * p.2.prod (c · ^ ·) ≤ gaussNorm norm c g.1 :=
        le_gaussNorm norm c g.1 (restricted.HasGaussNorm c g) p.2
      _ = ‖coeff j g.1‖ * j.prod (c · ^ ·) := by
        simpa [AchievesGaussNorm] using hj.symm
  have hi_nonneg : 0 ≤ ‖coeff i f.1‖ * i.prod (c · ^ ·) :=
    mul_nonneg (norm_nonneg _) (hfoo1 i)
  have hj_nonneg : 0 ≤ ‖coeff j g.1‖ * j.prod (c · ^ ·) :=
    mul_nonneg (norm_nonneg _) (hfoo1 j)
  have hpi_nonneg : 0 ≤ ‖coeff p.1 f.1‖ * p.1.prod (c · ^ ·) :=
    mul_nonneg (norm_nonneg _) (hfoo1 p.1)
  have hpj_nonneg : 0 ≤ ‖coeff p.2 g.1‖ * p.2.prod (c · ^ ·) :=
    mul_nonneg (norm_nonneg _) (hfoo1 p.2)
  have hstrict_or :
      ‖coeff p.1 f.1‖ * p.1.prod (c · ^ ·) < ‖coeff i f.1‖ * i.prod (c · ^ ·) ∨
      ‖coeff p.2 g.1‖ * p.2.prod (c · ^ ·) < ‖coeff j g.1‖ * j.prod (c · ^ ·) := by
    by_cases h1 : ‖coeff p.1 f.1‖ * p.1.prod (c · ^ ·) < ‖coeff i f.1‖ * i.prod (c · ^ ·)
    · exact Or.inl h1
    · have h1eq : ‖coeff p.1 f.1‖ * p.1.prod (c · ^ ·) = ‖coeff i f.1‖ * i.prod (c · ^ ·) :=
        le_antisymm hle1 (le_of_not_gt h1)
      by_cases h2 : ‖coeff p.2 g.1‖ * p.2.prod (c · ^ ·) < ‖coeff j g.1‖ * j.prod (c · ^ ·)
      · exact Or.inr h2
      · have h2eq : ‖coeff p.2 g.1‖ * p.2.prod (c · ^ ·) = ‖coeff j g.1‖ * j.prod (c · ^ ·) :=
          le_antisymm hle2 (le_of_not_gt h2)
        have hp1_ach : p.1 ∈ hSf_fin.toFinset := by
          exact (Set.Finite.mem_toFinset hSf_fin).2
            (by simpa [Sf] using h1eq.trans (by simpa [AchievesGaussNorm] using hi))
        have hp2_ach : p.2 ∈ hSg_fin.toFinset := by
          exact (Set.Finite.mem_toFinset hSg_fin).2
            (by simpa [Sg] using h2eq.trans (by simpa [AchievesGaussNorm] using hj))
        have hp1_le_i : toLex p.1 ≤ toLex i := hi_max p.1 hp1_ach
        have hp2_le_j : toLex p.2 ≤ toLex j := hj_max p.2 hp2_ach
        have hp1_eq_i : p.1 = i := by
          by_contra hne
          have hp1_lt_i : toLex p.1 < toLex i := lt_of_le_of_ne hp1_le_i (by simpa using hne)
          have hsumLex : toLex p.1 + toLex p.2 = toLex i + toLex j := by
            simpa [toLex_add] using congrArg toLex hsump
          have hlt_sum : toLex i + toLex j < toLex i + toLex p.2 := by
            calc
              toLex i + toLex j = toLex p.1 + toLex p.2 := hsumLex.symm
              _ < toLex i + toLex p.2 := by
                simpa [add_comm, add_left_comm, add_assoc] using
                  add_lt_add_left hp1_lt_i (toLex p.2)
          have hj_lt_p2 : toLex j < toLex p.2 := lt_of_add_lt_add_left hlt_sum
          exact (not_lt_of_ge hp2_le_j) hj_lt_p2
        have hp2_eq_j : p.2 = j := by
          simpa [hp1_eq_i] using hsump
        exact (hpne (Prod.ext hp1_eq_i hp2_eq_j)).elim
  have hmul_strict :
      (‖coeff p.1 f.1‖ * p.1.prod (c · ^ ·)) * (‖coeff p.2 g.1‖ * p.2.prod (c · ^ ·)) <
      (‖coeff i f.1‖ * i.prod (c · ^ ·)) * (‖coeff j g.1‖ * j.prod (c · ^ ·)) := by
    have hi_pos : 0 < ‖coeff i f.1‖ * i.prod (c · ^ ·) := by
      have hgf_pos : 0 < gaussNorm norm c f.1 :=
        (gaussNorm_nonneg norm c f.1 norm_nonneg).lt_of_ne' hf
      simpa [AchievesGaussNorm] using (hi.symm ▸ hgf_pos)
    have hj_pos : 0 < ‖coeff j g.1‖ * j.prod (c · ^ ·) := by
      have hgg_pos : 0 < gaussNorm norm c g.1 :=
        (gaussNorm_nonneg norm c g.1 norm_nonneg).lt_of_ne' hg
      simpa [AchievesGaussNorm] using (hj.symm ▸ hgg_pos)
    rcases hstrict_or with hlt1 | hlt2
    · exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos hlt1 hle2 hpi_nonneg hj_pos
    · exact mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hle1 hlt2 hpj_nonneg hi_pos
  have hprod_p : (p.1 + p.2).prod (c · ^ ·) = p.1.prod (c · ^ ·) * p.2.prod (c · ^ ·) := by
    simp [Finsupp.prod_add_index', pow_add]
  have hprod_ij : (i + j).prod (c · ^ ·) = i.prod (c · ^ ·) * j.prod (c · ^ ·) := by
    simp [Finsupp.prod_add_index', pow_add]
  have hfinal :
      norm (coeff p.1 f.1 * coeff p.2 g.1) * (p.1 + p.2).prod (c · ^ ·) <
      norm (coeff i f.1) * norm (coeff j g.1) * (i + j).prod (c · ^ ·) := by
    calc
      norm (coeff p.1 f.1 * coeff p.2 g.1) * (p.1 + p.2).prod (c · ^ ·)
        ≤ (‖coeff p.1 f.1‖ * ‖coeff p.2 g.1‖) * (p.1 + p.2).prod (c · ^ ·) := by
              exact mul_le_mul_of_nonneg_right
                (norm_mul_le (coeff p.1 f.1) (coeff p.2 g.1))
                (hfoo1 (p.1 + p.2))
      _ = (‖coeff p.1 f.1‖ * p.1.prod (c · ^ ·)) * (‖coeff p.2 g.1‖ * p.2.prod (c · ^ ·)) := by
        rw [hprod_p]
        ring
      _ < (‖coeff i f.1‖ * i.prod (c · ^ ·)) * (‖coeff j g.1‖ * j.prod (c · ^ ·)) := hmul_strict
      _ = norm (coeff i f.1) * norm (coeff j g.1) * (i + j).prod (c · ^ ·) := by
            rw [hprod_ij]
            ring
  exact hfinal


section norm

noncomputable
instance isRingNorm [NormedRing R] [IsUltrametricDist R] (hc : ∀ (i : σ), 0 < c i) :
    RingNorm (Restricted R c) where
  toFun f := gaussNorm norm c f.1
  map_zero' := gaussNorm_zero norm c norm_zero
  add_le' f g := by
    have h := gaussNorm_add_le_max norm c f.1 g.1 (test c hc) norm_nonneg
      (IsUltrametricDist.norm_add_le_max) (restricted.HasGaussNorm c f)
      (restricted.HasGaussNorm c g)
    have :  max (gaussNorm norm c f.1) (gaussNorm norm c g.1) ≤
        gaussNorm norm c f.1 + gaussNorm norm c g.1 := by
      refine max_le_add_of_nonneg ?_ ?_
      all_goals exact (gaussNorm_nonneg norm c _ norm_nonneg)
    exact h.trans this
  neg' f := gaussNorm_neg norm c f.1 (by aesop)
  mul_le' f g := gaussNorm_le_mul norm c f.1 g.1 (test c hc) norm_nonneg norm_mul_le
    IsUltrametricDist.norm_add_le_max norm_zero (restricted.HasGaussNorm c f)
    (restricted.HasGaussNorm c g)
    -- need to change my names around of mul_le and le_mul
  eq_zero_of_map_eq_zero' f := by
    simpa using (gaussNorm_eq_zero_iff norm c f.1 norm_zero norm_nonneg (by aesop) hc
      (restricted.HasGaussNorm c f)).mp

noncomputable
instance isNormedRing  [NormedRing R] [IsUltrametricDist R] (hc : ∀ i, 0 < c i) :
    NormedRing (Restricted R c) :=
  RingNorm.toNormedRing (isRingNorm c hc)

noncomputable
instance isNonarchimedean [NormedRing R] [IsUltrametricDist R] (hc : ∀ i, 0 < c i) :
    letI : NormedRing (Restricted R c) := isNormedRing (R := R) (c := c) hc
    IsNonarchimedean (R := ℝ) (α := Restricted R c) norm :=
  fun f g => gaussNorm_add_le_max norm c f.1 g.1 (test c hc) norm_nonneg
    IsUltrametricDist.norm_add_le_max (restricted.HasGaussNorm c f) (restricted.HasGaussNorm c g)

noncomputable -- ie it does work but its not able to infer below??
example [NormedRing R] [IsUltrametricDist R] (hc : ∀ i, 0 < c i) : Dist (Restricted R c) := by
  letI : NormedRing (Restricted R c) := isNormedRing (R := R) (c := c) hc
  infer_instance


noncomputable
instance (priority := high) isUltrametricDist
    [NormedRing R] [IsUltrametricDist R] (hc : ∀ i, 0 < c i) :
    IsUltrametricDist (Restricted R c) where
  dist_triangle_max f g :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean (R := R) (c := c) hc)

-- not sure what the correct assumption on hnorm should be
-- valued ring?? ... I need the norm to be mulitplicative (i.e. an absolute value)
noncomputable
instance isAbsoluteValue [NormedRing R] [IsUltrametricDist R] [LinearOrder σ]
    (hc : ∀ (i : σ), 0 < c i) (hnorm : ∀ a b : R, norm (a * b) = norm a * norm b) :
    AbsoluteValue (Restricted R c) ℝ where
  toFun f := gaussNorm norm c f.1
  map_mul' f g := by
    by_cases hf : f = 0
    · aesop
    by_cases hg : g = 0
    · aesop
    have hf1 : gaussNorm norm c f.1 ≠ 0 := by
      contrapose hf
      convert (gaussNorm_eq_zero_iff norm c f.1 norm_zero norm_nonneg (by aesop) hc
        (restricted.HasGaussNorm c f)).mp hf
      simp
    have hg1 : gaussNorm norm c g.1 ≠ 0 := by
      contrapose hg
      convert (gaussNorm_eq_zero_iff norm c g.1 norm_zero norm_nonneg (by aesop) hc
        (restricted.HasGaussNorm c g)).mp hg
      simp
    apply ge_antisymm_iff.mpr
    exact ⟨gaussNorm_mul_le norm c f.1 g.1 (test c hc) hnorm IsUltrametricDist.norm_add_le_max
      (by aesop) (restricted.HasGaussNorm c (f * g)) (bar c hc f g hf1 hg1),
      gaussNorm_le_mul norm c f.1 g.1 (test c hc) norm_nonneg norm_mul_le
      IsUltrametricDist.norm_add_le_max norm_zero (restricted.HasGaussNorm c f)
      (restricted.HasGaussNorm c g)⟩
  nonneg' f := gaussNorm_nonneg norm c f.1 norm_nonneg
  eq_zero' f := by
    simpa using gaussNorm_eq_zero_iff norm c f.1 norm_zero norm_nonneg (by aesop) hc
      (restricted.HasGaussNorm c f)
  add_le' f g := by
    have h := gaussNorm_add_le_max norm c f.1 g.1 (test c hc) norm_nonneg
      (IsUltrametricDist.norm_add_le_max) (restricted.HasGaussNorm c f)
      (restricted.HasGaussNorm c g)
    have :  max (gaussNorm norm c f.1) (gaussNorm norm c g.1) ≤
        gaussNorm norm c f.1 + gaussNorm norm c g.1 := by
      refine max_le_add_of_nonneg ?_ ?_
      all_goals exact (gaussNorm_nonneg norm c _ norm_nonneg)
    exact h.trans this

end norm

end MvPowerSeries
