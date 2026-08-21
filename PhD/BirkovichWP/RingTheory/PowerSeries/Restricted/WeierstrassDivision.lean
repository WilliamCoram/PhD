/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.PowerSeries.Trunc
import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.Complete
import PhD.BirkovichWP.RingTheory.PowerSeries.Restricted.Distinguished
import PhD.BirkovichWP.RingTheory.PowerSeries.Restricted.GaussNorm
import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.DivisionSet
import PhD.BirkovichWP.RingTheory.PowerSeries.Restricted.Rescale
import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.Residue
import PhD.ForMathlib.Topology.MetricSpace.HausdorffDistance

/-! # Weierstrass division for restricted power series: bounds, uniqueness, division set

Let `R` be a normed commutative ring with ultrametric distance and multiplicative norm, and
let `g : Restricted R c` be distinguished of degree `s`.  **Weierstrass division** states
that every `f : Restricted R c` is uniquely `f = g * q + r` with `r` a polynomial of degree
`< s`.  This file is the **shared core** of the theory:

* the **division bounds** `‖q‖ ≤ ‖g‖⁻¹ * ‖f‖`, `‖r‖ ≤ ‖f‖` and **quotient/remainder
  uniqueness**, at an arbitrary radius `c`, with direct weighted-norm proofs and no auxiliary
  hypotheses;
* the **division set** `divisionSet g s = {g * q + r}`, an additive subgroup which is
  **closed** (`isClosed_divisionSet`): the division bounds make quotient and remainder
  sequences Cauchy along a convergent sequence of divisible elements;
* the **strictly-dominated existence** engine `weierstrassDivision_exists_of_forall_lt` (via
  `AddSubgroup.dense_of_infDist_le`, BGR 1.1.4/2), applicable when the dominant Gauss term
  strictly dominates every other, and the completeness-free Euclidean
  `weierstrassDivision_polynomial`.

**Existence in general.** The canonical existence theorem — over any complete ultrametric
normed commutative ring, no scaling or norm-one hypotheses — is the extension-free Martin
proof `MulWeierstrassDivision.weierstrassDivision_exists_of_isMulDistinguished`, which reuses
the closedness and bounds proved here.  The older residue-field (radius-`1`) existence engine
now lives in `PhD.BirkovichWP.…PowerSeries.Restricted.WeierstrassDivisionOracle`.
-/

open Filter PowerBounded
open scoped Topology

namespace PowerSeries.Restricted

/-! ## Division bounds and uniqueness, at an arbitrary radius -/

section Bounds

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] (c : ℝ)
  [Fact (0 < c)]

private lemma norm_coeff_mul_pow_eq_of_dominant {g q : Restricted R c} {s j : ℕ}
    (hg : IsDistinguished norm c g.1 s) (hj : AchievesGaussNorm norm c q.1 j)
    (hdom : ∀ p ∈ Finset.antidiagonal (s + j), p ≠ (s, j) →
        ‖coeff p.1 g.1 * coeff p.2 q.1‖ < ‖coeff s g.1‖ * ‖coeff j q.1‖) :
    ‖coeff (s + j) (g * q).1‖ * c ^ (s + j) = ‖g‖ * ‖q‖ := by
  change ‖coeff (s + j) (g.1 * q.1)‖ * c ^ (s + j) = ‖g‖ * ‖q‖
  calc ‖coeff (s + j) (g.1 * q.1)‖ * c ^ (s + j)
      = ‖coeff s g.1 * coeff j q.1‖ * c ^ (s + j) := by
        rw [PowerSeries.coeff_mul, IsNonarchimedean.apply_sum_eq_of_lt
          (fun x y ↦ IsUltrametricDist.norm_add_le_max x y) (fun a ↦ (norm_neg a).symm)
          (k := (s, j)) (Finset.mem_antidiagonal.mpr rfl)
          (fun p hp hpne ↦ (hdom p hp hpne).trans_eq (norm_mul _ _).symm)]
    _ = (‖coeff s g.1‖ * c ^ s) * (‖coeff j q.1‖ * c ^ j) := by rw [norm_mul, pow_add]; ring
    _ = ‖g‖ * ‖q‖ := by rw [hg.norm_coeff_mul_pow_eq, hj.trans (norm_def c q).symm]

/-- The core estimate behind the division bounds: in a Weierstrass division `f = g * q + r`,
the norm of `f` dominates both `‖g * q‖` and `‖r‖`.  This is the Gauss-term form of the
reduction argument of BGR 5.2.1/2: at the dominant pair of achieving indices of `(g, q)` —
whose `g`-component is the distinguished degree `s`, the *largest* achieving index of `g` —
the coefficient of `g * q` attains `‖g‖ * ‖q‖`, and it survives in `f` because `r` has no
coefficients at degrees `≥ s`. -/
theorem max_le_norm_of_eq_mul_add {g : Restricted R c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s) {f q : Restricted R c} {r : Polynomial R}
    (hr : r.degree < s) (hf : f = g * q + Polynomial.toRestricted c r) :
    max ‖g * q‖ ‖Polynomial.toRestricted c r‖ ≤ ‖f‖ := by
  by_cases hq0 : q = 0
  · subst hq0
    rw [mul_zero, zero_add] at hf
    rw [hf, mul_zero, norm_zero]
    exact max_le (norm_nonneg _) le_rfl
  obtain ⟨i, j, hi, hj, hdom, hi_max, -⟩ :=
    exists_achievesGaussNorm_dominant_max c (Fact.out : (0 : ℝ) < c).le g q hg.norm_pos.ne'
      (norm_pos_iff.mpr hq0).ne'
  obtain rfl : s = i :=
    le_antisymm (hi_max s hg.achievesGaussNorm) (hg.le_of_achievesGaussNorm hi)
  have h_peak := norm_coeff_mul_pow_eq_of_dominant c hg hj hdom
  have h_toR_zero : coeff (s + j) (Polynomial.toRestricted c r).1 = 0 := by
    rw [Polynomial.val_toRestricted, Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_degree_lt (hr.trans_le (mod_cast Nat.le_add_right s j))
  have h_coeff_f : ‖coeff (s + j) f.1‖ * c ^ (s + j) = ‖g‖ * ‖q‖ := by
    rw [show f.1 = (g * q).1 + (Polynomial.toRestricted c r).1 from by rw [hf]; rfl,
      map_add, h_toR_zero, add_zero]
    exact h_peak
  have h_gq_bd : ‖g * q‖ ≤ ‖f‖ := by
    rw [norm_mul, ← h_coeff_f]
    exact norm_coeff_mul_pow_le c f (s + j)
  refine max_le h_gq_bd ?_
  rw [show Polynomial.toRestricted c r = f - g * q from by rw [hf]; abel]
  refine (?_ : ‖f - g * q‖ ≤ max ‖f‖ ‖g * q‖).trans (max_le le_rfl h_gq_bd)
  simpa [norm_neg, sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max f (-(g * q))

/-- The quotient bound in a Weierstrass division: `‖q‖ ≤ ‖g‖⁻¹ * ‖f‖`. -/
theorem norm_q_le_of_eq_mul_add {g : Restricted R c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s) {f q : Restricted R c} {r : Polynomial R}
    (hr : r.degree < s) (hf : f = g * q + Polynomial.toRestricted c r) :
    ‖q‖ ≤ ‖g‖⁻¹ * ‖f‖ := by
  rw [le_inv_mul_iff₀ hg.norm_pos, ← norm_mul]
  exact (le_max_left _ _).trans (max_le_norm_of_eq_mul_add c hg hr hf)

/-- The remainder bound in a Weierstrass division: `‖r‖ ≤ ‖f‖`. -/
theorem norm_r_le_of_eq_mul_add {g : Restricted R c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s) {f q : Restricted R c} {r : Polynomial R}
    (hr : r.degree < s) (hf : f = g * q + Polynomial.toRestricted c r) :
    ‖Polynomial.toRestricted c r‖ ≤ ‖f‖ :=
  (le_max_right _ _).trans (max_le_norm_of_eq_mul_add c hg hr hf)

/-- The quotient in a Weierstrass division is unique. -/
theorem weierstrassDivision_q_unique {g : Restricted R c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s) {f : Restricted R c}
    {q₁ q₂ : Restricted R c} {r₁ r₂ : Polynomial R}
    (hr₁ : r₁.degree < s) (hf₁ : f = g * q₁ + Polynomial.toRestricted c r₁)
    (hr₂ : r₂.degree < s) (hf₂ : f = g * q₂ + Polynomial.toRestricted c r₂) : q₁ = q₂ := by
  have h0 : (0 : Restricted R c) = g * (q₁ - q₂) + Polynomial.toRestricted c (r₁ - r₂) := by
    rw [map_sub]
    linear_combination hf₁ - hf₂
  have h_bd := norm_q_le_of_eq_mul_add c hg
    ((Polynomial.degree_sub_le _ _).trans_lt (max_lt hr₁ hr₂)) h0
  rwa [norm_zero, mul_zero, norm_le_zero_iff, sub_eq_zero] at h_bd

/-- The remainder in a Weierstrass division is unique: it is determined by the quotient
uniqueness (`weierstrassDivision_q_unique`) together with injectivity of the polynomial
embedding. -/
theorem weierstrassDivision_r_unique {g : Restricted R c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s) {f : Restricted R c}
    {q₁ q₂ : Restricted R c} {r₁ r₂ : Polynomial R}
    (hr₁ : r₁.degree < s) (hf₁ : f = g * q₁ + Polynomial.toRestricted c r₁)
    (hr₂ : r₂.degree < s) (hf₂ : f = g * q₂ + Polynomial.toRestricted c r₂) : r₁ = r₂ := by
  obtain rfl : q₁ = q₂ := weierstrassDivision_q_unique c hg hr₁ hf₁ hr₂ hf₂
  exact Polynomial.toRestricted_injective c (add_left_cancel (hf₁.symm.trans hf₂))

lemma exists_pos_lt_forall_le_of_tendsto_zero {a : ℕ → ℝ}
    (ha : Tendsto a atTop (𝓝 0)) (h0 : ∀ t, 0 ≤ a t) {M : ℝ} (hM : 0 < M)
    {S : ℕ → Prop} [DecidablePred S] (hS : ∀ t, S t → a t < M) :
    ∃ ε : ℝ, 0 < ε ∧ ε < M ∧ ∀ t, S t → a t ≤ ε := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ha (M / 2) (half_pos hM)
  simp only [Real.dist_eq, sub_zero, abs_of_nonneg (h0 _)] at hN
  set F : Finset ℝ := insert (M / 2) (((Finset.range N).filter S).image a)
  have hFne : F.Nonempty := ⟨M / 2, Finset.mem_insert_self _ _⟩
  refine ⟨F.max' hFne, (half_pos hM).trans_le (F.le_max' _ (Finset.mem_insert_self _ _)),
    (F.max'_lt_iff hFne).mpr fun x hx ↦ ?_, fun t ht ↦ ?_⟩
  · rcases Finset.mem_insert.mp hx with rfl | hx
    · exact half_lt_self hM
    · obtain ⟨t, htmem, rfl⟩ := Finset.mem_image.mp hx
      exact hS t (Finset.mem_filter.mp htmem).2
  · rcases lt_or_ge t N with htN | htN
    · exact F.le_max' _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr htN, ht⟩, rfl⟩))
    · exact (hN t htN).le.trans (F.le_max' _ (Finset.mem_insert_self _ _))

omit [NormMulClass R] in
/-- For `g` whose `s`-th Gauss term strictly dominates every other, there is a uniform
contraction factor `θ < 1` bounding all other Gauss terms relative to the dominant one. -/
lemma exists_lt_one_forall_norm_coeff_mul_pow_le {g : Restricted R c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s)
    (hstrict : ∀ t, t ≠ s → ‖coeff t g.1‖ * c ^ t < ‖coeff s g.1‖ * c ^ s) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧
      ∀ t, t ≠ s → ‖coeff t g.1‖ * c ^ t ≤ θ * (‖coeff s g.1‖ * c ^ s) := by
  have hc0 : (0 : ℝ) < c := Fact.out
  have hM : (0 : ℝ) < ‖coeff s g.1‖ * c ^ s := hg.norm_coeff_mul_pow_eq.symm ▸ hg.norm_pos
  obtain ⟨ε, hε0, hεM, hε⟩ := exists_pos_lt_forall_le_of_tendsto_zero
    ((isRestricted_iff' c g.1).mp g.2)
    (fun t ↦ mul_nonneg (norm_nonneg _) (pow_nonneg hc0.le t)) hM hstrict
  exact ⟨ε / (‖coeff s g.1‖ * c ^ s), div_nonneg hε0.le hM.le, (div_lt_one hM).mpr hεM,
    fun t ht ↦ (hε t ht).trans_eq (div_mul_cancel₀ ε hM.ne').symm⟩

variable {c}

omit [NormMulClass R] [Fact (0 < c)] in
private lemma exists_toRestricted_eq_of_coeff_eq_zero {r_T : Restricted R c} {s : ℕ}
    (h : ∀ v, s ≤ v → coeff v r_T.1 = 0) :
    ∃ r : Polynomial R, r.degree < s ∧ Polynomial.toRestricted c r = r_T := by
  refine ⟨PowerSeries.trunc s r_T.1, PowerSeries.degree_trunc_lt r_T.1 s, ?_⟩
  apply Subtype.ext
  ext v
  change coeff v ((PowerSeries.trunc s r_T.1 : Polynomial R) : PowerSeries R) = coeff v r_T.1
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with hv
  · rfl
  · exact (h v (not_lt.mp hv)).symm

private lemma cauchySeq_of_norm_sub_le {X Y : Type*} [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup Y] {b : ℕ → Y} (hb : CauchySeq b) {x : ℕ → X} {K : ℝ}
    (hK : 0 ≤ K) (hbd : ∀ n m, ‖x n - x m‖ ≤ K * ‖b n - b m‖) : CauchySeq x := by
  have hK1 : (0 : ℝ) < K + 1 := by linarith
  refine Metric.cauchySeq_iff.mpr fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hb (ε / (K + 1)) (div_pos hε hK1)
  refine ⟨N, fun n hn m hm ↦ ?_⟩
  have hb' : ‖b n - b m‖ * (K + 1) < ε := by
    rw [← lt_div_iff₀ hK1, ← dist_eq_norm]; exact hN n hn m hm
  rw [dist_eq_norm]
  exact (hbd n m).trans_lt (by nlinarith [norm_nonneg (b n - b m)])

/-- The division set of a distinguished series is closed: along a convergent sequence of
divisible elements the division bounds make the quotients and remainders Cauchy, and the limit
remainder is a polynomial of degree `< s`. -/
lemma isClosed_divisionSet [CompleteSpace R] {g : Restricted R c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s) : IsClosed (divisionSet g s) := by
  refine IsSeqClosed.isClosed ?_
  intro b_seq b hb_mem hb_lim
  choose q_seq r_seq hr_seq hb_eq using hb_mem
  have diff_eq : ∀ n m, b_seq n - b_seq m =
      g * (q_seq n - q_seq m) + Polynomial.toRestricted c (r_seq n - r_seq m) := fun n m ↦ by
    rw [hb_eq n, hb_eq m, map_sub, mul_sub]
    abel
  have diff_deg : ∀ n m, (r_seq n - r_seq m).degree < s := fun n m ↦
    (Polynomial.degree_sub_le _ _).trans_lt (max_lt (hr_seq n) (hr_seq m))
  have hq_cauchy : CauchySeq q_seq :=
    cauchySeq_of_norm_sub_le hb_lim.cauchySeq (inv_nonneg.mpr hg.norm_pos.le)
      fun n m ↦ norm_q_le_of_eq_mul_add c hg (diff_deg n m) (diff_eq n m)
  have hr_cauchy : CauchySeq fun n ↦ Polynomial.toRestricted c (r_seq n) :=
    cauchySeq_of_norm_sub_le hb_lim.cauchySeq zero_le_one fun n m ↦ by
      rw [one_mul, ← map_sub]
      exact norm_r_le_of_eq_mul_add c hg (diff_deg n m) (diff_eq n m)
  obtain ⟨q, hq_lim⟩ := cauchySeq_tendsto_of_complete hq_cauchy
  obtain ⟨r_T, hr_T_lim⟩ := cauchySeq_tendsto_of_complete hr_cauchy
  have h_r_T_in : r_T ∈ {f : Restricted R c | ∀ v, s ≤ v → coeff v f.1 = 0} := by
    refine (isClosed_setOf_coeff_eq_zero c s).mem_of_tendsto hr_T_lim
      (Eventually.of_forall fun n v hv ↦ ?_)
    simp only [Polynomial.val_toRestricted, Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_degree_lt ((hr_seq n).trans_le (mod_cast hv))
  obtain ⟨r, hr_deg, hr_toR⟩ := exists_toRestricted_eq_of_coeff_eq_zero h_r_T_in
  refine ⟨q, r, hr_deg, ?_⟩
  rw [hr_toR]
  exact tendsto_nhds_unique hb_lim
    (by simpa [funext hb_eq] using (hq_lim.const_mul g).add hr_T_lim)

omit [NormMulClass R] in
private lemma norm_sub_monomial_le {g : Restricted R c} {s : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hbd : ∀ t, t ≠ s → ‖coeff t g.1‖ * c ^ t ≤ θ * (‖coeff s g.1‖ * c ^ s)) :
    ‖g - monomial c s (coeff s g.1)‖ ≤ θ * (‖coeff s g.1‖ * c ^ s) := by
  refine (norm_le_iff c _).mpr fun i ↦ ?_
  by_cases his : i = s
  · subst his
    change ‖coeff i (g.1 - PowerSeries.monomial i (coeff i g.1))‖ * c ^ i ≤ _
    rw [map_sub, PowerSeries.coeff_monomial_same, sub_self, norm_zero, zero_mul]
    exact mul_nonneg hθ0 (mul_nonneg (norm_nonneg _) (pow_nonneg (Fact.out : (0 : ℝ) < c).le _))
  · change ‖coeff i (g.1 - PowerSeries.monomial s (coeff s g.1))‖ * c ^ i ≤ _
    rw [map_sub, PowerSeries.coeff_monomial, if_neg his, sub_zero]
    exact hbd i his

private lemma isRestricted_shiftDiv (u : Rˣ) (f : Restricted R c) (s : ℕ) :
    IsRestricted c (PowerSeries.mk fun n ↦ ((u⁻¹ : Rˣ) : R) * coeff (n + s) f.1) := by
  have hc0 : (0 : ℝ) < c := Fact.out
  rw [isRestricted_iff']
  have hshift : Tendsto (fun n : ℕ ↦ ‖coeff (n + s) f.1‖ * c ^ (n + s)) atTop (𝓝 0) :=
    (Filter.tendsto_add_atTop_iff_nat s).mpr ((isRestricted_iff' c f.1).mp f.2)
  have h2 := hshift.const_mul (‖((u⁻¹ : Rˣ) : R)‖ * (c ^ s)⁻¹)
  rw [mul_zero] at h2
  refine h2.congr fun n ↦ ?_
  rw [PowerSeries.coeff_mk, norm_mul, pow_add]
  field_simp [(pow_pos hc0 s).ne']

omit [NormMulClass R] [Fact (0 < c)] in
private lemma monomial_mul_shiftDiv_eq_sub {u : Rˣ} {g : Restricted R c} {s : ℕ}
    (hu : (u : R) = coeff s g.1) (f qf : Restricted R c)
    (hqf : ∀ n, coeff n qf.1 = ((u⁻¹ : Rˣ) : R) * coeff (n + s) f.1) :
    monomial c s (coeff s g.1) * qf = f - Polynomial.toRestricted c (PowerSeries.trunc s f.1) := by
  apply Subtype.ext
  ext m
  change coeff m (PowerSeries.monomial s (coeff s g.1) * qf.1)
    = coeff m (f.1 - ((PowerSeries.trunc s f.1 : Polynomial R) : PowerSeries R))
  rw [PowerSeries.monomial_eq_C_mul_X_pow, mul_assoc, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  rcases lt_or_ge m s with h1 | h1
  · rw [if_neg (not_le.mpr h1), if_pos h1, mul_zero, sub_self]
  · rw [if_pos h1, hqf (m - s), if_neg (not_lt.mpr h1), Nat.sub_add_cancel h1, sub_zero, ← hu,
      Units.mul_inv_cancel_left]

private lemma norm_shiftDiv_le [Nontrivial R] {u : Rˣ} {g : Restricted R c} {s : ℕ}
    (hu : (u : R) = coeff s g.1) (f qf : Restricted R c)
    (hqf : ∀ n, coeff n qf.1 = ((u⁻¹ : Rˣ) : R) * coeff (n + s) f.1) :
    ‖qf‖ ≤ (‖coeff s g.1‖ * c ^ s)⁻¹ * ‖f‖ := by
  have hc0 : (0 : ℝ) < c := Fact.out
  have : NormOneClass R := NormMulClass.toNormOneClass
  refine (norm_le_iff c _).mpr fun n ↦ ?_
  rw [hqf n, norm_mul, norm_units_inv, hu]
  have h2 : ‖coeff (n + s) f.1‖ * c ^ n ≤ (c ^ s)⁻¹ * ‖f‖ := by
    rw [le_inv_mul_iff₀ (pow_pos hc0 s), show c ^ s * (‖coeff (n + s) f.1‖ * c ^ n)
      = ‖coeff (n + s) f.1‖ * c ^ (n + s) by ring]
    exact norm_coeff_mul_pow_le c f (n + s)
  calc ‖coeff s g.1‖⁻¹ * ‖coeff (n + s) f.1‖ * c ^ n
      = ‖coeff s g.1‖⁻¹ * (‖coeff (n + s) f.1‖ * c ^ n) := mul_assoc _ _ _
    _ ≤ ‖coeff s g.1‖⁻¹ * ((c ^ s)⁻¹ * ‖f‖) :=
        mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr (norm_nonneg _))
    _ = (‖coeff s g.1‖ * c ^ s)⁻¹ * ‖f‖ := by rw [mul_inv, mul_assoc]

/-- **The one-step approximate division** for a divisor whose `s`-th Gauss term dominates all
others with contraction factor `θ`: there is `b ∈ divisionSet g s` with `‖-f + b‖ ≤ θ * ‖f‖`.

The witness is the head-term division: `b = g * qf + rf` with `qf` the `s`-shift of `f`
rescaled by the inverse of the dominant coefficient and `rf` the truncation of `f` below
degree `s`, so that `-f + b = (g - monomial s (coeff s g)) * qf` picks up the factor `θ`
from the off-dominant part of `g` and `‖qf‖ ≤ (‖coeff s g‖ * c ^ s)⁻¹ * ‖f‖`. -/
lemma exists_mem_divisionSet_norm_le_of_forall_le {g : Restricted R c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hbd : ∀ t, t ≠ s → ‖coeff t g.1‖ * c ^ t ≤ θ * (‖coeff s g.1‖ * c ^ s))
    (f : Restricted R c) : ∃ b ∈ divisionSet g s, ‖-f + b‖ ≤ θ * ‖f‖ := by
  have hntR : Nontrivial R := hg.nontrivial
  set u : Rˣ := hg.isUnit_coeff.unit
  have hu_spec : (u : R) = coeff s g.1 := hg.isUnit_coeff.unit_spec
  have hM : (0 : ℝ) < ‖coeff s g.1‖ * c ^ s := hg.norm_coeff_mul_pow_eq.symm ▸ hg.norm_pos
  set qf : Restricted R c := ⟨PowerSeries.mk fun n ↦ ((u⁻¹ : Rˣ) : R) * coeff (n + s) f.1,
    isRestricted_shiftDiv u f s⟩ with hqf_def
  have hqf_coeff : ∀ n, coeff n qf.1 = ((u⁻¹ : Rˣ) : R) * coeff (n + s) f.1 := fun n ↦ by
    rw [hqf_def]; exact PowerSeries.coeff_mk n fun k ↦ ((u⁻¹ : Rˣ) : R) * coeff (k + s) f.1
  set rf : Polynomial R := PowerSeries.trunc s f.1
  refine ⟨g * qf + Polynomial.toRestricted c rf,
    ⟨qf, rf, PowerSeries.degree_trunc_lt f.1 s, rfl⟩, ?_⟩
  have hkey : monomial c s (coeff s g.1) * qf = f - Polynomial.toRestricted c rf :=
    monomial_mul_shiftDiv_eq_sub hu_spec f qf hqf_coeff
  have hdiff : -f + (g * qf + Polynomial.toRestricted c rf)
      = (g - monomial c s (coeff s g.1)) * qf := by
    rw [sub_mul, hkey]
    ring
  rw [hdiff, norm_mul]
  calc ‖g - monomial c s (coeff s g.1)‖ * ‖qf‖
      ≤ (θ * (‖coeff s g.1‖ * c ^ s)) * ((‖coeff s g.1‖ * c ^ s)⁻¹ * ‖f‖) :=
        mul_le_mul (norm_sub_monomial_le hθ0 hbd) (norm_shiftDiv_le hu_spec f qf hqf_coeff)
          (norm_nonneg _) (mul_nonneg hθ0 hM.le)
    _ = θ * ‖f‖ := by rw [mul_assoc, mul_inv_cancel_left₀ hM.ne']

omit [NormMulClass R] in
lemma dense_divisionSet_of_forall_exists_norm_le {g : Restricted R c} {s : ℕ}
    {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1)
    (happrox : ∀ f : Restricted R c, f ≠ 0 → ∃ b ∈ divisionSet g s, ‖-f + b‖ ≤ k * ‖f‖) :
    Dense (divisionSet g s) := by
  refine AddSubgroup.dense_of_infDist_le (divisionAddSubgroup g s) k hk0 hk1 fun f ↦ ?_
  by_cases hf : f = 0
  · subst hf
    rw [Metric.infDist_zero_of_mem (divisionAddSubgroup g s).zero_mem]
    exact mul_nonneg hk0.le dist_nonneg
  · obtain ⟨b, hb, hbnorm⟩ := happrox f hf
    calc Metric.infDist f (divisionAddSubgroup g s)
        ≤ dist f b := Metric.infDist_le_dist_of_mem hb
      _ = ‖-f + b‖ := by rw [dist_eq_norm, ← norm_neg, neg_sub, sub_eq_neg_add]
      _ ≤ k * ‖f‖ := hbnorm
      _ = k * dist f 0 := by rw [dist_zero_right]

/-- The division set of a strictly-dominated distinguished series is dense, by
`AddSubgroup.dense_of_infDist_le` applied to the one-step approximate division. -/
lemma dense_divisionSet_of_forall_lt {g : Restricted R c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s)
    (hstrict : ∀ t, t ≠ s → ‖coeff t g.1‖ * c ^ t < ‖coeff s g.1‖ * c ^ s) :
    Dense (divisionSet g s) := by
  obtain ⟨θ, hθ0, hθ1, hθ_bd⟩ := exists_lt_one_forall_norm_coeff_mul_pow_le c hg hstrict
  refine dense_divisionSet_of_forall_exists_norm_le
    (lt_of_lt_of_le one_half_pos (le_max_right _ _)) (max_lt hθ1 one_half_lt_one) fun f _ ↦ ?_
  obtain ⟨b, hb, hbnorm⟩ := exists_mem_divisionSet_norm_le_of_forall_le hg hθ0 hθ_bd f
  exact ⟨b, hb, hbnorm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))⟩

/-- **Weierstrass division, existence, for strictly-dominated divisors**: if the `s`-th
Gauss term of `g` strictly dominates every other, every `f` divides as `f = g * q + r` with
`deg r < s`, at the radius itself — no scaling hypotheses. -/
theorem weierstrassDivision_exists_of_forall_lt [CompleteSpace R] {g : Restricted R c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s)
    (hstrict : ∀ t, t ≠ s → ‖coeff t g.1‖ * c ^ t < ‖coeff s g.1‖ * c ^ s)
    (f : Restricted R c) :
    ∃ (q : Restricted R c) (r : Polynomial R), r.degree < s ∧
      f = g * q + Polynomial.toRestricted c r := by
  change f ∈ divisionSet g s
  rw [← (isClosed_divisionSet hg).closure_eq]
  exact dense_divisionSet_of_forall_lt hg hstrict f

end Bounds

/-! ## Uniqueness and the polynomial case, from existence

The division bounds make uniqueness and the polynomial form of Weierstrass division
corollaries of bare existence — no scaling, completeness or topological hypotheses.  Every
general-radius existence theorem (here and in `DivisibleRadius`) instantiates these. -/

section OfExists

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] {c : ℝ}
  [Fact (0 < c)]

/-- **Weierstrass division uniqueness is a corollary of existence**: any division witness for
`f` upgrades to the nested `∃!`, by the hypothesis-free quotient uniqueness and injectivity
of the polynomial embedding. -/
theorem weierstrassDivision_uniqueness_of_exists {g : Restricted R c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s) {f : Restricted R c}
    (hex : ∃ (q : Restricted R c) (r : Polynomial R), r.degree < s ∧
      f = g * q + Polynomial.toRestricted c r) :
    ∃! q : Restricted R c, ∃! r : Polynomial R, r.degree < s ∧
      f = g * q + Polynomial.toRestricted c r := by
  obtain ⟨q₀, r₀, hr₀, hf₀⟩ := hex
  refine ⟨q₀, ⟨r₀, ⟨hr₀, hf₀⟩, ?_⟩, ?_⟩
  · rintro r' ⟨hr', hf'⟩
    exact Polynomial.toRestricted_injective c (add_left_cancel (hf'.symm.trans hf₀))
  · rintro q' ⟨r', ⟨hr', hf'⟩, -⟩
    exact weierstrassDivision_q_unique c hg hr' hf' hr₀ hf₀

/-- **Weierstrass division for polynomials**: if `f` and `g` are polynomials, with `g` of
degree `s`, the Weierstrass quotient is itself a polynomial — with no scaling, completeness
or topological hypotheses: the division is Euclidean division by the unit-rescaled monic
divisor, and agreement with any other witness is the hypothesis-free quotient uniqueness.

The hypothesis `hgs` is necessary: over `ℤ_p` at radius `1` the polynomial
`g = X ^ s + p • X ^ (s + 1)` is distinguished of degree `s`, but dividing `f = X ^ s` by it
gives `q = (1 + p • X)⁻¹`, which is not a polynomial. -/
theorem weierstrassDivision_polynomial {g₀ : Polynomial R}
    {s : ℕ} (hg : IsDistinguished norm c (Polynomial.toRestricted c g₀).1 s)
    (hgs : g₀.degree ≤ s) (f₀ : Polynomial R) :
    ∃! q : Polynomial R, ∃! r : Polynomial R, r.degree < s ∧
      Polynomial.toRestricted c f₀ = Polynomial.toRestricted c g₀ * Polynomial.toRestricted c q
        + Polynomial.toRestricted c r := by
  have hnt : Nontrivial R := hg.nontrivial
  obtain ⟨u, hu⟩ : IsUnit (g₀.coeff s) := by
    have h1 := hg.isUnit_coeff
    rwa [Polynomial.val_toRestricted, Polynomial.coeff_coe] at h1
  have hdeg : g₀.degree = s := le_antisymm hgs (Polynomial.le_degree_of_ne_zero (hu ▸ u.ne_zero))
  have hlead : g₀.leadingCoeff = g₀.coeff s :=
    congrArg g₀.coeff (Polynomial.natDegree_eq_of_degree_eq_some hdeg)
  have hmonic : (Polynomial.C (↑u⁻¹ : R) * g₀).Monic :=
    Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [hlead, ← hu, Units.inv_mul])
  have hdeg₁ : (Polynomial.C (↑u⁻¹ : R) * g₀).degree = s :=
    (Polynomial.degree_C_mul_of_isUnit (u⁻¹).isUnit g₀).trans hdeg
  have hr₁ : (f₀ %ₘ (Polynomial.C (↑u⁻¹ : R) * g₀)).degree < s :=
    hdeg₁ ▸ Polynomial.degree_modByMonic_lt f₀ hmonic
  have hf₁ : Polynomial.toRestricted c f₀ = Polynomial.toRestricted c g₀ *
      Polynomial.toRestricted c (Polynomial.C (↑u⁻¹ : R) *
        (f₀ /ₘ (Polynomial.C (↑u⁻¹ : R) * g₀))) +
      Polynomial.toRestricted c (f₀ %ₘ (Polynomial.C (↑u⁻¹ : R) * g₀)) := by
    rw [← map_mul, ← map_add]
    congr 1
    conv_lhs => rw [← Polynomial.modByMonic_add_div f₀ (Polynomial.C (↑u⁻¹ : R) * g₀)]
    ring
  refine ⟨Polynomial.C (↑u⁻¹ : R) * (f₀ /ₘ (Polynomial.C (↑u⁻¹ : R) * g₀)),
    ⟨f₀ %ₘ (Polynomial.C (↑u⁻¹ : R) * g₀), ⟨hr₁, hf₁⟩, ?_⟩, ?_⟩
  · rintro r'' ⟨-, hf''⟩
    exact Polynomial.toRestricted_injective c (add_left_cancel (hf''.symm.trans hf₁))
  · rintro q' ⟨r', ⟨hr', hf'⟩, -⟩
    exact Polynomial.toRestricted_injective c
      (weierstrassDivision_q_unique c hg hr' hf' hr₁ hf₁)

end OfExists

end PowerSeries.Restricted
