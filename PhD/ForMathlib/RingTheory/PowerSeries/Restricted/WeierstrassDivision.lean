/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.PowerSeries.Trunc
import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.Complete
import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.Rescale
import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.Residue
import PhD.ForMathlib.Topology.MetricSpace.HausdorffDistance

/-! # Weierstrass division for restricted power series

Let `R` be a complete normed commutative ring with ultrametric distance, multiplicative norm
and `‖1‖ = 1`, whose origin is not isolated, and let `g : Restricted R c` be distinguished of
degree `s`.  **Weierstrass division** states that every `f : Restricted R c` is uniquely
`f = g * q + r` with `r` a polynomial of degree `< s`, with the division bounds
`‖q‖ ≤ ‖g‖⁻¹ * ‖f‖` and `‖r‖ ≤ ‖f‖`.

The **bounds and uniqueness** hold at an arbitrary radius `c` with direct weighted-norm
proofs and no auxiliary hypotheses.  The **existence** needs only the scaling hypothesis
`hunit` (every nonzero norm value in `Restricted R c` is realised by a unit of `R`).  Note
that `hunit` forces `c` to lie in the value group `‖Rˣ‖`: applied to the variable `X` (of
norm `c`) it produces a unit `u : Rˣ` of norm `c` (`exists_units_norm_eq`).  Conversely, over
a normed field `hunit` holds **precisely when** `c ∈ ‖Rˣ‖` — for `c` outside the value group
(e.g. `R = ℚ_p` and `c ∉ pᶻ`) no `a` can realise `‖X‖⁻¹ = c⁻¹` and `hunit` fails.  The proof
rescales along `rescaleEquiv u` to the radius-`1` engine below and transports back.

The engine (radius `1` — the implementation layer, not the public API): the divisible
elements `divisionSet g s = {g * q + r}` form an additive subgroup which is

* **closed** (`isClosed_divisionSet`): the division bounds make quotient and remainder
  sequences Cauchy along a convergent sequence of divisible elements; and
* **dense** (`dense_divisionSet`): modulo the closed-ball ideal of radius `ε` the reduction of
  (a unit-normalisation of) `g` is a *monic polynomial* of degree `s` over `R° ⧸ ball`, where
  Euclidean division is available and lifts to an `ε`-approximate division; density then
  follows from `AddSubgroup.dense_of_infDist_le` (BGR 1.1.4/2).

The residue-polynomial description of the reduction is a radius-`1` phenomenon, which is why
the engine lives there; replacing it by a direct weighted `ε`-division at arbitrary radius
(removing the rescaling detour) is an identified future experiment.
-/

open Filter PowerBounded
open scoped Topology

namespace PowerSeries.Restricted

/-! ## Division bounds and uniqueness, at an arbitrary radius -/

section Bounds

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] (c : ℝ)
  [Fact (0 < c)]

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
  have hc0 : (0 : ℝ) < c := Fact.out
  have hq_pos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  obtain ⟨i, j, hi, hj, hdom, hi_max, -⟩ :=
    exists_achievesGaussNorm_dominant_max c hc0.le g q hg.norm_pos.ne' hq_pos.ne'
  obtain rfl : s = i :=
    le_antisymm (hi_max s hg.achievesGaussNorm) (hg.le_of_achievesGaussNorm hi)
  have h_peak : ‖coeff (s + j) (g * q).1‖ * c ^ (s + j) = ‖g‖ * ‖q‖ := by
    change ‖coeff (s + j) (g.1 * q.1)‖ * c ^ (s + j) = ‖g‖ * ‖q‖
    have hdom' : ∀ p ∈ Finset.antidiagonal (s + j), p ≠ (s, j) →
        ‖coeff p.1 g.1 * coeff p.2 q.1‖ < ‖coeff s g.1 * coeff j q.1‖ :=
      fun p hp hpne ↦ (hdom p hp hpne).trans_eq (norm_mul _ _).symm
    calc ‖coeff (s + j) (g.1 * q.1)‖ * c ^ (s + j)
        = ‖coeff s g.1 * coeff j q.1‖ * c ^ (s + j) := by
          rw [PowerSeries.coeff_mul, IsNonarchimedean.apply_sum_eq_of_lt
            (fun x y ↦ IsUltrametricDist.norm_add_le_max x y) (fun a ↦ (norm_neg a).symm)
            (k := (s, j)) (Finset.mem_antidiagonal.mpr rfl) hdom']
      _ = (‖coeff s g.1‖ * c ^ s) * (‖coeff j q.1‖ * c ^ j) := by rw [norm_mul, pow_add]; ring
      _ = ‖g‖ * ‖q‖ := by rw [hg.norm_coeff_mul_pow_eq, hj.trans (norm_def c q).symm]
  have h_toR_zero : coeff (s + j) (Polynomial.toRestricted c r).1 = 0 := by
    rw [Polynomial.val_toRestricted, Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_degree_lt
      (hr.trans_le (by exact_mod_cast Nat.le_add_right s j))
  have h_coeff_f : ‖coeff (s + j) f.1‖ * c ^ (s + j) = ‖g‖ * ‖q‖ := by
    have hval : f.1 = (g * q).1 + (Polynomial.toRestricted c r).1 := by rw [hf]; rfl
    rw [hval, map_add, h_toR_zero, add_zero]
    exact h_peak
  have h_gq_bd : ‖g * q‖ ≤ ‖f‖ := by
    rw [norm_mul, ← h_coeff_f]
    exact norm_coeff_mul_pow_le c f (s + j)
  refine max_le h_gq_bd ?_
  have heq : Polynomial.toRestricted c r = f - g * q := by rw [hf]; abel
  rw [heq]
  refine (?_ : ‖f - g * q‖ ≤ max ‖f‖ ‖g * q‖).trans (max_le le_rfl h_gq_bd)
  have h1 := IsUltrametricDist.norm_add_le_max f (-(g * q))
  rwa [← sub_eq_add_neg, norm_neg] at h1

/-- The quotient bound in a Weierstrass division: `‖q‖ ≤ ‖g‖⁻¹ * ‖f‖`. -/
theorem norm_q_le_of_eq_mul_add {g : Restricted R c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s) {f q : Restricted R c} {r : Polynomial R}
    (hr : r.degree < s) (hf : f = g * q + Polynomial.toRestricted c r) :
    ‖q‖ ≤ ‖g‖⁻¹ * ‖f‖ := by
  by_contra hlt
  have h1 : ‖f‖ < ‖g * q‖ := by
    rw [norm_mul]
    exact (inv_mul_lt_iff₀ hg.norm_pos).mp (not_le.mp hlt)
  exact absurd ((le_max_left _ _).trans (max_le_norm_of_eq_mul_add c hg hr hf)) (not_le.mpr h1)

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
    rw [map_sub, mul_sub]
    calc (0 : Restricted R c)
        = (g * q₁ + Polynomial.toRestricted c r₁) - (g * q₂ + Polynomial.toRestricted c r₂) := by
          rw [← hf₁, ← hf₂, sub_self]
      _ = _ := by ring
  have h_bd := norm_q_le_of_eq_mul_add c hg
    ((Polynomial.degree_sub_le _ _).trans_lt (max_lt hr₁ hr₂)) h0
  rw [norm_zero, mul_zero, norm_le_zero_iff] at h_bd
  exact sub_eq_zero.mp h_bd

private lemma exists_pos_lt_forall_le_of_tendsto_zero {a : ℕ → ℝ}
    (ha : Tendsto a atTop (𝓝 0)) (h0 : ∀ t, 0 ≤ a t) {M : ℝ} (hM : 0 < M)
    {S : ℕ → Prop} [DecidablePred S] (hS : ∀ t, S t → a t < M) :
    ∃ ε : ℝ, 0 < ε ∧ ε < M ∧ ∀ t, S t → a t ≤ ε := by
  obtain ⟨N, hN⟩ : ∃ N, ∀ t ≥ N, a t < M / 2 := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ha (M / 2) (half_pos hM)
    exact ⟨N, fun t ht ↦ by simpa [Real.dist_eq, abs_of_nonneg (h0 t)] using hN t ht⟩
  set F : Finset ℝ := insert (M / 2) (((Finset.range N).filter S).image a) with hF_def
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
  have hM : (0 : ℝ) < ‖coeff s g.1‖ * c ^ s := by
    rw [hg.norm_coeff_mul_pow_eq]
    exact hg.norm_pos
  obtain ⟨ε, hε0, hεM, hε⟩ := exists_pos_lt_forall_le_of_tendsto_zero
    ((isRestricted_iff' c g.1).mp g.2)
    (fun t ↦ mul_nonneg (norm_nonneg _) (pow_nonneg hc0.le t)) hM hstrict
  exact ⟨ε / (‖coeff s g.1‖ * c ^ s), div_nonneg hε0.le hM.le, (div_lt_one hM).mpr hεM,
    fun t ht ↦ (hε t ht).trans_eq (div_mul_cancel₀ ε hM.ne').symm⟩

omit [NormMulClass R] in
/-- Coefficient extraction is continuous on restricted power series. -/
lemma coeff_continuous (v : ℕ) : Continuous fun f : Restricted R c ↦ coeff v f.1 := by
  have hcv : (0 : ℝ) < c ^ v := pow_pos Fact.out v
  refine Metric.continuous_iff.mpr fun f ε hε ↦ ⟨ε * c ^ v, mul_pos hε hcv, fun g hg ↦ ?_⟩
  rw [dist_eq_norm, ← LinearMap.map_sub (PowerSeries.coeff v) g.1 f.1]
  have h1 : ‖coeff v (g.1 - f.1)‖ * c ^ v ≤ ‖g - f‖ := norm_coeff_mul_pow_le c (g - f) v
  exact lt_of_mul_lt_mul_right (h1.trans_lt (by rwa [← dist_eq_norm])) hcv.le

omit [NormMulClass R] in
/-- The set of restricted power series whose coefficients from degree `s` on all vanish is
closed. -/
lemma isClosed_setOf_coeff_eq_zero (s : ℕ) :
    IsClosed {f : Restricted R c | ∀ v, s ≤ v → coeff v f.1 = 0} := by
  refine IsSeqClosed.isClosed fun f_seq f hf_mem hf_lim v hv ↦ ?_
  have : Tendsto (fun n ↦ coeff v (f_seq n).1) atTop (𝓝 (coeff v f.1)) :=
    ((coeff_continuous c v).tendsto _).comp hf_lim
  simp_all

variable {c}

omit [NormMulClass R] [Fact (0 < c)] in
/-- The set of elements divisible by `g` with polynomial remainder of degree `< s`. -/
abbrev divisionSet (g : Restricted R c) (s : ℕ) : Set (Restricted R c) :=
  {f | ∃ q, ∃ r : Polynomial R, r.degree < s ∧ f = g * q + Polynomial.toRestricted c r}

omit [NormMulClass R] [Fact (0 < c)] in
/-- `divisionSet g s` as an additive subgroup. -/
def divisionAddSubgroup (g : Restricted R c) (s : ℕ) : AddSubgroup (Restricted R c) where
  carrier := divisionSet g s
  zero_mem' := ⟨0, 0, by simp, by simp⟩
  add_mem' := by
    rintro _ _ ⟨qa, ra, hra, rfl⟩ ⟨qb, rb, hrb, rfl⟩
    refine ⟨qa + qb, ra + rb, (Polynomial.degree_add_le _ _).trans_lt (max_lt hra hrb), ?_⟩
    rw [map_add, mul_add]
    abel
  neg_mem' := by
    rintro _ ⟨q, r, hr, rfl⟩
    exact ⟨-q, -r, by rwa [Polynomial.degree_neg], by rw [map_neg, mul_neg]; abel⟩

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

/-- The division set of a strictly-dominated distinguished series is dense, by
`AddSubgroup.dense_of_infDist_le` applied to the one-step approximate division. -/
lemma dense_divisionSet_of_forall_lt {g : Restricted R c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s)
    (hstrict : ∀ t, t ≠ s → ‖coeff t g.1‖ * c ^ t < ‖coeff s g.1‖ * c ^ s) :
    Dense (divisionSet g s) := by
  obtain ⟨θ, hθ0, hθ1, hθ_bd⟩ := exists_lt_one_forall_norm_coeff_mul_pow_le c hg hstrict
  refine AddSubgroup.dense_of_infDist_le (divisionAddSubgroup g s) (max θ (1 / 2))
    (lt_of_lt_of_le one_half_pos (le_max_right _ _)) (max_lt hθ1 one_half_lt_one) fun f ↦ ?_
  by_cases hf : f = 0
  · subst hf
    rw [Metric.infDist_zero_of_mem (divisionAddSubgroup g s).zero_mem]
    exact mul_nonneg (le_max_of_le_right one_half_pos.le) dist_nonneg
  · obtain ⟨b, hb, hbnorm⟩ := exists_mem_divisionSet_norm_le_of_forall_le hg hθ0 hθ_bd f
    calc Metric.infDist f (divisionAddSubgroup g s)
        ≤ dist f b := Metric.infDist_le_dist_of_mem hb
      _ = ‖-f + b‖ := by rw [dist_eq_norm, ← norm_neg, neg_sub, sub_eq_neg_add]
      _ ≤ θ * ‖f‖ := hbnorm
      _ ≤ max θ (1 / 2) * ‖f‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ = max θ (1 / 2) * dist f 0 := by rw [dist_zero_right]

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
  have hgu : IsUnit (g₀.coeff s) := by
    have h1 := hg.isUnit_coeff
    rwa [Polynomial.val_toRestricted, Polynomial.coeff_coe] at h1
  obtain ⟨u, hu⟩ := hgu
  have hdeg : g₀.degree = s := le_antisymm hgs (Polynomial.le_degree_of_ne_zero (hu ▸ u.ne_zero))
  have hlead : g₀.leadingCoeff = g₀.coeff s :=
    congrArg g₀.coeff (Polynomial.natDegree_eq_of_degree_eq_some hdeg)
  have hmonic : (Polynomial.C (↑u⁻¹ : R) * g₀).Monic :=
    Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [hlead, ← hu, Units.inv_mul])
  have hdeg₁ : (Polynomial.C (↑u⁻¹ : R) * g₀).degree = s := by
    refine le_antisymm ?_ (Polynomial.le_degree_of_ne_zero ?_)
    · calc (Polynomial.C (↑u⁻¹ : R) * g₀).degree
          ≤ (Polynomial.C (↑u⁻¹ : R)).degree + g₀.degree := Polynomial.degree_mul_le _ _
        _ ≤ 0 + (s : WithBot ℕ) := add_le_add Polynomial.degree_C_le hdeg.le
        _ = s := zero_add _
    · rw [Polynomial.coeff_C_mul, ← hu, Units.inv_mul]
      exact one_ne_zero
  have hpoly : f₀ = g₀ * (Polynomial.C (↑u⁻¹ : R) * (f₀ /ₘ (Polynomial.C (↑u⁻¹ : R) * g₀))) +
      f₀ %ₘ (Polynomial.C (↑u⁻¹ : R) * g₀) := by
    conv_lhs => rw [← Polynomial.modByMonic_add_div f₀ (Polynomial.C (↑u⁻¹ : R) * g₀)]
    ring
  have hr₁ : (f₀ %ₘ (Polynomial.C (↑u⁻¹ : R) * g₀)).degree < s := by
    have h2 := Polynomial.degree_modByMonic_lt f₀ hmonic
    rwa [hdeg₁] at h2
  have hf₁ : Polynomial.toRestricted c f₀ = Polynomial.toRestricted c g₀ *
      Polynomial.toRestricted c (Polynomial.C (↑u⁻¹ : R) *
        (f₀ /ₘ (Polynomial.C (↑u⁻¹ : R) * g₀))) +
      Polynomial.toRestricted c (f₀ %ₘ (Polynomial.C (↑u⁻¹ : R) * g₀)) := by
    rw [← map_mul, ← map_add]
    exact congrArg _ hpoly
  refine ⟨Polynomial.C (↑u⁻¹ : R) * (f₀ /ₘ (Polynomial.C (↑u⁻¹ : R) * g₀)),
    ⟨f₀ %ₘ (Polynomial.C (↑u⁻¹ : R) * g₀), ⟨hr₁, hf₁⟩, ?_⟩, ?_⟩
  · rintro r'' ⟨-, hf''⟩
    exact Polynomial.toRestricted_injective c (add_left_cancel (hf''.symm.trans hf₁))
  · rintro q' ⟨r', ⟨hr', hf'⟩, -⟩
    exact Polynomial.toRestricted_injective c
      (weierstrassDivision_q_unique c hg hr' hf' hr₁ hf₁)

end OfExists

/-! ## The radius-`1` engine

Everything in this section is the implementation layer behind the general-radius existence
theorem: it is stated at radius `1` because the reduction of `T°` modulo a ball ideal is a
*polynomial* ring only there.  Consumers should use the general-radius theorems below. -/

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormMulClass R] [NormOneClass R] [NeBot (𝓝[≠] (0 : R))]

/-- `R°`, the power-bounded subring of the base ring `R`. -/
local notation "R°" => PowerBounded.subring R (S := ℤ)
/-- `T°`, the power-bounded subring of the Tate algebra `Restricted R 1`. -/
local notation "T°" => PowerBounded.subring (PowerSeries.Restricted R 1) (S := ℤ)

section Engine

omit [CompleteSpace R] [NormMulClass R] [NormOneClass R] [(𝓝[≠] (0 : R)).NeBot] in
/-- For a distinguished `g` with leading-coefficient norm `1`, there is `ε ∈ (0, 1)`
dominating every strictly-higher coefficient norm. -/
lemma exists_lt_one_forall_norm_coeff_le {g : Restricted R 1} {s : ℕ}
    (hg : IsDistinguished norm 1 g.1 s) (hg1 : ‖coeff s g.1‖ = 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ t, s < t → ‖coeff t g.1‖ ≤ ε := by
  have htend := (isRestricted_iff' 1 g.1).mp g.2
  simp only [one_pow, mul_one] at htend
  exact exists_pos_lt_forall_le_of_tendsto_zero htend (fun t ↦ norm_nonneg _) one_pos
    fun t ht ↦ by simpa [hg1] using hg.gaussTerm_lt t ht

omit [CompleteSpace R] in
/-- For `0 < ε < 1` the residue ring `R° ⧸ closedBall ε` is nontrivial. -/
lemma nontrivial_quotient_closedBall_ideal {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Nontrivial (↥R° ⧸ closedBall_ideal (R := R) hε0.le) := by
  refine Ideal.Quotient.nontrivial_iff.mpr fun h ↦ ?_
  have h1 : (1 : ↥R°) ∈ closedBall_ideal (R := R) hε0.le := by
    rw [h]
    exact Submodule.mem_top
  rw [mem_closedBall_ideal, OneMemClass.coe_one, norm_one] at h1
  exact absurd (h1.trans_lt hε1) (lt_irrefl 1)

omit [CompleteSpace R] in
/-- When `g ∈ T°` has degree-`s` coefficient equal to `1` and `ε ∈ (0, 1)` dominates every
strictly-higher coefficient norm, the reduction of `g` modulo the closed ball of radius `ε` is
a monic polynomial of degree `s`. -/
lemma monic_residueRingHom_of_isDistinguished {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {s : ℕ}
    (g : ↥T°) (hcs : coeff s g.1.1 = 1) (hgt : ∀ t, s < t → ‖coeff t g.1.1‖ ≤ ε) :
    (residueRingHom (closedBall_ideal hε0.le) (isOpen_closedBall_ideal hε0) g).Monic ∧
    (residueRingHom (closedBall_ideal hε0.le) (isOpen_closedBall_ideal hε0) g).degree = s := by
  have := nontrivial_quotient_closedBall_ideal (R := R) hε0 hε1
  have hs : (residueRingHom (closedBall_ideal hε0.le) (isOpen_closedBall_ideal hε0) g).coeff s
      = 1 := by
    rw [coeff_residueRingHom, show powerBoundedCoeff g s = 1 from Subtype.ext hcs, map_one]
  have hzero : ∀ v, s < v →
      (residueRingHom (closedBall_ideal hε0.le) (isOpen_closedBall_ideal hε0) g).coeff v = 0 := by
    intro v hv
    rw [coeff_residueRingHom, Ideal.Quotient.eq_zero_iff_mem, mem_closedBall_ideal]
    exact hgt v hv
  have hdeg := le_antisymm
    ((Polynomial.degree_le_iff_coeff_zero _ _).mpr fun m hm ↦ hzero m (mod_cast hm))
    (Polynomial.le_degree_of_ne_zero (by rw [hs]; exact one_ne_zero))
  refine ⟨?_, hdeg⟩
  rw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some hdeg]
  exact hs

omit [CompleteSpace R] in
/-- If the reduction of `g` modulo the closed ball of radius `ε` is monic, every `f ∈ T°`
admits an `ε`-approximate Euclidean division by `g`: there are `q ∈ T°` and a polynomial `r`
over `R` with `deg r < deg (residue g)` and `‖f - g q - r‖ ≤ ε`. -/
lemma exists_approx_div_of_monic_residue {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (g f : ↥T°)
    (hτg : (residueRingHom (closedBall_ideal hε0.le) (isOpen_closedBall_ideal hε0) g).Monic) :
    ∃ (q : ↥T°) (r : Polynomial R),
      r.degree < (residueRingHom (closedBall_ideal hε0.le) (isOpen_closedBall_ideal hε0)
        g).degree ∧ ‖f.1 - g.1 * q.1 - Polynomial.toRestricted 1 r‖ ≤ ε := by
  have hnt := nontrivial_quotient_closedBall_ideal (R := R) hε0 hε1
  set τ := residueRingHom (closedBall_ideal (R := R) hε0.le) (isOpen_closedBall_ideal hε0)
    with hτdef
  have hdiv := Polynomial.modByMonic_add_div (τ f) (τ g)
  have hrdeg := Polynomial.degree_modByMonic_lt (τ f) hτg
  obtain ⟨Q, hQ⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective (τ f /ₘ τ g)
  have hmem : (τ f %ₘ τ g)
      ∈ Polynomial.lifts (Ideal.Quotient.mk (closedBall_ideal (R := R) hε0.le)) := by
    rw [Polynomial.lifts_iff_set_range]
    exact Polynomial.map_surjective _ Ideal.Quotient.mk_surjective _
  obtain ⟨P, hP_map, hP_deg⟩ := Polynomial.exists_degree_eq_of_mem_lifts hmem
  have hres : τ (f - g * toPowerBounded Q - toPowerBounded P) = 0 := by
    rw [map_sub, map_sub, map_mul, hτdef, residueRingHom_toPowerBounded,
      residueRingHom_toPowerBounded, ← hτdef, hQ, hP_map]
    linear_combination -hdiv
  refine ⟨toPowerBounded Q, P.map (PowerBounded.subring R (S := ℤ)).subtype,
    Polynomial.degree_map_le.trans_lt (hP_deg.trans_lt hrdeg), ?_⟩
  simpa [sub_sub] using (residueRingHom_closedBall_ideal_eq_zero_iff hε0 _).mp hres

omit [CompleteSpace R] [NormMulClass R] [NormOneClass R] [(𝓝[≠] (0 : R)).NeBot] in
/-- The algebraic core of transporting an approximate division back to the original data:
scaling the normalised Weierstrass residual `C α * f - (C u * g) * qT - r` by `C αinv`, with
`αinv * α = 1`, yields the un-normalised residual for the original `f` and `g`. -/
private lemma C_mul_normalised_residual_eq {f g qT : Restricted R 1} {α αinv u : R}
    (hαinv_α : αinv * α = 1) (r : Polynomial R) :
    C 1 αinv * (C 1 α * f - C 1 u * g * qT - Polynomial.toRestricted 1 r)
      = f - g * (C 1 (αinv * u) * qT) - Polynomial.toRestricted 1 (Polynomial.C αinv * r) := by
  rw [mul_sub, mul_sub,
    show C 1 αinv * Polynomial.toRestricted 1 r
        = Polynomial.toRestricted 1 (Polynomial.C αinv * r) from by
      rw [map_mul, Polynomial.toRestricted_C],
    show C 1 αinv * (C 1 α * f) = f from by
      rw [← mul_assoc, ← map_mul, hαinv_α, map_one, one_mul],
    show C 1 αinv * (C 1 u * g * qT) = g * (C 1 (αinv * u) * qT) from by
      rw [map_mul (C 1) αinv u]; ring]

omit [CompleteSpace R] in
/-- **The `ε`-approximation step**: for a distinguished `g` of norm `1` and every `f` whose
norm is realised by a unit, there is `b ∈ divisionSet g s` with `‖-f + b‖ ≤ ε * ‖f‖`. -/
lemma exists_mem_divisionSet_norm_le {g : Restricted R 1} (hgn : ‖g‖ = 1) {s : ℕ}
    (hg : IsDistinguished norm 1 g.1 s) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hε_bd : ∀ t, s < t → ‖coeff t g.1‖ ≤ ε) (f : Restricted R 1)
    (hf : ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃ b ∈ divisionSet g s, ‖-f + b‖ ≤ ε * ‖f‖ := by
  have hcoeff_C : ∀ (a : R) (h : Restricted R 1) (k : ℕ),
      coeff k (C 1 a * h).1 = a * coeff k h.1 := fun a h k ↦ coeff_C_mul k h.1 a
  have hntR : Nontrivial R := hg.nontrivial
  obtain ⟨α, hα_norm, hα_unit⟩ := hf
  have hf_pos : 0 < ‖f‖ := inv_pos.mp (hα_norm ▸ norm_pos_iff.mpr hα_unit.ne_zero)
  obtain ⟨A, hA⟩ := hα_unit
  set αinv : R := ((A⁻¹ : Rˣ) : R) with hαinv_def
  have hαinv_α : αinv * α = 1 := by rw [hαinv_def, ← hA]; exact A.inv_mul
  have hαinv_norm : ‖αinv‖ = ‖f‖ := by rw [hαinv_def, norm_units_inv, hA, hα_norm, inv_inv]
  have hg1 : ‖coeff s g.1‖ = 1 := by simpa [hgn] using hg.norm_coeff_mul_pow_eq
  obtain ⟨U, hU⟩ := hg.isUnit_coeff
  set u : R := ((U⁻¹ : Rˣ) : R) with hu_def
  have hu_cs : u * coeff s g.1 = 1 := by rw [hu_def, ← hU]; exact U.inv_mul
  have hu_norm : ‖u‖ = 1 := by rw [hu_def, norm_units_inv, hU, hg1, inv_one]
  set g' : Restricted R 1 := C 1 u * g with hg'_def
  set f' : Restricted R 1 := C 1 α * f with hf'_def
  have hg'_cs : coeff s g'.1 = 1 := by rw [hg'_def, hcoeff_C, hu_cs]
  have hg'_norm : ‖g'‖ = 1 := by rw [hg'_def, norm_mul, norm_C, hu_norm, hgn, one_mul]
  have hf'_norm : ‖f'‖ = 1 := by
    rw [hf'_def, norm_mul, norm_C, hα_norm, inv_mul_cancel₀ hf_pos.ne']
  have hg'_bd : ∀ t, s < t → ‖coeff t g'.1‖ ≤ ε := fun t ht ↦ by
    simpa only [hg'_def, hcoeff_C, norm_mul, hu_norm, one_mul] using hε_bd t ht
  have hg'_pb : g' ∈ PowerBounded.subring (Restricted R 1) (S := ℤ) :=
    isPowerBounded_of_norm_le_one hg'_norm.le
  have hf'_pb : f' ∈ PowerBounded.subring (Restricted R 1) (S := ℤ) :=
    isPowerBounded_of_norm_le_one hf'_norm.le
  have hnt := nontrivial_quotient_closedBall_ideal (R := R) hε0 hε1
  have hmonic := monic_residueRingHom_of_isDistinguished hε0 hε1 ⟨g', hg'_pb⟩ hg'_cs hg'_bd
  obtain ⟨qpb, r, hr_deg, hbound⟩ :=
    exists_approx_div_of_monic_residue hε0 hε1 ⟨g', hg'_pb⟩ ⟨f', hf'_pb⟩ hmonic.1
  rw [hmonic.2] at hr_deg
  set qT : Restricted R 1 := qpb.1
  have hX : ‖f' - g' * qT - Polynomial.toRestricted 1 r‖ ≤ ε := by
    simpa [sub_sub] using hbound
  set q : Restricted R 1 := C 1 (αinv * u) * qT
  set r' : Polynomial R := Polynomial.C αinv * r with hr'_def
  have key : C 1 αinv * (f' - g' * qT - Polynomial.toRestricted 1 r)
      = f - g * q - Polynomial.toRestricted 1 r' :=
    C_mul_normalised_residual_eq hαinv_α r
  refine ⟨g * q + Polynomial.toRestricted 1 r', ⟨q, r', ?_, rfl⟩, ?_⟩
  · rw [hr'_def, ← Polynomial.smul_eq_C_mul αinv]
    exact (Polynomial.degree_smul_le αinv r).trans_lt hr_deg
  · rw [show -f + (g * q + Polynomial.toRestricted 1 r')
        = -(C 1 αinv * (f' - g' * qT - Polynomial.toRestricted 1 r)) from by rw [key]; ring,
      norm_neg, norm_mul, norm_C, hαinv_norm, mul_comm ε]
    exact mul_le_mul_of_nonneg_left hX (norm_nonneg f)

omit [CompleteSpace R] in
/-- The division set of a norm-one distinguished series is dense, by
`AddSubgroup.dense_of_infDist_le` applied to the `ε`-approximation. -/
lemma dense_divisionSet {g : Restricted R 1} (hgn : ‖g‖ = 1) {s : ℕ}
    (hg : IsDistinguished norm 1 g.1 s)
    (hunit : ∀ f : Restricted R 1, f ≠ 0 → ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    Dense (divisionSet g s) := by
  have hg1 : ‖coeff s g.1‖ = 1 := by simpa [hgn] using hg.norm_coeff_mul_pow_eq
  obtain ⟨ε, hε0, hε1, hε_bd⟩ := exists_lt_one_forall_norm_coeff_le hg hg1
  refine AddSubgroup.dense_of_infDist_le (divisionAddSubgroup g s) ε hε0 hε1 fun f ↦ ?_
  by_cases hf : f = 0
  · subst hf
    rw [Metric.infDist_zero_of_mem (divisionAddSubgroup g s).zero_mem]
    positivity
  · obtain ⟨b, hb, hbnorm⟩ := exists_mem_divisionSet_norm_le hgn hg hε0 hε1 hε_bd f (hunit f hf)
    calc Metric.infDist f (divisionAddSubgroup g s)
        ≤ dist f b := Metric.infDist_le_dist_of_mem hb
      _ = ‖-f + b‖ := by rw [dist_eq_norm, ← norm_neg, neg_sub, sub_eq_neg_add]
      _ ≤ ε * ‖f‖ := hbnorm
      _ = ε * dist f 0 := by rw [dist_zero_right]

/-- **Weierstrass division at radius `1`, normalised case `‖g‖ = 1`**: the division set is
closed and dense, hence everything. -/
theorem weierstrassDivision_exists_of_norm_eq_one {g : Restricted R 1} (hgn : ‖g‖ = 1) {s : ℕ}
    (hg : IsDistinguished norm 1 g.1 s) (f : Restricted R 1)
    (hunit : ∀ f : Restricted R 1, f ≠ 0 → ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃ (q : Restricted R 1) (r : Polynomial R), r.degree < s ∧
      f = g * q + Polynomial.toRestricted 1 r := by
  change f ∈ divisionSet g s
  rw [← (isClosed_divisionSet hg).closure_eq]
  exact dense_divisionSet hgn hg hunit f

end Engine

/-! ## Weierstrass division, at an arbitrary radius -/

section Existence

variable {c : ℝ} [Fact (0 < c)]

omit [CompleteSpace R] [(𝓝[≠] (0 : R)).NeBot] in
/-- The scaling hypothesis of Weierstrass division realises the radius by a unit of `R`:
apply it to the variable `X` (of norm `c`) and invert the realising unit.  In particular
`hunit` can only hold when `c` lies in the value group `‖Rˣ‖`; over a normed field this is
exactly when it holds. -/
lemma exists_units_norm_eq
    (hunit : ∀ f : Restricted R c, f ≠ 0 → ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃ u : Rˣ, ‖(u : R)‖ = c := by
  have hXnorm : ‖X R c‖ = c := by rw [norm_X, norm_one, one_mul]
  have hX0 : X R c ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_eq (Fact.out : (0 : ℝ) < c) hXnorm.symm)
  obtain ⟨a, ha_norm, ha_unit⟩ := hunit _ hX0
  obtain ⟨A, rfl⟩ := ha_unit
  exact ⟨A⁻¹, by rw [norm_units_inv, ha_norm, hXnorm, inv_inv]⟩

/-- **Weierstrass division, existence**: for `g` distinguished of degree `s`, under the
scaling hypothesis `hunit` (every nonzero norm value is realised by a unit of `R`; over a
normed field this holds if and only if `c` lies in the value group `‖Rˣ‖`, cf.
`exists_units_norm_eq`), every `f` divides as `f = g * q + r` with `deg r < s`.  Proven by
rescaling to the radius-`1` engine along a unit realising the radius. -/
theorem weierstrassDivision_exists {g : Restricted R c} {s : ℕ}
    (hg : IsDistinguished norm c g.1 s) (f : Restricted R c)
    (hunit : ∀ f : Restricted R c, f ≠ 0 → ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃ (q : Restricted R c) (r : Polynomial R), r.degree < s ∧
      f = g * q + Polynomial.toRestricted c r := by
  have hntR : Nontrivial R := hg.nontrivial
  have hgne : g ≠ 0 := fun h0 ↦ hg.ne_zero (congrArg Subtype.val h0)
  obtain ⟨u, hu⟩ := exists_units_norm_eq hunit
  have hu' : ‖(u : R)‖ * 1 = c := by rw [mul_one]; exact hu
  have hg₁ : IsDistinguished norm 1 (rescaleEquiv u hu' g).1 s :=
    (isDistinguished_rescaleEquiv_iff u hu' g s).mpr hg
  obtain ⟨a, ha1, ha2⟩ : ∃ a : R, ‖a‖ = ‖rescaleEquiv u hu' g‖⁻¹ ∧ IsUnit a := by
    rw [norm_rescaleEquiv u hu' g]
    exact hunit g hgne
  have hga : ‖C 1 a * rescaleEquiv u hu' g‖ = 1 := by
    rw [norm_mul, norm_C, ha1, inv_mul_cancel₀ hg₁.norm_pos.ne']
  obtain ⟨q₀, r₀, hr₀, hf₀⟩ := weierstrassDivision_exists_of_norm_eq_one hga (hg₁.C_mul ha2)
    (rescaleEquiv u hu' f) (hunit_transport u hu' hunit)
  have hf₁ : rescaleEquiv u hu' f
      = rescaleEquiv u hu' g * (C 1 a * q₀) + Polynomial.toRestricted 1 r₀ := by
    rw [hf₀]; ring
  have h2 := congrArg (rescaleEquiv u hu').symm hf₁
  rw [RingEquiv.symm_apply_apply, map_add, map_mul, RingEquiv.symm_apply_apply,
    rescaleEquiv_symm_toRestricted] at h2
  exact ⟨(rescaleEquiv u hu').symm (C 1 a * q₀),
    r₀.comp (Polynomial.C ((u⁻¹ : Rˣ) : R) * Polynomial.X),
    Polynomial.degree_comp_C_mul_X_lt hr₀ _, h2⟩

/-- **Weierstrass division**: existence and uniqueness of the division `f = g * q + r`,
`deg r < s`, under the scaling hypothesis.  (The nested `∃!` shares the witness pair; the
parts are recovered by `weierstrassDivision_exists` and `weierstrassDivision_q_unique`.) -/
theorem weierstrassDivision_uniqueness {g : Restricted R c}
    {s : ℕ} (hg : IsDistinguished norm c g.1 s) (f : Restricted R c)
    (hunit : ∀ f : Restricted R c, f ≠ 0 → ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∃! q : Restricted R c, ∃! r : Polynomial R, r.degree < s ∧
      f = g * q + Polynomial.toRestricted c r :=
  weierstrassDivision_uniqueness_of_exists hg (weierstrassDivision_exists hg f hunit)

end Existence

end PowerSeries.Restricted
