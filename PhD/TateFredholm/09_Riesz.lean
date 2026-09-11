/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Topology.Algebra.Module.Complement
import Mathlib.Topology.Algebra.Module.FiniteDimension

import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.MulWeierstrassDivision
import PhD.TateFredholm.BaseChange
import PhD.TateFredholm.Fredholm

/-!
# Riesz theory: zeros of the characteristic power series are eigenvalues

For a compactoid operator `u` on the model space `c(I, R)` over a Banach–Tate ring, with
Fredholm determinant `H = charPowerSeries u`, we develop Serre's Riesz theory
[Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
Publ. Math. IHÉS 12 (1962), §§5–7]:

* the Fredholm resolvent `P(t, u) = H(t)/(1 - tu)` and its entireness (§6, Prop. 10);
* multiplicativity of the determinant value `det(1-u)` (§5, Cor. 1 to Prop. 7);
* Serre's Proposition 11: `1 - a•u` is invertible iff `H(a)` is a unit;
* the eigenvector theorem: over a complete nonarchimedean field, a zero `a` of `H`
  yields an eigenvector `u x = a⁻¹ • x` (the eigenvector content of §7, Prop. 12);
* the Riesz decomposition itself (§7, Prop. 12): the Riesz projector attached to a zero
  `a` of order `h`, the topological splitting `c(I, K) = N(a) ⊕ F(a)` it induces, and
  the dimension formula `dim N(a) = h`.

## Main definitions

* `PowerSeries.hasseDeriv`, `PowerSeries.evalT`: divided derivatives and tsum-evaluation
  of power series (mathlib has neither for `PowerSeries` in the normed setting).
* `TateFredholm.IsOpLimit`: operator-norm convergence, this file's substitute for a
  normed-space structure on `c(I, R) →L[R] c(I, R)`.
* `TateFredholm.resolventCoeff`, `TateFredholm.resolventPartialSum`: the coefficients
  `vₘ` of the Fredholm resolvent, and the partial sums of its divided evaluations `Nₛ`.
* `TateFredholm.fredholmDet`: the determinant value `det(1 - u) = H_u(1)`.

## Main results

* `TateFredholm.isUnit_one_sub_smul_iff_isUnit_evalT` (Serre Prop. 11).
* `TateFredholm.exists_mem_ker_of_hasseDeriv_evalT` (the dichotomy, over `R`).
* `TateFredholm.exists_eigenvector_of_evalT_charPowerSeries_eq_zero` and
  `TateFredholm.evalT_charPowerSeries_eq_zero_iff` (the eigenvector milestone, over a
  field), together with
  `TateFredholm.exists_eigenvector_of_evalT_charPowerSeries_conj_eq_zero`, which
  transports them along a continuous linear equivalence and so covers any Banach
  space with an orthonormalisable basis.
* `TateFredholm.exists_rieszProjection` (Serre's projector `p = eʰ`), together with the
  kernel/range characterisations `TateFredholm.ker_one_sub_smul_pow_of_rieszProjection`,
  `TateFredholm.range_one_sub_smul_pow_of_rieszProjection` and
  `TateFredholm.rieszProjection_unique`.
* `TateFredholm.charPowerSeries_blockTriangular` (Serre Lemme 2) and
  `TateFredholm.det_one_sub_X_smul_of_isNilpotent`: the two inputs to the block
  factorisation `TateFredholm.charPowerSeries_eq_pow_mul_of_riesz`.
* `TateFredholm.finrank_ker_one_sub_smul_pow` (`dim N(a) = h`) and
  `TateFredholm.exists_riesz_decomposition` (Serre Prop. 12 in full).

## References

* [Serre1962] Serre, *Endomorphismes complètement continus des espaces de Banach
  p-adiques*, Publ. Math. IHÉS 12 (1962), 69–85.  The sections formalised here are
  §5 (pp. 76–77), §6 (pp. 78–79) and §7 (pp. 80–81); the per-declaration docstrings
  carry the individual page references.
* [Buzzard2007] Buzzard, *Eigenvarieties*, §3 (pp. 22–23).
-/

open Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace PowerSeries

section HasseDeriv

variable {R : Type*} [Semiring R]

/-- The `k`-th divided (Hasse) derivative of a power series: the coefficient of `Xⁿ` in
`hasseDeriv k f` is `(n + k).choose k * coeff (n + k) f`.  Mirrors
`Polynomial.hasseDeriv`; Serre's `Δˢ` [Serre1962, §7 p. 80], Buzzard's `∆ˢ`
[Buzzard2007, p. 22]. -/
def hasseDeriv (k : ℕ) (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n ↦ (n + k).choose k * coeff (n + k) f

/-- Coefficients of the `k`-th divided derivative, by definition. -/
@[simp]
theorem coeff_hasseDeriv (k n : ℕ) (f : PowerSeries R) :
    coeff n (hasseDeriv k f) = (n + k).choose k * coeff (n + k) f :=
  coeff_mk n _

/-- `Δ⁰` is the identity. -/
@[simp]
theorem hasseDeriv_zero (f : PowerSeries R) : hasseDeriv 0 f = f := PowerSeries.ext fun n ↦ by
  rw [coeff_hasseDeriv, Nat.add_zero, Nat.choose_zero_right, Nat.cast_one, one_mul]


end HasseDeriv

section EvalT

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]

/-- Evaluation of a power series at a point, as an unconditional tsum
`∑' n, coeff n f * a ^ n` (junk value when not summable).  This is the norm-radius
evaluation of an entire (restricted) series; mathlib's `PowerSeries.eval₂` is
adic-topology-only and does not apply over a normed ring. -/
def evalT (a : R) (f : PowerSeries R) : R :=
  ∑' n, coeff n f * a ^ n

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- `evalT` of a polynomial is its evaluation. -/
theorem evalT_coe (a : R) (P : Polynomial R) : evalT a (P : PowerSeries R) = P.eval a := by
  rw [evalT, tsum_eq_sum (s := Finset.range (P.natDegree + 1)) fun n hn ↦ by
    rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt
      (by rw [Finset.mem_range, not_lt] at hn; omega), zero_mul], Polynomial.eval_eq_sum_range]
  exact Finset.sum_congr rfl fun n _ ↦ by rw [Polynomial.coeff_coe]

-- The cofinite form of the standing hypothesis.  Note that `‖a ^ n‖ ≤ ‖a‖ ^ n` may fail
-- at `n = 0` (the section has no `NormOneClass`), so the bound is only eventual.
private theorem tendsto_coeff_mul_pow_cofinite {a : R} {f : PowerSeries R}
    (hf : Tendsto (fun n ↦ ‖coeff n f‖ * ‖a‖ ^ n) atTop (𝓝 0)) :
    Tendsto (fun n ↦ coeff n f * a ^ n) cofinite (𝓝 0) := by
  rw [Nat.cofinite_eq_atTop]
  exact squeeze_zero_norm' ((eventually_gt_atTop 0).mono fun n hn ↦ (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_pow_le' a hn) (norm_nonneg _))) hf

/-- The standing summability hypothesis for `evalT`: the series is restricted at the
radius `‖a‖` (`isRestricted_iff'` shape). -/
theorem summable_coeff_mul_pow {a : R} {f : PowerSeries R}
    (hf : Tendsto (fun n ↦ ‖coeff n f‖ * ‖a‖ ^ n) atTop (𝓝 0)) :
    Summable fun n ↦ coeff n f * a ^ n :=
  TateFredholm.summable_of_tendsto_cofinite (tendsto_coeff_mul_pow_cofinite hf)

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- A series restricted at radius `c` satisfies the standing hypothesis of `evalT` at every
point of norm `≤ c`. -/
theorem tendsto_norm_coeff_mul_pow_of_isRestricted {c : ℝ} {f : PowerSeries R}
    (hf : IsRestricted c f) {a : R} (ha : ‖a‖ ≤ c) :
    Tendsto (fun n ↦ ‖coeff n f‖ * ‖a‖ ^ n) atTop (𝓝 0) :=
  squeeze_zero (fun n ↦ mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg a) n))
    (fun n ↦ mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg a) ha n) (norm_nonneg _))
    ((isRestricted_iff' c f).mp hf)

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- Evaluation of a constant series. -/
@[simp]
theorem evalT_C (a r : R) : evalT a (C r) = r := by
  rw [evalT, tsum_eq_single 0 fun n hn ↦ by simp [coeff_C, hn], coeff_zero_C, pow_zero, mul_one]

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- Evaluation of the constant series `1`. -/
@[simp]
theorem evalT_one (a : R) : evalT a (1 : PowerSeries R) = 1 := by
  simpa using evalT_C a (1 : R)

/-- Evaluation is additive on series restricted at the radius `‖a‖`. -/
theorem evalT_add {a : R} {f g : PowerSeries R}
    (hf : Tendsto (fun n ↦ ‖coeff n f‖ * ‖a‖ ^ n) atTop (𝓝 0))
    (hg : Tendsto (fun n ↦ ‖coeff n g‖ * ‖a‖ ^ n) atTop (𝓝 0)) :
    evalT a (f + g) = evalT a f + evalT a g :=
  (tsum_congr fun n ↦ by rw [map_add, add_mul]).trans
    ((summable_coeff_mul_pow hf).tsum_add (summable_coeff_mul_pow hg))

/-- Evaluation is subtractive on series restricted at the radius `‖a‖`. -/
theorem evalT_sub {a : R} {f g : PowerSeries R}
    (hf : Tendsto (fun n ↦ ‖coeff n f‖ * ‖a‖ ^ n) atTop (𝓝 0))
    (hg : Tendsto (fun n ↦ ‖coeff n g‖ * ‖a‖ ^ n) atTop (𝓝 0)) :
    evalT a (f - g) = evalT a f - evalT a g :=
  (tsum_congr fun n ↦ by rw [map_sub, sub_mul]).trans
    ((summable_coeff_mul_pow hf).tsum_sub (summable_coeff_mul_pow hg))

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- Evaluation of the series `X`. -/
@[simp]
theorem evalT_X (a : R) : evalT a X = a := by
  rw [evalT, tsum_eq_single 1 fun n hn ↦ by simp [coeff_X, hn], coeff_one_X, one_mul, pow_one]

/-- The product of two cofinitely-null families is cofinitely null on the product index —
the ultrametric substitute for absolute convergence.  For `ε > 0` the bad set
`{x | ε ≤ ‖F x.1 * G x.2‖}` sits inside the product of the two `(ε/B)`-bad sets, where `B`
bounds both families; both factors are finite. -/
private theorem summable_mul_of_tendsto_cofinite {ι κ : Type*} {F : ι → R} {G : κ → R}
    (hF : Tendsto F cofinite (𝓝 0)) (hG : Tendsto G cofinite (𝓝 0)) :
    Summable fun x : ι × κ ↦ F x.1 * G x.2 := by
  obtain ⟨Bf, hBf⟩ := TateFredholm.bddAbove_range_norm_of_tendsto_cofinite hF
  obtain ⟨Bg, hBg⟩ := TateFredholm.bddAbove_range_norm_of_tendsto_cofinite hG
  set B : ℝ := max (max Bf Bg) 1
  have hB0 : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hFB : ∀ i, ‖F i‖ ≤ B :=
    fun i ↦ (hBf ⟨i, rfl⟩).trans ((le_max_left Bf Bg).trans (le_max_left _ _))
  have hGB : ∀ k, ‖G k‖ ≤ B :=
    fun k ↦ (hBg ⟨k, rfl⟩).trans ((le_max_right Bf Bg).trans (le_max_left _ _))
  refine TateFredholm.summable_of_tendsto_cofinite (Metric.tendsto_nhds.mpr fun ε hε ↦ ?_)
  have hεB : 0 < ε / B := div_pos hε hB0
  /- One factor small and the other bounded already forces the product below `ε`. -/
  have hstep : ∀ p q : R, ‖q‖ ≤ B → ‖p‖ < ε / B → ‖p * q‖ < ε := fun p q hq hp ↦
    ((norm_mul_le p q).trans (mul_le_mul_of_nonneg_left hq (norm_nonneg _))).trans_lt
      ((mul_lt_mul_of_pos_right hp hB0).trans_eq (div_mul_cancel₀ ε hB0.ne'))
  have hSF : {i : ι | ε / B ≤ ‖F i‖}.Finite :=
    (Filter.eventually_cofinite.mp
      (by simpa [dist_zero_right] using Metric.tendsto_nhds.mp hF _ hεB)).subset
      fun _ hi ↦ not_lt.mpr hi
  have hSG : {k : κ | ε / B ≤ ‖G k‖}.Finite :=
    (Filter.eventually_cofinite.mp
      (by simpa [dist_zero_right] using Metric.tendsto_nhds.mp hG _ hεB)).subset
      fun _ hk ↦ not_lt.mpr hk
  rw [Filter.eventually_cofinite]
  refine (hSF.prod hSG).subset fun x hx ↦ ?_
  simp only [Set.mem_ofPred_eq, dist_zero_right, not_lt] at hx
  exact Set.mem_prod.mpr
    ⟨not_lt.mp fun h ↦ absurd hx (not_le.mpr (hstep _ _ (hGB x.2) h)),
      not_lt.mp fun h ↦ absurd hx (not_le.mpr
        ((congrArg (‖·‖) (mul_comm (F x.1) (G x.2))).trans_lt (hstep _ _ (hFB x.1) h)))⟩

/-- Cauchy product: evaluation is multiplicative on series restricted at the radius.
The product summability comes from the cofinite criterion (a product of two null
families has finite `ε`-bad set `bad_f × bad_g`), then
`Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`. -/
theorem evalT_mul {a : R} {f g : PowerSeries R}
    (hf : Tendsto (fun n ↦ ‖coeff n f‖ * ‖a‖ ^ n) atTop (𝓝 0))
    (hg : Tendsto (fun n ↦ ‖coeff n g‖ * ‖a‖ ^ n) atTop (𝓝 0)) :
    evalT a (f * g) = evalT a f * evalT a g := by
  have hfg := summable_mul_of_tendsto_cofinite (tendsto_coeff_mul_pow_cofinite hf)
    (tendsto_coeff_mul_pow_cofinite hg)
  rw [evalT, evalT, evalT, (summable_coeff_mul_pow hf).tsum_mul_tsum_eq_tsum_sum_antidiagonal
    (summable_coeff_mul_pow hg) hfg]
  refine tsum_congr fun n ↦ ?_
  rw [coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [← Finset.mem_antidiagonal.mp hp, pow_add]
  ring

private theorem evalT_one_sub_C_mul_X (a b : R) : evalT a (1 - C b * X) = 1 - b * a := by
  have hT : ∀ {f : PowerSeries R}, IsRestricted ‖a‖ f →
      Tendsto (fun n ↦ ‖coeff n f‖ * ‖a‖ ^ n) atTop (𝓝 0) :=
    fun hf ↦ tendsto_norm_coeff_mul_pow_of_isRestricted hf le_rfl
  rw [evalT_sub (hT (isRestricted_one ‖a‖))
      (hT (isRestricted.mul ‖a‖ (isRestricted_C ‖a‖ b) (isRestricted_X ‖a‖))),
    evalT_one, evalT_mul (hT (isRestricted_C ‖a‖ b)) (hT (isRestricted_X ‖a‖)),
    evalT_C, evalT_X]

omit [CompleteSpace R] in
/-- Divided derivatives preserve restrictedness at a positive radius: the binomial factor
is an `ℕ`-multiple, hence norm-nonincreasing ultrametrically, and the index shift only
costs the constant `(c ^ k)⁻¹`. -/
theorem isRestricted_hasseDeriv {c : ℝ} (hc : 0 < c) {f : PowerSeries R}
    (hf : IsRestricted c f) (k : ℕ) : IsRestricted c (hasseDeriv k f) := by
  rw [isRestricted_iff']
  have hbase : Tendsto (fun n ↦ ‖coeff (n + k) f‖ * c ^ (n + k) * (c ^ k)⁻¹) atTop (𝓝 0) := by
    simpa using
      (((isRestricted_iff' c f).mp hf).comp (tendsto_add_atTop_nat k)).mul_const (c ^ k)⁻¹
  refine squeeze_zero (fun n ↦ mul_nonneg (norm_nonneg _) (pow_nonneg hc.le n))
    (fun n ↦ ?_) hbase
  have hnorm : ‖coeff n (hasseDeriv k f)‖ ≤ ‖coeff (n + k) f‖ := by
    rw [coeff_hasseDeriv, ← nsmul_eq_mul]
    exact IsUltrametricDist.norm_nsmul_le _ _
  rw [show c ^ n = c ^ (n + k) * (c ^ k)⁻¹ by
        rw [pow_add, mul_inv_cancel_right₀ (pow_ne_zero k hc.ne')], ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnorm (pow_nonneg hc.le _))
    (inv_nonneg.mpr (pow_nonneg hc.le k))

private theorem coeff_zero_one_sub_C_mul_X_mul (b : R) (f : PowerSeries R) :
    coeff 0 ((1 - C b * X) * f) = coeff 0 f := by
  rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul, coeff_zero_X_mul, mul_zero, sub_zero]

private theorem coeff_succ_one_sub_C_mul_X_mul (b : R) (f : PowerSeries R) (n : ℕ) :
    coeff (n + 1) ((1 - C b * X) * f) = coeff (n + 1) f - b * coeff n f := by
  rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul, coeff_succ_X_mul]

/-- The affine product rule for divided derivatives:
`Δᵏ⁺¹((1 - bX)·f) = (1 - bX)·Δᵏ⁺¹f - b·Δᵏf` [Buzzard2007, p. 22].  Proved coefficientwise;
the two binomial coefficients on the right recombine by Pascal's rule. -/
theorem hasseDeriv_one_sub_C_mul_X_mul (b : R) (k : ℕ) (f : PowerSeries R) :
    hasseDeriv (k + 1) ((1 - C b * X) * f) =
      (1 - C b * X) * hasseDeriv (k + 1) f - C b * hasseDeriv k f := by
  refine PowerSeries.ext fun n ↦ ?_
  rw [map_sub, coeff_C_mul, coeff_hasseDeriv, coeff_hasseDeriv]
  cases n with
  | zero =>
    rw [Nat.zero_add, Nat.zero_add, coeff_zero_one_sub_C_mul_X_mul,
      coeff_succ_one_sub_C_mul_X_mul, coeff_hasseDeriv, Nat.zero_add]
    push_cast [Nat.choose_self]
    ring
  | succ j =>
    have e1 : j + 1 + (k + 1) = j + k + 1 + 1 := by omega
    rw [e1, show j + 1 + k = j + k + 1 by omega, coeff_succ_one_sub_C_mul_X_mul,
      coeff_succ_one_sub_C_mul_X_mul, coeff_hasseDeriv, coeff_hasseDeriv, e1,
      show j + (k + 1) = j + k + 1 by omega, Nat.choose_succ_succ' (j + k + 1) k]
    push_cast
    ring

/-- The combined divided-Taylor evaluation at the factored form, by induction on the
exponent: peel one factor `1 - bX` (whose value at `a` is `1 - b·a = 0`) using the affine
product rule. -/
private theorem evalT_hasseDeriv_pow_mul_aux {a b : R} (hba : b * a = 1) {g : PowerSeries R}
    (hg : ∀ c : ℝ, 0 < c → IsRestricted c g) (h : ℕ) :
    ∀ s ≤ h, evalT a (hasseDeriv s ((1 - C b * X) ^ h * g)) =
      if s = h then (-b) ^ h * evalT a g else 0 := by
  set c : ℝ := max ‖a‖ 1
  have hc : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hT : ∀ {F : PowerSeries R}, IsRestricted c F →
      Tendsto (fun n ↦ ‖coeff n F‖ * ‖a‖ ^ n) atTop (𝓝 0) :=
    fun hF ↦ tendsto_norm_coeff_mul_pow_of_isRestricted hF (le_max_left _ _)
  have hLres : IsRestricted c (1 - C b * X : PowerSeries R) :=
    isRestricted.sub c (isRestricted_one c) (isRestricted.mul c (isRestricted_C c b)
      (isRestricted_X c))
  have hCres : IsRestricted c (C b : PowerSeries R) := isRestricted_C c b
  have hL0 : evalT a (1 - C b * X : PowerSeries R) = 0 := by
    rw [evalT_one_sub_C_mul_X, hba, sub_self]
  induction h with
  | zero =>
    intro s hs
    simp [Nat.le_zero.mp hs]
  | succ h ih =>
    have hmul : IsRestricted c ((1 - C b * X : PowerSeries R) ^ h * g) :=
      isRestricted.mul c (isRestricted.pow c hLres h) (hg c hc)
    have hpeel : ((1 - C b * X : PowerSeries R) ^ (h + 1) * g) =
        (1 - C b * X) * ((1 - C b * X) ^ h * g) := by ring
    intro s hs
    match s with
    | 0 =>
      rw [if_neg (Nat.zero_ne_add_one h), hasseDeriv_zero, hpeel,
        evalT_mul (hT hLres) (hT hmul), hL0, zero_mul]
    | (k + 1) =>
      have hDk := isRestricted_hasseDeriv hc hmul k
      have hDk1 := isRestricted_hasseDeriv hc hmul (k + 1)
      rw [hpeel, hasseDeriv_one_sub_C_mul_X_mul,
        evalT_sub (hT (isRestricted.mul c hLres hDk1))
          (hT (isRestricted.mul c hCres hDk)),
        evalT_mul (hT hLres) (hT hDk1), hL0, zero_mul,
        evalT_mul (hT hCres) (hT hDk), evalT_C, zero_sub, ih k (Nat.succ_le_succ_iff.mp hs)]
      rcases eq_or_ne k h with rfl | hkh
      · rw [if_pos rfl, if_pos rfl, pow_succ]
        ring
      · rw [if_neg hkh, if_neg (by omega : k + 1 ≠ h + 1), mul_zero, neg_zero]

/-- Divided Taylor vanishing: evaluating `Δˢ ((1 - bX)ʰ · g)` at a point `a` with
`b * a = 1` gives `0` for `s < h` [Buzzard2007, p. 22]. -/
theorem evalT_hasseDeriv_pow_mul_of_lt {a b : R} (hba : b * a = 1) {g : PowerSeries R}
    (hg : ∀ c : ℝ, 0 < c → IsRestricted c g) {h s : ℕ} (hs : s < h) :
    evalT a (hasseDeriv s ((1 - C b * X) ^ h * g)) = 0 := by
  rw [evalT_hasseDeriv_pow_mul_aux hba hg h s hs.le, if_neg hs.ne]

/-- Divided Taylor leading term: evaluating `Δʰ ((1 - bX)ʰ · g)` at `a` with `b * a = 1`
gives `(-b)ʰ * g(a)` [Buzzard2007, p. 22]. -/
theorem evalT_hasseDeriv_pow_mul_self {a b : R} (hba : b * a = 1) {g : PowerSeries R}
    (hg : ∀ c : ℝ, 0 < c → IsRestricted c g) (h : ℕ) :
    evalT a (hasseDeriv h ((1 - C b * X) ^ h * g)) = (-b) ^ h * evalT a g := by
  rw [evalT_hasseDeriv_pow_mul_aux hba hg h h le_rfl, if_pos rfl]

end EvalT

section Order

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem isRestricted_of_le {R : Type*} [NormedRing R] {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d)
    {f : PowerSeries R} (hf : IsRestricted d f) : IsRestricted c f :=
  (isRestricted_iff' c f).mpr <| squeeze_zero (fun _ ↦ by positivity) (fun _ ↦ by gcongr)
    ((isRestricted_iff' d f).mp hf)

private theorem evalT_zero_eq_coeff_zero {R : Type*} [NormedCommRing R] (f : PowerSeries R) :
    evalT (0 : R) f = coeff 0 f := by
  rw [evalT, tsum_eq_single 0 fun n hn ↦ by simp [zero_pow hn], pow_zero, mul_one]

-- The linear factor `1 - a⁻¹X`, as an element of `Restricted K c`.
private def linFactor (a : K) (c : ℝ) : Restricted K c :=
  ⟨1 - C a⁻¹ * X, isRestricted.sub c (isRestricted_one c)
    (isRestricted.mul c (isRestricted_C c a⁻¹) (isRestricted_X c))⟩

private theorem val_linFactor (a : K) (c : ℝ) : (linFactor a c).1 = 1 - C a⁻¹ * X := rfl

/-- A restricted power series as an element of `Restricted R c`.  A definition rather than an
inline `⟨f, hf⟩`: the anonymous constructor unfolds the opaque type `Restricted R c` and loses
its normed-ring instances. -/
def restrictedOf {R : Type*} [NormedRing R] [IsUltrametricDist R] {c : ℝ}
    {f : PowerSeries R} (hf : IsRestricted c f) : Restricted R c := ⟨f, hf⟩

private theorem val_restrictedOf {c : ℝ} {f : PowerSeries K} (hf : IsRestricted c f) :
    (restrictedOf hf).1 = f := rfl

private theorem coeff_linFactor (a : K) (c : ℝ) (n : ℕ) : coeff n (linFactor a c).1 =
    if n = 0 then 1 else if n = 1 then -a⁻¹ else 0 := by
  obtain _ | _ | k := n <;> simp [val_linFactor]

private theorem norm_linFactor {a : K} (ha0 : a ≠ 0) {c : ℝ} [Fact (0 < c)] (hac : ‖a‖ < c) :
    ‖linFactor a c‖ = ‖a‖⁻¹ * c := by
  have h1 : 1 < ‖a‖⁻¹ * c := (one_lt_inv_mul₀ (norm_pos_iff.mpr ha0)).mpr hac
  have hc1 : ‖coeff 1 (linFactor a c).1‖ * c ^ 1 = ‖a‖⁻¹ * c := by
    rw [coeff_linFactor, if_neg one_ne_zero, if_pos rfl, norm_neg, norm_inv, pow_one]
  refine le_antisymm ((Restricted.norm_le_iff c _).mpr fun i ↦ ?_)
    (hc1 ▸ Restricted.norm_coeff_mul_pow_le c _ 1)
  match i with
  | 0 => simpa [coeff_linFactor] using h1.le
  | 1 => exact hc1.le
  | k + 2 => simpa [coeff_linFactor] using zero_le_one.trans h1.le

private theorem isMulDistinguished_linFactor {a : K} (ha0 : a ≠ 0) {c : ℝ} [Fact (0 < c)]
    (hac : ‖a‖ < c) : IsMulDistinguished c (linFactor a c).1 1 := by
  have hc1 : coeff 1 (linFactor a c).1 = -a⁻¹ := by
    rw [coeff_linFactor, if_neg one_ne_zero, if_pos rfl]
  have hnc1 : ‖coeff 1 (linFactor a c).1‖ * c ^ 1 = ‖a‖⁻¹ * c := by
    rw [hc1, norm_neg, norm_inv, pow_one]
  refine ⟨hc1 ▸ (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (inv_ne_zero ha0))).isNormMulUnit, ?_,
    fun t ht ↦ ?_⟩
  · rw [hnc1, ← Restricted.norm_def c, norm_linFactor ha0 hac]
  · rw [hnc1, coeff_linFactor, if_neg (by omega : t ≠ 0), if_neg (by omega : t ≠ 1)]
    simpa using one_pos.trans ((one_lt_inv_mul₀ (norm_pos_iff.mpr ha0)).mpr hac)

private theorem exists_factor_isRestricted {f : PowerSeries K}
    (hf : ∀ c : ℝ, 0 < c → IsRestricted c f) {a : K} (ha0 : a ≠ 0) (ha : evalT a f = 0) {c : ℝ}
    (hac : ‖a‖ < c) : ∃ g : PowerSeries K, IsRestricted c g ∧ f = (1 - C a⁻¹ * X) * g := by
  have hc0 : (0 : ℝ) < c := (norm_nonneg a).trans_lt hac
  have : Fact (0 < c) := ⟨hc0⟩
  have hLres : IsRestricted c (1 - C a⁻¹ * X : PowerSeries K) := (linFactor a c).2
  obtain ⟨q, r, hrdeg, hfeq⟩ := Restricted.weierstrassDivision_exists_of_isMulDistinguished
    (isMulDistinguished_linFactor ha0 hac) (restrictedOf (hf c hc0))
  have hraw : f = (1 - C a⁻¹ * X) * q.1 + (r : PowerSeries K) := congrArg Subtype.val hfeq
  have hrC : (r : PowerSeries K) = C (r.coeff 0) := by
    conv_lhs => rw [Polynomial.eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp hrdeg)]
    exact Polynomial.coe_C _
  have hT : ∀ {F : PowerSeries K}, IsRestricted c F →
      Tendsto (fun n ↦ ‖coeff n F‖ * ‖a‖ ^ n) atTop (𝓝 0) :=
    fun hF ↦ tendsto_norm_coeff_mul_pow_of_isRestricted hF hac.le
  have hLq : evalT a ((1 - C a⁻¹ * X) * q.1) = 0 := by
    rw [evalT_mul (hT hLres) (hT q.2), evalT_one_sub_C_mul_X a a⁻¹, inv_mul_cancel₀ ha0,
      sub_self, zero_mul]
  have hr0 : r.coeff 0 = 0 := by
    have h2 := (congrArg (evalT a) hraw).symm
    rwa [ha, evalT_add (hT (isRestricted.mul c hLres q.2))
      (hT (Polynomial.isRestricted_toPowerSeries c r)), hLq, zero_add, hrC, evalT_C] at h2
  exact ⟨q.1, q.2, by rw [hraw, hrC, hr0, map_zero, add_zero]⟩

private theorem pow_le_norm_of_eq_pow_mul {a : K} (ha0 : a ≠ 0) {c : ℝ} [Fact (0 < c)]
    (hac : ‖a‖ < c) {f g : PowerSeries K} (hfres : IsRestricted c f) (hgres : IsRestricted c g)
    (hg0 : coeff 0 g = 1) {s : ℕ} (hfg : f = (1 - C a⁻¹ * X) ^ s * g) :
    (‖a‖⁻¹ * c) ^ s ≤ ‖restrictedOf hfres‖ := by
  have hFG : restrictedOf hfres = linFactor a c ^ s * restrictedOf hgres := Subtype.ext hfg
  have hG1 : (1 : ℝ) ≤ ‖restrictedOf hgres‖ := by
    simpa [val_restrictedOf, hg0] using Restricted.norm_coeff_mul_pow_le c (restrictedOf hgres) 0
  rw [hFG, norm_mul, norm_pow, norm_linFactor ha0 hac]
  exact le_mul_of_one_le_right
    (pow_nonneg (zero_le_one.trans ((one_lt_inv_mul₀ (norm_pos_iff.mpr ha0)).mpr hac).le) s) hG1

/-- Division step: an entire series with constant term `1` vanishing at `a ≠ 0` has the
distinguished linear factor `1 - a⁻¹X`.  Proved through the Weierstrass division of
`PhD.ForMathlib` at a radius `c > ‖a‖` (where `1 - a⁻¹X` is `IsMulDistinguished c 1`),
the remainder being the constant `f(a) = 0`. -/
theorem exists_factor_of_evalT_eq_zero {f : PowerSeries K} (hf : ∀ c : ℝ, 0 < c → IsRestricted c f)
    {a : K} (ha0 : a ≠ 0) (ha : evalT a f = 0) :
    ∃ g : PowerSeries K, (∀ c : ℝ, 0 < c → IsRestricted c g) ∧ f = (1 - C a⁻¹ * X) * g := by
  obtain ⟨g, -, hg⟩ := exists_factor_isRestricted hf ha0 ha (c := ‖a‖ + 1) (lt_add_one _)
  refine ⟨g, fun c hc ↦ ?_, hg⟩
  obtain ⟨g', hg'res, hg'⟩ := exists_factor_isRestricted hf ha0 ha (c := max c (‖a‖ + 1))
    ((lt_add_one _).trans_le (le_max_right _ _))
  obtain rfl := (isUnit_iff_constantCoeff.mpr (by simp)).mul_left_cancel (hg.symm.trans hg')
  exact isRestricted_of_le hc.le (le_max_left _ _) hg'res

/-- A zero of an entire series with constant term `1` is nonzero and has finite order in
Buzzard's divided-derivative sense [Buzzard2007, pp. 22–23]. -/
theorem exists_order_of_evalT_eq_zero {f : PowerSeries K} (hf : ∀ c : ℝ, 0 < c → IsRestricted c f)
    (h0 : coeff 0 f = 1) {a : K} (ha : evalT a f = 0) :
    a ≠ 0 ∧ ∃ h : ℕ, 1 ≤ h ∧ (∀ s < h, evalT a (hasseDeriv s f) = 0) ∧
      evalT a (hasseDeriv h f) ≠ 0 := by
  classical
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [evalT_zero_eq_coeff_zero, h0] at ha
    exact one_ne_zero ha
  refine ⟨ha0, ?_⟩
  have hac : ‖a‖ < ‖a‖ + 1 := lt_add_one _
  have hc0 : (0 : ℝ) < ‖a‖ + 1 := (norm_nonneg a).trans_lt hac
  have : Fact (0 < ‖a‖ + 1) := ⟨hc0⟩
  /- Each split-off factor multiplies the Gauss norm at radius `‖a‖ + 1` by
  `‖a‖⁻¹(‖a‖ + 1)`, which exceeds `1`, so `‖f‖` bounds the number of such factors. -/
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ‖restrictedOf (hf _ hc0)‖
    ((one_lt_inv_mul₀ (norm_pos_iff.mpr ha0)).mpr hac)
  have hexN : ∃ s : ℕ, ¬ ∃ g : PowerSeries K, (∀ d : ℝ, 0 < d → IsRestricted d g) ∧
      coeff 0 g = 1 ∧ f = (1 - C a⁻¹ * X) ^ s * g :=
    ⟨N, fun ⟨g, hgres, hg0, hfg⟩ ↦ absurd
      (pow_le_norm_of_eq_pow_mul ha0 hac (hf _ hc0) (hgres _ hc0) hg0 hfg) (not_le.mpr hN)⟩
  have hfind := Nat.find_spec hexN
  obtain ⟨k, hkeq⟩ : ∃ k, Nat.find hexN = k + 1 := Nat.exists_eq_succ_of_ne_zero fun hz ↦
    hfind (by rw [hz]; exact ⟨f, hf, h0, by rw [pow_zero, one_mul]⟩)
  rw [hkeq] at hfind
  obtain ⟨g, hgres, hg0, hfg⟩ := not_not.mp (Nat.find_min hexN (by omega : k < Nat.find hexN))
  have hga : evalT a g ≠ 0 := fun hga0 ↦ by
    obtain ⟨g', hg'res, hgg'⟩ := exists_factor_of_evalT_eq_zero hgres ha0 hga0
    refine hfind ⟨g', hg'res, ?_, by rw [hfg, hgg', pow_succ, mul_assoc]⟩
    rwa [hgg', coeff_zero_one_sub_C_mul_X_mul] at hg0
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr fun hz ↦ hga <| by
    rw [hz, pow_zero, one_mul] at hfg
    exact hfg ▸ ha
  refine ⟨k, hk1, fun s hs ↦ ?_, ?_⟩ <;> rw [hfg]
  · exact evalT_hasseDeriv_pow_mul_of_lt (inv_mul_cancel₀ ha0) hgres hs
  · rw [evalT_hasseDeriv_pow_mul_self (inv_mul_cancel₀ ha0) hgres k]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr (inv_ne_zero ha0))) hga

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The order of a zero in the divided-derivative sense is unique. -/
theorem hasseDeriv_order_unique {f : PowerSeries K} {a : K} {h h' : ℕ}
    (h0 : ∀ s < h, evalT a (hasseDeriv s f) = 0) (hh : evalT a (hasseDeriv h f) ≠ 0)
    (h0' : ∀ s < h', evalT a (hasseDeriv s f) = 0) (hh' : evalT a (hasseDeriv h' f) ≠ 0) : h = h' :=
  le_antisymm (not_lt.mp fun hgt ↦ hh' (h0 h' hgt)) (not_lt.mp fun hlt ↦ hh (h0' h hlt))

end Order

end PowerSeries

namespace TateFredholm

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormOneClass R]

section OpLimit

variable {M N : Type*}
  [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]

/-- `L` is the operator-norm limit of the sequence `T`.  The file's substitute for a
(deliberately absent) normed-space structure on `M →L[R] N`; existence of limits comes
from `exists_lim_of_cauchySeq`. -/
def IsOpLimit (T : ℕ → M →L[R] N) (L : M →L[R] N) : Prop :=
  Tendsto (fun n ↦ ‖T n - L‖) atTop (𝓝 0)

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- Operator-norm limits are unique. -/
theorem IsOpLimit.unique [IsTate R] {T : ℕ → M →L[R] N} {L L' : M →L[R] N}
    (h : IsOpLimit T L) (h' : IsOpLimit T L') : L = L' := by
  have key : ∀ n, ‖L - L'‖ ≤ ‖T n - L‖ + ‖T n - L'‖ := fun n ↦ by
    rw [show L - L' = -(T n - L) + (T n - L') by abel]
    exact (norm_add_le _ _).trans_eq (by rw [opNorm_neg])
  exact sub_eq_zero.mp ((opNorm_eq_zero_iff _).mp (le_antisymm
    (ge_of_tendsto' (by simpa using Filter.Tendsto.add h h') key) (opNorm_nonneg _)))

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- Operator-norm limits add. -/
theorem IsOpLimit.add [IsTate R] {T T' : ℕ → M →L[R] N} {L L' : M →L[R] N}
    (h : IsOpLimit T L) (h' : IsOpLimit T' L') :
    IsOpLimit (fun n ↦ T n + T' n) (L + L') := by
  refine squeeze_zero (fun n ↦ opNorm_nonneg _) (fun n ↦ ?_)
    (by simpa using Filter.Tendsto.add h h')
  rw [show T n + T' n - (L + L') = T n - L + (T' n - L') by abel]
  exact norm_add_le _ _

omit [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R] [IsBoundedSMul R M]
  [IsBoundedSMul R N] in
/-- A constant sequence converges to its value. -/
theorem IsOpLimit.const (L : M →L[R] N) : IsOpLimit (fun _ ↦ L) L :=
  tendsto_const_nhds.congr fun _ ↦ by rw [sub_self, opNorm_zero]

variable [IsTate R]

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- Left composition with a fixed operator preserves operator-norm limits. -/
theorem IsOpLimit.comp_left {T : ℕ → M →L[R] M} {L : M →L[R] M}
    (h : IsOpLimit T L) (w : M →L[R] M) :
    IsOpLimit (fun n ↦ w * T n) (w * L) := by
  refine squeeze_zero (fun n ↦ opNorm_nonneg _) (fun n ↦ ?_)
    (by simpa using Filter.Tendsto.const_mul ‖w‖ h)
  rw [← mul_sub]
  exact opNorm_mul_le _ _

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- Right composition with a fixed operator preserves operator-norm limits. -/
theorem IsOpLimit.comp_right {T : ℕ → M →L[R] M} {L : M →L[R] M}
    (h : IsOpLimit T L) (w : M →L[R] M) :
    IsOpLimit (fun n ↦ T n * w) (L * w) := by
  refine squeeze_zero (fun n ↦ opNorm_nonneg _) (fun n ↦ ?_)
    (by simpa using Filter.Tendsto.mul_const ‖w‖ h)
  rw [← sub_mul]
  exact opNorm_mul_le _ _

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- Scalar multiples of operator-norm limits. -/
theorem IsOpLimit.smul {T : ℕ → M →L[R] N} {L : M →L[R] N} (h : IsOpLimit T L) (c : R) :
    IsOpLimit (fun n ↦ c • T n) (c • L) := by
  refine squeeze_zero (fun n ↦ opNorm_nonneg _) (fun n ↦ ?_)
    (by simpa using Filter.Tendsto.const_mul ‖c‖ h)
  rw [← smul_sub]
  exact opNorm_smul_le _ _

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- Products of operator-norm limits. -/
theorem IsOpLimit.mul {T T' : ℕ → M →L[R] M} {L L' : M →L[R] M} (h : IsOpLimit T L)
    (h' : IsOpLimit T' L') : IsOpLimit (fun n ↦ T n * T' n) (L * L') := by
  have hg : Tendsto (fun n ↦ ‖T n - L‖ * (‖T' n - L'‖ + ‖L'‖) + ‖L‖ * ‖T' n - L'‖) atTop
      (𝓝 0) := by
    simpa using Filter.Tendsto.add (Filter.Tendsto.mul h (Filter.Tendsto.add_const ‖L'‖ h'))
      (Filter.Tendsto.const_mul ‖L‖ h')
  refine squeeze_zero (fun n ↦ opNorm_nonneg _) (fun n ↦ ?_) hg
  rw [show T n * T' n - L * L' = (T n - L) * T' n + L * (T' n - L') by noncomm_ring]
  refine (norm_add_le _ _).trans (add_le_add ((opNorm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left ?_ (opNorm_nonneg _))) (opNorm_mul_le _ _))
  calc ‖T' n‖ = ‖(T' n - L') + L'‖ := by rw [sub_add_cancel]
    _ ≤ ‖T' n - L'‖ + ‖L'‖ := norm_add_le _ _

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- Powers of operator-norm limits. -/
theorem IsOpLimit.pow {T : ℕ → M →L[R] M} {L : M →L[R] M} (h : IsOpLimit T L) (m : ℕ) :
    IsOpLimit (fun n ↦ T n ^ m) (L ^ m) := by
  induction m with
  | zero => simpa only [pow_zero] using IsOpLimit.const (1 : M →L[R] M)
  | succ m ih => simpa only [pow_succ] using ih.mul h

end OpLimit

variable {I : Type*} [DecidableEq I]

section CompactoidClosure

variable {J : Type*} [DecidableEq J]

omit [DecidableEq J] in
omit [DecidableEq J] in
/-- Matrix coefficients commute with negation. -/
@[simp]
theorem matrixCoeff_neg (u : c(I, R) →L[R] c(J, R)) (j : J) (i : I) :
    matrixCoeff (-u) j i = -matrixCoeff u j i := rfl

omit [DecidableEq J] in
/-- Public form of the row bound `‖matrixCoeff u j i‖ ≤ ‖u‖` (private in
`Fredholm.lean`). -/
theorem norm_matrixCoeff_le' [IsTate R] (u : c(I, R) →L[R] c(J, R)) (j : J) (i : I) :
    ‖matrixCoeff u j i‖ ≤ ‖u‖ :=
  calc ‖matrixCoeff u j i‖ ≤ ‖u (cSpace.single i 1)‖ := cSpace.norm_apply_le _ _
  _ ≤ ‖u‖ * ‖cSpace.single i (1 : R)‖ := le_opNorm _ _
  _ = ‖u‖ := by rw [cSpace.norm_single_one, mul_one]

-- The rows are bounded families, so `rowNorm` is a genuine supremum (`le_ciSup` applies).
private theorem bddAbove_range_norm_matrixCoeff [IsTate R] (u : c(I, R) →L[R] c(J, R))
    (j : J) : BddAbove (Set.range fun i ↦ ‖matrixCoeff u j i‖) :=
  ⟨‖u‖, by rintro _ ⟨i, rfl⟩; exact norm_matrixCoeff_le' u j i⟩

/-- The row norms are ultrametric: `rowNorm (u + v) j ≤ max (rowNorm u j) (rowNorm v j)`. -/
theorem rowNorm_add_le [IsTate R] (u v : c(I, R) →L[R] c(J, R)) (j : J) :
    rowNorm (u + v) j ≤ max (rowNorm u j) (rowNorm v j) :=
  Real.iSup_le (fun i ↦ (IsUltrametricDist.norm_add_le_max (matrixCoeff u j i)
    (matrixCoeff v j i)).trans (max_le_max (le_ciSup (bddAbove_range_norm_matrixCoeff u j) i)
      (le_ciSup (bddAbove_range_norm_matrixCoeff v j) i)))
    (le_max_of_le_left (rowNorm_nonneg u j))

omit [DecidableEq J] in
/-- The row norms are invariant under negation. -/
@[simp]
theorem rowNorm_neg (u : c(I, R) →L[R] c(J, R)) (j : J) :
    rowNorm (-u) j = rowNorm u j :=
  iSup_congr fun i ↦ by rw [matrixCoeff_neg, norm_neg]

/-- Scalars scale the row norms: `rowNorm (a • u) j ≤ ‖a‖ * rowNorm u j`. -/
theorem rowNorm_smul_le [IsTate R] (a : R) (u : c(I, R) →L[R] c(J, R)) (j : J) :
    rowNorm (a • u) j ≤ ‖a‖ * rowNorm u j :=
  Real.iSup_le (fun i ↦ (norm_mul_le a (matrixCoeff u j i)).trans
    (mul_le_mul_of_nonneg_left (le_ciSup (bddAbove_range_norm_matrixCoeff u j) i)
      (norm_nonneg a)))
    (mul_nonneg (norm_nonneg a) (rowNorm_nonneg u j))

/-- Compactoid operators are closed under addition (the row norms are ultrametric). -/
theorem IsCompactoid.add [IsTate R] {u v : c(I, R) →L[R] c(J, R)}
    (hu : IsCompactoid u) (hv : IsCompactoid v) : IsCompactoid (u + v) := by
  refine squeeze_zero (fun j ↦ rowNorm_nonneg _ j) (fun j ↦ rowNorm_add_le u v j) ?_
  simpa using Filter.Tendsto.max hu hv

/-- Compactoid operators are closed under finite sums. -/
theorem IsCompactoid.finset_sum [IsTate R] {ι : Type*} (s : Finset ι)
    {f : ι → c(I, R) →L[R] c(J, R)} (hf : ∀ i ∈ s, IsCompactoid (f i)) :
    IsCompactoid (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isCompactoid_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

omit [DecidableEq J] in
/-- Compactoid operators are closed under negation. -/
theorem IsCompactoid.neg {u : c(I, R) →L[R] c(J, R)}
    (hu : IsCompactoid u) : IsCompactoid (-u) :=
  Filter.Tendsto.congr (fun j ↦ (rowNorm_neg u j).symm) hu

/-- Compactoid operators are closed under subtraction. -/
theorem IsCompactoid.sub [IsTate R] {u v : c(I, R) →L[R] c(J, R)}
    (hu : IsCompactoid u) (hv : IsCompactoid v) : IsCompactoid (u - v) :=
  sub_eq_add_neg u v ▸ hu.add hv.neg

/-- Compactoid operators are closed under scalar multiplication. -/
theorem IsCompactoid.smul [IsTate R] {u : c(I, R) →L[R] c(J, R)} (a : R)
    (hu : IsCompactoid u) : IsCompactoid (a • u) := by
  refine squeeze_zero (fun j ↦ rowNorm_nonneg _ j) (fun j ↦ rowNorm_smul_le a u j) ?_
  simpa using Filter.Tendsto.const_mul ‖a‖ hu

end CompactoidClosure

section Resolvent

/-- The coefficients `vₘ = ∑_{k ≤ m} cₖ u^{m-k}` of the Fredholm resolvent
`P(t, u) = det(1 - tu)/(1 - tu) = ∑ vₘ tᵐ` [Serre1962, §6 p. 78]. -/
def resolventCoeff (u : c(I, R) →L[R] c(I, R)) (m : ℕ) : c(I, R) →L[R] c(I, R) :=
  ∑ k ∈ Finset.range (m + 1), charCoeff u k • u ^ (m - k)

/-- The resolvent starts at `v₀ = 1`, since `c₀ = 1`. -/
@[simp]
theorem resolventCoeff_zero (u : c(I, R) →L[R] c(I, R)) : resolventCoeff u 0 = 1 := by
  simp [resolventCoeff]

/-- Serre's recursion `vₘ = cₘ·1 + u vₘ₋₁` [Serre1962, §6 p. 78]. -/
theorem resolventCoeff_succ (u : c(I, R) →L[R] c(I, R)) (m : ℕ) :
    resolventCoeff u (m + 1) = charCoeff u (m + 1) • 1 + u * resolventCoeff u m := by
  have h : u * resolventCoeff u m =
      ∑ k ∈ Finset.range (m + 1), charCoeff u k • u ^ (m + 1 - k) := by
    rw [resolventCoeff, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [mul_smul_comm, ← pow_succ', Nat.succ_sub (Finset.mem_range_succ_iff.mp hk)]
  rw [h, resolventCoeff, Finset.sum_range_succ_comm, Nat.sub_self, pow_zero]

/-- The defining identity `(1 - tu)·P(t, u) = det(1 - tu)`, coefficientwise. -/
theorem resolventCoeff_sub_mul (u : c(I, R) →L[R] c(I, R)) (m : ℕ) :
    resolventCoeff u (m + 1) - u * resolventCoeff u m = charCoeff u (m + 1) • 1 :=
  sub_eq_of_eq_add (resolventCoeff_succ u m)

/-- The identity operator has the identity matrix. -/
theorem matrixCoeff_one (j i : I) :
    matrixCoeff (1 : c(I, R) →L[R] c(I, R)) j i = if j = i then 1 else 0 := by
  by_cases h : j = i <;> simp [matrixCoeff, h, cSpace.single_apply_of_ne]

private theorem hasSum_matrixCoeff_mul (u w : c(I, R) →L[R] c(I, R)) (j i : I) :
    HasSum (fun k ↦ matrixCoeff w k i * matrixCoeff u j k) (matrixCoeff (u * w) j i) :=
  hasSum_matrixCoeff u (w (cSpace.single i 1)) j

/-- Off the support, the resolvent coefficients are scalar: `vₘ = cₘ` on the diagonal,
`0` elsewhere. -/
theorem matrixCoeff_resolventCoeff_of_notMem (u : c(I, R) →L[R] c(I, R)) (S : Finset I)
    (hS : ∀ j ∉ S, ∀ i, matrixCoeff u j i = 0) (m : ℕ) {j : I} (hj : j ∉ S) (i : I) :
    matrixCoeff (resolventCoeff u m) j i = if j = i then charCoeff u m else 0 := by
  cases m with
  | zero => simp [matrixCoeff_one]
  | succ m =>
  have h0 : matrixCoeff (u * resolventCoeff u m) j i = 0 :=
    (hasSum_matrixCoeff_mul u (resolventCoeff u m) j i).unique <| by
      simpa only [hS j hj, mul_zero] using hasSum_zero
  simp [resolventCoeff_succ, matrixCoeff_one, h0]

private theorem coeff_zero_ite_sub_X_mul_C_mul {A : Type*} [Ring A] {p : Prop} [Decidable p]
    (c : A) (P : Polynomial A) :
    (((if p then 1 else 0) - Polynomial.X * Polynomial.C c) * P).coeff 0 =
      if p then P.coeff 0 else 0 := by
  by_cases h : p
  · rw [if_pos h, if_pos h, sub_mul, one_mul, Polynomial.coeff_sub, mul_assoc,
      Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul, sub_zero]
  · rw [if_neg h, if_neg h, zero_sub, neg_mul, mul_assoc, Polynomial.coeff_neg,
      Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul, neg_zero]

private theorem coeff_succ_ite_sub_X_mul_C_mul {A : Type*} [Ring A] {p : Prop} [Decidable p]
    (c : A) (P : Polynomial A) (n : ℕ) :
    (((if p then 1 else 0) - Polynomial.X * Polynomial.C c) * P).coeff (n + 1) =
      (if p then P.coeff (n + 1) else 0) - c * P.coeff n := by
  by_cases h : p
  · rw [if_pos h, if_pos h, sub_mul, one_mul, Polynomial.coeff_sub, mul_assoc,
      Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]
  · rw [if_neg h, if_neg h, zero_sub, neg_mul, mul_assoc, Polynomial.coeff_neg,
      Polynomial.coeff_X_mul, Polynomial.coeff_C_mul, zero_sub]

private theorem matrixCoeff_mul_resolventCoeff_of_rows (u : c(I, R) →L[R] c(I, R)) (S : Finset I)
    (hS : ∀ j ∉ S, ∀ i, matrixCoeff u j i = 0) (n : ℕ) (p q : S) :
    matrixCoeff (u * resolventCoeff u n) p q =
      ∑ k : S, matrixCoeff u p k * matrixCoeff (resolventCoeff u n) k q := by
  have hz : ∀ k ∉ S,
      matrixCoeff (resolventCoeff u n) k (q : I) * matrixCoeff u (p : I) k = 0 := fun k hk ↦ by
    rw [matrixCoeff_resolventCoeff_of_notMem u S hS n hk (q : I),
      if_neg (by rintro rfl; exact hk q.2), zero_mul]
  rw [(hasSum_matrixCoeff_mul u (resolventCoeff u n) (p : I) (q : I)).unique
    (hasSum_sum_of_ne_finset_zero hz), ← Finset.sum_coe_sort S]
  exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _

/-- Finite case of Serre's Lemme 3, identification step: for a row-supported operator,
the resolvent coefficients on the block are the coefficients of the adjugate of
`1 - tA` [Serre1962, §6 p. 79, step a): "les formules de Cramer"]. -/
theorem matrixCoeff_resolventCoeff_of_rows (u : c(I, R) →L[R] c(I, R)) (S : Finset I)
    (hS : ∀ j ∉ S, ∀ i, matrixCoeff u j i = 0) (m : ℕ) (j i : S) :
    matrixCoeff (resolventCoeff u m) j i = Polynomial.coeff (Matrix.adjugate
      (1 - (Polynomial.X : Polynomial R) • Matrix.of fun p q : S ↦
        Polynomial.C (matrixCoeff u p q)) j i) m := by
  classical
  set B : Matrix S S (Polynomial R) := 1 - (Polynomial.X : Polynomial R) •
    Matrix.of fun p q : S ↦ Polynomial.C (matrixCoeff u p q) with hBdef
  have hdet : ∀ n : ℕ, B.det.coeff n = charCoeff u n := fun n ↦ by
    rw [hBdef]
    exact (charCoeff_eq_det_coeff u S hS n).symm
  have hBentry : ∀ p q : S, B p q =
      (if p = q then 1 else 0) - Polynomial.X * Polynomial.C (matrixCoeff u p q) := fun p q ↦ by
    rw [hBdef]
    simp only [Matrix.smul_of, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply,
      Pi.smul_apply, smul_eq_mul, Polynomial.X_mul_C]
  have hBmul0 : ∀ (p k : S) (P : Polynomial R),
      (B p k * P).coeff 0 = if p = k then P.coeff 0 else 0 := fun p k P ↦ by
    rw [hBentry, coeff_zero_ite_sub_X_mul_C_mul]
  have hBmul : ∀ (p k : S) (P : Polynomial R) (n : ℕ), (B p k * P).coeff (n + 1) =
      (if p = k then P.coeff (n + 1) else 0) - matrixCoeff u p k * P.coeff n :=
    fun p k P n ↦ by rw [hBentry, coeff_succ_ite_sub_X_mul_C_mul]
  have hcramer : ∀ (n : ℕ) (p q : S), ∑ k : S, (B p k * B.adjugate k q).coeff n =
      (B.det * (if p = q then 1 else 0)).coeff n := fun n p q ↦ by
    rw [← Polynomial.finsetSum_coeff, ← Matrix.mul_apply, Matrix.mul_adjugate, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
  have hdiag : ∀ (n : ℕ) (p q : S), charCoeff u n * (if (p : I) = (q : I) then 1 else 0) =
      (B.det * (if p = q then 1 else 0)).coeff n := fun n p q ↦ by
    rcases eq_or_ne p q with rfl | hpq
    · rw [if_pos rfl, if_pos rfl, mul_one, mul_one, hdet]
    · rw [if_neg fun hc ↦ hpq (Subtype.ext hc), if_neg hpq, mul_zero, mul_zero,
        Polynomial.coeff_zero]
  suffices h : ∀ (n : ℕ) (p q : S),
      matrixCoeff (resolventCoeff u n) p q = (B.adjugate p q).coeff n from h m j i
  intro n
  induction n with
  | zero =>
    intro p q
    have h := hcramer 0 p q
    simp only [hBmul0, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
    rw [resolventCoeff_zero, matrixCoeff_one, h, ← hdiag 0 p q, charCoeff_zero, one_mul]
  | succ n ih =>
    intro p q
    have h := hcramer (n + 1) p q
    simp only [hBmul, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      sub_eq_iff_eq_add] at h
    rw [resolventCoeff_succ, matrixCoeff_add, matrixCoeff_smul, matrixCoeff_one,
      matrixCoeff_mul_resolventCoeff_of_rows u S hS]
    simp only [ih, h]
    congr 1
    exact hdiag (n + 1) p q

private theorem norm_det_le_of_row_bounds' {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (f : n → ℝ) (hf : ∀ j i, ‖M j i‖ ≤ f j) : ‖M.det‖ ≤ ∏ j, f j := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty Finset.univ_nonempty fun σ _ ↦ ?_
  rw [norm_units_zsmul, ← Equiv.prod_comp σ f]
  exact (Finset.norm_prod_le _ _).trans <|
    Finset.prod_le_prod (fun i _ ↦ norm_nonneg _) fun i _ ↦ hf (σ i) i

-- Restated because the `Fredholm.lean` original is `private`.
private theorem norm_neg_one_pow' (m : ℕ) : ‖(-1 : R) ^ m‖ = 1 := by
  obtain h | h := neg_one_pow_eq_or R m <;> simp [h]

private theorem det_piecewise_neg_X_smul_map_C {S : Type*} [CommRing S] {n : Type*} [Fintype n]
    [DecidableEq n] (A Y : Matrix n n S) (s : Finset n) :
    Matrix.detRowAlternating (s.piecewise
        (-((Polynomial.X : Polynomial S) • A.map (Polynomial.C : S →+* Polynomial S)))
        (Y.map (Polynomial.C : S →+* Polynomial S))) = (-(Polynomial.X : Polynomial S)) ^ s.card *
      Polynomial.C (Matrix.of (s.piecewise A Y)).det := by
  have hdiag : s.piecewise
      (-((Polynomial.X : Polynomial S) • A.map (Polynomial.C : S →+* Polynomial S)))
      (Y.map (Polynomial.C : S →+* Polynomial S)) =
      Matrix.diagonal (fun p ↦ if p ∈ s then -(Polynomial.X : Polynomial S) else 1) *
        (Matrix.of (s.piecewise A Y)).map (Polynomial.C : S →+* Polynomial S) := by
    refine Matrix.ext fun p q ↦ ?_
    rw [Matrix.diagonal_mul, Matrix.map_apply, Matrix.of_apply]
    by_cases hp : p ∈ s
    · simp only [Finset.piecewise, if_pos hp]
      rw [Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, neg_mul]
    · simp only [Finset.piecewise, if_neg hp]
      rw [Matrix.map_apply, one_mul]
  have hmapdet : ((Matrix.of (s.piecewise A Y)).map (Polynomial.C : S →+* Polynomial S)).det =
      Polynomial.C (Matrix.of (s.piecewise A Y)).det :=
    (RingHom.map_det (Polynomial.C : S →+* Polynomial S) _).symm
  show Matrix.det _ = _
  rw [hdiag, Matrix.det_mul, Matrix.det_diagonal, hmapdet, Finset.prod_ite_mem,
    Finset.univ_inter, Finset.prod_const]

private theorem coeff_det_map_C_sub_X_smul {S : Type*} [CommRing S] {n : Type*} [Fintype n]
    [DecidableEq n] (A Y : Matrix n n S) (m : ℕ) :
    (Y.map (Polynomial.C : S →+* Polynomial S) -
        (Polynomial.X : Polynomial S) • A.map (Polynomial.C : S →+* Polynomial S)).det.coeff m =
      ∑ s : Finset n,
        if m = s.card then (-1 : S) ^ s.card * (Matrix.of (s.piecewise A Y)).det else 0 := by
  have hkey : (Y.map (Polynomial.C : S →+* Polynomial S) -
      (Polynomial.X : Polynomial S) • A.map (Polynomial.C : S →+* Polynomial S)).det =
      ∑ s : Finset n, Matrix.detRowAlternating (s.piecewise
        (-((Polynomial.X : Polynomial S) • A.map (Polynomial.C : S →+* Polynomial S)))
        (Y.map (Polynomial.C : S →+* Polynomial S))) := by
    rw [show Y.map (Polynomial.C : S →+* Polynomial S) -
        (Polynomial.X : Polynomial S) • A.map (Polynomial.C : S →+* Polynomial S) =
        -((Polynomial.X : Polynomial S) • A.map (Polynomial.C : S →+* Polynomial S)) +
          Y.map (Polynomial.C : S →+* Polynomial S) by abel]
    exact (Matrix.detRowAlternating (R := Polynomial S) (n := n)).map_add_univ _ _
  rw [hkey, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have hCX : (-(Polynomial.X : Polynomial S)) ^ s.card *
      Polynomial.C (Matrix.of (s.piecewise A Y)).det =
      Polynomial.C ((-1 : S) ^ s.card * (Matrix.of (s.piecewise A Y)).det) *
        (Polynomial.X : Polynomial S) ^ s.card := by
    rw [neg_pow, map_mul, map_pow, map_neg, map_one]
    ring
  rw [det_piecewise_neg_X_smul_map_C, hCX, Polynomial.coeff_C_mul_X_pow]

private theorem norm_coeff_det_le {n : Type*} [Fintype n] [DecidableEq n]
    (MC : Matrix n n (Polynomial R)) (A Y : Matrix n n R) (f : n → ℝ)
    (hMC : ∀ p q, MC p q = Polynomial.C (Y p q) - Polynomial.X * Polynomial.C (A p q))
    (hA : ∀ p q, ‖A p q‖ ≤ f p) (hY : ∀ p q, ‖Y p q‖ ≤ 1) (m : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hcT : ∀ T : Finset n, T.card = m → ∏ p ∈ T, f p ≤ c) :
    ‖(MC.det).coeff m‖ ≤ c := by
  have hMCeq : MC = Y.map (Polynomial.C : R →+* Polynomial R) -
      (Polynomial.X : Polynomial R) • A.map (Polynomial.C : R →+* Polynomial R) := by
    refine Matrix.ext fun p q ↦ ?_
    rw [hMC p q, Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.map_apply,
      smul_eq_mul]
  rw [hMCeq, coeff_det_map_C_sub_X_smul]
  refine le_trans ((Finset.univ_nonempty (α := Finset n)).norm_sum_le_sup'_norm _)
    (Finset.sup'_le _ _ fun s _ ↦ ?_)
  have hrow : ∀ p q, ‖Matrix.of (s.piecewise A Y) p q‖ ≤ if p ∈ s then f p else 1 := by
    intro p q
    rw [Matrix.of_apply]
    by_cases hp : p ∈ s
    · simpa only [Finset.piecewise, if_pos hp] using hA p q
    · simpa only [Finset.piecewise, if_neg hp] using hY p q
  by_cases hs : m = s.card
  · rw [if_pos hs]
    refine le_trans (norm_mul_le _ _) ?_
    rw [norm_neg_one_pow', one_mul]
    refine le_trans (norm_det_le_of_row_bounds' _ (fun p ↦ if p ∈ s then f p else 1) hrow) ?_
    rw [Finset.prod_ite_mem, Finset.univ_inter]
    exact hcT s hs.symm
  · rw [if_neg hs, norm_zero]
    exact hc

-- Duplicated from `Matrix.lean` and `Fredholm.lean`, where `norm_matrixCoeff_le_rowNorm`
-- is `private`.
private theorem norm_matrixCoeff_le_rowNorm' [IsTate R] (u : c(I, R) →L[R] c(I, R)) (j i : I) :
    ‖matrixCoeff u j i‖ ≤ rowNorm u j := le_ciSup (bddAbove_range_norm_matrixCoeff u j) i

private theorem norm_matrixCoeff_resolventCoeff_le_of_rows [IsTate R] (w : c(I, R) →L[R] c(I, R))
    (S : Finset I) (hS : ∀ j ∉ S, ∀ i, matrixCoeff w j i = 0) (m : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hcT : ∀ T : Finset I, T.card = m → ∏ j ∈ T, rowNorm w j ≤ c) (j i : I) :
    ‖matrixCoeff (resolventCoeff w m) j i‖ ≤ c := by
  set S' : Finset I := insert j (insert i S)
  have hjS' : j ∈ S' := Finset.mem_insert_self _ _
  have hiS' : i ∈ S' := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hSS' : ∀ p ∉ S', ∀ q, matrixCoeff w p q = 0 := fun p hp q ↦
    hS p (fun hpS ↦ hp (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hpS))) q
  rw [matrixCoeff_resolventCoeff_of_rows w S' hSS' m ⟨j, hjS'⟩ ⟨i, hiS'⟩, Matrix.adjugate_apply]
  refine norm_coeff_det_le _
    (Matrix.of fun p q : S' ↦ if p = ⟨i, hiS'⟩ then 0 else matrixCoeff w p q)
    (Matrix.of fun p q : S' ↦ if p = ⟨i, hiS'⟩ then (if q = ⟨j, hjS'⟩ then (1 : R) else 0)
      else (if p = q then (1 : R) else 0))
    (fun p ↦ rowNorm w p) (fun p q ↦ ?_) (fun p q ↦ ?_) (fun p q ↦ ?_) m hc fun T hT ↦ ?_
  · simp only [Matrix.updateRow_apply, Matrix.of_apply, Pi.single_apply, Matrix.sub_apply,
      Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  · rw [Matrix.of_apply]
    split_ifs
    · simpa using rowNorm_nonneg w p
    · exact norm_matrixCoeff_le_rowNorm' w p q
  · rw [Matrix.of_apply]
    split_ifs <;> simp
  · rw [← Finset.prod_image Subtype.coe_injective.injOn]
    exact hcT _ <| by rw [Finset.card_image_of_injective T Subtype.coe_injective, hT]

-- Serre's Lemme 3 for a row-supported operator.
private theorem norm_resolventCoeff_le_of_rows [IsTate R] (w : c(I, R) →L[R] c(I, R)) (S : Finset I)
    (hS : ∀ j ∉ S, ∀ i, matrixCoeff w j i = 0) (m : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hcT : ∀ T : Finset I, T.card = m → ∏ j ∈ T, rowNorm w j ≤ c) :
    ‖resolventCoeff w m‖ ≤ c :=
  (norm_eq_iSup_matrixCoeff _).trans_le <| Real.iSup_le
    (fun j ↦ Real.iSup_le (norm_matrixCoeff_resolventCoeff_le_of_rows w S hS m hc hcT j) hc) hc

-- Duplicated from `Fredholm.lean`, where `rowNorm_le_opNorm` is `private`.
private theorem rowNorm_le_opNorm' [IsTate R] (u : c(I, R) →L[R] c(I, R)) (j : I) :
    rowNorm u j ≤ ‖u‖ :=
  Real.iSup_le (norm_matrixCoeff_le' u j) (opNorm_nonneg u)

private theorem rowNorm_truncation_comp_le [IsTate R] (u : c(I, R) →L[R] c(I, R)) (S : Finset I)
    (j : I) : rowNorm ((truncation S).comp u) j ≤ rowNorm u j := by
  refine Real.iSup_le (fun i ↦ ?_) (rowNorm_nonneg u j)
  change ‖(if j ∈ S then matrixCoeff u j i else 0)‖ ≤ rowNorm u j
  split_ifs
  · exact norm_matrixCoeff_le_rowNorm' u j i
  · simpa using rowNorm_nonneg u j

private theorem tendsto_norm_pow_sub_pow [IsTate R] {α : Type*} {F : Filter α}
    (u : c(I, R) →L[R] c(I, R)) (v : α → c(I, R) →L[R] c(I, R)) {D : ℝ} (hD : ∀ x, ‖v x‖ ≤ D)
    (h : Tendsto (fun x ↦ ‖v x - u‖) F (𝓝 0)) (n : ℕ) :
    Tendsto (fun x ↦ ‖v x ^ n - u ^ n‖) F (𝓝 0) := by
  induction n with
  | zero => simpa using tendsto_const_nhds
  | succ n ih =>
  have hg : Tendsto (fun x ↦ D ^ n * ‖v x - u‖ + ‖v x ^ n - u ^ n‖ * ‖u‖) F (𝓝 0) := by
    simpa using (h.const_mul (D ^ n)).add (ih.mul_const ‖u‖)
  refine squeeze_zero (fun x ↦ opNorm_nonneg _) (fun x ↦ ?_) hg
  have h1 : ‖v x ^ n * (v x - u)‖ ≤ D ^ n * ‖v x - u‖ :=
    (opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ((opNorm_pow_le (v x) n).trans
      (pow_le_pow_left₀ (opNorm_nonneg (v x)) (hD x) n)) (opNorm_nonneg (v x - u)))
  calc ‖v x ^ (n + 1) - u ^ (n + 1)‖ = ‖v x ^ n * (v x - u) + (v x ^ n - u ^ n) * u‖ := by
        rw [mul_sub, sub_mul, pow_succ, pow_succ, sub_add_sub_cancel]
  _ ≤ ‖v x ^ n * (v x - u)‖ + ‖(v x ^ n - u ^ n) * u‖ := norm_add_le _ _
  _ ≤ D ^ n * ‖v x - u‖ + ‖v x ^ n - u ^ n‖ * ‖u‖ := add_le_add h1 (opNorm_mul_le _ _)

private theorem opNorm_truncation_comp_le [IsTate R] (u : c(I, R) →L[R] c(I, R)) (S : Finset I) :
    ‖(truncation S).comp u‖ ≤ ‖u‖ :=
  opNorm_le_of_forall _ (opNorm_nonneg u) fun x ↦
    (norm_truncation_apply_le S (u x)).trans (le_opNorm u x)

private theorem tendsto_norm_smul_sub_smul [IsTate R] {α : Type*} {F : Filter α} {D : ℝ} (a₀ : R)
    (b₀ : c(I, R) →L[R] c(I, R)) (a : α → R) (b : α → c(I, R) →L[R] c(I, R)) (hD : ∀ x, ‖b x‖ ≤ D)
    (ha : Tendsto (fun x ↦ ‖a x - a₀‖) F (𝓝 0)) (hb : Tendsto (fun x ↦ ‖b x - b₀‖) F (𝓝 0)) :
    Tendsto (fun x ↦ ‖a x • b x - a₀ • b₀‖) F (𝓝 0) := by
  have hg : Tendsto (fun x ↦ ‖a x - a₀‖ * D + ‖a₀‖ * ‖b x - b₀‖) F (𝓝 0) := by
    simpa using (ha.mul_const D).add (hb.const_mul ‖a₀‖)
  refine squeeze_zero (fun x ↦ opNorm_nonneg _) (fun x ↦ ?_) hg
  calc ‖a x • b x - a₀ • b₀‖ = ‖(a x - a₀) • b x + a₀ • (b x - b₀)‖ := by
        rw [sub_smul, smul_sub]
        congr 1
        abel
  _ ≤ ‖(a x - a₀) • b x‖ + ‖a₀ • (b x - b₀)‖ := norm_add_le _ _
  _ ≤ ‖a x - a₀‖ * D + ‖a₀‖ * ‖b x - b₀‖ :=
      add_le_add ((opNorm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (hD x) (norm_nonneg _)))
        (opNorm_smul_le _ _)

/-- Truncation-limit step of Lemme 3 [Serre1962, §6 p. 79, step c)]: the resolvent
coefficients of the row-truncations converge to those of `u`. -/
theorem tendsto_resolventCoeff_truncation [IsTate R] (u : c(I, R) →L[R] c(I, R))
    (hu : IsCompactoid u) (m : ℕ) :
    Tendsto (fun S : Finset I ↦ ‖resolventCoeff ((truncation S).comp u) m - resolventCoeff u m‖)
      atTop (𝓝 0) := by
  have htr : Tendsto (fun S : Finset I ↦ ‖(truncation S).comp u - u‖) atTop (𝓝 0) :=
    tendsto_truncation_comp u hu
  have hpow : ∀ n : ℕ,
      Tendsto (fun S : Finset I ↦ ‖((truncation S).comp u) ^ n - u ^ n‖) atTop (𝓝 0) :=
    fun n ↦ tendsto_norm_pow_sub_pow u (fun S ↦ (truncation S).comp u)
      (opNorm_truncation_comp_le u) htr n
  have hc : ∀ k : ℕ, Tendsto
      (fun S : Finset I ↦ ‖charCoeff ((truncation S).comp u) k - charCoeff u k‖) atTop (𝓝 0) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hg : Tendsto (fun S : Finset I ↦ ‖u‖ ^ (k - 1) * ‖(truncation S).comp u - u‖)
          atTop (𝓝 0) := by simpa using htr.const_mul (‖u‖ ^ (k - 1))
      exact squeeze_zero (fun S ↦ norm_nonneg _) (fun S ↦
        (norm_charCoeff_sub_le _ _ (hu.comp_left _) hu hk).trans
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_max_of_le_right (opNorm_nonneg u))
            (max_le (opNorm_truncation_comp_le u S) le_rfl) _) (opNorm_nonneg _))) hg
  have hterm : ∀ k : ℕ, Tendsto (fun S : Finset I ↦
      ‖charCoeff ((truncation S).comp u) k • ((truncation S).comp u) ^ (m - k)
        - charCoeff u k • u ^ (m - k)‖) atTop (𝓝 0) := fun k ↦
    tendsto_norm_smul_sub_smul (charCoeff u k) (u ^ (m - k))
      (fun S ↦ charCoeff ((truncation S).comp u) k) (fun S ↦ ((truncation S).comp u) ^ (m - k))
      (fun S ↦ (opNorm_pow_le _ _).trans
        (pow_le_pow_left₀ (opNorm_nonneg _) (opNorm_truncation_comp_le u S) _))
      (hc k) (hpow (m - k))
  have hgsum : Tendsto (fun S : Finset I ↦ ∑ k ∈ Finset.range (m + 1),
      ‖charCoeff ((truncation S).comp u) k • ((truncation S).comp u) ^ (m - k)
        - charCoeff u k • u ^ (m - k)‖) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.range (m + 1)) fun k _ ↦ hterm k
  refine squeeze_zero (fun S ↦ opNorm_nonneg _) (fun S ↦ ?_) hgsum
  rw [resolventCoeff, resolventCoeff, ← Finset.sum_sub_distrib]
  exact opNorm_sum_le _ _

/-- Serre's Lemme 3 [Serre1962, §6 p. 79]: `‖vₘ‖` is dominated by any bound on the products of
`m` pairwise-distinct row norms.  Serre states this with the sharpest such bound, the supremum
over `m`-element subsets; the hypothesis form used here lets a caller supply a cruder bound
without first having to prove that supremum exists (compare `norm_resolventCoeff_le_of_rows`,
the row-supported case that carries the induction). -/
theorem norm_resolventCoeff_le [IsTate R] (u : c(I, R) →L[R] c(I, R)) (hu : IsCompactoid u)
    (m : ℕ) {c : ℝ} (hc : 0 ≤ c) (hcT : ∀ T : Finset I, T.card = m → ∏ j ∈ T, rowNorm u j ≤ c) :
    ‖resolventCoeff u m‖ ≤ c := by
  -- The `.comp` spelling here is load-bearing, not a stylistic leftover: rewriting it to the
  -- `truncation S * u` form used further down the file makes this proof time out at whnf
  -- (200000 heartbeats), because unification against `norm_resolventCoeff_le_of_rows` then has
  -- to see through `*`.  A `rfl` bridge lemma for the `change` below does not avoid it.
  have hbound : ∀ S : Finset I, ‖resolventCoeff ((truncation S).comp u) m‖ ≤ c := fun S ↦ by
    refine norm_resolventCoeff_le_of_rows _ S (fun p hp q ↦ ?_) m hc (fun T hT ↦ ?_)
    · change (if p ∈ S then (u (cSpace.single q 1)) p else 0) = 0
      exact if_neg hp
    · exact (Finset.prod_le_prod (fun j _ ↦ rowNorm_nonneg _ j)
        (fun j _ ↦ rowNorm_truncation_comp_le u S j)).trans (hcT T hT)
  have htend : Tendsto (fun S : Finset I ↦
      ‖resolventCoeff ((truncation S).comp u) m - resolventCoeff u m‖ + c) atTop (𝓝 (0 + c)) :=
    (tendsto_resolventCoeff_truncation u hu m).add tendsto_const_nhds
  rw [zero_add] at htend
  refine ge_of_tendsto' htend fun S ↦ ?_
  refine le_trans ?_ (add_le_add le_rfl (hbound S))
  rw [opNorm_sub_comm]
  simpa using norm_add_le (resolventCoeff u m - resolventCoeff ((truncation S).comp u) m)
    (resolventCoeff ((truncation S).comp u) m)

-- `Finset.prod_le_pow_card` needs `MulLeftMono`, which `ℝ` is not; this is the ordered-semiring
-- form, used twice by `prod_le_of_threshold`.
private theorem prod_le_pow_card_of_nonneg {n : Type*} {g : n → ℝ} {c : ℝ} (s : Finset n)
    (hg0 : ∀ j ∈ s, 0 ≤ g j) (hgc : ∀ j ∈ s, g j ≤ c) : ∏ j ∈ s, g j ≤ c ^ s.card :=
  (Finset.prod_le_prod hg0 hgc).trans_eq (Finset.prod_const c)

-- Threshold split (`δ / D / b`) for a product of nonnegative bounds over an arbitrary index type;
-- the abstract form of `prod_rowNorm_le`, for the `↥T`-indexed products of `norm_det_sub_det_le'`.
private theorem prod_le_of_threshold {n : Type*} {g : n → ℝ} (hg0 : ∀ j, 0 ≤ g j) {δ D : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hD1 : (1 : ℝ) ≤ D) (hgD : ∀ j, g j ≤ D) (P : n → Prop)
    [DecidablePred P] (hgδ : ∀ j, ¬ P j → g j ≤ δ) (s : Finset n) {b k : ℕ}
    (hb : (s.filter P).card ≤ b) (hk : k ≤ s.card) : ∏ j ∈ s, g j ≤ D ^ b * δ ^ (k - b) := by
  have hcs : k - b ≤ (s.filter (fun j ↦ ¬ P j)).card := by
    have := Finset.card_filter_add_card_filter_not (s := s) P
    omega
  rw [← Finset.prod_filter_mul_prod_filter_not s P]
  refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun j _ ↦ hg0 j)
    (pow_nonneg (zero_le_one.trans hD1) _)
  · exact (prod_le_pow_card_of_nonneg _ (fun j _ ↦ hg0 j) fun j _ ↦ hgD j).trans
      (pow_le_pow_right₀ hD1 hb)
  · exact (prod_le_pow_card_of_nonneg _ (fun j _ ↦ hg0 j)
      fun j hj ↦ hgδ j (Finset.mem_filter.1 hj).2).trans (pow_le_pow_of_le_one hδ0.le hδ1 hcs)

-- Product analogue of the `δ / D / b` threshold split behind `charPowerSeries_isEntire`.
private theorem prod_rowNorm_le [IsTate R] (u : c(I, R) →L[R] c(I, R)) {δ D : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) (hD1 : (1 : ℝ) ≤ D) (hDu : ‖u‖ ≤ D) (hbad : {j : I | δ ≤ rowNorm u j}.Finite)
    (n : ℕ) (T : Finset I) (hT : T.card = n) :
    ∏ j ∈ T, rowNorm u j ≤ D ^ hbad.toFinset.card * δ ^ (n - hbad.toFinset.card) := by
  classical
  exact prod_le_of_threshold (rowNorm_nonneg u) hδ0 hδ1 hD1
    (fun j ↦ (rowNorm_le_opNorm' u j).trans hDu) (fun j ↦ δ ≤ rowNorm u j)
    (fun j hj ↦ (not_le.1 hj).le) T
    (Finset.card_le_card fun j hj ↦ hbad.mem_toFinset.2 (Finset.mem_filter.1 hj).2) hT.ge

/-- Serre's Proposition 10 [Serre1962, §6 p. 78]: the Fredholm resolvent is entire —
`‖vₘ‖ Mᵐ → 0` for every radius `M`. -/
theorem tendsto_norm_resolventCoeff [IsTate R] (u : c(I, R) →L[R] c(I, R)) (hu : IsCompactoid u)
    (M : ℝ) :
    Tendsto (fun m ↦ ‖resolventCoeff u m‖ * M ^ m) atTop (𝓝 0) := by
  set C : ℝ := max |M| 1
  have hC : (0 : ℝ) < C := one_pos.trans_le (le_max_right _ _)
  set δ : ℝ := min (1 / (2 * C)) 1
  have hδ0 : 0 < δ := lt_min (by positivity) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδC : δ * C ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hC.le).trans_eq (by field_simp)
  set D : ℝ := max ‖u‖ 1
  have hD1 : (1 : ℝ) ≤ D := le_max_right _ _
  have hD0 : (0 : ℝ) < D := one_pos.trans_le hD1
  have hbad : {j : I | δ ≤ rowNorm u j}.Finite := by
    have hev : ∀ᶠ j in cofinite, rowNorm u j < δ := by
      filter_upwards [Metric.tendsto_nhds.1 hu δ hδ0] with j hj
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (rowNorm_nonneg u j)] at hj
    simpa only [not_lt] using Filter.eventually_cofinite.1 hev
  set b : ℕ := hbad.toFinset.card
  have hres : ∀ n : ℕ, ‖resolventCoeff u n‖ ≤ D ^ b * δ ^ (n - b) := fun n ↦
    norm_resolventCoeff_le u hu n (mul_nonneg (pow_nonneg hD0.le _) (pow_nonneg hδ0.le _))
      (prod_rowNorm_le u hδ0 hδ1 hD1 (le_max_left _ _) hbad n)
  have hgeom : Tendsto (fun n : ℕ ↦ (D / δ) ^ b * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul ((D / δ) ^ b)
  have hmain : Tendsto (fun n : ℕ ↦ ‖resolventCoeff u n‖ * C ^ n) atTop (𝓝 0) := by
    refine squeeze_zero' (.of_forall fun n ↦
      mul_nonneg (opNorm_nonneg _) (pow_nonneg hC.le n)) ?_ hgeom
    refine eventually_atTop.2 ⟨b, fun n hn ↦ ?_⟩
    have hrew : D ^ b * δ ^ (n - b) * C ^ n = (D / δ) ^ b * (δ * C) ^ n := by
      rw [pow_sub₀ δ hδ0.ne' hn]
      ring
    exact (mul_le_mul_of_nonneg_right (hres n) (pow_nonneg hC.le n)).trans (hrew.trans_le
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hδ0.le hC.le) hδC n)
        (pow_nonneg (div_nonneg hD0.le hδ0.le) b)))
  refine squeeze_zero_norm (fun n ↦ ?_) hmain
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (opNorm_nonneg _), abs_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg M) (le_max_left _ _) n)
    (opNorm_nonneg _)

-- Replaces summability in the Cauchy estimate below: the summands of the divided
-- evaluations are null but not summable.
private theorem opNorm_add_le_max' [IsTate R] (w w' : c(I, R) →L[R] c(I, R)) :
    ‖w + w'‖ ≤ max ‖w‖ ‖w'‖ :=
  opNorm_le_of_forall _ (le_max_of_le_left (opNorm_nonneg w)) fun x ↦
    (IsUltrametricDist.norm_add_le_max (w x) (w' x)).trans <|
      (max_le_max (le_opNorm w x) (le_opNorm w' x)).trans_eq
        (max_mul_of_nonneg _ _ (norm_nonneg x)).symm

-- Ultrametric refinement of `opNorm_sum_le`, which bounds only by the sum of the norms.
private theorem opNorm_sum_le_of_forall [IsTate R] {ι : Type*} {c : ℝ} (hc : 0 ≤ c)
    (f : ι → c(I, R) →L[R] c(I, R)) (t : Finset ι) (hf : ∀ i ∈ t, ‖f i‖ ≤ c) :
    ‖∑ i ∈ t, f i‖ ≤ c := by
  induction t using Finset.cons_induction with
  | empty => simpa using hc
  | cons i t hi ih =>
  rw [Finset.sum_cons]
  exact (opNorm_add_le_max' _ _).trans <| max_le (hf i (Finset.mem_cons_self ..))
    (ih fun k hk ↦ hf k (Finset.mem_cons_of_mem hk))

-- Scalar bound for the summands of the divided evaluations.
private theorem norm_natCast_mul_mul_pow_le (k : ℕ) (b a : R) (m : ℕ) :
    ‖(k : R) * b * a ^ m‖ ≤ ‖b‖ * ‖a‖ ^ m := by
  rw [mul_assoc, ← nsmul_eq_mul]
  exact (IsUltrametricDist.norm_nsmul_le _ k).trans <| norm_mul_le_of_le le_rfl (norm_pow_le a m)

-- Operator-side bound for the summands of the divided evaluations.
private theorem norm_natCast_smul_pow_smul_le [IsTate R] (k m : ℕ) (a : R)
    (w : c(I, R) →L[R] c(I, R)) : ‖(k : R) • a ^ m • w‖ ≤ ‖w‖ * ‖a‖ ^ m := by
  rw [smul_smul, mul_comm ‖w‖]
  refine (opNorm_smul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (opNorm_nonneg w))
  exact (norm_mul_le _ _).trans ((mul_le_mul (IsUltrametricDist.norm_natCast_le_one R k)
    (norm_pow_le a m) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

private theorem opNorm_smul_one_le [IsTate R] (b : R) : ‖b • (1 : c(I, R) →L[R] c(I, R))‖ ≤ ‖b‖ :=
  (opNorm_smul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg b) opNorm_one_le)

private theorem isOpLimit_shift {T : ℕ → c(I, R) →L[R] c(I, R)} {L : c(I, R) →L[R] c(I, R)}
    (h : IsOpLimit T L) (k : ℕ) : IsOpLimit (fun n ↦ T (n + k)) L :=
  h.comp (tendsto_add_atTop_nat k)

private theorem isOpLimit_congr {T T' : ℕ → c(I, R) →L[R] c(I, R)} {L : c(I, R) →L[R] c(I, R)}
    (h : IsOpLimit T L) (hTT' : ∀ n, T n = T' n) : IsOpLimit T' L :=
  funext hTT' ▸ h

private theorem isOpLimit_zero_of_le {T : ℕ → c(I, R) →L[R] c(I, R)} {g : ℕ → ℝ}
    (hg : Tendsto g atTop (𝓝 0)) (h : ∀ n, ‖T n‖ ≤ g n) : IsOpLimit T 0 :=
  squeeze_zero (fun n ↦ opNorm_nonneg _) (fun n ↦ by simpa using h n) hg

private theorem isOpLimit_smul_one [IsTate R] {S : ℕ → R} {L : R} (h : Tendsto S atTop (𝓝 L)) :
    IsOpLimit (fun n ↦ S n • (1 : c(I, R) →L[R] c(I, R))) (L • 1) := by
  refine squeeze_zero (fun n ↦ opNorm_nonneg _) (fun n ↦ ?_)
    (by simpa using (h.sub_const L).norm)
  rw [← sub_smul]
  exact opNorm_smul_one_le _

/-- The partial sums of the `s`-th divided evaluation `Nₛ = (Δˢ P)(a, u)` of the resolvent. -/
def resolventPartialSum (u : c(I, R) →L[R] c(I, R)) (a : R) (s n : ℕ) : c(I, R) →L[R] c(I, R) :=
  ∑ m ∈ Finset.range n, ((m + s).choose s : R) • a ^ m • resolventCoeff u (m + s)

private theorem resolventPartialSum_succ (u : c(I, R) →L[R] c(I, R)) (a : R) (s n : ℕ) :
    resolventPartialSum u a s (n + 1) = resolventPartialSum u a s n +
      ((n + s).choose s : R) • a ^ n • resolventCoeff u (n + s) :=
  Finset.sum_range_succ _ n

private theorem resolventPartialSum_one (u : c(I, R) →L[R] c(I, R)) (a : R) (s : ℕ) :
    resolventPartialSum u a s 1 = resolventCoeff u s := by
  simp [resolventPartialSum]

private theorem mul_resolventCoeff (u : c(I, R) →L[R] c(I, R)) (m : ℕ) :
    u * resolventCoeff u m = resolventCoeff u (m + 1) - charCoeff u (m + 1) • 1 :=
  eq_sub_of_add_eq' (resolventCoeff_succ u m).symm

/-- The divided evaluations `Nₛ` of the resolvent exist: the partial sums converge in
operator norm. -/
theorem exists_isOpLimit_resolventPartialSum [IsTate R] (u : c(I, R) →L[R] c(I, R))
    (hu : IsCompactoid u) (a : R) (s : ℕ) :
    ∃ N : c(I, R) →L[R] c(I, R), IsOpLimit (resolventPartialSum u a s) N := by
  have hterm : Tendsto (fun m ↦ ‖((m + s).choose s : R) • a ^ m • resolventCoeff u (m + s)‖)
      atTop (𝓝 0) := by
    have hbase : Tendsto (fun m ↦ ‖resolventCoeff u (m + s)‖ * max ‖a‖ 1 ^ (m + s)) atTop (𝓝 0) :=
      (tendsto_norm_resolventCoeff u hu _).comp (tendsto_add_atTop_nat s)
    refine squeeze_zero (fun m ↦ opNorm_nonneg _) (fun m ↦ ?_) hbase
    refine (norm_natCast_smul_pow_smul_le _ _ _ _).trans
      (mul_le_mul_of_nonneg_left ?_ (opNorm_nonneg _))
    exact (pow_le_pow_left₀ (norm_nonneg a) (le_max_left _ _) m).trans
      (pow_le_pow_right₀ (le_max_right _ _) (Nat.le_add_right m s))
  refine exists_lim_of_cauchySeq _ fun ε hε ↦ ?_
  obtain ⟨M₀, hM₀⟩ := (hterm.eventually_lt_const (half_pos hε)).exists_forall_of_atTop
  have key : ∀ p q, M₀ ≤ p → p ≤ q →
      ‖resolventPartialSum u a s q - resolventPartialSum u a s p‖ < ε := by
    intro p q hp hpq
    simp only [resolventPartialSum]
    rw [← Finset.sum_Ico_eq_sub _ hpq]
    exact (opNorm_sum_le_of_forall (half_pos hε).le _ _ fun m hm ↦
      (hM₀ m (hp.trans (Finset.mem_Ico.mp hm).1)).le).trans_lt (half_lt_self hε)
  exact ⟨M₀, fun p q hp hq ↦ (le_total p q).elim
    (fun h ↦ (opNorm_sub_comm _ _).trans_lt (key p q hp h)) (key q p hq)⟩

/-- The divided evaluations `Nₛ` of the resolvent commute with `u`. -/
theorem commute_of_isOpLimit_resolventPartialSum [IsTate R] {u : c(I, R) →L[R] c(I, R)} {a : R}
    {s : ℕ} {N : c(I, R) →L[R] c(I, R)} (hN : IsOpLimit (resolventPartialSum u a s) N) :
    u * N = N * u :=
  (hN.comp_left u).unique <| isOpLimit_congr (hN.comp_right u) fun _ ↦
    (Commute.sum_right _ _ _ fun _ _ ↦ ((Commute.sum_right _ _ _ fun _ _ ↦
      (Commute.self_pow u _).smul_right _).smul_right _).smul_right _).symm.eq

-- The polynomial `∑_{k ≤ m} cₖ Xᵐ⁻ᵏ` evaluating to `resolventCoeff u m`.
private def resolventPoly (u : c(I, R) →L[R] c(I, R)) (m : ℕ) : Polynomial R :=
  ∑ k ∈ Finset.range (m + 1), Polynomial.C (charCoeff u k) * Polynomial.X ^ (m - k)

private theorem aeval_resolventPoly (u : c(I, R) →L[R] c(I, R)) (m : ℕ) :
    Polynomial.aeval u (resolventPoly u m) = resolventCoeff u m := by
  simp only [resolventPoly, resolventCoeff, map_sum, map_mul, Polynomial.aeval_C, map_pow,
    Polynomial.aeval_X, Algebra.smul_def]

private def resolventPartialPoly (u : c(I, R) →L[R] c(I, R)) (a : R) (s n : ℕ) : Polynomial R :=
  ∑ m ∈ Finset.range n, Polynomial.C (((m + s).choose s : R) * a ^ m) * resolventPoly u (m + s)

private theorem aeval_resolventPartialPoly (u : c(I, R) →L[R] c(I, R)) (a : R) (s n : ℕ) :
    Polynomial.aeval u (resolventPartialPoly u a s n) = resolventPartialSum u a s n := by
  simp only [resolventPartialPoly, resolventPartialSum, map_sum, map_mul, Polynomial.aeval_C,
    aeval_resolventPoly, Algebra.smul_def, mul_assoc]

/-- `L` lies in the closure of `R[u]`: it is an operator-norm limit of polynomials in `u`
([JN] Theorem 2.2.2: "the idempotent projectors … lie in the closure of `R[u]`"). -/
def IsOpLimitAeval (u L : c(I, R) →L[R] c(I, R)) : Prop :=
  ∃ pol : ℕ → Polynomial R, IsOpLimit (fun k ↦ Polynomial.aeval u (pol k)) L

omit [DecidableEq I] in
/-- Polynomials in `u` lie in the closure of `R[u]`. -/
theorem IsOpLimitAeval.aeval (u : c(I, R) →L[R] c(I, R)) (P : Polynomial R) :
    IsOpLimitAeval u (Polynomial.aeval u P) :=
  ⟨fun _ ↦ P, IsOpLimit.const _⟩

omit [DecidableEq I] in
/-- The closure of `R[u]` is closed under addition. -/
theorem IsOpLimitAeval.add [IsTate R] {u L L' : c(I, R) →L[R] c(I, R)} (h : IsOpLimitAeval u L)
    (h' : IsOpLimitAeval u L') : IsOpLimitAeval u (L + L') :=
  let ⟨p, hp⟩ := h
  let ⟨q, hq⟩ := h'
  ⟨fun k ↦ p k + q k, by simpa only [map_add] using hp.add hq⟩

omit [DecidableEq I] in
/-- The closure of `R[u]` is closed under multiplication. -/
theorem IsOpLimitAeval.mul [IsTate R] {u L L' : c(I, R) →L[R] c(I, R)} (h : IsOpLimitAeval u L)
    (h' : IsOpLimitAeval u L') : IsOpLimitAeval u (L * L') :=
  let ⟨p, hp⟩ := h
  let ⟨q, hq⟩ := h'
  ⟨fun k ↦ p k * q k, by simpa only [map_mul] using hp.mul hq⟩

omit [DecidableEq I] in
/-- The closure of `R[u]` is closed under scalar multiplication. -/
theorem IsOpLimitAeval.smul [IsTate R] {u L : c(I, R) →L[R] c(I, R)} (h : IsOpLimitAeval u L)
    (c : R) : IsOpLimitAeval u (c • L) :=
  let ⟨p, hp⟩ := h
  ⟨fun k ↦ Polynomial.C c * p k, by
    simpa only [map_mul, Polynomial.aeval_C, Algebra.smul_def] using hp.smul c⟩

omit [DecidableEq I] in
/-- The closure of `R[u]` is closed under powers. -/
theorem IsOpLimitAeval.pow [IsTate R] {u L : c(I, R) →L[R] c(I, R)} (h : IsOpLimitAeval u L)
    (m : ℕ) : IsOpLimitAeval u (L ^ m) :=
  let ⟨p, hp⟩ := h
  ⟨fun k ↦ p k ^ m, by simpa only [map_pow] using hp.pow m⟩

omit [DecidableEq I] in
/-- A limit of polynomials in a polynomial in `u` is a limit of polynomials in `u`. -/
theorem IsOpLimitAeval.comp {u L : c(I, R) →L[R] c(I, R)} {B : Polynomial R}
    (h : IsOpLimitAeval (Polynomial.aeval u B) L) : IsOpLimitAeval u L :=
  let ⟨p, hp⟩ := h
  ⟨fun k ↦ (p k).comp B, by simpa only [Polynomial.aeval_comp] using hp⟩

/-- The divided evaluations `Nₛ` of the resolvent lie in the closure of `R[u]`. -/
theorem IsOpLimitAeval.of_resolventPartialSum {u N : c(I, R) →L[R] c(I, R)} {a : R} {s : ℕ}
    (hN : IsOpLimit (resolventPartialSum u a s) N) : IsOpLimitAeval u N :=
  ⟨resolventPartialPoly u a s,
    isOpLimit_congr hN fun n ↦ (aeval_resolventPartialPoly u a s n).symm⟩

/-- An operator-norm limit of polynomials in `u` commutes with every operator commuting with
`u` ([Bel] II.2.17/II.2.18: "`N` and `F` are stable by every operator … that commutes with
`φ`"). -/
theorem commute_of_isOpLimit_aeval [IsTate R] {u p : c(I, R) →L[R] c(I, R)}
    {pol : ℕ → Polynomial R} (hp : IsOpLimit (fun k ↦ Polynomial.aeval u (pol k)) p)
    {w : c(I, R) →L[R] c(I, R)} (hw : u * w = w * u) : p * w = w * p :=
  (hp.comp_right w).unique <| isOpLimit_congr (hp.comp_left w) fun k ↦ by
    rw [Polynomial.aeval_eq_sum_range]
    exact (Commute.sum_right _ _ _ fun i _ ↦
      ((show Commute w u from hw.symm).pow_right i).smul_right _).eq

/-- Elements of the closure of `R[u]` commute with every operator commuting with `u`. -/
theorem IsOpLimitAeval.commute [IsTate R] {u p : c(I, R) →L[R] c(I, R)} (h : IsOpLimitAeval u p)
    {w : c(I, R) →L[R] c(I, R)} (hw : u * w = w * u) : p * w = w * p :=
  let ⟨_, hp⟩ := h
  commute_of_isOpLimit_aeval hp hw

private theorem resolventPartialSum_zero_succ (u : c(I, R) →L[R] c(I, R)) (a : R) (n : ℕ) :
    resolventPartialSum u a 0 (n + 1) = resolventPartialSum u a 0 n +
      a ^ n • resolventCoeff u n := by
  simp [resolventPartialSum_succ]

-- Finite (unevaluated) form of `(1 - tu)·P(t, u) = H(t)` at `t = a`, up to the boundary
-- term `aⁿ·vₙ`.
private theorem one_sub_smul_mul_resolventPartialSum_zero (u : c(I, R) →L[R] c(I, R)) (a : R)
    (n : ℕ) : (1 - a • u) * resolventPartialSum u a 0 n
      = (∑ j ∈ Finset.range (n + 1), charCoeff u j * a ^ j) • 1 - a ^ n • resolventCoeff u n := by
  induction n with
  | zero => simp [resolventPartialSum]
  | succ n ih =>
  rw [resolventPartialSum_zero_succ, mul_add, ih]
  simp only [Finset.sum_range_succ, sub_mul, one_mul, smul_mul_assoc, mul_smul_comm,
    mul_resolventCoeff]
  module

private theorem one_sub_smul_mul_resolventPartialSum_succ (u : c(I, R) →L[R] c(I, R)) (a : R)
    (t n : ℕ) : (1 - a • u) * resolventPartialSum u a (t + 1) (n + 1)
      = u * resolventPartialSum u a t (n + 1)
        + (∑ m ∈ Finset.range (n + 1),
            ((m + t + 1).choose (t + 1) : R) * charCoeff u (m + t + 1) * a ^ m) • 1
        + (((n + t + 1).choose (t + 1) : R) * charCoeff u (n + t + 2) * a ^ (n + 1)) • 1
        - ((n + t + 1).choose (t + 1) : R) • a ^ (n + 1) • resolventCoeff u (n + t + 2) := by
  induction n with
  | zero =>
    simp only [Nat.zero_add, Finset.sum_range_one, resolventPartialSum_one, Nat.choose_self,
      Nat.cast_one, pow_zero, pow_one, one_mul, mul_one, one_smul, sub_mul, smul_mul_assoc,
      mul_resolventCoeff]
    module
  | succ n ih =>
    have hP1 : resolventPartialSum u a (t + 1) (n + 1 + 1)
        = resolventPartialSum u a (t + 1) (n + 1)
          + ((n + t + 2).choose (t + 1) : R) • a ^ (n + 1) • resolventCoeff u (n + t + 2) := by
      rw [resolventPartialSum_succ, show n + 1 + (t + 1) = n + t + 2 by omega]
    have hP2 : resolventPartialSum u a t (n + 1 + 1)
        = resolventPartialSum u a t (n + 1)
          + ((n + t + 1).choose t : R) • a ^ (n + 1) • resolventCoeff u (n + t + 1) := by
      rw [resolventPartialSum_succ, show n + 1 + t = n + t + 1 by omega]
    have hpascal : ((n + t + 2).choose (t + 1) : R)
        = ((n + t + 1).choose t : R) + ((n + t + 1).choose (t + 1) : R) := by
      rw [show n + t + 2 = n + t + 1 + 1 from rfl, Nat.choose_succ_succ' (n + t + 1) t,
        Nat.cast_add]
    rw [hP1, hP2, Finset.sum_range_succ, mul_add, mul_add, ih,
      show n + 1 + t + 1 = n + t + 2 by omega, show n + 1 + t + 2 = n + t + 3 by omega, hpascal]
    simp only [sub_mul, one_mul, smul_mul_assoc, mul_smul_comm, mul_resolventCoeff]
    module

/-- Serre's evaluated identity at `s = 0`: `(1 - a•u) N₀ = H(a)·1` [Serre1962, §7
p. 80, from `(1-tu)P(t,u) = H(t)` at `t = a`]. -/
theorem one_sub_smul_mul_resolventEval_zero [IsTate R] {u : c(I, R) →L[R] c(I, R)}
    (hu : IsCompactoid u) {a : R} {N : c(I, R) →L[R] c(I, R)}
    (hN : IsOpLimit (resolventPartialSum u a 0) N) :
    (1 - a • u) * N = PowerSeries.evalT a (charPowerSeries u) • 1 := by
  have hC0 : (0 : ℝ) < max ‖a‖ 1 := one_pos.trans_le (le_max_right _ _)
  have hsum : Summable fun m ↦ PowerSeries.coeff m (charPowerSeries u) * a ^ m :=
    PowerSeries.summable_coeff_mul_pow (PowerSeries.tendsto_norm_coeff_mul_pow_of_isRestricted
      (charPowerSeries_isEntire u hu _ hC0) (le_max_left ‖a‖ 1))
  have hSc : Tendsto (fun n ↦ ∑ j ∈ Finset.range (n + 1), charCoeff u j * a ^ j) atTop
      (𝓝 (PowerSeries.evalT a (charPowerSeries u))) := by
    simp only [← charPowerSeries_coeff]
    exact hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hR3 : IsOpLimit (fun n ↦ -(a ^ n • resolventCoeff u n)) 0 := by
    refine isOpLimit_zero_of_le (tendsto_norm_resolventCoeff u hu (max ‖a‖ 1)) fun n ↦ ?_
    rw [opNorm_neg, mul_comm ‖resolventCoeff u n‖]
    exact (opNorm_smul_le _ _).trans (mul_le_mul_of_nonneg_right ((norm_pow_le a n).trans
      (pow_le_pow_left₀ (norm_nonneg a) (le_max_left _ _) n)) (opNorm_nonneg _))
  have hcomb := (isOpLimit_smul_one (I := I) hSc).add hR3
  rw [add_zero] at hcomb
  refine (hN.comp_left (1 - a • u)).unique (isOpLimit_congr hcomb fun n ↦ ?_)
  rw [one_sub_smul_mul_resolventPartialSum_zero]
  abel

private theorem tendsto_sum_range_choose_mul_charCoeff_mul_pow [IsTate R]
    {u : c(I, R) →L[R] c(I, R)} (hu : IsCompactoid u) (a : R) (t : ℕ) :
    Tendsto (fun n ↦ ∑ m ∈ Finset.range (n + 1),
        ((m + t + 1).choose (t + 1) : R) * charCoeff u (m + t + 1) * a ^ m)
      atTop (𝓝 (PowerSeries.evalT a (PowerSeries.hasseDeriv (t + 1) (charPowerSeries u)))) := by
  have hC0 : (0 : ℝ) < max ‖a‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsum : Summable fun m ↦ PowerSeries.coeff m
      (PowerSeries.hasseDeriv (t + 1) (charPowerSeries u)) * a ^ m :=
    PowerSeries.summable_coeff_mul_pow (PowerSeries.tendsto_norm_coeff_mul_pow_of_isRestricted
      (PowerSeries.isRestricted_hasseDeriv hC0 (charPowerSeries_isEntire u hu (max ‖a‖ 1) hC0)
        (t + 1)) (le_max_left ‖a‖ 1))
  have hco : ∀ m : ℕ, ((m + t + 1).choose (t + 1) : R) * charCoeff u (m + t + 1) * a ^ m =
      PowerSeries.coeff m (PowerSeries.hasseDeriv (t + 1) (charPowerSeries u)) * a ^ m :=
    fun m ↦ by rw [PowerSeries.coeff_hasseDeriv, charPowerSeries_coeff]; rfl
  simp only [hco]
  exact hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

/-- Serre's evaluated identities: `(1 - a•u) Nₛ = u N_{s-1} + (ΔˢH)(a)·1` [Serre1962,
§7 pp. 80–81: "En lui appliquant l'opérateur Δˢ"]. -/
theorem one_sub_smul_mul_resolventEval [IsTate R] {u : c(I, R) →L[R] c(I, R)} (hu : IsCompactoid u)
    {a : R} {s : ℕ} (hs : 1 ≤ s) {N N' : c(I, R) →L[R] c(I, R)}
    (hN : IsOpLimit (resolventPartialSum u a s) N)
    (hN' : IsOpLimit (resolventPartialSum u a (s - 1)) N') :
    (1 - a • u) * N = u * N' +
      PowerSeries.evalT a (PowerSeries.hasseDeriv s (charPowerSeries u)) • 1 := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hN'
  set C : ℝ := max ‖a‖ 1
  have hC1 : (1 : ℝ) ≤ C := le_max_right _ _
  have haC : ‖a‖ ≤ C := le_max_left _ _
  have hcC : Tendsto (fun n ↦ ‖charCoeff u (n + t + 2)‖ * C ^ (n + t + 2)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun m ↦ ‖charCoeff u m‖ * C ^ m) atTop (𝓝 0) := by
      simpa using (PowerSeries.isRestricted_iff' C (charPowerSeries u)).mp
        (charPowerSeries_isEntire u hu C (lt_of_lt_of_le one_pos hC1))
    exact h0.comp (tendsto_add_atTop_nat (t + 2))
  have hvC : Tendsto (fun n ↦ ‖resolventCoeff u (n + t + 2)‖ * C ^ (n + t + 2)) atTop (𝓝 0) :=
    (tendsto_norm_resolventCoeff u hu C).comp (tendsto_add_atTop_nat (t + 2))
  have hpow : ∀ n : ℕ, ‖a‖ ^ (n + 1) ≤ C ^ (n + t + 2) :=
    fun n ↦ (pow_le_pow_left₀ (norm_nonneg a) haC (n + 1)).trans
      (pow_le_pow_right₀ hC1 (by omega))
  have hR3 : IsOpLimit (fun n ↦ (((n + t + 1).choose (t + 1) : R) *
      charCoeff u (n + t + 2) * a ^ (n + 1)) • (1 : c(I, R) →L[R] c(I, R))) 0 := by
    refine isOpLimit_zero_of_le hcC fun n ↦ ?_
    exact ((opNorm_smul_one_le _).trans (norm_natCast_mul_mul_pow_le _ _ _ _)).trans
      (mul_le_mul_of_nonneg_left (hpow n) (norm_nonneg _))
  have hR4 : IsOpLimit (fun n ↦ -(((n + t + 1).choose (t + 1) : R) • a ^ (n + 1) •
      resolventCoeff u (n + t + 2))) 0 := by
    refine isOpLimit_zero_of_le hvC fun n ↦ ?_
    rw [opNorm_neg]
    exact (norm_natCast_smul_pow_smul_le _ _ _ _).trans
      (mul_le_mul_of_nonneg_left (hpow n) (opNorm_nonneg _))
  have hL : IsOpLimit (fun n ↦ (1 - a • u) * resolventPartialSum u a (t + 1) (n + 1))
      ((1 - a • u) * N) := isOpLimit_shift (hN.comp_left (1 - a • u)) 1
  have hR1 : IsOpLimit (fun n ↦ u * resolventPartialSum u a t (n + 1)) (u * N') :=
    isOpLimit_shift (hN'.comp_left u) 1
  have hcomb := ((hR1.add (isOpLimit_smul_one (I := I)
    (tendsto_sum_range_choose_mul_charCoeff_mul_pow hu a t))).add hR3).add hR4
  rw [add_zero, add_zero] at hcomb
  refine hL.unique (isOpLimit_congr hcomb fun n ↦ ?_)
  rw [one_sub_smul_mul_resolventPartialSum_succ]
  abel

end Resolvent

section DetValue

/-- The Fredholm determinant value `det(1 - u) := H_u(1)` of a compactoid operator
[Serre1962, §5 p. 76: "det(1+u) est défini pour tout u"]. -/
def fredholmDet (u : c(I, R) →L[R] c(I, R)) : R :=
  PowerSeries.evalT 1 (charPowerSeries u)

private theorem minor_smul (a : R) (u : c(I, R) →L[R] c(I, R)) (S : Finset I) :
    minor (a • u) S = a ^ S.card * minor u S := by
  have hmat : (Matrix.of fun j i : S ↦ matrixCoeff (a • u) j i)
      = a • Matrix.of fun j i : S ↦ matrixCoeff u j i := Matrix.ext fun _ _ ↦ rfl
  rw [minor, minor, hmat, Matrix.det_smul, Fintype.card_coe]

/-- Scaling of the characteristic coefficients: `cₙ(a•u) = aⁿ cₙ(u)` (the minors are
`n`-linear in the rows). -/
theorem charCoeff_smul [IsTate R] (a : R) (u : c(I, R) →L[R] c(I, R)) (hu : IsCompactoid u)
    (n : ℕ) : charCoeff (a • u) n = a ^ n * charCoeff u n := by
  have hminor (S : {S : Finset I // S.card = n}) :
      minor (a • u) (S : Finset I) = a ^ n * minor u (S : Finset I) := by
    rw [minor_smul, S.2]
  rw [charCoeff, charCoeff, tsum_congr hminor, (summable_minor u hu n).tsum_mul_left]
  ring

/-- **Scaling the operator rescales the determinant**: `det(1 - X·(a•u)) = det(1 - aX·u)`,
coefficientwise `charCoeff_smul`. -/
theorem charPowerSeries_smul [IsTate R] (a : R) (u : c(I, R) →L[R] c(I, R))
    (hu : IsCompactoid u) :
    charPowerSeries (a • u) = PowerSeries.rescale a (charPowerSeries u) := by
  refine PowerSeries.ext fun n => ?_
  rw [charPowerSeries_coeff, PowerSeries.coeff_rescale, charPowerSeries_coeff,
    charCoeff_smul a u hu n]

/-- `det(1 - a•u) = H_u(a)`: the determinant value of the rescaled operator is the
evaluation of the characteristic power series. -/
theorem fredholmDet_smul [IsTate R] (a : R) (u : c(I, R) →L[R] c(I, R)) (hu : IsCompactoid u) :
    fredholmDet (a • u) = PowerSeries.evalT a (charPowerSeries u) :=
  tsum_congr fun _ ↦ by simp [charCoeff_smul a u hu, mul_comm]

private theorem charCoeff_eq_zero_of_card_lt {u : c(I, R) →L[R] c(I, R)} {S : Finset I} {n : ℕ}
    (hS : ∀ j ∉ S, ∀ i, matrixCoeff u j i = 0) (hn : S.card < n) : charCoeff u n = 0 := by
  have hz : ∀ T : {T : Finset I // T.card = n}, minor u (T : Finset I) = 0 := fun T ↦ by
    obtain ⟨j, hjT, hjS⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show S.card < (T : Finset I).card by simpa [T.2] using hn)
    exact Matrix.det_eq_zero_of_row_eq_zero ⟨j, hjT⟩ fun i ↦ hS j hjS _
  simp [charCoeff, tsum_congr hz]

/-- The determinant value of a row-supported operator is the determinant of its finite
block. -/
theorem fredholmDet_eq_det_of_rows (u : c(I, R) →L[R] c(I, R)) (S : Finset I)
    (hS : ∀ j ∉ S, ∀ i, matrixCoeff u j i = 0) :
    fredholmDet u = Matrix.det (1 - Matrix.of fun j i : S ↦ matrixCoeff u j i) := by
  obtain ⟨p, hp⟩ : ∃ p : Polynomial R, p = Matrix.det (1 - (Polynomial.X : Polynomial R) •
      Matrix.of fun j i : S ↦ Polynomial.C (matrixCoeff u j i)) := ⟨_, rfl⟩
  have hcoeff : ∀ n, charCoeff u n = p.coeff n := hp ▸ charCoeff_eq_det_coeff u S hS
  have hdeg : p.natDegree < S.card + 1 :=
    Nat.lt_succ_of_le <| Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun N hN ↦
      (hcoeff N).symm.trans (charCoeff_eq_zero_of_card_lt hS hN)
  have hev : Polynomial.eval (1 : R) p
      = Matrix.det (1 - Matrix.of fun j i : S ↦ matrixCoeff u j i) := by
    change (Polynomial.evalRingHom (1 : R)) p = _
    rw [hp, RingHom.map_det]
    refine congrArg Matrix.det (Matrix.ext fun x y ↦ ?_)
    simp only [Matrix.smul_of, RingHom.mapMatrix_apply, Polynomial.coe_evalRingHom,
      Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, Pi.smul_apply,
      smul_eq_mul, Polynomial.X_mul_C, Polynomial.eval_sub, apply_ite (Polynomial.eval (1 : R)),
      Polynomial.eval_one, Polynomial.eval_zero, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, mul_one]
  rw [← hev, Polynomial.eval_eq_sum_range' hdeg (1 : R), fredholmDet, PowerSeries.evalT,
    tsum_eq_sum (s := Finset.range (S.card + 1)) ?_]
  · exact Finset.sum_congr rfl fun n _ ↦ by rw [charPowerSeries_coeff, hcoeff n]
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [charPowerSeries_coeff, charCoeff_eq_zero_of_card_lt hS hn, zero_mul]

/-- Composition of operators has the matrix-product coefficients when the inner factor
is row-supported. -/
theorem matrixCoeff_mul_of_rows (u v : c(I, R) →L[R] c(I, R)) (S : Finset I)
    (hv : ∀ j ∉ S, ∀ i, matrixCoeff v j i = 0) (j i : I) :
    matrixCoeff (u * v) j i = ∑ k ∈ S, matrixCoeff u j k * matrixCoeff v k i := by
  have h1 : v (cSpace.single i 1) = ∑ k ∈ S, matrixCoeff v k i • cSpace.single k (1 : R) :=
    HasSum.unique (cSpace.hasSum_single _)
      (hasSum_sum_of_ne_finset_zero fun k hk ↦
        show matrixCoeff v k i • cSpace.single k (1 : R) = 0 by rw [hv k hk, zero_smul])
  have h2 : matrixCoeff (u * v) j i = cSpace.evalCLM j (u (v (cSpace.single i 1))) := rfl
  rw [h2, h1, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_smul, map_smul, smul_eq_mul, mul_comm]
  rfl


private theorem det_updateRow_sub {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n R) (r : n)
    (u v : n → R) : (M.updateRow r (u - v)).det = (M.updateRow r u).det - (M.updateRow r v).det :=
  eq_sub_of_add_eq (by rw [← Matrix.det_updateRow_add, sub_add_cancel])

private theorem norm_det_sub_det_le_of_row_eq {n : Type*} [Fintype n] [DecidableEq n]
    (M N : Matrix n n R) (r : n) (hrow : ∀ p ≠ r, M p = N p) (f : n → ℝ) {ε c : ℝ} (hε : 0 ≤ ε)
    (hM : ∀ p q, ‖M p q‖ ≤ f p) (hr : ∀ q, ‖M r q - N r q‖ ≤ ε)
    (hprod : ∏ q ∈ Finset.univ.erase r, f q ≤ c) : ‖M.det - N.det‖ ≤ ε * c := by
  have hN : M.updateRow r (N r) = N := by
    ext p q
    rcases eq_or_ne p r with rfl | hp
    · rw [Matrix.updateRow_self]
    · rw [Matrix.updateRow_ne hp, hrow p hp]
  rw [show M.det - N.det = (M.updateRow r (M r - N r)).det by
    rw [det_updateRow_sub, Matrix.updateRow_eq_self, hN]]
  refine (norm_det_le_of_row_bounds' _ (Function.update f r ε) fun p q ↦ ?_).trans ?_
  · rw [Matrix.updateRow_apply, Function.update_apply]
    split_ifs with hp
    · exact hr q
    · exact hM p q
  · rw [Finset.prod_update_of_mem (Finset.mem_univ r), ← Finset.erase_eq]
    exact mul_le_mul_of_nonneg_left hprod hε

/- Serre's "somme de produits de différences" [Serre1962, §5 p. 77].  Refines
`norm_det_sub_det_le` (private in `Fredholm.lean`), whose uniform bound `max ‖u‖ ‖v‖ ^ (m−1)`
diverges at radius `M ≥ 1` and is therefore insufficient for Proposition 8. -/
private theorem norm_det_sub_det_le' {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n R)
    (f : n → ℝ) {ε c : ℝ} (hε : 0 ≤ ε) (hc : 0 ≤ c) (hA : ∀ p q, ‖A p q‖ ≤ f p)
    (hB : ∀ p q, ‖B p q‖ ≤ f p) (hAB : ∀ p q, ‖A p q - B p q‖ ≤ ε)
    (hprod : ∀ p : n, ∏ q ∈ Finset.univ.erase p, f q ≤ c) : ‖A.det - B.det‖ ≤ ε * c := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card n) with hcard | hcard
  · have : IsEmpty n := Fintype.card_eq_zero_iff.1 hcard
    rw [Matrix.det_isEmpty, Matrix.det_isEmpty, sub_self, norm_zero]
    exact mul_nonneg hε hc
  set m : ℕ := Fintype.card n
  obtain ⟨e⟩ : Nonempty (Fin m ≃ n) := ⟨(Fintype.equivFin n).symm⟩
  set H : ℕ → Matrix n n R :=
    fun t ↦ Matrix.of fun p q ↦ if ((e.symm p : Fin m) : ℕ) < t then A p q else B p q
  have hH0 : H 0 = B := by
    ext p q
    show (if ((e.symm p : Fin m) : ℕ) < 0 then A p q else B p q) = B p q
    exact if_neg (Nat.not_lt_zero _)
  have hHm : H m = A := by
    ext p q
    show (if ((e.symm p : Fin m) : ℕ) < m then A p q else B p q) = A p q
    exact if_pos (e.symm p).2
  have hHb : ∀ (t : ℕ) (p q : n), ‖H t p q‖ ≤ f p := fun t p q ↦ by
    show ‖if ((e.symm p : Fin m) : ℕ) < t then A p q else B p q‖ ≤ f p
    split
    · exact hA p q
    · exact hB p q
  rw [show A.det - B.det = ∑ t ∈ Finset.range m, ((H (t + 1)).det - (H t).det) by
    rw [Finset.sum_range_sub (fun t ↦ (H t).det), hH0, hHm]]
  have hne : (Finset.range m).Nonempty := ⟨0, Finset.mem_range.2 hcard⟩
  refine (hne.norm_sum_le_sup'_norm _).trans (Finset.sup'_le _ _ fun t ht ↦ ?_)
  rw [Finset.mem_range] at ht
  have hidx : ∀ p, p ≠ e ⟨t, ht⟩ → ((e.symm p : Fin m) : ℕ) ≠ t := fun p hp h ↦
    hp <| (e.apply_symm_apply p).symm.trans (congrArg (⇑e) (Fin.ext h))
  refine norm_det_sub_det_le_of_row_eq (H (t + 1)) (H t) (e ⟨t, ht⟩) (fun p hp ↦ ?_) f hε
    (hHb (t + 1)) (fun q ↦ ?_) (hprod _)
  · funext q
    show (if ((e.symm p : Fin m) : ℕ) < t + 1 then A p q else B p q)
      = if ((e.symm p : Fin m) : ℕ) < t then A p q else B p q
    exact if_congr ⟨fun h ↦ lt_of_le_of_ne (Nat.lt_succ_iff.1 h) (hidx p hp),
      Nat.lt_succ_of_lt⟩ rfl rfl
  · show ‖(if ((e.symm (e ⟨t, ht⟩) : Fin m) : ℕ) < t + 1 then A _ q else B _ q)
        - if ((e.symm (e ⟨t, ht⟩) : Fin m) : ℕ) < t then A _ q else B _ q‖ ≤ ε
    rw [Equiv.symm_apply_apply]
    show ‖(if t < t + 1 then A _ q else B _ q) - if t < t then A _ q else B _ q‖ ≤ ε
    rw [if_pos (Nat.lt_succ_self t), if_neg (lt_irrefl t)]
    exact hAB _ _

-- Serre's minor-difference estimate [Serre1962, §5 p. 77].
private theorem norm_minor_sub_minor_le (v u : c(I, R) →L[R] c(I, R)) {g : I → ℝ}
    (hg0 : ∀ j, 0 ≤ g j) (hgv : ∀ j i, ‖matrixCoeff v j i‖ ≤ g j)
    (hgu : ∀ j i, ‖matrixCoeff u j i‖ ≤ g j) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∀ j i, ‖matrixCoeff v j i - matrixCoeff u j i‖ ≤ η) {δ D : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hD1 : (1 : ℝ) ≤ D) (hgD : ∀ j, g j ≤ D) (B : Finset I) (hgδ : ∀ j ∉ B, g j ≤ δ) (m : ℕ)
    (T : Finset I) (hT : T.card = m) :
    ‖minor v T - minor u T‖ ≤ η * (D ^ B.card * δ ^ (m - 1 - B.card)) := by
  refine norm_det_sub_det_le' _ _ (fun q : T ↦ g (q : I)) hη0
    (mul_nonneg (pow_nonneg (zero_le_one.trans hD1) _) (pow_nonneg hδ0.le _)) (fun p q ↦ hgv _ _)
    (fun p q ↦ hgu _ _) (fun p q ↦ hη _ _) fun p ↦ ?_
  refine prod_le_of_threshold (g := fun q : T ↦ g (q : I)) (fun q ↦ hg0 _) hδ0 hδ1 hD1
    (fun q ↦ hgD _) (fun q : T ↦ (q : I) ∈ B) (fun q hq ↦ hgδ _ hq) _ ?_ ?_
  · exact Finset.card_le_card_of_injOn Subtype.val (fun _ hq ↦ (Finset.mem_filter.1 hq).2)
      Set.injOn_subtype_val
  · rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_coe, hT]

private theorem pow_sub_mul_pow_le_div_of_mul_le_half {δ C : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hC1 : (1 : ℝ) ≤ C) (hδC : δ * C ≤ 1 / 2) (b m : ℕ) :
    δ ^ (m - 1 - b) * C ^ m ≤ C ^ (b + 1) / δ ^ b := by
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  rw [le_div_iff₀ (pow_pos hδ0 b)]
  by_cases hcase : m - 1 ≤ b
  · rw [show m - 1 - b = 0 by omega, pow_zero, one_mul]
    calc C ^ m * δ ^ b ≤ C ^ m :=
          mul_le_of_le_one_right (pow_nonneg hC0.le _) (pow_le_one₀ hδ0.le hδ1)
      _ ≤ C ^ (b + 1) := pow_le_pow_right₀ hC1 (by omega)
  · have hδpow : δ ^ (m - 1 - b) * δ ^ b = δ ^ (m - 1) := by
      rw [← pow_add, Nat.sub_add_cancel (by omega : b ≤ m - 1)]
    have hCpow : C ^ (m - 1) * C = C ^ m := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]
    calc δ ^ (m - 1 - b) * C ^ m * δ ^ b = (δ * C) ^ (m - 1) * C := by
          rw [mul_pow, ← hCpow, ← hδpow]
          ring
      _ ≤ C := mul_le_of_le_one_left hC0.le
            (pow_le_one₀ (mul_nonneg hδ0.le hC0.le) (hδC.trans (by norm_num)))
      _ ≤ C ^ (b + 1) := by simpa using pow_le_pow_right₀ hC1 (Nat.le_add_left 1 b)

private theorem norm_charCoeff_sub_le_of_norm_minor_sub_le [IsTate R] {v u : c(I, R) →L[R] c(I, R)}
    (hv : IsCompactoid v) (hu : IsCompactoid u) (m : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hminor : ∀ T : Finset I, T.card = m → ‖minor v T - minor u T‖ ≤ A) :
    ‖charCoeff v m - charCoeff u m‖ ≤ A := by
  have hsum := (summable_minor v hv m).hasSum.sub (summable_minor u hu m).hasSum
  rw [charCoeff, charCoeff, ← mul_sub, ← hsum.tsum_eq]
  refine (norm_mul_le _ _).trans ?_
  rw [norm_neg_one_pow', one_mul]
  exact (norm_tsum_le_iSup hsum.summable.tendsto_cofinite_zero).trans
    (Real.iSup_le (fun T ↦ hminor _ T.2) hA)

private theorem norm_charCoeff_sub_le_of_opNorm_sub_le [IsTate R] {v u : c(I, R) →L[R] c(I, R)}
    (hv : IsCompactoid v) (hu : IsCompactoid u) {δ D η : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hD1 : (1 : ℝ) ≤ D) (hDu : ‖u‖ ≤ D) (hη0 : 0 < η) (hηδ : η ≤ δ) (hη1 : η ≤ 1) (B : Finset I)
    (hδB : ∀ j ∉ B, rowNorm u j ≤ δ) (hvu : ‖v - u‖ ≤ η) (m : ℕ) :
    ‖charCoeff v m - charCoeff u m‖ ≤ η * (D ^ B.card * δ ^ (m - 1 - B.card)) := by
  have hD0 : (0 : ℝ) < D := lt_of_lt_of_le one_pos hD1
  set g : I → ℝ := fun j ↦ max (rowNorm u j) η
  have hg0 : ∀ j, 0 ≤ g j := fun j ↦ le_max_of_le_left (rowNorm_nonneg u j)
  have hgu : ∀ j i, ‖matrixCoeff u j i‖ ≤ g j := fun j i ↦
    (norm_matrixCoeff_le_rowNorm' u j i).trans (le_max_left _ _)
  have hrow : ∀ j, rowNorm (v - u) j ≤ η := fun j ↦ (rowNorm_le_opNorm' _ j).trans hvu
  have hgv : ∀ j i, ‖matrixCoeff v j i‖ ≤ g j := fun j i ↦ by
    refine (norm_matrixCoeff_le_rowNorm' v j i).trans ?_
    have hsum := rowNorm_add_le (v - u) u j
    rw [sub_add_cancel] at hsum
    exact hsum.trans (max_le (le_max_of_le_right (hrow j)) (le_max_left _ _))
  have hdiff : ∀ j i, ‖matrixCoeff v j i - matrixCoeff u j i‖ ≤ η := fun j i ↦ by
    rw [← matrixCoeff_sub]
    exact (norm_matrixCoeff_le' (v - u) j i).trans hvu
  have hgD : ∀ j, g j ≤ D := fun j ↦ max_le ((rowNorm_le_opNorm' u j).trans hDu) (hη1.trans hD1)
  have hgδ : ∀ j ∉ B, g j ≤ δ := fun j hj ↦ max_le (hδB j hj) hηδ
  exact norm_charCoeff_sub_le_of_norm_minor_sub_le hv hu m
    (mul_nonneg hη0.le (mul_nonneg (pow_nonneg hD0.le _) (pow_nonneg hδ0.le _)))
    fun T hT ↦ norm_minor_sub_minor_le v u hg0 hgv hgu hη0.le hdiff hδ0 hδ1 hD1 hgD B hgδ m T hT

/-- Serre's Proposition 8 [Serre1962, §5 p. 77], the uniform-convergence engine: if
`wₙ → u` in operator norm along any filter (all compactoid), the characteristic coefficients
converge uniformly at any radius `M`. -/
theorem eventually_norm_charCoeff_sub_le [IsTate R] {u : c(I, R) →L[R] c(I, R)}
    (hu : IsCompactoid u) {ι : Type*} {l : Filter ι} {w : ι → c(I, R) →L[R] c(I, R)}
    (hw : ∀ n, IsCompactoid (w n)) (hconv : Tendsto (fun n ↦ ‖w n - u‖) l (𝓝 0)) (M : ℝ)
    (hM : 0 < M) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in l, ∀ m, ‖charCoeff (w n) m - charCoeff u m‖ * M ^ m ≤ ε := by
  classical
  set C : ℝ := max M 1
  have hC1 : (1 : ℝ) ≤ C := le_max_right _ _
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  set δ : ℝ := min (1 / (2 * C)) 1
  have hδ0 : 0 < δ := lt_min (by positivity) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδC : δ * C ≤ 1 / 2 := by
    calc δ * C ≤ 1 / (2 * C) * C := mul_le_mul_of_nonneg_right (min_le_left _ _) hC0.le
    _ = 1 / 2 := by field_simp
  set D : ℝ := max ‖u‖ 1
  have hD1 : (1 : ℝ) ≤ D := le_max_right _ _
  have hD0 : (0 : ℝ) < D := lt_of_lt_of_le one_pos hD1
  have hbad : {j : I | δ ≤ rowNorm u j}.Finite := by
    have hev : ∀ᶠ j in cofinite, rowNorm u j < δ := by
      filter_upwards [Metric.tendsto_nhds.1 hu δ hδ0] with j hj
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (rowNorm_nonneg u j)] at hj
    simpa only [not_lt] using Filter.eventually_cofinite.1 hev
  set b : ℕ := hbad.toFinset.card
  set K : ℝ := C ^ (b + 1) / δ ^ b
  have hK0 : 0 < K := div_pos (pow_pos hC0 _) (pow_pos hδ0 _)
  set η : ℝ := min δ (ε / (D ^ b * K)) with hηdef
  have hη0 : 0 < η := lt_min hδ0 (div_pos hε (mul_pos (pow_pos hD0 _) hK0))
  have hfinal : η * (D ^ b * K) ≤ ε := by
    rw [← le_div_iff₀ (mul_pos (pow_pos hD0 b) hK0), hηdef]
    exact min_le_right _ _
  have hev : ∀ᶠ n in l, ‖w n - u‖ ≤ η := by
    filter_upwards [Metric.tendsto_nhds.1 hconv η hη0] with n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (opNorm_nonneg _)] at hn
    exact hn.le
  filter_upwards [hev] with n hn m
  have hcoeff : ‖charCoeff (w n) m - charCoeff u m‖ ≤ η * (D ^ b * δ ^ (m - 1 - b)) :=
    norm_charCoeff_sub_le_of_opNorm_sub_le (hw n) hu hδ0 hδ1 hD1 (le_max_left _ _) hη0
      (min_le_left _ _) ((min_le_left _ _).trans hδ1) hbad.toFinset
      (fun j hj ↦ (not_le.1 fun h ↦ hj (hbad.mem_toFinset.2 h)).le) hn m
  calc ‖charCoeff (w n) m - charCoeff u m‖ * M ^ m
      ≤ η * (D ^ b * δ ^ (m - 1 - b)) * M ^ m :=
        mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hM.le m)
    _ ≤ η * (D ^ b * δ ^ (m - 1 - b)) * C ^ m := by
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM.le (le_max_left _ _) m) ?_
        exact mul_nonneg hη0.le (mul_nonneg (pow_nonneg hD0.le _) (pow_nonneg hδ0.le _))
    _ = η * D ^ b * (δ ^ (m - 1 - b) * C ^ m) := by ring
    _ ≤ η * D ^ b * K :=
        mul_le_mul_of_nonneg_left (pow_sub_mul_pow_le_div_of_mul_le_half hδ0 hδ1 hC1 hδC b m)
          (mul_nonneg hη0.le (pow_nonneg hD0.le _))
    _ = η * (D ^ b * K) := mul_assoc _ _ _
    _ ≤ ε := hfinal

-- The `*`-form of the truncation matrix coefficients; `matrixCoeff_truncation_comp_sub` in
-- `Matrix.lean` is private and states only the `- u` version.
private theorem matrixCoeff_truncation_mul (u : c(I, R) →L[R] c(I, R)) (S : Finset I) (j i : I) :
    matrixCoeff (truncation S * u) j i = if j ∈ S then matrixCoeff u j i else 0 := rfl

-- The `*`-form of the tail bound; `norm_truncation_comp_sub_le` in `Matrix.lean` is private.
private theorem norm_truncation_mul_sub_le [IsTate R] (u : c(I, R) →L[R] c(I, R)) (S : Finset I)
    {ε : ℝ} (hε : 0 ≤ ε) (hrow : ∀ j ∉ S, rowNorm u j ≤ ε) : ‖truncation S * u - u‖ ≤ ε := by
  rw [norm_eq_iSup_matrixCoeff]
  refine Real.iSup_le (fun j ↦ Real.iSup_le (fun i ↦ ?_) hε) hε
  rw [matrixCoeff_sub, matrixCoeff_truncation_mul]
  split_ifs with hj
  · simpa using hε
  · simpa using (norm_matrixCoeff_le_rowNorm' u j i).trans (hrow j hj)

-- Bridges the `Finset I`-directed convergence of `tendsto_truncation_comp` to the `ℕ`-indexed
-- sequences that `eventually_norm_charCoeff_sub_le` (Serre's Proposition 8) consumes.
private theorem exists_truncation_seq [IsTate R] {u v : c(I, R) →L[R] c(I, R)} (hu : IsCompactoid u)
    (hv : IsCompactoid v) :
    ∃ S : ℕ → Finset I, Tendsto (fun n ↦ ‖truncation (S n) * u - u‖) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ ‖truncation (S n) * v - v‖) atTop (𝓝 0) := by
  classical
  have hbad : ∀ w : c(I, R) →L[R] c(I, R), IsCompactoid w → ∀ n : ℕ,
      {j : I | 1 / (n + 1 : ℝ) ≤ rowNorm w j}.Finite := fun w hw n ↦ by
    have hev : ∀ᶠ j in cofinite, rowNorm w j < 1 / (n + 1 : ℝ) :=
      Filter.Tendsto.eventually_lt_const (by positivity) hw
    simpa using Filter.eventually_cofinite.1 hev
  have key : ∀ (w : c(I, R) →L[R] c(I, R)) (S : ℕ → Finset I),
      (∀ (n : ℕ) j, 1 / (n + 1 : ℝ) ≤ rowNorm w j → j ∈ S n) →
      Tendsto (fun n ↦ ‖truncation (S n) * w - w‖) atTop (𝓝 0) := by
    refine fun w S hS ↦ squeeze_zero (g := fun n : ℕ ↦ 1 / (n + 1 : ℝ))
      (fun n ↦ opNorm_nonneg _) (fun n ↦ ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    exact norm_truncation_mul_sub_le w _ (by positivity) fun j hj ↦
      not_lt.1 fun h ↦ hj (hS n j h.le)
  exact ⟨fun n ↦ (hbad u hu n).toFinset ∪ (hbad v hv n).toFinset,
    key u _ fun n j hj ↦ Finset.mem_union_left _ ((hbad u hu n).mem_toFinset.2 hj),
    key v _ fun n j hj ↦ Finset.mem_union_right _ ((hbad v hv n).mem_toFinset.2 hj)⟩

private theorem summable_charCoeff_one [IsTate R] {x : c(I, R) →L[R] c(I, R)}
    (hx : IsCompactoid x) :
    Summable fun m ↦ PowerSeries.coeff m (charPowerSeries x) * (1 : R) ^ m :=
  PowerSeries.summable_coeff_mul_pow <| PowerSeries.tendsto_norm_coeff_mul_pow_of_isRestricted
    (charPowerSeries_isEntire x hx 1 one_pos) norm_one.le

private theorem norm_fredholmDet_sub_le [IsTate R] {x y : c(I, R) →L[R] c(I, R)}
    (hx : IsCompactoid x) (hy : IsCompactoid y) {ε : ℝ}
    (hb : ∀ m, ‖charCoeff x m - charCoeff y m‖ ≤ ε) : ‖fredholmDet x - fredholmDet y‖ ≤ ε := by
  have hsub := (summable_charCoeff_one hx).hasSum.sub (summable_charCoeff_one hy).hasSum
  rw [fredholmDet, fredholmDet, PowerSeries.evalT, PowerSeries.evalT, ← hsub.tsum_eq]
  exact (norm_tsum_le_iSup hsub.summable.tendsto_cofinite_zero).trans <|
    Real.iSup_le (fun m ↦ by simpa using hb m) ((norm_nonneg _).trans (hb 0))

-- Serre's Proposition 8 (`eventually_norm_charCoeff_sub_le`) specialised to radius `M = 1`.
private theorem tendsto_fredholmDet [IsTate R] {u : c(I, R) →L[R] c(I, R)} (hu : IsCompactoid u)
    {w : ℕ → c(I, R) →L[R] c(I, R)} (hw : ∀ n, IsCompactoid (w n))
    (hconv : Tendsto (fun n ↦ ‖w n - u‖) atTop (𝓝 0)) :
    Tendsto (fun n ↦ fredholmDet (w n)) atTop (𝓝 (fredholmDet u)) := by
  refine Metric.nhds_basis_closedBall.tendsto_right_iff.2 fun ε hε ↦ ?_
  filter_upwards [eventually_norm_charCoeff_sub_le hu hw hconv 1 one_pos hε] with n hn
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact norm_fredholmDet_sub_le (hw n) hu fun m ↦ by simpa using hn m

private theorem fredholmDet_zero : fredholmDet (0 : c(I, R) →L[R] c(I, R)) = 1 :=
  (fredholmDet_eq_det_of_rows _ ∅ fun _ _ _ ↦ rfl).trans Matrix.det_isEmpty

private theorem fredholmDet_mul_of_rows (x y : c(I, R) →L[R] c(I, R)) (S : Finset I)
    (hx : ∀ j ∉ S, ∀ i, matrixCoeff x j i = 0) (hy : ∀ j ∉ S, ∀ i, matrixCoeff y j i = 0) :
    fredholmDet (x + y - x * y) = fredholmDet x * fredholmDet y := by
  have hxy : ∀ j ∉ S, ∀ i, matrixCoeff (x * y) j i = 0 := fun j hj i ↦
    (matrixCoeff_mul_of_rows x y S hy j i).trans <|
      Finset.sum_eq_zero fun k _ ↦ by rw [hx j hj k, zero_mul]
  have hw : ∀ j ∉ S, ∀ i, matrixCoeff (x + y - x * y) j i = 0 := fun j hj i ↦ by
    rw [matrixCoeff_sub, matrixCoeff_add, hx j hj i, hy j hj i, hxy j hj i, add_zero, sub_zero]
  have hmat : (Matrix.of fun j i : S ↦ matrixCoeff (x + y - x * y) j i)
      = (Matrix.of fun j i : S ↦ matrixCoeff x j i) + (Matrix.of fun j i : S ↦ matrixCoeff y j i)
        - (Matrix.of fun j i : S ↦ matrixCoeff x j i)
          * (Matrix.of fun j i : S ↦ matrixCoeff y j i) := by
    refine Matrix.ext fun p q ↦ ?_
    rw [Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, matrixCoeff_sub,
      matrixCoeff_add, matrixCoeff_mul_of_rows x y S hy (p : I) (q : I),
      ← Finset.sum_coe_sort S fun k ↦ matrixCoeff x (p : I) k * matrixCoeff y k (q : I)]
    rfl
  have hfac : ∀ A B : Matrix S S R, (1 : Matrix S S R) - (A + B - A * B) = (1 - A) * (1 - B) :=
    fun A B ↦ by noncomm_ring
  rw [fredholmDet_eq_det_of_rows _ S hw, fredholmDet_eq_det_of_rows _ S hx,
    fredholmDet_eq_det_of_rows _ S hy, hmat, hfac, Matrix.det_mul]

private theorem opNorm_sub_le [IsTate R] (x y : c(I, R) →L[R] c(I, R)) : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := by
  simpa [sub_eq_add_neg] using norm_add_le x (-y)

private theorem tendsto_norm_mul_sub_mul [IsTate R] {α : Type*} {F : Filter α} {D : ℝ}
    (a₀ b₀ : c(I, R) →L[R] c(I, R)) (a b : α → c(I, R) →L[R] c(I, R)) (hD : ∀ x, ‖b x‖ ≤ D)
    (ha : Tendsto (fun x ↦ ‖a x - a₀‖) F (𝓝 0)) (hb : Tendsto (fun x ↦ ‖b x - b₀‖) F (𝓝 0)) :
    Tendsto (fun x ↦ ‖a x * b x - a₀ * b₀‖) F (𝓝 0) := by
  have hg : Tendsto (fun x ↦ ‖a x - a₀‖ * D + ‖a₀‖ * ‖b x - b₀‖) F (𝓝 0) := by
    simpa using (ha.mul_const D).add (hb.const_mul ‖a₀‖)
  refine squeeze_zero (fun x ↦ opNorm_nonneg _) (fun x ↦ ?_) hg
  rw [show a x * b x - a₀ * b₀ = (a x - a₀) * b x + a₀ * (b x - b₀) by noncomm_ring]
  exact (norm_add_le _ _).trans (add_le_add ((opNorm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left (hD x) (opNorm_nonneg _))) (opNorm_mul_le _ _))

private theorem tendsto_norm_add_sub_mul_sub_add_sub_mul [IsTate R] {α : Type*} {F : Filter α}
    {D : ℝ} (a₀ b₀ : c(I, R) →L[R] c(I, R)) (a b : α → c(I, R) →L[R] c(I, R)) (hD : ∀ x, ‖b x‖ ≤ D)
    (ha : Tendsto (fun x ↦ ‖a x - a₀‖) F (𝓝 0)) (hb : Tendsto (fun x ↦ ‖b x - b₀‖) F (𝓝 0)) :
    Tendsto (fun x ↦ ‖a x + b x - a x * b x - (a₀ + b₀ - a₀ * b₀)‖) F (𝓝 0) := by
  have hg : Tendsto (fun x ↦ ‖a x - a₀‖ + ‖b x - b₀‖ + ‖a x * b x - a₀ * b₀‖) F (𝓝 0) := by
    simpa using (ha.add hb).add (tendsto_norm_mul_sub_mul a₀ b₀ a b hD ha hb)
  refine squeeze_zero (fun x ↦ opNorm_nonneg _) (fun x ↦ ?_) hg
  rw [show a x + b x - a x * b x - (a₀ + b₀ - a₀ * b₀)
      = a x - a₀ + (b x - b₀) - (a x * b x - a₀ * b₀) by noncomm_ring]
  exact (opNorm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)

/-- Multiplicativity of the determinant value [Serre1962, §5 p. 76, Corollaire 1 à la
Proposition 7]: `1 - (u + v - uv) = (1 - u)(1 - v)`, so `det(1 - ·)` factors. -/
theorem fredholmDet_mul [IsTate R] {u v : c(I, R) →L[R] c(I, R)} (hu : IsCompactoid u)
    (hv : IsCompactoid v) : fredholmDet (u + v - u * v) = fredholmDet u * fredholmDet v := by
  obtain ⟨S, hSu, hSv⟩ := exists_truncation_seq hu hv
  have hfin : ∀ n : ℕ, fredholmDet (truncation (S n) * u + truncation (S n) * v
        - truncation (S n) * u * (truncation (S n) * v))
      = fredholmDet (truncation (S n) * u) * fredholmDet (truncation (S n) * v) :=
    fun n ↦ fredholmDet_mul_of_rows _ _ (S n)
      (fun j hj i ↦ (matrixCoeff_truncation_mul u (S n) j i).trans (if_neg hj))
      (fun j hj i ↦ (matrixCoeff_truncation_mul v (S n) j i).trans (if_neg hj))
  have hUc : ∀ n : ℕ, IsCompactoid (truncation (S n) * u) :=
    fun n ↦ hu.comp_left (truncation (S n))
  have hVc : ∀ n : ℕ, IsCompactoid (truncation (S n) * v) :=
    fun n ↦ hv.comp_left (truncation (S n))
  have hWc : ∀ n : ℕ, IsCompactoid (truncation (S n) * u + truncation (S n) * v
      - truncation (S n) * u * (truncation (S n) * v)) :=
    fun n ↦ ((hUc n).add (hVc n)).sub ((hUc n).comp_right (truncation (S n) * v))
  have hVb : ∀ n : ℕ, ‖truncation (S n) * v‖ ≤ ‖v‖ := fun n ↦ opNorm_truncation_comp_le v (S n)
  exact tendsto_nhds_unique ((tendsto_fredholmDet ((hu.add hv).sub (hu.comp_right v)) hWc
    (tendsto_norm_add_sub_mul_sub_add_sub_mul u v _ _ hVb hSu hSv)).congr hfin)
    ((tendsto_fredholmDet hu hUc hSu).mul (tendsto_fredholmDet hv hVc hSv))

end DetValue

section Riesz

/-- Serre's Proposition 11, easy direction [Serre1962, §7 p. 80]: if `H(a)` is a unit
then `1 - a•u` is invertible. -/
theorem isUnit_one_sub_smul_of_isUnit_evalT [IsTate R] {u : c(I, R) →L[R] c(I, R)}
    (hu : IsCompactoid u) {a : R} (hd : IsUnit (PowerSeries.evalT a (charPowerSeries u))) :
    IsUnit (1 - a • u) := by
  obtain ⟨N, hN⟩ := exists_isOpLimit_resolventPartialSum u hu a 0
  have hcomm : Commute (1 - a • u) N := (Commute.one_left N).sub_left
    (Commute.smul_left (commute_of_isOpLimit_resolventPartialSum hN) a)
  refine (hcomm.isUnit_mul_iff.1 ?_).1
  rw [one_sub_smul_mul_resolventEval_zero hu hN, ← Algebra.algebraMap_eq_smul_one]
  exact hd.map (algebraMap R (c(I, R) →L[R] c(I, R)))

/-- Serre's Proposition 11, hard direction [Serre1962, §7 p. 80]: if `1 - a•u` is
invertible then `H(a)` is a unit. -/
theorem isUnit_evalT_of_isUnit_one_sub_smul [IsTate R] {u : c(I, R) →L[R] c(I, R)}
    (hu : IsCompactoid u) {a : R} (h : IsUnit (1 - a • u)) :
    IsUnit (PowerSeries.evalT a (charPowerSeries u)) := by
  obtain ⟨w, hw⟩ := h.exists_right_inv
  obtain ⟨v, rfl⟩ : ∃ v, w = 1 - v := ⟨1 - w, (sub_sub_cancel 1 w).symm⟩
  have hvc : IsCompactoid v := by
    rw [show v = -(a • u * (1 - v)) by linear_combination (norm := noncomm_ring) -hw]
    exact ((hu.smul a).comp_right (1 - v)).neg
  have hzero : a • u + v - a • u * v = 0 := by linear_combination (norm := noncomm_ring) -hw
  refine IsUnit.of_mul_eq_one (fredholmDet v) ?_
  rw [← fredholmDet_smul a u hu, ← fredholmDet_mul (hu.smul a) hvc, hzero, fredholmDet_zero]

/-- Serre's Proposition 11 [Serre1962, §7 p. 80], unit form over a Banach–Tate ring:
`1 - a•u` is invertible iff `H(a)` is a unit. -/
theorem isUnit_one_sub_smul_iff_isUnit_evalT [IsTate R] {u : c(I, R) →L[R] c(I, R)}
    (hu : IsCompactoid u) (a : R) :
    IsUnit (1 - a • u) ↔ IsUnit (PowerSeries.evalT a (charPowerSeries u)) :=
  ⟨isUnit_evalT_of_isUnit_one_sub_smul hu, isUnit_one_sub_smul_of_isUnit_evalT hu⟩

-- Serre's `Δˢ`-equations kill `N₀, …, N_{h-1}` when `1 - a•u` is injective [Serre1962, §7 p. 80].
private theorem resolventEval_eq_zero_of_ker_eq_zero [IsTate R] {u : c(I, R) →L[R] c(I, R)}
    (hu : IsCompactoid u) {a : R} {h : ℕ} {N : ℕ → c(I, R) →L[R] c(I, R)}
    (h0 : ∀ s < h, PowerSeries.evalT a (PowerSeries.hasseDeriv s (charPowerSeries u)) = 0)
    (hN : ∀ s, IsOpLimit (resolventPartialSum u a s) (N s))
    (hker : ∀ x : c(I, R), (1 - a • u) x = 0 → x = 0) (s : ℕ) (hs : s < h) :
    N s = 0 := by
  have hcancel : ∀ M : c(I, R) →L[R] c(I, R), (1 - a • u) * M = 0 → M = 0 := fun M hM ↦
    ContinuousLinearMap.ext fun x ↦ hker (M x) (DFunLike.congr_fun hM x)
  induction s with
  | zero =>
    have hH0 := h0 0 hs
    rw [PowerSeries.hasseDeriv_zero] at hH0
    refine hcancel _ ?_
    rw [one_sub_smul_mul_resolventEval_zero hu (hN 0), hH0, zero_smul]
  | succ t ih =>
    refine hcancel _ ?_
    rw [one_sub_smul_mul_resolventEval hu (by omega : 1 ≤ t + 1) (hN (t + 1)) (hN t),
      ih (by omega), h0 (t + 1) hs, mul_zero, zero_smul, add_zero]

private theorem isUnit_one_sub_smul_of_mul_eq_smul_one {u N : c(I, R) →L[R] c(I, R)} {a d : R}
    (hcomm : Commute u N) (hd : IsUnit d) (hmul : (1 - a • u) * N = d • 1) :
    IsUnit (1 - a • u) := by
  have hc : Commute (1 - a • u) N := (Commute.one_left N).sub_left (hcomm.smul_left a)
  have hright : (1 - a • u) * ((↑hd.unit⁻¹ : R) • N) = 1 := by
    rw [mul_smul_comm, hmul, smul_smul, hd.val_inv_mul, one_smul]
  exact isUnit_iff_exists.2 ⟨_, hright, by rw [smul_mul_assoc, ← hc.eq, ← mul_smul_comm, hright]⟩

/-- The dichotomy at a zero of finite order (the eigenvector content of [Serre1962, §7
Prop. 12], in Buzzard's divided-derivative formulation [Buzzard2007, pp. 22–23]): if
`a` is a zero of `H` of order `h ≥ 1`, then `1 - a•u` has a nonzero kernel element. -/
theorem exists_mem_ker_of_hasseDeriv_evalT [IsTate R] {u : c(I, R) →L[R] c(I, R)}
    (hu : IsCompactoid u) {a : R} {h : ℕ} (hh : 1 ≤ h)
    (h0 : ∀ s < h, PowerSeries.evalT a (PowerSeries.hasseDeriv s (charPowerSeries u)) = 0)
    (hunit : IsUnit (PowerSeries.evalT a (PowerSeries.hasseDeriv h (charPowerSeries u)))) :
    ∃ x : c(I, R), x ≠ 0 ∧ (1 - a • u) x = 0 := by
  by_contra hcon
  have hker : ∀ x : c(I, R), (1 - a • u) x = 0 → x = 0 := fun x hx ↦
    not_not.1 fun hx0 ↦ hcon ⟨x, hx0, hx⟩
  choose N hN using fun s : ℕ ↦ exists_isOpLimit_resolventPartialSum u hu a s
  have htop : (1 - a • u) * N h
      = PowerSeries.evalT a (PowerSeries.hasseDeriv h (charPowerSeries u)) • 1 := by
    rw [one_sub_smul_mul_resolventEval hu hh (hN h) (hN (h - 1)),
      resolventEval_eq_zero_of_ker_eq_zero hu h0 hN hker (h - 1) (by omega), mul_zero, zero_add]
  have hH0 : PowerSeries.evalT a (charPowerSeries u) = 0 := by simpa using h0 0 (by omega)
  have hHunit : IsUnit (PowerSeries.evalT a (charPowerSeries u)) :=
    isUnit_evalT_of_isUnit_one_sub_smul hu (isUnit_one_sub_smul_of_mul_eq_smul_one
      (commute_of_isOpLimit_resolventPartialSum (hN h)) hunit htop)
  rw [hH0] at hHunit
  have : Nontrivial R := NormOneClass.nontrivial
  exact not_isUnit_zero hHunit

end Riesz

section RieszDecomposition

-- Not inlined: this `DFunLike.congr_fun` step recurs throughout the section, and the
-- `ContinuousLinearMap.mul_apply` route it replaces is deprecated.
private theorem apply_of_mul_eq {A B C : c(I, R) →L[R] c(I, R)} (hABC : A * B = C) (x : c(I, R)) :
    A (B x) = C x := DFunLike.congr_fun hABC x

private theorem isIdempotentElem_pow_of_one_sub_mul_pow_eq_zero {A : Type*} [Ring A] {e : A} {n : ℕ}
    (he : (1 - e) * e ^ n = 0) : IsIdempotentElem (e ^ n) := by
  rw [sub_mul, one_mul, sub_eq_zero] at he
  suffices h : ∀ k, e ^ k * e ^ n = e ^ n from h n
  intro k
  induction k with
  | zero => rw [pow_zero, one_mul]
  | succ j ih => rw [pow_succ', mul_assoc, ih, ← he]

-- Serre's chain `(1 - a•u)^{s+1} Nₛ = 0` for `s < h` [Serre1962, §7 p. 80].
private theorem one_sub_smul_pow_mul_resolventEval_eq_zero [IsTate R] {u : c(I, R) →L[R] c(I, R)}
    (hu : IsCompactoid u) {a : R} {h : ℕ} {N : ℕ → c(I, R) →L[R] c(I, R)}
    (h0 : ∀ s < h, PowerSeries.evalT a (PowerSeries.hasseDeriv s (charPowerSeries u)) = 0)
    (hN : ∀ s, IsOpLimit (resolventPartialSum u a s) (N s)) (s : ℕ) (hs : s < h) :
    (1 - a • u) ^ (s + 1) * N s = 0 := by
  have hbu : Commute (1 - a • u) u := (Commute.one_left u).sub_left ((Commute.refl u).smul_left a)
  induction s with
  | zero =>
    have hH0 := h0 0 hs
    rw [PowerSeries.hasseDeriv_zero] at hH0
    rw [pow_one, one_sub_smul_mul_resolventEval_zero hu (hN 0), hH0, zero_smul]
  | succ t ih =>
    have heq : (1 - a • u) * N (t + 1) = u * N t := by
      rw [one_sub_smul_mul_resolventEval hu (by omega : 1 ≤ t + 1) (hN (t + 1)) (hN t),
        h0 (t + 1) hs, zero_smul, add_zero]
    calc (1 - a • u) ^ (t + 1 + 1) * N (t + 1)
        = (1 - a • u) ^ (t + 1) * ((1 - a • u) * N (t + 1)) := by rw [← mul_assoc, ← pow_succ]
    _ = u * ((1 - a • u) ^ (t + 1) * N t) := by
          rw [heq, ← mul_assoc, ← mul_assoc, (hbu.pow_left (t + 1)).eq]
    _ = 0 := by rw [ih (by omega), mul_zero]

/-- **Serre's Riesz projectors** [Serre1962, §7 p. 81]: at a zero of order `h ≥ 1`, from
`e := c⁻¹(1-au)N_h` and `f := -c⁻¹uN_{h-1}` (with `e + f = 1`, `f·eʰ = 0`), the binomial
expansion of `(e+f)ʰ = 1` splits as the idempotent `p := eʰ` and its complement.  The
witness `w` realises the invertibility of `1 - a•u` on the range of `p`.  Both `p` and `w`
lie in the closure of `R[u]` ([JN] Theorem 2.2.2, [Bel] II.2.17). -/
theorem exists_rieszProjection_isOpLimit [IsTate R] {u : c(I, R) →L[R] c(I, R)}
    (hu : IsCompactoid u) {a : R} {h : ℕ} (hh : 1 ≤ h)
    (h0 : ∀ s < h, PowerSeries.evalT a (PowerSeries.hasseDeriv s (charPowerSeries u)) = 0)
    (hunit : IsUnit (PowerSeries.evalT a (PowerSeries.hasseDeriv h (charPowerSeries u)))) :
    ∃ p w : c(I, R) →L[R] c(I, R),
      p * p = p ∧ u * p = p * u ∧ u * w = w * u ∧ p * w = w * p ∧
      (1 - a • u) ^ h * (1 - p) = 0 ∧ (1 - a • u) * w = p ∧
      IsOpLimitAeval u p ∧ IsOpLimitAeval u w := by
  choose N hN using fun s : ℕ ↦ exists_isOpLimit_resolventPartialSum u hu a s
  set b : c(I, R) →L[R] c(I, R) := 1 - a • u with hbdef
  have hcomm : ∀ s, Commute u (N s) := fun s ↦
    commute_of_isOpLimit_resolventPartialSum (hN s)
  have hbu : Commute b u := by
    rw [hbdef]; exact (Commute.one_left u).sub_left ((Commute.refl u).smul_left a)
  have hbN : ∀ s, Commute b (N s) := fun s ↦ by
    rw [hbdef]; exact (Commute.one_left (N s)).sub_left ((hcomm s).smul_left a)
  set d : R := PowerSeries.evalT a (PowerSeries.hasseDeriv h (charPowerSeries u))
  set di : R := (↑hunit.unit⁻¹ : R)
  have hdi : di * d = 1 := hunit.val_inv_mul
  have htop : b * N h = u * N (h - 1) + d • 1 := by
    rw [hbdef]; exact one_sub_smul_mul_resolventEval hu hh (hN h) (hN (h - 1))
  set e : c(I, R) →L[R] c(I, R) := di • (b * N h) with hedef
  have hone_sub_e : (1 : c(I, R) →L[R] c(I, R)) - e = -(di • (u * N (h - 1))) := by
    rw [hedef, htop, smul_add, smul_smul, hdi, one_smul]
    abel
  have hchain : b ^ h * N (h - 1) = 0 := by
    have h1 := one_sub_smul_pow_mul_resolventEval_eq_zero hu h0 hN (h - 1) (by omega)
    rwa [Nat.sub_add_cancel hh, ← hbdef] at h1
  have hbf : b ^ h * ((1 : c(I, R) →L[R] c(I, R)) - e) = 0 := by
    rw [hone_sub_e, mul_neg, mul_smul_comm, ← mul_assoc, (hbu.pow_left h).eq, mul_assoc,
      hchain, mul_zero, smul_zero, neg_zero]
  have heh : e ^ h = di ^ h • (b ^ h * N h ^ h) := by rw [hedef, smul_pow, (hbN h).mul_pow]
  have hfe : ((1 : c(I, R) →L[R] c(I, R)) - e) * e ^ h = 0 := by
    have hcore : u * N (h - 1) * (b ^ h * N h ^ h) = 0 := by
      rw [mul_assoc, ← mul_assoc (N (h - 1)), ← ((hbN (h - 1)).pow_left h).eq, hchain, zero_mul,
        mul_zero]
    rw [hone_sub_e, heh, neg_mul, smul_mul_assoc, mul_smul_comm, hcore, smul_zero, smul_zero,
      neg_zero]
  have hbe : Commute b e := by
    rw [hedef]; exact ((Commute.refl b).mul_right (hbN h)).smul_right di
  obtain ⟨q, hq⟩ := one_sub_dvd_one_sub_pow e h
  have hbw : b * (di ^ h • (b ^ (h - 1) * N h ^ h)) = e ^ h := by
    rw [mul_smul_comm, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hh, heh]
  have hNh : IsOpLimitAeval u (N h) := IsOpLimitAeval.of_resolventPartialSum (hN h)
  have hbl : IsOpLimitAeval u b := by
    have := IsOpLimitAeval.aeval u (1 - Polynomial.C a * Polynomial.X)
    rwa [map_sub, map_one, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, ← Algebra.smul_def,
      ← hbdef] at this
  refine ⟨e ^ h, di ^ h • (b ^ (h - 1) * N h ^ h),
    isIdempotentElem_pow_of_one_sub_mul_pow_eq_zero hfe, ?_, ?_, ?_,
    by rw [hq, ← mul_assoc, hbf, zero_mul], hbw, ((hbl.mul hNh).smul di).pow h,
    ((hbl.pow (h - 1)).mul (hNh.pow h)).smul (di ^ h)⟩
  · exact (((hbu.symm.mul_right (hcomm h)).smul_right di).pow_right h).eq
  · exact (((hbu.symm.pow_right (h - 1)).mul_right ((hcomm h).pow_right h)).smul_right (di ^ h)).eq
  · exact ((((hbe.symm.pow_right (h - 1)).mul_right
      ((((hbN h).mul_left (Commute.refl (N h))).smul_left di).pow_right h)).smul_right
      (di ^ h)).pow_left h).eq

/-- Serre's Riesz projectors (`exists_rieszProjection_isOpLimit` without the closure data). -/
theorem exists_rieszProjection [IsTate R] {u : c(I, R) →L[R] c(I, R)}
    (hu : IsCompactoid u) {a : R} {h : ℕ} (hh : 1 ≤ h)
    (h0 : ∀ s < h, PowerSeries.evalT a (PowerSeries.hasseDeriv s (charPowerSeries u)) = 0)
    (hunit : IsUnit (PowerSeries.evalT a (PowerSeries.hasseDeriv h (charPowerSeries u)))) :
    ∃ p w : c(I, R) →L[R] c(I, R),
      p * p = p ∧ u * p = p * u ∧ u * w = w * u ∧ p * w = w * p ∧
      (1 - a • u) ^ h * (1 - p) = 0 ∧ (1 - a • u) * w = p := by
  obtain ⟨p, w, h1, h2, h3, h4, h5, h6, -, -⟩ := exists_rieszProjection_isOpLimit hu hh h0 hunit
  exact ⟨p, w, h1, h2, h3, h4, h5, h6⟩

variable [IsTate R] {u p w : c(I, R) →L[R] c(I, R)} {a : R} {h : ℕ}

-- `_hup`/`_hpw` are unused here: the hypothesis list is `exists_rieszProjection`'s full
-- output interface, kept uniform across the four `rieszProjection` consumers.
-- `p = eʰ` is idempotent, so its powers collapse; at `h = 0` the nilpotency hypothesis forces
-- `p = 1`.  Shared by the two `…_one_sub_smul_pow_of_rieszProjection` characterisations.
omit [DecidableEq I] [IsTate R] in
private theorem pow_eq_of_rieszProjection (hp : p * p = p)
    (hnil : (1 - a • u) ^ h * (1 - p) = 0) : p ^ h = p := by
  obtain _ | k := h
  · simpa [sub_eq_zero] using hnil
  · exact IsIdempotentElem.pow_succ_eq k hp

omit [IsTate R] in
/-- The kernel of `(1 - a•u)ʰ` is the range of the complementary Riesz projector — the
`N(a)` of [Serre1962, §7 Prop. 12], in Buzzard's characterisation ("N = ker(ψ)",
[Buzzard2007, p. 23]). -/
theorem ker_one_sub_smul_pow_of_rieszProjection (hp : p * p = p) (_hup : u * p = p * u)
    (_hpw : p * w = w * p) (hnil : (1 - a • u) ^ h * (1 - p) = 0) (hw : (1 - a • u) * w = p)
    (huw : u * w = w * u) : ((1 - a • u) ^ h : c(I, R) →L[R] c(I, R)).ker = (1 - p).range := by
  have hcuw : Commute u w := huw
  have hbw : Commute (1 - a • u) w := (Commute.one_left w).sub_left (hcuw.smul_left a)
  have hph : p ^ h = p := pow_eq_of_rieszProjection hp hnil
  have hkey : w ^ h * (1 - a • u) ^ h = p := by
    rw [← (hbw.pow_pow h h).eq, ← hbw.mul_pow, hw, hph]
  apply le_antisymm
  · intro x hx
    have hx0 : ((1 - a • u) ^ h : c(I, R) →L[R] c(I, R)) x = 0 := hx
    have hpx : p x = 0 := by rw [← apply_of_mul_eq hkey x, hx0, map_zero]
    exact ⟨x, by simp [hpx]⟩
  · rintro _ ⟨y, rfl⟩
    exact apply_of_mul_eq hnil y

-- `_hpw` is unused here (see `ker_one_sub_smul_pow_of_rieszProjection`).
omit [IsTate R] in
/-- The range of `(1 - a•u)ʰ` is the range of the Riesz projector — the `F(a)` of
[Serre1962, §7 Prop. 12] ("F = Im(ψ)", [Buzzard2007, p. 23]). -/
theorem range_one_sub_smul_pow_of_rieszProjection (hp : p * p = p) (hup : u * p = p * u)
    (_hpw : p * w = w * p) (hnil : (1 - a • u) ^ h * (1 - p) = 0) (hw : (1 - a • u) * w = p)
    (huw : u * w = w * u) : ((1 - a • u) ^ h : c(I, R) →L[R] c(I, R)).range = p.range := by
  have hbw : Commute (1 - a • u) w := (Commute.one_left w).sub_left (Commute.smul_left huw a)
  have hbp : Commute (1 - a • u) p := (Commute.one_left p).sub_left (Commute.smul_left hup a)
  have hph : p ^ h = p := pow_eq_of_rieszProjection hp hnil
  have hkey : (1 - a • u) ^ h * w ^ h = p := by rw [← hbw.mul_pow, hw, hph]
  have hmulp : p * (1 - a • u) ^ h = (1 - a • u) ^ h := by
    rw [mul_sub, mul_one, sub_eq_zero] at hnil
    rw [← (hbp.pow_left h).eq, ← hnil]
  refine le_antisymm ?_ ?_ <;> rintro _ ⟨y, rfl⟩
  · exact ⟨_, apply_of_mul_eq hmulp y⟩
  · exact ⟨_, apply_of_mul_eq hkey y⟩

omit [DecidableEq I] [IsTate R] in
/-- The ranges of a continuous idempotent and of its complement are topological
complements; in particular both are closed, by `Submodule.IsTopCompl.isClosed`. -/
theorem isTopCompl_range_one_sub_range_of_isIdempotent (hp : p * p = p) :
    Submodule.IsTopCompl ((1 - p).range : Submodule R c(I, R)) p.range :=
  LinearMap.IsIdempotentElem.range_eq_ker_one_sub
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hp) ▸
    ContinuousLinearMap.IsIdempotentElem.isTopCompl (IsIdempotentElem.one_sub hp)

-- `_hh`, `_hh'` are unused: the proof runs at the common exponent `h + h'`, where no
-- positivity is needed.  They stay in the statement to match `exists_rieszProjection`.
omit [IsTate R] in
/-- Uniqueness of the Riesz decomposition [Serre1962, §7 p. 81: "son unicité est
immédiate"]: any projector with the defining properties (at any order) coincides
with `p`. -/
theorem rieszProjection_unique {p' w' : c(I, R) →L[R] c(I, R)} {h' : ℕ} (_hh : 1 ≤ h)
    (_hh' : 1 ≤ h') (hp : p * p = p) (hup : u * p = p * u) (hpw : p * w = w * p)
    (hnil : (1 - a • u) ^ h * (1 - p) = 0) (hw : (1 - a • u) * w = p) (huw : u * w = w * u)
    (hp' : p' * p' = p') (hup' : u * p' = p' * u) (hpw' : p' * w' = w' * p')
    (hnil' : (1 - a • u) ^ h' * (1 - p') = 0) (hw' : (1 - a • u) * w' = p')
    (huw' : u * w' = w' * u) : p' = p := by
  have hnilm : (1 - a • u) ^ (h + h') * (1 - p) = 0 := by
    rw [add_comm, pow_add, mul_assoc, hnil, mul_zero]
  have hnilm' : (1 - a • u) ^ (h + h') * (1 - p') = 0 := by
    rw [pow_add, mul_assoc, hnil', mul_zero]
  have hR := (range_one_sub_smul_pow_of_rieszProjection hp' hup' hpw' hnilm' hw' huw').symm.trans
    (range_one_sub_smul_pow_of_rieszProjection hp hup hpw hnilm hw huw)
  have hC := (ker_one_sub_smul_pow_of_rieszProjection hp' hup' hpw' hnilm' hw' huw').symm.trans
    (ker_one_sub_smul_pow_of_rieszProjection hp hup hpw hnilm hw huw)
  exact ContinuousLinearMap.IsIdempotentElem.ext hp' hp
    ⟨hR, ((LinearMap.IsIdempotentElem.ker_eq_range_one_sub
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hp')).trans hC).trans
      (LinearMap.IsIdempotentElem.ker_eq_range_one_sub
        (ContinuousLinearMap.IsIdempotentElem.toLinearMap hp)).symm⟩

/-- Blocks of a compactoid operator along an embedding of index types are compactoid. -/
theorem isCompactoid_of_comp_embedding {J : Type*} [DecidableEq J] (hu : IsCompactoid u) (e : J ↪ I)
    (v : c(J, R) →L[R] c(J, R)) (hv : ∀ j i, matrixCoeff v j i = matrixCoeff u (e j) (e i)) :
    IsCompactoid v := by
  refine squeeze_zero (rowNorm_nonneg v) (fun j ↦ ?_) (hu.comp e.injective.tendsto_cofinite)
  exact Real.iSup_le (fun i ↦ (congrArg (‖·‖) (hv j i)).trans_le
    (norm_matrixCoeff_le_rowNorm' u _ _)) (rowNorm_nonneg u _)

private def blockEquiv (P : I → Prop) [DecidablePred P] :
    Finset I ≃ Finset {i : I // P i} × Finset {i : I // ¬ P i} where
  toFun S := (S.subtype P, S.subtype fun i ↦ ¬ P i)
  invFun q := q.1.map (Function.Embedding.subtype P) ∪
      q.2.map (Function.Embedding.subtype fun i ↦ ¬ P i)
  left_inv _ := by simp only [Finset.subtype_map, Finset.filter_union_filter_not_eq]
  right_inv _ := by ext x <;> simp [x.2]

private theorem card_blockEquiv (P : I → Prop) [DecidablePred P] (S : Finset I) :
    (blockEquiv P S).1.card + (blockEquiv P S).2.card = S.card := by
  simpa [blockEquiv] using S.card_filter_add_card_filter_not P

-- The `P`-part of `S`, seen inside `↥S` or inside the subtype `{i // P i}`.
private def fiberEquiv (P : I → Prop) [DecidablePred P] (S : Finset I) :
    {x : {i : I // i ∈ S} // P x.1} ≃ {x : {i : I // P i} // x ∈ S.subtype P} where
  toFun x := ⟨⟨x.1.1, x.2⟩, Finset.mem_subtype.2 x.1.2⟩
  invFun y := ⟨⟨y.1.1, Finset.mem_subtype.1 y.2⟩, y.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def blockCard (P : I → Prop) (n : ℕ)
    (z : {z : Finset {i : I // P i} × Finset {i : I // ¬P i} // z.1.card + z.2.card = n}) :
    ↥(Finset.antidiagonal n) :=
  ⟨(z.1.1.card, z.1.2.card), Finset.mem_antidiagonal.mpr z.2⟩

private def blockCardFiberEquiv (P : I → Prop) [DecidablePred P] {n : ℕ}
    (p : ↥(Finset.antidiagonal n)) :
    ({S₁ : Finset {i : I // P i} // S₁.card = p.1.1} ×
      {S₂ : Finset {i : I // ¬ P i} // S₂.card = p.1.2}) ≃ ↥(blockCard P n ⁻¹' {p}) where
  toFun w := ⟨⟨(w.1.1, w.2.1), by simpa [w.1.2, w.2.2] using Finset.mem_antidiagonal.mp p.2⟩,
    Subtype.ext (Prod.ext w.1.2 w.2.2)⟩
  invFun z := (⟨z.1.1.1, congrArg (·.1.1) z.2⟩, ⟨z.1.1.2, congrArg (·.1.2) z.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl

private theorem det_toSquareBlockProp_eq_minor (Q : I → Prop) [DecidablePred Q] (S : Finset I)
    (v : c({i : I // Q i}, R) →L[R] c({i : I // Q i}, R))
    (hv : ∀ j i, matrixCoeff v j i = matrixCoeff u j.1 i.1) :
    ((Matrix.of fun j i : ↥S ↦ matrixCoeff u (j : I) (i : I)).toSquareBlockProp
      fun x : ↥S ↦ Q (x : I)).det = minor v (S.subtype Q) := by
  rw [minor, ← Matrix.det_submatrix_equiv_self (fiberEquiv Q S)]
  congr 1
  refine Matrix.ext fun j i ↦ ?_
  rw [Matrix.submatrix_apply, Matrix.of_apply, hv ((fiberEquiv Q S) j) ((fiberEquiv Q S) i)]
  rfl

private theorem minor_eq_mul_of_blockTriangular (P : I → Prop) [DecidablePred P]
    (htri : ∀ j i, P i → ¬P j → matrixCoeff u j i = 0)
    {u₁ : c({i : I // P i}, R) →L[R] c({i : I // P i}, R)}
    (h₁ : ∀ j i, matrixCoeff u₁ j i = matrixCoeff u j.1 i.1)
    {u₂ : c({i : I // ¬P i}, R) →L[R] c({i : I // ¬P i}, R)}
    (h₂ : ∀ j i, matrixCoeff u₂ j i = matrixCoeff u j.1 i.1) (S : Finset I) :
    minor u S = minor u₁ (blockEquiv P S).1 * minor u₂ (blockEquiv P S).2 := by
  have hblk := Matrix.twoBlockTriangular_det
    (Matrix.of fun j i : ↥S ↦ matrixCoeff u (j : I) (i : I)) (fun x : ↥S ↦ P (x : I))
    fun i hi j hj ↦ htri _ _ hj hi
  rw [minor, hblk, det_toSquareBlockProp_eq_minor P S u₁ h₁,
    det_toSquareBlockProp_eq_minor _ S u₂ h₂]
  rfl

private theorem tsum_minor_mul_minor_fiber (P : I → Prop) [DecidablePred P]
    {u₁ : c({i : I // P i}, R) →L[R] c({i : I // P i}, R)} (hu₁ : IsCompactoid u₁)
    {u₂ : c({i : I // ¬P i}, R) →L[R] c({i : I // ¬P i}, R)} (hu₂ : IsCompactoid u₂) (n : ℕ)
    (q : ↥(Finset.antidiagonal n)) :
    (∑' z : ↥(blockCard P n ⁻¹' {q}), minor u₁ (z : _).1.1.1 * minor u₂ (z : _).1.1.2)
      = (∑' S₁ : {S₁ : Finset {i : I // P i} // S₁.card = q.1.1}, minor u₁ (S₁ : Finset _))
        * ∑' S₂ : {S₂ : Finset {i : I // ¬P i} // S₂.card = q.1.2}, minor u₂ (S₂ : Finset _) := by
  have hstep : ∀ c : ({S₁ : Finset {i : I // P i} // S₁.card = q.1.1}
        × {S₂ : Finset {i : I // ¬P i} // S₂.card = q.1.2}),
      minor u₁ (blockCardFiberEquiv P q c).1.1.1 * minor u₂ (blockCardFiberEquiv P q c).1.1.2
        = minor u₁ (c.1 : Finset _) * minor u₂ (c.2 : Finset _) := fun _ ↦ rfl
  -- `Summable.congr` short-circuits a unifier blow-up on the two distinct index types
  have hprod : Summable fun x : ({S₁ : Finset {i : I // P i} // S₁.card = q.1.1}
      × {S₂ : Finset {i : I // ¬P i} // S₂.card = q.1.2}) =>
        minor u₁ (x.1 : Finset _) * minor u₂ (x.2 : Finset _) :=
    (PowerSeries.summable_mul_of_tendsto_cofinite
      (summable_minor u₁ hu₁ q.1.1).tendsto_cofinite_zero
      (summable_minor u₂ hu₂ q.1.2).tendsto_cofinite_zero).congr fun _ ↦ rfl
  rw [← Equiv.tsum_eq (blockCardFiberEquiv P q)
    (fun z : ↥(blockCard P n ⁻¹' {q}) ↦ minor u₁ (z : _).1.1.1 * minor u₂ (z : _).1.1.2),
    tsum_congr hstep]
  exact ((summable_minor u₁ hu₁ q.1.1).tsum_mul_tsum (summable_minor u₂ hu₂ q.1.2) hprod).symm

private theorem tsum_minor_eq_sum_antidiagonal (hu : IsCompactoid u) (P : I → Prop)
    [DecidablePred P] (htri : ∀ j i, P i → ¬P j → matrixCoeff u j i = 0)
    {u₁ : c({i : I // P i}, R) →L[R] c({i : I // P i}, R)}
    (h₁ : ∀ j i, matrixCoeff u₁ j i = matrixCoeff u j.1 i.1)
    {u₂ : c({i : I // ¬P i}, R) →L[R] c({i : I // ¬P i}, R)}
    (h₂ : ∀ j i, matrixCoeff u₂ j i = matrixCoeff u j.1 i.1) (n : ℕ) :
    (∑' S : {S : Finset I // S.card = n}, minor u (S : Finset I))
      = ∑ q ∈ Finset.antidiagonal n,
        (∑' S₁ : {S₁ : Finset {i : I // P i} // S₁.card = q.1}, minor u₁ (S₁ : Finset _))
          * ∑' S₂ : {S₂ : Finset {i : I // ¬P i} // S₂.card = q.2}, minor u₂ (S₂ : Finset _) := by
  have hu₁ : IsCompactoid u₁ :=
    isCompactoid_of_comp_embedding hu (Function.Embedding.subtype P) u₁ h₁
  have hu₂ : IsCompactoid u₂ :=
    isCompactoid_of_comp_embedding hu (Function.Embedding.subtype fun i ↦ ¬P i) u₂ h₂
  have hcard : ∀ z : Finset {i : I // P i} × Finset {i : I // ¬P i},
      z.1.card + z.2.card = ((blockEquiv P).symm z).card := by
    intro z
    have h := card_blockEquiv P ((blockEquiv P).symm z)
    rwa [Equiv.apply_symm_apply] at h
  let E : {z : Finset {i : I // P i} × Finset {i : I // ¬P i} // z.1.card + z.2.card = n}
      ≃ {S : Finset I // S.card = n} :=
    Equiv.subtypeEquiv (blockEquiv P).symm fun z ↦ by rw [hcard z]
  have hE : ∀ z, minor u ((E z : Finset I)) = minor u₁ (z : _).1.1 * minor u₂ (z : _).1.2 := by
    intro z
    have h := minor_eq_mul_of_blockTriangular P htri h₁ h₂ ((blockEquiv P).symm (z : _).1)
    rwa [Equiv.apply_symm_apply] at h
  have hsum : HasSum
      (fun z : {z : Finset {i : I // P i} × Finset {i : I // ¬P i} //
        z.1.card + z.2.card = n} => minor u₁ (z : _).1.1 * minor u₂ (z : _).1.2)
      (∑' S : {S : Finset I // S.card = n}, minor u (S : Finset I)) := by
    have h := (E.hasSum_iff (f := fun S : {S : Finset I // S.card = n} =>
      minor u (S : Finset I))).mpr (summable_minor u hu n).hasSum
    simpa only [Function.comp_def, hE] using h
  have hfib := hsum.tsum_fiberwise (blockCard P n)
  rw [funext (tsum_minor_mul_minor_fiber P hu₁ hu₂ n)] at hfib
  rw [hfib.unique (hasSum_fintype _),
    Finset.sum_coe_sort (Finset.antidiagonal n) (fun q : ℕ × ℕ ↦
      (∑' S₁ : {S₁ : Finset {i : I // P i} // S₁.card = q.1}, minor u₁ (S₁ : Finset _))
        * ∑' S₂ : {S₂ : Finset {i : I // ¬P i} // S₂.card = q.2}, minor u₂ (S₂ : Finset _))]

/-- Serre's Lemme 2 [Serre1962, §5 p. 77], local coordinate form: for a block-triangular
compactoid operator, the Fredholm determinant is the product of the determinants of the
two diagonal blocks.  (The Jacobs board has an equivalent statement; restated here to
keep this development file-independent.) -/
theorem charPowerSeries_blockTriangular {u : c(I, R) →L[R] c(I, R)} (hu : IsCompactoid u)
    (P : I → Prop) [DecidablePred P] (htri : ∀ j i, P i → ¬P j → matrixCoeff u j i = 0)
    (u₁ : c({i : I // P i}, R) →L[R] c({i : I // P i}, R))
    (h₁ : ∀ j i, matrixCoeff u₁ j i = matrixCoeff u j.1 i.1)
    (u₂ : c({i : I // ¬P i}, R) →L[R] c({i : I // ¬P i}, R))
    (h₂ : ∀ j i, matrixCoeff u₂ j i = matrixCoeff u j.1 i.1) :
    charPowerSeries u = charPowerSeries u₁ * charPowerSeries u₂ := by
  refine PowerSeries.ext fun n ↦ ?_
  simp only [PowerSeries.coeff_mul, charPowerSeries_coeff]
  rw [charCoeff, tsum_minor_eq_sum_antidiagonal hu P htri h₁ h₂ n, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq ↦ ?_
  rw [Finset.mem_antidiagonal] at hq
  rw [charCoeff, charCoeff, ← hq, pow_add]
  ring

end RieszDecomposition

section Field

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {I : Type*} [DecidableEq I]

/-- **A zero of the characteristic power series is an eigenvalue** [Serre1962, §7,
Props. 11–12; Buzzard2007, Prop. 3.2]: over a complete nonarchimedean field, if the
entire series `H = det(1 - Tu)` of a compactoid operator vanishes at `a`, then `a ≠ 0`
and `u` has an eigenvector of eigenvalue `a⁻¹`. -/
theorem exists_eigenvector_of_evalT_charPowerSeries_eq_zero (u : c(I, K) →L[K] c(I, K))
    (hu : IsCompactoid u) {a : K} (ha : PowerSeries.evalT a (charPowerSeries u) = 0) :
    a ≠ 0 ∧ ∃ x : c(I, K), x ≠ 0 ∧ u x = a⁻¹ • x := by
  obtain ⟨ha0, h, hh, h0, hne⟩ :=
    PowerSeries.exists_order_of_evalT_eq_zero (charPowerSeries_isEntire u hu) (by simp) ha
  obtain ⟨x, hx0, hx⟩ := exists_mem_ker_of_hasseDeriv_evalT hu hh h0 hne.isUnit
  have hax : x = a • u x := by simpa [sub_eq_zero] using hx
  exact ⟨ha0, x, hx0, (eq_inv_smul_iff₀ ha0).2 hax.symm⟩

/-- **Zeros of the characteristic power series are reciprocal eigenvalues** [Serre1962, §7,
Props. 11–12]: for a compactoid `u` over a complete nonarchimedean field, `H = det(1 - Tu)`
vanishes at a nonzero `a` exactly when `a⁻¹` is an eigenvalue of `u`.  The `←` direction is
Proposition 11 over a field: an eigenvector for `a⁻¹` is a nonzero kernel vector of `1 - a•u`. -/
theorem evalT_charPowerSeries_eq_zero_iff (u : c(I, K) →L[K] c(I, K)) (hu : IsCompactoid u) {a : K}
    (ha0 : a ≠ 0) :
    PowerSeries.evalT a (charPowerSeries u) = 0 ↔ ∃ x : c(I, K), x ≠ 0 ∧ u x = a⁻¹ • x := by
  refine ⟨fun ha ↦ (exists_eigenvector_of_evalT_charPowerSeries_eq_zero u hu ha).2, ?_⟩
  rintro ⟨x, hx0, hx⟩
  by_contra! hz
  -- the eigenvector `x` is a nonzero kernel vector, so `1 - a•u` cannot be invertible
  have hker : (1 - a • u) x = 0 := by simp [hx, smul_smul, mul_inv_cancel₀ ha0]
  exact hx0 <| ((isUnit_one_sub_smul_iff_isUnit_evalT hu a).2 hz.isUnit).smul_eq_zero.1 hker

/-- Transport of the eigenvector theorem along a continuous linear equivalence (covers
`IsONable` and `IsPotentiallyONable` Banach spaces via `charPowerSeries_conj`). -/
theorem exists_eigenvector_of_evalT_charPowerSeries_conj_eq_zero {E : Type*} [NormedAddCommGroup E]
    [Module K E] (φ : E ≃L[K] c(I, K)) (v : E →L[K] E)
    (hu : IsCompactoid (((φ : E →L[K] c(I, K)).comp v).comp (φ.symm : c(I, K) →L[K] E))) {a : K}
    (ha : PowerSeries.evalT a (charPowerSeries
      (((φ : E →L[K] c(I, K)).comp v).comp (φ.symm : c(I, K) →L[K] E))) = 0) :
    a ≠ 0 ∧ ∃ x : E, x ≠ 0 ∧ v x = a⁻¹ • x := by
  obtain ⟨ha0, y, hy0, hy⟩ := exists_eigenvector_of_evalT_charPowerSeries_eq_zero _ hu ha
  refine ⟨ha0, φ.symm y, fun hz ↦ hy0 (φ.symm.map_eq_zero_iff.1 hz), ?_⟩
  simpa using congrArg ⇑φ.symm hy

variable {u : c(I, K) →L[K] c(I, K)} {a : K} {h : ℕ}

private theorem mem_ker_of_commute {S T : c(I, K) →L[K] c(I, K)} (hST : Commute S T) {x : c(I, K)}
    (hx : x ∈ S.ker) : T x ∈ S.ker := by
  have hx0 : S x = 0 := hx
  show S (T x) = 0
  rw [apply_of_mul_eq hST.eq x, ← apply_of_mul_eq (rfl : T * S = _) x, hx0, map_zero]

private theorem apply_eq_self_of_mem_range {q : c(I, K) →L[K] c(I, K)} (hq : q * q = q)
    {x : c(I, K)} (hx : x ∈ q.range) : q x = x := by
  obtain ⟨z, rfl⟩ := hx
  exact apply_of_mul_eq hq z

private theorem coe_codRestrict_comp_apply {q : c(I, K) →L[K] c(I, K)} {N : Submodule K c(I, K)}
    (hfix : ∀ x ∈ N, q x = x) (hmem : ∀ x, q x ∈ N) {T : c(I, K) →L[K] c(I, K)}
    (hT : ∀ x ∈ N, T x ∈ N) (y : ↥N) :
    (((q.codRestrict N hmem).comp (T.comp N.subtypeL)) y : c(I, K)) = T (y : c(I, K)) :=
  hfix _ (hT _ y.2)

private theorem coe_pow_apply_of_coe_apply {N : Submodule K c(I, K)} {T : c(I, K) →L[K] c(I, K)}
    {v : ↥N →L[K] ↥N} (hv : ∀ y : ↥N, (v y : c(I, K)) = T (y : c(I, K))) (k : ℕ) (y : ↥N) :
    ((v ^ k) y : c(I, K)) = (T ^ k) (y : c(I, K)) := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    rfl
  | succ j ih =>
    have h1 : (v ^ (j + 1)) y = v ((v ^ j) y) := by
      rw [pow_succ']
      rfl
    rw [h1, hv, ih, pow_succ']
    rfl

private theorem finite_of_isCompletelyContinuous_one {M : Type*} [NormedAddCommGroup M] [Module K M]
    [IsBoundedSMul K M] [CompleteSpace M] (hcc : IsCompletelyContinuous (1 : M →L[K] M)) :
    Module.Finite K M := by
  obtain ⟨v, hv, hvnorm⟩ := hcc 1 one_pos
  obtain ⟨v', hv', -⟩ :=
    exists_inverse_of_norm_id_sub_lt_one v (by rwa [← ContinuousLinearMap.one_def])
  obtain ⟨Q, hQfg, hQle⟩ : IsFiniteRank (ContinuousLinearMap.id K M) := hv' ▸ hv.comp_right v'
  have hQtop : Q = ⊤ := top_le_iff.mp fun x _ ↦ hQle ⟨x, rfl⟩
  exact ⟨hQtop ▸ hQfg⟩

/-- The generalized eigenspace `N(a) = ker (1 - a•u)ʰ` at a zero of order `h` is
finite-dimensional [Serre1962, §7 Prop. 12: "la dimension de N(a) est finie"]: on it,
`1 - (a•u)` is nilpotent, so the identity is a polynomial in the compact operator
`(a•u)|_N`, hence compact; a finite-rank approximation within Neumann distance of the
identity is then invertible.  (Run directly on the closed subspace; the `HasPr` route of
`Pr.lean` is deliberately avoided — its model-space index must be a subset of the module,
which small `N` inside a large `c(I, K)` need not admit.) -/
theorem finite_ker_one_sub_smul_pow (hu : IsCompactoid u) (hh : 1 ≤ h)
    (h0 : ∀ s < h, PowerSeries.evalT a (PowerSeries.hasseDeriv s (charPowerSeries u)) = 0)
    (hunit : IsUnit (PowerSeries.evalT a (PowerSeries.hasseDeriv h (charPowerSeries u)))) :
    Module.Finite K (((1 - a • u) ^ h : c(I, K) →L[K] c(I, K)).ker) := by
  obtain ⟨p, w, hp, hup, huw, hpw, hnil, hw⟩ := exists_rieszProjection hu hh h0 hunit
  have hker := ker_one_sub_smul_pow_of_rieszProjection hp hup hpw hnil hw huw
  set N : Submodule K c(I, K) := ((1 - a • u) ^ h : c(I, K) →L[K] c(I, K)).ker
  have : CompleteSpace ↥N :=
    (((1 - a • u) ^ h : c(I, K) →L[K] c(I, K))).isClosed_ker.completeSpace_coe
  have : IsBoundedSMul K ↥N :=
    IsBoundedSMul.of_norm_smul_le fun r x ↦ norm_smul_le r (x : c(I, K))
  have hfix : ∀ x ∈ N, ((1 : c(I, K) →L[K] c(I, K)) - p) x = x := fun x hx ↦
    apply_eq_self_of_mem_range (IsIdempotentElem.one_sub hp) (hker ▸ hx)
  have hmemN : ∀ x : c(I, K), ((1 : c(I, K) →L[K] c(I, K)) - p) x ∈ N := fun x ↦ hker ▸ ⟨x, rfl⟩
  have hstab1 : ∀ x ∈ N, ((1 : c(I, K) →L[K] c(I, K)) - a • u) x ∈ N := fun x hx ↦
    mem_ker_of_commute ((Commute.refl _).pow_left h) hx
  have hstab2 : ∀ x ∈ N, (a • u) x ∈ N := fun x hx ↦
    mem_ker_of_commute (((Commute.one_left _).sub_left (Commute.refl _)).pow_left h) hx
  set ι : ↥N →L[K] c(I, K) := N.subtypeL
  set π : c(I, K) →L[K] ↥N := ((1 : c(I, K) →L[K] c(I, K)) - p).codRestrict N hmemN
  set nu : ↥N →L[K] ↥N := π.comp (((1 : c(I, K) →L[K] c(I, K)) - a • u).comp ι)
  set tau : ↥N →L[K] ↥N := π.comp ((a • u).comp ι)
  have hnucoe : ∀ y : ↥N,
      ((nu y : c(I, K))) = ((1 : c(I, K) →L[K] c(I, K)) - a • u) (y : c(I, K)) :=
    coe_codRestrict_comp_apply hfix hmemN hstab1
  have htaucoe : ∀ y : ↥N, ((tau y : c(I, K))) = (a • u) (y : c(I, K)) :=
    coe_codRestrict_comp_apply hfix hmemN hstab2
  have hsum1 : tau + nu = 1 := by
    refine ContinuousLinearMap.ext fun y ↦ Subtype.ext ?_
    show ((tau y : c(I, K)) + (nu y : c(I, K))) = (y : c(I, K))
    rw [htaucoe, hnucoe]
    simp [sub_apply, one_apply_eq_self]
  have hnuh : nu ^ h = 0 := by
    refine ContinuousLinearMap.ext fun y ↦ Subtype.ext ?_
    rw [coe_pow_apply_of_coe_apply hnucoe h y]
    exact y.2
  have hone : tau * (∑ k ∈ Finset.range h, nu ^ k) = 1 := by
    rw [eq_sub_of_add_eq hsum1, mul_neg_geom_sum, hnuh, sub_zero]
  have htaucc : IsCompletelyContinuous tau :=
    ((IsCompactoid.smul a hu).isCompletelyContinuous.comp_right ι).comp_left π
  refine finite_of_isCompletelyContinuous_one ?_
  have hcc := htaucc.comp_right (∑ k ∈ Finset.range h, nu ^ k)
  rwa [show tau.comp (∑ k ∈ Finset.range h, nu ^ k) = 1 from hone] at hcc

private theorem one_sub_X_smul_map_C_eq_aux {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (b : K) :
    1 - (Polynomial.X : Polynomial K) • A.map Polynomial.C
      = Matrix.scalar (Fin n) (1 - Polynomial.C b * Polynomial.X)
        - (Polynomial.X : Polynomial K) • (A - b • 1).map Polynomial.C :=
  Matrix.ext fun i j ↦ by
    by_cases hij : i = j
    · simp only [hij, Matrix.sub_apply, Matrix.one_apply_eq, Matrix.smul_apply, Matrix.map_apply,
        smul_eq_mul, Polynomial.X_mul_C, Matrix.scalar_apply, Matrix.diagonal_apply_eq, mul_one,
        map_sub]
      ring
    · simp only [Matrix.sub_apply, ne_eq, hij, not_false_eq_true, Matrix.one_apply_ne,
        Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Polynomial.X_mul_C, zero_sub,
        Matrix.scalar_apply, Matrix.diagonal_apply_ne, mul_zero, sub_zero]

/-- Determinant of a finite matrix with `1 - a•A` nilpotent: the characteristic power
series collapses to `(1 - a⁻¹T)ⁿ` (all eigenvalues of `A` are `a⁻¹`)
[Serre1962, §7 p. 81: "det(1 − tu_W) = (1 − ta⁻¹)^{dim W}"]. -/
theorem det_one_sub_X_smul_of_isNilpotent {n : ℕ} {A : Matrix (Fin n) (Fin n) K} (ha : a ≠ 0)
    (hnil : IsNilpotent ((1 : Matrix (Fin n) (Fin n) K) - a • A)) :
    Matrix.det (1 - (Polynomial.X : Polynomial K) • A.map Polynomial.C) =
      ((1 : Polynomial K) - Polynomial.C a⁻¹ * Polynomial.X) ^ n := by
  have hB : IsNilpotent (A - a⁻¹ • (1 : Matrix (Fin n) (Fin n) K)) := by
    have hBeq : A - a⁻¹ • (1 : Matrix (Fin n) (Fin n) K)
        = (-a⁻¹) • ((1 : Matrix (Fin n) (Fin n) K) - a • A) := by
      rw [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ ha]
      module
    exact hBeq ▸ hnil.smul (-a⁻¹)
  have hchar : ((Polynomial.X : Polynomial K)
      • (A - a⁻¹ • (1 : Matrix (Fin n) (Fin n) K)).map Polynomial.C).charpoly
      = (Polynomial.X : Polynomial (Polynomial K)) ^ n := by
    simpa [sub_eq_zero] using (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent
      ((hB.map (Polynomial.C (R := K)).mapMatrix).smul Polynomial.X)).eq_zero
  rw [one_sub_X_smul_map_C_eq_aux A a⁻¹, ← Matrix.eval_charpoly, hchar, Polynomial.eval_pow,
    Polynomial.eval_X]

section BlockCoordinates

variable {A B : Type*}

private def ofFun (f : A → K) (hf : Tendsto f cofinite (𝓝 0)) : c(A, K) :=
  ⟨⟨(f : Ix A → K), continuous_of_discreteTopology⟩, by rwa [Filter.cocompact_eq_cofinite]⟩

@[simp] private theorem ofFun_apply (f : A → K) (hf : Tendsto f cofinite (𝓝 0)) (x : A) :
    ofFun f hf x = f x := rfl

-- `Real.iSup_le` covers an empty index type, so no `Nonempty A` hypothesis is needed.
private theorem cSpace_norm_le {v : c(A, K)} {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖v x‖ ≤ C) : ‖v‖ ≤ C :=
  (cSpace.norm_eq_iSup v).trans_le (Real.iSup_le hb hC)

-- Restriction of a model-space vector along an injective reindexing map: the continuous-linear
-- upgrade of `ZeroAtInftyContinuousMap.compLinearMap`, transported across the `cSpace`/`Ix` seam.
private def pullCLM (e : A → B) (he : Function.Injective e) : c(B, K) →L[K] c(A, K) where
  toFun f := ofFun (fun x ↦ f (e x)) ((cSpace.tendsto_cofinite f).comp he.tendsto_cofinite)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by
    refine (LipschitzWith.mk_one fun f g ↦ ?_).continuous
    rw [dist_eq_norm, dist_eq_norm]
    exact cSpace_norm_le (norm_nonneg _) fun x ↦ cSpace.norm_apply_le (f - g) (e x)

@[simp] private theorem pullCLM_apply (e : A → B) (he : Function.Injective e) (f : c(B, K))
    (x : A) : pullCLM e he f x = f (e x) := rfl

private theorem pullCLM_single [DecidableEq A] [DecidableEq B] {e : A → B}
    (he : Function.Injective e) (x : A) :
    pullCLM e he (cSpace.single (e x) (1 : K)) = cSpace.single x 1 := by
  refine DFunLike.ext _ _ fun y ↦ ?_
  rcases eq_or_ne y x with rfl | hne <;> simp [cSpace.single_apply_of_ne, he.eq_iff, *]

private def sumElimCLM : c(A, K) × c(B, K) →L[K] c(A ⊕ B, K) where
  toFun fg := ofFun (Sum.elim (⇑fg.1) ⇑fg.2) fun _ hU ↦ Set.finite_preimage_inl_and_inr.mp
    ⟨cSpace.tendsto_cofinite fg.1 hU, cSpace.tendsto_cofinite fg.2 hU⟩
  map_add' _ _ := DFunLike.ext _ _ <| by rintro (x | y) <;> rfl
  map_smul' _ _ := DFunLike.ext _ _ <| by rintro (x | y) <;> rfl
  cont := by
    refine (LipschitzWith.of_dist_le_mul (K := 1) fun x y ↦ ?_).continuous
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    refine cSpace_norm_le (norm_nonneg _) fun z ↦ ?_
    rcases z with z | z
    · exact (cSpace.norm_apply_le (x.1 - y.1) z).trans (norm_fst_le (x - y))
    · exact (cSpace.norm_apply_le (x.2 - y.2) z).trans (norm_snd_le (x - y))

private def sumCLE : (c(A, K) × c(B, K)) ≃L[K] c(A ⊕ B, K) :=
  ContinuousLinearEquiv.equivOfInverse sumElimCLM
    ((pullCLM Sum.inl Sum.inl_injective).prod (pullCLM Sum.inr Sum.inr_injective))
    (fun _ ↦ rfl) fun _ ↦ DFunLike.ext _ _ <| by rintro (x | y) <;> rfl

@[simp] private theorem sumCLE_apply_inl (fg : c(A, K) × c(B, K)) (x : A) :
    sumCLE fg (Sum.inl x) = fg.1 x := rfl

@[simp] private theorem sumCLE_apply_inr (fg : c(A, K) × c(B, K)) (y : B) :
    sumCLE fg (Sum.inr y) = fg.2 y := rfl

private theorem sumCLE_symm_apply (f : c(A ⊕ B, K)) :
    sumCLE.symm f = (pullCLM Sum.inl Sum.inl_injective f, pullCLM Sum.inr Sum.inr_injective f) :=
  rfl

private def reindexCLE (e : A ≃ B) : c(A, K) ≃L[K] c(B, K) :=
  ContinuousLinearEquiv.equivOfInverse (pullCLM e.symm e.symm.injective) (pullCLM e e.injective)
    (fun _ ↦ DFunLike.ext _ _ fun _ ↦ by simp) fun _ ↦ DFunLike.ext _ _ fun _ ↦ by simp

private theorem reindexCLE_symm_apply (e : A ≃ B) (f : c(B, K)) :
    (reindexCLE e).symm f = pullCLM e e.injective f := rfl

@[simp] private theorem reindexCLE_apply' (e : A ≃ B) (f : c(A, K)) (y : B) :
    reindexCLE e f y = f (e.symm y) := rfl

variable [DecidableEq A] [DecidableEq B]

private theorem sumCLE_inl_single (x : A) :
    (sumCLE : (c(A, K) × c(B, K)) ≃L[K] c(A ⊕ B, K)) (cSpace.single x 1, 0)
      = cSpace.single (Sum.inl x) 1 := by
  rw [← ContinuousLinearEquiv.eq_symm_apply, sumCLE_symm_apply]
  refine Prod.ext (pullCLM_single Sum.inl_injective x).symm <| DFunLike.ext _ _ fun _ ↦ ?_
  rw [pullCLM_apply, cSpace.single_apply_of_ne Sum.inr_ne_inl]
  rfl

private theorem sumCLE_inr_single (y : B) :
    (sumCLE : (c(A, K) × c(B, K)) ≃L[K] c(A ⊕ B, K)) (0, cSpace.single y 1)
      = cSpace.single (Sum.inr y) 1 := by
  rw [← ContinuousLinearEquiv.eq_symm_apply, sumCLE_symm_apply]
  refine Prod.ext (DFunLike.ext _ _ fun _ ↦ ?_) (pullCLM_single Sum.inr_injective y).symm
  rw [pullCLM_apply, cSpace.single_apply_of_ne Sum.inl_ne_inr]
  rfl

private theorem reindexCLE_symm_single (e : A ≃ B) (y : B) :
    (reindexCLE e).symm (cSpace.single y (1 : K)) = cSpace.single (e.symm y) 1 := by
  simpa [reindexCLE_symm_apply] using pullCLM_single e.injective (e.symm y)

private def finLE (A : Type*) [Finite A] : (A → K) ≃ₗ[K] c(A, K) where
  toFun f := ofFun f (by simp)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun g := ⇑g
  left_inv _ := rfl
  right_inv _ := rfl

end BlockCoordinates

section Conjugation

variable {E E' : Type*} [NormedAddCommGroup E] [Module K E] [IsBoundedSMul K E]
  [NormedAddCommGroup E'] [Module K E'] [IsBoundedSMul K E']

-- Bundled as a `≃+*` so that `map_pow` and `IsUnit.map` transport nilpotency and invertibility.
-- Not `ContinuousLinearEquiv.arrowCongr e e`: that forces `IsBoundedSMul`, absent on `↥N`.
private def conjRingEquiv (e : E ≃L[K] E') : (E →L[K] E) ≃+* (E' →L[K] E') where
  toFun T := ((e : E →L[K] E').comp T).comp (e.symm : E' →L[K] E)
  invFun S := ((e.symm : E' →L[K] E).comp S).comp (e : E →L[K] E')
  left_inv _ := ContinuousLinearMap.ext fun x ↦ by simp
  right_inv _ := ContinuousLinearMap.ext fun x ↦ by simp
  map_mul' _ _ := ContinuousLinearMap.ext fun x ↦ by simp
  map_add' _ _ := ContinuousLinearMap.ext fun x ↦ by simp

@[simp] private theorem conjRingEquiv_apply (e : E ≃L[K] E') (T : E →L[K] E) (x : E') :
    conjRingEquiv e T x = e (T (e.symm x)) := rfl

private theorem conjRingEquiv_eq_comp (e : E ≃L[K] E') (T : E →L[K] E) :
    conjRingEquiv e T = ((e : E →L[K] E').comp T).comp (e.symm : E' →L[K] E) := rfl

private theorem conjRingEquiv_one_sub_smul (e : E ≃L[K] E') (a : K) (T : E →L[K] E) :
    conjRingEquiv e ((1 : E →L[K] E) - a • T) = 1 - a • conjRingEquiv e T :=
  ContinuousLinearMap.ext fun _ ↦ by simp

-- `charPowerSeries_conj` is stated on the unbundled `.comp` form, so every use against a
-- `conjRingEquiv` otherwise pays an extra `conjRingEquiv_eq_comp` rewrite to unfold it back.
private theorem charPowerSeries_conjRingEquiv {J : Type*} [DecidableEq J]
    (φ : c(I, K) ≃L[K] c(J, K)) (v : c(I, K) →L[K] c(I, K)) (hv : IsCompactoid v) :
    charPowerSeries (conjRingEquiv φ v) = charPowerSeries v := by
  rw [conjRingEquiv_eq_comp, charPowerSeries_conj φ v hv]

end Conjugation

section FiniteBlock

variable {A : Type*} [Fintype A] [DecidableEq A]

private theorem matrixCoeff_mul_fintype (v v' : c(A, K) →L[K] c(A, K)) (j i : A) :
    matrixCoeff (v * v') j i = ∑ k, matrixCoeff v j k * matrixCoeff v' k i :=
  matrixCoeff_mul_of_rows v v' Finset.univ (by simp) j i

private theorem matrixCoeff_pow (v : c(A, K) →L[K] c(A, K)) (n : ℕ) (j i : A) :
    matrixCoeff (v ^ n) j i = ((Matrix.of fun j i ↦ matrixCoeff v j i) ^ n) j i := by
  induction n generalizing j i with
  | zero => simp [matrixCoeff_one, Matrix.one_apply]
  | succ m ih => simp [pow_succ, matrixCoeff_mul_fintype, Matrix.mul_apply, ih]

private theorem isNilpotent_one_sub_smul_matrix {v : c(A, K) →L[K] c(A, K)} {n : ℕ}
    (hv : ((1 : c(A, K) →L[K] c(A, K)) - a • v) ^ n = 0) :
    IsNilpotent ((1 : Matrix A A K) - a • Matrix.of fun j i ↦ matrixCoeff v j i) := by
  have hM : ((1 : Matrix A A K) - a • Matrix.of fun j i ↦ matrixCoeff v j i)
      = Matrix.of fun j i ↦ matrixCoeff ((1 : c(A, K) →L[K] c(A, K)) - a • v) j i :=
    Matrix.ext fun j i ↦ by
      simp only [Matrix.smul_of, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply,
        Pi.smul_apply, smul_eq_mul, matrixCoeff_sub, matrixCoeff_one, matrixCoeff_smul]
  refine ⟨n, Matrix.ext fun j i ↦ ?_⟩
  rw [hM, ← matrixCoeff_pow, hv]
  rfl

-- The `N(a)`-block of [Serre1962, §7 p. 81].
private theorem charPowerSeries_eq_pow_of_isNilpotent {d : ℕ} {v : c(Fin d, K) →L[K] c(Fin d, K)}
    (ha : a ≠ 0) {n : ℕ} (hv : ((1 : c(Fin d, K) →L[K] c(Fin d, K)) - a • v) ^ n = 0) :
    charPowerSeries v = (1 - PowerSeries.C a⁻¹ * PowerSeries.X) ^ d := by
  have hdet := det_one_sub_X_smul_of_isNilpotent ha (isNilpotent_one_sub_smul_matrix hv)
  set eu : ↥(Finset.univ : Finset (Fin d)) ≃ Fin d :=
    Equiv.subtypeUnivEquiv Finset.mem_univ with heu
  have heq : (1 : Matrix ↥(Finset.univ : Finset (Fin d)) ↥(Finset.univ : Finset (Fin d))
        (Polynomial K)) - (Polynomial.X : Polynomial K) •
        (Matrix.of fun j i : ↥(Finset.univ : Finset (Fin d)) ↦
          Polynomial.C (matrixCoeff v (j : Fin d) (i : Fin d)))
      = ((1 : Matrix (Fin d) (Fin d) (Polynomial K)) - (Polynomial.X : Polynomial K) •
          (Matrix.of fun j i : Fin d ↦ matrixCoeff v j i).map Polynomial.C).submatrix eu eu := by
    refine Matrix.ext fun j i ↦ ?_
    simp only [heu, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply,
      Matrix.map_apply, smul_eq_mul, Matrix.one_apply, Equiv.subtypeUnivEquiv_apply,
      Subtype.ext_iff]
  refine PowerSeries.ext fun k ↦ ?_
  rw [charPowerSeries_coeff,
    charCoeff_eq_det_coeff v Finset.univ (fun j hj ↦ absurd (Finset.mem_univ j) hj) k, heq,
    Matrix.det_submatrix_equiv_self eu, hdet, ← Polynomial.coeff_coe]
  simp

end FiniteBlock

private theorem map_mem_ker_pow_one_sub_smul
    (z : ↥(((1 - a • u) ^ h : c(I, K) →L[K] c(I, K)).ker)) :
    u (z : c(I, K)) ∈ ((1 - a • u) ^ h : c(I, K) →L[K] c(I, K)).ker :=
  mem_ker_of_commute
    (((Commute.one_left u).sub_left ((Commute.refl u).smul_left a)).pow_left h) z.2

private theorem map_mem_range_of_commute {p T : c(I, K) →L[K] c(I, K)} (hT : T * p = p * T)
    (z : ↥(p.range)) : T (z : c(I, K)) ∈ p.range := by
  obtain ⟨y, hy⟩ := z.2
  refine ⟨T y, ?_⟩
  show p (T y) = T (z : c(I, K))
  rw [← hy]
  exact (apply_of_mul_eq hT y).symm

private theorem pow_one_sub_smul_codRestrict_eq_zero {N : Submodule K c(I, K)}
    (hstab : ∀ z : ↥N, u (z : c(I, K)) ∈ N)
    (hmem : ∀ z : ↥N, ((1 - a • u) ^ h : c(I, K) →L[K] c(I, K)) (z : c(I, K)) = 0) :
    ((1 : ↥N →L[K] ↥N) - a • (u.comp N.subtypeL).codRestrict N hstab) ^ h = 0 := by
  set uN : ↥N →L[K] ↥N := (u.comp N.subtypeL).codRestrict N hstab
  have hcoe : ∀ y : ↥N, ((((1 : ↥N →L[K] ↥N) - a • uN) y : ↥N) : c(I, K))
      = ((1 : c(I, K) →L[K] c(I, K)) - a • u) (y : c(I, K)) := by
    intro y
    show ((y : c(I, K)) - a • u (y : c(I, K))) = _
    rw [sub_apply, one_apply_eq_self, smul_apply]
  refine ContinuousLinearMap.ext fun z ↦ Subtype.ext ?_
  show ((((1 : ↥N →L[K] ↥N) - a • uN) ^ h) z : c(I, K)) = 0
  rw [coe_pow_apply_of_coe_apply hcoe h z]
  exact hmem z

private theorem isUnit_one_sub_smul_codRestrict_range {p w : c(I, K) →L[K] c(I, K)}
    (hp : p * p = p) (huw : u * w = w * u) (hw : (1 - a • u) * w = p)
    (hstab : ∀ z : ↥(p.range), u (z : c(I, K)) ∈ p.range)
    (hstabw : ∀ z : ↥(p.range), w (z : c(I, K)) ∈ p.range) :
    IsUnit ((1 : ↥(p.range) →L[K] ↥(p.range))
      - a • (u.comp (p.range).subtypeL).codRestrict p.range hstab) := by
  have hfix : ∀ z : ↥(p.range), p (z : c(I, K)) = (z : c(I, K)) := by
    intro z
    obtain ⟨y, hy⟩ := z.2
    rw [← hy]
    exact apply_of_mul_eq hp y
  have hwb : w * (1 - a • u) = p := by
    have hcuw : Commute u w := huw
    rw [← ((Commute.one_left w).sub_left (hcuw.smul_left a)).eq, hw]
  refine ⟨⟨(1 : ↥(p.range) →L[K] ↥(p.range))
      - a • (u.comp (p.range).subtypeL).codRestrict p.range hstab,
    (w.comp (p.range).subtypeL).codRestrict p.range hstabw, ?_, ?_⟩, rfl⟩
  · refine ContinuousLinearMap.ext fun z ↦ Subtype.ext ?_
    show ((1 : c(I, K) →L[K] c(I, K)) - a • u) (w (z : c(I, K))) = (z : c(I, K))
    rw [apply_of_mul_eq hw (z : c(I, K))]
    exact hfix z
  · refine ContinuousLinearMap.ext fun z ↦ Subtype.ext ?_
    show w (((1 : c(I, K) →L[K] c(I, K)) - a • u) (z : c(I, K))) = (z : c(I, K))
    rw [apply_of_mul_eq hwb (z : c(I, K))]
    exact hfix z

private theorem matrixCoeff_conjRingEquiv_reindexCLE {A B : Type*} [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (v : c(A, K) →L[K] c(A, K)) (j i : B) :
    matrixCoeff (conjRingEquiv (reindexCLE e) v) j i = matrixCoeff v (e.symm j) (e.symm i) := by
  show (reindexCLE e) (v ((reindexCLE e).symm (cSpace.single i 1))) j = _
  rw [reindexCLE_symm_single]
  rfl

private theorem exists_conj_blockTriangular_of_isTopCompl {N F : Submodule K c(I, K)}
    [IsBoundedSMul K ↥N] [IsBoundedSMul K ↥F]
    {A B : Type*} [DecidableEq A] [DecidableEq B] {eN : ↥N ≃L[K] c(A, K)} {eF : ↥F ≃L[K] c(B, K)}
    {uN : ↥N →L[K] ↥N} {uF : ↥F →L[K] ↥F} {v : c(A, K) →L[K] c(A, K)}
    {v' : c(B, K) →L[K] c(B, K)} (hu : IsCompactoid u) (hcompl : Submodule.IsTopCompl N F)
    (hv : v = conjRingEquiv eN uN) (hv' : v' = conjRingEquiv eF uF)
    (huN : ∀ z : ↥N, (uN z : c(I, K)) = u (z : c(I, K)))
    (huF : ∀ z : ↥F, (uF z : c(I, K)) = u (z : c(I, K))) :
    ∃ u' : c(A ⊕ B, K) →L[K] c(A ⊕ B, K), charPowerSeries u' = charPowerSeries u ∧
      IsCompactoid u' ∧
      (∀ x y : A, matrixCoeff u' (Sum.inl y) (Sum.inl x) = matrixCoeff v y x) ∧
      (∀ x y : B, matrixCoeff u' (Sum.inr y) (Sum.inr x) = matrixCoeff v' y x) ∧
      ∀ (x : A) (y : B), matrixCoeff u' (Sum.inr y) (Sum.inl x) = 0 := by
  subst hv
  subst hv'
  set Φ : c(A ⊕ B, K) ≃L[K] c(I, K) :=
    (sumCLE.symm.trans (eN.symm.prodCongr eF.symm)).trans
      (Submodule.prodEquivOfIsTopCompl N F hcompl)
  have hΦ_sum : ∀ (x : c(A, K)) (y : c(B, K)),
      Φ (sumCLE (x, y)) = ((eN.symm x : ↥N) : c(I, K)) + ((eF.symm y : ↥F) : c(I, K)) := by
    intro x y
    show Submodule.prodEquivOfIsTopCompl N F hcompl
      ((eN.symm.prodCongr eF.symm) (sumCLE.symm (sumCLE (x, y)))) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact Submodule.prodEquivOfIsTopCompl_apply _ _
  have hΦ_inl : ∀ x : A,
      Φ (cSpace.single (Sum.inl x) 1) = ((eN.symm (cSpace.single x 1) : ↥N) : c(I, K)) := by
    intro x
    rw [← sumCLE_inl_single (B := B) x, hΦ_sum]
    simp
  have hΦ_inr : ∀ y : B,
      Φ (cSpace.single (Sum.inr y) 1) = ((eF.symm (cSpace.single y 1) : ↥F) : c(I, K)) := by
    intro y
    rw [← sumCLE_inr_single (A := A) y, hΦ_sum]
    simp
  have hΦsymm_N : ∀ z : ↥N, Φ.symm (z : c(I, K)) = sumCLE (eN z, 0) := by
    intro z
    rw [ContinuousLinearEquiv.symm_apply_eq, hΦ_sum]
    simp
  have hΦsymm_F : ∀ z : ↥F, Φ.symm (z : c(I, K)) = sumCLE (0, eF z) := by
    intro z
    rw [ContinuousLinearEquiv.symm_apply_eq, hΦ_sum]
    simp
  refine ⟨((Φ.symm : c(I, K) →L[K] c(A ⊕ B, K)).comp u).comp
    (Φ : c(A ⊕ B, K) →L[K] c(I, K)), ?_, ?_, ?_, ?_, ?_⟩
  · have hc := charPowerSeries_conj Φ.symm u hu
    rwa [ContinuousLinearEquiv.symm_symm] at hc
  · rw [ContinuousLinearMap.comp_assoc]
    exact (hu.comp_right _).comp_left _
  · intro x y
    show Φ.symm (u (Φ (cSpace.single (Sum.inl x) 1))) (Sum.inl y) = _
    rw [hΦ_inl x, ← huN (eN.symm (cSpace.single x 1)), hΦsymm_N, sumCLE_apply_inl]
    rfl
  · intro x y
    show Φ.symm (u (Φ (cSpace.single (Sum.inr x) 1))) (Sum.inr y) = _
    rw [hΦ_inr x, ← huF (eF.symm (cSpace.single x 1)), hΦsymm_F, sumCLE_apply_inr]
    rfl
  · intro x y
    show Φ.symm (u (Φ (cSpace.single (Sum.inl x) 1))) (Sum.inr y) = 0
    rw [hΦ_inl x, ← huN (eN.symm (cSpace.single x 1)), hΦsymm_N, sumCLE_apply_inr]
    rfl

private theorem charPowerSeries_eq_mul_of_blockTriangular_sum {A B : Type*} [DecidableEq A]
    [DecidableEq B] {u' : c(A ⊕ B, K) →L[K] c(A ⊕ B, K)} {v : c(A, K) →L[K] c(A, K)}
    {v' : c(B, K) →L[K] c(B, K)} (hu' : IsCompactoid u')
    (hv : ∀ x y : A, matrixCoeff u' (Sum.inl y) (Sum.inl x) = matrixCoeff v y x)
    (hv' : ∀ x y : B, matrixCoeff u' (Sum.inr y) (Sum.inr x) = matrixCoeff v' y x)
    (htri : ∀ (x : A) (y : B), matrixCoeff u' (Sum.inr y) (Sum.inl x) = 0) :
    charPowerSeries u' = charPowerSeries v * charPowerSeries v' := by
  set eL : A ≃ {z : A ⊕ B // z.isLeft = true} := Equiv.sumIsLeft.symm
  set eR : B ≃ {z : A ⊕ B // ¬ (z.isLeft = true)} :=
    Equiv.sumIsRight.symm.trans <| Equiv.subtypeEquivRight fun _ ↦ by simp
  have h₁ : ∀ (j i : {z : A ⊕ B // z.isLeft = true}),
      matrixCoeff (conjRingEquiv (reindexCLE eL) v) j i
        = matrixCoeff u' (j : A ⊕ B) (i : A ⊕ B) := by
    intro j i
    have hi : (i : A ⊕ B) = Sum.inl (eL.symm i) :=
      (congrArg Subtype.val (eL.apply_symm_apply i)).symm
    have hj : (j : A ⊕ B) = Sum.inl (eL.symm j) :=
      (congrArg Subtype.val (eL.apply_symm_apply j)).symm
    rw [matrixCoeff_conjRingEquiv_reindexCLE, hi, hj, hv]
  have h₂ : ∀ (j i : {z : A ⊕ B // ¬ (z.isLeft = true)}),
      matrixCoeff (conjRingEquiv (reindexCLE eR) v') j i
        = matrixCoeff u' (j : A ⊕ B) (i : A ⊕ B) := by
    intro j i
    have hi : (i : A ⊕ B) = Sum.inr (eR.symm i) :=
      (congrArg Subtype.val (eR.apply_symm_apply i)).symm
    have hj : (j : A ⊕ B) = Sum.inr (eR.symm j) :=
      (congrArg Subtype.val (eR.apply_symm_apply j)).symm
    rw [matrixCoeff_conjRingEquiv_reindexCLE, hi, hj, hv']
  have htri' : ∀ (j i : A ⊕ B), i.isLeft = true → ¬ (j.isLeft = true) →
      matrixCoeff u' j i = 0 := by
    rintro (jx | jy) (ix | iy) hi hj
    · exact absurd rfl hj
    · exact absurd rfl hj
    · exact htri ix jy
    · exact absurd hi (by simp)
  have hvc : IsCompactoid v :=
    isCompactoid_of_comp_embedding hu' ⟨Sum.inl, Sum.inl_injective⟩ v fun j i ↦ (hv i j).symm
  have hv'c : IsCompactoid v' :=
    isCompactoid_of_comp_embedding hu' ⟨Sum.inr, Sum.inr_injective⟩ v' fun j i ↦ (hv' i j).symm
  rw [charPowerSeries_blockTriangular hu' (fun z : A ⊕ B ↦ z.isLeft = true) htri'
      (conjRingEquiv (reindexCLE eL) v) h₁ (conjRingEquiv (reindexCLE eR) v') h₂,
    charPowerSeries_conjRingEquiv (reindexCLE eL) v hvc,
    charPowerSeries_conjRingEquiv (reindexCLE eR) v' hv'c]

/-- The factorisation `H = (1 - a⁻¹T)^d · H'` with `H'(a) ≠ 0`, where
`d = dim N(a)` — obtained by conjugating the Riesz decomposition into block-diagonal
coordinates (the finite block from a basis of `N(a)`; the complement via
`isPotentiallyONable_of_uniformizer`, whence the discreteness hypothesis `hd`) and
applying the block factorisation of the determinant [Serre1962, §7 p. 81:
"det(1−tu) = (1−ta⁻¹)^{dim N} H′(t)"]. -/
theorem charPowerSeries_eq_pow_mul_of_riesz
    (hd : ∃ π : K, 0 < ‖π‖ ∧ ‖π‖ < 1 ∧ ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖π‖) (hu : IsCompactoid u)
    (hh : 1 ≤ h)
    (h0 : ∀ s < h, PowerSeries.evalT a (PowerSeries.hasseDeriv s (charPowerSeries u)) = 0)
    (hunit : IsUnit (PowerSeries.evalT a (PowerSeries.hasseDeriv h (charPowerSeries u)))) :
    ∃ H' : PowerSeries K, (∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c H') ∧
      PowerSeries.evalT a H' ≠ 0 ∧ charPowerSeries u = (1 - PowerSeries.C a⁻¹ * PowerSeries.X) ^
        (Module.finrank K (((1 - a • u) ^ h : c(I, K) →L[K] c(I, K)).ker)) * H' := by
  classical
  let : NormedSpace K c(I, K) :=
    { (inferInstance : Module K c(I, K)) with norm_smul_le := fun r x ↦ norm_smul_le r x }
  have hcoeff : PowerSeries.coeff 0 (charPowerSeries u) = 1 := by
    rw [charPowerSeries_coeff, charCoeff_zero]
  have hH0 : PowerSeries.evalT a (charPowerSeries u) = 0 := by
    have h00 := h0 0 (by omega)
    rwa [PowerSeries.hasseDeriv_zero] at h00
  obtain ⟨ha0, -⟩ :=
    PowerSeries.exists_order_of_evalT_eq_zero (charPowerSeries_isEntire u hu) hcoeff hH0
  obtain ⟨p, w, hp, hup, huw, hpw, hnil, hw⟩ := exists_rieszProjection hu hh h0 hunit
  have hkerN := ker_one_sub_smul_pow_of_rieszProjection hp hup hpw hnil hw huw
  set N : Submodule K c(I, K) := ((1 - a • u) ^ h : c(I, K) →L[K] c(I, K)).ker
  have : Module.Finite K ↥N := finite_ker_one_sub_smul_pow hu hh h0 hunit
  have : FiniteDimensional K ↥N := inferInstance
  have hmemN : ∀ z : ↥N, ((1 - a • u) ^ h : c(I, K) →L[K] c(I, K)) (z : c(I, K)) = 0 :=
    fun z ↦ z.2
  have hstabN : ∀ z : ↥N, u (z : c(I, K)) ∈ N := map_mem_ker_pow_one_sub_smul
  clear_value N
  have hcompl : Submodule.IsTopCompl N p.range := by
    rw [hkerN]
    exact isTopCompl_range_one_sub_range_of_isIdempotent hp
  have : CompleteSpace ↥(p.range) := hcompl.symm.isClosed.completeSpace_coe
  obtain ⟨s, ⟨eF⟩⟩ := isPotentiallyONable_of_uniformizer K hd ↥(p.range)
  have hstabF : ∀ z : ↥(p.range), u (z : c(I, K)) ∈ p.range := map_mem_range_of_commute hup
  have hstabwF : ∀ z : ↥(p.range), w (z : c(I, K)) ∈ p.range := map_mem_range_of_commute hpw.symm
  set d : ℕ := Module.finrank K ↥N
  set eN : ↥N ≃L[K] c(Fin d, K) :=
    ((Module.finBasis K ↥N).equivFun.trans (finLE (Fin d))).toContinuousLinearEquiv
  set uN : ↥N →L[K] ↥N := (u.comp N.subtypeL).codRestrict N hstabN
  set uF : ↥(p.range) →L[K] ↥(p.range) :=
    (u.comp (p.range).subtypeL).codRestrict p.range hstabF
  set v : c(Fin d, K) →L[K] c(Fin d, K) := conjRingEquiv eN uN with hvdef
  set vF : c(↥s, K) →L[K] c(↥s, K) := conjRingEquiv eF uF with hvFdef
  obtain ⟨u', hconj, hu'c, hcore1, hcore2, htri⟩ :=
    exists_conj_blockTriangular_of_isTopCompl hu hcompl hvdef hvFdef (fun _ ↦ rfl) fun _ ↦ rfl
  have hnilv : ((1 : c(Fin d, K) →L[K] c(Fin d, K)) - a • v) ^ h = 0 := by
    have hnilN : ((1 : ↥N →L[K] ↥N) - a • uN) ^ h = 0 :=
      pow_one_sub_smul_codRestrict_eq_zero hstabN hmemN
    have hmap := congrArg (conjRingEquiv eN) hnilN
    rwa [map_pow, conjRingEquiv_one_sub_smul, ← hvdef, map_zero] at hmap
  have hunitvF : IsUnit ((1 : c(↥s, K) →L[K] c(↥s, K)) - a • vF) := by
    have hunitF : IsUnit ((1 : ↥(p.range) →L[K] ↥(p.range)) - a • uF) :=
      isUnit_one_sub_smul_codRestrict_range hp huw hw hstabF hstabwF
    have h1 := hunitF.map (conjRingEquiv eF)
    rwa [conjRingEquiv_one_sub_smul, ← hvFdef] at h1
  have hcptF : IsCompactoid vF :=
    isCompactoid_of_comp_embedding hu'c ⟨Sum.inr, Sum.inr_injective⟩ vF fun j i ↦ (hcore2 i j).symm
  refine ⟨charPowerSeries vF, charPowerSeries_isEntire vF hcptF, ?_, ?_⟩
  · exact ((isUnit_one_sub_smul_iff_isUnit_evalT hcptF a).mp hunitvF).ne_zero
  · rw [← hconj, charPowerSeries_eq_mul_of_blockTriangular_sum hu'c hcore1 hcore2 htri,
      charPowerSeries_eq_pow_of_isNilpotent ha0 hnilv]

/-- **`dim N(a) = h`** [Serre1962, §7 Prop. 12]: the dimension of the generalized
eigenspace equals the order of the zero.  (Discreteness hypothesis `hd` as in
`isPotentiallyONable_of_uniformizer`.) -/
theorem finrank_ker_one_sub_smul_pow
    (hd : ∃ π : K, 0 < ‖π‖ ∧ ‖π‖ < 1 ∧ ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖π‖) (hu : IsCompactoid u)
    (hh : 1 ≤ h)
    (h0 : ∀ s < h, PowerSeries.evalT a (PowerSeries.hasseDeriv s (charPowerSeries u)) = 0)
    (hunit : IsUnit (PowerSeries.evalT a (PowerSeries.hasseDeriv h (charPowerSeries u)))) :
    Module.finrank K (((1 - a • u) ^ h : c(I, K) →L[K] c(I, K)).ker) = h := by
  obtain ⟨H', hH'res, hH'ne, hfact⟩ := charPowerSeries_eq_pow_mul_of_riesz hd hu hh h0 hunit
  have hH0 : PowerSeries.evalT a (charPowerSeries u) = 0 := by simpa using h0 0 hh
  obtain ⟨ha0, -⟩ :=
    PowerSeries.exists_order_of_evalT_eq_zero (charPowerSeries_isEntire u hu) (by simp) hH0
  have hba : a⁻¹ * a = 1 := inv_mul_cancel₀ ha0
  refine PowerSeries.hasseDeriv_order_unique (fun s hs ↦ ?_) ?_ h0 hunit.ne_zero <;> rw [hfact]
  · exact PowerSeries.evalT_hasseDeriv_pow_mul_of_lt hba hH'res hs
  · rw [PowerSeries.evalT_hasseDeriv_pow_mul_self hba hH'res _]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr (inv_ne_zero ha0))) hH'ne

/-- **Serre's Riesz decomposition** [Serre1962, §7 Prop. 12]: a zero `a` of the characteristic
power series has an order `h ≥ 1` at which `c(I, K)` splits topologically as `N(a) ⊕ F(a)` into
two `u`-stable closed subspaces, with `(1 - a•u)ʰ` vanishing on the `h`-dimensional `N(a)` and
`1 - a•u` bijective on `F(a)`.  Where `finrank_ker_one_sub_smul_pow` computes `dim N(a)` for an
order supplied by the caller, this bundles the whole splitting and produces `h` from `a` alone. -/
theorem exists_riesz_decomposition (hd : ∃ π : K, 0 < ‖π‖ ∧ ‖π‖ < 1 ∧ ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    (hu : IsCompactoid u) (ha : PowerSeries.evalT a (charPowerSeries u) = 0) :
    ∃ (h : ℕ) (N F : Submodule K c(I, K)), 1 ≤ h ∧ Submodule.IsTopCompl N F ∧ (∀ x ∈ N, u x ∈ N) ∧
      (∀ x ∈ F, u x ∈ F) ∧ (∀ x ∈ N, ((1 - a • u) ^ h) x = 0) ∧
      (∀ y ∈ F, ∃ x ∈ F, (1 - a • u) x = y) ∧ (∀ x ∈ F, (1 - a • u) x = 0 → x = 0) ∧
      Module.finrank K N = h := by
  have hcoeff : PowerSeries.coeff 0 (charPowerSeries u) = 1 := by simp
  obtain ⟨-, h, hh, h0, hne⟩ :=
    PowerSeries.exists_order_of_evalT_eq_zero (charPowerSeries_isEntire u hu) hcoeff ha
  obtain ⟨p, w, hp, hup, huw, hpw, hnil, hw⟩ := exists_rieszProjection hu hh h0 hne.isUnit
  have hwb : w * (1 - a • u) = p := by
    rw [← ((Commute.one_left w).sub_left (Commute.smul_left huw a)).eq, hw]
  refine ⟨h, ((1 - a • u) ^ h : c(I, K) →L[K] c(I, K)).ker, p.range, hh, ?_, ?_, ?_,
    fun x hx ↦ hx, ?_, ?_, finrank_ker_one_sub_smul_pow hd hu hh h0 hne.isUnit⟩
  · rw [ker_one_sub_smul_pow_of_rieszProjection hp hup hpw hnil hw huw]
    exact isTopCompl_range_one_sub_range_of_isIdempotent hp
  · intro x hx
    have hx0 : ((1 - a • u) ^ h : c(I, K) →L[K] c(I, K)) x = 0 := hx
    change ((1 - a • u) ^ h : c(I, K) →L[K] c(I, K)) (u x) = 0
    rw [apply_of_mul_eq
      (((Commute.one_left u).sub_left ((Commute.refl u).smul_left a)).pow_left h).eq x]
    exact (congrArg u hx0).trans (map_zero u)
  · rintro _ ⟨y, rfl⟩
    exact ⟨u y, (apply_of_mul_eq hup y).symm⟩
  · rintro _ ⟨z, rfl⟩
    exact ⟨w (p z), ⟨w z, (apply_of_mul_eq hpw.symm z).symm⟩,
      (apply_of_mul_eq hw (p z)).trans (apply_of_mul_eq hp z)⟩
  · rintro _ ⟨z, rfl⟩ hz0
    have hz1 : ((1 : c(I, K) →L[K] c(I, K)) - a • u) (p z) = 0 := hz0
    have hz := (apply_of_mul_eq hwb (p z)).symm
    rw [hz1, map_zero] at hz
    exact (apply_of_mul_eq hp z).symm.trans hz

end Field

end TateFredholm
