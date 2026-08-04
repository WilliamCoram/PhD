/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TateFredholm.Fredholm
import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.MulWeierstrassDivision
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Topology.Algebra.Module.Complement

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
  yields an eigenvector `u x = a⁻¹ • x` (the eigenvector content of §7, Prop. 12).

## Main definitions

* `PowerSeries.hasseDeriv`, `PowerSeries.evalT`: divided derivatives and tsum-evaluation
  of power series (mathlib has neither for `PowerSeries` in the normed setting).
* `TateFredholm.resolventCoeff`: the coefficients `vₘ` of the Fredholm resolvent.
* `TateFredholm.fredholmDet`: the determinant value `det(1 - u) = H_u(1)`.

## Main results

* `TateFredholm.isUnit_one_sub_smul_iff_isUnit_evalT` (Serre Prop. 11).
* `TateFredholm.exists_mem_ker_of_hasseDeriv_evalT` (the dichotomy, over `R`).
* `TateFredholm.exists_eigenvector_of_evalT_charPowerSeries_eq_zero` (the headline,
  over a field).

## References

* [Serre1962] Serre, *Endomorphismes complètement continus des espaces de Banach
  p-adiques*, Publ. Math. IHÉS 12 (1962), 69–85.
* [Buzzard2007] Buzzard, *Eigenvarieties*, §3.
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
  PowerSeries.mk fun n => (n + k).choose k * coeff (n + k) f

@[simp]
theorem coeff_hasseDeriv (k n : ℕ) (f : PowerSeries R) :
    coeff n (hasseDeriv k f) = (n + k).choose k * coeff (n + k) f :=
  coeff_mk n _

@[simp]
theorem hasseDeriv_zero (f : PowerSeries R) : hasseDeriv 0 f = f := PowerSeries.ext fun n => by
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

/-- The cofinite form of the standing hypothesis.  Note that `‖a ^ n‖ ≤ ‖a‖ ^ n` may fail
at `n = 0` (the section has no `NormOneClass`), so the bound is only eventual. -/
private theorem tendsto_coeff_mul_pow_cofinite {a : R} {f : PowerSeries R}
    (hf : Tendsto (fun n => ‖coeff n f‖ * ‖a‖ ^ n) atTop (𝓝 0)) :
    Tendsto (fun n => coeff n f * a ^ n) cofinite (𝓝 0) := by
  rw [Nat.cofinite_eq_atTop]
  exact squeeze_zero_norm' ((eventually_gt_atTop 0).mono fun n hn => (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_pow_le' a hn) (norm_nonneg _))) hf

/-- The standing summability hypothesis for `evalT`: the series is restricted at the
radius `‖a‖` (`isRestricted_iff'` shape). -/
theorem summable_coeff_mul_pow {a : R} {f : PowerSeries R}
    (hf : Tendsto (fun n => ‖coeff n f‖ * ‖a‖ ^ n) atTop (𝓝 0)) :
    Summable fun n => coeff n f * a ^ n :=
  TateFredholm.summable_of_tendsto_cofinite (tendsto_coeff_mul_pow_cofinite hf)

theorem tendsto_norm_coeff_mul_pow_of_isRestricted {c : ℝ} {f : PowerSeries R}
    (hf : IsRestricted c f) {a : R} (ha : ‖a‖ ≤ c) :
    Tendsto (fun n => ‖coeff n f‖ * ‖a‖ ^ n) atTop (𝓝 0) :=
  squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg a) n))
    (fun n => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg a) ha n) (norm_nonneg _))
    ((isRestricted_iff' c f).mp hf)

@[simp]
theorem evalT_C (a r : R) : evalT a (C r) = r := by
  rw [evalT, tsum_eq_single 0 fun n hn => by simp [coeff_C, hn], coeff_zero_C, pow_zero, mul_one]

@[simp]
theorem evalT_one (a : R) : evalT a (1 : PowerSeries R) = 1 := by
  simpa using evalT_C a (1 : R)

theorem evalT_add {a : R} {f g : PowerSeries R}
    (hf : Tendsto (fun n => ‖coeff n f‖ * ‖a‖ ^ n) atTop (𝓝 0))
    (hg : Tendsto (fun n => ‖coeff n g‖ * ‖a‖ ^ n) atTop (𝓝 0)) :
    evalT a (f + g) = evalT a f + evalT a g :=
  (tsum_congr fun n => by rw [map_add, add_mul]).trans
    ((summable_coeff_mul_pow hf).tsum_add (summable_coeff_mul_pow hg))

private theorem evalT_sub' {a : R} {f g : PowerSeries R}
    (hf : Tendsto (fun n => ‖coeff n f‖ * ‖a‖ ^ n) atTop (𝓝 0))
    (hg : Tendsto (fun n => ‖coeff n g‖ * ‖a‖ ^ n) atTop (𝓝 0)) :
    evalT a (f - g) = evalT a f - evalT a g :=
  (tsum_congr fun n => by rw [map_sub, sub_mul]).trans
    ((summable_coeff_mul_pow hf).tsum_sub (summable_coeff_mul_pow hg))

private theorem evalT_X (a : R) : evalT a X = a := by
  rw [evalT, tsum_eq_single 1 fun n hn => by simp [coeff_X, hn], coeff_one_X, one_mul, pow_one]

/-- The product of two cofinitely-null families is cofinitely null on the product index —
the ultrametric substitute for absolute convergence.  For `ε > 0` the bad set
`{x | ε ≤ ‖F x.1 * G x.2‖}` sits inside the product of the two `(ε/B)`-bad sets, where `B`
bounds both families; both factors are finite. -/
private theorem summable_mul_of_tendsto_cofinite {ι κ : Type*} {F : ι → R} {G : κ → R}
    (hF : Tendsto F cofinite (𝓝 0)) (hG : Tendsto G cofinite (𝓝 0)) :
    Summable fun x : ι × κ => F x.1 * G x.2 := by
  obtain ⟨Bf, hBf⟩ := TateFredholm.bddAbove_range_norm_of_tendsto_cofinite hF
  obtain ⟨Bg, hBg⟩ := TateFredholm.bddAbove_range_norm_of_tendsto_cofinite hG
  set B : ℝ := max (max Bf Bg) 1
  have hB0 : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hFB : ∀ i, ‖F i‖ ≤ B :=
    fun i => (hBf ⟨i, rfl⟩).trans ((le_max_left Bf Bg).trans (le_max_left _ _))
  have hGB : ∀ k, ‖G k‖ ≤ B :=
    fun k => (hBg ⟨k, rfl⟩).trans ((le_max_right Bf Bg).trans (le_max_left _ _))
  refine TateFredholm.summable_of_tendsto_cofinite (Metric.tendsto_nhds.mpr fun ε hε => ?_)
  have hεB : 0 < ε / B := div_pos hε hB0
  /- One factor small and the other bounded already forces the product below `ε`. -/
  have hstep : ∀ p q : R, ‖q‖ ≤ B → ‖p‖ < ε / B → ‖p * q‖ < ε := fun p q hq hp =>
    ((norm_mul_le p q).trans (mul_le_mul_of_nonneg_left hq (norm_nonneg _))).trans_lt
      ((mul_lt_mul_of_pos_right hp hB0).trans_eq (div_mul_cancel₀ ε hB0.ne'))
  have hSF : {i : ι | ε / B ≤ ‖F i‖}.Finite :=
    (Filter.eventually_cofinite.mp
      (by simpa [dist_zero_right] using Metric.tendsto_nhds.mp hF _ hεB)).subset
      fun _ hi => not_lt.mpr hi
  have hSG : {k : κ | ε / B ≤ ‖G k‖}.Finite :=
    (Filter.eventually_cofinite.mp
      (by simpa [dist_zero_right] using Metric.tendsto_nhds.mp hG _ hεB)).subset
      fun _ hk => not_lt.mpr hk
  rw [Filter.eventually_cofinite]
  refine (hSF.prod hSG).subset fun x hx => ?_
  simp only [Set.mem_ofPred_eq, dist_zero_right, not_lt] at hx
  exact Set.mem_prod.mpr
    ⟨not_lt.mp fun h => absurd hx (not_le.mpr (hstep _ _ (hGB x.2) h)),
      not_lt.mp fun h => absurd hx (not_le.mpr
        ((congrArg (‖·‖) (mul_comm (F x.1) (G x.2))).trans_lt (hstep _ _ (hFB x.1) h)))⟩

/-- Cauchy product: evaluation is multiplicative on series restricted at the radius.
The product summability comes from the cofinite criterion (a product of two null
families has finite `ε`-bad set `bad_f × bad_g`), then
`Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`. -/
theorem evalT_mul {a : R} {f g : PowerSeries R}
    (hf : Tendsto (fun n => ‖coeff n f‖ * ‖a‖ ^ n) atTop (𝓝 0))
    (hg : Tendsto (fun n => ‖coeff n g‖ * ‖a‖ ^ n) atTop (𝓝 0)) :
    evalT a (f * g) = evalT a f * evalT a g := by
  have hfg := summable_mul_of_tendsto_cofinite (tendsto_coeff_mul_pow_cofinite hf)
    (tendsto_coeff_mul_pow_cofinite hg)
  rw [evalT, evalT, evalT, (summable_coeff_mul_pow hf).tsum_mul_tsum_eq_tsum_sum_antidiagonal
    (summable_coeff_mul_pow hg) hfg]
  refine tsum_congr fun n => ?_
  rw [coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Finset.mem_antidiagonal.mp hp, pow_add]
  ring

private theorem evalT_one_sub_C_mul_X (a b : R) : evalT a (1 - C b * X) = 1 - b * a := by
  have hT : ∀ {f : PowerSeries R}, IsRestricted ‖a‖ f →
      Tendsto (fun n => ‖coeff n f‖ * ‖a‖ ^ n) atTop (𝓝 0) :=
    fun hf => tendsto_norm_coeff_mul_pow_of_isRestricted hf le_rfl
  rw [evalT_sub' (hT (isRestricted_one ‖a‖))
      (hT (isRestricted.mul ‖a‖ (isRestricted_C ‖a‖ b) (isRestricted_X ‖a‖))),
    evalT_one, evalT_mul (hT (isRestricted_C ‖a‖ b)) (hT (isRestricted_X ‖a‖)),
    evalT_C, evalT_X]

/-- Divided derivatives preserve restrictedness at a positive radius: the binomial factor
is an `ℕ`-multiple, hence norm-nonincreasing ultrametrically, and the index shift only
costs the constant `(c ^ k)⁻¹`. -/
private theorem isRestricted_hasseDeriv {c : ℝ} (hc : 0 < c) {f : PowerSeries R}
    (hf : IsRestricted c f) (k : ℕ) : IsRestricted c (hasseDeriv k f) := by
  rw [isRestricted_iff']
  have hbase : Tendsto (fun n => ‖coeff (n + k) f‖ * c ^ (n + k) * (c ^ k)⁻¹) atTop (𝓝 0) := by
    simpa using
      (((isRestricted_iff' c f).mp hf).comp (tendsto_add_atTop_nat k)).mul_const (c ^ k)⁻¹
  refine squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hc.le n))
    (fun n => ?_) hbase
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
private theorem hasseDeriv_one_sub_C_mul_X_mul (b : R) (k : ℕ) (f : PowerSeries R) :
    hasseDeriv (k + 1) ((1 - C b * X) * f) =
      (1 - C b * X) * hasseDeriv (k + 1) f - C b * hasseDeriv k f := by
  refine PowerSeries.ext fun n => ?_
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
      Tendsto (fun n => ‖coeff n F‖ * ‖a‖ ^ n) atTop (𝓝 0) :=
    fun hF => tendsto_norm_coeff_mul_pow_of_isRestricted hF (le_max_left _ _)
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
            evalT_sub' (hT (isRestricted.mul c hLres hDk1))
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

/-- Division step: an entire series with constant term `1` vanishing at `a ≠ 0` has the
distinguished linear factor `1 - a⁻¹X`.  Proved through the Weierstrass division of
`PhD.ForMathlib` at a radius `c > ‖a‖` (where `1 - a⁻¹X` is `IsMulDistinguished c 1`),
the remainder being the constant `f(a) = 0`. -/
theorem exists_factor_of_evalT_eq_zero {f : PowerSeries K}
    (hf : ∀ c : ℝ, 0 < c → IsRestricted c f) (h0 : coeff 0 f = 1)
    {a : K} (ha0 : a ≠ 0) (ha : evalT a f = 0) :
    ∃ g : PowerSeries K, (∀ c : ℝ, 0 < c → IsRestricted c g) ∧
      f = (1 - C a⁻¹ * X) * g := by sorry

/-- Every zero of a nonzero entire series over a complete nonarchimedean field has
finite order: iterate the division step; termination because the Gauss norm at a radius
`c > ‖a‖` shrinks by `‖a‖/c < 1` at each step while the constant coefficient stays `1`.
The order is produced in Buzzard's divided-derivative form [Buzzard2007, pp. 22–23]. -/
theorem exists_order_of_evalT_eq_zero {f : PowerSeries K}
    (hf : ∀ c : ℝ, 0 < c → IsRestricted c f) (h0 : coeff 0 f = 1)
    {a : K} (ha : evalT a f = 0) :
    a ≠ 0 ∧ ∃ h : ℕ, 1 ≤ h ∧ (∀ s < h, evalT a (hasseDeriv s f) = 0) ∧
      evalT a (hasseDeriv h f) ≠ 0 := by sorry

/-- The order of a zero in the divided-derivative sense is unique. -/
theorem hasseDeriv_order_unique {f : PowerSeries K} {a : K} {h h' : ℕ}
    (h0 : ∀ s < h, evalT a (hasseDeriv s f) = 0) (hh : evalT a (hasseDeriv h f) ≠ 0)
    (h0' : ∀ s < h', evalT a (hasseDeriv s f) = 0)
    (hh' : evalT a (hasseDeriv h' f) ≠ 0) : h = h' := by sorry

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
  Tendsto (fun n => ‖T n - L‖) atTop (𝓝 0)

theorem IsOpLimit.unique [IsTate R] {T : ℕ → M →L[R] N} {L L' : M →L[R] N}
    (h : IsOpLimit T L) (h' : IsOpLimit T L') : L = L' := by
  have key : ∀ n, ‖L - L'‖ ≤ ‖T n - L‖ + ‖T n - L'‖ := fun n => by
    rw [show L - L' = -(T n - L) + (T n - L') by abel]
    exact (norm_add_le _ _).trans_eq (by rw [opNorm_neg])
  exact sub_eq_zero.mp ((opNorm_eq_zero_iff _).mp (le_antisymm
    (ge_of_tendsto' (by simpa using Filter.Tendsto.add h h') key) (opNorm_nonneg _)))

theorem IsOpLimit.add [IsTate R] {T T' : ℕ → M →L[R] N} {L L' : M →L[R] N}
    (h : IsOpLimit T L) (h' : IsOpLimit T' L') :
    IsOpLimit (fun n => T n + T' n) (L + L') := by
  refine squeeze_zero (fun n => opNorm_nonneg _) (fun n => ?_)
    (by simpa using Filter.Tendsto.add h h')
  rw [show T n + T' n - (L + L') = T n - L + (T' n - L') by abel]
  exact norm_add_le _ _

theorem IsOpLimit.const (L : M →L[R] N) : IsOpLimit (fun _ => L) L :=
  tendsto_const_nhds.congr fun _ => by rw [sub_self, opNorm_zero]

variable [IsTate R]

theorem IsOpLimit.comp_left {T : ℕ → M →L[R] M} {L : M →L[R] M}
    (h : IsOpLimit T L) (w : M →L[R] M) :
    IsOpLimit (fun n => w * T n) (w * L) := by
  refine squeeze_zero (fun n => opNorm_nonneg _) (fun n => ?_)
    (by simpa using Filter.Tendsto.const_mul ‖w‖ h)
  rw [← mul_sub]
  exact opNorm_mul_le _ _

theorem IsOpLimit.comp_right {T : ℕ → M →L[R] M} {L : M →L[R] M}
    (h : IsOpLimit T L) (w : M →L[R] M) :
    IsOpLimit (fun n => T n * w) (L * w) := by
  refine squeeze_zero (fun n => opNorm_nonneg _) (fun n => ?_)
    (by simpa using Filter.Tendsto.mul_const ‖w‖ h)
  rw [← sub_mul]
  exact opNorm_mul_le _ _

end OpLimit

variable {I : Type*} [DecidableEq I]

section CompactoidClosure

variable {J : Type*} [DecidableEq J]

@[simp]
theorem matrixCoeff_add (u v : c(I, R) →L[R] c(J, R)) (j : J) (i : I) :
    matrixCoeff (u + v) j i = matrixCoeff u j i + matrixCoeff v j i := rfl

@[simp]
theorem matrixCoeff_neg (u : c(I, R) →L[R] c(J, R)) (j : J) (i : I) :
    matrixCoeff (-u) j i = -matrixCoeff u j i := rfl

@[simp]
theorem matrixCoeff_sub (u v : c(I, R) →L[R] c(J, R)) (j : J) (i : I) :
    matrixCoeff (u - v) j i = matrixCoeff u j i - matrixCoeff v j i := rfl

@[simp]
theorem matrixCoeff_smul (a : R) (u : c(I, R) →L[R] c(J, R)) (j : J) (i : I) :
    matrixCoeff (a • u) j i = a * matrixCoeff u j i := rfl

/-- Public form of the row bound `‖matrixCoeff u j i‖ ≤ ‖u‖` (private in
`Fredholm.lean`). -/
theorem norm_matrixCoeff_le' [IsTate R] (u : c(I, R) →L[R] c(J, R)) (j : J) (i : I) :
    ‖matrixCoeff u j i‖ ≤ ‖u‖ :=
  calc ‖matrixCoeff u j i‖ ≤ ‖u (cSpace.single i 1)‖ := cSpace.norm_apply_le _ _
  _ ≤ ‖u‖ * ‖cSpace.single i (1 : R)‖ := le_opNorm _ _
  _ = ‖u‖ := by rw [cSpace.norm_single_one, mul_one]

/-- The rows are bounded families, so `rowNorm` is a genuine supremum (`le_ciSup`
applies). -/
private theorem bddAbove_range_norm_matrixCoeff [IsTate R] (u : c(I, R) →L[R] c(J, R))
    (j : J) : BddAbove (Set.range fun i => ‖matrixCoeff u j i‖) :=
  ⟨‖u‖, by rintro _ ⟨i, rfl⟩; exact norm_matrixCoeff_le' u j i⟩

theorem rowNorm_add_le [IsTate R] (u v : c(I, R) →L[R] c(J, R)) (j : J) :
    rowNorm (u + v) j ≤ max (rowNorm u j) (rowNorm v j) :=
  Real.iSup_le (fun i => (IsUltrametricDist.norm_add_le_max (matrixCoeff u j i)
    (matrixCoeff v j i)).trans (max_le_max (le_ciSup (bddAbove_range_norm_matrixCoeff u j) i)
      (le_ciSup (bddAbove_range_norm_matrixCoeff v j) i)))
    (le_max_of_le_left (rowNorm_nonneg u j))

@[simp]
theorem rowNorm_neg (u : c(I, R) →L[R] c(J, R)) (j : J) :
    rowNorm (-u) j = rowNorm u j :=
  iSup_congr fun i => by rw [matrixCoeff_neg, norm_neg]

theorem rowNorm_smul_le [IsTate R] (a : R) (u : c(I, R) →L[R] c(J, R)) (j : J) :
    rowNorm (a • u) j ≤ ‖a‖ * rowNorm u j :=
  Real.iSup_le (fun i => (norm_mul_le a (matrixCoeff u j i)).trans
    (mul_le_mul_of_nonneg_left (le_ciSup (bddAbove_range_norm_matrixCoeff u j) i)
      (norm_nonneg a)))
    (mul_nonneg (norm_nonneg a) (rowNorm_nonneg u j))

theorem IsCompactoid.add [IsTate R] {u v : c(I, R) →L[R] c(J, R)}
    (hu : IsCompactoid u) (hv : IsCompactoid v) : IsCompactoid (u + v) := by
  refine squeeze_zero (fun j => rowNorm_nonneg _ j) (fun j => rowNorm_add_le u v j) ?_
  simpa using Filter.Tendsto.max hu hv

theorem IsCompactoid.neg {u : c(I, R) →L[R] c(J, R)}
    (hu : IsCompactoid u) : IsCompactoid (-u) :=
  Filter.Tendsto.congr (fun j => (rowNorm_neg u j).symm) hu

theorem IsCompactoid.sub [IsTate R] {u v : c(I, R) →L[R] c(J, R)}
    (hu : IsCompactoid u) (hv : IsCompactoid v) : IsCompactoid (u - v) :=
  sub_eq_add_neg u v ▸ hu.add hv.neg

theorem IsCompactoid.smul [IsTate R] {u : c(I, R) →L[R] c(J, R)} (a : R)
    (hu : IsCompactoid u) : IsCompactoid (a • u) := by
  refine squeeze_zero (fun j => rowNorm_nonneg _ j) (fun j => rowNorm_smul_le a u j) ?_
  simpa using Filter.Tendsto.const_mul ‖a‖ hu

end CompactoidClosure

section Resolvent

/-- The coefficients `vₘ = ∑_{k ≤ m} cₖ u^{m-k}` of the Fredholm resolvent
`P(t, u) = det(1 - tu)/(1 - tu) = ∑ vₘ tᵐ` [Serre1962, §6 p. 78]. -/
def resolventCoeff (u : c(I, R) →L[R] c(I, R)) (m : ℕ) : c(I, R) →L[R] c(I, R) :=
  ∑ k ∈ Finset.range (m + 1), charCoeff u k • u ^ (m - k)

@[simp]
theorem resolventCoeff_zero (u : c(I, R) →L[R] c(I, R)) :
    resolventCoeff u 0 = 1 := by
  rw [resolventCoeff, Finset.sum_range_one, charCoeff_zero, Nat.sub_self, pow_zero, one_smul]

/-- Serre's recursion `vₘ = cₘ·1 + u vₘ₋₁` [Serre1962, §6 p. 78]. -/
theorem resolventCoeff_succ (u : c(I, R) →L[R] c(I, R)) (m : ℕ) :
    resolventCoeff u (m + 1) = charCoeff u (m + 1) • 1 + u * resolventCoeff u m := by
  have h : u * resolventCoeff u m
      = ∑ k ∈ Finset.range (m + 1), charCoeff u k • u ^ (m + 1 - k) := by
    rw [resolventCoeff, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [mul_smul_comm, ← pow_succ', show m + 1 - k = m - k + 1 by omega]
  rw [h, resolventCoeff, Finset.sum_range_succ, Nat.sub_self, pow_zero]
  exact add_comm _ _

/-- The defining identity `(1 - tu)·P(t, u) = det(1 - tu)`, coefficientwise. -/
theorem resolventCoeff_sub_mul (u : c(I, R) →L[R] c(I, R)) (m : ℕ) :
    resolventCoeff u (m + 1) - u * resolventCoeff u m = charCoeff u (m + 1) • 1 := by
  rw [resolventCoeff_succ, add_sub_cancel_right]

/-- The matrix of the identity is the Kronecker delta. -/
private theorem matrixCoeff_one (j i : I) :
    matrixCoeff (1 : c(I, R) →L[R] c(I, R)) j i = if j = i then 1 else 0 := by
  by_cases h : j = i
  · subst h
    rw [if_pos rfl]
    exact cSpace.single_apply_self _ _
  · rw [if_neg h]
    exact cSpace.single_apply_of_ne h 1

/-- Row expansion of a composite, in `tsum` form: the `(j, i)` coefficient of `u * w` is the
(unconditionally convergent) sum over `k` of `w[k,i]·u[j,k]`.  Unlike
`matrixCoeff_mul_of_rows` this needs no support hypothesis on the inner factor. -/
private theorem hasSum_matrixCoeff_mul (u w : c(I, R) →L[R] c(I, R)) (j i : I) :
    HasSum (fun k => matrixCoeff w k i * matrixCoeff u j k) (matrixCoeff (u * w) j i) := by
  have h := (cSpace.hasSum_single (w (cSpace.single i 1))).mapL ((cSpace.evalCLM j).comp u)
  simp only [ContinuousLinearMap.comp_apply, cSpace.evalCLM_apply, map_smul, smul_eq_mul] at h
  exact h

/-- Off the support, the resolvent coefficients are scalar (proved here so that it is
available to `matrixCoeff_resolventCoeff_of_rows`, which is stated first). -/
private theorem matrixCoeff_resolventCoeff_of_notMem' (u : c(I, R) →L[R] c(I, R)) (S : Finset I)
    (hS : ∀ j ∉ S, ∀ i, matrixCoeff u j i = 0) (m : ℕ) {j : I} (hj : j ∉ S) (i : I) :
    matrixCoeff (resolventCoeff u m) j i =
      if j = i then charCoeff u m else 0 := by
  cases m with
  | zero => rw [resolventCoeff_zero, matrixCoeff_one, charCoeff_zero]
  | succ m =>
      have h0 : HasSum (fun k => matrixCoeff (resolventCoeff u m) k i * matrixCoeff u j k) 0 := by
        simpa only [hS j hj, mul_zero] using hasSum_zero
      rw [resolventCoeff_succ, matrixCoeff_add, matrixCoeff_smul, matrixCoeff_one,
        (hasSum_matrixCoeff_mul u (resolventCoeff u m) j i).unique h0, add_zero, mul_ite,
        mul_one, mul_zero]

/-- Finite case of Serre's Lemme 3, identification step: for a row-supported operator,
the resolvent coefficients on the block are the coefficients of the adjugate of
`1 - tA` [Serre1962, §6 p. 79, step a): "les formules de Cramer"]. -/
theorem matrixCoeff_resolventCoeff_of_rows (u : c(I, R) →L[R] c(I, R)) (S : Finset I)
    (hS : ∀ j ∉ S, ∀ i, matrixCoeff u j i = 0) (m : ℕ) (j i : S) :
    matrixCoeff (resolventCoeff u m) j i =
      Polynomial.coeff
        ((Matrix.adjugate (1 - (Polynomial.X : Polynomial R) •
          Matrix.of fun p q : S => Polynomial.C (matrixCoeff u p q))) j i) m := by
  classical
  set B : Matrix S S (Polynomial R) := 1 - (Polynomial.X : Polynomial R) •
    Matrix.of fun p q : S => Polynomial.C (matrixCoeff u p q) with hBdef
  have hdet : ∀ n : ℕ, Polynomial.coeff (Matrix.det B) n = charCoeff u n := fun n => by
    rw [hBdef]; exact (charCoeff_eq_det_coeff u S hS n).symm
  have hBentry : ∀ p q : S, B p q
      = (if p = q then 1 else 0) - Polynomial.X * Polynomial.C (matrixCoeff u p q) := fun p q => by
    rw [hBdef]
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.of_apply,
      smul_eq_mul]
  -- coefficientwise form of `B p k * P`, at `0` and at a successor
  have hBmul0 : ∀ (p k : S) (P : Polynomial R),
      Polynomial.coeff (B p k * P) 0 = if p = k then P.coeff 0 else 0 := fun p k P => by
    rw [hBentry]
    by_cases h : p = k
    · rw [if_pos h, if_pos h, sub_mul, one_mul, Polynomial.coeff_sub, mul_assoc,
        Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul, sub_zero]
    · rw [if_neg h, if_neg h, zero_sub, neg_mul, mul_assoc, Polynomial.coeff_neg,
        Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul, neg_zero]
  have hBmul : ∀ (p k : S) (P : Polynomial R) (n : ℕ),
      Polynomial.coeff (B p k * P) (n + 1)
        = (if p = k then P.coeff (n + 1) else 0) - matrixCoeff u p k * P.coeff n := by
    intro p k P n
    rw [hBentry]
    by_cases h : p = k
    · rw [if_pos h, if_pos h, sub_mul, one_mul, Polynomial.coeff_sub, mul_assoc,
        Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]
    · rw [if_neg h, if_neg h, zero_sub, neg_mul, mul_assoc, Polynomial.coeff_neg,
        Polynomial.coeff_X_mul, Polynomial.coeff_C_mul, zero_sub]
  -- Cramer: `B · adj B = det B · 1`, read entrywise and coefficientwise
  have hcramer : ∀ (n : ℕ) (p q : S),
      ∑ k : S, Polynomial.coeff (B p k * Matrix.adjugate B k q) n
        = Polynomial.coeff (Matrix.det B * (if p = q then 1 else 0)) n := fun n p q => by
    rw [← Polynomial.finsetSum_coeff, ← Matrix.mul_apply, Matrix.mul_adjugate, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
  -- the operator side expands over `S` because `i ∈ S` kills the off-support correction
  have hprod : ∀ (n : ℕ) (p q : S), matrixCoeff (u * resolventCoeff u n) p q
      = ∑ k : S, matrixCoeff u p k * matrixCoeff (resolventCoeff u n) k q := fun n p q => by
    have hz : ∀ k ∉ S,
        matrixCoeff (resolventCoeff u n) k (q : I) * matrixCoeff u (p : I) k = 0 := fun k hk => by
      rw [matrixCoeff_resolventCoeff_of_notMem' u S hS n hk (q : I),
        if_neg (by rintro rfl; exact hk q.2), zero_mul]
    rw [(hasSum_matrixCoeff_mul u (resolventCoeff u n) (p : I) (q : I)).unique
      (hasSum_sum_of_ne_finset_zero hz), ← Finset.sum_coe_sort S]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  suffices h : ∀ (n : ℕ) (p q : S),
      matrixCoeff (resolventCoeff u n) p q = Polynomial.coeff (Matrix.adjugate B p q) n from h m j i
  intro n
  induction n with
  | zero =>
      intro p q
      have h := hcramer 0 p q
      simp only [hBmul0, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
      rw [resolventCoeff_zero, matrixCoeff_one, h]
      rcases eq_or_ne p q with rfl | hpq
      · rw [if_pos rfl, if_pos rfl, mul_one, hdet, charCoeff_zero]
      · rw [if_neg fun hc => hpq (Subtype.ext hc), if_neg hpq, mul_zero, Polynomial.coeff_zero]
  | succ n ih =>
      intro p q
      have h := hcramer (n + 1) p q
      simp only [hBmul, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
      rw [sub_eq_iff_eq_add] at h
      have hsum : ∑ k : S, matrixCoeff u p k * matrixCoeff (resolventCoeff u n) k q
          = ∑ k : S, matrixCoeff u p k * Polynomial.coeff (Matrix.adjugate B k q) n :=
        Finset.sum_congr rfl fun k _ => by rw [ih k q]
      rw [resolventCoeff_succ, matrixCoeff_add, matrixCoeff_smul, matrixCoeff_one, hprod, hsum, h]
      congr 1
      rcases eq_or_ne p q with rfl | hpq
      · rw [if_pos rfl, if_pos rfl, mul_one, mul_one, hdet]
      · rw [if_neg fun hc => hpq (Subtype.ext hc), if_neg hpq, mul_zero, mul_zero,
          Polynomial.coeff_zero]

/-- Off the support, the resolvent coefficients are scalar: `vₘ = cₘ` on the diagonal,
`0` elsewhere. -/
theorem matrixCoeff_resolventCoeff_of_notMem (u : c(I, R) →L[R] c(I, R)) (S : Finset I)
    (hS : ∀ j ∉ S, ∀ i, matrixCoeff u j i = 0) (m : ℕ) {j : I} (hj : j ∉ S) (i : I) :
    matrixCoeff (resolventCoeff u m) j i =
      if j = i then charCoeff u m else 0 :=
  matrixCoeff_resolventCoeff_of_notMem' u S hS m hj i

/-- Ultrametric Hadamard bound: a determinant is bounded by the product of row bounds
(restated locally: `norm_det_le_of_row_bounds` is private in `Fredholm.lean`). -/
private theorem norm_det_le_of_row_bounds' {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (f : n → ℝ) (hf : ∀ j i, ‖M j i‖ ≤ f j) :
    ‖M.det‖ ≤ ∏ j, f j := by
  classical
  rw [Matrix.det_apply]
  have hne : (Finset.univ : Finset (Equiv.Perm n)).Nonempty := Finset.univ_nonempty
  refine le_trans (hne.norm_sum_le_sup'_norm _) (Finset.sup'_le _ _ fun σ _ => ?_)
  have hsm : ‖Equiv.Perm.sign σ • ∏ i, M (σ i) i‖ = ‖∏ i, M (σ i) i‖ := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
    · rw [one_smul]
    · rw [Units.neg_smul, one_smul, norm_neg]
  rw [hsm]
  calc ‖∏ i, M (σ i) i‖ ≤ ∏ i, ‖M (σ i) i‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ i, f (σ i) := Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hf (σ i) i)
    _ = ∏ j, f j := Equiv.prod_comp σ f

/-- `‖(-1)ⁿ‖ = 1` (restated: private in `Fredholm.lean`). -/
private theorem norm_neg_one_pow' (m : ℕ) : ‖(-1 : R) ^ m‖ = 1 := by
  rcases Nat.even_or_odd m with he | ho
  · rw [he.neg_one_pow, norm_one]
  · rw [ho.neg_one_pow, norm_neg, norm_one]

/-- **Coefficientwise ultrametric Hadamard bound.**  If the polynomial matrix `MC` has
entries `C (Y p q) - X · C (A p q)` with `‖Y p q‖ ≤ 1` and `‖A p q‖ ≤ f p`, then the
`m`-th coefficient of `det MC` is bounded by any bound `c` for the products
`∏_{p ∈ T} f p` over `m`-element sets `T`: expanding `det` multilinearly in the rows,
each summand carries exactly one `A`-row per element of an `m`-set. -/
private theorem norm_coeff_det_le {n : Type*} [Fintype n] [DecidableEq n]
    (MC : Matrix n n (Polynomial R)) (A Y : Matrix n n R) (f : n → ℝ)
    (hMC : ∀ p q, MC p q = Polynomial.C (Y p q) - Polynomial.X * Polynomial.C (A p q))
    (hA : ∀ p q, ‖A p q‖ ≤ f p) (hY : ∀ p q, ‖Y p q‖ ≤ 1) (m : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hcT : ∀ T : Finset n, T.card = m → ∏ p ∈ T, f p ≤ c) :
    ‖(MC.det).coeff m‖ ≤ c := by
  have hMCeq : MC = Y.map (Polynomial.C : R →+* Polynomial R)
      - (Polynomial.X : Polynomial R) • A.map (Polynomial.C : R →+* Polynomial R) := by
    refine Matrix.ext fun p q => ?_
    rw [hMC p q, Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.map_apply,
      smul_eq_mul]
  have hpw : ∀ (t : Finset n) (U V : Matrix n n (Polynomial R)) (r : n),
      t.piecewise U V r = if r ∈ t then U r else V r := fun _ _ _ _ => rfl
  have hpwR : ∀ (t : Finset n) (U V : Matrix n n R) (r : n),
      t.piecewise U V r = if r ∈ t then U r else V r := fun _ _ _ _ => rfl
  have hkey : MC.det = ∑ s : Finset n, Matrix.detRowAlternating
      (s.piecewise (-((Polynomial.X : Polynomial R) •
        A.map (Polynomial.C : R →+* Polynomial R)))
        (Y.map (Polynomial.C : R →+* Polynomial R))) := by
    rw [hMCeq, show (Y.map (Polynomial.C : R →+* Polynomial R)
        - (Polynomial.X : Polynomial R) • A.map (Polynomial.C : R →+* Polynomial R))
        = (-((Polynomial.X : Polynomial R) • A.map (Polynomial.C : R →+* Polynomial R)))
          + Y.map (Polynomial.C : R →+* Polynomial R) from by abel]
    exact (Matrix.detRowAlternating (R := Polynomial R) (n := n)).map_add_univ _ _
  -- each summand: pull the `-X` out of the `s`-rows through a diagonal matrix
  have hdiag : ∀ s : Finset n,
      (s.piecewise (-((Polynomial.X : Polynomial R) •
        A.map (Polynomial.C : R →+* Polynomial R)))
        (Y.map (Polynomial.C : R →+* Polynomial R)))
        = Matrix.diagonal (fun p => if p ∈ s then -(Polynomial.X : Polynomial R) else 1)
          * ((Matrix.of (s.piecewise A Y)).map (Polynomial.C : R →+* Polynomial R)) := by
    intro s
    refine Matrix.ext fun p q => ?_
    rw [Matrix.diagonal_mul, Matrix.map_apply, Matrix.of_apply, hpw, hpwR]
    by_cases hp : p ∈ s
    · rw [if_pos hp, if_pos hp, if_pos hp, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply,
        smul_eq_mul, neg_mul]
    · rw [if_neg hp, if_neg hp, if_neg hp, Matrix.map_apply, one_mul]
  have hdet_s : ∀ s : Finset n, Matrix.detRowAlternating
      (s.piecewise (-((Polynomial.X : Polynomial R) •
        A.map (Polynomial.C : R →+* Polynomial R)))
        (Y.map (Polynomial.C : R →+* Polynomial R)))
        = (-(Polynomial.X : Polynomial R)) ^ s.card
          * Polynomial.C (Matrix.det (Matrix.of (s.piecewise A Y))) := by
    intro s
    have hmapdet : ((Matrix.of (s.piecewise A Y)).map (Polynomial.C : R →+* Polynomial R)).det
        = Polynomial.C (Matrix.det (Matrix.of (s.piecewise A Y))) :=
      (RingHom.map_det (Polynomial.C : R →+* Polynomial R) _).symm
    show Matrix.det _ = _
    rw [hdiag s, Matrix.det_mul, Matrix.det_diagonal, hmapdet]
    congr 1
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  have hcoeff : (MC.det).coeff m = ∑ s : Finset n,
      (if m = s.card then (-1 : R) ^ s.card * Matrix.det (Matrix.of (s.piecewise A Y))
        else 0) := by
    rw [hkey, Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hCX : (-(Polynomial.X : Polynomial R)) ^ s.card
        * Polynomial.C (Matrix.det (Matrix.of (s.piecewise A Y)))
        = Polynomial.C ((-1 : R) ^ s.card * Matrix.det (Matrix.of (s.piecewise A Y)))
          * (Polynomial.X : Polynomial R) ^ s.card := by
      rw [neg_pow, map_mul, map_pow, map_neg, map_one]
      ring
    rw [hdet_s s, hCX, Polynomial.coeff_C_mul_X_pow]
  rw [hcoeff]
  have hne : (Finset.univ : Finset (Finset n)).Nonempty := Finset.univ_nonempty
  refine le_trans (hne.norm_sum_le_sup'_norm _) (Finset.sup'_le _ _ fun s _ => ?_)
  by_cases hs : m = s.card
  · rw [if_pos hs]
    refine le_trans (norm_mul_le _ _) ?_
    rw [norm_neg_one_pow', one_mul]
    refine le_trans (norm_det_le_of_row_bounds' _ (fun p => if p ∈ s then f p else 1)
      (fun p q => ?_)) ?_
    · rw [Matrix.of_apply, hpwR]
      by_cases hp : p ∈ s
      · rw [if_pos hp, if_pos hp]; exact hA p q
      · rw [if_neg hp, if_neg hp]; exact hY p q
    · rw [Finset.prod_ite_mem, Finset.univ_inter]
      exact hcT s hs.symm
  · rw [if_neg hs, norm_zero]
    exact hc

/-- Row bound in terms of `rowNorm` (`norm_matrixCoeff_le_rowNorm` is private in
`Fredholm.lean` and in `Matrix.lean`). -/
private theorem norm_matrixCoeff_le_rowNorm' [IsTate R] (u : c(I, R) →L[R] c(I, R)) (j i : I) :
    ‖matrixCoeff u j i‖ ≤ rowNorm u j :=
  le_ciSup (bddAbove_range_norm_matrixCoeff u j) i

/-- **Serre's Lemme 3, entrywise** for a row-supported operator: every matrix coefficient of
`vₘ` is bounded by any bound for the products of `m` distinct row norms.  Enlarging the
support to `S ∪ {i, j}` makes the Cramer identity `matrixCoeff_resolventCoeff_of_rows`
applicable to *every* pair of indices. -/
private theorem norm_matrixCoeff_resolventCoeff_le_of_rows [IsTate R] (w : c(I, R) →L[R] c(I, R))
    (S : Finset I) (hS : ∀ j ∉ S, ∀ i, matrixCoeff w j i = 0) (m : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hcT : ∀ T : Finset I, T.card = m → ∏ j ∈ T, rowNorm w j ≤ c) (j i : I) :
    ‖matrixCoeff (resolventCoeff w m) j i‖ ≤ c := by
  classical
  set S' : Finset I := insert j (insert i S) with hS'def
  have hjS' : j ∈ S' := Finset.mem_insert_self _ _
  have hiS' : i ∈ S' := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hSS' : ∀ p ∉ S', ∀ q, matrixCoeff w p q = 0 := fun p hp q =>
    hS p (fun hpS => hp (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hpS))) q
  have hrow : matrixCoeff (resolventCoeff w m) j i =
      Polynomial.coeff ((Matrix.adjugate (1 - (Polynomial.X : Polynomial R) •
        Matrix.of fun p q : S' => Polynomial.C (matrixCoeff w p q)))
          ⟨j, hjS'⟩ ⟨i, hiS'⟩) m :=
    matrixCoeff_resolventCoeff_of_rows w S' hSS' m ⟨j, hjS'⟩ ⟨i, hiS'⟩
  rw [hrow, Matrix.adjugate_apply]
  refine norm_coeff_det_le _
    (Matrix.of fun p q : S' => if p = ⟨i, hiS'⟩ then 0 else matrixCoeff w p q)
    (Matrix.of fun p q : S' => if p = ⟨i, hiS'⟩ then (if q = ⟨j, hjS'⟩ then (1 : R) else 0)
      else (if p = q then (1 : R) else 0))
    (fun p => rowNorm w p) (fun p q => ?_) (fun p q => ?_)
    (fun p q => ?_) m hc (fun T hT => ?_)
  · rw [Matrix.updateRow_apply, Matrix.of_apply, Matrix.of_apply]
    by_cases hp : p = ⟨i, hiS'⟩
    · rw [if_pos hp, if_pos hp, if_pos hp, map_zero, mul_zero, sub_zero, Pi.single_apply]
      by_cases hq : q = ⟨j, hjS'⟩
      · rw [if_pos hq, if_pos hq, map_one]
      · rw [if_neg hq, if_neg hq, map_zero]
    · rw [if_neg hp, if_neg hp, if_neg hp, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul]
      by_cases hpq : p = q
      · rw [if_pos hpq, if_pos hpq, map_one]
      · rw [if_neg hpq, if_neg hpq, map_zero]
  · rw [Matrix.of_apply]
    by_cases hp : p = ⟨i, hiS'⟩
    · rw [if_pos hp, norm_zero]
      exact rowNorm_nonneg w p
    · rw [if_neg hp]
      exact norm_matrixCoeff_le_rowNorm' w p q
  · rw [Matrix.of_apply]
    by_cases hp : p = ⟨i, hiS'⟩
    · rw [if_pos hp]
      by_cases hq : q = ⟨j, hjS'⟩
      · rw [if_pos hq, norm_one]
      · rw [if_neg hq, norm_zero]; exact zero_le_one
    · rw [if_neg hp]
      by_cases hpq : p = q
      · rw [if_pos hpq, norm_one]
      · rw [if_neg hpq, norm_zero]; exact zero_le_one
  · have hinj : ∀ x ∈ T, ∀ y ∈ T, (x : I) = (y : I) → x = y := fun x _ y _ h => Subtype.ext h
    have himg : (T.image (fun p : S' => (p : I))).card = m := by
      rw [Finset.card_image_of_injective T Subtype.coe_injective, hT]
    rw [← Finset.prod_image hinj]
    exact hcT _ himg

/-- Serre's Lemme 3 for a row-supported operator. -/
private theorem norm_resolventCoeff_le_of_rows [IsTate R] (w : c(I, R) →L[R] c(I, R))
    (S : Finset I) (hS : ∀ j ∉ S, ∀ i, matrixCoeff w j i = 0) (m : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hcT : ∀ T : Finset I, T.card = m → ∏ j ∈ T, rowNorm w j ≤ c) :
    ‖resolventCoeff w m‖ ≤ c := by
  rw [norm_eq_iSup_matrixCoeff]
  exact Real.iSup_le (fun j => Real.iSup_le
    (fun i => norm_matrixCoeff_resolventCoeff_le_of_rows w S hS m hc hcT j i) hc) hc

/-- The row sup is bounded by the operator norm (`rowNorm_le_opNorm` is private in
`Fredholm.lean`). -/
private theorem rowNorm_le_opNorm' [IsTate R] (u : c(I, R) →L[R] c(I, R)) (j : I) :
    rowNorm u j ≤ ‖u‖ :=
  Real.iSup_le (fun i => norm_matrixCoeff_le' u j i) (opNorm_nonneg u)

/-- Truncating rows can only decrease the row norms. -/
private theorem rowNorm_truncation_comp_le [IsTate R] (u : c(I, R) →L[R] c(I, R)) (S : Finset I)
    (j : I) : rowNorm ((truncation S).comp u) j ≤ rowNorm u j := by
  refine Real.iSup_le (fun i => ?_) (rowNorm_nonneg u j)
  show ‖(if j ∈ S then matrixCoeff u j i else 0)‖ ≤ rowNorm u j
  by_cases hj : j ∈ S
  · rw [if_pos hj]
    exact norm_matrixCoeff_le_rowNorm' u j i
  · rw [if_neg hj, norm_zero]
    exact rowNorm_nonneg u j

/-- Scalars scale the operator norm (`OperatorNorm.lean` has `opNorm_mul_le` but no
`smul` version). -/
private theorem opNorm_smul_le' [IsTate R] (a : R) (w : c(I, R) →L[R] c(I, R)) :
    ‖a • w‖ ≤ ‖a‖ * ‖w‖ := by
  refine opNorm_le_of_forall _ (mul_nonneg (norm_nonneg a) (opNorm_nonneg w)) fun x => ?_
  calc ‖(a • w) x‖ = ‖a • w x‖ := rfl
  _ ≤ ‖a‖ * ‖w x‖ := norm_smul_le _ _
  _ ≤ ‖a‖ * (‖w‖ * ‖x‖) := mul_le_mul_of_nonneg_left (le_opNorm w x) (norm_nonneg a)
  _ = ‖a‖ * ‖w‖ * ‖x‖ := (mul_assoc _ _ _).symm

/-- Powers are continuous on norm-bounded families: `vₐ → u` uniformly bounded implies
`vₐⁿ → uⁿ`.  Induction on `n` through `v^{n+1} - u^{n+1} = vⁿ(v - u) + (vⁿ - uⁿ)u`. -/
private theorem tendsto_norm_pow_sub_pow [IsTate R] {α : Type*} {F : Filter α}
    (u : c(I, R) →L[R] c(I, R)) (v : α → c(I, R) →L[R] c(I, R)) {D : ℝ}
    (hD : ∀ x, ‖v x‖ ≤ D) (h : Tendsto (fun x => ‖v x - u‖) F (𝓝 0)) (n : ℕ) :
    Tendsto (fun x => ‖v x ^ n - u ^ n‖) F (𝓝 0) := by
  induction n with
  | zero =>
      simp only [pow_zero, sub_self, opNorm_zero]
      exact tendsto_const_nhds
  | succ n ih =>
      have hg : Tendsto (fun x => D ^ n * ‖v x - u‖ + ‖v x ^ n - u ^ n‖ * ‖u‖) F (𝓝 0) := by
        simpa using (h.const_mul (D ^ n)).add (ih.mul_const ‖u‖)
      refine squeeze_zero (fun x => opNorm_nonneg _)
        (g := fun x => D ^ n * ‖v x - u‖ + ‖v x ^ n - u ^ n‖ * ‖u‖) (fun x => ?_) hg
      have hbnd : ‖v x ^ n‖ ≤ D ^ n :=
        (opNorm_pow_le (v x) n).trans (pow_le_pow_left₀ (opNorm_nonneg (v x)) (hD x) n)
      have h1 : ‖v x ^ n * (v x - u)‖ ≤ D ^ n * ‖v x - u‖ :=
        (opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hbnd (opNorm_nonneg (v x - u)))
      have h2 : ‖(v x ^ n - u ^ n) * u‖ ≤ ‖v x ^ n - u ^ n‖ * ‖u‖ := opNorm_mul_le _ _
      calc ‖v x ^ (n + 1) - u ^ (n + 1)‖
          = ‖v x ^ n * (v x - u) + (v x ^ n - u ^ n) * u‖ := by
            rw [show v x ^ n * (v x - u) + (v x ^ n - u ^ n) * u = v x ^ (n + 1) - u ^ (n + 1) from
              by rw [mul_sub, sub_mul, pow_succ, pow_succ]; abel]
      _ ≤ ‖v x ^ n * (v x - u)‖ + ‖(v x ^ n - u ^ n) * u‖ := norm_add_le _ _
      _ ≤ D ^ n * ‖v x - u‖ + ‖v x ^ n - u ^ n‖ * ‖u‖ := add_le_add h1 h2

/-- Truncation-limit step of Lemme 3, proved here so that it is available to
`norm_resolventCoeff_le`, which is stated first (the public form below delegates). -/
private theorem tendsto_resolventCoeff_truncation' [IsTate R] (u : c(I, R) →L[R] c(I, R))
    (hu : IsCompactoid u) (m : ℕ) :
    Tendsto (fun S : Finset I =>
      ‖resolventCoeff ((truncation S).comp u) m - resolventCoeff u m‖) atTop (𝓝 0) := by
  have hvD : ∀ S : Finset I, ‖(truncation S).comp u‖ ≤ ‖u‖ := fun S =>
    opNorm_le_of_forall _ (opNorm_nonneg u) fun x =>
      show ‖truncation S (u x)‖ ≤ ‖u‖ * ‖x‖ from
        (norm_truncation_apply_le S (u x)).trans (le_opNorm u x)
  have htr : Tendsto (fun S : Finset I => ‖(truncation S).comp u - u‖) atTop (𝓝 0) :=
    tendsto_truncation_comp u hu
  have hpow : ∀ n : ℕ,
      Tendsto (fun S : Finset I => ‖((truncation S).comp u) ^ n - u ^ n‖) atTop (𝓝 0) :=
    fun n => tendsto_norm_pow_sub_pow u (fun S => (truncation S).comp u) hvD htr n
  have hc : ∀ k : ℕ, Tendsto
      (fun S : Finset I => ‖charCoeff ((truncation S).comp u) k - charCoeff u k‖) atTop (𝓝 0) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [charCoeff_zero, sub_self, norm_zero]
      exact tendsto_const_nhds
    · have hg : Tendsto (fun S : Finset I => ‖u‖ ^ (k - 1) * ‖(truncation S).comp u - u‖)
          atTop (𝓝 0) := by simpa using htr.const_mul (‖u‖ ^ (k - 1))
      refine squeeze_zero (fun S => norm_nonneg _)
        (g := fun S : Finset I => ‖u‖ ^ (k - 1) * ‖(truncation S).comp u - u‖) (fun S => ?_) hg
      exact (norm_charCoeff_sub_le _ _ (hu.comp_left _) hu hk).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_max_of_le_right (opNorm_nonneg u))
          (max_le (hvD S) le_rfl) _) (opNorm_nonneg _))
  have hterm : ∀ k : ℕ, Tendsto (fun S : Finset I =>
      ‖charCoeff ((truncation S).comp u) k • ((truncation S).comp u) ^ (m - k)
        - charCoeff u k • u ^ (m - k)‖) atTop (𝓝 0) := by
    intro k
    have hg : Tendsto (fun S : Finset I =>
        ‖charCoeff ((truncation S).comp u) k - charCoeff u k‖ * ‖u‖ ^ (m - k)
          + ‖charCoeff u k‖ * ‖((truncation S).comp u) ^ (m - k) - u ^ (m - k)‖)
        atTop (𝓝 0) := by
      have h1 := (hc k).mul_const (‖u‖ ^ (m - k))
      have h2 := (hpow (m - k)).const_mul ‖charCoeff u k‖
      simpa using h1.add h2
    refine squeeze_zero (fun S => opNorm_nonneg _)
      (g := fun S : Finset I =>
        ‖charCoeff ((truncation S).comp u) k - charCoeff u k‖ * ‖u‖ ^ (m - k)
          + ‖charCoeff u k‖ * ‖((truncation S).comp u) ^ (m - k) - u ^ (m - k)‖)
      (fun S => ?_) hg
    calc ‖charCoeff ((truncation S).comp u) k • ((truncation S).comp u) ^ (m - k)
            - charCoeff u k • u ^ (m - k)‖
        = ‖(charCoeff ((truncation S).comp u) k - charCoeff u k) • ((truncation S).comp u) ^ (m - k)
            + charCoeff u k • (((truncation S).comp u) ^ (m - k) - u ^ (m - k))‖ := by
          rw [sub_smul, smul_sub]
          congr 1
          abel
    _ ≤ ‖(charCoeff ((truncation S).comp u) k - charCoeff u k) • ((truncation S).comp u) ^ (m - k)‖
          + ‖charCoeff u k • (((truncation S).comp u) ^ (m - k) - u ^ (m - k))‖ := norm_add_le _ _
    _ ≤ ‖charCoeff ((truncation S).comp u) k - charCoeff u k‖ * ‖u‖ ^ (m - k)
          + ‖charCoeff u k‖ * ‖((truncation S).comp u) ^ (m - k) - u ^ (m - k)‖ :=
        add_le_add ((opNorm_smul_le' _ _).trans (mul_le_mul_of_nonneg_left
          ((opNorm_pow_le _ _).trans (pow_le_pow_left₀ (opNorm_nonneg _) (hvD S) _))
          (norm_nonneg _))) (opNorm_smul_le' _ _)
  have hgsum : Tendsto (fun S : Finset I => ∑ k ∈ Finset.range (m + 1),
      ‖charCoeff ((truncation S).comp u) k • ((truncation S).comp u) ^ (m - k)
        - charCoeff u k • u ^ (m - k)‖) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.range (m + 1)) fun k _ => hterm k
  refine squeeze_zero (fun S => opNorm_nonneg _)
    (g := fun S : Finset I => ∑ k ∈ Finset.range (m + 1),
      ‖charCoeff ((truncation S).comp u) k • ((truncation S).comp u) ^ (m - k)
        - charCoeff u k • u ^ (m - k)‖) (fun S => ?_) hgsum
  rw [resolventCoeff, resolventCoeff, ← Finset.sum_sub_distrib]
  exact opNorm_sum_le _ _

/-- Serre's Lemme 3 [Serre1962, §6 p. 79]: `‖vₘ‖` is bounded by a product of `m`
pairwise-distinct row norms (stated as the sup over `m`-element subsets). -/
theorem norm_resolventCoeff_le [IsTate R] (u : c(I, R) →L[R] c(I, R))
    (hu : IsCompactoid u) (m : ℕ) :
    ‖resolventCoeff u m‖ ≤ ⨆ S : {S : Finset I // S.card = m}, ∏ j ∈ (S : Finset I), rowNorm u j := by
  classical
  have hbdd : BddAbove (Set.range fun S : {S : Finset I // S.card = m} =>
      ∏ j ∈ (S : Finset I), rowNorm u j) := by
    refine ⟨‖u‖ ^ m, ?_⟩
    rintro _ ⟨T, rfl⟩
    calc ∏ j ∈ (T : Finset I), rowNorm u j ≤ ∏ _j ∈ (T : Finset I), ‖u‖ :=
          Finset.prod_le_prod (fun j _ => rowNorm_nonneg u j) (fun j _ => rowNorm_le_opNorm' u j)
    _ = ‖u‖ ^ m := by rw [Finset.prod_const, T.2]
  set c : ℝ := ⨆ S : {S : Finset I // S.card = m}, ∏ j ∈ (S : Finset I), rowNorm u j with hcdef
  have hc : 0 ≤ c := Real.iSup_nonneg fun T => Finset.prod_nonneg fun j _ => rowNorm_nonneg u j
  have hcT : ∀ T : Finset I, T.card = m → ∏ j ∈ T, rowNorm u j ≤ c := fun T hT =>
    le_ciSup hbdd (⟨T, hT⟩ : {S : Finset I // S.card = m})
  have hbound : ∀ S : Finset I, ‖resolventCoeff ((truncation S).comp u) m‖ ≤ c := by
    intro S
    refine norm_resolventCoeff_le_of_rows _ S (fun p hp q => ?_) m hc (fun T hT => ?_)
    · show (if p ∈ S then (u (cSpace.single q 1)) p else 0) = 0
      exact if_neg hp
    · exact le_trans (Finset.prod_le_prod (fun j _ => rowNorm_nonneg _ j)
        (fun j _ => rowNorm_truncation_comp_le u S j)) (hcT T hT)
  have htend : Tendsto (fun S : Finset I =>
      ‖resolventCoeff ((truncation S).comp u) m - resolventCoeff u m‖ + c) atTop (𝓝 (0 + c)) :=
    (tendsto_resolventCoeff_truncation' u hu m).add tendsto_const_nhds
  rw [zero_add] at htend
  refine ge_of_tendsto htend (Filter.Eventually.of_forall fun S => ?_)
  calc ‖resolventCoeff u m‖
      = ‖resolventCoeff ((truncation S).comp u) m
          + -(resolventCoeff ((truncation S).comp u) m - resolventCoeff u m)‖ := by
        congr 1
        abel
  _ ≤ ‖resolventCoeff ((truncation S).comp u) m‖
        + ‖-(resolventCoeff ((truncation S).comp u) m - resolventCoeff u m)‖ := norm_add_le _ _
  _ = ‖resolventCoeff ((truncation S).comp u) m‖
        + ‖resolventCoeff ((truncation S).comp u) m - resolventCoeff u m‖ := by rw [opNorm_neg]
  _ ≤ c + ‖resolventCoeff ((truncation S).comp u) m - resolventCoeff u m‖ :=
        add_le_add (hbound S) le_rfl
  _ = ‖resolventCoeff ((truncation S).comp u) m - resolventCoeff u m‖ + c := add_comm _ _

/-- Truncation-limit step of Lemme 3 [Serre1962, §6 p. 79, step c)]: the resolvent
coefficients of the row-truncations converge to those of `u`. -/
theorem tendsto_resolventCoeff_truncation [IsTate R] (u : c(I, R) →L[R] c(I, R))
    (hu : IsCompactoid u) (m : ℕ) :
    Tendsto (fun S : Finset I =>
      ‖resolventCoeff ((truncation S).comp u) m - resolventCoeff u m‖) atTop (𝓝 0) :=
  tendsto_resolventCoeff_truncation' u hu m

/-- Threshold split (`δ / D / b`) for the products of `m` distinct row norms — the same
argument that makes `charPowerSeries_isEntire` work, for products instead of minors. -/
private theorem prod_rowNorm_le [IsTate R] (u : c(I, R) →L[R] c(I, R)) {δ D : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hD1 : (1 : ℝ) ≤ D) (hDu : ‖u‖ ≤ D)
    (hbad : {j : I | δ ≤ rowNorm u j}.Finite) (n : ℕ) (T : Finset I) (hT : T.card = n) :
    ∏ j ∈ T, rowNorm u j ≤ D ^ hbad.toFinset.card * δ ^ (n - hbad.toFinset.card) := by
  classical
  have hD0 : (0 : ℝ) < D := lt_of_lt_of_le one_pos hD1
  have hunion : ∏ j ∈ T, rowNorm u j
      = (∏ j ∈ T.filter (fun j => δ ≤ rowNorm u j), rowNorm u j)
        * ∏ j ∈ T.filter (fun j => ¬ δ ≤ rowNorm u j), rowNorm u j :=
    (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
  have hcb : (T.filter (fun j => δ ≤ rowNorm u j)).card ≤ hbad.toFinset.card := by
    refine Finset.card_le_card fun j hj => ?_
    rw [Finset.mem_filter] at hj
    exact hbad.mem_toFinset.2 hj.2
  have hcs : n - hbad.toFinset.card ≤ (T.filter (fun j => ¬ δ ≤ rowNorm u j)).card := by
    have hsplit : (T.filter (fun j => δ ≤ rowNorm u j)).card
        + (T.filter (fun j => ¬ δ ≤ rowNorm u j)).card = n := by
      rw [Finset.card_filter_add_card_filter_not, hT]
    omega
  rw [hunion]
  refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun j _ => rowNorm_nonneg u j)
    (pow_nonneg hD0.le _)
  · calc ∏ j ∈ T.filter (fun j => δ ≤ rowNorm u j), rowNorm u j
        ≤ ∏ _j ∈ T.filter (fun j => δ ≤ rowNorm u j), D :=
          Finset.prod_le_prod (fun j _ => rowNorm_nonneg u j)
            (fun j _ => (rowNorm_le_opNorm' u j).trans hDu)
    _ = D ^ (T.filter (fun j => δ ≤ rowNorm u j)).card := Finset.prod_const D
    _ ≤ D ^ hbad.toFinset.card := pow_le_pow_right₀ hD1 hcb
  · calc ∏ j ∈ T.filter (fun j => ¬ δ ≤ rowNorm u j), rowNorm u j
        ≤ ∏ _j ∈ T.filter (fun j => ¬ δ ≤ rowNorm u j), δ := by
          refine Finset.prod_le_prod (fun j _ => rowNorm_nonneg u j) fun j hj => ?_
          rw [Finset.mem_filter, not_le] at hj
          exact hj.2.le
    _ = δ ^ (T.filter (fun j => ¬ δ ≤ rowNorm u j)).card := Finset.prod_const δ
    _ ≤ δ ^ (n - hbad.toFinset.card) := pow_le_pow_of_le_one hδ0.le hδ1 hcs

/-- Serre's Proposition 10 [Serre1962, §6 p. 78]: the Fredholm resolvent is entire —
`‖vₘ‖ Mᵐ → 0` for every radius `M`. -/
theorem tendsto_norm_resolventCoeff [IsTate R] (u : c(I, R) →L[R] c(I, R))
    (hu : IsCompactoid u) (M : ℝ) :
    Tendsto (fun m => ‖resolventCoeff u m‖ * M ^ m) atTop (𝓝 0) := by
  set C : ℝ := max |M| 1 with hCdef
  have hC1 : (1 : ℝ) ≤ C := le_max_right _ _
  have hC : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  set δ : ℝ := min (1 / (2 * C)) 1 with hδdef
  have hδ0 : 0 < δ := lt_min (by positivity) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδC : δ * C ≤ 1 / 2 := by
    calc δ * C ≤ 1 / (2 * C) * C := mul_le_mul_of_nonneg_right (min_le_left _ _) hC.le
    _ = 1 / 2 := by field_simp
  set D : ℝ := max ‖u‖ 1 with hDdef
  have hD1 : (1 : ℝ) ≤ D := le_max_right _ _
  have hD0 : (0 : ℝ) < D := lt_of_lt_of_le one_pos hD1
  have hbad : {j : I | δ ≤ rowNorm u j}.Finite := by
    have hev : ∀ᶠ j in cofinite, rowNorm u j < δ := by
      filter_upwards [Metric.tendsto_nhds.1 hu δ hδ0] with j hj
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (rowNorm_nonneg u j)] at hj
    simpa only [not_lt] using Filter.eventually_cofinite.1 hev
  set b : ℕ := hbad.toFinset.card with hbdef
  have hres : ∀ n : ℕ, ‖resolventCoeff u n‖ ≤ D ^ b * δ ^ (n - b) := fun n =>
    (norm_resolventCoeff_le u hu n).trans
      (Real.iSup_le (fun T => prod_rowNorm_le u hδ0 hδ1 hD1 (le_max_left _ _) hbad n
        (T : Finset I) T.2)
        (mul_nonneg (pow_nonneg hD0.le _) (pow_nonneg hδ0.le _)))
  have hgeom : Tendsto (fun n : ℕ => (D / δ) ^ b * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    simpa using h2.const_mul ((D / δ) ^ b)
  have hmain : Tendsto (fun n : ℕ => ‖resolventCoeff u n‖ * C ^ n) atTop (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun n =>
      mul_nonneg (opNorm_nonneg _) (pow_nonneg hC.le n)) ?_ hgeom
    rw [Filter.eventually_atTop]
    refine ⟨b, fun n hn => ?_⟩
    have h1 : ‖resolventCoeff u n‖ * C ^ n ≤ D ^ b * δ ^ (n - b) * C ^ n :=
      mul_le_mul_of_nonneg_right (hres n) (pow_nonneg hC.le n)
    refine h1.trans ?_
    have hδn : δ ^ (n - b) = δ ^ n / δ ^ b := pow_sub₀ δ hδ0.ne' hn
    have hrew : D ^ b * (δ ^ n / δ ^ b) * C ^ n = (D / δ) ^ b * (δ * C) ^ n := by
      rw [div_pow, mul_pow]
      ring
    rw [hδn, hrew]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (div_nonneg hD0.le hδ0.le) b)
    exact pow_le_pow_left₀ (mul_nonneg hδ0.le hC.le) hδC n
  refine squeeze_zero_norm (fun n => ?_) hmain
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (opNorm_nonneg _), abs_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg M) (le_max_left _ _) n)
    (opNorm_nonneg _)

/-- The operator norm is itself ultrametric, because the target `c(I, R)` is.  This is what
replaces summability in the Cauchy estimate below: the summands of the divided evaluations
are null but not summable. -/
private theorem opNorm_add_le_max' [IsTate R] (w w' : c(I, R) →L[R] c(I, R)) :
    ‖w + w'‖ ≤ max ‖w‖ ‖w'‖ := by
  refine opNorm_le_of_forall _ (le_max_of_le_left (opNorm_nonneg w)) fun x => ?_
  show ‖w x + w' x‖ ≤ max ‖w‖ ‖w'‖ * ‖x‖
  refine (IsUltrametricDist.norm_add_le_max (w x) (w' x)).trans (max_le ?_ ?_)
  · exact (le_opNorm w x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x))
  · exact (le_opNorm w' x).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg x))

/-- Ultrametric bound for a finite sum of operators: a uniform bound on the summands bounds
the sum (contrast `opNorm_sum_le`, which needs the sum of the norms). -/
private theorem opNorm_sum_le_of_forall [IsTate R] {ι : Type*} {c : ℝ} (hc : 0 ≤ c)
    (f : ι → c(I, R) →L[R] c(I, R)) (t : Finset ι) (hf : ∀ i ∈ t, ‖f i‖ ≤ c) :
    ‖∑ i ∈ t, f i‖ ≤ c := by
  classical
  revert hf
  refine Finset.induction_on t ?_ ?_
  · intro _
    rw [Finset.sum_empty, opNorm_zero]
    exact hc
  · intro i t hi ih hf
    rw [Finset.sum_insert hi]
    exact (opNorm_add_le_max' _ _).trans (max_le (hf i (Finset.mem_insert_self _ _))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk)))

/-- Natural-number casts have norm at most `1` in an ultrametric normed ring.  (Stated
through `nsmul_eq_mul` rather than through `IsUltrametricDist.norm_natCast_le_one`, which
carries a `NormOneClass` side condition on a different form of the statement.) -/
private theorem norm_natCast_le_one' (k : ℕ) : ‖(k : R)‖ ≤ 1 := by
  rw [← mul_one (k : R), ← nsmul_eq_mul]
  exact (IsUltrametricDist.norm_nsmul_le (1 : R) k).trans_eq norm_one

/-- Scalar bound for the summands of the divided evaluations: `‖χ·b·aᵐ‖ ≤ ‖b‖·‖a‖ᵐ`. -/
private theorem norm_natCast_mul_mul_pow_le (k : ℕ) (b a : R) (m : ℕ) :
    ‖(k : R) * b * a ^ m‖ ≤ ‖b‖ * ‖a‖ ^ m := by
  calc ‖(k : R) * b * a ^ m‖ ≤ ‖(k : R) * b‖ * ‖a ^ m‖ := norm_mul_le _ _
  _ ≤ ‖(k : R)‖ * ‖b‖ * ‖a ^ m‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
  _ ≤ 1 * ‖b‖ * ‖a‖ ^ m :=
        mul_le_mul (mul_le_mul_of_nonneg_right (norm_natCast_le_one' k) (norm_nonneg b))
          (norm_pow_le a m) (norm_nonneg _) (by positivity)
  _ = ‖b‖ * ‖a‖ ^ m := by rw [one_mul]

/-- Operator bound for the summands of the divided evaluations: `‖χ • aᵐ • w‖ ≤ ‖w‖·‖a‖ᵐ`. -/
private theorem norm_natCast_smul_pow_smul_le [IsTate R] (k m : ℕ) (a : R)
    (w : c(I, R) →L[R] c(I, R)) : ‖(k : R) • a ^ m • w‖ ≤ ‖w‖ * ‖a‖ ^ m := by
  calc ‖(k : R) • a ^ m • w‖ ≤ ‖(k : R)‖ * ‖a ^ m • w‖ := opNorm_smul_le' _ _
  _ ≤ 1 * (‖a ^ m‖ * ‖w‖) :=
        mul_le_mul (norm_natCast_le_one' k) (opNorm_smul_le' _ _) (opNorm_nonneg _) zero_le_one
  _ ≤ 1 * (‖a‖ ^ m * ‖w‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (norm_pow_le a m) (opNorm_nonneg w)) zero_le_one
  _ = ‖w‖ * ‖a‖ ^ m := by rw [one_mul, mul_comm]

/-- Scalars against the identity: `‖b • 1‖ ≤ ‖b‖` (`opNorm_one_le`-scaled). -/
private theorem opNorm_smul_one_le [IsTate R] (b : R) :
    ‖b • (1 : c(I, R) →L[R] c(I, R))‖ ≤ ‖b‖ := by
  refine (opNorm_smul_le' _ _).trans ?_
  simpa using mul_le_mul_of_nonneg_left opNorm_one_le (norm_nonneg b)

/-- Shifting the index does not change an operator-norm limit. -/
private theorem isOpLimit_shift [IsTate R] {T : ℕ → c(I, R) →L[R] c(I, R)}
    {L : c(I, R) →L[R] c(I, R)} (h : IsOpLimit T L) (k : ℕ) :
    IsOpLimit (fun n => T (n + k)) L := by
  have h' : Tendsto (fun n => ‖T n - L‖) atTop (𝓝 0) := h
  have h'' := h'.comp (tendsto_add_atTop_nat k)
  exact h''

/-- Congruence for operator-norm limits along a pointwise-equal sequence. -/
private theorem isOpLimit_congr [IsTate R] {T T' : ℕ → c(I, R) →L[R] c(I, R)}
    {L : c(I, R) →L[R] c(I, R)} (h : IsOpLimit T L) (hTT' : ∀ n, T n = T' n) :
    IsOpLimit T' L := by
  show Tendsto (fun n => ‖T' n - L‖) atTop (𝓝 0)
  have h' : Tendsto (fun n => ‖T n - L‖) atTop (𝓝 0) := h
  exact Filter.Tendsto.congr (fun n => by rw [hTT' n]) h'

/-- Domination by a null real sequence forces the operator-norm limit `0`. -/
private theorem isOpLimit_zero_of_le [IsTate R] {T : ℕ → c(I, R) →L[R] c(I, R)} {g : ℕ → ℝ}
    (hg : Tendsto g atTop (𝓝 0)) (h : ∀ n, ‖T n‖ ≤ g n) : IsOpLimit T 0 := by
  refine squeeze_zero (fun n => opNorm_nonneg _) (fun n => ?_) hg
  rw [sub_zero]
  exact h n

/-- Scalar limits become operator-norm limits after `• 1`. -/
private theorem isOpLimit_smul_one [IsTate R] {S : ℕ → R} {L : R}
    (h : Tendsto S atTop (𝓝 L)) :
    IsOpLimit (fun n => S n • (1 : c(I, R) →L[R] c(I, R))) (L • 1) := by
  have hnorm : Tendsto (fun n => ‖S n - L‖) atTop (𝓝 0) := by
    simpa using (h.sub_const L).norm
  refine squeeze_zero (fun n => opNorm_nonneg _) (fun n => ?_) hnorm
  rw [← sub_smul]
  exact opNorm_smul_one_le _

/-- The partial sums of the `s`-th divided evaluation `Nₛ = (Δˢ P)(a, u)` of the
resolvent. -/
def resolventPartialSum (u : c(I, R) →L[R] c(I, R)) (a : R) (s n : ℕ) :
    c(I, R) →L[R] c(I, R) :=
  ∑ m ∈ Finset.range n, ((m + s).choose s : R) • a ^ m • resolventCoeff u (m + s)

private theorem resolventPartialSum_succ (u : c(I, R) →L[R] c(I, R)) (a : R) (s n : ℕ) :
    resolventPartialSum u a s (n + 1)
      = resolventPartialSum u a s n + ((n + s).choose s : R) • a ^ n • resolventCoeff u (n + s) :=
  Finset.sum_range_succ _ n

private theorem resolventPartialSum_one (u : c(I, R) →L[R] c(I, R)) (a : R) (s : ℕ) :
    resolventPartialSum u a s 1 = resolventCoeff u s := by
  rw [resolventPartialSum, Finset.sum_range_one, Nat.zero_add, Nat.choose_self, Nat.cast_one,
    pow_zero, one_smul, one_smul]

/-- Solved form of Serre's recursion: `u vₘ = vₘ₊₁ − cₘ₊₁·1`. -/
private theorem mul_resolventCoeff (u : c(I, R) →L[R] c(I, R)) (m : ℕ) :
    u * resolventCoeff u m = resolventCoeff u (m + 1) - charCoeff u (m + 1) • 1 := by
  rw [← resolventCoeff_sub_mul u m]
  abel

/-- Existence of the divided evaluations `Nₛ` of the resolvent (operator-norm limits of
the partial sums), from entireness and ultrametric Cauchyness. -/
theorem exists_isOpLimit_resolventPartialSum [IsTate R] (u : c(I, R) →L[R] c(I, R))
    (hu : IsCompactoid u) (a : R) (s : ℕ) :
    ∃ N : c(I, R) →L[R] c(I, R), IsOpLimit (resolventPartialSum u a s) N := by
  set C : ℝ := max ‖a‖ 1 with hCdef
  have hC1 : (1 : ℝ) ≤ C := le_max_right _ _
  have haC : ‖a‖ ≤ C := le_max_left _ _
  have hterm : Tendsto
      (fun m => ‖((m + s).choose s : R) • a ^ m • resolventCoeff u (m + s)‖) atTop (𝓝 0) := by
    have hbase : Tendsto (fun m => ‖resolventCoeff u (m + s)‖ * C ^ (m + s)) atTop (𝓝 0) :=
      Filter.Tendsto.comp (tendsto_norm_resolventCoeff u hu C) (tendsto_add_atTop_nat s)
    refine squeeze_zero (fun m => opNorm_nonneg _) (fun m => ?_) hbase
    refine (norm_natCast_smul_pow_smul_le _ _ _ _).trans
      (mul_le_mul_of_nonneg_left ?_ (opNorm_nonneg _))
    exact (pow_le_pow_left₀ (norm_nonneg a) haC m).trans
      (pow_le_pow_right₀ hC1 (Nat.le_add_right m s))
  refine exists_lim_of_cauchySeq _ fun ε hε => ?_
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp (hterm.eventually_lt_const (half_pos hε))
  have key : ∀ p q, M₀ ≤ p → p ≤ q →
      ‖resolventPartialSum u a s q - resolventPartialSum u a s p‖ ≤ ε / 2 := by
    intro p q hp hpq
    simp only [resolventPartialSum]
    rw [← Finset.sum_Ico_eq_sub _ hpq]
    exact opNorm_sum_le_of_forall (half_pos hε).le _ _
      fun m hm => (hM₀ m (hp.trans (Finset.mem_Ico.mp hm).1)).le
  refine ⟨M₀, fun p q hp hq => ?_⟩
  rcases le_total p q with h | h
  · rw [opNorm_sub_comm]
    exact (key p q hp h).trans_lt (half_lt_self hε)
  · exact (key q p hq h).trans_lt (half_lt_self hε)

/-- The divided evaluations commute with `u` (they are limits of polynomials in `u`). -/
theorem commute_of_isOpLimit_resolventPartialSum [IsTate R]
    {u : c(I, R) →L[R] c(I, R)} {a : R} {s : ℕ} {N : c(I, R) →L[R] c(I, R)}
    (hN : IsOpLimit (resolventPartialSum u a s) N) :
    u * N = N * u := by
  have hpow : ∀ (b : R) (p : ℕ), u * (b • u ^ p) = (b • u ^ p) * u := fun b p => by
    rw [mul_smul_comm, smul_mul_assoc, ← pow_succ', ← pow_succ]
  have hres : ∀ m, u * resolventCoeff u m = resolventCoeff u m * u := fun m => by
    rw [resolventCoeff, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => hpow _ _
  have hpart : ∀ n, u * resolventPartialSum u a s n
      = resolventPartialSum u a s n * u := fun n => by
    rw [resolventPartialSum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, hres]
  refine (hN.comp_left u).unique ?_
  rw [show (fun n => u * resolventPartialSum u a s n)
      = fun n => resolventPartialSum u a s n * u from funext hpart]
  exact hN.comp_right u

private theorem resolventPartialSum_zero_succ (u : c(I, R) →L[R] c(I, R)) (a : R) (n : ℕ) :
    resolventPartialSum u a 0 (n + 1)
      = resolventPartialSum u a 0 n + a ^ n • resolventCoeff u n := by
  rw [resolventPartialSum_succ, Nat.add_zero, Nat.choose_zero_right, Nat.cast_one, one_smul]

/-- Finite (unevaluated) form of `(1 - tu)·P(t, u) = H(t)` at `t = a`: the partial sums
telescope, up to the single boundary term `aⁿ·vₙ`. -/
private theorem one_sub_smul_mul_resolventPartialSum_zero [IsTate R]
    (u : c(I, R) →L[R] c(I, R)) (a : R) (n : ℕ) :
    (1 - a • u) * resolventPartialSum u a 0 n
      = (∑ j ∈ Finset.range (n + 1), charCoeff u j * a ^ j) • 1
        - a ^ n • resolventCoeff u n := by
  induction n with
  | zero =>
      rw [resolventPartialSum, Finset.range_zero, Finset.sum_empty, mul_zero,
        Finset.sum_range_one, resolventCoeff_zero, charCoeff_zero, pow_zero, mul_one, one_smul,
        sub_self]
  | succ n ih =>
      rw [resolventPartialSum_zero_succ, mul_add, ih]
      simp only [Finset.sum_range_succ, sub_mul, one_mul, smul_mul_assoc, mul_smul_comm,
        mul_resolventCoeff]
      module

/-- Finite (unevaluated) form of Serre's `Δˢ`-equation for `s = t + 1 ≥ 1`.  Applying
`(1 - a•u)` to the `s`-th partial sum and using the recursion `u vₘ = vₘ₊₁ − cₘ₊₁·1` twice,
the two families of binomial coefficients recombine by Pascal's rule
`C(n+t+2, t+1) = C(n+t+1, t+1) + C(n+t+1, t)`, leaving the `(s-1)`-st partial sum, the
partial sums of `ΔˢH` and two boundary terms. -/
private theorem one_sub_smul_mul_resolventPartialSum_succ [IsTate R]
    (u : c(I, R) →L[R] c(I, R)) (a : R) (t n : ℕ) :
    (1 - a • u) * resolventPartialSum u a (t + 1) (n + 1)
      = u * resolventPartialSum u a t (n + 1)
        + (∑ m ∈ Finset.range (n + 1),
            ((m + t + 1).choose (t + 1) : R) * charCoeff u (m + t + 1) * a ^ m) • 1
        + (((n + t + 1).choose (t + 1) : R) * charCoeff u (n + t + 2) * a ^ (n + 1)) • 1
        - ((n + t + 1).choose (t + 1) : R) • a ^ (n + 1) • resolventCoeff u (n + t + 2) := by
  induction n with
  | zero =>
      have hv0 : u * resolventCoeff u t
          = resolventCoeff u (t + 1) - charCoeff u (t + 1) • 1 := mul_resolventCoeff u t
      have hv1 : u * resolventCoeff u (t + 1)
          = resolventCoeff u (t + 2) - charCoeff u (t + 2) • 1 := mul_resolventCoeff u (t + 1)
      simp only [Nat.zero_add, Finset.sum_range_one, resolventPartialSum_one, Nat.choose_self,
        Nat.cast_one, pow_zero, pow_one, one_mul, mul_one, one_smul]
      simp only [sub_mul, one_mul, smul_mul_assoc, hv0, hv1]
      module
  | succ n ih =>
      have hP1 : resolventPartialSum u a (t + 1) (n + 1 + 1)
          = resolventPartialSum u a (t + 1) (n + 1)
            + ((n + t + 2).choose (t + 1) : R) • a ^ (n + 1) • resolventCoeff u (n + t + 2) := by
        rw [resolventPartialSum_succ, show n + 1 + (t + 1) = n + t + 2 from by omega]
      have hP2 : resolventPartialSum u a t (n + 1 + 1)
          = resolventPartialSum u a t (n + 1)
            + ((n + t + 1).choose t : R) • a ^ (n + 1) • resolventCoeff u (n + t + 1) := by
        rw [resolventPartialSum_succ, show n + 1 + t = n + t + 1 from by omega]
      have hpascal : ((n + t + 2).choose (t + 1) : R)
          = ((n + t + 1).choose (t + 1) : R) + ((n + t + 1).choose t : R) := by
        rw [show n + t + 2 = n + t + 1 + 1 from rfl, Nat.choose_succ_succ' (n + t + 1) t]
        push_cast
        ring
      have hv1 : u * resolventCoeff u (n + t + 1)
          = resolventCoeff u (n + t + 2) - charCoeff u (n + t + 2) • 1 :=
        mul_resolventCoeff u (n + t + 1)
      have hv2 : u * resolventCoeff u (n + t + 2)
          = resolventCoeff u (n + t + 3) - charCoeff u (n + t + 3) • 1 :=
        mul_resolventCoeff u (n + t + 2)
      rw [hP1, hP2, Finset.sum_range_succ, mul_add, mul_add, ih,
        show n + 1 + t + 1 = n + t + 2 from by omega,
        show n + 1 + t + 2 = n + t + 3 from by omega, hpascal]
      simp only [sub_mul, one_mul, smul_mul_assoc, mul_smul_comm, hv1, hv2]
      module

/-- Serre's evaluated identity at `s = 0`: `(1 - a•u) N₀ = H(a)·1` [Serre1962, §7
p. 80, from `(1-tu)P(t,u) = H(t)` at `t = a`]. -/
theorem one_sub_smul_mul_resolventEval_zero [IsTate R]
    {u : c(I, R) →L[R] c(I, R)} (hu : IsCompactoid u) {a : R}
    {N : c(I, R) →L[R] c(I, R)} (hN : IsOpLimit (resolventPartialSum u a 0) N) :
    (1 - a • u) * N = PowerSeries.evalT a (charPowerSeries u) • 1 := by
  set C : ℝ := max ‖a‖ 1 with hCdef
  have hC1 : (1 : ℝ) ≤ C := le_max_right _ _
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  have haC : ‖a‖ ≤ C := le_max_left _ _
  have hHres : PowerSeries.IsRestricted C (charPowerSeries u) :=
    charPowerSeries_isEntire u hu C hC0
  have hsum : Summable fun m => PowerSeries.coeff m (charPowerSeries u) * a ^ m :=
    PowerSeries.summable_coeff_mul_pow
      (PowerSeries.tendsto_norm_coeff_mul_pow_of_isRestricted hHres haC)
  have hSc : Tendsto (fun n => ∑ j ∈ Finset.range (n + 1), charCoeff u j * a ^ j) atTop
      (𝓝 (PowerSeries.evalT a (charPowerSeries u))) := by
    have hco : ∀ j : ℕ, charCoeff u j * a ^ j
        = PowerSeries.coeff j (charPowerSeries u) * a ^ j := fun j => by
      rw [charPowerSeries_coeff]
    simp only [hco]
    have h1 := hsum.hasSum.tendsto_sum_nat
    have h2 := h1.comp (tendsto_add_atTop_nat 1)
    exact h2
  have hR2 := isOpLimit_smul_one (I := I) hSc
  have hR3 : IsOpLimit (fun n => -(a ^ n • resolventCoeff u n)) 0 := by
    refine isOpLimit_zero_of_le (tendsto_norm_resolventCoeff u hu C) fun n => ?_
    calc ‖-(a ^ n • resolventCoeff u n)‖ = ‖a ^ n • resolventCoeff u n‖ := opNorm_neg _
    _ ≤ ‖a ^ n‖ * ‖resolventCoeff u n‖ := opNorm_smul_le' _ _
    _ ≤ C ^ n * ‖resolventCoeff u n‖ :=
          mul_le_mul_of_nonneg_right ((norm_pow_le a n).trans
            (pow_le_pow_left₀ (norm_nonneg a) haC n)) (opNorm_nonneg _)
    _ = ‖resolventCoeff u n‖ * C ^ n := mul_comm _ _
  have hcomb := hR2.add hR3
  rw [add_zero] at hcomb
  refine (hN.comp_left (1 - a • u)).unique (isOpLimit_congr hcomb fun n => ?_)
  rw [one_sub_smul_mul_resolventPartialSum_zero]
  abel

/-- Serre's evaluated identities: `(1 - a•u) Nₛ = u N_{s-1} + (ΔˢH)(a)·1` [Serre1962,
§7 pp. 80–81: "En lui appliquant l'opérateur Δˢ"]. -/
theorem one_sub_smul_mul_resolventEval [IsTate R]
    {u : c(I, R) →L[R] c(I, R)} (hu : IsCompactoid u) {a : R} {s : ℕ} (hs : 1 ≤ s)
    {N N' : c(I, R) →L[R] c(I, R)}
    (hN : IsOpLimit (resolventPartialSum u a s) N)
    (hN' : IsOpLimit (resolventPartialSum u a (s - 1)) N') :
    (1 - a • u) * N =
      u * N' + PowerSeries.evalT a (PowerSeries.hasseDeriv s (charPowerSeries u)) • 1 := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hN'
  set C : ℝ := max ‖a‖ 1 with hCdef
  have hC1 : (1 : ℝ) ≤ C := le_max_right _ _
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  have haC : ‖a‖ ≤ C := le_max_left _ _
  have hHres : PowerSeries.IsRestricted C (charPowerSeries u) :=
    charPowerSeries_isEntire u hu C hC0
  have hDres : PowerSeries.IsRestricted C
      (PowerSeries.hasseDeriv (t + 1) (charPowerSeries u)) :=
    PowerSeries.isRestricted_hasseDeriv hC0 hHres (t + 1)
  have hsum : Summable fun m => PowerSeries.coeff m
      (PowerSeries.hasseDeriv (t + 1) (charPowerSeries u)) * a ^ m :=
    PowerSeries.summable_coeff_mul_pow
      (PowerSeries.tendsto_norm_coeff_mul_pow_of_isRestricted hDres haC)
  -- the scalar side: partial sums of `ΔˢH` at `a`
  have hSc : Tendsto (fun n => ∑ m ∈ Finset.range (n + 1),
      ((m + t + 1).choose (t + 1) : R) * charCoeff u (m + t + 1) * a ^ m) atTop
      (𝓝 (PowerSeries.evalT a (PowerSeries.hasseDeriv (t + 1) (charPowerSeries u)))) := by
    have hco : ∀ m : ℕ, ((m + t + 1).choose (t + 1) : R) * charCoeff u (m + t + 1) * a ^ m
        = PowerSeries.coeff m (PowerSeries.hasseDeriv (t + 1) (charPowerSeries u)) * a ^ m :=
      fun m => by rw [PowerSeries.coeff_hasseDeriv, charPowerSeries_coeff]; rfl
    simp only [hco]
    have h1 := hsum.hasSum.tendsto_sum_nat
    have h2 := h1.comp (tendsto_add_atTop_nat 1)
    exact h2
  -- the two boundary terms vanish
  have hcC : Tendsto (fun n => ‖charCoeff u (n + t + 2)‖ * C ^ (n + t + 2)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun m => ‖charCoeff u m‖ * C ^ m) atTop (𝓝 0) := by
      simpa using (PowerSeries.isRestricted_iff' C (charPowerSeries u)).mp hHres
    have h1 := h0.comp (tendsto_add_atTop_nat (t + 2))
    exact h1
  have hvC : Tendsto (fun n => ‖resolventCoeff u (n + t + 2)‖ * C ^ (n + t + 2)) atTop (𝓝 0) := by
    have h1 := (tendsto_norm_resolventCoeff u hu C).comp (tendsto_add_atTop_nat (t + 2))
    exact h1
  have hpow : ∀ n : ℕ, ‖a‖ ^ (n + 1) ≤ C ^ (n + t + 2) :=
    fun n => (pow_le_pow_left₀ (norm_nonneg a) haC (n + 1)).trans
      (pow_le_pow_right₀ hC1 (by omega))
  have hR3 : IsOpLimit (fun n => (((n + t + 1).choose (t + 1) : R) *
      charCoeff u (n + t + 2) * a ^ (n + 1)) • (1 : c(I, R) →L[R] c(I, R))) 0 := by
    refine isOpLimit_zero_of_le hcC fun n => ?_
    exact ((opNorm_smul_one_le _).trans (norm_natCast_mul_mul_pow_le _ _ _ _)).trans
      (mul_le_mul_of_nonneg_left (hpow n) (norm_nonneg _))
  have hR4 : IsOpLimit (fun n => -(((n + t + 1).choose (t + 1) : R) • a ^ (n + 1) •
      resolventCoeff u (n + t + 2))) 0 := by
    refine isOpLimit_zero_of_le hvC fun n => ?_
    rw [opNorm_neg]
    exact (norm_natCast_smul_pow_smul_le _ _ _ _).trans
      (mul_le_mul_of_nonneg_left (hpow n) (opNorm_nonneg _))
  -- pass to the limit in the finite identity
  have hL : IsOpLimit (fun n => (1 - a • u) * resolventPartialSum u a (t + 1) (n + 1))
      ((1 - a • u) * N) := isOpLimit_shift (hN.comp_left (1 - a • u)) 1
  have hR1 : IsOpLimit (fun n => u * resolventPartialSum u a t (n + 1)) (u * N') :=
    isOpLimit_shift (hN'.comp_left u) 1
  have hcomb := ((hR1.add (isOpLimit_smul_one (I := I) hSc)).add hR3).add hR4
  rw [add_zero, add_zero] at hcomb
  refine hL.unique (isOpLimit_congr hcomb fun n => ?_)
  rw [one_sub_smul_mul_resolventPartialSum_succ]
  abel

end Resolvent

section DetValue

/-- The Fredholm determinant value `det(1 - u) := H_u(1)` of a compactoid operator
[Serre1962, §5 p. 76: "det(1+u) est défini pour tout u"]. -/
def fredholmDet (u : c(I, R) →L[R] c(I, R)) : R :=
  PowerSeries.evalT 1 (charPowerSeries u)

/-- Scaling of the characteristic coefficients: `cₙ(a•u) = aⁿ cₙ(u)` (the minors are
`n`-linear in the rows). -/
theorem charCoeff_smul [IsTate R] (a : R) (u : c(I, R) →L[R] c(I, R))
    (hu : IsCompactoid u) (n : ℕ) :
    charCoeff (a • u) n = a ^ n * charCoeff u n := by
  have hminor : ∀ S : {S : Finset I // S.card = n},
      minor (a • u) (S : Finset I) = a ^ n * minor u (S : Finset I) := by
    intro S
    have hmat : (Matrix.of fun j i : (S : Finset I) => matrixCoeff (a • u) (j : I) (i : I))
        = a • Matrix.of fun j i : (S : Finset I) => matrixCoeff u (j : I) (i : I) :=
      Matrix.ext fun _ _ => rfl
    rw [show minor (a • u) (S : Finset I)
          = Matrix.det (Matrix.of fun j i : (S : Finset I) => matrixCoeff (a • u) (j : I) (i : I))
          from rfl,
      show minor u (S : Finset I)
          = Matrix.det (Matrix.of fun j i : (S : Finset I) => matrixCoeff u (j : I) (i : I))
          from rfl,
      hmat, Matrix.det_smul, Fintype.card_coe, S.2]
  rw [charCoeff, charCoeff, tsum_congr hminor, (summable_minor u hu n).tsum_mul_left]
  ring

/-- `det(1 - a•u) = H_u(a)`: the determinant value of the rescaled operator is the
evaluation of the characteristic power series. -/
theorem fredholmDet_smul [IsTate R] (a : R) (u : c(I, R) →L[R] c(I, R))
    (hu : IsCompactoid u) :
    fredholmDet (a • u) = PowerSeries.evalT a (charPowerSeries u) := by
  rw [fredholmDet, PowerSeries.evalT, PowerSeries.evalT]
  refine tsum_congr fun n => ?_
  rw [charPowerSeries_coeff, charPowerSeries_coeff, charCoeff_smul a u hu n, one_pow, mul_one,
    mul_comm]

/-- The determinant value of a row-supported operator is the determinant of its finite
block. -/
theorem fredholmDet_eq_det_of_rows (u : c(I, R) →L[R] c(I, R)) (S : Finset I)
    (hS : ∀ j ∉ S, ∀ i, matrixCoeff u j i = 0) :
    fredholmDet u = Matrix.det (1 - Matrix.of fun j i : S => matrixCoeff u j i) := by
  classical
  obtain ⟨p, hp⟩ : ∃ p : Polynomial R, p = Matrix.det (1 - (Polynomial.X : Polynomial R) •
      Matrix.of fun j i : S => Polynomial.C (matrixCoeff u j i)) := ⟨_, rfl⟩
  have hcoeff : ∀ n, charCoeff u n = p.coeff n := by
    intro n
    rw [hp]
    exact charCoeff_eq_det_coeff u S hS n
  -- minors over more than `S.card` rows have a zero row, so the coefficients stop
  have hvanish : ∀ n, S.card < n → charCoeff u n = 0 := by
    intro n hn
    have hz : ∀ T : {T : Finset I // T.card = n}, minor u (T : Finset I) = 0 := by
      intro T
      have hnsub : ¬ ((T : Finset I) ⊆ S) := by
        intro hsub
        have hcard := Finset.card_le_card hsub
        rw [T.2] at hcard
        omega
      obtain ⟨j, hjT, hjS⟩ := Finset.not_subset.1 hnsub
      rw [show minor u (T : Finset I)
            = Matrix.det (Matrix.of fun j i : (T : Finset I) => matrixCoeff u (j : I) (i : I))
            from rfl]
      exact Matrix.det_eq_zero_of_row_eq_zero (⟨j, hjT⟩ : {x // x ∈ (T : Finset I)})
        fun i => hS j hjS _
    rw [charCoeff, tsum_congr hz, tsum_zero, mul_zero]
  have hdeg : p.natDegree < S.card + 1 := by
    refine Nat.lt_succ_of_le (Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun N hN => ?_)
    rw [← hcoeff N]
    exact hvanish N hN
  have hev : Polynomial.eval (1 : R) p
      = Matrix.det (1 - Matrix.of fun j i : S => matrixCoeff u j i) := by
    have hmat : (Polynomial.evalRingHom (1 : R)).mapMatrix
        (1 - (Polynomial.X : Polynomial R) •
          Matrix.of fun j i : S => Polynomial.C (matrixCoeff u j i))
        = 1 - Matrix.of fun j i : S => matrixCoeff u j i := by
      refine Matrix.ext fun x y => ?_
      rw [RingHom.mapMatrix_apply, Matrix.map_apply]
      by_cases hxy : x = y
      · subst hxy
        simp
      · simp [Matrix.one_apply_ne hxy]
    have h1 : Polynomial.eval (1 : R) p = (Polynomial.evalRingHom (1 : R)) p := rfl
    rw [h1, hp, RingHom.map_det, hmat]
  have hfd : fredholmDet u = ∑ n ∈ Finset.range (S.card + 1), p.coeff n * (1 : R) ^ n := by
    rw [fredholmDet, PowerSeries.evalT, tsum_eq_sum (s := Finset.range (S.card + 1)) ?_]
    · exact Finset.sum_congr rfl fun n _ => by rw [charPowerSeries_coeff, hcoeff n]
    · intro n hn
      rw [Finset.mem_range, not_lt] at hn
      rw [charPowerSeries_coeff, hvanish n (by omega), zero_mul]
  rw [hfd, ← Polynomial.eval_eq_sum_range' hdeg (1 : R), hev]

/-- Composition of operators has the matrix-product coefficients when the inner factor
is row-supported. -/
theorem matrixCoeff_mul_of_rows (u v : c(I, R) →L[R] c(I, R)) (S : Finset I)
    (hv : ∀ j ∉ S, ∀ i, matrixCoeff v j i = 0) (j i : I) :
    matrixCoeff (u * v) j i = ∑ k ∈ S, matrixCoeff u j k * matrixCoeff v k i := by
  have h1 : v (cSpace.single i 1) = ∑ k ∈ S, matrixCoeff v k i • cSpace.single k (1 : R) :=
    HasSum.unique (cSpace.hasSum_single _)
      (hasSum_sum_of_ne_finset_zero fun k hk =>
        show matrixCoeff v k i • cSpace.single k (1 : R) = 0 by rw [hv k hk, zero_smul])
  have h2 : matrixCoeff (u * v) j i = cSpace.evalCLM j (u (v (cSpace.single i 1))) := rfl
  rw [h2, h1, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, map_smul, smul_eq_mul, mul_comm]
  rfl

/-- Threshold split (`δ / D / b`) for a product of nonnegative row bounds over an arbitrary
index type: at most `b` factors exceed `δ` and all are `≤ D`, so a product over a set with at
least `k` elements is `≤ Dᵇ δ^{k−b}`.  The abstract form of `prod_rowNorm_le`, needed for the
`↥T`-indexed products produced by `norm_det_sub_det_le'`. -/
private theorem prod_le_of_threshold {n : Type*} {g : n → ℝ} (hg0 : ∀ j, 0 ≤ g j)
    {δ D : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hD1 : (1 : ℝ) ≤ D) (hgD : ∀ j, g j ≤ D)
    (P : n → Prop) [DecidablePred P] (hgδ : ∀ j, ¬ P j → g j ≤ δ) (s : Finset n) {b k : ℕ}
    (hb : (s.filter P).card ≤ b) (hk : k ≤ s.card) :
    ∏ j ∈ s, g j ≤ D ^ b * δ ^ (k - b) := by
  have hD0 : (0 : ℝ) < D := lt_of_lt_of_le one_pos hD1
  have hunion : ∏ j ∈ s, g j
      = (∏ j ∈ s.filter P, g j) * ∏ j ∈ s.filter (fun j => ¬ P j), g j :=
    (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
  have hsplit : (s.filter P).card + (s.filter (fun j => ¬ P j)).card = s.card := by
    rw [Finset.card_filter_add_card_filter_not]
  have hcs : k - b ≤ (s.filter (fun j => ¬ P j)).card := by omega
  rw [hunion]
  refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun j _ => hg0 j) (pow_nonneg hD0.le _)
  · calc ∏ j ∈ s.filter P, g j ≤ ∏ _j ∈ s.filter P, D :=
          Finset.prod_le_prod (fun j _ => hg0 j) (fun j _ => hgD j)
      _ = D ^ (s.filter P).card := Finset.prod_const D
      _ ≤ D ^ b := pow_le_pow_right₀ hD1 hb
  · calc ∏ j ∈ s.filter (fun j => ¬ P j), g j ≤ ∏ _j ∈ s.filter (fun j => ¬ P j), δ :=
          Finset.prod_le_prod (fun j _ => hg0 j)
            (fun j hj => hgδ j (Finset.mem_filter.1 hj).2)
      _ = δ ^ (s.filter (fun j => ¬ P j)).card := Finset.prod_const δ
      _ ≤ δ ^ (k - b) := pow_le_pow_of_le_one hδ0.le hδ1 hcs

/-- **Row-telescoping bound with per-row bounds** — Serre's "somme de produits de
différences" [Serre1962, §5 p. 77].  Swapping the rows of `B` for those of `A` one at a
time, each step is a determinant with a single `(A − B)`-row, hence bounded by `ε` times
the product of the *remaining* row bounds.  This refines `norm_det_sub_det_le`
(private in `Fredholm.lean`), whose uniform bound `max ‖u‖ ‖v‖ ^ (m−1)` diverges at
radius `M ≥ 1` and is therefore insufficient for Proposition 8. -/
private theorem norm_det_sub_det_le' {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n R) (f : n → ℝ) {ε c : ℝ} (hε : 0 ≤ ε) (hc : 0 ≤ c)
    (hA : ∀ p q, ‖A p q‖ ≤ f p) (hB : ∀ p q, ‖B p q‖ ≤ f p)
    (hAB : ∀ p q, ‖A p q - B p q‖ ≤ ε)
    (hprod : ∀ p : n, ∏ q ∈ Finset.univ.erase p, f q ≤ c) :
    ‖A.det - B.det‖ ≤ ε * c := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card n) with hcard | hcard
  · haveI : IsEmpty n := Fintype.card_eq_zero_iff.1 hcard
    rw [Matrix.det_isEmpty, Matrix.det_isEmpty, sub_self, norm_zero]
    exact mul_nonneg hε hc
  set m : ℕ := Fintype.card n
  obtain ⟨e⟩ : Nonempty (Fin m ≃ n) := ⟨(Fintype.equivFin n).symm⟩
  -- the hybrid matrices: rows enumerated before `t` come from `A`, the rest from `B`
  set H : ℕ → Matrix n n R :=
    fun t => Matrix.of fun p q => if ((e.symm p : Fin m) : ℕ) < t then A p q else B p q
  have hH0 : H 0 = B := by
    ext p q
    show (if ((e.symm p : Fin m) : ℕ) < 0 then A p q else B p q) = B p q
    exact if_neg (Nat.not_lt_zero _)
  have hHm : H m = A := by
    ext p q
    show (if ((e.symm p : Fin m) : ℕ) < m then A p q else B p q) = A p q
    exact if_pos (e.symm p).2
  have htele : A.det - B.det = ∑ t ∈ Finset.range m, ((H (t + 1)).det - (H t).det) := by
    rw [Finset.sum_range_sub (fun t => (H t).det), hH0, hHm]
  rw [htele]
  have hne : (Finset.range m).Nonempty := ⟨0, Finset.mem_range.2 hcard⟩
  refine (hne.norm_sum_le_sup'_norm _).trans ((Finset.sup'_le _ _) fun t ht => ?_)
  rw [Finset.mem_range] at ht
  -- the two hybrids differ in row `e t` only
  have hupdate : H (t + 1) = (H t).updateRow (e ⟨t, ht⟩) fun q => A (e ⟨t, ht⟩) q := by
    ext p q
    rw [Matrix.updateRow_apply]
    by_cases hp : p = e ⟨t, ht⟩
    · subst hp
      rw [if_pos rfl]
      show (if ((e.symm (e ⟨t, ht⟩) : Fin m) : ℕ) < t + 1 then A _ q else B _ q) = A _ q
      rw [Equiv.symm_apply_apply]
      exact if_pos (Nat.lt_succ_self t)
    · rw [if_neg hp]
      show (if ((e.symm p : Fin m) : ℕ) < t + 1 then A p q else B p q)
        = (if ((e.symm p : Fin m) : ℕ) < t then A p q else B p q)
      have hne' : ((e.symm p : Fin m) : ℕ) ≠ t := fun h => by
        refine hp ?_
        have heq : e.symm p = ⟨t, ht⟩ := Fin.ext h
        rw [← heq, Equiv.apply_symm_apply]
      by_cases hc' : ((e.symm p : Fin m) : ℕ) < t
      · rw [if_pos (Nat.lt_succ_of_lt hc'), if_pos hc']
      · have hnot : ¬ ((e.symm p : Fin m) : ℕ) < t + 1 := fun h =>
          hc' (lt_of_le_of_ne (Nat.lt_succ_iff.1 h) hne')
        rw [if_neg hnot, if_neg hc']
  -- row `e t` of `H t` is the `B`-row, so the difference is a single-row determinant
  have hBrow : H t = (H t).updateRow (e ⟨t, ht⟩) fun q => B (e ⟨t, ht⟩) q := by
    ext p q
    rw [Matrix.updateRow_apply]
    by_cases hp : p = e ⟨t, ht⟩
    · subst hp
      rw [if_pos rfl]
      show (if ((e.symm (e ⟨t, ht⟩) : Fin m) : ℕ) < t then A _ q else B _ q) = B _ q
      rw [Equiv.symm_apply_apply]
      exact if_neg (lt_irrefl t)
    · rw [if_neg hp]
  have hdiff : (H (t + 1)).det - (H t).det
      = ((H t).updateRow (e ⟨t, ht⟩) fun q =>
          A (e ⟨t, ht⟩) q - B (e ⟨t, ht⟩) q).det := by
    have hadd := Matrix.det_updateRow_add (H t) (e ⟨t, ht⟩)
      (fun q => A (e ⟨t, ht⟩) q - B (e ⟨t, ht⟩) q) (fun q => B (e ⟨t, ht⟩) q)
    have hfun : (fun q => A (e ⟨t, ht⟩) q - B (e ⟨t, ht⟩) q)
        + (fun q => B (e ⟨t, ht⟩) q) = fun q => A (e ⟨t, ht⟩) q := by
      funext q
      show A (e ⟨t, ht⟩) q - B (e ⟨t, ht⟩) q + B (e ⟨t, ht⟩) q = A (e ⟨t, ht⟩) q
      rw [sub_add_cancel]
    rw [hfun] at hadd
    rw [hupdate]
    nth_rewrite 2 [hBrow]
    rw [hadd]
    ring
  rw [hdiff]
  have hHtb : ∀ p q, ‖H t p q‖ ≤ f p := fun p q => by
    show ‖if ((e.symm p : Fin m) : ℕ) < t then A p q else B p q‖ ≤ f p
    split
    · exact hA p q
    · exact hB p q
  refine (norm_det_le_of_row_bounds' _
    (fun p => if p = e ⟨t, ht⟩ then ε else f p) (fun p q => ?_)).trans ?_
  · rw [Matrix.updateRow_apply]
    by_cases hp : p = e ⟨t, ht⟩
    · rw [if_pos hp]
      show ‖A (e ⟨t, ht⟩) q - B (e ⟨t, ht⟩) q‖ ≤ if p = e ⟨t, ht⟩ then ε else f p
      rw [if_pos hp]
      exact hAB _ _
    · rw [if_neg hp]
      show ‖H t p q‖ ≤ if p = e ⟨t, ht⟩ then ε else f p
      rw [if_neg hp]
      exact hHtb p q
  · have hprod' : (∏ p : n, if p = e ⟨t, ht⟩ then ε else f p)
        = ε * ∏ p ∈ Finset.univ.erase (e ⟨t, ht⟩), f p := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (e ⟨t, ht⟩)), if_pos rfl]
      exact congrArg _ (Finset.prod_congr rfl fun p hp => if_neg (Finset.mem_erase.1 hp).1)
    rw [hprod']
    exact mul_le_mul_of_nonneg_left (hprod (e ⟨t, ht⟩)) hε

/-- Serre's minor-difference estimate: if the rows of `v` and `u` are both bounded by `g`,
which is `≤ D` everywhere and `≤ δ` off the finite set `B`, and corresponding entries differ
by at most `η`, then the `m`-minors differ by at most `η · D^{|B|} · δ^{m−1−|B|}`. -/
private theorem norm_minor_sub_minor_le [IsTate R] (v u : c(I, R) →L[R] c(I, R))
    {g : I → ℝ} (hg0 : ∀ j, 0 ≤ g j)
    (hgv : ∀ j i, ‖matrixCoeff v j i‖ ≤ g j) (hgu : ∀ j i, ‖matrixCoeff u j i‖ ≤ g j)
    {η : ℝ} (hη0 : 0 ≤ η) (hη : ∀ j i, ‖matrixCoeff v j i - matrixCoeff u j i‖ ≤ η)
    {δ D : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hD1 : (1 : ℝ) ≤ D) (hgD : ∀ j, g j ≤ D)
    (B : Finset I) (hgδ : ∀ j ∉ B, g j ≤ δ) (m : ℕ) (T : Finset I) (hT : T.card = m) :
    ‖minor v T - minor u T‖ ≤ η * (D ^ B.card * δ ^ (m - 1 - B.card)) := by
  have hD0 : (0 : ℝ) < D := lt_of_lt_of_le one_pos hD1
  rw [show minor v T = Matrix.det (Matrix.of fun j i : T => matrixCoeff v (j : I) (i : I))
        from rfl,
    show minor u T = Matrix.det (Matrix.of fun j i : T => matrixCoeff u (j : I) (i : I))
        from rfl]
  refine norm_det_sub_det_le' _ _ (fun q : T => g (q : I)) hη0
    (mul_nonneg (pow_nonneg hD0.le _) (pow_nonneg hδ0.le _))
    (fun p q => hgv _ _) (fun p q => hgu _ _) (fun p q => hη _ _) fun p => ?_
  refine prod_le_of_threshold (g := fun q : {x // x ∈ T} => g (q : I)) (fun q => hg0 _)
    hδ0 hδ1 hD1 (fun q => hgD _) (fun q : {x // x ∈ T} => (q : I) ∈ B)
    (fun q hq => hgδ _ hq) _ ?_ ?_
  · exact Finset.card_le_card_of_injOn (fun q : {x // x ∈ T} => (q : I))
      (fun q hq => (Finset.mem_filter.1 hq).2) (fun q _ q' _ h => Subtype.ext h)
  · have hcard : (Finset.univ.erase p).card = m - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_coe, hT]
    omega

/-- Serre's Proposition 8 [Serre1962, §5 p. 77], the uniform-convergence engine: if
`wₙ → u` in operator norm (all compactoid), the characteristic coefficients converge
uniformly at any radius `M`. -/
theorem eventually_norm_charCoeff_sub_le [IsTate R] {u : c(I, R) →L[R] c(I, R)}
    (hu : IsCompactoid u) {w : ℕ → c(I, R) →L[R] c(I, R)} (hw : ∀ n, IsCompactoid (w n))
    (hconv : Tendsto (fun n => ‖w n - u‖) atTop (𝓝 0)) (M : ℝ) (hM : 0 < M)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ m, ‖charCoeff (w n) m - charCoeff u m‖ * M ^ m ≤ ε := by
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
  set K : ℝ := C ^ (b + 1) / δ ^ b with hKdef
  have hK0 : 0 < K := div_pos (pow_pos hC0 _) (pow_pos hδ0 _)
  set η : ℝ := min (min δ 1) (ε / (D ^ b * K)) with hηdef
  have hη0 : 0 < η := lt_min (lt_min hδ0 one_pos) (div_pos hε (mul_pos (pow_pos hD0 _) hK0))
  have hηδ : η ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hη1 : η ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  /- The `m`-uniform bound: below the threshold the `δ`-power is `1` and `Cᵐ ≤ C^{b+1}`;
  above it the geometric factor `(δC)^{m−1} ≤ 2^{-(m−1)}` absorbs the growth of `Cᵐ`. -/
  have hKbound : ∀ m : ℕ, δ ^ (m - 1 - b) * C ^ m ≤ K := by
    intro m
    rw [hKdef, le_div_iff₀ (pow_pos hδ0 b)]
    by_cases hcase : m - 1 ≤ b
    · rw [show m - 1 - b = 0 by omega, pow_zero, one_mul]
      calc C ^ m * δ ^ b ≤ C ^ m * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ hδ0.le hδ1) (pow_nonneg hC0.le _)
        _ = C ^ m := mul_one _
        _ ≤ C ^ (b + 1) := pow_le_pow_right₀ hC1 (by omega)
    · have h1 : δ ^ (m - 1 - b) * δ ^ b = δ ^ (m - 1) := by
        rw [← pow_add]
        congr 1
        omega
      have h2 : C ^ m = C ^ (m - 1) * C := by
        rw [← pow_succ]
        congr 1
        omega
      have hpow : δ ^ (m - 1 - b) * C ^ m * δ ^ b = (δ * C) ^ (m - 1) * C := by
        rw [h2, mul_pow]
        calc δ ^ (m - 1 - b) * (C ^ (m - 1) * C) * δ ^ b
            = δ ^ (m - 1 - b) * δ ^ b * C ^ (m - 1) * C := by ring
          _ = δ ^ (m - 1) * C ^ (m - 1) * C := by rw [h1]
      rw [hpow]
      calc (δ * C) ^ (m - 1) * C ≤ (1 / 2 : ℝ) ^ (m - 1) * C :=
            mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (mul_nonneg hδ0.le hC0.le) hδC _) hC0.le
        _ ≤ 1 * C := mul_le_mul_of_nonneg_right
              (pow_le_one₀ (by norm_num) (by norm_num)) hC0.le
        _ = C ^ 1 := by rw [one_mul, pow_one]
        _ ≤ C ^ (b + 1) := pow_le_pow_right₀ hC1 (by omega)
  have hfinal : η * (D ^ b * K) ≤ ε := by
    rw [← le_div_iff₀ (mul_pos (pow_pos hD0 b) hK0), hηdef]
    exact min_le_right _ _
  have hev : ∀ᶠ n in atTop, ‖w n - u‖ ≤ η := by
    filter_upwards [Metric.tendsto_nhds.1 hconv η hη0] with n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (opNorm_nonneg _)] at hn
    exact hn.le
  filter_upwards [hev] with n hn
  intro m
  -- row bounds valid for `w n` and `u` simultaneously
  set g : I → ℝ := fun j => max (rowNorm u j) η
  have hg0 : ∀ j, 0 ≤ g j := fun j => le_max_of_le_left (rowNorm_nonneg u j)
  have hgu : ∀ j i, ‖matrixCoeff u j i‖ ≤ g j := fun j i =>
    (norm_matrixCoeff_le_rowNorm' u j i).trans (le_max_left _ _)
  have hrow : ∀ j, rowNorm (w n - u) j ≤ η := fun j => (rowNorm_le_opNorm' _ j).trans hn
  have hgv : ∀ j i, ‖matrixCoeff (w n) j i‖ ≤ g j := by
    intro j i
    refine (norm_matrixCoeff_le_rowNorm' (w n) j i).trans ?_
    have hadd : rowNorm (w n) j ≤ max (rowNorm (w n - u) j) (rowNorm u j) := by
      have hsum := rowNorm_add_le (w n - u) u j
      rwa [sub_add_cancel] at hsum
    exact hadd.trans (max_le (le_max_of_le_right (hrow j)) (le_max_left _ _))
  have hdiff : ∀ j i, ‖matrixCoeff (w n) j i - matrixCoeff u j i‖ ≤ η := by
    intro j i
    rw [← matrixCoeff_sub]
    exact (norm_matrixCoeff_le' (w n - u) j i).trans hn
  have hgD : ∀ j, g j ≤ D :=
    fun j => max_le ((rowNorm_le_opNorm' u j).trans (le_max_left _ _)) (hη1.trans hD1)
  have hgδ : ∀ j ∉ hbad.toFinset, g j ≤ δ := by
    intro j hj
    have hj' : ¬ (δ ≤ rowNorm u j) := fun h => hj (hbad.mem_toFinset.2 h)
    exact max_le (not_le.1 hj').le hηδ
  -- the coefficient difference is the tsum of the minor differences
  have hsummv := summable_minor (w n) (hw n) m
  have hsummu := summable_minor u hu m
  have htend : Tendsto (fun T : {T : Finset I // T.card = m} =>
      minor (w n) (T : Finset I) - minor u (T : Finset I)) cofinite (𝓝 0) :=
    (hsummv.hasSum.sub hsummu.hasSum).summable.tendsto_cofinite_zero
  have htsum : charCoeff (w n) m - charCoeff u m
      = (-1 : R) ^ m * ∑' T : {T : Finset I // T.card = m},
          (minor (w n) (T : Finset I) - minor u (T : Finset I)) := by
    rw [charCoeff, charCoeff, ← mul_sub]
    congr 1
    exact ((hsummv.hasSum.sub hsummu.hasSum).tsum_eq).symm
  have hcoeff : ‖charCoeff (w n) m - charCoeff u m‖ ≤ η * (D ^ b * δ ^ (m - 1 - b)) := by
    rw [htsum]
    refine (norm_mul_le _ _).trans ?_
    rw [norm_neg_one_pow', one_mul]
    refine (norm_tsum_le_iSup htend).trans (Real.iSup_le (fun T => ?_) ?_)
    · exact norm_minor_sub_minor_le (w n) u hg0 hgv hgu hη0.le hdiff hδ0 hδ1 hD1 hgD
        hbad.toFinset hgδ m (T : Finset I) T.2
    · exact mul_nonneg hη0.le (mul_nonneg (pow_nonneg hD0.le _) (pow_nonneg hδ0.le _))
  calc ‖charCoeff (w n) m - charCoeff u m‖ * M ^ m
      ≤ η * (D ^ b * δ ^ (m - 1 - b)) * M ^ m :=
        mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hM.le m)
    _ ≤ η * (D ^ b * δ ^ (m - 1 - b)) * C ^ m := by
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM.le (le_max_left _ _) m) ?_
        exact mul_nonneg hη0.le (mul_nonneg (pow_nonneg hD0.le _) (pow_nonneg hδ0.le _))
    _ = η * D ^ b * (δ ^ (m - 1 - b) * C ^ m) := by ring
    _ ≤ η * D ^ b * K :=
        mul_le_mul_of_nonneg_left (hKbound m) (mul_nonneg hη0.le (pow_nonneg hD0.le _))
    _ = η * (D ^ b * K) := mul_assoc _ _ _
    _ ≤ ε := hfinal

/-- Matrix coefficients of a row truncation: `π_S ∘ u` keeps the rows indexed by `S` and
kills the others. -/
private theorem matrixCoeff_truncation_mul (u : c(I, R) →L[R] c(I, R)) (S : Finset I) (j i : I) :
    matrixCoeff (truncation S * u) j i = if j ∈ S then matrixCoeff u j i else 0 := rfl

/-- The tail bound behind the compactoid theory (`norm_truncation_comp_sub_le` is private in
`Matrix.lean`), in the `*`-form used below: if the rows off `S` are `≤ ε`, so is
`‖π_S∘u − u‖`. -/
private theorem norm_truncation_mul_sub_le [IsTate R] (u : c(I, R) →L[R] c(I, R)) (S : Finset I)
    {ε : ℝ} (hε : 0 ≤ ε) (hrow : ∀ j ∉ S, rowNorm u j ≤ ε) :
    ‖truncation S * u - u‖ ≤ ε := by
  rw [norm_eq_iSup_matrixCoeff]
  refine Real.iSup_le (fun j => Real.iSup_le (fun i => ?_) hε) hε
  rw [matrixCoeff_sub, matrixCoeff_truncation_mul]
  by_cases hj : j ∈ S
  · rw [if_pos hj, sub_self, norm_zero]
    exact hε
  · rw [if_neg hj, zero_sub, norm_neg]
    exact (norm_matrixCoeff_le_rowNorm' u j i).trans (hrow j hj)

/-- **The `Finset I`-to-`ℕ` filter bridge.**  `tendsto_truncation_comp` converges along the
directed family of *all* finite subsets, whereas `eventually_norm_charCoeff_sub_le` (Serre's
Proposition 8) consumes `ℕ`-indexed sequences.  The union of the two `1/(n+1)`-bad row sets —
finite by compactoidness — is a single `ℕ`-indexed exhaustion, cofinal for the row decay of
`u` and of `v` simultaneously. -/
private theorem exists_truncation_seq [IsTate R] {u v : c(I, R) →L[R] c(I, R)}
    (hu : IsCompactoid u) (hv : IsCompactoid v) :
    ∃ S : ℕ → Finset I,
      Tendsto (fun n => ‖truncation (S n) * u - u‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖truncation (S n) * v - v‖) atTop (𝓝 0) := by
  classical
  have hbad : ∀ w : c(I, R) →L[R] c(I, R), IsCompactoid w → ∀ n : ℕ,
      {j : I | 1 / (n + 1 : ℝ) ≤ rowNorm w j}.Finite := by
    intro w hw n
    have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    have hev : ∀ᶠ j in cofinite, rowNorm w j < 1 / (n + 1 : ℝ) := by
      filter_upwards [Metric.tendsto_nhds.1 hw _ hpos] with j hj
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (rowNorm_nonneg w j)] at hj
    simpa only [not_lt] using Filter.eventually_cofinite.1 hev
  refine ⟨fun n => (hbad u hu n).toFinset ∪ (hbad v hv n).toFinset, ?_, ?_⟩
  · refine squeeze_zero (g := fun n : ℕ => 1 / (n + 1 : ℝ)) (fun n => opNorm_nonneg _)
      (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    refine norm_truncation_mul_sub_le u _ (by positivity) fun j hj => ?_
    by_contra hcon
    exact hj (Finset.mem_union_left _ ((hbad u hu n).mem_toFinset.2 (not_le.1 hcon).le))
  · refine squeeze_zero (g := fun n : ℕ => 1 / (n + 1 : ℝ)) (fun n => opNorm_nonneg _)
      (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    refine norm_truncation_mul_sub_le v _ (by positivity) fun j hj => ?_
    by_contra hcon
    exact hj (Finset.mem_union_right _ ((hbad v hv n).mem_toFinset.2 (not_le.1 hcon).le))

/-- Summability of the characteristic coefficients at `t = 1` (entireness at radius `1`). -/
private theorem summable_charCoeff_one [IsTate R] {x : c(I, R) →L[R] c(I, R)}
    (hx : IsCompactoid x) :
    Summable fun m => PowerSeries.coeff m (charPowerSeries x) * (1 : R) ^ m :=
  PowerSeries.summable_coeff_mul_pow
    (PowerSeries.tendsto_norm_coeff_mul_pow_of_isRestricted
      (charPowerSeries_isEntire x hx 1 one_pos) norm_one.le)

/-- A uniform bound on the characteristic-coefficient difference bounds the difference of the
determinant values: the value is the (ultrametric) `tsum` of the coefficients at `t = 1`, so
`‖evalT 1 f − evalT 1 g‖ ≤ ⨆ m, ‖coeff m (f − g)‖`. -/
private theorem norm_fredholmDet_sub_le [IsTate R] {x y : c(I, R) →L[R] c(I, R)}
    (hx : IsCompactoid x) (hy : IsCompactoid y) {ε : ℝ} (hε : 0 ≤ ε)
    (hb : ∀ m, ‖charCoeff x m - charCoeff y m‖ ≤ ε) :
    ‖fredholmDet x - fredholmDet y‖ ≤ ε := by
  have hsub := (summable_charCoeff_one hx).hasSum.sub (summable_charCoeff_one hy).hasSum
  have hdiff : fredholmDet x - fredholmDet y
      = ∑' m, (PowerSeries.coeff m (charPowerSeries x) * (1 : R) ^ m
        - PowerSeries.coeff m (charPowerSeries y) * (1 : R) ^ m) := hsub.tsum_eq.symm
  rw [hdiff]
  refine (norm_tsum_le_iSup hsub.summable.tendsto_cofinite_zero).trans
    (Real.iSup_le (fun m => ?_) hε)
  simpa using hb m

/-- Determinant values are continuous along operator-norm convergent sequences of compactoid
operators: Serre's Proposition 8 at radius `M = 1`. -/
private theorem tendsto_fredholmDet [IsTate R] {u : c(I, R) →L[R] c(I, R)}
    (hu : IsCompactoid u) {w : ℕ → c(I, R) →L[R] c(I, R)} (hw : ∀ n, IsCompactoid (w n))
    (hconv : Tendsto (fun n => ‖w n - u‖) atTop (𝓝 0)) :
    Tendsto (fun n => fredholmDet (w n)) atTop (𝓝 (fredholmDet u)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [eventually_norm_charCoeff_sub_le hu hw hconv 1 one_pos (half_pos hε)] with n hn
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (norm_fredholmDet_sub_le (hw n) hu (half_pos hε).le fun m => ?_)
    (half_lt_self hε)
  simpa using hn m

/-- `det(1 - 0) = 1`: every minor of positive size of the zero operator vanishes. -/
private theorem fredholmDet_zero : fredholmDet (0 : c(I, R) →L[R] c(I, R)) = 1 := by
  have hz : ∀ n : ℕ, n ≠ 0 → charCoeff (0 : c(I, R) →L[R] c(I, R)) n = 0 := by
    intro n hn
    have hmin : ∀ T : {T : Finset I // T.card = n},
        minor (0 : c(I, R) →L[R] c(I, R)) (T : Finset I) = 0 := by
      intro T
      haveI : Nonempty ((T : Finset I) : Type _) :=
        Finset.Nonempty.to_subtype (Finset.card_pos.1 (by rw [T.2]; omega))
      have hmat : (Matrix.of fun j i : (T : Finset I) =>
          matrixCoeff (0 : c(I, R) →L[R] c(I, R)) (j : I) (i : I)) = 0 :=
        Matrix.ext fun _ _ => rfl
      rw [show minor (0 : c(I, R) →L[R] c(I, R)) (T : Finset I)
            = Matrix.det (Matrix.of fun j i : (T : Finset I) =>
                matrixCoeff (0 : c(I, R) →L[R] c(I, R)) (j : I) (i : I)) from rfl,
        hmat, Matrix.det_zero]
    rw [charCoeff, tsum_congr hmin, tsum_zero, mul_zero]
  have hsingle : ∀ n : ℕ, n ≠ 0 →
      PowerSeries.coeff n (charPowerSeries (0 : c(I, R) →L[R] c(I, R))) * (1 : R) ^ n = 0 := by
    intro n hn
    rw [charPowerSeries_coeff, hz n hn, zero_mul]
  rw [fredholmDet, PowerSeries.evalT, tsum_eq_single 0 hsingle, charPowerSeries_coeff,
    charCoeff_zero, pow_zero, mul_one]

/-- Multiplicativity of the determinant value for two operators supported on the *same* finite
row set: both sides are honest finite determinants and `1 − (x + y − xy) = (1 − x)(1 − y)` on
the block.  The operator ring is not commutative, so the order in `x * y` matters. -/
private theorem fredholmDet_mul_of_rows (x y : c(I, R) →L[R] c(I, R)) (S : Finset I)
    (hx : ∀ j ∉ S, ∀ i, matrixCoeff x j i = 0) (hy : ∀ j ∉ S, ∀ i, matrixCoeff y j i = 0) :
    fredholmDet (x + y - x * y) = fredholmDet x * fredholmDet y := by
  have hxy : ∀ j ∉ S, ∀ i, matrixCoeff (x * y) j i = 0 := by
    intro j hj i
    rw [matrixCoeff_mul_of_rows x y S hy j i]
    exact Finset.sum_eq_zero fun k _ => by rw [hx j hj k, zero_mul]
  have hw : ∀ j ∉ S, ∀ i, matrixCoeff (x + y - x * y) j i = 0 := by
    intro j hj i
    rw [matrixCoeff_sub, matrixCoeff_add, hx j hj i, hy j hj i, hxy j hj i, add_zero, sub_zero]
  have hmat : (Matrix.of fun j i : S => matrixCoeff (x + y - x * y) (j : I) (i : I))
      = (Matrix.of fun j i : S => matrixCoeff x (j : I) (i : I))
        + (Matrix.of fun j i : S => matrixCoeff y (j : I) (i : I))
        - (Matrix.of fun j i : S => matrixCoeff x (j : I) (i : I))
          * (Matrix.of fun j i : S => matrixCoeff y (j : I) (i : I)) := by
    refine Matrix.ext fun p q => ?_
    rw [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply]
    show matrixCoeff (x + y - x * y) (p : I) (q : I) = _
    rw [matrixCoeff_sub, matrixCoeff_add, matrixCoeff_mul_of_rows x y S hy (p : I) (q : I),
      ← Finset.sum_coe_sort S fun k => matrixCoeff x (p : I) k * matrixCoeff y k (q : I)]
    rfl
  have hfac : ∀ A B : Matrix S S R, (1 : Matrix S S R) - (A + B - A * B) = (1 - A) * (1 - B) :=
    fun A B => by noncomm_ring
  rw [fredholmDet_eq_det_of_rows _ S hw, fredholmDet_eq_det_of_rows _ S hx,
    fredholmDet_eq_det_of_rows _ S hy, hmat, hfac, Matrix.det_mul]

/-- Multiplicativity of the determinant value [Serre1962, §5 p. 76, Corollaire 1 à la
Proposition 7]: for `1 - (u ⊞ v) = (1 - u)(1 - v)`,
`det((1-u)(1-v)) = det(1-u)·det(1-v)`. -/
theorem fredholmDet_mul [IsTate R] {u v : c(I, R) →L[R] c(I, R)}
    (hu : IsCompactoid u) (hv : IsCompactoid v) :
    fredholmDet (u + v - u * v) = fredholmDet u * fredholmDet v := by
  obtain ⟨S, hSu, hSv⟩ := exists_truncation_seq hu hv
  have hUrow : ∀ n : ℕ, ∀ j ∉ S n, ∀ i, matrixCoeff (truncation (S n) * u) j i = 0 :=
    fun n j hj i => (matrixCoeff_truncation_mul u (S n) j i).trans (if_neg hj)
  have hVrow : ∀ n : ℕ, ∀ j ∉ S n, ∀ i, matrixCoeff (truncation (S n) * v) j i = 0 :=
    fun n j hj i => (matrixCoeff_truncation_mul v (S n) j i).trans (if_neg hj)
  have hfin : ∀ n : ℕ, fredholmDet (truncation (S n) * u + truncation (S n) * v
        - truncation (S n) * u * (truncation (S n) * v))
      = fredholmDet (truncation (S n) * u) * fredholmDet (truncation (S n) * v) :=
    fun n => fredholmDet_mul_of_rows _ _ (S n) (hUrow n) (hVrow n)
  have hUc : ∀ n : ℕ, IsCompactoid (truncation (S n) * u) :=
    fun n => hu.comp_left (truncation (S n))
  have hVc : ∀ n : ℕ, IsCompactoid (truncation (S n) * v) :=
    fun n => hv.comp_left (truncation (S n))
  have hWc : ∀ n : ℕ, IsCompactoid (truncation (S n) * u + truncation (S n) * v
      - truncation (S n) * u * (truncation (S n) * v)) :=
    fun n => ((hUc n).add (hVc n)).sub ((hUc n).comp_right (truncation (S n) * v))
  have huvc : IsCompactoid (u + v - u * v) := (hu.add hv).sub (hu.comp_right v)
  have htrunc : ∀ T : Finset I, ‖(truncation T : c(I, R) →L[R] c(I, R))‖ ≤ 1 :=
    fun T => opNorm_le_of_forall _ zero_le_one fun f => by
      rw [one_mul]; exact norm_truncation_apply_le T f
  have hVb : ∀ n : ℕ, ‖truncation (S n) * v‖ ≤ ‖v‖ := fun n =>
    (opNorm_mul_le _ _).trans
      (by simpa using mul_le_mul_of_nonneg_right (htrunc (S n)) (opNorm_nonneg v))
  have hAB : ∀ A B : c(I, R) →L[R] c(I, R), ‖A - B‖ ≤ ‖A‖ + ‖B‖ := fun A B => by
    rw [sub_eq_add_neg]
    exact (norm_add_le _ _).trans_eq (by rw [opNorm_neg])
  have hWconv : Tendsto (fun n => ‖truncation (S n) * u + truncation (S n) * v
      - truncation (S n) * u * (truncation (S n) * v) - (u + v - u * v)‖) atTop (𝓝 0) := by
    have hg : Tendsto (fun n => (‖truncation (S n) * u - u‖ + ‖truncation (S n) * v - v‖)
        + (‖truncation (S n) * u - u‖ * ‖v‖ + ‖u‖ * ‖truncation (S n) * v - v‖))
        atTop (𝓝 0) := by
      simpa using (hSu.add hSv).add ((hSu.mul_const ‖v‖).add (hSv.const_mul ‖u‖))
    refine squeeze_zero (fun n => opNorm_nonneg _) (fun n => ?_) hg
    have hsplit : truncation (S n) * u + truncation (S n) * v
        - truncation (S n) * u * (truncation (S n) * v) - (u + v - u * v)
        = (truncation (S n) * u - u + (truncation (S n) * v - v))
          - ((truncation (S n) * u - u) * (truncation (S n) * v)
            + u * (truncation (S n) * v - v)) := by
      noncomm_ring
    rw [hsplit]
    refine (hAB _ _).trans (add_le_add (norm_add_le _ _) ((norm_add_le _ _).trans
      (add_le_add ?_ (opNorm_mul_le _ _))))
    exact (opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hVb n) (opNorm_nonneg _))
  exact tendsto_nhds_unique ((tendsto_fredholmDet huvc hWc hWconv).congr hfin)
    ((tendsto_fredholmDet hu hUc hSu).mul (tendsto_fredholmDet hv hVc hSv))

end DetValue

section Riesz

/-- Serre's Proposition 11, easy direction [Serre1962, §7 p. 80]: if `H(a)` is a unit
then `1 - a•u` is invertible, with inverse `H(a)⁻¹ N₀`. -/
theorem isUnit_one_sub_smul_of_isUnit_evalT [IsTate R] {u : c(I, R) →L[R] c(I, R)}
    (hu : IsCompactoid u) {a : R}
    (hd : IsUnit (PowerSeries.evalT a (charPowerSeries u))) :
    IsUnit (1 - a • u) := by
  obtain ⟨N, hN⟩ := exists_isOpLimit_resolventPartialSum u hu a 0
  have hkey : (1 - a • u) * N = PowerSeries.evalT a (charPowerSeries u) • 1 :=
    one_sub_smul_mul_resolventEval_zero hu hN
  have hcomm : u * N = N * u := commute_of_isOpLimit_resolventPartialSum hN
  have hcomm' : (1 - a • u) * N = N * (1 - a • u) := by
    rw [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hcomm]
  have hright : (1 - a • u) * ((↑hd.unit⁻¹ : R) • N) = 1 := by
    rw [mul_smul_comm, hkey, smul_smul, hd.val_inv_mul, one_smul]
  have hleft : ((↑hd.unit⁻¹ : R) • N) * (1 - a • u) = 1 := by
    rw [smul_mul_assoc, ← hcomm', ← mul_smul_comm, hright]
  exact isUnit_iff_exists.2 ⟨(↑hd.unit⁻¹ : R) • N, hright, hleft⟩

/-- Serre's Proposition 11, hard direction [Serre1962, §7 p. 80]: if `1 - a•u` is
invertible then `H(a)` is a unit (via multiplicativity applied to the inverse
`(1 - a•u)⁻¹ = 1 - v` with `v` compactoid). -/
theorem isUnit_evalT_of_isUnit_one_sub_smul [IsTate R] {u : c(I, R) →L[R] c(I, R)}
    (hu : IsCompactoid u) {a : R} (h : IsUnit (1 - a • u)) :
    IsUnit (PowerSeries.evalT a (charPowerSeries u)) := by
  obtain ⟨w, hw, -⟩ := isUnit_iff_exists.1 h
  -- Serre's `v := 1 - (1 - a•u)⁻¹` satisfies `v = -(a•u) + (a•u)·v`, hence is compactoid
  have hveq : (1 : c(I, R) →L[R] c(I, R)) - w
      = -(a • u) + a • u * ((1 : c(I, R) →L[R] c(I, R)) - w) := by
    have hexp : -(a • u) + a • u * ((1 : c(I, R) →L[R] c(I, R)) - w)
        = 1 - w - (1 - (1 - a • u) * w) := by noncomm_ring
    rw [hexp, hw, sub_self, sub_zero]
  have hvc : IsCompactoid ((1 : c(I, R) →L[R] c(I, R)) - w) := by
    rw [hveq]
    exact (hu.smul a).neg.add ((hu.smul a).comp_right ((1 : c(I, R) →L[R] c(I, R)) - w))
  -- and `(a•u) ⊞ v = 0`, so multiplicativity forces `H(a) · det(1 - v) = det(1) = 1`
  have hzero : a • u + ((1 : c(I, R) →L[R] c(I, R)) - w)
      - a • u * ((1 : c(I, R) →L[R] c(I, R)) - w) = 0 := by
    have hexp : a • u + ((1 : c(I, R) →L[R] c(I, R)) - w)
        - a • u * ((1 : c(I, R) →L[R] c(I, R)) - w) = 1 - (1 - a • u) * w := by noncomm_ring
    rw [hexp, hw, sub_self]
  have hmul := fredholmDet_mul (hu.smul a) hvc
  rw [hzero, fredholmDet_zero, fredholmDet_smul a u hu] at hmul
  exact IsUnit.of_mul_eq_one _ hmul.symm

/-- Serre's Proposition 11 [Serre1962, §7 p. 80], unit form over a Banach–Tate ring:
`1 - a•u` is invertible iff `H(a)` is a unit. -/
theorem isUnit_one_sub_smul_iff_isUnit_evalT [IsTate R] {u : c(I, R) →L[R] c(I, R)}
    (hu : IsCompactoid u) (a : R) :
    IsUnit (1 - a • u) ↔ IsUnit (PowerSeries.evalT a (charPowerSeries u)) :=
  ⟨isUnit_evalT_of_isUnit_one_sub_smul hu, isUnit_one_sub_smul_of_isUnit_evalT hu⟩

/-- The dichotomy at a zero of finite order (the eigenvector content of [Serre1962, §7
Prop. 12], in Buzzard's divided-derivative formulation [Buzzard2007, pp. 22–23]): if
`a` is a zero of `H` of order `h ≥ 1`, then `1 - a•u` has a nonzero kernel element.
If `1 - a•u` were injective, the evaluated identities would force `N₀ = ⋯ = N_{h-1} = 0`
and then exhibit `(ΔʰH)(a)⁻¹ N_h` as an inverse of `1 - a•u`, contradicting
Proposition 11. -/
theorem exists_mem_ker_of_hasseDeriv_evalT [IsTate R] {u : c(I, R) →L[R] c(I, R)}
    (hu : IsCompactoid u) {a : R} {h : ℕ} (hh : 1 ≤ h)
    (h0 : ∀ s < h, PowerSeries.evalT a (PowerSeries.hasseDeriv s (charPowerSeries u)) = 0)
    (hunit : IsUnit
      (PowerSeries.evalT a (PowerSeries.hasseDeriv h (charPowerSeries u)))) :
    ∃ x : c(I, R), x ≠ 0 ∧ (1 - a • u) x = 0 := by
  by_contra hcon
  -- no kernel means `1 - a•u` cancels on the left
  have hker : ∀ y : c(I, R), (1 - a • u) y = 0 → y = 0 := fun y hy => by
    by_contra hy0
    exact hcon ⟨y, hy0, hy⟩
  have hMzero : ∀ M : c(I, R) →L[R] c(I, R), (1 - a • u) * M = 0 → M = 0 := by
    intro M hM
    refine ContinuousLinearMap.ext fun x => ?_
    have hx : (1 - a • u) (M x) = 0 := by
      have h1 := congrArg (fun T : c(I, R) →L[R] c(I, R) => T x) hM
      simpa using h1
    simpa using hker (M x) hx
  choose N hN using fun s : ℕ => exists_isOpLimit_resolventPartialSum u hu a s
  have hH0 : PowerSeries.evalT a (charPowerSeries u) = 0 := by
    have h00 := h0 0 (by omega)
    rwa [PowerSeries.hasseDeriv_zero] at h00
  -- Serre's `Δˢ`-equations kill `N₀, …, N_{h-1}` one after the other
  have hNs : ∀ s, s < h → N s = 0 := by
    intro s
    induction s with
    | zero =>
        intro _
        refine hMzero _ ?_
        rw [one_sub_smul_mul_resolventEval_zero hu (hN 0), hH0, zero_smul]
    | succ t ih =>
        intro hts
        have hs1 : 1 ≤ t + 1 := by omega
        refine hMzero _ ?_
        rw [one_sub_smul_mul_resolventEval hu hs1 (hN (t + 1)) (hN t), ih (by omega),
          h0 (t + 1) hts, mul_zero, zero_smul, add_zero]
  -- at `s = h` the scalar is a unit, so `N_h` inverts `1 - a•u`
  have htop : (1 - a • u) * N h
      = PowerSeries.evalT a (PowerSeries.hasseDeriv h (charPowerSeries u)) • 1 := by
    rw [one_sub_smul_mul_resolventEval hu hh (hN h) (hN (h - 1)), hNs (h - 1) (by omega),
      mul_zero, zero_add]
  have hcomm : u * N h = N h * u := commute_of_isOpLimit_resolventPartialSum (hN h)
  have hcomm' : (1 - a • u) * N h = N h * (1 - a • u) := by
    rw [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hcomm]
  have hright : (1 - a • u) * ((↑hunit.unit⁻¹ : R) • N h) = 1 := by
    rw [mul_smul_comm, htop, smul_smul, hunit.val_inv_mul, one_smul]
  have hleft : ((↑hunit.unit⁻¹ : R) • N h) * (1 - a • u) = 1 := by
    rw [smul_mul_assoc, ← hcomm', ← mul_smul_comm, hright]
  have hHunit : IsUnit (PowerSeries.evalT a (charPowerSeries u)) :=
    isUnit_evalT_of_isUnit_one_sub_smul hu
      (isUnit_iff_exists.2 ⟨(↑hunit.unit⁻¹ : R) • N h, hright, hleft⟩)
  rw [hH0] at hHunit
  haveI : Nontrivial R := NormOneClass.nontrivial
  exact not_isUnit_zero hHunit

end Riesz

section RieszDecomposition

/-- **Serre's Riesz projectors** [Serre1962, §7 p. 81]: at a zero of order `h ≥ 1`, from
`e := c⁻¹(1-au)N_h` and `f := -c⁻¹uN_{h-1}` (with `e + f = 1`, `f·eʰ = 0`), the binomial
expansion of `(e+f)ʰ = 1` splits as the idempotent `p := eʰ` and its complement.  The
witness `w` realises the invertibility of `1 - a•u` on the range of `p`. -/
theorem exists_rieszProjection [IsTate R] {u : c(I, R) →L[R] c(I, R)}
    (hu : IsCompactoid u) {a : R} {h : ℕ} (hh : 1 ≤ h)
    (h0 : ∀ s < h, PowerSeries.evalT a (PowerSeries.hasseDeriv s (charPowerSeries u)) = 0)
    (hunit : IsUnit
      (PowerSeries.evalT a (PowerSeries.hasseDeriv h (charPowerSeries u)))) :
    ∃ p w : c(I, R) →L[R] c(I, R),
      p * p = p ∧ u * p = p * u ∧ u * w = w * u ∧ p * w = w * p ∧
      (1 - a • u) ^ h * (1 - p) = 0 ∧ (1 - a • u) * w = p := by sorry

variable [IsTate R] {u p w : c(I, R) →L[R] c(I, R)} {a : R} {h : ℕ}

/-- The kernel of `(1 - a•u)ʰ` is the range of the complementary Riesz projector — the
`N(a)` of [Serre1962, §7 Prop. 12], in Buzzard's characterisation ("N = ker(ψ)",
[Buzzard2007, p. 23]). -/
theorem ker_one_sub_smul_pow_of_rieszProjection (hp : p * p = p) (hup : u * p = p * u)
    (hpw : p * w = w * p) (hnil : (1 - a • u) ^ h * (1 - p) = 0)
    (hw : (1 - a • u) * w = p) (huw : u * w = w * u) :
    ((1 - a • u) ^ h : c(I, R) →L[R] c(I, R)).ker = (1 - p).range := by sorry

/-- The range of `(1 - a•u)ʰ` is the range of the Riesz projector — the `F(a)` of
[Serre1962, §7 Prop. 12] ("F = Im(ψ)", [Buzzard2007, p. 23]). -/
theorem range_one_sub_smul_pow_of_rieszProjection (hp : p * p = p) (hup : u * p = p * u)
    (hpw : p * w = w * p) (hnil : (1 - a • u) ^ h * (1 - p) = 0)
    (hw : (1 - a • u) * w = p) (huw : u * w = w * u) :
    ((1 - a • u) ^ h : c(I, R) →L[R] c(I, R)).range = p.range := by sorry

/-- The ranges of a continuous idempotent and of its complement are topological
complements (essentially mathlib's `ContinuousLinearMap.IsIdempotentElem.isTopCompl`;
in particular both are closed, by `Submodule.IsTopCompl.isClosed`). -/
theorem isTopCompl_range_one_sub_range_of_isIdempotent (hp : p * p = p) :
    Submodule.IsTopCompl ((1 - p).range : Submodule R c(I, R)) p.range := by sorry

/-- Uniqueness of the Riesz decomposition [Serre1962, §7 p. 81: "son unicité est
immédiate"]: any projector with the defining properties (at any order) coincides
with `p`. -/
theorem rieszProjection_unique {p' w' : c(I, R) →L[R] c(I, R)} {h' : ℕ}
    (hh : 1 ≤ h) (hh' : 1 ≤ h')
    (hp : p * p = p) (hup : u * p = p * u) (hpw : p * w = w * p)
    (hnil : (1 - a • u) ^ h * (1 - p) = 0) (hw : (1 - a • u) * w = p)
    (huw : u * w = w * u)
    (hp' : p' * p' = p') (hup' : u * p' = p' * u) (hpw' : p' * w' = w' * p')
    (hnil' : (1 - a • u) ^ h' * (1 - p') = 0) (hw' : (1 - a • u) * w' = p')
    (huw' : u * w' = w' * u) : p' = p := by sorry

/-- Blocks of a compactoid operator along an embedding of index types are compactoid. -/
theorem isCompactoid_of_comp_embedding {J : Type*} [DecidableEq J]
    (hu : IsCompactoid u) (e : J ↪ I) (v : c(J, R) →L[R] c(J, R))
    (hv : ∀ j i, matrixCoeff v j i = matrixCoeff u (e j) (e i)) :
    IsCompactoid v := by sorry

/-- Serre's Lemme 2 [Serre1962, §5 p. 77], local coordinate form: for a block-triangular
compactoid operator, the Fredholm determinant is the product of the determinants of the
two diagonal blocks.  (The Jacobs board has an equivalent statement; restated here to
keep this development file-independent.) -/
theorem charPowerSeries_blockTriangular {u : c(I, R) →L[R] c(I, R)}
    (hu : IsCompactoid u) (P : I → Prop) [DecidablePred P]
    (htri : ∀ j i, P i → ¬P j → matrixCoeff u j i = 0)
    (u₁ : c({i : I // P i}, R) →L[R] c({i : I // P i}, R))
    (h₁ : ∀ j i, matrixCoeff u₁ j i = matrixCoeff u j.1 i.1)
    (u₂ : c({i : I // ¬P i}, R) →L[R] c({i : I // ¬P i}, R))
    (h₂ : ∀ j i, matrixCoeff u₂ j i = matrixCoeff u j.1 i.1) :
    charPowerSeries u = charPowerSeries u₁ * charPowerSeries u₂ := by sorry

end RieszDecomposition

section Field

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {I : Type*} [DecidableEq I]

/-- **A zero of the characteristic power series is an eigenvalue** [Serre1962, §7,
Props. 11–12; Buzzard2007, Prop. 3.2]: over a complete nonarchimedean field, if the
entire series `H = det(1 - Tu)` of a compactoid operator vanishes at `a`, then `a ≠ 0`
and `u` has an eigenvector of eigenvalue `a⁻¹`. -/
theorem exists_eigenvector_of_evalT_charPowerSeries_eq_zero
    (u : c(I, K) →L[K] c(I, K)) (hu : IsCompactoid u) {a : K}
    (ha : PowerSeries.evalT a (charPowerSeries u) = 0) :
    a ≠ 0 ∧ ∃ x : c(I, K), x ≠ 0 ∧ u x = a⁻¹ • x := by sorry

/-- The zeros of the characteristic power series are exactly the reciprocals of the
nonzero eigenvalues. -/
theorem evalT_charPowerSeries_eq_zero_iff
    (u : c(I, K) →L[K] c(I, K)) (hu : IsCompactoid u) {a : K} (ha0 : a ≠ 0) :
    PowerSeries.evalT a (charPowerSeries u) = 0 ↔
      ∃ x : c(I, K), x ≠ 0 ∧ u x = a⁻¹ • x := by sorry

/-- Transport of the eigenvector theorem along a continuous linear equivalence (covers
`IsONable` and `IsPotentiallyONable` Banach spaces via `charPowerSeries_conj`). -/
theorem exists_eigenvector_of_evalT_charPowerSeries_conj_eq_zero
    {E : Type*} [NormedAddCommGroup E] [Module K E] [IsBoundedSMul K E]
    (φ : E ≃L[K] c(I, K)) (v : E →L[K] E)
    (hu : IsCompactoid (((φ : E →L[K] c(I, K)).comp v).comp
      (φ.symm : c(I, K) →L[K] E))) {a : K}
    (ha : PowerSeries.evalT a (charPowerSeries
      ((((φ : E →L[K] c(I, K)).comp v).comp (φ.symm : c(I, K) →L[K] E)))) = 0) :
    a ≠ 0 ∧ ∃ x : E, x ≠ 0 ∧ v x = a⁻¹ • x := by sorry

variable {u : c(I, K) →L[K] c(I, K)} {a : K} {h : ℕ}

/-- The generalized eigenspace `N(a) = ker (1 - a•u)ʰ` at a zero of order `h` is
finite-dimensional [Serre1962, §7 Prop. 12: "la dimension de N(a) est finie"]: on it,
`1 - (a•u)` is nilpotent, so the identity is a polynomial in the compact operator
`(a•u)|_N`, hence compact; a finite-rank approximation within Neumann distance of the
identity is then invertible.  (Run directly on the closed subspace; the `HasPr` route of
`Pr.lean` is deliberately avoided — its model-space index must be a subset of the module,
which small `N` inside a large `c(I, K)` need not admit.) -/
theorem finite_ker_one_sub_smul_pow (hu : IsCompactoid u) (hh : 1 ≤ h)
    (h0 : ∀ s < h, PowerSeries.evalT a (PowerSeries.hasseDeriv s (charPowerSeries u)) = 0)
    (hunit : IsUnit
      (PowerSeries.evalT a (PowerSeries.hasseDeriv h (charPowerSeries u)))) :
    Module.Finite K (((1 - a • u) ^ h : c(I, K) →L[K] c(I, K)).ker) := by sorry

/-- Determinant of a finite matrix with `1 - a•A` nilpotent: the characteristic power
series collapses to `(1 - a⁻¹T)ⁿ` (all eigenvalues of `A` are `a⁻¹`)
[Serre1962, §7 p. 81: "det(1 − tu_W) = (1 − ta⁻¹)^{dim W}"]. -/
theorem det_one_sub_X_smul_of_isNilpotent {n : ℕ} {A : Matrix (Fin n) (Fin n) K}
    (ha : a ≠ 0) (hnil : IsNilpotent ((1 : Matrix (Fin n) (Fin n) K) - a • A)) :
    Matrix.det (1 - (Polynomial.X : Polynomial K) • A.map Polynomial.C) =
      ((1 : Polynomial K) - Polynomial.C a⁻¹ * Polynomial.X) ^ n := by sorry

/-- The factorisation `H = (1 - a⁻¹T)^d · H'` with `H'(a) ≠ 0`, where
`d = dim N(a)` — obtained by conjugating the Riesz decomposition into block-diagonal
coordinates (the finite block from a basis of `N(a)`; the complement via
`isPotentiallyONable_of_uniformizer`, whence the discreteness hypothesis `hd`) and
applying the block factorisation of the determinant [Serre1962, §7 p. 81:
"det(1−tu) = (1−ta⁻¹)^{dim N} H′(t)"]. -/
theorem charPowerSeries_eq_pow_mul_of_riesz
    (hd : ∃ π : K, 0 < ‖π‖ ∧ ‖π‖ < 1 ∧ ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    (hu : IsCompactoid u) (hh : 1 ≤ h)
    (h0 : ∀ s < h, PowerSeries.evalT a (PowerSeries.hasseDeriv s (charPowerSeries u)) = 0)
    (hunit : IsUnit
      (PowerSeries.evalT a (PowerSeries.hasseDeriv h (charPowerSeries u)))) :
    ∃ H' : PowerSeries K, (∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c H') ∧
      PowerSeries.evalT a H' ≠ 0 ∧
      charPowerSeries u =
        (1 - PowerSeries.C a⁻¹ * PowerSeries.X) ^
          (Module.finrank K (((1 - a • u) ^ h : c(I, K) →L[K] c(I, K)).ker)) *
          H' := by sorry

/-- **`dim N(a) = h`** [Serre1962, §7 Prop. 12]: the dimension of the generalized
eigenspace equals the order of the zero — from the factorisation and uniqueness of the
divided-derivative order.  (Discreteness hypothesis `hd` as in
`isPotentiallyONable_of_uniformizer`.) -/
theorem finrank_ker_one_sub_smul_pow
    (hd : ∃ π : K, 0 < ‖π‖ ∧ ‖π‖ < 1 ∧ ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    (hu : IsCompactoid u) (hh : 1 ≤ h)
    (h0 : ∀ s < h, PowerSeries.evalT a (PowerSeries.hasseDeriv s (charPowerSeries u)) = 0)
    (hunit : IsUnit
      (PowerSeries.evalT a (PowerSeries.hasseDeriv h (charPowerSeries u)))) :
    Module.finrank K (((1 - a • u) ^ h : c(I, K) →L[K] c(I, K)).ker) = h := by sorry

/-- **Serre's Riesz decomposition** [Serre1962, §7 Prop. 12], assembled: at a zero `a`
of the characteristic power series, `c(I, K)` splits topologically as `N(a) ⊕ F(a)`
with both parts closed and `u`-stable, `(1 - a•u)ʰ` vanishing on the
`h`-dimensional `N(a)`, and `1 - a•u` bijective on `F(a)`. -/
theorem exists_riesz_decomposition
    (hd : ∃ π : K, 0 < ‖π‖ ∧ ‖π‖ < 1 ∧ ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    (hu : IsCompactoid u) (ha : PowerSeries.evalT a (charPowerSeries u) = 0) :
    ∃ (h : ℕ) (N F : Submodule K c(I, K)), 1 ≤ h ∧ Submodule.IsTopCompl N F ∧
      (∀ x ∈ N, u x ∈ N) ∧ (∀ x ∈ F, u x ∈ F) ∧
      (∀ x ∈ N, ((1 - a • u) ^ h) x = 0) ∧
      (∀ y ∈ F, ∃ x ∈ F, (1 - a • u) x = y) ∧
      (∀ x ∈ F, (1 - a • u) x = 0 → x = 0) ∧
      Module.finrank K N = h := by sorry

end Field

end TateFredholm
