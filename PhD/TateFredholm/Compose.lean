/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Analytic substitution into a power series

The composition law of the weight-`κ` action of [Jacobs, Ch. 2] is a matrix identity whose
entries are infinite sums over the inner index; read as generating functions that sum is
the substitution `F ↦ F ∘ w` of one power series into another.  The series `w` in play is a
Möbius map `(ax + b)/(cx + d)` with constant term `b/d ≠ 0`, so `PowerSeries.subst` — which
requires the substituted series to have zero constant term — cannot express it.

The substitution is nonetheless well defined *analytically*: over a complete ultrametric
field, if the outer coefficients are absolutely summable and `w` is coefficientwise
integral, then `∑ₖ Fₖ · coeff n (wᵏ)` converges for every `n`.  This file defines that
substitution and proves it is a ring homomorphism in the outer series.

## Main definitions

* `PowerSeries.AbsSummable`: absolute summability of the coefficients — the class of outer
  series.
* `PowerSeries.CoeffLeOne`: coefficientwise integrality — the class of inner series.
* `PowerSeries.compAn`: the analytic substitution `F ∘ w`.

## Main results

* `PowerSeries.compAn_mul`: `compAn` is multiplicative in the outer series.
* `PowerSeries.compAn_pow`, `PowerSeries.compAn_add`, `PowerSeries.compAn_C`,
  `PowerSeries.compAn_X`: the remaining ring-homomorphism laws.
* `PowerSeries.derivative_compAn`: the chain rule.
* `PowerSeries.eq_of_ode`: uniqueness for `A · S' = t · A' · S` over a characteristic-zero
  field — the mechanism by which the `κ`-cocycle is proved.

## Implementation notes

Everything is stated over an abstract complete ultrametric normed field, both for
generality and because unfolding a concrete adic completion during unification is
prohibitively expensive.
-/

namespace PowerSeries

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- The outer class for `compAn`: the coefficients of `F` are absolutely summable.  In the
applications they decay geometrically, so this holds by comparison with a geometric
series. -/
def AbsSummable (F : PowerSeries K) : Prop := Summable fun k => ‖coeff k F‖

/-- The inner class for `compAn`: every coefficient of `w` has norm at most `1`.  This is
what makes `‖coeff n (wᵏ)‖ ≤ 1` uniform in `k`. -/
def CoeffLeOne (w : PowerSeries K) : Prop := ∀ n, ‖coeff n w‖ ≤ 1

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem CoeffLeOne.one : CoeffLeOne (1 : PowerSeries K) := by
  intro n
  rw [coeff_one]
  split_ifs
  · simp
  · simp

omit [CompleteSpace K] in
theorem CoeffLeOne.mul {w v : PowerSeries K} (hw : CoeffLeOne w) (hv : CoeffLeOne v) :
    CoeffLeOne (w * v) := by
  intro n
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hw _) (norm_nonneg _) (hv _)

omit [CompleteSpace K] in
theorem CoeffLeOne.pow {w : PowerSeries K} (hw : CoeffLeOne w) (k : ℕ) :
    CoeffLeOne (w ^ k) := by
  induction k with
  | zero => simpa using CoeffLeOne.one
  | succ m ih => rw [pow_succ]; exact ih.mul hw

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem absSummable_add {F G : PowerSeries K} (hF : AbsSummable F) (hG : AbsSummable G) :
    AbsSummable (F + G) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    (Summable.add hF hG)
  rw [map_add]
  exact norm_add_le _ _

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem absSummable_mul {F G : PowerSeries K} (hF : AbsSummable F) (hG : AbsSummable G) :
    AbsSummable (F * G) := by
  have h := summable_norm_sum_mul_antidiagonal_of_summable_norm (f := fun k => coeff k F)
    (g := fun k => coeff k G) hF hG
  refine h.congr fun n => ?_
  rw [coeff_mul]

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem absSummable_of_eventually_eq_zero {F : PowerSeries K}
    (h : ∀ᶠ k in Filter.cofinite, coeff k F = 0) : AbsSummable F := by
  refine summable_of_hasFiniteSupport ?_
  refine h.mono fun k hk => ?_
  simp [hk]

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem absSummable_C (a : K) : AbsSummable (C a) := by
  refine absSummable_of_eventually_eq_zero (Set.Finite.eventually_cofinite_notMem
    (Set.finite_singleton 0) |>.mono fun k hk => ?_)
  rw [coeff_C, if_neg (by simpa using hk)]

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem absSummable_X : AbsSummable (X : PowerSeries K) := by
  refine absSummable_of_eventually_eq_zero (Set.Finite.eventually_cofinite_notMem
    (Set.finite_singleton 1) |>.mono fun k hk => ?_)
  rw [coeff_X, if_neg (by simpa using hk)]

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem absSummable_one : AbsSummable (1 : PowerSeries K) := by
  simpa using absSummable_C (1 : K)

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem absSummable_pow {F : PowerSeries K} (hF : AbsSummable F) (k : ℕ) :
    AbsSummable (F ^ k) := by
  induction k with
  | zero => simpa using absSummable_one (K := K)
  | succ m ih => rw [pow_succ]; exact absSummable_mul ih hF

omit [CompleteSpace K] in
/-- The defining family of `compAn` is absolutely summable: `‖Fₖ · coeff n (wᵏ)‖ ≤ ‖Fₖ‖`. -/
theorem summable_norm_compAn_term {F w : PowerSeries K} (hF : AbsSummable F)
    (hw : CoeffLeOne w) (n : ℕ) :
    Summable fun k => ‖coeff k F * coeff n (w ^ k)‖ := by
  refine hF.of_nonneg_of_le (fun _ => norm_nonneg _) fun k => ?_
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hw.pow k n)

theorem summable_compAn_term {F w : PowerSeries K} (hF : AbsSummable F)
    (hw : CoeffLeOne w) (n : ℕ) :
    Summable fun k => coeff k F * coeff n (w ^ k) :=
  (summable_norm_compAn_term hF hw n).of_norm

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem summable_norm_coeff_mul {F : PowerSeries K} (hF : AbsSummable F) (v : ℕ → K)
    (hv : ∀ k, ‖v k‖ ≤ 1) : Summable fun k => ‖coeff k F * v k‖ := by
  refine hF.of_nonneg_of_le (fun _ => norm_nonneg _) fun k => ?_
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hv k)

omit [IsUltrametricDist K] in
theorem summable_coeff_mul {F : PowerSeries K} (hF : AbsSummable F) (v : ℕ → K)
    (hv : ∀ k, ‖v k‖ ≤ 1) : Summable fun k => coeff k F * v k :=
  (summable_norm_coeff_mul hF v hv).of_norm

omit [CompleteSpace K] in
theorem absSummable_derivative {F : PowerSeries K} (hF : AbsSummable F) :
    AbsSummable (d⁄dX K F) := by
  have h : Summable fun k => ‖coeff (k + 1) F‖ := (summable_nat_add_iff 1).mpr hF
  refine h.of_nonneg_of_le (fun _ => norm_nonneg _) fun k => ?_
  rw [coeff_derivative, norm_mul]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  exact_mod_cast IsUltrametricDist.norm_natCast_le_one K (k + 1)

/-- **Analytic substitution** `F ∘ w`: the series whose `n`-th coefficient is the
convergent sum `∑ₖ Fₖ · coeff n (wᵏ)`.  Unlike `PowerSeries.subst` this does not require
`w` to have zero constant term — convergence comes from the decay of `F` instead. -/
noncomputable def compAn (F w : PowerSeries K) : PowerSeries K :=
  mk fun n => ∑' k, coeff k F * coeff n (w ^ k)

omit [CompleteSpace K] [IsUltrametricDist K] in
@[simp] theorem coeff_compAn (F w : PowerSeries K) (n : ℕ) :
    coeff n (compAn F w) = ∑' k, coeff k F * coeff n (w ^ k) :=
  coeff_mk _ _

omit [CompleteSpace K] [IsUltrametricDist K] in
@[simp] theorem compAn_C (a : K) (w : PowerSeries K) : compAn (C a) w = C a := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_compAn, tsum_eq_single 0 (fun k hk => by rw [coeff_C, if_neg hk, zero_mul])]
  simp [coeff_C]

omit [CompleteSpace K] [IsUltrametricDist K] in
@[simp] theorem compAn_one (w : PowerSeries K) : compAn 1 w = 1 := by
  simpa using compAn_C (1 : K) w

omit [CompleteSpace K] [IsUltrametricDist K] in
@[simp] theorem compAn_X (w : PowerSeries K) : compAn X w = w := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_compAn, tsum_eq_single 1 (fun k hk => by rw [coeff_X, if_neg hk, zero_mul])]
  simp

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The constant term of an analytic substitution is the outer series evaluated at the
constant term of the inner one. -/
theorem constantCoeff_compAn (F w : PowerSeries K) :
    constantCoeff (compAn F w) = ∑' n : ℕ, coeff n F * (constantCoeff w) ^ n := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_compAn]
  refine tsum_congr fun n => ?_
  rw [coeff_zero_eq_constantCoeff_apply, map_pow]

theorem compAn_add {F G w : PowerSeries K} (hF : AbsSummable F) (hG : AbsSummable G)
    (hw : CoeffLeOne w) : compAn (F + G) w = compAn F w + compAn G w := by
  refine PowerSeries.ext fun n => ?_
  rw [map_add, coeff_compAn, coeff_compAn, coeff_compAn,
    ← (summable_compAn_term hF hw n).tsum_add (summable_compAn_term hG hw n)]
  refine tsum_congr fun k => ?_
  rw [map_add, add_mul]

/-- Multiplying a substitution by a fixed series, coefficientwise: the `n`-th coefficient
of `a · (F ∘ w)` is `∑ₖ Fₖ · coeff n (a · wᵏ)`.  This is the form in which the matrix
product of two generating-function operators is read. -/
theorem coeff_mul_compAn {F w : PowerSeries K} (hF : AbsSummable F) (hw : CoeffLeOne w)
    (a : PowerSeries K) (n : ℕ) :
    coeff n (a * compAn F w) = ∑' k : ℕ, coeff k F * coeff n (a * w ^ k) := by
  rw [coeff_mul]
  have step : ∀ p ∈ Finset.antidiagonal n,
      coeff p.1 a * coeff p.2 (compAn F w)
        = ∑' k : ℕ, coeff k F * coeff p.2 (w ^ k) * coeff p.1 a := by
    intro p _
    rw [coeff_compAn, mul_comm (coeff p.1 a), ← tsum_mul_right]
  have hswap := Summable.tsum_finsetSum
    (f := fun (p : ℕ × ℕ) (k : ℕ) => coeff k F * coeff p.2 (w ^ k) * coeff p.1 a)
    (s := Finset.antidiagonal n)
    (fun p _ => (summable_compAn_term hF hw p.2).mul_right _)
  rw [Finset.sum_congr rfl step, ← hswap]
  refine tsum_congr fun k => ?_
  rw [coeff_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- Grouping a sum over `ℕ × ℕ` by the diagonals `k + l = m`.  (The same regrouping that
mathlib performs inside `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`, isolated here
because the summand below is not of the form `f k * g l`.) -/
theorem tsum_prod_eq_tsum_sum_antidiagonal {H : ℕ × ℕ → K} (h : Summable H) :
    ∑' p : ℕ × ℕ, H p = ∑' m : ℕ, ∑ kl ∈ Finset.antidiagonal m, H kl := by
  have hsig : Summable fun c : Σ m : ℕ, Finset.antidiagonal m =>
      H (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd c) :=
    (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).summable_iff.mpr h
  rw [← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq H,
    hsig.tsum_sigma' fun m => (hasSum_fintype _).summable]
  refine tsum_congr fun m => ?_
  rw [tsum_fintype]
  exact Finset.sum_finset_coe _ _

/-- **`compAn` is multiplicative in the outer series.**  Both sides equal the double sum
`∑'_{(k,l)} Fₖ Gₗ · coeff n (w^(k+l))`: the left by grouping along `k + l`, the right by
expanding the Cauchy product of the two convergent sums. -/
theorem compAn_mul {F G w : PowerSeries K} (hF : AbsSummable F) (hG : AbsSummable G)
    (hw : CoeffLeOne w) : compAn (F * G) w = compAn F w * compAn G w := by
  refine PowerSeries.ext fun n => ?_
  set H : ℕ × ℕ → K :=
    fun p => coeff p.1 F * coeff p.2 G * coeff n (w ^ (p.1 + p.2)) with hH
  have hHs : Summable H := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
      (hF.mul_norm hG))
    rw [hH]
    simp only [norm_mul]
    exact mul_le_of_le_one_right (by positivity) (hw.pow _ _)
  have hLHS : coeff n (compAn (F * G) w) = ∑' p : ℕ × ℕ, H p := by
    rw [coeff_compAn, tsum_prod_eq_tsum_sum_antidiagonal hHs]
    refine tsum_congr fun m => ?_
    rw [coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [Finset.mem_antidiagonal] at hkl
    simp only [hH]
    rw [hkl]
  have hRHS : coeff n (compAn F w * compAn G w) = ∑' p : ℕ × ℕ, H p := by
    rw [coeff_mul]
    have step : ∀ kl ∈ Finset.antidiagonal n,
        coeff kl.1 (compAn F w) * coeff kl.2 (compAn G w)
          = ∑' p : ℕ × ℕ, coeff p.1 F * coeff kl.1 (w ^ p.1) *
              (coeff p.2 G * coeff kl.2 (w ^ p.2)) := by
      intro kl _
      rw [coeff_compAn, coeff_compAn]
      exact tsum_mul_tsum_of_summable_norm (f := fun k => coeff k F * coeff kl.1 (w ^ k))
        (g := fun l => coeff l G * coeff kl.2 (w ^ l))
        (summable_norm_compAn_term hF hw kl.1) (summable_norm_compAn_term hG hw kl.2)
    have hswap := Summable.tsum_finsetSum
      (f := fun (kl : ℕ × ℕ) (p : ℕ × ℕ) =>
        coeff p.1 F * coeff kl.1 (w ^ p.1) * (coeff p.2 G * coeff kl.2 (w ^ p.2)))
      (s := Finset.antidiagonal n)
      (fun kl _ => summable_mul_of_summable_norm
        (f := fun k => coeff k F * coeff kl.1 (w ^ k))
        (g := fun l => coeff l G * coeff kl.2 (w ^ l))
        (summable_norm_compAn_term hF hw kl.1) (summable_norm_compAn_term hG hw kl.2))
    rw [Finset.sum_congr rfl step, ← hswap]
    refine tsum_congr fun p => ?_
    simp only [hH]
    rw [pow_add, coeff_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun kl _ => by ring
  rw [hLHS, hRHS]

theorem compAn_pow {F w : PowerSeries K} (hF : AbsSummable F) (hw : CoeffLeOne w) (k : ℕ) :
    compAn (F ^ k) w = (compAn F w) ^ k := by
  induction k with
  | zero => simp
  | succ m ih => rw [pow_succ, compAn_mul (absSummable_pow hF m) hF hw, ih, pow_succ]

/-- `compAn` commutes with inverses, given that the inverse is itself an admissible outer
series and the composite has invertible constant term. -/
theorem compAn_inv {F w : PowerSeries K} (hF : AbsSummable F) (hFi : AbsSummable F⁻¹)
    (hw : CoeffLeOne w) (h0 : constantCoeff F ≠ 0)
    (h1 : constantCoeff (compAn F w) ≠ 0) :
    compAn F⁻¹ w = (compAn F w)⁻¹ := by
  refine (eq_inv_iff_mul_eq_one h1).mpr ?_
  rw [← compAn_mul hFi hF hw, mul_comm F⁻¹ F, PowerSeries.mul_inv_cancel F h0, compAn_one]

omit [CompleteSpace K] in
theorem CoeffLeOne.derivative {w : PowerSeries K} (hw : CoeffLeOne w) :
    CoeffLeOne (d⁄dX K w) := by
  intro n
  rw [coeff_derivative, norm_mul]
  refine mul_le_one₀ (hw _) (norm_nonneg _) ?_
  exact_mod_cast IsUltrametricDist.norm_natCast_le_one K (n + 1)

theorem derivative_compAn {F w : PowerSeries K} (hF : AbsSummable F) (hw : CoeffLeOne w) :
    d⁄dX K (compAn F w) = compAn (d⁄dX K F) w * d⁄dX K w := by
  have hw' : CoeffLeOne (d⁄dX K w) := hw.derivative
  have hF' : AbsSummable (d⁄dX K F) := absSummable_derivative hF
  have hcast : ∀ m : ℕ, ((m : PowerSeries K)) = C (m : K) := fun m =>
    (map_natCast (C : K →+* PowerSeries K) m).symm
  refine PowerSeries.ext fun n => ?_
  have hbdd : ∀ j : ℕ, ‖(j : K) * coeff n (w ^ (j - 1) * d⁄dX K w)‖ ≤ 1 := by
    intro j
    rw [norm_mul]
    refine mul_le_one₀ ?_ (norm_nonneg _) ((hw.pow (j - 1)).mul hw' n)
    exact_mod_cast IsUltrametricDist.norm_natCast_le_one K j
  have hsum : Summable fun k => coeff k F * ((k : K) * coeff n (w ^ (k - 1) * d⁄dX K w)) :=
    summable_coeff_mul hF _ hbdd
  have hLHS : coeff n (d⁄dX K (compAn F w))
      = ∑' j : ℕ, coeff (j + 1) F * (((j : K) + 1) * coeff n (w ^ j * d⁄dX K w)) := by
    rw [coeff_derivative, coeff_compAn, ← tsum_mul_right]
    have hstep : ∀ k : ℕ, coeff k F * coeff (n + 1) (w ^ k) * ((n : K) + 1)
        = coeff k F * ((k : K) * coeff n (w ^ (k - 1) * d⁄dX K w)) := by
      intro k
      rw [mul_assoc, ← coeff_derivative, derivative_pow, mul_assoc, hcast, coeff_C_mul]
    rw [tsum_congr hstep, hsum.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add]
    refine tsum_congr fun j => ?_
    push_cast
    rfl
  have hRHS : coeff n (compAn (d⁄dX K F) w * d⁄dX K w)
      = ∑' j : ℕ, coeff (j + 1) F * (((j : K) + 1) * coeff n (w ^ j * d⁄dX K w)) := by
    rw [coeff_mul]
    have step : ∀ p ∈ Finset.antidiagonal n,
        coeff p.1 (compAn (d⁄dX K F) w) * coeff p.2 (d⁄dX K w)
          = ∑' j : ℕ, coeff j (d⁄dX K F) * coeff p.1 (w ^ j) * coeff p.2 (d⁄dX K w) := by
      intro p _
      rw [coeff_compAn, ← tsum_mul_right]
    have hswap := Summable.tsum_finsetSum
      (f := fun (p : ℕ × ℕ) (j : ℕ) =>
        coeff j (d⁄dX K F) * coeff p.1 (w ^ j) * coeff p.2 (d⁄dX K w))
      (s := Finset.antidiagonal n)
      (fun p _ => (summable_compAn_term hF' hw p.1).mul_right _)
    rw [Finset.sum_congr rfl step, ← hswap]
    refine tsum_congr fun j => ?_
    rw [coeff_derivative, coeff_mul, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hLHS, hRHS]

/-- **Analytic substitution transports the first-order ODE.**  If `A · S′ = t · A′ · S`,
then the same relation holds for `A ∘ w` and `S ∘ w` — the chain rule turns the
substituted equation into the substituted ODE. -/
theorem compAn_ode {A S w : PowerSeries K} {t : K} (hA : AbsSummable A)
    (hS : AbsSummable S) (hw : CoeffLeOne w)
    (hode : A * d⁄dX K S = C t * d⁄dX K A * S) :
    compAn A w * d⁄dX K (compAn S w) = C t * d⁄dX K (compAn A w) * compAn S w := by
  have h1 : compAn A w * compAn (d⁄dX K S) w
      = C t * compAn (d⁄dX K A) w * compAn S w := by
    have h : compAn (A * d⁄dX K S) w = compAn (C t * d⁄dX K A * S) w := by rw [hode]
    rwa [compAn_mul hA (absSummable_derivative hS) hw,
      compAn_mul (absSummable_mul (absSummable_C t) (absSummable_derivative hA)) hS hw,
      compAn_mul (absSummable_C t) (absSummable_derivative hA) hw, compAn_C] at h
  rw [derivative_compAn hS hw, derivative_compAn hA hw]
  calc compAn A w * (compAn (d⁄dX K S) w * d⁄dX K w)
      = compAn A w * compAn (d⁄dX K S) w * d⁄dX K w := by ring
    _ = C t * compAn (d⁄dX K A) w * compAn S w * d⁄dX K w := by rw [h1]
    _ = C t * (compAn (d⁄dX K A) w * d⁄dX K w) * compAn S w := by ring

section ODE

variable {k : Type*} [Field k] [CharZero k]

/-- **Uniqueness for the first-order linear ODE** `A · S' = t · A' · S`.  When `A` has
invertible constant term, a solution is determined by its constant term. -/
theorem eq_of_ode {t : k} {A S T : PowerSeries k} (hA : constantCoeff A ≠ 0)
    (hS : A * d⁄dX k S = C t * (d⁄dX k A) * S)
    (hT : A * d⁄dX k T = C t * (d⁄dX k A) * T)
    (h0 : constantCoeff S = constantCoeff T) : S = T := by
  have hDode : A * d⁄dX k (S - T) = C t * (d⁄dX k A) * (S - T) := by
    rw [map_sub, mul_sub, hS, hT, mul_sub]
  have hzero : ∀ n, coeff n (S - T) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | m
      · rw [coeff_zero_eq_constantCoeff_apply, map_sub, h0, sub_self]
      · have hc := congrArg (coeff m) hDode
        rw [coeff_mul, coeff_mul] at hc
        have hR : ∑ p ∈ Finset.antidiagonal m,
            coeff p.1 (C t * d⁄dX k A) * coeff p.2 (S - T) = 0 := by
          refine Finset.sum_eq_zero fun p hp => ?_
          rw [Finset.mem_antidiagonal] at hp
          rw [ih p.2 (by omega), mul_zero]
        have hL : ∑ p ∈ Finset.antidiagonal m, coeff p.1 A * coeff p.2 (d⁄dX k (S - T))
            = constantCoeff A * (coeff (m + 1) (S - T) * ((m : k) + 1)) := by
          rw [Finset.sum_eq_single (0, m)]
          · rw [coeff_zero_eq_constantCoeff_apply, coeff_derivative]
          · intro p hp hne
            rw [Finset.mem_antidiagonal] at hp
            have hlt : p.2 < m := by
              rcases Nat.lt_or_ge p.2 m with h | h
              · exact h
              · exact absurd (Prod.ext (by omega) (by omega)) hne
            rw [coeff_derivative, ih (p.2 + 1) (by omega), zero_mul, mul_zero]
          · intro h
            exact absurd (Finset.mem_antidiagonal.mpr (by simp)) h
        rw [hL, hR] at hc
        have hm1 : ((m : k) + 1) ≠ 0 := by
          have : ((m + 1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
          simpa using this
        rcases mul_eq_zero.mp hc with h | h
        · exact absurd h hA
        · rcases mul_eq_zero.mp h with h' | h'
          · exact h'
          · exact absurd h' hm1
  have : S - T = 0 := PowerSeries.ext fun n => by rw [hzero n, map_zero]
  linear_combination (norm := module) this

end ODE

end PowerSeries
