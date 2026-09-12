/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.RingTheory.PowerSeries.Derivative
import PhD.Jacobs.U3Data

/-!
# The `p`-adic binomial theorem

[Jacobs, §2.1 p. 29] writes the weight character as `κ(cx + d) = (cx + d)^t` and expands it
by the binomial series.  Making that legitimate needs the identity

  `∑ₙ (t choose n) zⁿ = (1 + z)^t`,

with `(1 + z)^t = exp₃(t · log₃(1 + z))` — `Jacobs.unitPow` — on the right.  This file
proves it by *density in the exponent*: both sides are `‖t − t'‖`-Lipschitz in `t`, and
they agree for `t` a natural number, where the left side truncates to the ordinary
binomial theorem.

## Main results

* `Jacobs.unitPow_add`, `Jacobs.unitPow_one_eq`, `Jacobs.unitPow_natCast`: the weight power
  is additive in the exponent, is the identity at `t = 1`, and is the ordinary power at
  natural exponents.
* `Jacobs.binomialCoeff_natCast`: `(m choose n)` at a natural exponent is the ordinary
  binomial coefficient — in particular it vanishes for `n > m`.
* `Jacobs.tsum_binomialCoeff_natCast`: the binomial theorem at natural exponents.
* `Jacobs.norm_unitPow_sub_unitPow_le`, `Jacobs.norm_tsum_binomialCoeff_sub_le`: both sides
  are `‖t − t'‖`-Lipschitz in the exponent.
* `Jacobs.tsum_binomialCoeff_eq_unitPow`: the binomial theorem, for any exponent
  approximable by natural numbers.
* `Jacobs.binomialSeries_ode`: the binomial series satisfies `(1 + e·x)·B′ = t·e·B` — the
  first-order ODE that pins the `κ`-column of the weight action.
-/

open Filter Topology

open scoped Nat
open scoped PowerSeries

namespace Jacobs

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

section UnitPowExponent

variable (h3 : ‖(3 : K)‖ < 1)
include h3

/-- On the `1`-unit disc the weight power is additive in the exponent:
`u^(t+s) = u^t · u^s`. -/
theorem unitPow_add {t s u : K} (ht : ‖t‖ ≤ 1) (hs : ‖s‖ ≤ 1) (hu : ‖u - 1‖ ≤ ‖(3 : K)‖) :
    unitPow (t + s) u = unitPow t u * unitPow s u := by
  have h3pos : (0 : ℝ) < ‖(3 : K)‖ := norm_pos_iff.mpr (by norm_num)
  have hsq : ‖(3 : K)‖ ^ 2 < ‖(3 : K)‖ := by nlinarith
  have hL : ‖padicLog u‖ ≤ ‖(3 : K)‖ := norm_padicLog_le h3 hu
  have hb : ∀ r : K, ‖r‖ ≤ 1 → ‖r * padicLog u‖ ^ 2 < ‖(3 : K)‖ := by
    intro r hr
    refine lt_of_le_of_lt (pow_le_pow_left₀ (norm_nonneg _) ?_ 2) hsq
    rw [norm_mul]
    calc ‖r‖ * ‖padicLog u‖ ≤ 1 * ‖(3 : K)‖ :=
          mul_le_mul hr hL (norm_nonneg _) zero_le_one
      _ = ‖(3 : K)‖ := one_mul _
  simp only [unitPow]
  rw [add_mul, padicExp_add h3 (hb t ht) (hb s hs)]

/-- `u^1 = u`. -/
theorem unitPow_one_eq {u : K} (hu : ‖u - 1‖ ≤ ‖(3 : K)‖) : unitPow (1 : K) u = u := by
  have h3pos : (0 : ℝ) < ‖(3 : K)‖ := norm_pos_iff.mpr (by norm_num)
  have hsq : ‖(3 : K)‖ ^ 2 < ‖(3 : K)‖ := by nlinarith
  have hu2 : ‖u - 1‖ ^ 2 < ‖(3 : K)‖ :=
    lt_of_le_of_lt (pow_le_pow_left₀ (norm_nonneg _) hu 2) hsq
  rw [unitPow, one_mul, padicExp_padicLog h3 hu2]

/-- At a natural exponent the weight power is the ordinary power. -/
theorem unitPow_natCast {u : K} (hu : ‖u - 1‖ ≤ ‖(3 : K)‖) (m : ℕ) :
    unitPow ((m : ℕ) : K) u = u ^ m := by
  induction m with
  | zero => simp [unitPow]
  | succ n ih =>
      rw [Nat.cast_succ,
        unitPow_add h3 (IsUltrametricDist.norm_natCast_le_one K n) (le_of_eq norm_one) hu,
        ih, unitPow_one_eq h3 hu, pow_succ]

end UnitPowExponent

section BinomialNat

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The descending product at a natural argument is the descending factorial. -/
theorem prod_natCast_sub (m n : ℕ) :
    ∏ k ∈ Finset.range n, ((m : K) - (k : K)) = ((m.descFactorial n : ℕ) : K) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, ih, Nat.descFactorial_succ, Nat.cast_mul]
      rcases le_or_gt n m with h | h
      · rw [Nat.cast_sub h]; ring
      · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h]; simp

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The generalised binomial coefficient at a natural exponent is the ordinary one.  In
particular it VANISHES for `n > m`, which is what truncates the binomial series. -/
theorem binomialCoeff_natCast (m n : ℕ) :
    binomialCoeff ((m : ℕ) : K) n = ((m.choose n : ℕ) : K) := by
  have hfac : ((n ! : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [binomialCoeff, prod_natCast_sub, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  field_simp

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **The binomial theorem at a natural exponent.**  The series truncates, because
`(m choose n) = 0` for `n > m`. -/
theorem tsum_binomialCoeff_natCast (m : ℕ) (z : K) :
    ∑' n : ℕ, binomialCoeff ((m : ℕ) : K) n * z ^ n = (1 + z) ^ m := by
  have hvanish : ∀ n ∉ Finset.range (m + 1),
      binomialCoeff ((m : ℕ) : K) n * z ^ n = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [binomialCoeff_natCast, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
  rw [tsum_eq_sum hvanish, add_comm (1 : K) z, add_pow]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [binomialCoeff_natCast, one_pow, mul_one]
  ring

end BinomialNat

section Lipschitz

omit [CompleteSpace K] [CharZero K] in
/-- An ultrametric product estimate: two products of norm-`≤ 1` families whose factors are
`ε`-close differ by at most `ε`. -/
theorem norm_prod_sub_prod_le {a b : ℕ → K} (ha : ∀ i, ‖a i‖ ≤ 1) (hb : ∀ i, ‖b i‖ ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hab : ∀ i, ‖a i - b i‖ ≤ ε) (n : ℕ) :
    ‖∏ i ∈ Finset.range n, a i - ∏ i ∈ Finset.range n, b i‖ ≤ ε := by
  induction n with
  | zero => simpa using hε
  | succ m ih =>
      have hp : ‖∏ i ∈ Finset.range m, a i‖ ≤ 1 := by
        rw [norm_prod]
        exact Finset.prod_le_one (fun i _ => norm_nonneg _) fun i _ => ha i
      rw [Finset.prod_range_succ, Finset.prod_range_succ,
        show (∏ i ∈ Finset.range m, a i) * a m - (∏ i ∈ Finset.range m, b i) * b m
          = (∏ i ∈ Finset.range m, a i) * (a m - b m)
            + ((∏ i ∈ Finset.range m, a i) - ∏ i ∈ Finset.range m, b i) * b m from by ring]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]
        calc ‖∏ i ∈ Finset.range m, a i‖ * ‖a m - b m‖ ≤ 1 * ε :=
              mul_le_mul hp (hab m) (norm_nonneg _) zero_le_one
          _ = ε := one_mul ε
      · rw [norm_mul]
        calc ‖(∏ i ∈ Finset.range m, a i) - ∏ i ∈ Finset.range m, b i‖ * ‖b m‖ ≤ ε * 1 :=
              mul_le_mul ih (hb m) (norm_nonneg _) hε
          _ = ε := mul_one ε

variable (h3 : ‖(3 : K)‖ < 1)
include h3

/-- A weight power of a `1`-unit is itself a unit (norm exactly one), for `‖t‖ ≤ 1`. -/
theorem norm_unitPow_eq_one {t u : K} (ht : ‖t‖ ≤ 1) (hu : ‖u - 1‖ ≤ ‖(3 : K)‖) :
    ‖unitPow t u‖ = 1 := by
  have h3pos : (0 : ℝ) < ‖(3 : K)‖ := norm_pos_iff.mpr (by norm_num)
  have hsq : ‖(3 : K)‖ ^ 2 < ‖(3 : K)‖ := by nlinarith
  have hL : ‖padicLog u‖ ≤ ‖(3 : K)‖ := norm_padicLog_le h3 hu
  have hw : ‖t * padicLog u‖ ≤ ‖(3 : K)‖ := by
    rw [norm_mul]
    calc ‖t‖ * ‖padicLog u‖ ≤ 1 * ‖(3 : K)‖ :=
          mul_le_mul ht hL (norm_nonneg _) zero_le_one
      _ = ‖(3 : K)‖ := one_mul _
  have hw2 : ‖t * padicLog u‖ ^ 2 < ‖(3 : K)‖ :=
    lt_of_le_of_lt (pow_le_pow_left₀ (norm_nonneg _) hw 2) hsq
  exact norm_eq_one_of_norm_sub_one_lt_one
    ((norm_padicExp_sub_one_le h3 hw2).trans_lt (lt_of_le_of_lt hw h3))

/-- The weight power of a `1`-unit is nonzero — it has norm `1`
(`norm_unitPow_eq_one`). -/
theorem unitPow_ne_zero {t u : K} (ht : ‖t‖ ≤ 1) (hu : ‖u - 1‖ ≤ ‖(3 : K)‖) :
    unitPow t u ≠ 0 :=
  norm_ne_zero_iff.mp <| by simp [norm_unitPow_eq_one h3 ht hu]

/-- **The weight power is Lipschitz in the exponent.** -/
theorem norm_unitPow_sub_unitPow_le {t t' u : K} (ht' : ‖t'‖ ≤ 1) (hlt : ‖t - t'‖ < 1)
    (hu : ‖u - 1‖ ≤ ‖(3 : K)‖) :
    ‖unitPow t u - unitPow t' u‖ ≤ ‖t - t'‖ * ‖(3 : K)‖ := by
  have hsplit : unitPow t u = unitPow t' u * unitPow (t - t') u := by
    rw [← unitPow_add h3 ht' hlt.le hu, add_sub_cancel]
  rw [hsplit, ← mul_sub_one, norm_mul, norm_unitPow_eq_one h3 ht' hu, one_mul]
  exact norm_unitPow_sub_one_le h3 hlt hu


/-- The binomial series converges (geometrically) for `‖t‖ ≤ 1` and `‖z‖ ≤ ‖3‖²`. -/
theorem summable_binomialCoeff_mul_pow {t z : K} (ht : ‖t‖ ≤ 1) (hz : ‖z‖ ≤ ‖(3 : K)‖ ^ 2) :
    Summable fun n : ℕ => binomialCoeff t n * z ^ n := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (summable_geometric_of_lt_one (norm_nonneg _) h3))
  exact norm_binomialCoeff_mul_pow_le h3 ht hz n

/-- **The binomial coefficients are Lipschitz in the exponent**, with the `n!`-denominator
absorbed by `‖3‖ⁿ ≤ ‖n!‖`. -/
theorem norm_binomialCoeff_sub_mul_pow_le {t t' z : K} (ht : ‖t‖ ≤ 1) (ht' : ‖t'‖ ≤ 1)
    (hz : ‖z‖ ≤ ‖(3 : K)‖ ^ 2) (n : ℕ) :
    ‖(binomialCoeff t n - binomialCoeff t' n) * z ^ n‖ ≤ ‖t - t'‖ * ‖(3 : K)‖ ^ n := by
  have hfac : (0 : ℝ) < ‖((n ! : ℕ) : K)‖ := by
    rw [norm_pos_iff, Nat.cast_ne_zero]
    exact Nat.factorial_ne_zero n
  have hprod : ‖(∏ k ∈ Finset.range n, (t - (k : K)))
      - ∏ k ∈ Finset.range n, (t' - (k : K))‖ ≤ ‖t - t'‖ := by
    refine norm_prod_sub_prod_le (fun i => ?_) (fun i => ?_) (norm_nonneg _) (fun i => ?_) n
    · exact (norm_sub_le_max' _ _).trans
        (max_le ht (IsUltrametricDist.norm_natCast_le_one K i))
    · exact (norm_sub_le_max' _ _).trans
        (max_le ht' (IsUltrametricDist.norm_natCast_le_one K i))
    · rw [sub_sub_sub_cancel_right]
  have hsub : binomialCoeff t n - binomialCoeff t' n
      = ((∏ k ∈ Finset.range n, (t - (k : K))) - ∏ k ∈ Finset.range n, (t' - (k : K)))
        / ((n ! : ℕ) : K) := by
    rw [binomialCoeff, binomialCoeff, sub_div]
  have hzn : ‖z ^ n‖ ≤ ‖(3 : K)‖ ^ (2 * n) := by
    rw [norm_pow, pow_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) hz n
  rw [hsub, div_mul_eq_mul_div, norm_div, div_le_iff₀ hfac, norm_mul]
  calc ‖(∏ k ∈ Finset.range n, (t - (k : K))) - ∏ k ∈ Finset.range n, (t' - (k : K))‖ * ‖z ^ n‖
      ≤ ‖t - t'‖ * ‖(3 : K)‖ ^ (2 * n) :=
        mul_le_mul hprod hzn (norm_nonneg _) (norm_nonneg _)
    _ = ‖t - t'‖ * ‖(3 : K)‖ ^ n * ‖(3 : K)‖ ^ n := by rw [two_mul, pow_add]; ring
    _ ≤ ‖t - t'‖ * ‖(3 : K)‖ ^ n * ‖((n ! : ℕ) : K)‖ :=
        mul_le_mul_of_nonneg_left (norm_pow_le_norm_factorial h3 n)
          (by positivity)

/-- **The binomial series is Lipschitz in the exponent.** -/
theorem norm_tsum_binomialCoeff_sub_le {t t' z : K} (ht : ‖t‖ ≤ 1) (ht' : ‖t'‖ ≤ 1)
    (hz : ‖z‖ ≤ ‖(3 : K)‖ ^ 2) :
    ‖(∑' n : ℕ, binomialCoeff t n * z ^ n) - ∑' n : ℕ, binomialCoeff t' n * z ^ n‖
      ≤ ‖t - t'‖ := by
  rw [← (summable_binomialCoeff_mul_pow h3 ht hz).tsum_sub
    (summable_binomialCoeff_mul_pow h3 ht' hz)]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le fun n => ?_
  rw [← sub_mul]
  refine (norm_binomialCoeff_sub_mul_pow_le h3 ht ht' hz n).trans ?_
  exact mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) h3.le)

/-- **The `p`-adic binomial theorem**: `∑ₙ (t choose n) zⁿ = (1 + z)^t`.

The density hypothesis `hdense` — that `t` is approximable by natural numbers — is exactly
what makes the exponent argument work; over the completion `K₃ = ℚ₃` it holds for every
`t` in the unit ball.  Both sides are `‖t − t'‖`-Lipschitz in the exponent
(`norm_tsum_binomialCoeff_sub_le`, `norm_unitPow_sub_unitPow_le`) and agree at natural
exponents (`tsum_binomialCoeff_natCast`, `unitPow_natCast`), so they agree everywhere. -/
theorem tsum_binomialCoeff_eq_unitPow {t z : K} (ht : ‖t‖ ≤ 1) (hz : ‖z‖ ≤ ‖(3 : K)‖ ^ 2)
    (hdense : ∀ ε > 0, ∃ m : ℕ, ‖t - ((m : ℕ) : K)‖ < ε) :
    ∑' n : ℕ, binomialCoeff t n * z ^ n = unitPow t (1 + z) := by
  have h3le : ‖(3 : K)‖ ≤ 1 := h3.le
  have hu : ‖(1 + z) - 1‖ ≤ ‖(3 : K)‖ := by
    rw [add_sub_cancel_left]
    exact hz.trans (by nlinarith [norm_nonneg (3 : K)])
  have key : ∀ ε : ℝ, 0 < ε →
      ‖(∑' n : ℕ, binomialCoeff t n * z ^ n) - unitPow t (1 + z)‖ < ε := by
    intro ε hε
    obtain ⟨m, hm⟩ := hdense (min ε 1) (lt_min hε one_pos)
    have hm1 : ‖t - ((m : ℕ) : K)‖ < 1 := hm.trans_le (min_le_right _ _)
    have hmnorm : ‖((m : ℕ) : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K m
    have hagree : ∑' n : ℕ, binomialCoeff ((m : ℕ) : K) n * z ^ n
        = unitPow ((m : ℕ) : K) (1 + z) := by
      rw [tsum_binomialCoeff_natCast, unitPow_natCast h3 hu]
    have hsplit : (∑' n : ℕ, binomialCoeff t n * z ^ n) - unitPow t (1 + z)
        = ((∑' n : ℕ, binomialCoeff t n * z ^ n)
            - ∑' n : ℕ, binomialCoeff ((m : ℕ) : K) n * z ^ n)
          + (unitPow ((m : ℕ) : K) (1 + z) - unitPow t (1 + z)) := by
      rw [hagree]; ring
    rw [hsplit]
    refine lt_of_le_of_lt ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_))
      (hm.trans_le (min_le_left _ _))
    · exact norm_tsum_binomialCoeff_sub_le h3 ht hmnorm hz
    · rw [← norm_neg, neg_sub]
      refine (norm_unitPow_sub_unitPow_le h3 hmnorm hm1 hu).trans ?_
      exact mul_le_of_le_one_right (norm_nonneg _) h3le
  by_contra hne
  have hpos : 0 < ‖(∑' n : ℕ, binomialCoeff t n * z ^ n) - unitPow t (1 + z)‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  exact lt_irrefl _ (key _ hpos)

end Lipschitz

section ODE

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The defining recursion of the generalised binomial coefficients:
`(n+1)·(t choose n+1) = (t − n)·(t choose n)`. -/
theorem binomialCoeff_succ (t : K) (n : ℕ) :
    binomialCoeff t (n + 1) * ((n : K) + 1) = binomialCoeff t n * (t - (n : K)) := by
  have hfac : ((n ! : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn1 : ((n : K) + 1) ≠ 0 := by
    have h : ((n + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    simpa using h
  rw [binomialCoeff, binomialCoeff, Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  field_simp

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
@[simp] theorem coeff_binomialSeries (t e : K) (n : ℕ) :
    PowerSeries.coeff n (binomialSeries t e) = binomialCoeff t n * e ^ n :=
  PowerSeries.coeff_mk _ _

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem binomialCoeff_one (t : K) : binomialCoeff t 1 = t := by
  rw [binomialCoeff]
  simp

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **The binomial series satisfies the hypergeometric ODE** `(1 + e·x)·B' = t·e·B`. -/
theorem binomialSeries_ode (t e : K) :
    (1 + PowerSeries.C e * PowerSeries.X) * d⁄dX K (binomialSeries t e)
      = PowerSeries.C (t * e) * binomialSeries t e := by
  refine PowerSeries.ext fun n => ?_
  rw [add_mul, one_mul, map_add, mul_assoc, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_derivative, coeff_binomialSeries, PowerSeries.coeff_C_mul,
    coeff_binomialSeries]
  rcases n with _ | m
  · simp [binomialCoeff]
  · simp only [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
      coeff_binomialSeries]
    have hrec := binomialCoeff_succ t (m + 1)
    push_cast at hrec ⊢
    linear_combination (e ^ (m + 2)) * hrec

end ODE

end Jacobs
