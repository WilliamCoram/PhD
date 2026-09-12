/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# `ℝ≥0` and `ℝᵐ⁰`

The real analogue of `Mathlib/Data/Int/WithZero.lean`: the two monoid-with-zero homs relating
the multiplicative-with-zero real line `ℝᵐ⁰ = WithZero (Multiplicative ℝ)` to `ℝ≥0`.

## Main definitions

* `NNReal.toRealMultZero : ℝ≥0 →*₀ ℝᵐ⁰`, `0 ↦ 0` and `x ↦ exp (log x)`.  It is an
  isomorphism; we only need that it is a strictly monotone hom.
* `WithZeroMulReal.toNNReal : ℝᵐ⁰ →*₀ ℝ≥0` for a base `e ≠ 0`, `0 ↦ 0` and `exp t ↦ e ^ t`
  (an `NNReal.rpow`) — the real analogue of `WithZeroMulInt.toNNReal`.

Everything here is meant to be redistributed into the relevant `Mathlib` files.
-/

open scoped NNReal WithZero

namespace NNReal

/-- The order-preserving monoid-with-zero hom `ℝ≥0 →*₀ ℝᵐ⁰` sending `0` to `0` and `x` to
`exp (log x)`.  It is an isomorphism; we only need that it is a strictly monotone hom. -/
noncomputable def toRealMultZero : ℝ≥0 →*₀ ℝᵐ⁰ where
  toFun x := if x = 0 then 0 else WithZero.exp (Real.log x)
  map_zero' := if_pos rfl
  map_one' := by rw [if_neg one_ne_zero]; simp
  map_mul' x y := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    rw [if_neg (mul_ne_zero hx hy), if_neg hx, if_neg hy, ← WithZero.exp_add, NNReal.coe_mul,
      Real.log_mul (by exact_mod_cast hx) (by exact_mod_cast hy)]

lemma toRealMultZero_of_ne_zero {x : ℝ≥0} (hx : x ≠ 0) :
    toRealMultZero x = WithZero.exp (Real.log x) := if_neg hx

lemma toRealMultZero_strictMono : StrictMono toRealMultZero := by
  intro x y hxy
  have hy : y ≠ 0 := (bot_le.trans_lt hxy).ne'
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, toRealMultZero_of_ne_zero hy]
    exact WithZero.exp_pos
  · rw [toRealMultZero_of_ne_zero hx, toRealMultZero_of_ne_zero hy, WithZero.exp_lt_exp]
    exact Real.log_lt_log (by exact_mod_cast hx.bot_lt) (by exact_mod_cast hxy)

end NNReal

namespace WithZeroMulReal

open WithZero

/-- The real analogue of `WithZeroMulInt.toNNReal`: the hom `ℝᵐ⁰ →*₀ ℝ≥0` sending `0` to `0` and
`exp t` to `e ^ t` (an `NNReal.rpow`), for a base `e ≠ 0`. -/
noncomputable def toNNReal {e : ℝ≥0} (he : e ≠ 0) : ℝᵐ⁰ →*₀ ℝ≥0 where
  toFun x := if x = 0 then 0 else e ^ (log x)
  map_zero' := if_pos rfl
  map_one' := by rw [if_neg one_ne_zero, log_one, NNReal.rpow_zero]
  map_mul' x y := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    rw [if_neg (mul_ne_zero hx hy), if_neg hx, if_neg hy, log_mul hx hy, NNReal.rpow_add he]

@[simp] lemma toNNReal_exp {e : ℝ≥0} (he : e ≠ 0) (t : ℝ) : toNNReal he (exp t) = e ^ t := by
  simp only [toNNReal, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, if_neg exp_ne_zero, log_exp]

lemma toNNReal_strictMono {e : ℝ≥0} (he : 1 < e) : StrictMono (toNNReal (ne_zero_of_lt he)) := by
  intro x y hxy
  have hy : y ≠ 0 := (bot_le.trans_lt hxy).ne'
  rcases eq_or_ne x 0 with rfl | hx
  · lift y to ℝ using hy with t
    rw [map_zero, toNNReal_exp]
    exact NNReal.rpow_pos (zero_lt_one.trans he)
  · lift x to ℝ using hx with s
    lift y to ℝ using hy with t
    rw [toNNReal_exp, toNNReal_exp]
    exact NNReal.rpow_lt_rpow_of_exponent_lt he (exp_lt_exp.mp hxy)

end WithZeroMulReal
