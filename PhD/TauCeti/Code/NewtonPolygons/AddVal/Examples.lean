/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.NewtonPolygons.AddVal.LaurentSeries
import PhD.TauCeti.Code.NewtonPolygons.AddVal.PadicComplex

/-!
# Examples

The worked examples of the roadmap's Layer 1, kept as theorems so that they are checked.

* `ℚ_p`: `normAddValZ p = 1`, `normAddValZ (1 / p²) = -2`, and `normAddVal ℚ_[p]` is `log p`
  times `normAddValZ`.
* `ℚ_p(√p)`-type fields: in any algebraic ultrametric normed `ℚ_p`-algebra field, an element `s`
  with `s² = p` has `normAddValQ` (normalised at `p`) equal to `1/2`; if the field is discretely
  valued with `normAddValZ s = 1`, then `normAddValZ p = 2`.
* `ℂ_p` at `π = p`: a cube root of `p` has additive valuation `1/3`.
* Laurent series at `X`: the `ℤ`-valued additive valuation is the order of vanishing, so `X ^ n`
  has additive valuation `n`.

Roadmap: `PhD/TauCeti/Roadmaps/NewtonPolygons/README.md`, Layer 1, "Examples".
-/

open scoped NNReal WithZero

namespace NormedField

open Valuation

variable {p : ℕ} [Fact p.Prime]

/-- `normAddValZ p = 1` on `ℚ_p`. -/
theorem normAddValZ_padic_p : normAddValZ ℚ_[p] (p : ℚ_[p]) = 1 :=
  normAddValZ_isUniformizer _ Padic.isUniformizer_p

/-- `normAddValZ (1 / p²) = -2` on `ℚ_p`. -/
theorem normAddValZ_padic_inv_p_sq :
    normAddValZ ℚ_[p] ((p : ℚ_[p]) ^ 2)⁻¹ = ((-2 : ℤ) : WithTop ℤ) := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [normAddValZ_padic_apply, Padic.addValuation.apply (inv_ne_zero (pow_ne_zero 2 hp)),
    Padic.valuation_inv, Padic.valuation_pow, Padic.valuation_p]
  norm_num

/-- `normAddVal ℚ_[p]` is `log p` times `normAddValZ ℚ_[p]`. -/
theorem normAddVal_padic (x : ℚ_[p]) :
    normAddVal ℚ_[p] x
      = WithTop.map (fun k : ℤ ↦ (k : ℝ) * Real.log p) (normAddValZ ℚ_[p] x) := by
  rw [normAddVal_eq_map_normAddValZ ℚ_[p] Padic.isUniformizer_p x, Padic.norm_p, Real.log_inv,
    neg_neg]

section SqrtP

variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [NormedAlgebra ℚ_[p] L]
  [Algebra.IsAlgebraic ℚ_[p] L]

/-- A square root of `p` has `ℚ`-valued additive valuation `1/2` (normalised at `p`). -/
theorem normAddValQ_of_sq_eq_prime {s : L} (hs : s ^ 2 = p) :
    normAddValQ L p s = ((1 / 2 : ℚ) : WithTop ℚ) := by
  have hp : (p : L) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[p] L) p]
    exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hp (by rw [← hs, zero_pow two_ne_zero])
  rw [normAddValQ_eq_of_pow_eq_pow L (p : L) hs0 (m := 1) (n := 2) two_pos
    (by rw [← norm_pow, hs, pow_one])]
  norm_num

omit [Fact p.Prime] [NormedAlgebra ℚ_[p] L] [Algebra.IsAlgebraic ℚ_[p] L] in
/-- In a discretely valued field in which a square root `s` of `p` has `ℤ`-valued additive
valuation `1`, `p` has `ℤ`-valued additive valuation `2`. -/
theorem normAddValZ_prime_of_sq_eq_prime [(valuation (K := L)).IsRankOneDiscrete] {s : L}
    (hs : s ^ 2 = p) (h1 : normAddValZ L s = 1) : normAddValZ L (p : L) = 2 := by
  rw [← hs, AddValuation.map_pow, h1, two_nsmul, one_add_one_eq_two]

end SqrtP

/-- In `ℂ_p`, a cube root of `p` has additive valuation `1/3`. -/
theorem normAddValQ_padicComplex_of_pow_three {x : ℂ_[p]} (hx : x ^ 3 = p) :
    normAddValQ ℂ_[p] p x = ((1 / 3 : ℚ) : WithTop ℚ) := by
  have hp : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hp (by rw [← hx, zero_pow three_ne_zero])
  rw [normAddValQ_eq_of_pow_eq_pow ℂ_[p] (p : ℂ_[p]) hx0 (m := 1) (n := 3) (by norm_num)
    (by rw [← norm_pow, hx, pow_one])]
  norm_num

end NormedField

namespace LaurentSeries

open Valuation.IsRankOneDiscrete

variable (K : Type*) [Field K]

/-- `X ^ n` has `ℤ`-valued additive valuation `n`: the order of vanishing at `X`. -/
theorem addValZ_X_pow (n : ℕ) :
    addValZ (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰)
      (((PowerSeries.X : PowerSeries K) : LaurentSeries K) ^ n) = ((n : ℤ) : WithTop ℤ) := by
  rw [AddValuation.map_pow, LaurentSeries.addValZ_X, ← WithTop.coe_one, ← WithTop.coe_nsmul,
    nsmul_one]

end LaurentSeries
