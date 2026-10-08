/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.RingTheory.LaurentSeries
import PhD.TauCeti.Code.NewtonPolygons.AddVal.Discrete

/-!
# Laurent series: the `ℤ`-valued additive valuation is the order of vanishing

The second concrete discretely valued field of the roadmap: the field `K⸨X⸩` of Laurent series
over a field `K`, with Mathlib's `X`-adic valuation `Valued.v : Valuation K⸨X⸩ ℤᵐ⁰`. The valuation
is discrete, `X` is a uniformiser, and the `ℤ`-valued additive valuation of a nonzero series is the
order of its first nonzero coefficient.

Mathlib's `K⸨X⸩` is a valued field, not a normed field, so this file is stated for
`Valuation.IsRankOneDiscrete.addValZ Valued.v` rather than for `NormedField.normAddValZ`.

Roadmap: `PhD/TauCeti/Roadmaps/NewtonPolygons/README.md`, §1.3.5 (the Laurent-series half, for an
arbitrary coefficient field `K`). Tau Ceti home: `TauCeti/RingTheory/LaurentSeries/AddVal.lean`.

## Main results

* `LaurentSeries.isRankOneDiscrete_valued`: the `X`-adic valuation is discrete;
* `LaurentSeries.isUniformizer_X`: `X` is a uniformiser;
* `LaurentSeries.addValZ_eq_order`: `addValZ Valued.v f = f.order` for `f ≠ 0`.
-/

open scoped WithZero

namespace LaurentSeries

open Valuation Valuation.IsRankOneDiscrete WithZero

variable (K : Type*) [Field K]

/-- The valuation of a nonzero Laurent series is `exp (-order)`. -/
theorem valuation_eq_exp_neg_order {f : LaurentSeries K} (hf : f ≠ 0) :
    Valued.v f = exp (-f.order) := by
  have hF0 : PowerSeries.coeff 0 f.powerSeriesPart ≠ 0 := by
    rw [powerSeriesPart_coeff, Nat.cast_zero, add_zero]
    exact HahnSeries.coeff_order_eq_zero.not.mpr hf
  have h1 : Valued.v (f.powerSeriesPart : LaurentSeries K) ≤ 1 :=
    (PowerSeries.idealX K).valuation_le_one f.powerSeriesPart
  have h2 : ¬ Valued.v (f.powerSeriesPart : LaurentSeries K) ≤ exp (-((1 : ℕ) : ℤ)) := fun h ↦
    hF0 ((intValuation_le_iff_coeff_lt_eq_zero K _).mp h 0 zero_lt_one)
  have key : Valued.v (f.powerSeriesPart : LaurentSeries K) = 1 := by
    generalize Valued.v (f.powerSeriesPart : LaurentSeries K) = a at h1 h2 ⊢
    have ha0 : a ≠ 0 := fun h ↦ h2 (h ▸ zero_le)
    obtain ⟨k, rfl⟩ : ∃ k : ℤ, exp k = a := ⟨log a, exp_log ha0⟩
    rw [← exp_zero, exp_le_exp] at h1
    rw [exp_le_exp, not_le, Nat.cast_one] at h2
    rw [← exp_zero, exp_inj]
    omega
  conv_lhs => rw [← f.single_order_mul_powerSeriesPart]
  rw [map_mul, valuation_single_zpow, key, mul_one]

/-- The `X`-adic valuation of `K⸨X⸩` is a discrete rank-one valuation. -/
instance isRankOneDiscrete_valued :
    (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).IsRankOneDiscrete := by
  haveI : (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).IsNontrivial :=
    ⟨⟨((PowerSeries.X : PowerSeries K) : LaurentSeries K), by
      have h := valuation_X_pow K 1
      simp only [pow_one, Nat.cast_one] at h
      rw [h]
      exact ⟨exp_ne_zero, by simp⟩⟩⟩
  exact Valuation.IsRankOneDiscrete.mk' _

/-- The generator of the value group of `K⸨X⸩` is `exp (-1)`. -/
theorem generator_valued_eq :
    generator (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰)
      = Units.mk0 (exp (-1 : ℤ)) exp_ne_zero :=
  generator_eq_exp_neg_one_of_surjective (valuation_surjective K)

/-- `X` is a uniformiser of `K⸨X⸩`. -/
theorem isUniformizer_X :
    IsUniformizer (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰)
      ((PowerSeries.X : PowerSeries K) : LaurentSeries K) := by
  rw [IsUniformizer.iff, generator_valued_eq, Units.val_mk0]
  simpa using valuation_X_pow K 1

/-- `X` has `ℤ`-valued additive valuation `1`. -/
theorem addValZ_X :
    addValZ (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰)
      ((PowerSeries.X : PowerSeries K) : LaurentSeries K) = 1 :=
  addValZ_isUniformizer _ (isUniformizer_X K)

/-- The monomial `X ^ s` has `ℤ`-valued additive valuation `s`. -/
theorem addValZ_single (s : ℤ) :
    addValZ (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) (HahnSeries.single s (1 : K))
      = (s : WithTop ℤ) := by
  refine addValZ_eq_of_zpow _ (isUniformizer_X K) ?_
  rw [valuation_single_zpow, (isUniformizer_X K).val, generator_valued_eq, Units.val_mk0,
    ← exp_zsmul]
  congr 1
  simp

/-- **The `ℤ`-valued additive valuation of a Laurent series is its order of vanishing.** -/
theorem addValZ_eq_order {f : LaurentSeries K} (hf : f ≠ 0) :
    addValZ (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) f = (f.order : WithTop ℤ) := by
  refine addValZ_eq_of_zpow _ (isUniformizer_X K) ?_
  rw [valuation_eq_exp_neg_order K hf, (isUniformizer_X K).val, generator_valued_eq,
    Units.val_mk0, ← exp_zsmul]
  congr 1
  simp

end LaurentSeries
