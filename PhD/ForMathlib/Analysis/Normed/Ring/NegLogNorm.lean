/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The additive reading of a norm

`negLogNorm r = -log ‖r‖`, valued in `WithTop ℝ = ℝ ∪ {∞}` with the genuine value `∞` at `r = 0`.

This is the logarithmic picture of a norm, in the form that Newton polygons consume: the
order is reversed (`negLogNorm` is antitone in `‖·‖`), and the zero element sits at `⊤` rather
than at the junk value `-Real.log 0 = 0`.

**This is not an `AddValuation`.**  On a `NormedRing` the norm is only submultiplicative, so
`negLogNorm` is only *super*additive: `negLogNorm r + negLogNorm s ≤ negLogNorm (r * s)`, with
equality exactly when the norm is multiplicative (`negLogNorm_mul`, under `[NormMulClass]`).
Mathlib's `AddValuation` demands the equality, so it is unavailable here; there is no bundled
structure for the additive dual of a submultiplicative seminorm, and this file does not invent
one.

## Main statements

* `negLogNorm_le_negLogNorm`: the order reversal `negLogNorm r ≤ negLogNorm s ↔ ‖s‖ ≤ ‖r‖`,
  valid at `0` with no side condition.  The workhorse.
* `add_negLogNorm_le_negLogNorm_mul` and `negLogNorm_mul`: submultiplicativity, and the
  multiplicative case.
* `le_negLogNorm_add`: the ultrametric bound `min (negLogNorm r) (negLogNorm s) ≤
  negLogNorm (r + s)`.

Everything here is meant to be redistributed into the relevant `Mathlib` files.
-/

variable {E : Type*}

/-- The additive reading of a norm: `-log ‖r‖`, valued in `WithTop ℝ` with the genuine value
`⊤` at `r = 0` (rather than the junk value `-Real.log 0 = 0`).

This is *not* an `AddValuation` unless the norm is multiplicative; see the module docstring. -/
noncomputable def negLogNorm [Norm E] (r : E) : WithTop ℝ :=
  if ‖r‖ = 0 then ⊤ else ((-Real.log ‖r‖ : ℝ) : WithTop ℝ)

section Norm

variable [Norm E] {r s : E}

theorem negLogNorm_of_norm_eq_zero (h : ‖r‖ = 0) : negLogNorm r = ⊤ := if_pos h

theorem negLogNorm_of_norm_ne_zero (h : ‖r‖ ≠ 0) :
    negLogNorm r = ((-Real.log ‖r‖ : ℝ) : WithTop ℝ) := if_neg h

@[simp] theorem negLogNorm_eq_top_iff_norm : negLogNorm r = ⊤ ↔ ‖r‖ = 0 := by
  rcases eq_or_ne ‖r‖ 0 with h | h
  · simp [negLogNorm_of_norm_eq_zero h, h]
  · simp [negLogNorm_of_norm_ne_zero h, h]

end Norm

section SeminormedAddGroup

variable [SeminormedAddGroup E] {r s : E}

@[simp] theorem negLogNorm_zero : negLogNorm (0 : E) = ⊤ :=
  negLogNorm_of_norm_eq_zero norm_zero

/-- **The order reversal.**  Larger norm means smaller `negLogNorm`; the equivalence holds at
`0` too, where both sides degenerate correctly. -/
theorem negLogNorm_le_negLogNorm : negLogNorm r ≤ negLogNorm s ↔ ‖s‖ ≤ ‖r‖ := by
  rcases eq_or_ne ‖r‖ 0 with hr | hr
  · rw [negLogNorm_of_norm_eq_zero hr, top_le_iff, negLogNorm_eq_top_iff_norm, hr]
    exact ⟨fun h ↦ h.le, fun h ↦ le_antisymm h (norm_nonneg s)⟩
  · rcases eq_or_ne ‖s‖ 0 with hs | hs
    · simp [negLogNorm_of_norm_eq_zero hs, hs, norm_nonneg r]
    · rw [negLogNorm_of_norm_ne_zero hr, negLogNorm_of_norm_ne_zero hs, WithTop.coe_le_coe,
        neg_le_neg_iff,
        Real.log_le_log_iff ((norm_nonneg s).lt_of_ne' hs) ((norm_nonneg r).lt_of_ne' hr)]

theorem negLogNorm_lt_negLogNorm : negLogNorm r < negLogNorm s ↔ ‖s‖ < ‖r‖ :=
  lt_iff_lt_of_le_iff_le negLogNorm_le_negLogNorm

/-- **The ultrametric bound.**  The additive form of `‖r + s‖ ≤ max ‖r‖ ‖s‖`. -/
theorem le_negLogNorm_add [IsUltrametricDist E] :
    min (negLogNorm r) (negLogNorm s) ≤ negLogNorm (r + s) := by
  rcases le_total ‖s‖ ‖r‖ with h | h
  · exact (min_le_left _ _).trans (negLogNorm_le_negLogNorm.mpr
      ((IsUltrametricDist.norm_add_le_max r s).trans (max_le le_rfl h)))
  · exact (min_le_right _ _).trans (negLogNorm_le_negLogNorm.mpr
      ((IsUltrametricDist.norm_add_le_max r s).trans (max_le h le_rfl)))

end SeminormedAddGroup

section NormedAddGroup

variable [NormedAddGroup E] {r : E}

@[simp] theorem negLogNorm_eq_top : negLogNorm r = ⊤ ↔ r = 0 := by
  rw [negLogNorm_eq_top_iff_norm, norm_eq_zero]

theorem negLogNorm_of_ne_zero (h : r ≠ 0) :
    negLogNorm r = ((-Real.log ‖r‖ : ℝ) : WithTop ℝ) :=
  negLogNorm_of_norm_ne_zero (norm_ne_zero_iff.mpr h)

theorem negLogNorm_ne_top (h : r ≠ 0) : negLogNorm r ≠ ⊤ := by simpa using h

end NormedAddGroup

section NormedRing

variable {A : Type*} [NormedRing A] {r s : A}

/-- **Submultiplicativity, additively.**  Only an inequality: `negLogNorm` is *super*additive
on products.  See `negLogNorm_mul` for the multiplicative case. -/
theorem add_negLogNorm_le_negLogNorm_mul :
    negLogNorm r + negLogNorm s ≤ negLogNorm (r * s) := by
  rcases eq_or_ne ‖r * s‖ 0 with hrs | hrs
  · rw [negLogNorm_of_norm_eq_zero hrs]; exact le_top
  have hr : ‖r‖ ≠ 0 := fun h ↦ hrs
    (le_antisymm (by simpa [h] using norm_mul_le r s) (norm_nonneg _))
  have hs : ‖s‖ ≠ 0 := fun h ↦ hrs
    (le_antisymm (by simpa [h] using norm_mul_le r s) (norm_nonneg _))
  rw [negLogNorm_of_norm_ne_zero hr, negLogNorm_of_norm_ne_zero hs,
    negLogNorm_of_norm_ne_zero hrs, ← WithTop.coe_add, WithTop.coe_le_coe, ← neg_add,
    neg_le_neg_iff, ← Real.log_mul hr hs]
  exact Real.log_le_log ((norm_nonneg _).lt_of_ne' hrs) (norm_mul_le r s)

/-- When the norm is multiplicative, `negLogNorm` is additive on products — this is exactly
where the inequalities of this file become equalities. -/
theorem negLogNorm_mul [NormMulClass A] :
    negLogNorm (r * s) = negLogNorm r + negLogNorm s := by
  rcases eq_or_ne ‖r‖ 0 with hr | hr
  · rw [negLogNorm_of_norm_eq_zero hr, negLogNorm_of_norm_eq_zero (by simp [norm_mul, hr]), top_add]
  rcases eq_or_ne ‖s‖ 0 with hs | hs
  · rw [negLogNorm_of_norm_eq_zero hs, negLogNorm_of_norm_eq_zero (by simp [norm_mul, hs]), add_top]
  rw [negLogNorm_of_norm_ne_zero hr, negLogNorm_of_norm_ne_zero hs,
    negLogNorm_of_norm_ne_zero (by simp [norm_mul, hr, hs]), ← WithTop.coe_add, ← neg_add,
    norm_mul, Real.log_mul hr hs]

variable (A) in
@[simp] theorem negLogNorm_one [NormOneClass A] : negLogNorm (1 : A) = 0 := by
  rw [negLogNorm_of_norm_ne_zero (by simp), norm_one, Real.log_one, neg_zero, WithTop.coe_zero]

/-- `negLogNorm` is nonnegative exactly on the power-bounded-by-one elements. -/
theorem negLogNorm_nonneg_iff [NormOneClass A] : 0 ≤ negLogNorm r ↔ ‖r‖ ≤ 1 := by
  rw [← negLogNorm_one A, negLogNorm_le_negLogNorm, norm_one]

end NormedRing
