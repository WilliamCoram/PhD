/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.ForMathlib.Data.Real.WithZero
import PhD.Main.ForMathlib.RingTheory.Valuation.AddVal.Basic
import Mathlib.RingTheory.Valuation.RankOne

/-!
# The real additive valuation of a rank-one valuation

For a rank-one valuation `v` we build `Valuation.RankOne.addVal`, the additive valuation
`x ↦ -log ‖x‖` with values in `WithTop ℝ = ℝ ∪ {∞}` and `∞` at `0`.

This is the *unnormalised* member of the family: it takes no normalising element, and
correspondingly `addVal v π` is `-log ‖π‖` rather than `1`.  The normalised refinements are
`Valuation.addValQ` (`Commensurable.lean`) and `Valuation.IsRankOneDiscrete.addValZ`
(`Discrete.lean`), and `Commensurable.lean` records the rescaling that relates them.

## Main definitions

* `Valuation.RankOne.realValuation`, the `ℝᵐ⁰`-valued valuation attached to a rank-one valuation;
* `Valuation.RankOne.addVal : AddValuation R (WithTop ℝ)`, its additive valuation.

Everything here is meant to be redistributed into the relevant `Mathlib` files.
-/

open scoped NNReal WithZero

namespace Valuation.RankOne

open MonoidWithZeroHom WithZero

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation R Γ₀) [RankOne v]

/-- The `ℝᵐ⁰`-valued valuation attached to a rank-one valuation. -/
noncomputable def realValuation : Valuation R ℝᵐ⁰ :=
  v.restrict.map (NNReal.toRealMultZero.comp (RankOne.hom v))
    ((NNReal.toRealMultZero_strictMono.comp (RankOne.strictMono v)).monotone)

/-- **The real additive valuation of a rank-one valuation**, `x ↦ -log ‖x‖`, valued in
`WithTop ℝ = ℝ ∪ {∞}` with `∞` at `0`. -/
noncomputable def addVal : AddValuation R (WithTop ℝ) := (realValuation v).addVal

@[simp] lemma addVal_apply (x : R) :
    addVal v x = negLog (NNReal.toRealMultZero (RankOne.hom v (v.restrict x))) := rfl

@[simp] lemma addVal_zero : addVal v 0 = ⊤ := AddValuation.map_zero _

@[simp] lemma addVal_eq_top {x : R} : addVal v x = ⊤ ↔ v x = 0 := by
  rw [addVal, Valuation.addVal_eq_top]
  show NNReal.toRealMultZero (RankOne.hom v (v.restrict x)) = 0 ↔ v x = 0
  rw [map_eq_zero, RankOne.hom_eq_zero_iff, restrict_eq_zero_iff]

/-- On elements of nonzero valuation the real additive valuation is `-log ‖x‖`. -/
lemma addVal_apply_of_val_ne_zero {x : R} (hx : v x ≠ 0) :
    addVal v x = ((-Real.log (RankOne.hom v (v.restrict x)) : ℝ) : WithTop ℝ) := by
  have h : RankOne.hom v (v.restrict x) ≠ 0 := by
    rw [Ne, RankOne.hom_eq_zero_iff, restrict_eq_zero_iff]
    exact hx
  rw [addVal_apply, NNReal.toRealMultZero_of_ne_zero h, WithZero.negLog_exp]

end Valuation.RankOne
