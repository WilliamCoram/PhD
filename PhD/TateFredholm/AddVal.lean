/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TateFredholm.Tate
import PhD.ForMathlib.Topology.Algebra.Valued.AddVal

/-!
# The seam between `v_ϖ` and the additive-valuation API
(See `Tate.lean` for the development's overview and dictionary.)

`PseudoUniformizer.val` (`v_ϖ`) and `ForMathlib`'s `Valuation.addVal` family solve the same
problem in incomparable settings, and this file pins them together.

* `v_ϖ` lives on a Banach–Tate ring, whose norm is only *sub*multiplicative.  There is no
  `Valuation` there, so none of `ForMathlib/RingTheory/Valuation/AddVal/` applies, and
  `v_ϖ` is correspondingly only superadditive on products.
* `Valuation.addVal` and friends need an honest multiplicative valuation, and in exchange give
  an honest `AddValuation`, the `ℚ`- and `ℤ`-valued refinements, and the naturality squares.

Where both apply — over an ultrametric normed field, i.e. along the bridge
`isTate_of_normedAlgebra` — they agree up to the normalisation: `v_ϖ` is
`NormedField.normAddVal` rescaled by `-log ‖ϖ‖` (`val_eq_map_normAddVal`).  So the ring-level
object is not a rival definition but the unnormalised one rescaled, and a future divergence
between the two is a build error rather than a silent fork.

## Main statements

* `negLogNorm_eq_negLog`: `-log ‖r‖` computed by `negLogNorm` is the `WithZero.negLog` of the
  norm read in `ℝᵐ⁰` — the two constructions are literally the same map.
* `negLogNorm_eq_normAddVal`: over an ultrametric normed field, `negLogNorm` *is*
  `NormedField.normAddVal`.
* `PseudoUniformizer.val_eq_map_normAddVal`: `v_ϖ` is that, rescaled by `-log ‖ϖ‖`.
-/

open Valuation WithZero

/-- `negLogNorm` and `WithZero.negLog` are the same construction: reading the norm in `ℝᵐ⁰`
and taking `negLog` gives back `-log ‖r‖` with `⊤` at `0`. -/
theorem negLogNorm_eq_negLog {E : Type*} [SeminormedAddGroup E] (r : E) :
    negLogNorm r = negLog (NNReal.toRealMultZero ‖r‖₊) := by
  rcases eq_or_ne ‖r‖ 0 with h | h
  · have h' : ‖r‖₊ = 0 := by rw [← NNReal.coe_eq_zero, coe_nnnorm]; exact h
    rw [negLogNorm_of_norm_eq_zero h, h', map_zero, negLog_zero]
  · have h' : ‖r‖₊ ≠ 0 := fun h' ↦ h (by rw [← coe_nnnorm, h', NNReal.coe_zero])
    rw [negLogNorm_of_norm_ne_zero h, NNReal.toRealMultZero_of_ne_zero h', negLog_exp, coe_nnnorm]

/-- Over an ultrametric normed field, `negLogNorm` is exactly the additive valuation
`x ↦ -log ‖x‖` of `ForMathlib`'s `AddVal`. -/
theorem negLogNorm_eq_normAddVal (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    (x : K) : negLogNorm x = NormedField.normAddVal K x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [negLogNorm_zero, NormedField.normAddVal_zero]
  · rw [negLogNorm_of_ne_zero hx, NormedField.normAddVal_apply_of_ne_zero K hx]

namespace TateFredholm

/-- **The compatibility with `AddVal`.**  Over an ultrametric normed field, `v_ϖ` is
`NormedField.normAddVal` rescaled by `-log ‖ϖ‖`; the rescaling is what turns the unnormalised
`x ↦ -log ‖x‖` into the `ϖ`-normalised valuation with `v_ϖ(ϖ) = 1`.

This is the exact analogue of `Valuation.RankOne.addVal_eq_map_addValQ`, whose rescaling factor
is the same `-log ‖π‖`.  In particular, if the valuation of `K` is additionally commensurable at
`ϖ`, then `Valuation.addValQ` refines `v_ϖ` to a `WithTop ℚ`-valued `AddValuation` — the
ring-level definition here does not compete with that, it is its unnormalised shadow. -/
theorem PseudoUniformizer.val_eq_map_normAddVal (K : Type*) [NontriviallyNormedField K]
    [IsUltrametricDist K] (ϖ : PseudoUniformizer K) (x : K) :
    ϖ.val x = WithTop.map (· * (-Real.log ‖(ϖ : K)‖)⁻¹) (NormedField.normAddVal K x) := by
  rw [PseudoUniformizer.val_def, negLogNorm_eq_normAddVal]

end TateFredholm
