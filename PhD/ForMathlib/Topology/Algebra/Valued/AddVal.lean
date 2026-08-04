/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.ForMathlib.RingTheory.Valuation.AddVal.Discrete
import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Additive valuations of an ultrametric normed field

The additive valuations of `PhD/ForMathlib/RingTheory/Valuation/AddVal/` applied to
`NormedField.valuation`, i.e. read off the norm of an ultrametric normed field directly.

## Main definitions

* `NormedField.normAddVal : AddValuation K (WithTop ℝ)`, the additive valuation `x ↦ -log ‖x‖`;
* `NormedField.normAddValZ : AddValuation K (WithTop ℤ)` in the discretely valued case;
* `NormedField.normAddValQ K π : AddValuation K (WithTop ℚ)` in the rational-rank-one case,
  normalised at `π` (so `normAddValQ K π π = 1`).  For `ℂ_p` one takes `π = p`.

## Main results

* `NormedField.norm_eq_zpow_neg_normAddValZ`: `‖x‖ = e ^ (-d)`, the discrete case;
* `NormedField.norm_eq_norm_rpow_normAddValQ`: `‖x‖ = ‖π‖ ^ q`, with no exponential base and no
  factorisation hypothesis — the normalisation at `π` pins the base to `‖π‖⁻¹`.

Everything here is meant to be redistributed into the relevant `Mathlib` files.
-/

open scoped NNReal WithZero

namespace Valuation.RankOne

variable {L Γ₀ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation L Γ₀) [RankOne v]

/-- On a field, the real additive valuation is literally `x ↦ -log ‖x‖`. -/
lemma addVal_apply_of_ne_zero {x : L} (hx : x ≠ 0) :
    addVal v x = ((-Real.log (v.norm x) : ℝ) : WithTop ℝ) := by
  have h : RankOne.hom v (v.restrict x) ≠ 0 := by
    rw [Ne, RankOne.hom_eq_zero_iff, v.restrict_eq_zero_iff, v.zero_iff]
    exact hx
  rw [addVal_apply, NNReal.toRealMultZero_of_ne_zero h, WithZero.negLog_exp]
  rfl

end Valuation.RankOne

namespace NormedField

open Valuation MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀ WithZero

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]

/-- The real-valued norm attached to `NormedField.valuation` is just `‖·‖`. -/
@[simp] lemma valuation_norm_eq (x : K) : (valuation (K := K)).norm x = ‖x‖ := by
  rw [Valuation.norm_def, Valuation.restrict_def]
  show ((embedding (restrict₀ (.ofClass (valuation (K := K))) x) : ℝ≥0) : ℝ) = ‖x‖
  rw [embedding_restrict₀]
  rfl

private lemma norm_eq_coe_hom (x : K) :
    ‖x‖ = ((RankOne.hom (valuation (K := K)) ((valuation (K := K)).restrict x) : ℝ≥0) : ℝ) := by
  rw [← valuation_norm_eq K x]; rfl

/-- **The additive valuation `x ↦ -log ‖x‖`** of an ultrametric normed field. -/
noncomputable def normAddVal : AddValuation K (WithTop ℝ) := RankOne.addVal (valuation (K := K))

@[simp] lemma normAddVal_zero : normAddVal K 0 = ⊤ := AddValuation.map_zero _

lemma normAddVal_apply_of_ne_zero {x : K} (hx : x ≠ 0) :
    normAddVal K x = ((-Real.log ‖x‖ : ℝ) : WithTop ℝ) := by
  rw [normAddVal, RankOne.addVal_apply_of_ne_zero _ hx, valuation_norm_eq]

/-! ### The discrete (`ℚ_p`-style) case -/

/-- The honest `ℤ`-valued additive valuation of a discretely-valued ultrametric normed field. -/
noncomputable def normAddValZ [(valuation (K := K)).IsRankOneDiscrete] :
    AddValuation K (WithTop ℤ) :=
  IsRankOneDiscrete.addValZ (valuation (K := K))

@[simp] lemma normAddValZ_zero [(valuation (K := K)).IsRankOneDiscrete] :
    normAddValZ K 0 = ⊤ := AddValuation.map_zero _

/-- **The norm is the base to the power of minus the additive valuation.**  If a uniformizer has
norm `e⁻¹` (which pins `e = ‖ϖ‖⁻¹`) and `normAddValZ K x = d`, then `‖x‖ = e ^ (-d)`.  For the
standard `p`-adic norm `e = p`, so `‖x‖ = p ^ (-vₚ x)`. -/
theorem norm_eq_zpow_neg_normAddValZ [(valuation (K := K)).IsRankOneDiscrete] {e : ℝ≥0}
    (he : e ≠ 0)
    (hgen : RankOne.hom (valuation (K := K))
      (IsRankOneDiscrete.generator' (valuation (K := K)) :
        ValueGroup₀ (.ofClass (valuation (K := K)))) = e⁻¹)
    {x : K} {d : ℤ} (hd : normAddValZ K x = (d : WithTop ℤ)) :
    ‖x‖ = (e : ℝ) ^ (-d) := by
  rw [norm_eq_coe_hom K x,
    IsRankOneDiscrete.hom_eq_zpow_neg_addValZ (valuation (K := K)) he hgen hd, NNReal.coe_zpow]

/-! ### The rational-rank-one (`ℂ_p`-style) case -/

/-- The honest `ℚ`-valued additive valuation of an ultrametric normed field of rational rank one,
normalised at `π` (so `normAddValQ K π π = 1`).  For `ℂ_p` one takes `π = p`. -/
noncomputable def normAddValQ (π : K) [(valuation (K := K)).IsCommensurable π] :
    AddValuation K (WithTop ℚ) :=
  Valuation.addValQ (valuation (K := K)) π

@[simp] lemma normAddValQ_zero (π : K) [(valuation (K := K)).IsCommensurable π] :
    normAddValQ K π 0 = ⊤ := AddValuation.map_zero _

@[simp] lemma normAddValQ_self (π : K) [(valuation (K := K)).IsCommensurable π] :
    normAddValQ K π π = 1 := Valuation.addValQ_self _ _

/-- **`‖x‖ = ‖π‖ ^ q`.**  On an ultrametric normed field of rational rank one, the norm is the norm
of the normalising element raised to the `ℚ`-valued additive valuation.  For `ℂ_p` with `π = p` this
reads `‖x‖ = p ^ (-v x)`. -/
theorem norm_eq_norm_rpow_normAddValQ (π : K) [(valuation (K := K)).IsCommensurable π]
    {x : K} {q : ℚ} (hq : normAddValQ K π x = (q : WithTop ℚ)) :
    ‖x‖ = ‖π‖ ^ (q : ℝ) := by
  rw [norm_eq_coe_hom K x, norm_eq_coe_hom K π]
  exact Valuation.RankOne.hom_eq_rpow_addValQ (valuation (K := K)) π hq

end NormedField
