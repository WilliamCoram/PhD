/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.ForMathlib.RingTheory.Valuation.AddVal.Commensurable
import Mathlib.Data.Int.WithZero
import Mathlib.RingTheory.Valuation.Discrete.RankOne

/-!
# Discrete valuations: an honest `ℤ`-valued additive valuation

For a valuation of rank one *discrete* the value group is infinite cyclic, so the additive
valuation can be taken with values in `WithTop ℤ = ℤ ∪ {∞}` rather than `WithTop ℚ` or
`WithTop ℝ`.

## Main definitions

* `Valuation.IsRankOneDiscrete.addValZ : AddValuation R (WithTop ℤ)`.

## Main results

* `Valuation.IsRankOneDiscrete.isCommensurable`: a discrete valuation is commensurable at any
  uniformizer, so the `ℚ`-valued theory of `Commensurable.lean` applies to it;
* `Valuation.addValQ_eq_map_addValZ`: and it is then the `ℤ`-valued one composed with `Int.cast`.
  So the `ℚ`-valued theory subsumes the `ℤ`-valued one *as values*, but not as types: `addValZ`
  is the genuinely `WithTop ℤ`-valued object;
* `Valuation.IsRankOneDiscrete.hom_eq_zpow_neg_addValZ`: `‖x‖ = e ^ (-d)` once a uniformizer is
  known to have norm `e⁻¹`.  On a discrete valuation that single scalar suffices — the value
  group is infinite cyclic, so a `→*₀` out of it is determined by its value on the generator
  (`Valuation.hb_of_norm_generator`).

Everything here is meant to be redistributed into the relevant `Mathlib` files.
-/

open scoped NNReal WithZero

namespace Valuation

open MonoidWithZeroHom WithZero IsRankOneDiscrete

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)
  [v.IsRankOneDiscrete]

/-- On a discrete valuation every nonzero value is an integer power of a uniformizer: the `n = 1`
case of commensurability. -/
lemma IsRankOneDiscrete.exists_zpow_eq_of_isUniformizer {π : R} (hπ : IsUniformizer v π)
    {x : R} (hx : v x ≠ 0) : ∃ k : ℤ, v x = v π ^ k := by
  have hu : Units.mk0 (v x) hx ∈ valueGroup (.ofClass v) := mem_valueGroup _ ⟨x, rfl⟩
  rw [hπ.zpowers_eq_valueGroup, Subgroup.mem_zpowers_iff] at hu
  obtain ⟨k, hk⟩ := hu
  refine ⟨k, ?_⟩
  rw [← Units.val_mk0 hx, ← hk, Units.val_zpow_eq_zpow_val, Units.val_mk0]

/-- **`IsRankOneDiscrete ⟹ IsCommensurable` at any uniformizer.**  A discrete valuation has
rational rank one, normalised at a uniformizer. -/
lemma IsRankOneDiscrete.isCommensurable {π : R} (hπ : IsUniformizer v π) :
    v.IsCommensurable π where
  val_pos := hπ.val_pos
  val_lt_one := hπ.val_lt_one
  exists_zpow_eq x hx := by
    obtain ⟨k, hk⟩ := IsRankOneDiscrete.exists_zpow_eq_of_isUniformizer v hπ hx
    exact ⟨k, 1, one_pos, by rw [zpow_one, hk]⟩

/-- **The honest `ℤ`-valued additive valuation of a discrete valuation**, valued in
`WithTop ℤ = ℤ ∪ {∞}` with `∞` at `0`. -/
noncomputable def IsRankOneDiscrete.addValZ : AddValuation R (WithTop ℤ) :=
  (v.restrict.map (.ofClass (valueGroup₀_equiv_withZeroMulInt v))
    (valueGroup₀_equiv_withZeroMulInt_strictMono v).monotone).addVal

@[simp] lemma IsRankOneDiscrete.addValZ_apply (x : R) :
    IsRankOneDiscrete.addValZ v x = negLog (valueGroup₀_equiv_withZeroMulInt v (v.restrict x)) :=
  rfl

@[simp] lemma IsRankOneDiscrete.addValZ_zero : IsRankOneDiscrete.addValZ v 0 = ⊤ :=
  AddValuation.map_zero _

/-- A witness `v x = v π ^ k` at a uniformizer computes the `ℤ`-valued additive valuation. -/
lemma IsRankOneDiscrete.addValZ_eq_of_zpow {π : R} (hπ : IsUniformizer v π) {x : R} {k : ℤ}
    (hk : v x = v π ^ k) : IsRankOneDiscrete.addValZ v x = (k : WithTop ℤ) := by
  rw [addValZ_apply, negLog_eq_coe]
  have h1 : v.restrict x = v.restrict π ^ k := by
    apply ValueGroup₀.embedding_injective
    rw [map_zpow₀, embedding_restrict, embedding_restrict, hk]
  have h2 : v.restrict π
      = ((generator' v : valueGroup (.ofClass v)) : ValueGroup₀ (.ofClass v)) := by
    apply ValueGroup₀.embedding_injective
    rw [embedding_restrict, hπ]
    rfl
  rw [h1, h2, valueGroup₀_equiv_withZeroMulInt_apply_zpow]

/-- **Inclusion `WithTop ℤ → WithTop ℚ`.**  For a discrete valuation normalised at a uniformizer,
the `ℚ`-valued additive valuation is the `ℤ`-valued one composed with `Int.cast`.

So the `ℚ`-valued theory subsumes the `ℤ`-valued one *as values*, but not as types: `addValZ` is
the genuinely `WithTop ℤ`-valued object. -/
theorem addValQ_eq_map_addValZ {π : R} (hπ : IsUniformizer v π) [v.IsCommensurable π] (x : R) :
    v.addValQ π x = WithTop.map (fun n : ℤ ↦ (n : ℚ)) (IsRankOneDiscrete.addValZ v x) := by
  rcases eq_or_ne (v x) 0 with hx | hx
  · have h1 : v.addValQ π x = ⊤ := by
      rw [addValQ_apply, addValValueGroup_apply,
        show v.restrict x = 0 from v.restrict_eq_zero_iff.mpr hx]
      rfl
    have h2 : IsRankOneDiscrete.addValZ v x = ⊤ := by
      rw [addValZ_apply, show v.restrict x = 0 from v.restrict_eq_zero_iff.mpr hx]
      simp
    rw [h1, h2, WithTop.map_top]
  · obtain ⟨k, hk⟩ := IsRankOneDiscrete.exists_zpow_eq_of_isUniformizer v hπ hx
    rw [addValQ_eq_of_zpow v π hx one_pos (by rw [zpow_one, hk]),
      IsRankOneDiscrete.addValZ_eq_of_zpow v hπ hk, WithTop.map_coe]
    norm_num

private lemma toNNReal_exp {e : ℝ≥0} (he : e ≠ 0) (n : ℤ) :
    WithZeroMulInt.toNNReal he (exp n) = e ^ n :=
  WithZeroMulInt.toNNReal_neg_apply he exp_ne_zero

/-- **The factorization follows from one scalar.**  On a discrete valuation the value group is
infinite cyclic, so a `→*₀` hom out of it is determined by its value on the generator: to know that
a given `RankOne.hom v` is "`exp` in base `e`", it suffices that a uniformizer has norm `e⁻¹`. -/
lemma hb_of_norm_generator [RankOne v] {e : ℝ≥0} (he : e ≠ 0)
    (hgen : RankOne.hom v (generator' v : ValueGroup₀ (.ofClass v)) = e⁻¹) :
    RankOne.hom v =
      (WithZeroMulInt.toNNReal he).comp (.ofClass (valueGroup₀_equiv_withZeroMulInt v)) := by
  refine MonoidWithZeroHom.ext fun γ ↦ ?_
  induction γ using WithZero.recZeroCoe with
  | zero => simp
  | coe u =>
    obtain ⟨k, rfl⟩ : ∃ k : ℤ, generator' v ^ k = u :=
      Subgroup.mem_zpowers_iff.mp (by rw [generator'_zpowers_eq_top]; exact Subgroup.mem_top u)
    rw [MonoidWithZeroHom.comp_apply, MonoidWithZeroHom.coe_ofClass, WithZero.coe_zpow,
      valueGroup₀_equiv_withZeroMulInt_apply_zpow, toNNReal_exp he, map_zpow₀, hgen, inv_zpow,
      ← zpow_neg]

/-- **The absolute value is the base to the power of minus the `ℤ`-valued additive valuation.**  If
a uniformizer has norm `e⁻¹` (which pins `e = ‖ϖ‖⁻¹`) and `addValZ v x = d`, then `‖x‖ = e ^ (-d)`. -/
theorem IsRankOneDiscrete.hom_eq_zpow_neg_addValZ [RankOne v] {e : ℝ≥0} (he : e ≠ 0)
    (hgen : RankOne.hom v (generator' v : ValueGroup₀ (.ofClass v)) = e⁻¹)
    {x : R} {d : ℤ} (hd : IsRankOneDiscrete.addValZ v x = (d : WithTop ℤ)) :
    RankOne.hom v (v.restrict x) = e ^ (-d) := by
  rw [IsRankOneDiscrete.addValZ_apply, negLog_eq_coe] at hd
  rw [hb_of_norm_generator v he hgen, MonoidWithZeroHom.comp_apply,
    MonoidWithZeroHom.coe_ofClass, hd, toNNReal_exp he]

end Valuation
