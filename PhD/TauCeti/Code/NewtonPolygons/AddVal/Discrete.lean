/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import PhD.TauCeti.Code.NewtonPolygons.AddVal.Commensurable

/-!
# Discrete rank one: the `ℤ`-valued additive valuation

For a valuation of rank one *discrete* the value group is infinite cyclic, so the additive
valuation can be taken with values in `WithTop ℤ = ℤ ∪ {∞}` rather than `WithTop ℚ` or
`WithTop ℝ`.

Roadmap: `PhD/TauCeti/Roadmaps/NewtonPolygons/README.md`, §1.3.1–§1.3.3 and the discrete half of
§1.4.5. Tau Ceti home: `TauCeti/RingTheory/Valuation/AddValuation/Discrete.lean`.

## Main definitions

* `Valuation.IsRankOneDiscrete.addValZ : AddValuation R (WithTop ℤ)`.

## Main results

* `Valuation.IsRankOneDiscrete.addValZ_eq_iff`: `addValZ v x = k ↔ v x = generator v ^ k`, and its
  form at a uniformiser, `addValZ_eq_iff_of_isUniformizer : addValZ v x = k ↔ v x = v π ^ k`;
* `Valuation.IsRankOneDiscrete.isCommensurable`: a discrete valuation is commensurable at any
  uniformiser (indeed at any element of valuation strictly between `0` and `1`), so the `ℚ`-valued
  theory of `Commensurable.lean` applies to it;
* `Valuation.addValQ_eq_map_addValZ`: and it is then the `ℤ`-valued one composed with `Int.cast`;
* `Valuation.IsRankOneDiscrete.hom_eq_zpow_neg_addValZ`: `‖x‖ = e ^ (-d)` once a uniformiser is
  known to have norm `e⁻¹`. On a discrete valuation that single scalar suffices — the value group
  is infinite cyclic, so a `→*₀` out of it is determined by its value on the generator
  (`Valuation.IsRankOneDiscrete.hom_eq_toNNReal_comp`).
-/

open scoped NNReal WithZero

namespace Valuation

open MonoidWithZeroHom WithZero IsRankOneDiscrete

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)
  [v.IsRankOneDiscrete]

/-- On a discrete valuation every nonzero value is an integer power of the generator. -/
lemma IsRankOneDiscrete.exists_zpow_generator_eq {x : R} (hx : v x ≠ 0) :
    ∃ k : ℤ, v x = ((generator v ^ k : Γ₀ˣ) : Γ₀) := by
  have hu : Units.mk0 (v x) hx ∈ valueGroup (.ofClass v) := mem_valueGroup _ ⟨x, rfl⟩
  rw [← generator_zpowers_eq_valueGroup, Subgroup.mem_zpowers_iff] at hu
  obtain ⟨k, hk⟩ := hu
  exact ⟨k, by rw [hk, Units.val_mk0]⟩

/-- On a discrete valuation every nonzero value is an integer power of a uniformiser: the `n = 1`
case of commensurability. -/
lemma IsRankOneDiscrete.exists_zpow_eq_of_isUniformizer {π : R} (hπ : IsUniformizer v π)
    {x : R} (hx : v x ≠ 0) : ∃ k : ℤ, v x = v π ^ k := by
  obtain ⟨k, hk⟩ := exists_zpow_generator_eq v hx
  exact ⟨k, by rw [hk, hπ.val, Units.val_zpow_eq_zpow_val]⟩

/-- A discrete valuation is commensurable at every element of valuation strictly between `0`
and `1`. -/
lemma IsRankOneDiscrete.isCommensurable_of_lt_one {π : R} (h0 : v π ≠ 0) (h1 : v π < 1) :
    v.IsCommensurable π where
  val_pos := zero_lt_iff.mpr h0
  val_lt_one := h1
  exists_zpow_eq x hx := by
    obtain ⟨k, hk⟩ := exists_zpow_generator_eq v hx
    obtain ⟨j, hj⟩ := exists_zpow_generator_eq v h0
    have hg1 : ((generator v : Γ₀ˣ) : Γ₀) < 1 := by
      simpa using Units.val_lt_val.mpr (generator_lt_one v)
    have hg0 : (0 : Γ₀) < (generator v : Γ₀ˣ) := zero_lt_iff.mpr (Units.ne_zero _)
    have hj0 : 0 < j := by
      rw [hj, Units.val_zpow_eq_zpow_val] at h1
      exact (zpow_lt_one_iff_right_of_lt_one₀ hg0 hg1).mp h1
    refine ⟨k, j, hj0, ?_⟩
    rw [hk, hj, ← Units.val_zpow_eq_zpow_val, ← Units.val_zpow_eq_zpow_val, ← zpow_mul,
      ← zpow_mul, mul_comm]

/-- **`IsRankOneDiscrete ⟹ IsCommensurable` at any uniformiser.** A discrete valuation has
rational rank one, normalised at a uniformiser. -/
lemma IsRankOneDiscrete.isCommensurable {π : R} (hπ : IsUniformizer v π) :
    v.IsCommensurable π :=
  isCommensurable_of_lt_one v hπ.val_ne_zero hπ.val_lt_one

/-- **The `ℤ`-valued additive valuation of a discrete valuation**, valued in
`WithTop ℤ = ℤ ∪ {∞}` with `∞` at `0`. -/
noncomputable def IsRankOneDiscrete.addValZ : AddValuation R (WithTop ℤ) :=
  (v.restrict.map (.ofClass (valueGroup₀_equiv_withZeroMulInt v))
    (valueGroup₀_equiv_withZeroMulInt_strictMono v).monotone).addVal

lemma IsRankOneDiscrete.addValZ_apply (x : R) :
    addValZ v x = negLog (valueGroup₀_equiv_withZeroMulInt v (v.restrict x)) := rfl

lemma IsRankOneDiscrete.addValZ_zero : addValZ v 0 = ⊤ := AddValuation.map_zero _

@[simp] lemma IsRankOneDiscrete.addValZ_eq_top {x : R} : addValZ v x = ⊤ ↔ v x = 0 := by
  rw [addValZ_apply, negLog_eq_top, map_eq_zero, restrict_eq_zero_iff]

/-- The characterisation of the `ℤ`-valued additive valuation by the generator. -/
theorem IsRankOneDiscrete.addValZ_eq_iff (x : R) (k : ℤ) :
    addValZ v x = (k : WithTop ℤ) ↔ v x = ((generator v ^ k : Γ₀ˣ) : Γ₀) := by
  rw [addValZ_apply, negLog_eq_coe, ← valueGroup₀_equiv_withZeroMulInt_apply_zpow v k,
    (EquivLike.injective (valueGroup₀_equiv_withZeroMulInt v)).eq_iff,
    ← (ValueGroup₀.embedding_injective (f := .ofClass v)).eq_iff, embedding_restrict, map_zpow₀,
    embedding_generator', Units.val_zpow_eq_zpow_val]

/-- A witness `v x = v π ^ k` at a uniformiser computes the `ℤ`-valued additive valuation. -/
lemma IsRankOneDiscrete.addValZ_eq_of_zpow {π : R} (hπ : IsUniformizer v π) {x : R} {k : ℤ}
    (hk : v x = v π ^ k) : addValZ v x = (k : WithTop ℤ) :=
  (addValZ_eq_iff v x k).mpr (by rw [hk, hπ.val, Units.val_zpow_eq_zpow_val])

/-- The characterisation of the `ℤ`-valued additive valuation by a uniformiser. -/
theorem IsRankOneDiscrete.addValZ_eq_iff_of_isUniformizer {π : R} (hπ : IsUniformizer v π)
    (x : R) (k : ℤ) : addValZ v x = (k : WithTop ℤ) ↔ v x = v π ^ k := by
  rw [addValZ_eq_iff, hπ.val, Units.val_zpow_eq_zpow_val]

/-- A uniformiser has `ℤ`-valued additive valuation `1`. -/
theorem IsRankOneDiscrete.addValZ_isUniformizer {π : R} (hπ : IsUniformizer v π) :
    addValZ v π = 1 :=
  (addValZ_eq_of_zpow v hπ (zpow_one (v π)).symm).trans WithTop.coe_one

lemma IsRankOneDiscrete.addValZ_le_addValZ {x y : R} :
    addValZ v x ≤ addValZ v y ↔ v y ≤ v x := by
  rw [addValZ_apply, addValZ_apply, negLog_le_negLog,
    (valueGroup₀_equiv_withZeroMulInt_strictMono v).le_iff_le, restrict_le_iff]

/-- **Inclusion `WithTop ℤ → WithTop ℚ`.** For a discrete valuation normalised at a uniformiser,
the `ℚ`-valued additive valuation is the `ℤ`-valued one composed with `Int.cast`. -/
theorem addValQ_eq_map_addValZ {π : R} (hπ : IsUniformizer v π) [v.IsCommensurable π] (x : R) :
    v.addValQ π x = WithTop.map (fun n : ℤ ↦ (n : ℚ)) (addValZ v x) := by
  rcases eq_or_ne (v x) 0 with hx | hx
  · rw [(addValQ_eq_top v π).mpr hx, (addValZ_eq_top v).mpr hx, WithTop.map_top]
  · obtain ⟨k, hk⟩ := exists_zpow_eq_of_isUniformizer v hπ hx
    rw [addValQ_eq_of_zpow v π hx one_pos (by rw [zpow_one, hk]), addValZ_eq_of_zpow v hπ hk,
      WithTop.map_coe]
    norm_num

private lemma toNNReal_exp {e : ℝ≥0} (he : e ≠ 0) (n : ℤ) :
    WithZeroMulInt.toNNReal he (exp n) = e ^ n :=
  WithZeroMulInt.toNNReal_neg_apply he exp_ne_zero

/-- **The absolute value is determined by one scalar.** On a discrete valuation the value group is
infinite cyclic, so a `→*₀` hom out of it is determined by its value on the generator: if the
generator has absolute value `e⁻¹`, then `RankOne.hom v` is "`e` to the power" through
`valueGroup₀_equiv_withZeroMulInt`. -/
lemma IsRankOneDiscrete.hom_eq_toNNReal_comp [RankOne v] {e : ℝ≥0} (he : e ≠ 0)
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

/-- **The absolute value is the base to the power of minus the `ℤ`-valued additive valuation.**
If the generator has absolute value `e⁻¹` and `addValZ v x = d`, then `‖x‖ = e ^ (-d)`. -/
theorem IsRankOneDiscrete.hom_eq_zpow_neg_addValZ [RankOne v] {e : ℝ≥0} (he : e ≠ 0)
    (hgen : RankOne.hom v (generator' v : ValueGroup₀ (.ofClass v)) = e⁻¹)
    {x : R} {d : ℤ} (hd : addValZ v x = (d : WithTop ℤ)) :
    RankOne.hom v (v.restrict x) = e ^ (-d) := by
  rw [IsRankOneDiscrete.addValZ_apply, negLog_eq_coe] at hd
  rw [hom_eq_toNNReal_comp v he hgen, MonoidWithZeroHom.comp_apply,
    MonoidWithZeroHom.coe_ofClass, hd, toNNReal_exp he]

/-- The same, with the scalar hypothesis read off a uniformiser. -/
theorem IsRankOneDiscrete.hom_eq_zpow_neg_addValZ_of_isUniformizer [RankOne v] {π : R}
    (hπ : IsUniformizer v π) {e : ℝ≥0} (he : e ≠ 0)
    (hπe : RankOne.hom v (v.restrict π) = e⁻¹)
    {x : R} {d : ℤ} (hd : addValZ v x = (d : WithTop ℤ)) :
    RankOne.hom v (v.restrict x) = e ^ (-d) := by
  have h :
      v.restrict π = ((generator' v : valueGroup (.ofClass v)) : ValueGroup₀ (.ofClass v)) := by
    apply ValueGroup₀.embedding_injective
    rw [embedding_restrict, hπ]
    rfl
  rw [h] at hπe
  exact hom_eq_zpow_neg_addValZ v he hπe hd

end Valuation
