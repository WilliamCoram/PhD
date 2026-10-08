/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Topology.Algebra.Valued.NormedValued
import PhD.TauCeti.Code.NewtonPolygons.AddVal.Discrete

/-!
# Additive valuations of an ultrametric normed field

The additive valuations of `PhD/TauCeti/Code/NewtonPolygons/AddVal/` applied to
`NormedField.valuation`, i.e. read off the norm of an ultrametric normed field directly. These
are the three instances roadmap convention 2 is about, from least to most specific:
`normAddVal` (`ℝ`-valued, unnormalised), `normAddValQ K π` (`ℚ`-valued, normalised at `π`) and
`normAddValZ` (`ℤ`-valued, for a discretely valued field).

Roadmap: `PhD/TauCeti/Roadmaps/NewtonPolygons/README.md`, §1.2.2–§1.2.3, §1.3.4, §1.4.6. Tau Ceti
home: `TauCeti/Topology/Algebra/Valued/AddVal.lean`.

## Main definitions

* `NormedField.normAddVal : AddValuation K (WithTop ℝ)`, the additive valuation `x ↦ -log ‖x‖`;
* `NormedField.normAddValZ : AddValuation K (WithTop ℤ)` in the discretely valued case;
* `NormedField.normAddValQ K π : AddValuation K (WithTop ℚ)` in the rational-rank-one case,
  normalised at `π` (so `normAddValQ K π π = 1`). For `ℂ_p` one takes `π = p`.

## Main results

* `NormedField.normAddVal_unique`: `normAddVal K` is the only additive valuation into `WithTop ℝ`
  with `‖x‖ = exp (-(v x))`;
* `NormedField.norm_eq_zpow_neg_normAddValZ`: `‖x‖ = e ^ (-d)`, the discrete case;
* `NormedField.norm_eq_norm_rpow_normAddValQ`: `‖x‖ = ‖π‖ ^ q`, with no exponential base and no
  factorisation hypothesis — the normalisation at `π` pins the base to `‖π‖⁻¹`;
* the compatibility squares `normAddVal_eq_map_normAddValQ`, `normAddValQ_eq_map_normAddValZ`
  and `normAddVal_eq_map_normAddValZ`.
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

/-- The norm is the rank-one `hom` of the valuation, restricted to its value group. -/
lemma norm_eq_coe_hom (x : K) :
    ‖x‖ = ((RankOne.hom (valuation (K := K)) ((valuation (K := K)).restrict x) : ℝ≥0) : ℝ) := by
  rw [← valuation_norm_eq K x]; rfl

/-- **The additive valuation `x ↦ -log ‖x‖`** of an ultrametric normed field: the unnormalised
member of the family. -/
noncomputable def normAddVal : AddValuation K (WithTop ℝ) := RankOne.addVal (valuation (K := K))

lemma normAddVal_zero : normAddVal K 0 = ⊤ := AddValuation.map_zero _

lemma normAddVal_eq_top {x : K} : normAddVal K x = ⊤ ↔ x = 0 := by
  rw [normAddVal, RankOne.addVal_eq_top, Valuation.zero_iff]

lemma normAddVal_apply_of_ne_zero {x : K} (hx : x ≠ 0) :
    normAddVal K x = ((-Real.log ‖x‖ : ℝ) : WithTop ℝ) := by
  rw [normAddVal, RankOne.addVal_apply_of_ne_zero _ hx, valuation_norm_eq]

/-- **The defining equivalence**: on a nonzero element the real additive valuation is a real `r`
with `‖x‖ = exp (-r)`. -/
lemma exists_normAddVal_eq_and_norm_eq_exp_neg {x : K} (hx : x ≠ 0) :
    ∃ r : ℝ, normAddVal K x = (r : WithTop ℝ) ∧ ‖x‖ = Real.exp (-r) :=
  ⟨-Real.log ‖x‖, normAddVal_apply_of_ne_zero K hx,
    by rw [neg_neg, Real.exp_log (norm_pos_iff.mpr hx)]⟩

lemma normAddVal_le_normAddVal {x y : K} :
    normAddVal K x ≤ normAddVal K y ↔ ‖y‖ ≤ ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rw [normAddVal_apply_of_ne_zero K hx, normAddVal_apply_of_ne_zero K hy, WithTop.coe_le_coe,
    neg_le_neg_iff, Real.log_le_log_iff (norm_pos_iff.mpr hy) (norm_pos_iff.mpr hx)]

/-- **Uniqueness**: `normAddVal K` is the only additive valuation into `WithTop ℝ` satisfying the
defining equivalence `‖x‖ = exp (-(w x))` on nonzero elements. -/
theorem normAddVal_unique (w : AddValuation K (WithTop ℝ))
    (hw : ∀ x : K, x ≠ 0 → ∃ r : ℝ, w x = (r : WithTop ℝ) ∧ ‖x‖ = Real.exp (-r)) :
    w = normAddVal K := by
  refine AddValuation.ext fun x ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · rw [AddValuation.map_zero, normAddVal_zero]
  obtain ⟨r, hr, hxr⟩ := hw x hx
  have hr' : r = -Real.log ‖x‖ := by rw [hxr, Real.log_exp, neg_neg]
  rw [hr, hr', normAddVal_apply_of_ne_zero K hx]

/-! ### The discrete (`ℚ_p`-style) case -/

section Discrete

variable [(valuation (K := K)).IsRankOneDiscrete]

/-- The `ℤ`-valued additive valuation of a discretely valued ultrametric normed field. -/
noncomputable def normAddValZ : AddValuation K (WithTop ℤ) :=
  IsRankOneDiscrete.addValZ (valuation (K := K))

lemma normAddValZ_zero : normAddValZ K 0 = ⊤ := AddValuation.map_zero _

lemma normAddValZ_eq_top {x : K} : normAddValZ K x = ⊤ ↔ x = 0 := by
  rw [normAddValZ, IsRankOneDiscrete.addValZ_eq_top, Valuation.zero_iff]

/-- The characterisation by a uniformiser: `normAddValZ K x = k ↔ ‖x‖ = ‖π‖ ^ k`. -/
theorem normAddValZ_eq_iff_of_isUniformizer {π : K} (hπ : IsUniformizer (valuation (K := K)) π)
    (x : K) (k : ℤ) : normAddValZ K x = (k : WithTop ℤ) ↔ ‖x‖ = ‖π‖ ^ k := by
  rw [normAddValZ, IsRankOneDiscrete.addValZ_eq_iff_of_isUniformizer _ hπ, valuation_apply,
    valuation_apply, ← NNReal.coe_inj, NNReal.coe_zpow, coe_nnnorm, coe_nnnorm]

/-- A uniformiser has `ℤ`-valued additive valuation `1`. -/
theorem normAddValZ_isUniformizer {π : K} (hπ : IsUniformizer (valuation (K := K)) π) :
    normAddValZ K π = 1 :=
  IsRankOneDiscrete.addValZ_isUniformizer _ hπ

/-- **The norm is the base to the power of minus the additive valuation.** If the generator of
the value group is `e⁻¹` and `normAddValZ K x = d`, then `‖x‖ = e ^ (-d)`. -/
theorem norm_eq_zpow_neg_normAddValZ {e : ℝ≥0} (he : e ≠ 0)
    (hgen : RankOne.hom (valuation (K := K))
      (IsRankOneDiscrete.generator' (valuation (K := K)) :
        ValueGroup₀ (.ofClass (valuation (K := K)))) = e⁻¹)
    {x : K} {d : ℤ} (hd : normAddValZ K x = (d : WithTop ℤ)) :
    ‖x‖ = (e : ℝ) ^ (-d) := by
  rw [norm_eq_coe_hom K x, IsRankOneDiscrete.hom_eq_zpow_neg_addValZ _ he hgen hd, NNReal.coe_zpow]

/-- **Norm recovery at a uniformiser**: if a uniformiser has norm `e⁻¹` and `normAddValZ K x = d`,
then `‖x‖ = e ^ (-d)`. For the standard `p`-adic norm `e = p`, so `‖x‖ = p ^ (-vₚ x)`. -/
theorem norm_eq_zpow_neg_normAddValZ_of_isUniformizer {π : K}
    (hπ : IsUniformizer (valuation (K := K)) π) {e : ℝ} (hπe : ‖π‖ = e⁻¹)
    {x : K} {d : ℤ} (hd : normAddValZ K x = (d : WithTop ℤ)) : ‖x‖ = e ^ (-d) := by
  rw [(normAddValZ_eq_iff_of_isUniformizer K hπ x d).mp hd, hπe, inv_zpow']

/-- **The compatibility square `ℤ → ℝ`**: the real additive valuation is `-log ‖π‖` times the
`ℤ`-valued one, for a uniformiser `π`. -/
theorem normAddVal_eq_map_normAddValZ {π : K} (hπ : IsUniformizer (valuation (K := K)) π)
    (x : K) :
    normAddVal K x
      = WithTop.map (fun k : ℤ ↦ (k : ℝ) * (-Real.log ‖π‖)) (normAddValZ K x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [normAddVal_zero, normAddValZ_zero, WithTop.map_top]
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp ((normAddValZ_eq_top K).not.mpr hx)
  rw [← hd, WithTop.map_coe, normAddVal_apply_of_ne_zero K hx,
    (normAddValZ_eq_iff_of_isUniformizer K hπ x d).mp hd.symm, Real.log_zpow]
  congr 1
  ring

end Discrete

/-! ### The rational-rank-one (`ℂ_p`-style) case -/

section Commensurable

variable (π : K) [(valuation (K := K)).IsCommensurable π]

/-- The `ℚ`-valued additive valuation of an ultrametric normed field of rational rank one,
normalised at `π` (so `normAddValQ K π π = 1`). For `ℂ_p` one takes `π = p`. -/
noncomputable def normAddValQ : AddValuation K (WithTop ℚ) :=
  Valuation.addValQ (valuation (K := K)) π

lemma normAddValQ_zero : normAddValQ K π 0 = ⊤ := AddValuation.map_zero _

lemma normAddValQ_eq_top {x : K} : normAddValQ K π x = ⊤ ↔ x = 0 := by
  rw [normAddValQ, addValQ_eq_top, Valuation.zero_iff]

@[simp] lemma normAddValQ_self : normAddValQ K π π = 1 := addValQ_self _ _

/-- The workhorse, read off the norm: `‖x‖ ^ n = ‖π‖ ^ m` computes `normAddValQ K π x = m / n`. -/
lemma normAddValQ_eq_of_pow_eq_pow {x : K} (hx : x ≠ 0) {m n : ℕ} (hn : 0 < n)
    (h : ‖x‖ ^ n = ‖π‖ ^ m) :
    normAddValQ K π x = (((m : ℚ) / (n : ℚ) : ℚ) : WithTop ℚ) := by
  refine addValQ_eq_of_pow_eq_pow _ π ((Valuation.ne_zero_iff _).mpr hx) hn ?_
  rw [valuation_apply, valuation_apply, ← NNReal.coe_inj]
  push_cast
  exact h

/-- **`‖x‖ = ‖π‖ ^ q`.** On an ultrametric normed field of rational rank one, the norm is the norm
of the normalising element raised to the `ℚ`-valued additive valuation. For `ℂ_p` with `π = p` this
reads `‖x‖ = p ^ (-v x)`. -/
theorem norm_eq_norm_rpow_normAddValQ {x : K} {q : ℚ}
    (hq : normAddValQ K π x = (q : WithTop ℚ)) :
    ‖x‖ = ‖π‖ ^ (q : ℝ) := by
  rw [norm_eq_coe_hom K x, norm_eq_coe_hom K π]
  exact Valuation.RankOne.hom_eq_rpow_addValQ (valuation (K := K)) π hq

/-- **The compatibility square `ℚ → ℝ`**: the real additive valuation is `-log ‖π‖` times the
`ℚ`-valued one normalised at `π`. -/
theorem normAddVal_eq_map_normAddValQ (x : K) :
    normAddVal K x
      = WithTop.map (fun q : ℚ ↦ (q : ℝ) * (-Real.log ‖π‖)) (normAddValQ K π x) := by
  have h := Valuation.RankOne.addVal_eq_map_addValQ (valuation (K := K)) π x
  rwa [← norm_eq_coe_hom K π] at h

/-- **The compatibility square `ℤ → ℚ`**: on a discretely valued field normalised at a uniformiser,
the `ℚ`-valued additive valuation is the `ℤ`-valued one composed with `Int.cast`. -/
theorem normAddValQ_eq_map_normAddValZ [(valuation (K := K)).IsRankOneDiscrete]
    (hπ : IsUniformizer (valuation (K := K)) π) (x : K) :
    normAddValQ K π x = WithTop.map (fun n : ℤ ↦ (n : ℚ)) (normAddValZ K x) :=
  Valuation.addValQ_eq_map_addValZ _ hπ x

end Commensurable

end NormedField
