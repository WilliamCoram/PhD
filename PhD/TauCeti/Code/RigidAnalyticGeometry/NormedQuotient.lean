/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Quotient norms of ultrametric normed rings

The quotient seminorm of an ultrametric seminormed group is ultrametric, and the quotient of a
complete normed ring with `‖1‖ = 1` by a proper closed ideal again has `‖1‖ = 1`, because an
element at distance less than one from `1` is a unit. These are the two facts about
residue norms (BGR 6.1.1) that Mathlib's quotient-norm instances do not supply.

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, §1.1.1. Tau Ceti home:
`TauCeti/Analysis/Normed/Group/Quotient/Ultra.lean`.

## Main results

* `QuotientAddGroup.isUltrametricDist` — the quotient seminorm of an ultrametric seminormed
  group is ultrametric.
* `Ideal.Quotient.normOneClass_of_ne_top` — `‖1‖ = 1` in the quotient by a proper closed ideal.
* `Ideal.Quotient.norm_mk_eq_norm_of_forall_le` — the quotient norm is attained at a nearest
  representative.
-/

open Metric Topology

namespace QuotientAddGroup

variable {M : Type*} [SeminormedAddCommGroup M] [IsUltrametricDist M] (S : AddSubgroup M)

/-- The quotient seminorm of an ultrametric seminormed group is ultrametric: the infimum over
cosets of an ultrametric norm. Source: BGR 1.1.6 (the residue norm of a quotient group). -/
instance isUltrametricDist : IsUltrametricDist (M ⧸ S) := by
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ ?_
  by_contra! hlt
  obtain ⟨m₁, rfl, h₁⟩ := QuotientAddGroup.norm_lt_iff.1 ((le_max_left _ _).trans_lt hlt)
  obtain ⟨m₂, rfl, h₂⟩ := QuotientAddGroup.norm_lt_iff.1 ((le_max_right _ _).trans_lt hlt)
  have h : ‖(m₁ : M ⧸ S) + m₂‖ < ‖(m₁ : M ⧸ S) + m₂‖ :=
    QuotientAddGroup.norm_lt_iff.2 ⟨m₁ + m₂, QuotientAddGroup.mk_add S m₁ m₂,
      (IsUltrametricDist.norm_add_le_max m₁ m₂).trans_lt (max_lt h₁ h₂)⟩
  exact lt_irrefl _ h

end QuotientAddGroup

namespace Submodule.Quotient

variable {R M : Type*} [Ring R] [SeminormedAddCommGroup M] [Module R M] [IsUltrametricDist M]
  (S : Submodule R M)

instance isUltrametricDist : IsUltrametricDist (M ⧸ S) :=
  inferInstanceAs (IsUltrametricDist (M ⧸ S.toAddSubgroup))

end Submodule.Quotient

namespace Ideal.Quotient

variable {R : Type*} [SeminormedCommRing R] [IsUltrametricDist R] (I : Ideal R)

instance isUltrametricDist : IsUltrametricDist (R ⧸ I) :=
  inferInstanceAs (IsUltrametricDist (R ⧸ (I : Submodule R R)))

omit [IsUltrametricDist R] in
/-- The quotient norm of a residue class is attained by a representative whenever some
representative has the smallest norm in its coset. -/
theorem norm_mk_eq_norm_of_forall_le {f : R} (h : ∀ a ∈ I, ‖f‖ ≤ ‖f - a‖) :
    ‖Ideal.Quotient.mk I f‖ = ‖f‖ := by
  have hq : ‖Ideal.Quotient.mk I f‖ = Metric.infDist f (I : Set R) :=
    QuotientAddGroup.norm_mk (S := I.toAddSubgroup) f
  rw [hq]
  refine le_antisymm ?_ ((Metric.le_infDist ⟨0, I.zero_mem⟩).2 fun a ha ↦ ?_)
  · have h0 := Metric.infDist_le_dist_of_mem (x := f) I.zero_mem
    rwa [dist_zero_right] at h0
  · rw [dist_eq_norm]
    exact h a ha

end Ideal.Quotient

namespace Ideal.Quotient

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [CompleteSpace R]

/-- In a complete normed ring with `‖1‖ = 1`, every element at distance less than one from `1` is
a unit, so the residue class of `1` modulo a proper closed ideal has norm one.
Source: BGR 1.2.4/4 and 6.1.1 (the residue norm). -/
theorem normOneClass_of_ne_top (I : Ideal R) [IsClosed (I : Set R)] (hI : I ≠ ⊤) :
    NormOneClass (R ⧸ I) := by
  have h : ∀ a ∈ I, ‖(1 : R)‖ ≤ ‖1 - a‖ := fun a ha ↦ by
    by_contra! hlt
    rw [norm_one] at hlt
    have hu := isUnit_one_sub_of_norm_lt_one hlt
    rw [sub_sub_cancel] at hu
    exact hI (Ideal.eq_top_of_isUnit_mem I ha hu)
  exact ⟨by rw [← map_one (Ideal.Quotient.mk I), norm_mk_eq_norm_of_forall_le I h, norm_one]⟩

end Ideal.Quotient
