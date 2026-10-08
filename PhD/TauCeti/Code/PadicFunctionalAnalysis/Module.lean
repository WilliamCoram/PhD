/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Constructions of nonarchimedean Banach modules

A normed module over a nonarchimedean normed ring `R` is `[NormedAddCommGroup M] [Module R M]
[IsBoundedSMul R M] [IsUltrametricDist M]` (roadmap convention 1); there is no bundled class. This
file supplies the instances Mathlib lacks for the standard constructions — binary products,
submodules, quotients — and the transfer of completeness along a linear equivalence that is bounded
in both directions, which is how "bounded-equivalent norms" are expressed without putting two norms
on one type.

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, §0.3.1–§0.3.2. Tau Ceti home:
`TauCeti/Analysis/Normed/Module/Ultra/Basic.lean`.

## Main results

* `Prod.instIsUltrametricDist` — a binary product of ultrametric spaces is ultrametric.
* `Submodule.instIsBoundedSMul` — a submodule of a normed module is a normed module.
* `QuotientAddGroup.instIsUltrametricDist` — the quotient norm is ultrametric.
* `AddEquiv.completeSpace_congr_of_bounds` — completeness transfers along a bounded-equivalence.
-/

open Filter Topology

/-- Source: roadmap §0.3.1 ("finite products with the max norm"). -/
instance Prod.instIsUltrametricDist {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [IsUltrametricDist X] [IsUltrametricDist Y] : IsUltrametricDist (X × Y) := by
  refine ⟨fun x y z ↦ ?_⟩
  simp only [Prod.dist_eq]
  refine max_le ?_ ?_
  · exact (IsUltrametricDist.dist_triangle_max _ _ _).trans
      (max_le_max (le_max_left _ _) (le_max_left _ _))
  · exact (IsUltrametricDist.dist_triangle_max _ _ _).trans
      (max_le_max (le_max_right _ _) (le_max_right _ _))

/-- Source: roadmap §0.3.1 ("a closed submodule with the restricted norm"). -/
instance Submodule.instIsBoundedSMul {R M : Type*} [SeminormedRing R] [SeminormedAddCommGroup M]
    [Module R M] [IsBoundedSMul R M] (S : Submodule R M) : IsBoundedSMul R S := by
  exact .of_norm_smul_le fun r x ↦ norm_smul_le r (x : M)

section Quotient

variable {M : Type*} [SeminormedAddCommGroup M] [IsUltrametricDist M]

/-- Source: roadmap §0.3.1 ("the quotient norm ... is again ultrametric"); Schneider, §5.B (the
quotient seminorm `q(v + U) = inf_{u ∈ U} q(v + u)`). -/
instance QuotientAddGroup.instIsUltrametricDist (S : AddSubgroup M) :
    IsUltrametricDist (M ⧸ S) := by
  refine IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun x y ↦ ?_
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  obtain ⟨m, rfl, hm⟩ := QuotientAddGroup.norm_lt_iff.1 (lt_add_of_pos_right ‖x‖ hε)
  obtain ⟨n, rfl, hn⟩ := QuotientAddGroup.norm_lt_iff.1 (lt_add_of_pos_right ‖y‖ hε)
  calc ‖(m : M ⧸ S) + n‖ = ‖((m + n : M) : M ⧸ S)‖ := rfl
    _ ≤ ‖m + n‖ := QuotientAddGroup.norm_mk_le_norm
    _ ≤ max ‖m‖ ‖n‖ := IsUltrametricDist.norm_add_le_max m n
    _ < max (‖(m : M ⧸ S)‖ + ε) (‖(n : M ⧸ S)‖ + ε) := max_lt_max hm hn
    _ = max ‖(m : M ⧸ S)‖ ‖(n : M ⧸ S)‖ + ε := max_add_add_right _ _ _

/-- Source: roadmap §0.3.1. -/
instance Submodule.Quotient.instIsUltrametricDist {R : Type*} [Ring R] [Module R M]
    (S : Submodule R M) : IsUltrametricDist (M ⧸ S) := by
  exact inferInstanceAs (IsUltrametricDist (M ⧸ S.toAddSubgroup))

end Quotient

/-- Source: roadmap §0.3.1 (quotient rings of nonarchimedean normed rings). -/
instance Ideal.Quotient.instIsUltrametricDist {R : Type*} [SeminormedCommRing R]
    [IsUltrametricDist R] (I : Ideal R) : IsUltrametricDist (R ⧸ I) := by
  exact inferInstanceAs (IsUltrametricDist (R ⧸ I.toAddSubgroup))

/-- Source: roadmap §0.3.2 ("bounded-equivalent norms have ... the same Cauchy sequences");
Schneider, proof of Proposition 10.1 (the rescaled norm "defines the same topology"). -/
theorem AddEquiv.completeSpace_congr_of_bounds {E F : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] (e : E ≃+ F) {C C' : ℝ} (h : ∀ x, ‖e x‖ ≤ C * ‖x‖)
    (h' : ∀ y, ‖e.symm y‖ ≤ C' * ‖y‖) : CompleteSpace E ↔ CompleteSpace F := by
  let u : E ≃ᵤ F :=
    { toEquiv := e.toEquiv
      uniformContinuous_toFun := (AddMonoidHomClass.lipschitz_of_bound e C h).uniformContinuous
      uniformContinuous_invFun :=
        (AddMonoidHomClass.lipschitz_of_bound e.symm C' h').uniformContinuous }
  exact u.completeSpace_iff
