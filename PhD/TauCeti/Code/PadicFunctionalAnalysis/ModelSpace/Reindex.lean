/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Module
import PhD.TauCeti.Code.PadicFunctionalAnalysis.ModelSpace.Basic

/-!
# Reindexing and block decompositions of the model space

A bijection of index sets induces an isometry of model spaces; disjoint unions, products and finite
products of index sets correspond to products, iterated model spaces and finite powers, with the
max norm; and an isometric isomorphism (or, over a Tate ring, a continuous linear equivalence) of
the value module induces one of the model spaces. The finite block decomposition
`C₀(σ × I, E) ≃ₗᵢ (σ → C₀(I, E))` is what the compact-operators and overconvergent-forms roadmaps
use to assemble operators from `σ × σ` matrices of operators.

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, §2.1.4.
Tau Ceti home: `TauCeti/Analysis/Normed/Module/Ultra/ModelSpace/Reindex.lean`.

## Main declarations

* `ZeroAtInftyContinuousMap.reindex` — `C₀(I, E) ≃ₗᵢ[R] C₀(J, E)` from `I ≃ J`.
* `ZeroAtInftyContinuousMap.sumEquiv` — `C₀(I ⊕ J, E) ≃ₗᵢ[R] C₀(I, E) × C₀(J, E)`.
* `ZeroAtInftyContinuousMap.prodEquiv` — `C₀(I × J, E) ≃ₗᵢ[R] C₀(I, C₀(J, E))`.
* `ZeroAtInftyContinuousMap.piEquiv`, `ZeroAtInftyContinuousMap.blockEquiv` — finite index sets.
* `ZeroAtInftyContinuousMap.congrRight`, `ZeroAtInftyContinuousMap.compL`,
  `ZeroAtInftyContinuousMap.congrRightL` — functoriality in the values.
* `ZeroAtInftyContinuousMap.setSumComplEquiv` — `C₀(I, E) ≃ₗᵢ[R] C₀(S, E) × C₀(Sᶜ, E)`.
-/

open Filter Topology
open scoped ZeroAtInfty ContinuousLinearMap.Ultra

namespace ZeroAtInftyContinuousMap

open NormedRing

variable {R E : Type*} [NormedRing R] [NormedAddCommGroup E] [Module R E] [IsBoundedSMul R E]

section Reindex

variable {I J : Type*} [TopologicalSpace I] [DiscreteTopology I] [TopologicalSpace J]
  [DiscreteTopology J]

/-- A bijection of index sets induces an isometric isomorphism of model spaces, `f ↦ f ∘ e.symm`.
Source: roadmap §2.1.4 ("A bijection `I ≃ J` induces an isometry `C₀(I, R) ≃ₗᵢ[R] C₀(J, R)`"). -/
noncomputable def reindex (e : I ≃ J) : C₀(I, E) ≃ₗᵢ[R] C₀(J, E) where
  toFun f := ofTendsto (fun j ↦ f (e.symm j)) (by sorry)
  invFun g := ofTendsto (fun i ↦ g (e i)) (by sorry)
  map_add' := by sorry
  map_smul' := by sorry
  left_inv := by sorry
  right_inv := by sorry
  norm_map' := by sorry

@[simp]
theorem reindex_apply (e : I ≃ J) (f : C₀(I, E)) (j : J) : reindex (R := R) e f j = f (e.symm j) :=
  rfl

@[simp]
theorem reindex_symm_apply (e : I ≃ J) (g : C₀(J, E)) (i : I) :
    (reindex (R := R) e).symm g i = g (e i) := rfl

theorem reindex_single [DecidableEq I] [DecidableEq J] (e : I ≃ J) (i : I) (x : E) :
    reindex (R := R) e (single i x) = single (e i) x := by
  sorry

/-- The model space on a disjoint union is the product of the model spaces, with the max norm.
Source: roadmap §2.1.4 ("`C₀(I ⊕ J, R) ≃ₗᵢ C₀(I, R) × C₀(J, R)` with the max norm"). -/
noncomputable def sumEquiv : C₀(I ⊕ J, E) ≃ₗᵢ[R] C₀(I, E) × C₀(J, E) where
  toFun f := (ofTendsto (fun i ↦ f (Sum.inl i)) (by sorry), ofTendsto (fun j ↦ f (Sum.inr j)) (by sorry))
  invFun p := ofTendsto (Sum.elim p.1 p.2) (by sorry)
  map_add' := by sorry
  map_smul' := by sorry
  left_inv := by sorry
  right_inv := by sorry
  norm_map' := by sorry

@[simp]
theorem sumEquiv_apply_fst (f : C₀(I ⊕ J, E)) (i : I) :
    (sumEquiv (R := R) f).1 i = f (Sum.inl i) := rfl

@[simp]
theorem sumEquiv_apply_snd (f : C₀(I ⊕ J, E)) (j : J) :
    (sumEquiv (R := R) f).2 j = f (Sum.inr j) := rfl

@[simp]
theorem sumEquiv_symm_apply (p : C₀(I, E) × C₀(J, E)) (x : I ⊕ J) :
    (sumEquiv (R := R)).symm p x = Sum.elim p.1 p.2 x := rfl

/-- The model space on a product is the iterated model space. Source: roadmap §2.1.4
("`C₀(I × J, R) ≃ₗᵢ C₀(I, C₀(J, R))`"). -/
noncomputable def prodEquiv : C₀(I × J, E) ≃ₗᵢ[R] C₀(I, C₀(J, E)) where
  toFun f := ofTendsto (fun i ↦ ofTendsto (fun j ↦ f (i, j)) (by sorry)) (by sorry)
  invFun g := ofTendsto (fun p ↦ g p.1 p.2) (by sorry)
  map_add' := by sorry
  map_smul' := by sorry
  left_inv := by sorry
  right_inv := by sorry
  norm_map' := by sorry

@[simp]
theorem prodEquiv_apply (f : C₀(I × J, E)) (i : I) (j : J) :
    prodEquiv (R := R) f i j = f (i, j) := rfl

@[simp]
theorem prodEquiv_symm_apply (g : C₀(I, C₀(J, E))) (p : I × J) :
    (prodEquiv (R := R)).symm g p = g p.1 p.2 := rfl

/-- On a finite index set every family is in the model space, and the model space is the finite
power with the max norm. Source: roadmap §2.1.4 (the block decomposition "for a finite `σ`"). -/
noncomputable def piEquiv [Fintype I] : C₀(I, E) ≃ₗᵢ[R] (I → E) where
  toFun f := ⇑f
  invFun g := ofTendsto g (by sorry)
  map_add' := by sorry
  map_smul' := by sorry
  left_inv := by sorry
  right_inv := by sorry
  norm_map' := by sorry

@[simp]
theorem piEquiv_apply [Fintype I] (f : C₀(I, E)) :
    (piEquiv : C₀(I, E) ≃ₗᵢ[R] (I → E)) f = ⇑f := rfl

/-- **The block decomposition**: for a finite `σ`, `C₀(σ × I, E) ≃ₗᵢ (σ → C₀(I, E))`. Source:
roadmap §2.1.4 ("for a finite `σ`, `C₀(σ × I, R) ≃ₗᵢ (σ → C₀(I, R))`, the block decomposition
that the compact-operators and overconvergent-forms roadmaps use"). -/
noncomputable def blockEquiv (σ : Type*) [TopologicalSpace σ] [DiscreteTopology σ] [Fintype σ] :
    C₀(σ × I, E) ≃ₗᵢ[R] (σ → C₀(I, E)) :=
  (prodEquiv (R := R)).trans piEquiv

@[simp]
theorem blockEquiv_apply (σ : Type*) [TopologicalSpace σ] [DiscreteTopology σ] [Fintype σ]
    (f : C₀(σ × I, E)) (a : σ) (i : I) : blockEquiv (R := R) σ f a i = f (a, i) := rfl

/-- The model space on `I` splits along a subset `S` as `C₀(S, E) × C₀(Sᶜ, E)`. Source: roadmap
§2.2.5 ("`M ≅ C₀(S, R) × C₀(I ∖ S, R)`"), the model-space case. -/
noncomputable def setSumComplEquiv (S : Set I) [DecidablePred (· ∈ S)] :
    C₀(I, E) ≃ₗᵢ[R] C₀(S, E) × C₀((Sᶜ : Set I), E) :=
  (reindex (Equiv.Set.sumCompl S).symm).trans sumEquiv

end Reindex

section CongrRight

variable {I : Type*} [TopologicalSpace I] [DiscreteTopology I]
  {F : Type*} [NormedAddCommGroup F] [Module R F] [IsBoundedSMul R F]

/-- An isometric isomorphism of the values induces one of the model spaces. Source: roadmap §2.2.3
(stability of the three notions under "`C₀(J, −)`"). -/
noncomputable def congrRight (e : E ≃ₗᵢ[R] F) : C₀(I, E) ≃ₗᵢ[R] C₀(I, F) where
  toFun f := ofTendsto (fun i ↦ e (f i)) (by sorry)
  invFun g := ofTendsto (fun i ↦ e.symm (g i)) (by sorry)
  map_add' := by sorry
  map_smul' := by sorry
  left_inv := by sorry
  right_inv := by sorry
  norm_map' := by sorry

@[simp]
theorem congrRight_apply (e : E ≃ₗᵢ[R] F) (f : C₀(I, E)) (i : I) : congrRight e f i = e (f i) :=
  rfl

/-- Post-composition with a continuous linear map of the values, over a Tate ring (where
continuous linear maps are bounded). Source: roadmap §2.2.3. -/
noncomputable def compL [NormOneClass R] [IsTate R] (u : E →L[R] F) :
    C₀(I, E) →L[R] C₀(I, F) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ofTendsto (fun i ↦ u (f i)) (by sorry)
      map_add' := by sorry
      map_smul' := by sorry }
    ‖u‖ (by sorry)

@[simp]
theorem compL_apply [NormOneClass R] [IsTate R] (u : E →L[R] F) (f : C₀(I, E)) (i : I) :
    compL u f i = u (f i) := rfl

/-- A continuous linear equivalence of the values induces one of the model spaces, over a Tate
ring. Source: roadmap §2.2.3 (stability of potential orthonormalisability and (Pr) under
"`C₀(J, −)`"). -/
noncomputable def congrRightL [NormOneClass R] [IsTate R] (e : E ≃L[R] F) :
    C₀(I, E) ≃L[R] C₀(I, F) :=
  ContinuousLinearEquiv.equivOfInverse (compL (e : E →L[R] F)) (compL (e.symm : F →L[R] E))
    (by sorry) (by sorry)

@[simp]
theorem congrRightL_apply [NormOneClass R] [IsTate R] (e : E ≃L[R] F) (f : C₀(I, E)) (i : I) :
    congrRightL e f i = e (f i) := rfl

end CongrRight

end ZeroAtInftyContinuousMap
