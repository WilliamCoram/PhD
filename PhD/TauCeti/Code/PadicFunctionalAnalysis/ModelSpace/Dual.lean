/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import PhD.TauCeti.Code.PadicFunctionalAnalysis.ModelSpace.Matrix
import PhD.TauCeti.Code.PadicFunctionalAnalysis.ONable

/-!
# The dual of the model space

Over a Banach–Tate ring `R` the continuous dual of `C₀(I, R)` is `ℓ^∞(I, R)` isometrically, by the
universal property: a functional is determined by its values on the coordinate vectors and
`‖λ‖ = sup ‖λ (single i 1)‖`. The pairing `⟨λ, f⟩ = ∑' λᵢ fᵢ` is continuous with
`‖⟨λ, f⟩‖ ≤ ‖λ‖ ‖f‖`, and the evaluation `C₀(I, R) → (ℓ^∞(I, R))'` is an isometric embedding.
⚠ It is not surjective: `C₀(ℕ, K)` is not reflexive, and nothing about reflexivity is in scope. For
an orthonormalisable module the dual is identified with bounded families indexed by the basis, and
the transpose of an operator between model spaces has the transposed matrix.

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, §2.5.
Tau Ceti home: `TauCeti/Analysis/Normed/Module/Ultra/ModelSpace/Dual.lean`.
-/

universe u v

open Filter Topology Function Module
open scoped ZeroAtInfty ContinuousLinearMap.Ultra ENNReal

namespace ZeroAtInftyContinuousMap

open NormedRing

variable {R : Type*} [NormedCommRing R] {I : Type*} [TopologicalSpace I] [DiscreteTopology I]
  [DecidableEq I]

/-- The values of a continuous functional on the coordinate vectors form a bounded family. -/
theorem memℓp_infty_apply_single [NormOneClass R] [IsTate R] (l : C₀(I, R) →L[R] R) :
    Memℓp (fun i ↦ l (single i 1)) ∞ := by
  sorry

variable (R I) in
/-- **The dual of the model space is `ℓ^∞`**: `λ ↦ (λ (single i 1))ᵢ`, with inverse
`l ↦ (f ↦ ∑' i, f i * l i)`. Source: roadmap §2.5.1 ("the continuous dual of `C₀(I, R)` is
`ℓ^∞(I, R)` (bounded families, sup norm) isometrically, by the universal property §2.1.3");
Schneider §3, Example ("`c₀(X)' = ℓ^∞(X)`"). -/
noncomputable def dualEquivLp [NormOneClass R] [IsUltrametricDist R] [IsTate R] [CompleteSpace R] :
    (C₀(I, R) →L[R] R) ≃ₗᵢ[R] lp (fun _ : I ↦ R) ∞ where
  toFun l := ⟨fun i ↦ l (single i 1), memℓp_infty_apply_single l⟩
  invFun l := ofBounded R (fun i ↦ l i) (by sorry)
  map_add' := by sorry
  map_smul' := by sorry
  left_inv := by sorry
  right_inv := by sorry
  norm_map' := by sorry

@[simp]
theorem dualEquivLp_apply [NormOneClass R] [IsUltrametricDist R] [IsTate R] [CompleteSpace R]
    (l : C₀(I, R) →L[R] R) (i : I) : dualEquivLp R I l i = l (single i 1) :=
  rfl

theorem dualEquivLp_symm_apply [NormOneClass R] [IsUltrametricDist R] [IsTate R] [CompleteSpace R]
    (l : lp (fun _ : I ↦ R) ∞) (f : C₀(I, R)) :
    (dualEquivLp R I).symm l f = ∑' i, f i * l i := by
  sorry

/-! ### The pairing with `ℓ^∞` -/

theorem summable_lp_mul [IsUltrametricDist R] [CompleteSpace R] (l : lp (fun _ : I ↦ R) ∞)
    (f : C₀(I, R)) : Summable fun i ↦ l i * f i := by
  sorry

/-- Source: roadmap §2.5.2 ("`‖⟨λ, f⟩‖ ≤ ‖λ‖ ‖f‖`"). -/
theorem norm_tsum_lp_mul_le [IsUltrametricDist R] [CompleteSpace R] (l : lp (fun _ : I ↦ R) ∞)
    (f : C₀(I, R)) :
    ‖∑' i, l i * f i‖ ≤ ‖l‖ * ‖f‖ := by
  sorry

/-- Source: roadmap §2.5.2 ("The pairing … is continuous"). -/
theorem continuous_pairing [IsUltrametricDist R] [CompleteSpace R] :
    Continuous fun p : lp (fun _ : I ↦ R) ∞ × C₀(I, R) ↦ ∑' i, p.1 i * p.2 i := by
  sorry

variable (R I) in
/-- The evaluation of the model space on its dual `ℓ^∞`, an isometric embedding. Source: roadmap
§2.5.2 ("the evaluation `C₀ → (C₀)'' = (ℓ^∞)'` is an isometric embedding"). -/
noncomputable def toBidual [NormOneClass R] [IsUltrametricDist R] [IsTate R] [CompleteSpace R] :
    C₀(I, R) →ₗᵢ[R] (lp (fun _ : I ↦ R) ∞ →L[R] R) where
  toFun f :=
    LinearMap.mkContinuous
      { toFun := fun l ↦ ∑' i, l i * f i
        map_add' := by sorry
        map_smul' := by sorry }
      ‖f‖ (by sorry)
  map_add' := by sorry
  map_smul' := by sorry
  norm_map' := by sorry

@[simp]
theorem toBidual_apply [NormOneClass R] [IsUltrametricDist R] [IsTate R] [CompleteSpace R]
    (f : C₀(I, R)) (l : lp (fun _ : I ↦ R) ∞) : toBidual R I f l = ∑' i, l i * f i := rfl

/-! ### Transposes -/

/-- The transpose of an operator between model spaces has the transposed matrix. Source: roadmap
§2.5.3 ("the transpose of `u : M →L[R] N` between orthonormalisable modules has the transposed
matrix (§2.6)"). -/
theorem dualEquivLp_comp_apply [NormOneClass R] [IsUltrametricDist R] [IsTate R] [CompleteSpace R]
    {J : Type*} [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J]
    (u : C₀(J, R) →L[R] C₀(I, R)) (l : C₀(I, R) →L[R] R) (j : J) :
    dualEquivLp R J (l.comp u) j = ∑' i, dualEquivLp R I l i * matrixCoeff u i j := by
  sorry

end ZeroAtInftyContinuousMap

/-! ### The dual of an orthonormalisable module -/

namespace ContinuousLinearMap.Ultra

open NormedRing

variable {R M N P : Type*} [NormedRing R] [NormOneClass R] [IsTate R] [NormedAddCommGroup M]
  [Module R M] [IsBoundedSMul R M] [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  [NormedAddCommGroup P] [Module R P] [IsBoundedSMul R P]

/-- Precomposition with an isometric isomorphism preserves the operator norm. -/
theorem opNorm_comp_linearIsometryEquiv (u : N →L[R] P) (e : M ≃ₗᵢ[R] N) :
    ‖u.comp (e.toContinuousLinearEquiv : M →L[R] N)‖ = ‖u‖ := by
  sorry

end ContinuousLinearMap.Ultra

/-- The dual of an orthonormalisable module is `ℓ^∞` on the index set of a basis. Source: roadmap
§2.5.3 ("For an orthonormalisable `M` with basis `e`, the dual is identified with bounded families
indexed by the basis"). -/
theorem Module.IsONable.exists_dual_linearIsometryEquiv_lp {R : Type u} {M : Type v}
    [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R] [NormedRing.IsTate R]
    [CompleteSpace R] [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] (h : IsONable R M) :
    ∃ (I : Type v) (_ : TopologicalSpace I) (_ : DiscreteTopology I),
      Nonempty ((M →L[R] R) ≃ₗᵢ[R] lp (fun _ : I ↦ R) ∞) := by
  sorry
