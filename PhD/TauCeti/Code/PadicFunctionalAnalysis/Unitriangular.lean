/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.PadicFunctionalAnalysis.ModelSpace.Matrix
import PhD.TauCeti.Code.PadicFunctionalAnalysis.ONable

/-!
# The unitriangular-perturbation criterion

A matrix `a : ℕ → ℕ → R` over a nonarchimedean Banach ring with `‖1‖ = 1` is a *unitriangular
perturbation of level `q < 1`* when all entries have norm at most `1`, the diagonal entries are
multiplicative units of norm `1`, the entries strictly below the diagonal have norm at most `q`, and
every column is finitely supported. Such a matrix is the matrix of an isometric automorphism of
`C₀(ℕ, R)`: the isometry is the largest-index argument (the largest index at which `‖fⱼ‖` is attained
contributes a term no other term can cancel), and surjectivity is successive approximation with
contraction factor `max q 2⁻¹` (solve the upper unitriangular part exactly on a finite truncation).
Hence a family whose matrix in an orthonormal basis is, after reindexing, a unitriangular
perturbation is itself an orthonormal basis — the form in which Amice's theorem (§4.4) is proved.

Relation to Colmez's Proposition 1.1.5: over a discretely valued field the criterion follows from
residue-basis lifting (§2.3.1), since a triangular matrix with unit diagonal is invertible over the
residue field; the criterion here needs no discreteness and no residue field (roadmap §2.7.3).

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, §2.7.
Tau Ceti home: `TauCeti/Analysis/Normed/Module/Ultra/Unitriangular.lean`.
-/

open Filter Topology Function
open scoped ZeroAtInfty ContinuousLinearMap.Ultra
open ZeroAtInftyContinuousMap NormedRing

namespace ContinuousLinearMap.Ultra

variable {R M N : Type*} [NormedRing R] [NormOneClass R] [IsTate R] [NormedAddCommGroup M]
  [Module R M] [IsBoundedSMul R M] [CompleteSpace M] [NormedAddCommGroup N] [Module R N]
  [IsBoundedSMul R N]

/-- **Surjectivity by successive approximation**: a bounded operator from a Banach module with
approximate preimages of contraction factor `q < 1` is surjective. Source: roadmap §2.7.1
("`T` is surjective (successive approximation with contraction factor `q`)"); the iteration of
Layer 1's `exists_preimage_norm_le`. -/
theorem surjective_of_forall_exists_approx (u : M →L[R] N) {q C : ℝ} (hq : q < 1)
    (h : ∀ y, ∃ x, ‖x‖ ≤ C * ‖y‖ ∧ ‖y - u x‖ ≤ q * ‖y‖) : Surjective u := by
  sorry

end ContinuousLinearMap.Ultra

namespace ZeroAtInftyContinuousMap

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R] [CompleteSpace R]

/-- **A unitriangular perturbation of level `q`**: entries in the unit ball, multiplicative units
of norm `1` on the diagonal, entries of norm at most `q < 1` below it, finitely supported columns.
Source: roadmap §2.7.1. -/
structure IsUnitriangularPerturbation (a : ℕ → ℕ → R) (q : ℝ) : Prop where
  q_lt_one : q < 1
  norm_le_one : ∀ i j, ‖a i j‖ ≤ 1
  diag_isUnit : ∀ i, IsUnit (a i i)
  diag_isMultiplicative : ∀ i, IsMultiplicative (a i i)
  norm_diag : ∀ i, ‖a i i‖ = 1
  norm_lower_le : ∀ i j, j < i → ‖a i j‖ ≤ q
  column_finite : ∀ j, {i | a i j ≠ 0}.Finite

namespace IsUnitriangularPerturbation

variable {a : ℕ → ℕ → R} {q : ℝ} (ha : IsUnitriangularPerturbation a q)
include ha

theorem tendsto_column (j : ℕ) : Tendsto (fun i ↦ a i j) cofinite (𝓝 0) := by
  sorry

/-- The operator of a unitriangular perturbation. Source: roadmap §2.7.1 ("such a matrix is the
matrix of a bounded operator `T` of `C₀(ℕ, R)`"). -/
noncomputable def toCLM : C₀(ℕ, R) →L[R] C₀(ℕ, R) :=
  ofMatrix a ha.tendsto_column ⟨1, ha.norm_le_one⟩

@[simp]
theorem matrixCoeff_toCLM (i j : ℕ) : matrixCoeff ha.toCLM i j = a i j :=
  matrixCoeff_ofMatrix _ _ _ i j

theorem toCLM_apply (f : C₀(ℕ, R)) (i : ℕ) : ha.toCLM f i = ∑' j, a i j * f j :=
  ofMatrix_apply _ _ _ f i

/-- **The largest-index argument**: `T` is an isometry. Source: roadmap §2.7.1 ("`T` is an
isometry (`‖T f‖ = ‖f‖`, by the largest-index argument: the largest index at which `‖fⱼ‖` is
attained contributes a term that no other term can cancel)"). -/
theorem norm_toCLM_apply (f : C₀(ℕ, R)) : ‖ha.toCLM f‖ = ‖f‖ := by
  sorry

/-- The upper unitriangular part is solved exactly on finitely supported targets, by backward
substitution, without increasing the norm. Source: roadmap §2.7.1 (the approximation step). -/
theorem exists_forall_tsum_eq_of_finite (g : C₀(ℕ, R)) (N : ℕ) (hg : ∀ i, N < i → g i = 0) :
    ∃ f : C₀(ℕ, R), ‖f‖ ≤ ‖g‖ ∧ (∀ i, N < i → f i = 0) ∧
      ∀ i, ∑' j, (if i ≤ j then a i j else 0) * f j = g i := by
  sorry

/-- **One step of the successive approximation**: every `g` is approximated by `T f` with
`‖f‖ ≤ ‖g‖` up to the contraction factor `max q 2⁻¹`. Source: roadmap §2.7.1 ("successive
approximation with contraction factor `q`"). -/
theorem exists_norm_sub_toCLM_le (g : C₀(ℕ, R)) :
    ∃ f : C₀(ℕ, R), ‖f‖ ≤ ‖g‖ ∧ ‖g - ha.toCLM f‖ ≤ max q 2⁻¹ * ‖g‖ := by
  sorry

/-- Source: roadmap §2.7.1 ("`T` is surjective"). -/
theorem surjective_toCLM [IsTate R] : Surjective ha.toCLM := by
  sorry

/-- **The isometric automorphism** of a unitriangular perturbation. Source: roadmap §2.7.1
("hence an isometric automorphism"). -/
noncomputable def linearIsometryEquiv [IsTate R] : C₀(ℕ, R) ≃ₗᵢ[R] C₀(ℕ, R) :=
  LinearIsometryEquiv.ofSurjective ⟨(ha.toCLM : C₀(ℕ, R) →ₗ[R] C₀(ℕ, R)), ha.norm_toCLM_apply⟩
    ha.surjective_toCLM

@[simp]
theorem coe_linearIsometryEquiv [IsTate R] : ⇑ha.linearIsometryEquiv = ha.toCLM := rfl

/-- Source: roadmap §2.7.1, in the form of `Suggested.lean`
(`exists_linearIsometryEquiv_of_isUnitriangularPerturbation`). -/
theorem exists_linearIsometryEquiv [IsTate R] :
    ∃ T : C₀(ℕ, R) ≃ₗᵢ[R] C₀(ℕ, R),
      ∀ i j, matrixCoeff (T.toContinuousLinearEquiv : C₀(ℕ, R) →L[R] C₀(ℕ, R)) i j = a i j := by
  sorry

end IsUnitriangularPerturbation

end ZeroAtInftyContinuousMap

/-- **The unitriangular-perturbation criterion for families**: if `e` is an orthonormal basis and
`f j = ∑' i, a i j • e i` with `a` a unitriangular perturbation, then `f` is an orthonormal basis
(reindex by `IsOrthonormalBasis.comp_equiv` first when the matrix is unitriangular only after a
bijection of `ℕ`). Source: roadmap §2.7.2 ("if `e : ℕ → M` is a family in an orthonormalisable
Banach module whose matrix in an orthonormal basis, after a reindexing by a bijection of `ℕ`, is a
unitriangular perturbation, then `e` is an orthonormal basis"). -/
theorem IsOrthonormalBasis.of_isUnitriangularPerturbation {R : Type*} [NormedCommRing R]
    [NormOneClass R] [IsUltrametricDist R] [NormedRing.IsTate R] [CompleteSpace R] {M : Type*}
    [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [IsUltrametricDist M] [CompleteSpace M]
    {e : ℕ → M} (he : IsOrthonormalBasis R e) {a : ℕ → ℕ → R} {q : ℝ}
    (ha : ZeroAtInftyContinuousMap.IsUnitriangularPerturbation a q) {f : ℕ → M}
    (hf : ∀ j, HasSum (fun i ↦ a i j • e i) (f j)) : IsOrthonormalBasis R f := by
  sorry
