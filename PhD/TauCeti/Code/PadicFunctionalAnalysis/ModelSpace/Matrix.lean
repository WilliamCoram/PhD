/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.PadicFunctionalAnalysis.ModelSpace.Universal
import PhD.TauCeti.Code.PadicFunctionalAnalysis.ModelSpace.Map
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.Banach

/-!
# Matrices of bounded operators between model spaces

For `u : C₀(J, R) →L[R] C₀(I, R)` the matrix coefficient `matrixCoeff u i j` is the `i`-th
coordinate of `u (single j 1)` (roadmap convention 7: columns are the images of the basis vectors).
Each column tends to `0` cofinitely, `‖u‖ = sup ‖matrixCoeff u i j‖` over a Banach–Tate ring,
`(u f) i = ∑' j, matrixCoeff u i j * f j`, and conversely a matrix with bounded entries and columns
tending to `0` is the matrix of a unique bounded operator (`ofMatrix`). Composition is the matrix
product, with the middle sum convergent. Diagonal operators and the base change of matrices along
a bounded ring homomorphism are included.

⚠ The matrix-product formulas are stated over a commutative ring: over a noncommutative `R` the
coefficients multiply in the opposite order (`(u f) i = ∑' j, f j * matrixCoeff u i j`); nothing
downstream needs the noncommutative case (plan, design decision D3).

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, convention 7, §2.6.1–2.6.2,
§2.6.6. Tau Ceti home: `TauCeti/Analysis/Normed/Module/Ultra/ModelSpace/Matrix.lean`.
-/

open Filter Topology Function
open scoped ZeroAtInfty ContinuousLinearMap.Ultra

namespace ZeroAtInftyContinuousMap

open NormedRing

section Coeff

variable {R : Type*} [NormedRing R] {I J : Type*} [TopologicalSpace I] [DiscreteTopology I]
  [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J]

/-- The matrix coefficient of `u : C₀(J, R) →L[R] C₀(I, R)`: the `i`-th coordinate of the image
of the `j`-th basis vector. Source: roadmap convention 7 ("the matrix coefficient
`matrixCoeff u i j` is the `i`-th coordinate of `u (single j 1)`"); Buzzard §2; Bellaïche §II.1.3
(both write the transpose). -/
noncomputable def matrixCoeff (u : C₀(J, R) →L[R] C₀(I, R)) (i : I) (j : J) : R :=
  u (single j 1) i

/-- Each column tends to `0` cofinitely. Source: roadmap §2.6.1 ("each column tends to `0`
cofinitely"); Buzzard §2 ("`a_{ij} → 0` as `i → ∞` for fixed `j`"). -/
theorem tendsto_matrixCoeff_column (u : C₀(J, R) →L[R] C₀(I, R)) (j : J) :
    Tendsto (fun i ↦ matrixCoeff u i j) cofinite (𝓝 0) := by
  sorry

/-- Over a Tate ring every entry is bounded by the operator norm. Source: roadmap §2.6.1
("`‖u‖ = sup_{i,j} ‖matrixCoeff u i j‖`"), the inequality `≥`. -/
theorem norm_matrixCoeff_le [NormOneClass R] [IsTate R] (u : C₀(J, R) →L[R] C₀(I, R)) (i : I)
    (j : J) : ‖matrixCoeff u i j‖ ≤ ‖u‖ := by
  sorry

/-- An operator between model spaces is determined by its matrix. Source: roadmap §2.6.1 ("the
matrix of a unique bounded operator"); Buzzard §2. -/
theorem ext_matrixCoeff {u v : C₀(J, R) →L[R] C₀(I, R)}
    (h : ∀ i j, matrixCoeff u i j = matrixCoeff v i j) : u = v := by
  sorry

end Coeff

section Comm

variable {R : Type*} [NormedCommRing R] {I J : Type*} [TopologicalSpace I] [DiscreteTopology I]
  [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J]

/-- The action of an operator in coordinates: `(u f) i = ∑' j, matrixCoeff u i j * f j`. Source:
roadmap §2.6.1; Buzzard §2 ("`φ(∑ f_j e_j) = ∑_i (∑_j a_{ij} f_j) e_i`"). -/
theorem hasSum_matrixCoeff_mul (u : C₀(J, R) →L[R] C₀(I, R)) (f : C₀(J, R)) (i : I) :
    HasSum (fun j ↦ matrixCoeff u i j * f j) (u f i) := by
  sorry

/-- The operator norm is the supremum of the matrix entries. Source: roadmap §2.6.1
("`‖u‖ = sup_{i,j} ‖matrixCoeff u i j‖`"); Buzzard §2 ("the norm of `φ` is `sup_{i,j} |a_{ij}|`"). -/
theorem opNorm_eq_iSup_matrixCoeff [NormOneClass R] [IsUltrametricDist R] [IsTate R]
    (u : C₀(J, R) →L[R] C₀(I, R)) : ‖u‖ = ⨆ p : I × J, ‖matrixCoeff u p.1 p.2‖ := by
  sorry

variable [IsUltrametricDist R] [CompleteSpace R]

/-- The operator with a given matrix whose columns tend to `0` and whose entries are bounded.
Source: roadmap §2.6.1 ("Conversely a matrix `a : I → J → R` whose columns tend to `0` cofinitely
and whose entries are bounded is the matrix of a unique bounded operator"); Buzzard §2. -/
noncomputable def ofMatrix (a : I → J → R) (hcol : ∀ j, Tendsto (fun i ↦ a i j) cofinite (𝓝 0))
    (hbdd : ∃ C, ∀ i j, ‖a i j‖ ≤ C) : C₀(J, R) →L[R] C₀(I, R) :=
  ofBounded R (fun j ↦ ofTendsto (fun i ↦ a i j) (hcol j)) (by sorry)

@[simp]
theorem matrixCoeff_ofMatrix (a : I → J → R) (hcol : ∀ j, Tendsto (fun i ↦ a i j) cofinite (𝓝 0))
    (hbdd : ∃ C, ∀ i j, ‖a i j‖ ≤ C) (i : I) (j : J) : matrixCoeff (ofMatrix a hcol hbdd) i j = a i j := by
  sorry

theorem ofMatrix_apply (a : I → J → R) (hcol : ∀ j, Tendsto (fun i ↦ a i j) cofinite (𝓝 0))
    (hbdd : ∃ C, ∀ i j, ‖a i j‖ ≤ C) (f : C₀(J, R)) (i : I) :
    ofMatrix a hcol hbdd f i = ∑' j, a i j * f j := by
  sorry

/-- Source: roadmap §2.6.1 ("of norm `sup ‖a i j‖`"). -/
theorem norm_ofMatrix [NormOneClass R] [IsTate R] (a : I → J → R)
    (hcol : ∀ j, Tendsto (fun i ↦ a i j) cofinite (𝓝 0)) (hbdd : ∃ C, ∀ i j, ‖a i j‖ ≤ C) :
    ‖ofMatrix a hcol hbdd‖ = ⨆ p : I × J, ‖a p.1 p.2‖ := by
  sorry

variable {L : Type*} [TopologicalSpace L] [DiscreteTopology L] [DecidableEq L]

/-- The middle sum of a matrix product converges: a bounded family times a family tending to `0`.
Source: roadmap §2.6.1 ("with the middle sum convergent by §0.1.4"). -/
theorem summable_matrixCoeff_mul_matrixCoeff [NormOneClass R] [IsTate R]
    (u : C₀(J, R) →L[R] C₀(I, R)) (v : C₀(L, R) →L[R] C₀(J, R)) (i : I) (l : L) :
    Summable fun j ↦ matrixCoeff u i j * matrixCoeff v j l := by
  sorry

/-- The matrix of a composite is the matrix product. Source: roadmap §2.6.1 ("The matrix of a
composite is the matrix product"); Buzzard §2. -/
theorem matrixCoeff_comp [NormOneClass R] [IsTate R] (u : C₀(J, R) →L[R] C₀(I, R))
    (v : C₀(L, R) →L[R] C₀(J, R)) (i : I) (l : L) :
    matrixCoeff (u.comp v) i l = ∑' j, matrixCoeff u i j * matrixCoeff v j l := by
  sorry

end Comm

/-! ### Diagonal operators -/

section Diagonal

variable {R : Type*} [NormedCommRing R] {I : Type*} [TopologicalSpace I] [DiscreteTopology I]

/-- The diagonal operator `f ↦ (i ↦ d i * f i)` of a bounded family `d`. Source: roadmap §2.6.2
("The diagonal operator of a bounded family `d : I → R`"). -/
noncomputable def diagonal (d : I → R) (C : ℝ) (hd : ∀ i, ‖d i‖ ≤ C) :
    C₀(I, R) →L[R] C₀(I, R) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ofTendsto (fun i ↦ d i * f i) (by sorry)
      map_add' := by sorry
      map_smul' := by sorry }
    C (by sorry)

@[simp]
theorem diagonal_apply (d : I → R) (C : ℝ) (hd : ∀ i, ‖d i‖ ≤ C) (f : C₀(I, R)) (i : I) :
    diagonal d C hd f i = d i * f i := rfl

theorem matrixCoeff_diagonal [DecidableEq I] (d : I → R) (C : ℝ) (hd : ∀ i, ‖d i‖ ≤ C) (i j : I) :
    matrixCoeff (diagonal d C hd) i j = if i = j then d i else 0 := by
  sorry

/-- Source: roadmap §2.6.2 ("has norm `sup ‖dᵢ‖`"), roadmap Layer 1 Examples ("diagonal
operator"). -/
theorem norm_diagonal [NormOneClass R] [IsTate R] [DecidableEq I] (d : I → R) (C : ℝ)
    (hd : ∀ i, ‖d i‖ ≤ C) : ‖diagonal d C hd‖ = ⨆ i, ‖d i‖ := by
  sorry

/-- Source: roadmap §2.6.2 ("injective … when every `dᵢ` is a non-zero-divisor"). -/
theorem injective_diagonal (d : I → R) (C : ℝ) (hd : ∀ i, ‖d i‖ ≤ C)
    (h : ∀ i, ∀ x : R, d i * x = 0 → x = 0) : Injective (diagonal d C hd) := by
  sorry

/-- The diagonal operator of a family of units has dense range (the inverses need not be bounded:
`diag(⌊n/pʰ⌋!)` in §4.4). Source: roadmap §2.6.2 ("injective with dense range … which is the case
of `diag(⌊n/pʰ⌋!)` in §4.4") — ⚠ dense range needs units, not merely non-zero-divisors (plan
erratum E22). -/
theorem denseRange_diagonal (d : I → R) (C : ℝ) (hd : ∀ i, ‖d i‖ ≤ C) (h : ∀ i, IsUnit (d i)) :
    DenseRange (diagonal d C hd) := by
  sorry

/-- The diagonal operator of a family of multiplicative units of norm `1` is an isometric
automorphism. Source: roadmap §2.6.2 ("it is an isometric automorphism when every `dᵢ` is a
multiplicative unit of norm `1`"). -/
noncomputable def diagonalEquiv (d : I → Rˣ) (hd : ∀ i, IsMultiplicative (d i : R))
    (h1 : ∀ i, ‖(d i : R)‖ = 1) : C₀(I, R) ≃ₗᵢ[R] C₀(I, R) where
  toFun f := ofTendsto (fun i ↦ (d i : R) * f i) (by sorry)
  invFun f := ofTendsto (fun i ↦ ((d i)⁻¹ : Rˣ) * f i) (by sorry)
  map_add' := by sorry
  map_smul' := by sorry
  left_inv := by sorry
  right_inv := by sorry
  norm_map' := by sorry

@[simp]
theorem diagonalEquiv_apply (d : I → Rˣ) (hd : ∀ i, IsMultiplicative (d i : R))
    (h1 : ∀ i, ‖(d i : R)‖ = 1) (f : C₀(I, R)) (i : I) : diagonalEquiv d hd h1 f i = (d i : R) * f i :=
  rfl

/-- The matrix of the permutation operator `reindex σ`. Source: roadmap §2.6.2 ("The permutation
operator of `σ : I ≃ I` is an isometric automorphism"). -/
theorem matrixCoeff_reindex [DecidableEq I] (σ : I ≃ I) (i j : I) :
    matrixCoeff (reindex (R := R) (E := R) σ).toContinuousLinearEquiv.toContinuousLinearMap i j =
      if i = σ j then 1 else 0 := by
  sorry

end Diagonal

/-! ### Base change of matrices -/

section BaseChange

variable {R S : Type*} [NormedCommRing R] [NormOneClass R] [IsTate R] [NormedCommRing S]
  [IsUltrametricDist S] [CompleteSpace S] {I J : Type*} [TopologicalSpace I] [DiscreteTopology I]
  [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J]
  (φ : R →+* S)

/-- The base change of an operator along a bounded ring homomorphism: the operator with matrix
`φ (matrixCoeff u i j)`. Source: roadmap §2.6.6 ("the operator `C₀(J, S) → C₀(I, S)` with matrix
`φ (matrixCoeff u i j)` exists"); Johansson–Newton, Proposition 2.1.8. -/
noncomputable def baseChange (C : ℝ) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (u : C₀(J, R) →L[R] C₀(I, R)) :
    C₀(J, S) →L[S] C₀(I, S) :=
  ofMatrix (fun i j ↦ φ (matrixCoeff u i j)) (by sorry) (by sorry)

variable (C : ℝ) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)

@[simp]
theorem matrixCoeff_baseChange (u : C₀(J, R) →L[R] C₀(I, R)) (i : I) (j : J) :
    matrixCoeff (baseChange φ C hφ u) i j = φ (matrixCoeff u i j) := by
  sorry

/-- The base change is `φ`-semilinearly compatible with `u`. Source: roadmap §2.6.6 ("is
`φ`-semilinearly compatible with `u`"). -/
theorem baseChange_map (u : C₀(J, R) →L[R] C₀(I, R)) (f : C₀(J, R)) :
    baseChange φ C hφ u (map φ C hφ f) = map φ C hφ (u f) := by
  sorry

/-- Source: roadmap §2.6.6 ("and has norm at most `‖φ‖ ‖u‖`"). -/
theorem norm_baseChange_le [NormOneClass S] [IsTate S] (hC : 0 ≤ C)
    (u : C₀(J, R) →L[R] C₀(I, R)) : ‖baseChange φ C hφ u‖ ≤ C * ‖u‖ := by
  sorry

/-- A bicontinuous ring isomorphism transports bounded operators: base change along `e` and along
`e.symm` are inverse. Source: roadmap §2.6.6 ("a bicontinuous ring isomorphism transports bounded
operators (Johansson–Newton, Proposition 2.1.8, the part that does not mention compactness)"). -/
theorem baseChange_symm_baseChange [IsUltrametricDist R] [CompleteSpace R] [NormOneClass S]
    [IsTate S] (e : R ≃+* S) (C' : ℝ) (he : ∀ r, ‖e r‖ ≤ C * ‖r‖) (he' : ∀ s, ‖e.symm s‖ ≤ C' * ‖s‖)
    (u : C₀(J, R) →L[R] C₀(I, R)) :
    baseChange e.symm.toRingHom C' he' (baseChange e.toRingHom C he u) = u := by
  sorry

end BaseChange

end ZeroAtInftyContinuousMap
