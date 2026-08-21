/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.QMF.WeightModule
import PhD.QMF.Slash.Basic

/-!
# The right slash on classical weight modules

Buzzard's `L_{n,v}` is a *right* `Mₜ`-module [*Eigenvarieties*, §9 p. 68]:
`γ = (a b; c d)` sends `Z^m` to `(cZ+d)^n (ad−bc)^v ((aZ+b)/(cZ+d))^m` — in the
two-variable homogeneous model, `P(X,Y) ↦ det(γ)^v · P(aX+bY, cX+dY)`, i.e. the
*untransposed* substitution twisted by the determinant character.  This file defines
that action as a `RightSlashAction (Sigma0' K γ hγ) (WeightModule R n ν)` — **by
Buzzard's formula directly**, not by transport — and proves the bridge to the
library's left action.

## The bridge (design note)

The left action (`PhD/QMF/WeightModule.lean`) is `g • P = ν g • P(gᵀ·(X,Y))`
(*transposed* substitution).  Since `(adjugate δ)ᵀ = J δ J⁻¹` for `J = (0 1; −1 0)`,
the adjugate transport of the left action agrees with Buzzard's formula only up to
the change of variables `J` — classically, the `Z = X/Y` vs `Z = Y/X` homogenisation
seam.  The bridge is therefore

`P ∣ₛ δ = jTwist ((Sigma0'.adj δ) • jTwist.symm P)`

with `jTwist` the (signed) variable-swap automorphism, and *no* determinant
correction: `det (adjugate δ) = det δ` for `2×2`, so the character values agree on
the nose.  Statements in thesis form use `∣ₛ`; proofs cross to the left library
through `slash_eq_adj_smul` once and stay there.
-/

open MvPolynomial Valued
open scoped QMF

section MatrixSubstR

variable {K : Type*} [Field K] {R : Type*} [CommRing R] [Algebra K R]

/-- Untransposed substitution action of a `2×2` matrix on two-variable polynomials:
`P ∣ g = P(aX + bY, cX + dY)` (substitution by the matrix itself, which makes this a
*right* monoid action: `matrixSubstR (g*h) = matrixSubstR h ∘ matrixSubstR g`).
Companion of the left-handed `matrixSubst` (`PhD/QMF/WeightModule.lean`). -/
noncomputable def matrixSubstR (g : Matrix (Fin 2) (Fin 2) K) :
    MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  aeval fun i => ∑ j, algebraMap K R (g i j) • (X j : MvPolynomial (Fin 2) R)

@[simp]
lemma matrixSubstR_X (g : Matrix (Fin 2) (Fin 2) K) (i : Fin 2) :
    matrixSubstR (R := R) g (X i) = ∑ j, algebraMap K R (g i j) • X j := by
  simp [matrixSubstR]

lemma matrixSubstR_one :
    matrixSubstR (R := R) (1 : Matrix (Fin 2) (Fin 2) K) = AlgHom.id R _ := by
  refine MvPolynomial.algHom_ext fun i => ?_
  fin_cases i <;> simp [Matrix.one_apply]

/-- Untransposed substitution is a right action:
`P ∣ (gh) = (P ∣ g) ∣ h`. -/
lemma matrixSubstR_mul (g h : Matrix (Fin 2) (Fin 2) K) :
    matrixSubstR (R := R) (g * h) = (matrixSubstR (R := R) h).comp (matrixSubstR g) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  simp only [AlgHom.coe_comp, Function.comp_apply, matrixSubstR_X, map_sum, map_smul,
    Matrix.mul_apply, map_mul, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

/-- Relation to the left-handed substitution: `matrixSubstR g = matrixSubst gᵀ`. -/
lemma matrixSubstR_eq_matrixSubst_transpose (g : Matrix (Fin 2) (Fin 2) K) :
    matrixSubstR (R := R) g = matrixSubst g.transpose := by
  refine MvPolynomial.algHom_ext fun i => ?_
  simp [Matrix.transpose_apply]

/-- Untransposed substitution preserves homogeneity of degree `n`. -/
lemma matrixSubstR_mem_homogeneousSubmodule (g : Matrix (Fin 2) (Fin 2) K) {n : ℕ}
    {P : MvPolynomial (Fin 2) R} (hP : P ∈ homogeneousSubmodule (Fin 2) R n) :
    matrixSubstR g P ∈ homogeneousSubmodule (Fin 2) R n := by
  rw [mem_homogeneousSubmodule] at hP ⊢
  have h1 : ∀ i, (∑ j, algebraMap K R (g i j) • (X j : MvPolynomial (Fin 2) R)).IsHomogeneous 1 := by
    intro i
    apply IsHomogeneous.sum
    intro j _
    rw [smul_eq_C_mul]
    exact (isHomogeneous_X R j).C_mul _
  simpa [matrixSubstR] using hP.aeval _ h1

end MatrixSubstR

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  [Valued K Γ₀] {γ : Γ₀} {hγ : γ < 1}
variable {R : Type*} [CommRing R] [Algebra K R] {n : ℕ} {ν : Sigma0 K γ hγ →* Rˣ}

namespace WeightModule

/-- Buzzard's right action on `L_{n,ν}` [*Eigenvarieties*, §9 p. 68]:
`P ∣ₛ δ = ν(adj δ) • P(aX + bY, cX + dY)` for `δ = (a b; c d) ∈ Σ₀'(γ)`.
The character is evaluated through the dictionary (`det ∘ adj = det`, so for
`ν = detChar w` this is Buzzard's `det(δ)^w` on the nose). -/
noncomputable instance : RightSlashAction (Sigma0' K γ hγ) (WeightModule R n ν) where
  slash P δ := ⟨ν (Sigma0'.adj δ) • matrixSubstR δ.1 P.1, by
    rw [Units.smul_def]
    exact Submodule.smul_mem _ _ (matrixSubstR_mem_homogeneousSubmodule _ P.2)⟩
  zero_slash δ := Subtype.ext (by simp)
  slash_one P := Subtype.ext (by simp [matrixSubstR_one])
  slash_mul P δ₁ δ₂ := Subtype.ext (by
    simp [Sigma0'.adj_mul, matrixSubstR_mul, Units.smul_def, map_smul, mul_smul])
  add_slash P Q δ := Subtype.ext (by
    simp only [WeightModule.coe_add, map_add, smul_add]
    rfl)

@[simp]
lemma slash_coe (δ : Sigma0' K γ hγ) (P : WeightModule R n ν) :
    (P ∣ₛ δ).1 = ν (Sigma0'.adj δ) • matrixSubstR δ.1 P.1 := rfl

instance : RightSlashAction.SMulSlashClass R (Sigma0' K γ hγ) (WeightModule R n ν) where
  smul_slash r P δ := Subtype.ext (by
    simp [Units.smul_def, map_smul, smul_smul, mul_comm])

/-- Untransposed substitution by a fixed matrix, restricted to the weight module, as an
`R`-linear map. -/
noncomputable def substRLinear (M : Matrix (Fin 2) (Fin 2) K) :
    WeightModule R n ν →ₗ[R] WeightModule R n ν where
  toFun P := ⟨matrixSubstR M P.1, matrixSubstR_mem_homogeneousSubmodule _ P.2⟩
  map_add' P Q := Subtype.ext (by
    simp only [WeightModule.coe_add, map_add]
    rfl)
  map_smul' r P := Subtype.ext (by
    simp only [WeightModule.coe_rsmul, map_smul, RingHom.id_apply]
    rfl)

@[simp] lemma substRLinear_coe (M : Matrix (Fin 2) (Fin 2) K) (P : WeightModule R n ν) :
    (substRLinear M P).1 = matrixSubstR M P.1 := rfl

private lemma substRLinear_comp (M N : Matrix (Fin 2) (Fin 2) K) :
    (substRLinear (R := R) (n := n) (ν := ν) N).comp (substRLinear M)
      = substRLinear (M * N) :=
  LinearMap.ext fun P => Subtype.ext
    (DFunLike.congr_fun (matrixSubstR_mul (R := R) M N) P.1).symm

private lemma substRLinear_one :
    substRLinear (R := R) (n := n) (ν := ν) (1 : Matrix (Fin 2) (Fin 2) K)
      = LinearMap.id :=
  LinearMap.ext fun P => Subtype.ext
    (by simp [matrixSubstR_one])

/-- The homogenisation-seam intertwiner: the (signed) variable swap induced by
`J = (0 1; −1 0)`, as an `R`-linear automorphism of the weight module.  (The precise
sign convention is fixed by the bridge lemma below.) -/
noncomputable def jTwist : WeightModule R n ν ≃ₗ[R] WeightModule R n ν :=
  LinearEquiv.ofLinear (substRLinear !![0, 1; -1, 0]) (substRLinear !![0, -1; 1, 0])
    (by
      rw [substRLinear_comp, show (!![0, -1; 1, 0] * !![0, 1; -1, 0] :
        Matrix (Fin 2) (Fin 2) K) = 1 by
          rw [Matrix.mul_fin_two, Matrix.one_fin_two]
          norm_num, substRLinear_one])
    (by
      rw [substRLinear_comp, show (!![0, 1; -1, 0] * !![0, -1; 1, 0] :
        Matrix (Fin 2) (Fin 2) K) = 1 by
          rw [Matrix.mul_fin_two, Matrix.one_fin_two]
          norm_num, substRLinear_one])

/-- **The bridge**: Buzzard's right slash is the adjugate transport of the library's
left action, conjugated by the homogenisation seam:
`P ∣ₛ δ = jTwist (adj δ • jTwist⁻¹ P)`.  Proof route: `(adjugate δ)ᵀ = J δ J⁻¹` and
`matrixSubstR (A·B) = matrixSubstR B ∘ matrixSubstR A`; the characters agree because
`det (adjugate δ) = det δ`. -/
lemma slash_eq_adj_smul (δ : Sigma0' K γ hγ) (P : WeightModule R n ν) :
    P ∣ₛ δ = jTwist (Sigma0'.adj δ • jTwist.symm P) := by
  have hadj : δ.1.adjugate = !![δ.1 1 1, -δ.1 0 1; -δ.1 1 0, δ.1 0 0] :=
    Matrix.adjugate_fin_two _
  have hadjT : (δ.1.adjugate).transpose
      = !![δ.1 1 1, -δ.1 1 0; -δ.1 0 1, δ.1 0 0] := by
    rw [Matrix.eta_fin_two ((δ.1.adjugate).transpose)]
    simp [hadj, Matrix.transpose_apply]
  have hJ : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) K) * (δ.1.adjugate).transpose
      * !![0, 1; -1, 0] = δ.1 := by
    rw [hadjT, Matrix.mul_fin_two, Matrix.mul_fin_two]
    conv_rhs => rw [Matrix.eta_fin_two δ.1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine Subtype.ext ?_
  show ν (Sigma0'.adj δ) • matrixSubstR δ.1 P.1
      = matrixSubstR !![0, 1; -1, 0]
          (ν (Sigma0'.adj δ) • matrixSubst δ.1.adjugate (matrixSubstR !![0, -1; 1, 0] P.1))
  rw [Units.smul_def, Units.smul_def, map_smul]
  congr 1
  conv_rhs =>
    rw [show matrixSubst (R := R) δ.1.adjugate = matrixSubstR ((δ.1.adjugate).transpose) from by
      rw [matrixSubstR_eq_matrixSubst_transpose, Matrix.transpose_transpose],
      ← AlgHom.comp_apply, ← matrixSubstR_mul, ← AlgHom.comp_apply, ← matrixSubstR_mul]
  rw [← mul_assoc, hJ]

end WeightModule
