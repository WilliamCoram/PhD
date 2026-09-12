/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Salvatore Mercuri, Ruben Van de Velde
-/
import PhD.Main.QMF.FLTstuff.Mathlib.Algebra.Algebra.Hom
import PhD.Main.QMF.FLTstuff.Mathlib.Algebra.Algebra.Tower
import PhD.Main.QMF.FLTstuff.Hacks.RightActionInstances

/-!

# API for basic constructions not in mathlib

## Main definitions

* `SemialgHom.baseChangeOfAlgebraMap ψ` : if `ψ : A →ₛₐ[algebraMap R S] B`
  then this is the induced map `S ⊗[R] A →ₐ[S] B` (A,B rings, R,S commutative rings).
* `SemialgHom.baseChangeRightOfAlgebraMap ψ` : if `ψ : A →ₛₐ[algebraMap R S] B` then
  this is the induced map `S ⊗[R] A →ₐ[A] B` (all rings are commutative).

PARTIAL PORT (T016d part 2a) of `FLT.Mathlib.Algebra.Algebra.Bilinear`: the
`LinearEquiv.mulLeft` / `LinearEquiv.mulRight` definitions are not needed by
`PhD.Main.QMF.FLTstuff.DedekindDomain.Completion.BaseChange` and were omitted.

-- PORT (T016f-2a extension): the `LinearEquiv.mulLeft` / `LinearEquiv.mulRight` block is now
needed downstream and has been added at the end of the file; this is therefore a complete port.
-/

open scoped TensorProduct
variable {R S : Type*} [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    {A B : Type*}

/-- Given S an R-algebra, and a ring homomorphism `ψ` from an R-algebra A to an S-algebra B
compatible with the algebra map R → S, `baseChangeOfAlgebraMap ψ` is the induced
`S`-algebra map `S ⊗[R] A → B`.
-/
noncomputable
def SemialgHom.baseChangeOfAlgebraMap [Semiring A] [Algebra R S] [Algebra R A]
    [Semiring B] [Algebra S B] (ψ : A →ₛₐ[algebraMap R S] B) :
    S ⊗[R] A →ₐ[S] B :=
  letI : Algebra R B := Algebra.compHom _ (algebraMap R S)
  have : IsScalarTower R S B := .of_algebraMap_eq fun _ ↦ rfl
  let ρ : A →ₐ[R] B := {
    toRingHom := ψ.toRingHom
    commutes' := ψ.commutes
  }
  Algebra.TensorProduct.lift (Algebra.ofId S _) ρ fun s a ↦ Algebra.commutes s (ρ a)

theorem SemialgHom.baseChange_of_algebraMap_tmul [Semiring A] [Algebra R S] [Algebra R A]
    [Semiring B] [Algebra S B] (ψ : A →ₛₐ[algebraMap R S] B) (s : S) (a : A) :
    ψ.baseChangeOfAlgebraMap (s ⊗ₜ[R] a) = algebraMap _ _ s * ψ a :=
  -- PORT (v4.33): `simp [baseChangeOfAlgebraMap]` no longer fires `lift_tmul` through the
  -- `letI` algebra instances; the equation holds definitionally.
  rfl

@[simp]
theorem SemialgHom.baseChange_of_algebraMap_tmul_right [Semiring A] [Algebra R S] [Algebra R A]
    [Semiring B] [Algebra S B] (ψ : A →ₛₐ[algebraMap R S] B) (a : A) :
    ψ.baseChangeOfAlgebraMap (1 ⊗ₜ[R] a) = ψ a := by
  -- PORT (v4.33): rewrite via the tmul lemma instead of unfolding by `simp`.
  rw [SemialgHom.baseChange_of_algebraMap_tmul, map_one, one_mul]

@[simp]
theorem SemialgHom.baseChange_of_algebraMap_tmul_left [Semiring A] [Algebra R S] [Algebra R A]
    [Semiring B] [Algebra S B] (ψ : A →ₛₐ[algebraMap R S] B) (s : S) :
    ψ.baseChangeOfAlgebraMap (s ⊗ₜ[R] 1) = algebraMap _ _ s := by
  -- PORT (v4.33): rewrite via the tmul lemma instead of unfolding by `simp`.
  rw [SemialgHom.baseChange_of_algebraMap_tmul, map_one, mul_one]

open scoped TensorProduct.RightActions in
/-- If `ψ : A →ₛₐ[algebra R S] B` and if `B` is given the `A`-algebra induced by `ψ`, then
the resulting base change map `S ⊗[R] A →ₐ[S] B` is scalar in both `S` and `A`. -/
instance [Algebra R S] [CommSemiring A] [Algebra R A] [CommSemiring B] [Algebra S B]
    (ψ : A →ₛₐ[algebraMap R S] B) :
    letI := ψ.toAlgebra
    IsBiscalar S A ψ.baseChangeOfAlgebraMap where
  __ := ψ.toAlgebra
  map_smul₁ s x := ψ.baseChangeOfAlgebraMap.map_smul_of_tower ..
  map_smul₂ a x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp [TensorProduct.smul_tmul', -algebraMap_smul,
        algebra_compatible_smul B a, SemialgHom.baseChange_of_algebraMap_tmul,
        RingHom.algebraMap_toAlgebra, SemialgHom.toLinearMap_eq_coe]
      ring
    | add x y hx hy => simp_all

open scoped TensorProduct.RightActions in
/-- If `ψ : A →ₛₐ[algebraMap R S] B` and if `B` is given the `A`-algebra induced by `ψ`, then
the resulting base change map `S ⊗[R] A →ₐ[S] B` is scalar in both `S` and `A`.
`baseChangeRightOfAlgebraMap ψ` is the induced `A`-algebra map `S ⊗[R] A →ₐ[A] B`. -/
noncomputable
def SemialgHom.baseChangeRightOfAlgebraMap [Algebra R S] [CommSemiring A] [Algebra R A]
    [CommSemiring B] [Algebra S B]
    (ψ : A →ₛₐ[algebraMap R S] B) :
    letI := ψ.toAlgebra
    S ⊗[R] A →ₐ[A] B :=
  letI := ψ.toAlgebra
  AlgHom.changeScalars A ψ.baseChangeOfAlgebraMap

open scoped TensorProduct.RightActions in
@[simp]
theorem SemialgHom.baseChangeRightOfAlgebraMap_apply [Algebra R S] [CommSemiring A] [Algebra R A]
    [CommSemiring B] [Algebra S B]
    (ψ : A →ₛₐ[algebraMap R S] B) (x : S ⊗[R] A) :
    baseChangeRightOfAlgebraMap ψ x = baseChangeOfAlgebraMap ψ x := by
  simp [baseChangeRightOfAlgebraMap, AlgHom.changeScalars_apply]

open scoped TensorProduct.RightActions in
@[simp]
theorem SemialgHom.baseChangeRightOfAlgebraMap_coe [Algebra R S] [CommSemiring A] [Algebra R A]
    [CommSemiring B] [Algebra S B]
    (ψ : A →ₛₐ[algebraMap R S] B) :
    ⇑ψ.baseChangeRightOfAlgebraMap = ⇑ψ.baseChangeOfAlgebraMap :=
  funext_iff.2 <| ψ.baseChangeRightOfAlgebraMap_apply

-- PORT (T016f-2a extension): `PhD.Main.QMF.FLTstuff.Mathlib.LinearAlgebra.Determinant` and
-- `PhD.Main.QMF.FLTstuff.HaarMeasure.HaarChar.FiniteDimensional` need the `LinearEquiv.mulLeft` /
-- `LinearEquiv.mulRight` block that the original partial port omitted, so it is added here,
-- verbatim from `FLT.Mathlib.Algebra.Algebra.Bilinear`. Mathlib has no equivalent.
variable (F : Type*) [CommSemiring F] {A : Type*} [Ring A]
    [Algebra F A]

-- needs PRing
/-- The F-linear equivalence on an F-algebra induced by left multiplication
by a unit
-/
def _root_.LinearEquiv.mulLeft (u : Aˣ) : A ≃ₗ[F] A where
  toFun x := u * x
  invFun y := u⁻¹ * y
  left_inv x := by simp
  right_inv y := by simp
  map_add' x₁ x₂ := left_distrib ↑u x₁ x₂
  map_smul' f x := by simp

@[simp]
theorem LinearEquiv.coe_mulLeft (u : Aˣ) :
    (LinearEquiv.mulLeft F u : A →ₗ[F] A) = LinearMap.mulLeft F (u : A) :=
  rfl

-- needs PRing
/-- The F-linear equivalence on an F-algebra induced by right multiplication
by a unit
-/
def _root_.LinearEquiv.mulRight (u : Aˣ) : A ≃ₗ[F] A where
  toFun x := x * u
  invFun y := y * u⁻¹
  left_inv x := by simp [mul_assoc]
  right_inv y := by simp [mul_assoc]
  map_add' x₁ x₂ := right_distrib x₁ x₂ u
  map_smul' f x := by simp

@[simp]
theorem LinearEquiv.coe_mulRight (u : Aˣ) :
    (LinearEquiv.mulRight F u : A →ₗ[F] A) = LinearMap.mulRight F (u : A) :=
  rfl
