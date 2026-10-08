/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Base change on the right: `D ⊗[F] R` as a topological `R`-algebra

The finite-adelic points of an `F`-algebra `D` are `D ⊗[F] 𝔸_F^f`, with the coefficient ring on the
**right**, as in Buzzard's `D_f := D ⊗_F 𝔸_{F,f}` and the FLT project. Mathlib's base-change API
puts the coefficients on the left (`Algebra.TensorProduct.leftAlgebra`,
`Module.Finite.base_change`, `Algebra.TensorProduct.basis`) and keeps
`Algebra.TensorProduct.rightAlgebra` a non-instance, because
on `A ⊗[R] A` the two actions are different. For a noncommutative `D` there is no such ambiguity, so
this file turns the right action on, in the scope `AdelicAlgebra.RightAlgebra`, and transports
finiteness, freeness and bases along `TensorProduct.comm`. The topology is the `R`-module topology.

[Buz07, §9, p. 68]: "Define `𝔸_{F,f}` to be the finite adeles of `F` and `D_f := D ⊗_F 𝔸_{F,f}`."

## Main definitions

* `AdelicAlgebra.RightAlgebra`: the scope of the instances `Algebra R (D ⊗[F] R)`,
  `Module.Finite R (D ⊗[F] R)`, `Module.Free R (D ⊗[F] R)`, the module topology,
  `ContinuousAdd (D ⊗[F] R)` and `IsTopologicalRing (D ⊗[F] R)`.
* `AdelicAlgebra.commRight`: the commutation `R ⊗[F] D ≃ₗ[R] D ⊗[F] R`.
* `AdelicAlgebra.rightBasis`: the `R`-basis `b i ⊗ₜ 1` of `D ⊗[F] R`.
* `AdelicAlgebra.rightCoordsL`: the coordinates `D ⊗[F] R ≃L[R] (ι → R)`, a homeomorphism.

## Main results

* `AdelicAlgebra.continuous_map_id`: `id ⊗ f` is continuous for a continuous `f : R →ₐ[F] R'`.

Roadmap: §0.2.1. Tau Ceti home: `TauCeti/NumberTheory/AdelicAlgebra/RightBaseChange.lean`.
-/

open scoped TensorProduct

noncomputable section

namespace AdelicAlgebra

namespace RightAlgebra

attribute [scoped instance] Algebra.TensorProduct.rightAlgebra

variable {F : Type*} [CommRing F] {D : Type*} [Ring D] [Algebra F D]
variable {R : Type*} [CommRing R] [Algebra F R]

private def commRightAux (F D R : Type*) [CommRing F] [Ring D] [Algebra F D] [CommRing R]
    [Algebra F R] : R ⊗[F] D ≃ₗ[R] D ⊗[F] R :=
  { (TensorProduct.comm F R D).toAddEquiv with
    map_smul' := by
      intro r x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r' y =>
        simp [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply,
          Algebra.TensorProduct.tmul_mul_tmul]
      | add u v hu hv =>
        have hu' : TensorProduct.comm F R D (r • u) = r • TensorProduct.comm F R D u := hu
        have hv' : TensorProduct.comm F R D (r • v) = r • TensorProduct.comm F R D v := hv
        simp [smul_add, hu', hv'] }

/-- The right base change of a finite module is finite. -/
scoped instance instModuleFinite [Module.Finite F D] : Module.Finite R (D ⊗[F] R) :=
  Module.Finite.equiv (commRightAux F D R)

/-- The right base change of a free module is free. -/
scoped instance instModuleFree [Module.Free F D] : Module.Free R (D ⊗[F] R) :=
  Module.Free.of_equiv (commRightAux F D R)

/-- The `R`-module topology on `D ⊗[F] R`. -/
scoped instance instTopologicalSpace [TopologicalSpace R] : TopologicalSpace (D ⊗[F] R) :=
  moduleTopology R (D ⊗[F] R)

scoped instance instIsModuleTopology [TopologicalSpace R] : IsModuleTopology R (D ⊗[F] R) :=
  ⟨rfl⟩

/-- Addition is continuous for the module topology. -/
scoped instance instContinuousAdd [TopologicalSpace R] : ContinuousAdd (D ⊗[F] R) :=
  IsModuleTopology.toContinuousAdd R _

/-- `D ⊗[F] R` is a topological ring for the module topology. -/
scoped instance instIsTopologicalRing [TopologicalSpace R] [IsTopologicalRing R]
    [Module.Finite F D] : IsTopologicalRing (D ⊗[F] R) :=
  IsModuleTopology.isTopologicalRing R _

end RightAlgebra

open scoped RightAlgebra

variable {F : Type*} [CommRing F] {D : Type*} [Ring D] [Algebra F D]
variable {R : Type*} [CommRing R] [Algebra F R]
variable {ι : Type*}

/-- The commutation `R ⊗[F] D ≃ₗ[R] D ⊗[F] R`, linear for the right action on the target. -/
def commRight (F D R : Type*) [CommRing F] [Ring D] [Algebra F D] [CommRing R] [Algebra F R] :
    R ⊗[F] D ≃ₗ[R] D ⊗[F] R :=
  { (TensorProduct.comm F R D).toAddEquiv with
    map_smul' := (RightAlgebra.commRightAux F D R).map_smul' }

@[simp]
theorem commRight_tmul (r : R) (x : D) : commRight F D R (r ⊗ₜ x) = x ⊗ₜ r := rfl

/-- **The right base change of a basis**: `b i ⊗ₜ 1` is an `R`-basis of `D ⊗[F] R`. -/
def rightBasis (b : Module.Basis ι F D) : Module.Basis ι R (D ⊗[F] R) :=
  (Algebra.TensorProduct.basis R b).map (commRight F D R)

@[simp]
theorem rightBasis_apply (b : Module.Basis ι F D) (i : ι) :
    rightBasis (R := R) b i = b i ⊗ₜ 1 := by
  simp [rightBasis]

/-- The coordinates of `x ⊗ₜ r`: those of `x`, scaled by `r`. -/
theorem rightBasis_repr_tmul (b : Module.Basis ι F D) (x : D) (r : R) (i : ι) :
    (rightBasis (R := R) b).repr (x ⊗ₜ r) i = r * algebraMap F R (b.repr x i) := by
  have hsymm : (commRight F D R).symm (x ⊗ₜ r) = r ⊗ₜ x :=
    (LinearEquiv.symm_apply_eq _).mpr (commRight_tmul r x).symm
  simp [rightBasis, hsymm]

section Topology

variable [TopologicalSpace R] [IsTopologicalRing R] [Finite ι]

/-- **The coordinates are a homeomorphism**: `D ⊗[F] R ≃L[R] (ι → R)` for the module topology. -/
def rightCoordsL (b : Module.Basis ι F D) : (D ⊗[F] R) ≃L[R] (ι → R) :=
  { (rightBasis (R := R) b).equivFun with
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (rightBasis (R := R) b).equivFun.toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (rightBasis (R := R) b).equivFun.symm.toLinearMap }

@[simp]
theorem rightCoordsL_apply (b : Module.Basis ι F D) (x : D ⊗[F] R) (i : ι) :
    rightCoordsL b x i = (rightBasis (R := R) b).repr x i := rfl

variable {R' : Type*} [CommRing R'] [Algebra F R'] [TopologicalSpace R'] [IsTopologicalRing R']

omit [IsTopologicalRing R] [IsTopologicalRing R'] in
/-- **Base change of a continuous coefficient map is continuous**: for `f : R →ₐ[F] R'` continuous,
`id ⊗ f : D ⊗[F] R → D ⊗[F] R'` is continuous for the module topologies. -/
theorem continuous_map_id (f : R →ₐ[F] R') (hf : Continuous f) :
    Continuous (Algebra.TensorProduct.map (AlgHom.id F D) f) := by
  let φ : (D ⊗[F] R) →ₛₗ[f.toRingHom] (D ⊗[F] R') :=
    { toFun := Algebra.TensorProduct.map (AlgHom.id F D) f
      map_add' := map_add _
      map_smul' := by
        intro r x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul y r' =>
          simp [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply,
            Algebra.TensorProduct.tmul_mul_tmul]
        | add u v hu hv =>
          have hu' : Algebra.TensorProduct.map (AlgHom.id F D) f (r • u)
              = f r • Algebra.TensorProduct.map (AlgHom.id F D) f u := hu
          have hv' : Algebra.TensorProduct.map (AlgHom.id F D) f (r • v)
              = f r • Algebra.TensorProduct.map (AlgHom.id F D) f v := hv
          simp [smul_add, hu', hv'] }
  exact IsModuleTopology.continuous_of_linearMapₛₗ hf φ

end Topology

end AdelicAlgebra
