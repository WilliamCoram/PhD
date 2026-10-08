/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.OverconvergentForms.Adelic.Basic

/-!
# Local components, rigidifications and the local sections `ι_v`

For each finite place `v` the evaluation `𝔸_F^f → F_v` induces the component map
`D_f → D ⊗_F F_v`, a continuous `F`-algebra homomorphism, and the components are jointly injective.
A *rigidification at `v`* is an `F_v`-algebra isomorphism `θ_v : D ⊗_F F_v ≃ M₂(F_v)`, carried as
data; with it the component becomes `θ_v : D_f^× →* GL₂(F_v)`. The component map is split by the
inclusion `ι_v : (D ⊗_F F_v)^× → D_f^×` of the elements that are trivial away from `v`, and the
image of `ι_v` commutes with every element whose `v`-component is trivial.

[Buz07, §9, p. 68]: "fix an isomorphism `𝒪_D ⊗_{𝒪_F} 𝒪_{F_v} = M₂(𝒪_{F_v})` for all finite places
`v` of `F` where `D` splits"; "If `x ∈ D_f` then let `x_p ∈ D_p = M₂(F_p)` denote the projection
onto the factor of `D_f` at `p`."

## Main definitions

* `AdelicAlgebra.Dv`: the local points `D ⊗_F F_v`; `AdelicAlgebra.evalAlgHom`: `𝔸_F^f → F_v`.
* `AdelicAlgebra.toLocal`, `AdelicAlgebra.toLocalUnits`: the `v`-component.
* `AdelicAlgebra.RigidificationAt`: the data of a splitting at `v`.
* `AdelicAlgebra.toGL`, `AdelicAlgebra.toMatrix`, `AdelicAlgebra.toMatrixHom`: the component
  through the rigidification.
* `AdelicAlgebra.singleₗ`, `AdelicAlgebra.extendZero`: extension by zero `F_v → 𝔸_F^f` and
  `D ⊗_F F_v → D_f`.
* `AdelicAlgebra.localIncl`, `AdelicAlgebra.unitAt`: the sections `ι_v`.

## Main results

* `AdelicAlgebra.continuous_toLocal`, `AdelicAlgebra.continuous_toGL`,
  `AdelicAlgebra.continuous_localIncl`, `AdelicAlgebra.continuous_unitAt`.
* `AdelicAlgebra.rightBasis_repr_toLocal`, `AdelicAlgebra.ext_toLocal`: the coordinates commute
  with the components, which are jointly injective.
* `AdelicAlgebra.RigidificationAt.moduleFinite`: a rigidification forces `D` finite over `F`.
* `AdelicAlgebra.extendZero_mul_eq`, `AdelicAlgebra.mul_extendZero_eq`: products with an element
  supported at `v` only see the `v`-component.
* `AdelicAlgebra.toLocalUnits_localIncl`, `AdelicAlgebra.toLocalUnits_localIncl_of_ne`,
  `AdelicAlgebra.toGL_unitAt`, `AdelicAlgebra.toGL_unitAt_of_ne`: `ι_v` splits the `v`-component
  and is trivial elsewhere.
* `AdelicAlgebra.localIncl_commute`, `AdelicAlgebra.unitAt_commute`: `ι_v` commutes with elements
  of trivial `v`-component; `AdelicAlgebra.exists_eq_localIncl_mul`: `g = ι_v(g_v) · g^{(v)}`.
* `AdelicAlgebra.unitsIncl_algebraMap_commute`, `AdelicAlgebra.toMatrix_unitsIncl_algebraMap`:
  global scalars are central and act as scalar matrices.

Roadmap: §0.1.3, §0.2.2. Tau Ceti home: `TauCeti/NumberTheory/AdelicAlgebra/Components.lean`.
-/

open scoped TensorProduct Classical
open IsDedekindDomain NumberField

noncomputable section

namespace AdelicAlgebra

open scoped RightAlgebra

variable (F : Type*) [Field F] [NumberField F] (D : Type*) [Ring D] [Algebra F D]
variable (v : HeightOneSpectrum (𝓞 F))

/-- Evaluation at `v`, as an `F`-algebra homomorphism `𝔸_F^f → F_v`. -/
def evalAlgHom : FiniteAdeleRing (𝓞 F) F →ₐ[F] v.adicCompletion F where
  toRingHom := RestrictedProduct.evalRingHom _ v
  commutes' _ := rfl

/-- **The local points** `D ⊗_F F_v`. -/
abbrev Dv : Type _ := D ⊗[F] v.adicCompletion F

/-- **The `v`-component** `D_f → D ⊗_F F_v`. -/
def toLocal : Df F D →ₐ[F] Dv F D v :=
  Algebra.TensorProduct.map (AlgHom.id F D) (evalAlgHom F v)

/-- The `v`-component on units. -/
def toLocalUnits : Dfx F D →* (Dv F D v)ˣ := Units.map (toLocal F D v).toMonoidHom

variable {F D}

@[simp]
theorem toLocal_tmul (x : D) (a : FiniteAdeleRing (𝓞 F) F) :
    toLocal F D v (x ⊗ₜ a) = x ⊗ₜ a v := rfl

/-- The component of a global element is the global element. -/
theorem toLocal_incl (x : D) : toLocal F D v (incl F D x) = x ⊗ₜ 1 := rfl

variable (F D)

/-- **The component map is continuous.** -/
theorem continuous_toLocal : Continuous (toLocal F D v) :=
  continuous_map_id (evalAlgHom F v) (RestrictedProduct.continuous_eval v)

/-- The `v`-component on units is continuous. -/
theorem continuous_toLocalUnits : Continuous (toLocalUnits F D v) :=
  Continuous.units_map _ (continuous_toLocal F D v)

variable {F D}

/-- The coordinates commute with the components. -/
theorem rightBasis_repr_toLocal {ι : Type*} (b : Module.Basis ι F D) (x : Df F D)
    (i : ι) :
    (rightBasis (R := v.adicCompletion F) b).repr (toLocal F D v x) i
      = ((rightBasis (R := FiniteAdeleRing (𝓞 F) F) b).repr x i) v := by
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    rfl
  | tmul d a =>
    rw [toLocal_tmul, rightBasis_repr_tmul, rightBasis_repr_tmul]
    rfl
  | add p q hp hq =>
    rw [map_add, map_add, Finsupp.add_apply, hp, hq, map_add, Finsupp.add_apply]
    rfl

/-- **The components are jointly injective.** -/
theorem ext_toLocal [Module.Finite F D] {x y : Df F D}
    (h : ∀ v, toLocal F D v x = toLocal F D v y) : x = y := by
  set b := Module.Free.chooseBasis F D
  apply (rightBasis (R := FiniteAdeleRing (𝓞 F) F) b).repr.injective
  refine Finsupp.ext fun i => DFunLike.ext _ _ fun w => ?_
  have hw := congrArg (fun z => (rightBasis (R := w.adicCompletion F) b).repr z i) (h w)
  simpa only [rightBasis_repr_toLocal] using hw

variable (F D)

/-- **A rigidification of `D` at `v`**: an `F_v`-algebra isomorphism `D ⊗_F F_v ≃ M₂(F_v)`. -/
class RigidificationAt : Type _ where
  /-- The splitting isomorphism `θ_v`. -/
  equiv : Dv F D v ≃ₐ[v.adicCompletion F] Matrix (Fin 2) (Fin 2) (v.adicCompletion F)

section Rigidification

variable [RigidificationAt F D v]

/-- The rigidification, as an `F`-algebra homomorphism from `D_f`. -/
def toMatrixHom : Df F D →ₐ[F] Matrix (Fin 2) (Fin 2) (v.adicCompletion F) :=
  ((RigidificationAt.equiv (F := F) (D := D) (v := v)).toAlgHom.restrictScalars F).comp
    (toLocal F D v)

/-- **`θ_v : D_f^× →* GL₂(F_v)`**, the `v`-component through the rigidification. -/
def toGL : Dfx F D →* GL (Fin 2) (v.adicCompletion F) :=
  Units.map (toMatrixHom F D v).toMonoidHom

/-- `θ_v` as a matrix-valued monoid homomorphism. -/
def toMatrix : Dfx F D →* Matrix (Fin 2) (Fin 2) (v.adicCompletion F) :=
  (Units.coeHom _).comp (toGL F D v)

variable {F D}

@[simp]
theorem coe_toGL (g : Dfx F D) :
    ((toGL F D v g : GL (Fin 2) (v.adicCompletion F)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = toMatrix F D v g := rfl

theorem toMatrix_apply (g : Dfx F D) :
    toMatrix F D v g =
      RigidificationAt.equiv (F := F) (D := D) (v := v) (toLocal F D v (g : Df F D)) := rfl

/-- `θ_v(g)` is an invertible matrix. -/
theorem toMatrix_det_ne_zero (g : Dfx F D) : (toMatrix F D v g).det ≠ 0 := by
  rw [← coe_toGL]
  exact ((toGL F D v g).isUnit.map Matrix.detMonoidHom).ne_zero

variable (F D)

include v in
/-- **A split algebra is finite-dimensional**: `D ⊗_F F_v ≃ M₂(F_v)` has rank `4` over `F_v`, and a
linearly independent family of `D` stays independent after base change. -/
theorem RigidificationAt.moduleFinite : Module.Finite F D := by
  classical
  have hfin : Module.Finite (v.adicCompletion F) (Dv F D v) :=
    Module.Finite.equiv (RigidificationAt.equiv (F := F) (D := D) (v := v)).symm.toLinearEquiv
  have : Finite (Module.Free.ChooseBasisIndex F D) :=
    Module.Finite.finite_basis (rightBasis (R := v.adicCompletion F) (Module.Free.chooseBasis F D))
  exact Module.Finite.of_basis (Module.Free.chooseBasis F D)

/-- The rigidification is a homeomorphism, being `F_v`-linear between finite free modules with
their module topologies. -/
theorem continuous_rigidification :
    Continuous (RigidificationAt.equiv (F := F) (D := D) (v := v)) :=
  IsModuleTopology.continuous_of_linearMap
    (RigidificationAt.equiv (F := F) (D := D) (v := v)).toLinearMap

/-- The inverse rigidification is continuous. -/
theorem continuous_rigidification_symm :
    Continuous (RigidificationAt.equiv (F := F) (D := D) (v := v)).symm := by
  haveI : IsModuleTopology (v.adicCompletion F)
      (Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) :=
    inferInstanceAs (IsModuleTopology (v.adicCompletion F)
      (Fin 2 → Fin 2 → v.adicCompletion F))
  exact IsModuleTopology.continuous_of_linearMap
    (RigidificationAt.equiv (F := F) (D := D) (v := v)).symm.toLinearMap

/-- **`θ_v` is continuous.** -/
theorem continuous_toMatrix : Continuous (toMatrix F D v) :=
  (continuous_rigidification F D v).comp ((continuous_toLocal F D v).comp Units.continuous_val)

/-- **`θ_v : D_f^× → GL₂(F_v)` is continuous.** -/
theorem continuous_toGL : Continuous (toGL F D v) :=
  Continuous.units_map _ ((continuous_rigidification F D v).comp (continuous_toLocal F D v))

end Rigidification

section LocalIncl

/-- The adele with `v`-component `a` and every other component `0`, `F`-linear in `a`. -/
def singleₗ : v.adicCompletion F →ₗ[F] FiniteAdeleRing (𝓞 F) F where
  toFun a := RestrictedProduct.single
    (fun w : HeightOneSpectrum (𝓞 F) ↦ w.adicCompletionIntegers F) v a
  map_add' a b := DFunLike.ext _ _ fun w => congrFun (Pi.single_add v a b) w
  map_smul' c a := by
    rw [RingHom.id_apply, Algebra.smul_def c a]
    exact (RestrictedProduct.mul_single (fun w ↦ w.adicCompletionIntegers F) v a
      (algebraMap F (FiniteAdeleRing (𝓞 F) F) c)).trans
      (Algebra.smul_def (A := FiniteAdeleRing (𝓞 F) F) c _).symm

/-- **Extension by zero** `D ⊗_F F_v → D_f`: additive and multiplicative, not unital. -/
def extendZero : Dv F D v →ₗ[F] Df F D := LinearMap.lTensor D (singleₗ F v)

variable {F D}

private theorem singleₗ_apply_same (a : v.adicCompletion F) : singleₗ F v a v = a :=
  RestrictedProduct.single_eq_same (fun w ↦ w.adicCompletionIntegers F) v a

private theorem singleₗ_apply_ne (a : v.adicCompletion F) {w : HeightOneSpectrum (𝓞 F)}
    (hw : w ≠ v) : singleₗ F v a w = 0 :=
  RestrictedProduct.single_eq_of_ne (fun w ↦ w.adicCompletionIntegers F) a hw

private theorem adele_mul_apply (x y : FiniteAdeleRing (𝓞 F) F) (w : HeightOneSpectrum (𝓞 F)) :
    (x * y) w = x w * y w := rfl

private theorem singleₗ_mul (a : v.adicCompletion F) (b : FiniteAdeleRing (𝓞 F) F) :
    singleₗ F v a * b = singleₗ F v (a * b v) := by
  refine DFunLike.ext _ _ fun w => ?_
  rcases eq_or_ne w v with rfl | hw
  · rw [adele_mul_apply, singleₗ_apply_same, singleₗ_apply_same]
  · rw [adele_mul_apply, singleₗ_apply_ne v a hw, singleₗ_apply_ne v _ hw, zero_mul]

private theorem mul_singleₗ (a : v.adicCompletion F) (b : FiniteAdeleRing (𝓞 F) F) :
    b * singleₗ F v a = singleₗ F v (b v * a) := by
  refine DFunLike.ext _ _ fun w => ?_
  rcases eq_or_ne w v with rfl | hw
  · rw [adele_mul_apply, singleₗ_apply_same, singleₗ_apply_same]
  · rw [adele_mul_apply, singleₗ_apply_ne v a hw, singleₗ_apply_ne v _ hw, mul_zero]

private theorem extendZero_tmul (d : D) (a : v.adicCompletion F) :
    extendZero F D v (d ⊗ₜ a) = d ⊗ₜ singleₗ F v a :=
  LinearMap.lTensor_tmul D (singleₗ F v) d a

/-- Extension by zero is multiplicative. -/
theorem extendZero_mul (x y : Dv F D v) :
    extendZero F D v (x * y) = extendZero F D v x * extendZero F D v y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul d a =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul e b =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, extendZero_tmul, extendZero_tmul, extendZero_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, singleₗ_mul, singleₗ_apply_same]
    | add y₁ y₂ h₁ h₂ => rw [mul_add, map_add, map_add, h₁, h₂, mul_add]
  | add x₁ x₂ h₁ h₂ => rw [add_mul, map_add, map_add, h₁, h₂, add_mul]

/-- The `v`-component of `ι_v(x)` is `x`. -/
theorem toLocal_extendZero (x : Dv F D v) : toLocal F D v (extendZero F D v x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul d a => rw [extendZero_tmul, toLocal_tmul, singleₗ_apply_same]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The `w`-component of `ι_v(x)` vanishes for `w ≠ v`. -/
theorem toLocal_extendZero_of_ne {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) (x : Dv F D v) :
    toLocal F D w (extendZero F D v x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul d a => rw [extendZero_tmul, toLocal_tmul, singleₗ_apply_ne v a hw, TensorProduct.tmul_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/-- `ι_v(x) · g = ι_v(x · g_v)`: multiplying by an element supported at `v` only sees the
`v`-component. -/
theorem extendZero_mul_eq (x : Dv F D v) (g : Df F D) :
    extendZero F D v x * g = extendZero F D v (x * toLocal F D v g) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul d a =>
    induction g using TensorProduct.induction_on with
    | zero => simp
    | tmul e b =>
      rw [extendZero_tmul, Algebra.TensorProduct.tmul_mul_tmul, toLocal_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, extendZero_tmul, singleₗ_mul]
    | add g₁ g₂ h₁ h₂ => rw [mul_add, h₁, h₂, map_add, mul_add, map_add]
  | add x₁ x₂ h₁ h₂ => rw [map_add, add_mul, h₁, h₂, add_mul, map_add]

/-- `g · ι_v(x) = ι_v(g_v · x)`. -/
theorem mul_extendZero_eq (x : Dv F D v) (g : Df F D) :
    g * extendZero F D v x = extendZero F D v (toLocal F D v g * x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul d a =>
    induction g using TensorProduct.induction_on with
    | zero => simp
    | tmul e b =>
      rw [extendZero_tmul, Algebra.TensorProduct.tmul_mul_tmul, toLocal_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, extendZero_tmul, mul_singleₗ]
    | add g₁ g₂ h₁ h₂ => rw [add_mul, h₁, h₂, map_add, add_mul, map_add]
  | add x₁ x₂ h₁ h₂ => rw [map_add, mul_add, h₁, h₂, mul_add, map_add]

private theorem one_add_extendZero_mul (x y : Dv F D v) :
    (1 + extendZero F D v (x - 1)) * (1 + extendZero F D v (y - 1)) =
      1 + extendZero F D v (x * y - 1) := by
  have h : x * y - 1 = (x - 1) + (y - 1) + (x - 1) * (y - 1) := by noncomm_ring
  rw [h, map_add, map_add, extendZero_mul]
  noncomm_ring

private theorem continuous_singleₗ : Continuous (singleₗ F v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.mpr (Set.finite_singleton v).compl_mem_cofinite
  have hmem (a : v.adicCompletion F) :
      ∀ᶠ w in Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))),
        Pi.single v a w ∈ (w.adicCompletionIntegers F : Set (w.adicCompletion F)) :=
    Filter.eventually_principal.mpr fun w hw => by
      rw [Pi.single_eq_of_ne (Set.mem_compl_singleton_iff.mp hw)]
      exact (w.adicCompletionIntegers F).zero_mem
  have hf : Continuous fun a : v.adicCompletion F => RestrictedProduct.mk _ (hmem a) :=
    RestrictedProduct.continuous_rng_of_principal.mpr (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

private theorem rightBasis_repr_extendZero {ι : Type*} (b : Module.Basis ι F D) (x : Dv F D v)
    (i : ι) :
    (rightBasis (R := FiniteAdeleRing (𝓞 F) F) b).repr (extendZero F D v x) i
      = singleₗ F v ((rightBasis (R := v.adicCompletion F) b).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul d a =>
    rw [extendZero_tmul, rightBasis_repr_tmul, rightBasis_repr_tmul]
    exact singleₗ_mul v a _
  | add p q hp hq => simp only [map_add, Finsupp.add_apply, hp, hq]

private theorem continuous_extendZero [Module.Finite F D] : Continuous (extendZero F D v) := by
  set b := Module.Free.chooseBasis F D
  let eA := rightCoordsL (R := FiniteAdeleRing (𝓞 F) F) b
  let eV := rightCoordsL (R := v.adicCompletion F) b
  have h : ∀ x, extendZero F D v x = eA.symm (fun i => singleₗ F v (eV x i)) := fun x =>
    eA.injective <| by
      rw [ContinuousLinearEquiv.apply_symm_apply]
      funext i
      exact rightBasis_repr_extendZero v b x i
  have hc : Continuous fun x => eA.symm (fun i => singleₗ F v (eV x i)) :=
    eA.symm.continuous.comp (continuous_pi fun i =>
      (continuous_singleₗ v).comp ((continuous_apply i).comp eV.continuous))
  exact hc.congr fun x => (h x).symm

variable (F D)

/-- **The local section** `ι_v : (D ⊗_F F_v)^× →* D_f^×`: the unit with `v`-component `u` and
trivial components elsewhere, `1 + ι_v(u − 1)`. -/
def localIncl : (Dv F D v)ˣ →* Dfx F D where
  toFun u :=
    ⟨1 + extendZero F D v ((u : Dv F D v) - 1), 1 + extendZero F D v (((u⁻¹ : (Dv F D v)ˣ) :
      Dv F D v) - 1), by rw [one_add_extendZero_mul, Units.mul_inv, sub_self, map_zero, add_zero],
      by rw [one_add_extendZero_mul, Units.inv_mul, sub_self, map_zero, add_zero]⟩
  map_one' := Units.ext <| by simp
  map_mul' u u' := Units.ext (one_add_extendZero_mul v (u : Dv F D v) u').symm

variable {F D}

private theorem val_localIncl (u : (Dv F D v)ˣ) :
    (localIncl F D v u : Df F D) = 1 + extendZero F D v ((u : Dv F D v) - 1) := rfl

private theorem val_toLocalUnits (g : Dfx F D) :
    (toLocalUnits F D v g : Dv F D v) = toLocal F D v g := rfl

/-- **`ι_v` splits the `v`-component.** -/
@[simp]
theorem toLocalUnits_localIncl (u : (Dv F D v)ˣ) :
    toLocalUnits F D v (localIncl F D v u) = u := by
  refine Units.ext ?_
  rw [val_toLocalUnits, val_localIncl, map_add, map_one, toLocal_extendZero]
  abel

/-- **`ι_v` is trivial at every `w ≠ v`.** -/
theorem toLocalUnits_localIncl_of_ne {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v)
    (u : (Dv F D v)ˣ) : toLocalUnits F D w (localIncl F D v u) = 1 := by
  refine Units.ext ?_
  rw [val_toLocalUnits, val_localIncl, map_add, map_one, toLocal_extendZero_of_ne v hw, add_zero,
    Units.val_one]

private theorem toLocal_localIncl (u : (Dv F D v)ˣ) :
    toLocal F D v (localIncl F D v u : Df F D) = u :=
  congrArg Units.val (toLocalUnits_localIncl v u)

private theorem toLocal_localIncl_of_ne {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v)
    (u : (Dv F D v)ˣ) : toLocal F D w (localIncl F D v u : Df F D) = 1 :=
  congrArg Units.val (toLocalUnits_localIncl_of_ne v hw u)

/-- `ι_v` is injective, being split by the `v`-component. -/
theorem localIncl_injective : Function.Injective (localIncl F D v) :=
  Function.LeftInverse.injective (g := toLocalUnits F D v) (toLocalUnits_localIncl v)

/-- **`ι_v` commutes with every element of trivial `v`-component.** -/
theorem localIncl_commute (u : (Dv F D v)ˣ) {g : Dfx F D} (hg : toLocalUnits F D v g = 1) :
    Commute (localIncl F D v u) g := by
  have hg' : toLocal F D v (g : Df F D) = 1 := by
    rw [← val_toLocalUnits, hg, Units.val_one]
  show localIncl F D v u * g = g * localIncl F D v u
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, val_localIncl, add_mul, mul_add, one_mul, mul_one,
    extendZero_mul_eq, mul_extendZero_eq, hg', mul_one, one_mul]

/-- The images of `ι_v` and `ι_w` commute for `v ≠ w`. -/
theorem localIncl_commute_of_ne {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v)
    (u : (Dv F D v)ˣ) (u' : (Dv F D w)ˣ) :
    Commute (localIncl F D v u) (localIncl F D w u') :=
  localIncl_commute v u (toLocalUnits_localIncl_of_ne w hw.symm u')

/-- An element is determined by its `v`-component and its components away from `v`:
`g = ι_v(g_v) · g^{(v)}` with `g^{(v)}` of trivial `v`-component. -/
theorem exists_eq_localIncl_mul (g : Dfx F D) :
    ∃ g' : Dfx F D, toLocalUnits F D v g' = 1 ∧
      g = localIncl F D v (toLocalUnits F D v g) * g' :=
  ⟨(localIncl F D v (toLocalUnits F D v g))⁻¹ * g, by
    rw [map_mul, map_inv, toLocalUnits_localIncl, inv_mul_cancel], by
    rw [mul_inv_cancel_left]⟩

/-- **`ι_v` is continuous**: `RestrictedProduct.single` is continuous through the restricted
product over the principal filter of `{v}ᶜ`, and `ι_v` is `single` in the coordinates of a basis. -/
theorem continuous_localIncl [Module.Finite F D] : Continuous (localIncl F D v) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun u : (Dv F D v)ˣ => 1 + extendZero F D v ((u : Dv F D v) - 1)
    exact continuous_const.add
      ((continuous_extendZero v).comp (Units.continuous_val.sub continuous_const))
  · show Continuous fun u : (Dv F D v)ˣ =>
      1 + extendZero F D v (((u⁻¹ : (Dv F D v)ˣ) : Dv F D v) - 1)
    exact continuous_const.add
      ((continuous_extendZero v).comp (Units.continuous_coe_inv.sub continuous_const))

end LocalIncl

section UnitAt

variable [RigidificationAt F D v]

/-- **`ι_v : GL₂(F_v) →* D_f^×`**, the local section through the rigidification. -/
def unitAt : GL (Fin 2) (v.adicCompletion F) →* Dfx F D :=
  (localIncl F D v).comp
    (Units.map (RigidificationAt.equiv (F := F) (D := D) (v := v)).symm.toAlgHom.toMonoidHom)

variable {F D}

private theorem unitAt_apply (m : GL (Fin 2) (v.adicCompletion F)) :
    unitAt F D v m = localIncl F D v
      (Units.map (RigidificationAt.equiv (F := F) (D := D) (v := v)).symm.toAlgHom.toMonoidHom m) :=
  rfl

/-- **`θ_v ∘ ι_v = id`.** -/
@[simp]
theorem toGL_unitAt (m : GL (Fin 2) (v.adicCompletion F)) : toGL F D v (unitAt F D v m) = m := by
  refine Units.ext ?_
  rw [coe_toGL, toMatrix_apply, unitAt_apply, toLocal_localIncl, Units.coe_map]
  exact (RigidificationAt.equiv (F := F) (D := D) (v := v)).apply_symm_apply _

/-- **`θ_w ∘ ι_v = 1`** for `w ≠ v`. -/
theorem toGL_unitAt_of_ne {w : HeightOneSpectrum (𝓞 F)} [RigidificationAt F D w] (hw : w ≠ v)
    (m : GL (Fin 2) (v.adicCompletion F)) : toGL F D w (unitAt F D v m) = 1 := by
  refine Units.ext ?_
  rw [coe_toGL, toMatrix_apply, unitAt_apply, toLocal_localIncl_of_ne v hw, map_one,
    Units.val_one]

/-- `ι_v : GL₂(F_v) → D_f^×` is injective. -/
theorem unitAt_injective : Function.Injective (unitAt F D v) :=
  Function.LeftInverse.injective (g := toGL F D v) (toGL_unitAt v)

/-- `ι_v(m)` commutes with every element of trivial `v`-component. -/
theorem unitAt_commute (m : GL (Fin 2) (v.adicCompletion F)) {g : Dfx F D}
    (hg : toLocalUnits F D v g = 1) : Commute (unitAt F D v m) g := by
  rw [unitAt_apply]
  exact localIncl_commute v _ hg

/-- The `v`-component is trivial as soon as `θ_v` is. -/
theorem toLocalUnits_eq_one_of_toGL_eq_one {g : Dfx F D} (hg : toGL F D v g = 1) :
    toLocalUnits F D v g = 1 := by
  refine Units.ext ?_
  have h : RigidificationAt.equiv (F := F) (D := D) (v := v) (toLocal F D v (g : Df F D)) =
      RigidificationAt.equiv (F := F) (D := D) (v := v) 1 := by
    rw [map_one, ← toMatrix_apply, ← coe_toGL, hg, Units.val_one]
  exact (RigidificationAt.equiv (F := F) (D := D) (v := v)).injective h

/-- Global scalars are central. -/
theorem unitsIncl_algebraMap_commute (c : Fˣ) (g : Dfx F D) :
    Commute (unitsIncl F D (Units.map (algebraMap F D).toMonoidHom c)) g := by
  have h : ((unitsIncl F D (Units.map (algebraMap F D).toMonoidHom c) : Dfx F D) : Df F D) =
      algebraMap F (Df F D) (c : F) := rfl
  show _ * g = g * _
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, h]
  exact Algebra.commutes _ _

/-- `θ_v` of a global scalar is the scalar matrix. -/
theorem toMatrix_unitsIncl_algebraMap (c : Fˣ) :
    toMatrix F D v (unitsIncl F D (Units.map (algebraMap F D).toMonoidHom c)) =
      algebraMap F (v.adicCompletion F) (c : F) •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) := by
  have h : toLocal F D v ((unitsIncl F D (Units.map (algebraMap F D).toMonoidHom c) : Dfx F D) :
      Df F D) = algebraMap (v.adicCompletion F) (Dv F D v)
        (algebraMap F (v.adicCompletion F) (c : F)) := by
    rw [Algebra.TensorProduct.right_algebraMap_apply]
    show algebraMap F D (c : F) ⊗ₜ[F] (1 : v.adicCompletion F) =
      (1 : D) ⊗ₜ[F] algebraMap F (v.adicCompletion F) (c : F)
    rw [Algebra.algebraMap_eq_smul_one (A := D),
      Algebra.algebraMap_eq_smul_one (A := v.adicCompletion F), TensorProduct.smul_tmul]
  rw [toMatrix_apply, h, AlgEquiv.commutes]
  exact Algebra.algebraMap_eq_smul_one _

/-- **`ι_v : GL₂(F_v) → D_f^×` is continuous.** -/
theorem continuous_unitAt [Module.Finite F D] : Continuous (unitAt F D v) :=
  (continuous_localIncl v).comp (Continuous.units_map
    (RigidificationAt.equiv (F := F) (D := D) (v := v)).symm.toAlgHom.toMonoidHom
    (continuous_rigidification_symm F D v))

end UnitAt

end AdelicAlgebra
