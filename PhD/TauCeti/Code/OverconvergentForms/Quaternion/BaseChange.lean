/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.OverconvergentForms.Quaternion.ReducedNorm
import PhD.TauCeti.Code.OverconvergentForms.Adelic.RightBaseChange
import Mathlib.Algebra.QuaternionBasis

/-!
# Base change of quaternion algebras

`ℍ[F,a,b] ⊗_F R ≃ ℍ[R,a,b]` for every commutative `F`-algebra `R`, natural in `R`. Through it the
reduced norm extends to `ℍ[F,a,b] ⊗_F R → R`, which is what makes the reduced norm of an adelic
point `g ∈ (D ⊗_F 𝔸_F^f)^×` an idele.

[Voi21, 27.6.12]: "we have a natural multiplicative map `‖ ‖ : B̂^× → ℝ_{>0}`,
`α = (α_v)_v ↦ ∏_v |nrd(α_v)|_v`."

## Main definitions

* `QuaternionAlgebra.baseChangeEquiv`: `ℍ[F,a,b] ⊗[F] R ≃ₐ[R] ℍ[R,a,b]`.
* `QuaternionAlgebra.nrdBaseChange`: the reduced norm `ℍ[F,a,b] ⊗[F] R →*₀ R`.

## Main results

* `QuaternionAlgebra.baseChangeEquiv_map`: naturality in `R`.
* `QuaternionAlgebra.baseChangeEquiv_tmul`: `x ⊗ r ↦ r • x`.
* `QuaternionAlgebra.nrdBaseChange_map`, `QuaternionAlgebra.nrdBaseChange_tmul_one`.
* `QuaternionAlgebra.continuous_nrdBaseChange`: continuity for the module topology.
* `QuaternionAlgebra.det_eq_nrdBaseChange`: the reduced norm is the determinant of every
  `R`-linear splitting.

## Implementation notes

Mathlib has no base change for quaternion algebras, so `baseChangeEquiv` is built by hand: the
forward map is `Algebra.TensorProduct.lift` of `mapRingHom` and `algebraMap R _` (an `F`-algebra
homomorphism, upgraded to an `R`-algebra homomorphism by its `commutes'` field), and the inverse is
`QuaternionAlgebra.Basis.liftHom` for the quaternionic basis `i ⊗ 1`, `j ⊗ 1`, `k ⊗ 1`. Note that
the `•` of the scoped right algebra is invisible to the generic `smul` simp lemmas; rewrite with
`Algebra.smul_def` and `Algebra.TensorProduct.right_algebraMap_apply` instead.

Roadmap: §0.1.1, §0.2.4. Tau Ceti home: `TauCeti/Algebra/QuaternionAlgebra/BaseChange.lean`.
-/

open scoped Quaternion TensorProduct

noncomputable section

namespace QuaternionAlgebra

open scoped AdelicAlgebra.RightAlgebra

variable (F : Type*) [Field F] (a b : F)
variable (R : Type*) [CommRing R] [Algebra F R]

private theorem tmul_algebraMap_one (c : F) :
    (algebraMap F ℍ[F,a,b] c) ⊗ₜ[F] (1 : R)
      = algebraMap R (ℍ[F,a,b] ⊗[F] R) (algebraMap F R c) := by
  rw [Algebra.TensorProduct.right_algebraMap_apply, Algebra.algebraMap_eq_smul_one,
    TensorProduct.smul_tmul]
  simp [Algebra.smul_def]

/-- The coefficient map `ℍ[F,a,b] → ℍ[R,a,b]`, as an `F`-algebra homomorphism. -/
private def mapAlgHom : ℍ[F,a,b] →ₐ[F] ℍ[R,algebraMap F R a,algebraMap F R b] :=
  { mapRingHom (algebraMap F R) a b with
    commutes' := fun c => by
      rw [algebraMap_eq, IsScalarTower.algebraMap_apply F R ℍ[R,algebraMap F R a,algebraMap F R b],
        algebraMap_eq]
      ext <;> simp [mapRingHom] }

/-- The forward map of the base change as an `F`-algebra homomorphism. -/
private def baseChangeHomF : ℍ[F,a,b] ⊗[F] R →ₐ[F] ℍ[R,algebraMap F R a,algebraMap F R b] :=
  Algebra.TensorProduct.lift (mapAlgHom F a b R)
    ((Algebra.ofId R ℍ[R,algebraMap F R a,algebraMap F R b]).restrictScalars F)
    fun _ y => (Algebra.commutes y _).symm

private theorem baseChangeHomF_tmul (x : ℍ[F,a,b]) (r : R) :
    baseChangeHomF F a b R (x ⊗ₜ[F] r) = r • mapRingHom (algebraMap F R) a b x := by
  simp only [baseChangeHomF]
  simp only [mapAlgHom, Algebra.smul_def]
  exact (Algebra.commutes r _).symm

/-- The forward map of the base change, `x ⊗ r ↦ r • x`. -/
private def baseChangeHom : ℍ[F,a,b] ⊗[F] R →ₐ[R] ℍ[R,algebraMap F R a,algebraMap F R b] :=
  { baseChangeHomF F a b R with
    commutes' := fun r => by
      rw [show algebraMap R (ℍ[F,a,b] ⊗[F] R) r = (1 : ℍ[F,a,b]) ⊗ₜ[F] r from
        Algebra.TensorProduct.right_algebraMap_apply r]
      show baseChangeHomF F a b R ((1 : ℍ[F,a,b]) ⊗ₜ[F] r) = _
      rw [baseChangeHomF_tmul]
      simp [mapRingHom, Algebra.smul_def, algebraMap_eq] }

private theorem baseChangeHom_tmul (x : ℍ[F,a,b]) (r : R) :
    baseChangeHom F a b R (x ⊗ₜ[F] r) = r • mapRingHom (algebraMap F R) a b x :=
  baseChangeHomF_tmul F a b R x r

/-- The quaternionic basis of `ℍ[F,a,b] ⊗[F] R` over `R`. -/
private def baseChangeBasis :
    QuaternionAlgebra.Basis (ℍ[F,a,b] ⊗[F] R) (algebraMap F R a) 0 (algebraMap F R b) where
  i := (⟨0, 1, 0, 0⟩ : ℍ[F,a,b]) ⊗ₜ[F] 1
  j := (⟨0, 0, 1, 0⟩ : ℍ[F,a,b]) ⊗ₜ[F] 1
  k := (⟨0, 0, 0, 1⟩ : ℍ[F,a,b]) ⊗ₜ[F] 1
  i_mul_i := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      show (⟨0, 1, 0, 0⟩ : ℍ[F,a,b]) * ⟨0, 1, 0, 0⟩ = algebraMap F ℍ[F,a,b] a from by
        rw [algebraMap_eq]; ext <;> simp, tmul_algebraMap_one]
    simp [Algebra.smul_def]
  j_mul_j := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      show (⟨0, 0, 1, 0⟩ : ℍ[F,a,b]) * ⟨0, 0, 1, 0⟩ = algebraMap F ℍ[F,a,b] b from by
        rw [algebraMap_eq]; ext <;> simp, tmul_algebraMap_one]
    simp [Algebra.smul_def]
  i_mul_j := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      show (⟨0, 1, 0, 0⟩ : ℍ[F,a,b]) * ⟨0, 0, 1, 0⟩ = ⟨0, 0, 0, 1⟩ from by ext <;> simp]
  j_mul_i := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      show (⟨0, 0, 1, 0⟩ : ℍ[F,a,b]) * ⟨0, 1, 0, 0⟩ = -⟨0, 0, 0, 1⟩ from by ext <;> simp,
      TensorProduct.neg_tmul]
    simp [Algebra.smul_def]

private theorem tmul_one_eq (xr xi xj xk : F) :
    (⟨xr, xi, xj, xk⟩ : ℍ[F,a,b]) ⊗ₜ[F] (1 : R)
      = algebraMap F ℍ[F,a,b] xr ⊗ₜ[F] (1 : R) + (⟨0, 1, 0, 0⟩ : ℍ[F,a,b]) ⊗ₜ[F] (xi • (1 : R))
        + (⟨0, 0, 1, 0⟩ : ℍ[F,a,b]) ⊗ₜ[F] (xj • (1 : R))
        + (⟨0, 0, 0, 1⟩ : ℍ[F,a,b]) ⊗ₜ[F] (xk • (1 : R)) := by
  rw [show (⟨xr, xi, xj, xk⟩ : ℍ[F,a,b]) = algebraMap F ℍ[F,a,b] xr + xi • ⟨0, 1, 0, 0⟩
      + xj • ⟨0, 0, 1, 0⟩ + xk • ⟨0, 0, 0, 1⟩ from by rw [algebraMap_eq]; ext <;> simp]
  simp only [TensorProduct.add_tmul, TensorProduct.smul_tmul]

private theorem liftHom_mapRingHom (x : ℍ[F,a,b]) :
    (baseChangeBasis F a b R).liftHom (mapRingHom (algebraMap F R) a b x) = x ⊗ₜ[F] (1 : R) := by
  obtain ⟨xr, xi, xj, xk⟩ := x
  rw [QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift, tmul_one_eq,
    tmul_algebraMap_one]
  simp [baseChangeBasis, mapRingHom, Algebra.smul_def,
    Algebra.TensorProduct.right_algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]

/-- **Base change of a quaternion algebra**: `ℍ[F,a,b] ⊗_F R ≃ ℍ[R,a,b]`, an `R`-algebra
isomorphism sending `x ⊗ r` to `r • x`. -/
def baseChangeEquiv :
    ℍ[F,a,b] ⊗[F] R ≃ₐ[R] ℍ[R,algebraMap F R a,algebraMap F R b] := by
  refine AlgEquiv.ofAlgHom (baseChangeHom F a b R) (baseChangeBasis F a b R).liftHom
    (QuaternionAlgebra.hom_ext ?_ ?_) (AlgHom.ext fun z => ?_)
  · have hl : (baseChangeBasis F a b R).lift ⟨0, 1, 0, 0⟩
        = (⟨0, 1, 0, 0⟩ : ℍ[F,a,b]) ⊗ₜ[F] (1 : R) := by
      simp [QuaternionAlgebra.Basis.lift, baseChangeBasis, Algebra.smul_def,
        Algebra.TensorProduct.right_algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    show baseChangeHom F a b R ((baseChangeBasis F a b R).lift ⟨0, 1, 0, 0⟩) = _
    rw [hl, baseChangeHom_tmul]
    simp [mapRingHom, QuaternionAlgebra.Basis.self]
  · have hl : (baseChangeBasis F a b R).lift ⟨0, 0, 1, 0⟩
        = (⟨0, 0, 1, 0⟩ : ℍ[F,a,b]) ⊗ₜ[F] (1 : R) := by
      simp [QuaternionAlgebra.Basis.lift, baseChangeBasis, Algebra.smul_def,
        Algebra.TensorProduct.right_algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    show baseChangeHom F a b R ((baseChangeBasis F a b R).lift ⟨0, 0, 1, 0⟩) = _
    rw [hl, baseChangeHom_tmul]
    simp [mapRingHom, QuaternionAlgebra.Basis.self]
  · induction z using TensorProduct.induction_on with
    | zero =>
      show (baseChangeBasis F a b R).liftHom (baseChangeHom F a b R 0) = 0
      simp [QuaternionAlgebra.Basis.lift_zero]
    | tmul x r =>
      show (baseChangeBasis F a b R).liftHom (baseChangeHom F a b R (x ⊗ₜ[F] r)) = x ⊗ₜ[F] r
      rw [baseChangeHom_tmul, map_smul, liftHom_mapRingHom, Algebra.smul_def,
        Algebra.TensorProduct.right_algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
      simp
    | add u v hu hv =>
      show (baseChangeBasis F a b R).liftHom (baseChangeHom F a b R (u + v)) = u + v
      rw [map_add, map_add,
        show (baseChangeBasis F a b R).liftHom (baseChangeHom F a b R u) = u from hu,
        show (baseChangeBasis F a b R).liftHom (baseChangeHom F a b R v) = v from hv]

variable {F a b R}

@[simp]
theorem baseChangeEquiv_tmul (x : ℍ[F,a,b]) (r : R) :
    baseChangeEquiv F a b R (x ⊗ₜ r) = r • mapRingHom (algebraMap F R) a b x :=
  baseChangeHom_tmul F a b R x r

variable {R' : Type*} [CommRing R'] [Algebra F R']

/-- **Naturality of the base change** in the coefficient ring, as one equation of coordinate
tuples: the two sides live in quaternion algebras whose parameters are only propositionally
equal. -/
theorem baseChangeEquiv_map (f : R →ₐ[F] R') (x : ℍ[F,a,b] ⊗[F] R) :
    equivTuple _ _ _
        (baseChangeEquiv F a b R' (Algebra.TensorProduct.map (AlgHom.id F ℍ[F,a,b]) f x)) =
      f ∘ equivTuple _ _ _ (baseChangeEquiv F a b R x) := by
  induction x using TensorProduct.induction_on with
  | zero => funext i; fin_cases i <;> simp
  | tmul y r =>
    rw [Algebra.TensorProduct.map_tmul, baseChangeEquiv_tmul, baseChangeEquiv_tmul]
    funext i
    fin_cases i <;>
      simp [mapRingHom, Algebra.smul_def, AlgHom.commutes]
  | add u v hu hv =>
    funext i
    have hu' := congrFun hu i
    have hv' := congrFun hv i
    rw [map_add, map_add]
    fin_cases i <;>
      simp_all [Function.comp, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]

variable (F a b R)

/-- **The reduced norm of `ℍ[F,a,b] ⊗_F R`**, valued in `R`. -/
def nrdBaseChange : ℍ[F,a,b] ⊗[F] R →*₀ R :=
  (nrd (R := R)).comp (baseChangeEquiv F a b R).toAlgHom.toRingHom.toMonoidWithZeroHom

variable {F a b R}

@[simp]
theorem nrdBaseChange_tmul_one (x : ℍ[F,a,b]) :
    nrdBaseChange F a b R (x ⊗ₜ 1) = algebraMap F R (nrd x) := by
  show nrd (baseChangeEquiv F a b R (x ⊗ₜ (1 : R))) = _
  rw [baseChangeEquiv_tmul, one_smul, nrd_mapRingHom]

/-- The reduced norm commutes with a change of coefficients. -/
theorem nrdBaseChange_map (f : R →ₐ[F] R') (x : ℍ[F,a,b] ⊗[F] R) :
    nrdBaseChange F a b R' (Algebra.TensorProduct.map (AlgHom.id F ℍ[F,a,b]) f x) =
      f (nrdBaseChange F a b R x) := by
  have h := baseChangeEquiv_map f x
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp [Function.comp] at h0 h1 h2 h3
  show nrd (baseChangeEquiv F a b R' _) = f (nrd (baseChangeEquiv F a b R x))
  rw [nrd_apply, nrd_apply]
  simp only [h0, h1, h2, h3, map_add, map_sub, map_mul, map_pow, AlgHom.commutes]

/-- The reduced norm is continuous for the module topology. -/
theorem continuous_nrdBaseChange [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (nrdBaseChange F a b R) := by
  set L : (ℍ[F,a,b] ⊗[F] R) →ₗ[R] (Fin 4 → R) :=
    (QuaternionAlgebra.linearEquivTuple (algebraMap F R a) 0 (algebraMap F R b)).toLinearMap ∘ₗ
      (baseChangeEquiv F a b R).toLinearMap with hL
  have hco : ∀ i, Continuous fun x : ℍ[F,a,b] ⊗[F] R => L x i := fun i =>
    (continuous_apply i).comp (IsModuleTopology.continuous_of_linearMap L)
  have heq : ∀ x, nrdBaseChange F a b R x
      = L x 0 ^ 2 - algebraMap F R a * L x 1 ^ 2 - algebraMap F R b * L x 2 ^ 2
        + algebraMap F R a * algebraMap F R b * L x 3 ^ 2 := by
    intro x
    show nrd (baseChangeEquiv F a b R x) = _
    rw [nrd_apply]
    simp [hL]
  have hfun : (fun x => nrdBaseChange F a b R x) = fun x =>
      L x 0 ^ 2 - algebraMap F R a * L x 1 ^ 2 - algebraMap F R b * L x 2 ^ 2
        + algebraMap F R a * algebraMap F R b * L x 3 ^ 2 := funext heq
  show Continuous fun x => nrdBaseChange F a b R x
  rw [hfun]
  exact ((((hco 0).pow 2).sub (continuous_const.mul ((hco 1).pow 2))).sub
    (continuous_const.mul ((hco 2).pow 2))).add (continuous_const.mul ((hco 3).pow 2))

/-- **The reduced norm is the determinant of every `R`-linear splitting** of the base change. -/
theorem det_eq_nrdBaseChange (θ : ℍ[F,a,b] ⊗[F] R ≃ₐ[R] Matrix (Fin 2) (Fin 2) R)
    (h2 : IsUnit (2 : R)) (ha : IsUnit (algebraMap F R a)) (hb : IsUnit (algebraMap F R b))
    (x : ℍ[F,a,b] ⊗[F] R) : (θ x).det = nrdBaseChange F a b R x := by
  have hφ := det_map_eq_nrd (θ.toAlgHom.comp (baseChangeEquiv F a b R).symm.toAlgHom) h2
    (by simpa using ha) (by simpa using hb) (baseChangeEquiv F a b R x)
  simpa [nrdBaseChange] using hφ

end QuaternionAlgebra
