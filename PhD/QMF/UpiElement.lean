/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.QMF.Quaternionic
import PhD.QMF.FLTstuff.Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Tactic.NoncommRing

/-!
# The standard `U_ϖ` Hecke element

Construction of the adelic element realising the standard `U_ϖ` operator on quaternionic
modular forms [Buzzard, *Eigenvarieties*, §9 p. 69]: the unit of `(D ⊗[F] 𝔸_F^∞)ˣ` whose
component at the distinguished place `v` is the `Σ₀(γ)`-element `Sigma0.eta = (1 0; 0 ϖ)`
and whose components at all other places are `1`.

* `QMF.singleₗ` — the `F`-linear inclusion `F_v →ₗ[F] 𝔸_F^∞` (zero at the other places).
* `QMF.iotaV` — the induced map `D ⊗[F] F_v →ₗ[F] D ⊗[F] 𝔸_F^∞`; it is multiplicative
  (`iotaV_mul`) and is split by the `v`-component map (`toLocal_iotaV`).
* `QMF.etaAdelic` — the unit `1 + ι_v(η - 1)`, with inverse `1 + ι_v(η⁻¹ - 1)`.
* `QMF.heckeUpi` — the Hecke operator `[UηU]` at `η = etaAdelic`, Buzzard's `U_ϖ`.
-/

open scoped TensorProduct Pointwise
open IsDedekindDomain NumberField

namespace QMF

variable (F : Type*) [Field F] [NumberField F]
variable (D : Type*) [Ring D] [Algebra F D]
variable (v : HeightOneSpectrum (RingOfIntegers F))

/-! ## The single-place inclusion `F_v → 𝔸_F^∞` -/

section Single

attribute [local instance] Classical.decEq

/-- The single-place inclusion as an additive monoid homomorphism into the finite adele
ring (the ported `RestrictedProduct.singleAddMonoidHom`, retyped at `FiniteAdeleRing`). -/
private noncomputable def singleHom :
    v.adicCompletion F →+ FiniteAdeleRing (RingOfIntegers F) F :=
  RestrictedProduct.singleAddMonoidHom (fun w ↦ w.adicCompletion F)
    (B := fun w ↦ w.adicCompletionIntegers F) v

/-- The inclusion of the local field at `v` into the finite adele ring, sending `a` to the
adele with component `a` at `v` and `0` at every other place, as an `F`-linear map. -/
noncomputable def singleₗ :
    v.adicCompletion F →ₗ[F] FiniteAdeleRing (RingOfIntegers F) F :=
  { singleHom F v with
    map_smul' := fun c a ↦ by
      have h1 : singleHom F v (c • a) =
          singleHom F v (algebraMap F (v.adicCompletion F) c * a) := by
        rw [Algebra.smul_def]
      have h2 : c • singleHom F v a =
          algebraMap F (FiniteAdeleRing (RingOfIntegers F) F) c * singleHom F v a :=
        Algebra.smul_def c (singleHom F v a)
      have h3 : singleHom F v (algebraMap F (v.adicCompletion F) c * a) =
          algebraMap F (FiniteAdeleRing (RingOfIntegers F) F) c * singleHom F v a :=
        RestrictedProduct.mul_single (fun w ↦ w.adicCompletionIntegers F) v a
          (algebraMap F (FiniteAdeleRing (RingOfIntegers F) F) c)
      exact h1.trans (h3.trans h2.symm) }

/-- The component of `singleₗ F v a` at `v` is `a`. -/
@[simp] lemma singleₗ_apply_same (a : v.adicCompletion F) : singleₗ F v a v = a :=
  RestrictedProduct.single_eq_same (fun w ↦ w.adicCompletionIntegers F) v a

/-- The component of `singleₗ F v a` at any place `w ≠ v` is `0`. -/
@[simp] lemma singleₗ_apply_ne (a : v.adicCompletion F)
    {w : HeightOneSpectrum (RingOfIntegers F)} (hw : w ≠ v) : singleₗ F v a w = 0 :=
  RestrictedProduct.single_eq_of_ne (fun w ↦ w.adicCompletionIntegers F) a hw

private lemma adele_mul_apply (x y : FiniteAdeleRing (RingOfIntegers F) F)
    (w : HeightOneSpectrum (RingOfIntegers F)) : (x * y) w = x w * y w := rfl

/-- `singleₗ` is multiplicative: componentwise, both sides are `a * b` at `v` and `0`
elsewhere. -/
lemma singleₗ_mul_singleₗ (a b : v.adicCompletion F) :
    singleₗ F v a * singleₗ F v b = singleₗ F v (a * b) := by
  refine FiniteAdeleRing.ext F fun w ↦ ?_
  rcases eq_or_ne w v with rfl | hw
  · rw [adele_mul_apply, singleₗ_apply_same, singleₗ_apply_same, singleₗ_apply_same]
  · rw [adele_mul_apply, singleₗ_apply_ne F v a hw, singleₗ_apply_ne F v b hw,
      singleₗ_apply_ne F v (a * b) hw, mul_zero]

end Single

/-- `evalAlgHom F w` is evaluation of a finite adele at the place `w`. -/
@[simp] lemma evalAlgHom_apply (w : HeightOneSpectrum (RingOfIntegers F))
    (x : FiniteAdeleRing (RingOfIntegers F) F) : evalAlgHom F w x = x w := rfl

/-! ## The single-place inclusion `D ⊗ F_v → D ⊗ 𝔸_F^∞` -/

/-- The `F`-linear inclusion `D ⊗[F] F_v →ₗ[F] D ⊗[F] 𝔸_F^∞` induced by `singleₗ` on the
second factor; it is not unital, but it is multiplicative (`iotaV_mul`). -/
noncomputable def iotaV :
    (D ⊗[F] v.adicCompletion F) →ₗ[F] D ⊗[F] FiniteAdeleRing (RingOfIntegers F) F :=
  LinearMap.lTensor D (singleₗ F v)

/-- `iotaV` on pure tensors. -/
@[simp] lemma iotaV_tmul (d : D) (a : v.adicCompletion F) :
    iotaV F D v (d ⊗ₜ[F] a) = d ⊗ₜ[F] singleₗ F v a :=
  LinearMap.lTensor_tmul D (singleₗ F v) d a

/-- Key lemma: `iotaV` respects multiplication. -/
lemma iotaV_mul (x y : D ⊗[F] v.adicCompletion F) :
    iotaV F D v x * iotaV F D v y = iotaV F D v (x * y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, zero_mul]
  | tmul d a =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, mul_zero]
    | tmul e b =>
      simp only [iotaV_tmul, Algebra.TensorProduct.tmul_mul_tmul, singleₗ_mul_singleₗ]
    | add y₁ y₂ h₁ h₂ => simp only [map_add, mul_add, h₁, h₂]
  | add x₁ x₂ h₁ h₂ => simp only [map_add, add_mul, h₁, h₂]

/-- `toLocal` on pure tensors: evaluate the adelic factor at `v`. -/
@[simp] lemma toLocal_tmul (d : D) (x : FiniteAdeleRing (RingOfIntegers F) F) :
    toLocal F D v (d ⊗ₜ[F] x) = d ⊗ₜ[F] evalAlgHom F v x :=
  Algebra.TensorProduct.map_tmul (AlgHom.id F D) (evalAlgHom F v) d x

/-- Key lemma: the `v`-component map `toLocal` splits `iotaV`. -/
lemma toLocal_iotaV (x : D ⊗[F] v.adicCompletion F) :
    toLocal F D v (iotaV F D v x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul d a => rw [iotaV_tmul, toLocal_tmul, evalAlgHom_apply, singleₗ_apply_same]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- If `a * b = 1` in `D ⊗[F] F_v`, then `(1 + ι_v(a - 1)) * (1 + ι_v(b - 1)) = 1` in
`D ⊗[F] 𝔸_F^∞`: single-place perturbations of `1` multiply like the local elements. -/
lemma one_add_iotaV_mul (a b : D ⊗[F] v.adicCompletion F) (hab : a * b = 1) :
    (1 + iotaV F D v (a - 1)) * (1 + iotaV F D v (b - 1)) = 1 := by
  have expand : (1 + iotaV F D v (a - 1)) * (1 + iotaV F D v (b - 1)) =
      1 + (iotaV F D v (a - 1) + iotaV F D v (b - 1) +
        iotaV F D v (a - 1) * iotaV F D v (b - 1)) := by
    noncomm_ring
  have collapse : a - 1 + (b - 1) + (a - 1) * (b - 1) = a * b - 1 := by noncomm_ring
  rw [expand, iotaV_mul, ← map_add, ← map_add, collapse, hab, sub_self, map_zero, add_zero]

/-! ## The `U_ϖ` element -/

variable [RigidificationAt F D v]
variable (γ : WithZero (Multiplicative ℤ)) (hγ : γ < 1)

/-- The matrix `(1 0; 0 ϖ)` of `Sigma0.eta`, pulled back to `D ⊗[F] F_v` through the
rigidification. -/
noncomputable def etaTensor (ϖ : v.adicCompletion F) : D ⊗[F] v.adicCompletion F :=
  (RigidificationAt.equiv (F := F) (D := D) (v := v)).symm (Matrix.of ![![1, 0], ![0, ϖ]])

/-- `etaTensor` is the pullback of the underlying matrix of the `Σ₀(γ)`-element
`Sigma0.eta`. -/
lemma etaTensor_eq (ϖ : v.adicCompletion F) (hϖ : Valued.v ϖ ≤ 1) (hϖ0 : ϖ ≠ 0) :
    etaTensor F D v ϖ =
      (RigidificationAt.equiv (F := F) (D := D) (v := v)).symm
        (Sigma0.eta γ hγ ϖ hϖ hϖ0).1 :=
  rfl

/-- The pullback to `D ⊗[F] F_v` of the explicit inverse matrix `(1 0; 0 ϖ⁻¹)`. -/
noncomputable def etaTensorInv (ϖ : v.adicCompletion F) : D ⊗[F] v.adicCompletion F :=
  (RigidificationAt.equiv (F := F) (D := D) (v := v)).symm (Matrix.of ![![1, 0], ![0, ϖ⁻¹]])

/-- `etaTensor` and `etaTensorInv` multiply to `1` (for `ϖ ≠ 0`). -/
lemma etaTensor_mul_etaTensorInv (ϖ : v.adicCompletion F) (hϖ0 : ϖ ≠ 0) :
    etaTensor F D v ϖ * etaTensorInv F D v ϖ = 1 := by
  have h : (Matrix.of ![![1, 0], ![0, ϖ]] : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) *
      Matrix.of ![![1, 0], ![0, ϖ⁻¹]] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ hϖ0]
  show (RigidificationAt.equiv (F := F) (D := D) (v := v)).symm
        (Matrix.of ![![1, 0], ![0, ϖ]]) *
      (RigidificationAt.equiv (F := F) (D := D) (v := v)).symm
        (Matrix.of ![![1, 0], ![0, ϖ⁻¹]]) = 1
  rw [← map_mul, h, map_one]

/-- `etaTensorInv` and `etaTensor` multiply to `1` (for `ϖ ≠ 0`). -/
lemma etaTensorInv_mul_etaTensor (ϖ : v.adicCompletion F) (hϖ0 : ϖ ≠ 0) :
    etaTensorInv F D v ϖ * etaTensor F D v ϖ = 1 := by
  have h : (Matrix.of ![![1, 0], ![0, ϖ⁻¹]] : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) *
      Matrix.of ![![1, 0], ![0, ϖ]] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ hϖ0]
  show (RigidificationAt.equiv (F := F) (D := D) (v := v)).symm
        (Matrix.of ![![1, 0], ![0, ϖ⁻¹]]) *
      (RigidificationAt.equiv (F := F) (D := D) (v := v)).symm
        (Matrix.of ![![1, 0], ![0, ϖ]]) = 1
  rw [← map_mul, h, map_one]

/-- The standard `U_ϖ` Hecke element of `(D ⊗[F] 𝔸_F^∞)ˣ`: the unit `1 + ι_v(η - 1)` whose
`v`-component is `η = (1 0; 0 ϖ)` and whose components at all other places are `1`. -/
noncomputable def etaAdelic (ϖ : v.adicCompletion F) (hϖ0 : ϖ ≠ 0) : Dfx F D :=
  ⟨1 + iotaV F D v (etaTensor F D v ϖ - 1),
    1 + iotaV F D v (etaTensorInv F D v ϖ - 1),
    one_add_iotaV_mul F D v _ _ (etaTensor_mul_etaTensorInv F D v ϖ hϖ0),
    one_add_iotaV_mul F D v _ _ (etaTensorInv_mul_etaTensor F D v ϖ hϖ0)⟩

/-- `toMatrix` computes as the rigidification applied to the `v`-component. -/
lemma toMatrix_apply (u : Dfx F D) :
    toMatrix F D v u =
      RigidificationAt.equiv (F := F) (D := D) (v := v) (toLocal F D v ↑u) := rfl

/-- The `v`-component matrix of `etaAdelic` is exactly the underlying matrix of
`Sigma0.eta`. -/
lemma toMatrix_etaAdelic (ϖ : v.adicCompletion F) (hϖ : Valued.v ϖ ≤ 1) (hϖ0 : ϖ ≠ 0) :
    toMatrix F D v (etaAdelic F D v ϖ hϖ0) = (Sigma0.eta γ hγ ϖ hϖ hϖ0).1 := by
  have h1 : toLocal F D v ↑(etaAdelic F D v ϖ hϖ0) = etaTensor F D v ϖ := by
    show toLocal F D v (1 + iotaV F D v (etaTensor F D v ϖ - 1)) = etaTensor F D v ϖ
    rw [map_add, map_one, toLocal_iotaV]
    abel
  rw [toMatrix_apply, h1]
  show RigidificationAt.equiv (F := F) (D := D) (v := v)
      ((RigidificationAt.equiv (F := F) (D := D) (v := v)).symm
        (Matrix.of ![![1, 0], ![0, ϖ]])) =
    Matrix.of ![![1, 0], ![0, ϖ]]
  exact AlgEquiv.apply_symm_apply _ _

/-- `etaAdelic` lies in the wild-level monoid `Δ`: its `v`-component lies in `Σ₀(γ)`. -/
lemma etaAdelic_mem_levelMonoid (ϖ : v.adicCompletion F) (hϖ : Valued.v ϖ ≤ 1)
    (hϖ0 : ϖ ≠ 0) : etaAdelic F D v ϖ hϖ0 ∈ levelMonoid F D v γ hγ := by
  refine Submonoid.mem_comap.mpr ?_
  rw [toMatrix_etaAdelic F D v γ hγ ϖ hϖ hϖ0]
  exact (Sigma0.eta γ hγ ϖ hϖ hϖ0).2

variable {R : Type*} [CommRing R] [Algebra (v.adicCompletion F) R]
variable (n : ℕ) (ν : Sigma0 (v.adicCompletion F) γ hγ →* Rˣ)

/-- The standard `U_ϖ` Hecke operator on quaternionic modular forms of weight `(n, ν)` and
level `U`: the double-coset operator `[UηU]` of `QMF.heckeOperator` specialised at
`η = etaAdelic`, whose `v`-component is `(1 0; 0 ϖ)` — in our left-handed convention this
is the analogue of Buzzard's `η = (π 0; 0 1)` [Buzzard, *Eigenvarieties*, §9 p. 69]. -/
noncomputable def heckeUpi (U : Subgroup (Dfx F D))
    (hU : (U : Set (Dfx F D)) ⊆ levelMonoid F D v γ hγ)
    (ϖ : v.adicCompletion F) (hϖ : Valued.v ϖ ≤ 1) (hϖ0 : ϖ ≠ 0)
    (h : (QuotientGroup.mk '' ((U : Set (Dfx F D)) * {etaAdelic F D v ϖ hϖ0}) :
      Set (Dfx F D ⧸ U)).Finite) :
    Space F D v γ hγ n ν U hU →ₗ[R] Space F D v γ hγ n ν U hU :=
  heckeOperator F D v γ hγ n ν U hU (etaAdelic_mem_levelMonoid F D v γ hγ ϖ hϖ hϖ0) h

end QMF
