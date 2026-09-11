/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.QMF.Quaternionic
import PhD.QMF.UpiElement
import PhD.QMF.Slash.WeightModule
import PhD.QMF.Slash.HeckeMatrix

/-!
# Quaternionic modular forms with the classical right slash

Right-handed mirror of `PhD/QMF/Quaternionic.lean` (+ the `etaAdelic` layer of
`PhD/QMF/UpiElement.lean`): the specialisation of the slash theory to a quaternion
algebra `D` over a number field `F`, in the classical convention of
[Buzzard, *Eigenvarieties*, §9] — the space `S^D_{k,w}(U) = L(U, L_{n,v})` with
`L_{n,v}` a *right* `Mₜ`-module and `f∣u` the classical slash.

The convention-neutral plumbing (`Dfx`, `globalUnits`, `toMatrix`,
`RigidificationAt`) is reused from the left files; only the handed objects are
mirrored:

* `levelMonoid'` — Buzzard's wild-level monoid via `Σ₀'` (his `Mₜ` on the nose);
* `levelMonoid'ToSigma0'` — the corestriction of the `v`-component map;
* the right slash of `levelMonoid'` on `WeightModule R n ν` (through the
  corestriction);
* `etaAdelic'` — the thesis-form Hecke element with `v`-component `(ϖ 0; 0 1)`;
* `SpaceSlash` — quaternionic modular forms with the classical right slash;
* `spaceSlash_eq_space` — the FLT-facing agreement corollary: under the pointwise
  `detNorm`-dictionary on the level group, the right-slash space *equals* the
  left-action space of `PhD/QMF/Quaternionic.lean`.
-/

open scoped TensorProduct Pointwise QMF
open IsDedekindDomain NumberField RightSlashAction AbstractHeckeOperatorSlash

namespace QMF

variable (F : Type*) [Field F] [NumberField F]
variable (D : Type*) [Ring D] [Algebra F D]
variable (v : HeightOneSpectrum (RingOfIntegers F)) [RigidificationAt F D v]
variable (γ : WithZero (Multiplicative ℤ)) (hγ : γ < 1)

/-- Buzzard's wild-level monoid in his own convention: adelic units whose
`v`-component lies in `Σ₀'(γ)` (= `Mₜ`, [*Eigenvarieties*, §9 p. 68]).  Right-handed
mirror of `QMF.levelMonoid`. -/
noncomputable def levelMonoid' : Submonoid (Dfx F D) :=
  (Sigma0' (v.adicCompletion F) γ hγ).comap (toMatrix F D v)

/-- The corestriction `Δ' →* Σ₀'(γ)` of the `v`-component map. -/
noncomputable def levelMonoid'ToSigma0' :
    levelMonoid' F D v γ hγ →* Sigma0' (v.adicCompletion F) γ hγ where
  toFun g := ⟨toMatrix F D v g.1, g.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp)

variable {R : Type*} [CommRing R] [Algebra (v.adicCompletion F) R]
variable (n : ℕ) (ν : Sigma0 (v.adicCompletion F) γ hγ →* Rˣ)

/-- The wild-level monoid slashes the weight module through its `v`-component. -/
noncomputable instance : RightSlashAction (levelMonoid' F D v γ hγ) (WeightModule R n ν) where
  slash P δ := P ∣ₛ (levelMonoid'ToSigma0' F D v γ hγ δ)
  zero_slash δ := RightSlashAction.zero_slash _
  slash_one P := by
    show P ∣ₛ (levelMonoid'ToSigma0' F D v γ hγ 1) = P
    rw [map_one, RightSlashAction.slash_one]
  slash_mul P δ₁ δ₂ := by
    show P ∣ₛ (levelMonoid'ToSigma0' F D v γ hγ (δ₁ * δ₂)) = _
    rw [map_mul, RightSlashAction.slash_mul]
  add_slash P Q δ := RightSlashAction.add_slash _ _ _

instance : SMulSlashClass R (levelMonoid' F D v γ hγ) (WeightModule R n ν) where
  smul_slash r P δ := by
    show (r • P) ∣ₛ (levelMonoid'ToSigma0' F D v γ hγ δ)
      = r • (P ∣ₛ (levelMonoid'ToSigma0' F D v γ hγ δ))
    exact SMulSlashClass.smul_slash r P _

/-- The thesis-form `η`-tensor: `(ϖ 0; 0 1)` read back through the rigidification.
Mirror of `QMF.etaTensor` (`(1 0; 0 ϖ)`). -/
noncomputable def etaTensor' (ϖ : v.adicCompletion F) : D ⊗[F] v.adicCompletion F :=
  (RigidificationAt.equiv (F := F) (D := D) (v := v)).symm
    (Matrix.of ![![ϖ, 0], ![0, 1]])

/-- The inverse `η`-tensor `(ϖ⁻¹ 0; 0 1)`. -/
noncomputable def etaTensorInv' (ϖ : v.adicCompletion F) : D ⊗[F] v.adicCompletion F :=
  (RigidificationAt.equiv (F := F) (D := D) (v := v)).symm
    (Matrix.of ![![ϖ⁻¹, 0], ![0, 1]])

lemma etaTensor'_mul_etaTensorInv' (ϖ : v.adicCompletion F) (hϖ0 : ϖ ≠ 0) :
    etaTensor' F D v ϖ * etaTensorInv' F D v ϖ = 1 := by
  have h : (Matrix.of ![![ϖ, 0], ![0, 1]] :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) * Matrix.of ![![ϖ⁻¹, 0], ![0, 1]]
      = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ hϖ0]
  show (RigidificationAt.equiv (F := F) (D := D) (v := v)).symm _ *
      (RigidificationAt.equiv (F := F) (D := D) (v := v)).symm _ = 1
  rw [← map_mul, h, map_one]

lemma etaTensorInv'_mul_etaTensor' (ϖ : v.adicCompletion F) (hϖ0 : ϖ ≠ 0) :
    etaTensorInv' F D v ϖ * etaTensor' F D v ϖ = 1 := by
  have h : (Matrix.of ![![ϖ⁻¹, 0], ![0, 1]] :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) * Matrix.of ![![ϖ, 0], ![0, 1]]
      = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ hϖ0]
  show (RigidificationAt.equiv (F := F) (D := D) (v := v)).symm _ *
      (RigidificationAt.equiv (F := F) (D := D) (v := v)).symm _ = 1
  rw [← map_mul, h, map_one]

/-- The thesis-form `U_ϖ` Hecke element: the adelic unit whose `v`-component is
`η = (ϖ 0; 0 1)` [Jacobs `η₃ = (3 0; 0 1)`, p. 20] and whose components at all other
places are `1`.  Mirror of `QMF.etaAdelic` (component `(1 0; 0 ϖ)`). -/
noncomputable def etaAdelic' (ϖ : v.adicCompletion F) (hϖ0 : ϖ ≠ 0) : Dfx F D :=
  ⟨1 + iotaV F D v (etaTensor' F D v ϖ - 1),
    1 + iotaV F D v (etaTensorInv' F D v ϖ - 1),
    one_add_iotaV_mul F D v _ _ (etaTensor'_mul_etaTensorInv' F D v ϖ hϖ0),
    one_add_iotaV_mul F D v _ _ (etaTensorInv'_mul_etaTensor' F D v ϖ hϖ0)⟩

/-- The `v`-component matrix of `etaAdelic'` is the underlying matrix of the
thesis-form `Sigma0'.eta`. -/
lemma toMatrix_etaAdelic' (ϖ : v.adicCompletion F) (hϖ : Valued.v ϖ ≤ 1) (hϖ0 : ϖ ≠ 0) :
    toMatrix F D v (etaAdelic' F D v ϖ hϖ0) = (Sigma0'.eta γ hγ ϖ hϖ hϖ0).1 := by
  have h1 : toLocal F D v ↑(etaAdelic' F D v ϖ hϖ0) = etaTensor' F D v ϖ := by
    show toLocal F D v (1 + iotaV F D v (etaTensor' F D v ϖ - 1)) = etaTensor' F D v ϖ
    rw [map_add, map_one, toLocal_iotaV]
    abel
  rw [toMatrix_apply, h1]
  show RigidificationAt.equiv (F := F) (D := D) (v := v)
      ((RigidificationAt.equiv (F := F) (D := D) (v := v)).symm
        (Matrix.of ![![ϖ, 0], ![0, 1]])) = Matrix.of ![![ϖ, 0], ![0, 1]]
  simp

lemma etaAdelic'_mem_levelMonoid' (ϖ : v.adicCompletion F) (hϖ : Valued.v ϖ ≤ 1)
    (hϖ0 : ϖ ≠ 0) : etaAdelic' F D v ϖ hϖ0 ∈ levelMonoid' F D v γ hγ := by
  refine Submonoid.mem_comap.mpr ?_
  rw [toMatrix_etaAdelic' F D v γ hγ ϖ hϖ hϖ0]
  exact (Sigma0'.eta γ hγ ϖ hϖ hϖ0).2

/-- Away from `v`, `etaAdelic'` has component `1`. -/
@[simp] lemma toLocal_etaAdelic'_ne (ϖ : v.adicCompletion F) (hϖ0 : ϖ ≠ 0)
    {w : HeightOneSpectrum (RingOfIntegers F)} (hw : w ≠ v) :
    toLocal F D w ((etaAdelic' F D v ϖ hϖ0 : Dfx F D) :
      D ⊗[F] FiniteAdeleRing (RingOfIntegers F) F) = 1 := by
  show toLocal F D w (1 + iotaV F D v _) = 1
  rw [map_add, map_one, toLocal_iotaV_ne _ _ _ hw, add_zero]

/-- Away from `v`, the inverse of `etaAdelic'` has component `1`. -/
@[simp] lemma toLocal_etaAdelic'_inv_ne (ϖ : v.adicCompletion F) (hϖ0 : ϖ ≠ 0)
    {w : HeightOneSpectrum (RingOfIntegers F)} (hw : w ≠ v) :
    toLocal F D w (((etaAdelic' F D v ϖ hϖ0)⁻¹ : Dfx F D) :
      D ⊗[F] FiniteAdeleRing (RingOfIntegers F) F) = 1 := by
  show toLocal F D w (1 + iotaV F D v _) = 1
  rw [map_add, map_one, toLocal_iotaV_ne _ _ _ hw, add_zero]

/-- The space of quaternionic modular forms of weight `(n, ν)` and level `U` **with the
classical right slash**: Buzzard's `S^D_{k,w}(U) = L(U, L_{n,v})` [*Eigenvarieties*,
§9 p. 70] with `L_{n,v}` a right `Mₜ`-module, as in the source.  Right-handed mirror
of `QMF.Space`. -/
noncomputable def SpaceSlash (U : Subgroup (Dfx F D))
    (hU : (U : Set (Dfx F D)) ⊆ levelMonoid' F D v γ hγ) :
    Submodule R (AutomorphicFunction (Dfx F D) (globalUnits F D) (WeightModule R n ν)) :=
  AutomorphicFunction.levelSubmoduleSlash R U hU

/-- The Hecke operator `[UηU]` on right-slash quaternionic modular forms
(`f∣[UηU] = ∑ᵢ f∣xᵢ`, [Buz07 §9 p. 69] verbatim through
`AbstractHeckeOperatorSlash.heckeOperatorSlash`). -/
noncomputable def heckeOperatorQSlash (U : Subgroup (Dfx F D))
    (hU : (U : Set (Dfx F D)) ⊆ levelMonoid' F D v γ hγ) {η : Dfx F D}
    (hη : η ∈ levelMonoid' F D v γ hγ)
    (h : (((Quotient.mk'' : Dfx F D → RightCosets U) ''
        ({η} * (U : Set (Dfx F D)))) : Set (RightCosets U)).Finite) :
    slashFixedPointsOfLE (U := U) R
        (AutomorphicFunction (Dfx F D) (globalUnits F D) (WeightModule R n ν)) hU →ₗ[R]
      slashFixedPointsOfLE (U := U) R
        (AutomorphicFunction (Dfx F D) (globalUnits F D) (WeightModule R n ν)) hU :=
  heckeOperatorSlash R hU hU hη h

/-- **The FLT-facing agreement corollary**: under the pointwise dictionary between the
coefficient slash and the coefficient left action on `U`-elements, the right-slash
space *equals* the left-action space of `PhD/QMF/Quaternionic.lean`.  Instantiation of
the abstract seam theorem (`levelSubmoduleSlash_eq_levelSubmodule`); the hypothesis is
discharged per weight module via the `detNorm`-identity (board decomposition, T-CRIT
resolution). -/
theorem spaceSlash_eq_space (U : Subgroup (Dfx F D))
    (hU' : (U : Set (Dfx F D)) ⊆ levelMonoid' F D v γ hγ)
    (hU : (U : Set (Dfx F D)) ⊆ levelMonoid F D v γ hγ)
    (hcompat : ∀ u : U, ∀ P : WeightModule R n ν,
      P ∣ₛ (⟨u.1, hU' u.2⟩ : levelMonoid' F D v γ hγ)
        = (⟨(u⁻¹ : U).1, hU (u⁻¹ : U).2⟩ : levelMonoid F D v γ hγ) • P) :
    SpaceSlash F D v γ hγ n ν U hU' = Space F D v γ hγ n ν U hU :=
  AutomorphicFunction.levelSubmoduleSlash_eq_levelSubmodule R hU' hU hcompat

end QMF
