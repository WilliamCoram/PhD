/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.QMF.Slash.«03_HeckeMonoid»
import PhD.QMF.«03_Quaternionic»
import PhD.QMF.FLTstuff.Hacks.RightActionInstances
import PhD.QMF.FLTstuff.Mathlib.NumberTheory.NumberField.FiniteAdeleRing
import PhD.QMF.FLTstuff.NumberField.Completion.Finite
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Compact open levels

[Buzzard, *Eigenvarieties*, §9 p. 68]: "we say that a **compact open** subgroup `U ⊆ D_f^×` has
wild level `≥ π^t` if …", and p. 69: "decompose `UηU = ∐_i U x_i` (a finite union)".  The
finiteness of that decomposition is automatic at a compact open level
(`AbstractHeckeOperatorSlash.finite_image_doubleCoset_of_isOpen_of_isCompact`), so what an
application needs is that its level *is* compact open.

The route (no restricted products needed): the integral order of `D` at all finite places is
the image of a compact set under a continuous map, hence compact; the unit group of a compact
multiplicatively-closed set is compact because `Units.embedProduct` is a closed embedding.

The topology on `D ⊗[F] 𝔸_F^∞` is the `𝔸_F^∞`-module topology, taken from the
`TensorProduct.RightActions` scope (`PhD/QMF/FLTstuff/Hacks/RightActionInstances.lean`) — the
same choice FLT makes, so downstream files must open that scope rather than mathlib's
`Algebra.TensorProduct.rightAlgebra`, which would give a second (propositionally equal but not
syntactically equal) `𝔸`-module structure.

## Main declarations

* `Units.isCompact_of_isCompact` — `{u : Rˣ | ↑u ∈ s ∧ ↑u⁻¹ ∈ s}` is compact for compact `s`.
* `QMF.isCompact_integralTensor` — the integral order `𝒪 ⊗ ℤ̂ ⊆ D ⊗ 𝔸_F^∞` is compact.
-/

open scoped TensorProduct TensorProduct.RightActions
open IsDedekindDomain NumberField

/-- **Units of an open set form an open set of units**: both `u ↦ u` and `u ↦ u⁻¹` are
continuous on `Rˣ`. -/
theorem Units.isOpen_of_isOpen {R : Type*} [TopologicalSpace R] [Monoid R]
    {s : Set R} (hs : IsOpen s) :
    IsOpen {u : Rˣ | (u : R) ∈ s ∧ ((u⁻¹ : Rˣ) : R) ∈ s} :=
  (hs.preimage Units.continuous_val).inter (hs.preimage Units.continuous_coe_inv)

/-- **Units of a compact set form a compact set of units**: `Units.embedProduct` is a closed
embedding into `R × Rᵐᵒᵖ` (`Units.isClosedEmbedding_embedProduct`), and the set in question is
the preimage of `s ×ˢ op '' s`. -/
theorem Units.isCompact_of_isCompact {R : Type*} [TopologicalSpace R] [Monoid R]
    [ContinuousMul R] [T1Space R] {s : Set R} (hs : IsCompact s) :
    IsCompact {u : Rˣ | (u : R) ∈ s ∧ ((u⁻¹ : Rˣ) : R) ∈ s} := by
  have hset : {u : Rˣ | (u : R) ∈ s ∧ ((u⁻¹ : Rˣ) : R) ∈ s}
      = Units.embedProduct R ⁻¹' (s ×ˢ (MulOpposite.unop ⁻¹' s)) := rfl
  have himg : (MulOpposite.unop ⁻¹' s) = MulOpposite.op '' s :=
    Set.ext fun x => ⟨fun hx => ⟨MulOpposite.unop x, hx, rfl⟩, by rintro ⟨y, hy, rfl⟩; exact hy⟩
  rw [hset]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hs.prod (himg ▸ hs.image MulOpposite.continuous_op))

namespace QMF

variable (F : Type*) [Field F] [NumberField F]
variable (D : Type*) [Ring D] [Algebra F D] [Module.Finite F D]

/-- The integral order of `D` over the integral finite adeles: the image of
`(integral adeles)^n` under a chosen `F`-basis of `D`. -/
noncomputable def integralTensor (b : Module.Basis (Fin (Module.finrank F D)) F D) :
    Set (D ⊗[F] FiniteAdeleRing (RingOfIntegers F) F) :=
  (fun a : Fin (Module.finrank F D) → FiniteAdeleRing (RingOfIntegers F) F =>
      ∑ i, (b i) ⊗ₜ[F] a i) ''
    {a | ∀ i, a i ∈ IsDedekindDomain.FiniteAdeleRing.integralAdeles (RingOfIntegers F) F}

/-- **The integral order is compact**: it is the image of the compact set
`(integralAdeles)^n` (`FiniteAdeleRing.isCompact_integralAdeles`) under a continuous map. -/
theorem isCompact_integralTensor
    (b : Module.Basis (Fin (Module.finrank F D)) F D) :
    IsCompact (integralTensor F D b) := by
  -- The source is a finite product of copies of the (compact) integral adeles.
  have hpi : {a : Fin (Module.finrank F D) → FiniteAdeleRing (RingOfIntegers F) F |
      ∀ i, a i ∈ IsDedekindDomain.FiniteAdeleRing.integralAdeles (RingOfIntegers F) F}
      = Set.univ.pi fun _ =>
        IsDedekindDomain.FiniteAdeleRing.integralAdeles (RingOfIntegers F) F := by
    ext a
    exact ⟨fun h i _ => h i, fun h i => h i (Set.mem_univ i)⟩
  -- The map is continuous: `d ⊗ₜ x = x • (d ⊗ₜ 1)` for the right `𝔸`-action.
  haveI : ContinuousAdd (D ⊗[F] FiniteAdeleRing (RingOfIntegers F) F) :=
    IsModuleTopology.toContinuousAdd (FiniteAdeleRing (RingOfIntegers F) F) _
  have hcont : Continuous fun a : Fin (Module.finrank F D) → FiniteAdeleRing (RingOfIntegers F) F =>
      ∑ i, (b i) ⊗ₜ[F] a i := by
    refine continuous_finsetSum _ fun i _ => ?_
    have hsmul : (fun a : Fin (Module.finrank F D) → FiniteAdeleRing (RingOfIntegers F) F =>
        (b i) ⊗ₜ[F] a i)
        = fun a => (a i) • ((b i) ⊗ₜ[F] (1 : FiniteAdeleRing (RingOfIntegers F) F)) := by
      funext a
      rw [Algebra.smul_def, TensorProduct.RightActions.algebraMap_eval,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [hsmul]
    exact (continuous_apply i).smul
      (continuous_const (y := (b i) ⊗ₜ[F] (1 : FiniteAdeleRing (RingOfIntegers F) F)))
  rw [integralTensor, hpi]
  exact (isCompact_univ_pi fun _ =>
    IsDedekindDomain.FiniteAdeleRing.isCompact_integralAdeles F).image hcont

/-! ### Continuity of the local components

`D ⊗ 𝔸_f → D ⊗ F_v` is *not* an `𝔸_f`-linear map — it is semilinear over the evaluation
`𝔸_f → F_v`.  That is exactly the shape of `IsModuleTopology.continuous_of_linearMapₛₗ`, so no
tensor-specific continuity API (an `lTensor` companion of FLT's `ContinuousLinearMap.rTensor'`)
is needed: the source carries the `𝔸_f`-module topology and the target is a topological
`F_v`-module. -/

/-- `toLocal` as a semilinear map over the evaluation `𝔸_F^∞ → F_v`. -/
noncomputable def toLocalₛₗ (v : HeightOneSpectrum (RingOfIntegers F)) :
    (D ⊗[F] FiniteAdeleRing (RingOfIntegers F) F) →ₛₗ[(evalAlgHom F v).toRingHom]
      (D ⊗[F] v.adicCompletion F) where
  toFun := toLocal F D v
  map_add' _ _ := map_add _ _ _
  map_smul' a x := by
    have hsrc : ∀ (b : FiniteAdeleRing (RingOfIntegers F) F) (d : D)
        (z : FiniteAdeleRing (RingOfIntegers F) F), b • (d ⊗ₜ[F] z) = d ⊗ₜ[F] (b * z) := by
      intro b d z
      simp [TensorProduct.RightActions.smul_def, TensorProduct.smul_tmul']
    have htgt : ∀ (b : v.adicCompletion F) (d : D) (z : v.adicCompletion F),
        b • (d ⊗ₜ[F] z) = d ⊗ₜ[F] (b * z) := by
      intro b d z
      simp [TensorProduct.RightActions.smul_def, TensorProduct.smul_tmul']
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul d z =>
        have hmap : ∀ (e : D) (y : FiniteAdeleRing (RingOfIntegers F) F),
            toLocal F D v (e ⊗ₜ[F] y) = e ⊗ₜ[F] (evalAlgHom F v y) := fun _ _ => rfl
        rw [hsrc, hmap, hmap, map_mul, htgt]
        rfl
    | add y z hy hz => rw [smul_add, map_add, map_add, hy, hz, smul_add]

omit [Module.Finite F D] in
@[simp] theorem toLocalₛₗ_apply (v : HeightOneSpectrum (RingOfIntegers F))
    (x : D ⊗[F] FiniteAdeleRing (RingOfIntegers F) F) :
    toLocalₛₗ F D v x = toLocal F D v x := rfl

/-- **The local component map is continuous** for the module topologies. -/
theorem continuous_toLocal (v : HeightOneSpectrum (RingOfIntegers F)) :
    Continuous (toLocal F D v) :=
  IsModuleTopology.continuous_of_linearMapₛₗ
    (RestrictedProduct.continuous_eval v) (toLocalₛₗ F D v)

/-- The integral adeles are open (the restricted product's structure map is an open
embedding, the local integers being open). -/
theorem isOpen_integralAdeles :
    IsOpen (IsDedekindDomain.FiniteAdeleRing.integralAdeles (RingOfIntegers F) F :
      Set (FiniteAdeleRing (RingOfIntegers F) F)) :=
  (RestrictedProduct.isOpenEmbedding_structureMap
    (NumberField.isOpenAdicCompletionIntegers F)).isOpen_range

/-! ### Continuity of the matrix component

`QMF.RigidificationAt` records only the *`F`*-algebra equivalence `D ⊗[F] F_v ≅ M₂(F_v)`, which
is not enough for a topological argument: continuity for the module topologies needs
`F_v`-linearity.  Rather than strengthen the class (which would force one fixed
`Algebra F_v (D ⊗[F] F_v)` instance through the whole framework), we record the missing half as
a `Prop`-valued mixin.  It says exactly that the rigidification carries the scalars `1 ⊗ z` to
the scalar matrices, and every concrete rigidification proves it in one line — the fork's
`theta` is built from a `K₃`-algebra map, so its instance is `theta_one_tmul`. -/

/-- **The rigidification is linear over the completion**: `θ(1 ⊗ z)` is the scalar matrix `z`.
Equivalently (see `continuous_rigidificationEquiv`) `θ` is `F_v`-linear, hence continuous. -/
class RigidificationAt.IsCompletionLinear (v : HeightOneSpectrum (RingOfIntegers F))
    [RigidificationAt F D v] : Prop where
  /-- The rigidification sends `1 ⊗ z` to the scalar matrix `z`. -/
  equiv_one_tmul : ∀ z : v.adicCompletion F,
    RigidificationAt.equiv (F := F) (D := D) (v := v) ((1 : D) ⊗ₜ[F] z)
      = algebraMap (v.adicCompletion F) (Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) z

variable (v : HeightOneSpectrum (RingOfIntegers F)) [RigidificationAt F D v]

/-- The rigidification as an `F_v`-linear map (`RigidificationAt.IsCompletionLinear`). -/
noncomputable def rigidificationₗ [RigidificationAt.IsCompletionLinear F D v] :
    (D ⊗[F] v.adicCompletion F) →ₗ[v.adicCompletion F]
      Matrix (Fin 2) (Fin 2) (v.adicCompletion F) where
  toFun := RigidificationAt.equiv (F := F) (D := D) (v := v)
  map_add' _ _ := map_add _ _ _
  map_smul' z x := by
    rw [Algebra.smul_def, map_mul, TensorProduct.RightActions.algebraMap_eval,
      RigidificationAt.IsCompletionLinear.equiv_one_tmul, RingHom.id_apply, Algebra.smul_def]

/-- **The rigidification is continuous** for the module topologies. -/
theorem continuous_rigidificationEquiv [RigidificationAt.IsCompletionLinear F D v] :
    Continuous (RigidificationAt.equiv (F := F) (D := D) (v := v)) :=
  IsModuleTopology.continuous_of_linearMap (rigidificationₗ F D v)

/-- **The matrix component of an adelic unit depends continuously on the unit**: the composite
`u ↦ θ(toLocal u)` of three continuous maps. -/
theorem continuous_toMatrix [RigidificationAt.IsCompletionLinear F D v] :
    Continuous (toMatrix F D v) :=
  (continuous_rigidificationEquiv F D v).comp
    ((continuous_toLocal F D v).comp Units.continuous_val)

omit [Module.Finite F D] in
/-- The matrix component of a unit is invertible, so the `det ≠ 0` clause of `Sigma0'` is
automatic on `Dfx`. -/
theorem toMatrix_det_ne_zero (u : Dfx F D) : (toMatrix F D v u).det ≠ 0 := by
  have h : IsUnit (toMatrix F D v u) :=
    Units.isUnit (Units.map ((RigidificationAt.equiv (F := F) (D := D)
      (v := v)).toAlgHom.comp (toLocal F D v)).toMonoidHom u)
  exact ((Matrix.isUnit_iff_isUnit_det _).mp h).ne_zero

end QMF
