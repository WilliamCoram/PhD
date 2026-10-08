/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.OverconvergentForms.Adelic.RightBaseChange
import PhD.TauCeti.Code.OverconvergentForms.Adelic.FiniteAdeles

/-!
# The adelic group `D_f^× = (D ⊗_F 𝔸_F^f)^×`

For a finite-dimensional algebra `D` over a number field `F`: the ring `D_f := D ⊗_F 𝔸_F^f` with the
`𝔸_F^f`-module topology, its unit group `D_f^×` with the topology of `Units.embedProduct`, and the
diagonal embedding `D^× → D_f^×`. `D_f` is a locally compact, Hausdorff, totally disconnected
topological ring and `D_f^×` a locally compact, totally disconnected topological group.

[Buz07, §9, p. 68]: "Define `𝔸_{F,f}` to be the finite adeles of `F` and `D_f := D ⊗_F 𝔸_{F,f}`."

## Main definitions

* `AdelicAlgebra.Df`, `AdelicAlgebra.Dfx`: the ring `D ⊗[F] 𝔸_F^f` and its unit group.
* `AdelicAlgebra.unitsIncl`: the diagonal embedding `Dˣ →* D_f^×`; `AdelicAlgebra.globalUnits`.

## Main results

* `AdelicAlgebra.unitsIncl_injective`.
* `AdelicAlgebra.locallyCompactSpace_Df`, `AdelicAlgebra.locallyCompactSpace_Dfx` and the
  Hausdorff and totally disconnected companions.
* `Units.isOpen_of_isOpen`, `Units.isCompact_of_isCompact`: the unit group of an open (compact)
  multiplicatively defined subset is open (compact).

Roadmap: §0.2.1. Tau Ceti home: `TauCeti/NumberTheory/AdelicAlgebra/Basic.lean`.
-/

open scoped TensorProduct
open IsDedekindDomain NumberField

noncomputable section

section Units

variable {M : Type*} [Monoid M] [TopologicalSpace M]

/-- The units whose value and inverse lie in an open set form an open set. -/
theorem Units.isOpen_of_isOpen {S : Set M} (hS : IsOpen S) :
    IsOpen {u : Mˣ | (u : M) ∈ S ∧ ((u⁻¹ : Mˣ) : M) ∈ S} :=
  (hS.preimage Units.continuous_val).inter (hS.preimage Units.continuous_coe_inv)

/-- The units whose value and inverse lie in a compact set form a compact set: `Units.embedProduct`
is a closed embedding. -/
theorem Units.isCompact_of_isCompact [T1Space M] [ContinuousMul M] {S : Set M}
    (hS : IsCompact S) : IsCompact {u : Mˣ | (u : M) ∈ S ∧ ((u⁻¹ : Mˣ) : M) ∈ S} := by
  have h := (Units.isClosedEmbedding_embedProduct (α := M)).isCompact_preimage
    (hS.prod (hS.image MulOpposite.continuous_op))
  convert h using 1
  ext u
  simp [Units.embedProduct]

end Units

namespace AdelicAlgebra

open scoped RightAlgebra

variable (F : Type*) [Field F] [NumberField F] (D : Type*) [Ring D] [Algebra F D]

/-- **The finite-adelic points** `D_f := D ⊗_F 𝔸_F^f` of `D`. -/
abbrev Df : Type _ := D ⊗[F] FiniteAdeleRing (𝓞 F) F

/-- **The adelic group** `D_f^× = (D ⊗_F 𝔸_F^f)^×`. -/
abbrev Dfx : Type _ := (Df F D)ˣ

/-- The diagonal embedding `D → D_f`, `x ↦ x ⊗ 1`. -/
def incl : D →ₐ[F] Df F D := Algebra.TensorProduct.includeLeft

/-- **The diagonal embedding** `D^× → D_f^×`. -/
def unitsIncl : Dˣ →* Dfx F D := Units.map (incl F D).toMonoidHom

/-- The subgroup `D^× ⊆ D_f^×`. -/
def globalUnits : Subgroup (Dfx F D) := (unitsIncl F D).range

variable {F D}

@[simp]
theorem incl_apply (x : D) : incl F D x = x ⊗ₜ 1 := rfl

@[simp]
theorem coe_unitsIncl (x : Dˣ) : ((unitsIncl F D x : Dfx F D) : Df F D) = (x : D) ⊗ₜ 1 := rfl

variable (F D)

omit [Ring D] [Algebra F D] in
private theorem nonempty_heightOneSpectrum : Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨M, hM.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)⟩⟩

omit [Ring D] [Algebra F D] in
private theorem algebraMap_finiteAdeleRing_injective :
    Function.Injective (algebraMap F (FiniteAdeleRing (𝓞 F) F)) := by
  obtain ⟨v⟩ := nonempty_heightOneSpectrum F
  intro x y hxy
  exact (algebraMap F (v.adicCompletion F)).injective
    (congrArg (fun z : FiniteAdeleRing (𝓞 F) F => z v) hxy)

/-- `D → D_f` is injective: `D` is free over `F` and `F → 𝔸_F^f` is injective. -/
theorem incl_injective : Function.Injective (incl F D) :=
  Algebra.TensorProduct.includeLeft_injective (algebraMap_finiteAdeleRing_injective F)

/-- **`D^× → D_f^×` is an injective group homomorphism.** -/
theorem unitsIncl_injective : Function.Injective (unitsIncl F D) :=
  Units.map_injective (incl_injective F D)

section Topology

variable [Module.Finite F D]

/-- **`D_f` is locally compact**: it is homeomorphic to a finite power of `𝔸_F^f`. -/
instance locallyCompactSpace_Df : LocallyCompactSpace (Df F D) :=
  (rightCoordsL (R := FiniteAdeleRing (𝓞 F) F)
    (Module.Free.chooseBasis F D)).toHomeomorph.isClosedEmbedding.locallyCompactSpace

instance t2Space_Df : T2Space (Df F D) :=
  (rightCoordsL (R := FiniteAdeleRing (𝓞 F) F)
    (Module.Free.chooseBasis F D)).toHomeomorph.isEmbedding.t2Space

/-- **`D_f` is totally disconnected.** -/
instance totallyDisconnectedSpace_Df : TotallyDisconnectedSpace (Df F D) :=
  ⟨isTotallyDisconnected_of_image
    (rightCoordsL (R := FiniteAdeleRing (𝓞 F) F)
      (Module.Free.chooseBasis F D)).continuous.continuousOn
    (rightCoordsL (R := FiniteAdeleRing (𝓞 F) F) (Module.Free.chooseBasis F D)).injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

/-- **`D_f^×` is locally compact**: a closed subspace of `D_f × D_f` through
`Units.embedProduct`. -/
instance locallyCompactSpace_Dfx : LocallyCompactSpace (Dfx F D) :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

/-- **`D_f^×` is totally disconnected.** -/
instance totallyDisconnectedSpace_Dfx : TotallyDisconnectedSpace (Dfx F D) :=
  ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

example : IsTopologicalGroup (Dfx F D) := inferInstance

end Topology

end AdelicAlgebra
