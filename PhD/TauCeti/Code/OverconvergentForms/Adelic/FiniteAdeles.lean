/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# The finite adeles of a number field: the topological facts Layer 0 consumes

The seam with the global-number-fields roadmap. For a number field `F` the local integers `𝒪_v` are
compact and open, the integral adeles `∏_v 𝒪_v` are a compact open subring of `𝔸_F^f`, and `𝔸_F^f`
is a locally compact, Hausdorff, totally disconnected topological ring. Mathlib has the openness
(`Valued.isOpen_valuationSubring`), the criterion
`compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField`, and
`RestrictedProduct.locallyCompactSpace_of_group`; the finiteness of the residue field of the
completion, and everything about `∏_v 𝒪_v`, is stated here.

[Voi21, 27.6.6]: "The `S`-finite adele ring has a compact open subring `Ô := ∏_{v ∉ S} O_v`."

## Main definitions

* `IsDedekindDomain.FiniteAdeleRing.integralAdeles`: the subring `∏_v 𝒪_v` of `𝔸_F^f`.

## Main results

* `NumberField.finite_residueField_adicCompletionIntegers`: the residue field of `𝒪_v` is finite.
* `NumberField.compactSpace_adicCompletionIntegers`: `𝒪_v` is compact;
  `NumberField.locallyCompactSpace_adicCompletion`: `F_v` is locally compact.
* `IsDedekindDomain.FiniteAdeleRing.exists_integralAdeles_eq`: every family of local integers is
  an integral adele.
* `IsDedekindDomain.FiniteAdeleRing.isCompact_integralAdeles`, `isOpen_integralAdeles`.
* `NumberField.locallyCompactSpace_finiteAdeleRing`, `t2Space_finiteAdeleRing`,
  `totallyDisconnectedSpace_finiteAdeleRing`.

## Implementation notes

The coercion `F → F_v` is a structure literal (`{ toCompletion := … }`), not `algebraMap`, and
`adicCompletionIntegers` is a non-reducible `def` for `Valued.v.valuationSubring`, so
`valuedAdicCompletion_eq_valuation(')` and `Valuation.mem_maximalIdeal_iff` are used in term mode,
where the unfolding is automatic. Mathlib's compactness criterion is stated for `𝒪[K]`
(`Valued.integer`, a `Subring`); its hypotheses transfer to the `ValuationSubring` by defeq, except
`CompleteSpace`, which comes from closedness.

Roadmap: §0.2.1, §0.2.3. Tau Ceti home: the global-number-fields tree,
`TauCeti/NumberTheory/NumberField/FiniteAdeleRing.lean`.
-/

open IsDedekindDomain NumberField
open scoped WithZero Valued algebraMap RestrictedProduct

noncomputable section

namespace NumberField

variable (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/-- The residue field of the completion at a finite place of a number field is finite: the
residue map `𝓞 F → 𝒪_v / 𝔪_v` is surjective, by the density of `F` in `F_v`, and its kernel is the
maximal ideal `v`, of finite index. -/
instance finite_residueField_adicCompletionIntegers :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := by
  classical
  have hfin : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  have key : ∀ x : v.adicCompletionIntegers F, ∃ a : 𝓞 F,
      Valued.v ((algebraMap (𝓞 F) (v.adicCompletion F) a) - (x : v.adicCompletion F)) < 1 := by
    intro x
    have hnhds : {z : v.adicCompletion F | Valued.v (z - (x : v.adicCompletion F)) < 1}
        ∈ nhds (x : v.adicCompletion F) := by
      rw [Valued.mem_nhds]
      exact ⟨1, by simp⟩
    obtain ⟨z, hz, y, rfl⟩ := mem_closure_iff_nhds.mp
      (HeightOneSpectrum.denseRange_algebraMap F (v := v) (x : v.adicCompletion F)) _ hnhds
    rw [Set.mem_ofPred_eq] at hz
    have hx1 : Valued.v ((x : v.adicCompletion F)) ≤ 1 := x.2
    have hy1 : v.valuation F y ≤ 1 := by
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      have h2 := Valuation.map_add Valued.v
        ((algebraMap F (v.adicCompletion F) y) - (x : v.adicCompletion F))
        ((x : v.adicCompletion F))
      rw [sub_add_cancel] at h2
      exact h2.trans (max_le hz.le hx1)
    obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hy1 1
    refine ⟨a, ?_⟩
    have e : (algebraMap (𝓞 F) (v.adicCompletion F) a) - algebraMap F (v.adicCompletion F) y
        = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a - y) := by
      rw [map_sub, ← IsScalarTower.algebraMap_apply]
    have hsub : Valued.v ((algebraMap (𝓞 F) (v.adicCompletion F) a)
        - algebraMap F (v.adicCompletion F) y) < 1 := by
      rw [e]
      exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) _).trans_lt
        (by simpa using ha)
    have h3 := Valuation.map_add Valued.v
      ((algebraMap (𝓞 F) (v.adicCompletion F) a) - algebraMap F (v.adicCompletion F) y)
      (algebraMap F (v.adicCompletion F) y - (x : v.adicCompletion F))
    rw [sub_add_sub_cancel] at h3
    exact lt_of_le_of_lt h3 (max_lt hsub hz)
  refine Finite.of_surjective (α := 𝓞 F ⧸ v.asIdeal)
    (Ideal.Quotient.lift v.asIdeal ((IsLocalRing.residue (v.adicCompletionIntegers F)).comp
      (algebraMap (𝓞 F) (v.adicCompletionIntegers F))) ?_) ?_
  · intro a ha
    rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
    exact (Valuation.mem_maximalIdeal_iff _ _).mpr
      ((HeightOneSpectrum.valuedAdicCompletion_eq_valuation (v := v) a).trans_lt
        ((HeightOneSpectrum.valuation_lt_one_iff_mem v a).mpr ha))
  · intro w
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective w
    obtain ⟨a, ha⟩ := key x
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Ideal.Quotient.lift_mk, RingHom.comp_apply, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff]
    exact (Valuation.mem_maximalIdeal_iff _ _).mpr ha

/-- **The local integers are compact.** -/
instance compactSpace_adicCompletionIntegers : CompactSpace (v.adicCompletionIntegers F) := by
  have hres : Finite 𝓀[v.adicCompletion F] :=
    finite_residueField_adicCompletionIntegers F v
  have hdvr : IsDiscreteValuationRing 𝒪[v.adicCompletion F] :=
    inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F))
  have hcomp : CompleteSpace 𝒪[v.adicCompletion F] := by
    have hcl : IsClosed (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
      (v.adicCompletionIntegers F).toSubring.toAddSubgroup.isClosed_of_isOpen
        (Valued.isOpen_valuationSubring _)
    exact hcl.completeSpace_coe
  open Valued.integer in
  exact (compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    (K := v.adicCompletion F)).mpr ⟨hcomp, hdvr, hres⟩

theorem isCompact_adicCompletionIntegers :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers F v)

theorem isOpen_adicCompletionIntegers :
    IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  Valued.isOpen_valuationSubring _

/-- The completion at a finite place of a number field is locally compact. -/
instance locallyCompactSpace_adicCompletion : LocallyCompactSpace (v.adicCompletion F) := by
  have : WeaklyLocallyCompactSpace (v.adicCompletion F) :=
    ⟨fun x => open Pointwise in
      ⟨x +ᵥ (v.adicCompletionIntegers F : Set (v.adicCompletion F)),
        (isCompact_adicCompletionIntegers F v).vadd x,
        ((isOpen_adicCompletionIntegers F v).vadd x).mem_nhds
          (Set.mem_vadd_set.mpr ⟨0, (v.adicCompletionIntegers F).zero_mem, by simp⟩)⟩⟩
  infer_instance

end NumberField

namespace IsDedekindDomain.FiniteAdeleRing

variable (F : Type*) [Field F] [NumberField F]

/-- **The integral adeles** `∏_v 𝒪_v`, a subring of the finite adeles. -/
def integralAdeles : Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {x | ∀ v, x v ∈ v.adicCompletionIntegers F}
  mul_mem' hx hy v := mul_mem (hx v) (hy v)
  one_mem' _ := one_mem _
  add_mem' hx hy v := add_mem (hx v) (hy v)
  zero_mem' _ := zero_mem _
  neg_mem' hx v := neg_mem (hx v)

variable {F}

theorem mem_integralAdeles_iff {x : FiniteAdeleRing (𝓞 F) F} :
    x ∈ integralAdeles F ↔ ∀ v, x v ∈ v.adicCompletionIntegers F :=
  Iff.rfl

variable (F)

/-- Every family of local integers is an integral adele. -/
theorem exists_integralAdeles_eq
    (z : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) :
    ∃ x ∈ integralAdeles F, ∀ v, x v = z v :=
  ⟨RestrictedProduct.structureMap _ _ _ z, fun v => (z v).2, fun _ => rfl⟩

/-- **The integral adeles are compact**: the image of the compact product `∏_v 𝒪_v` under the
structure map of the restricted product. -/
theorem isCompact_integralAdeles :
    IsCompact (integralAdeles F : Set (FiniteAdeleRing (𝓞 F) F)) := by
  have hemb := RestrictedProduct.isOpenEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => NumberField.isOpen_adicCompletionIntegers F v)
  haveI : ∀ v : HeightOneSpectrum (𝓞 F),
      CompactSpace (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => inferInstanceAs (CompactSpace (v.adicCompletionIntegers F))
  have hcpt := isCompact_range hemb.continuous
  rw [RestrictedProduct.range_structureMap] at hcpt
  exact hcpt

/-- **The integral adeles are open**, because each `𝒪_v` is open in `F_v`. -/
theorem isOpen_integralAdeles :
    IsOpen (integralAdeles F : Set (FiniteAdeleRing (𝓞 F) F)) := by
  have hopen := (RestrictedProduct.isOpenEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => NumberField.isOpen_adicCompletionIntegers F v)).isOpen_range
  rw [RestrictedProduct.range_structureMap] at hopen
  exact hopen

end IsDedekindDomain.FiniteAdeleRing

namespace NumberField

variable (F : Type*) [Field F] [NumberField F]

/-- **The finite adeles are locally compact.** -/
instance locallyCompactSpace_finiteAdeleRing :
    LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := by
  haveI : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v => isOpen_adicCompletionIntegers F v⟩
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F) :=
    fun v => compactSpace_adicCompletionIntegers F v
  exact inferInstanceAs (LocallyCompactSpace
    (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))

/-- The finite adeles are Hausdorff: the coordinates are continuous and jointly injective. -/
instance t2Space_finiteAdeleRing : T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space
    (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))

/-- **The finite adeles are totally disconnected.** -/
instance totallyDisconnectedSpace_finiteAdeleRing :
    TotallyDisconnectedSpace (FiniteAdeleRing (𝓞 F) F) := by
  refine ⟨isTotallyDisconnected_of_image
    (f := fun x : Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]
      => (⇑x : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F))
    RestrictedProduct.continuous_coe.continuousOn DFunLike.coe_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

end NumberField
