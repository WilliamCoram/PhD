/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.Topology.Algebra.Group.Quotient
import PhD.TauCeti.Code.RigidAnalyticGeometry.NormedQuotient
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Rueckert
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.StrictlyClosed

/-!
# Affinoid algebras

A `K`-algebra `A` is *affinoid* if it is a quotient of a Tate algebra `Tₙ = K⟨X₁, …, Xₙ⟩`
(BGR 6.1.1/1; Bosch 1.4, Definition 1). Following convention 3 of the roadmap, the definition is
purely ring-theoretic: a presentation `α : Tₙ ↠ A` as `K`-algebras. The *residue norm* of a
presentation is the quotient norm of `Tₙ ⧸ ker α`, which Mathlib supplies for closed ideals
(`Ideal.Quotient.normedCommRing`); that every ideal of `Tₙ` is closed is Layer 0
(`MvPowerSeries.Restricted.isClosed_ideal`). Layer 1 proves that every `K`-algebra homomorphism
between affinoid algebras is continuous for any residue norms (`Affinoid/Continuity.lean`), so the
choice of presentation is immaterial for the topology.

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, §1.1.1–1.1.2. Tau Ceti home:
`TauCeti/RingTheory/Affinoid/Basic.lean`.

## Main definitions and results

* `IsAffinoidAlgebra K A` — `A` is a quotient of some Tate algebra `Tₙ`.
* The residue-norm instances on `TateAlgebra K n ⧸ I`: `NormedCommRing`, `NormedAlgebra K`,
  `CompleteSpace`, `IsUltrametricDist`, and `NormOneClass` for `I ≠ ⊤` (BGR 6.1.1, the opening
  paragraph).
* `Affinoid.TateAlgebra.norm_quotient_mk_mem_range_norm` (Layer 0): residue norms take values in
  `‖K‖` (BGR 6.1.1/2).
* `IsAffinoidAlgebra.isNoetherianRing`, `IsAffinoidAlgebra.isJacobsonRing`,
  `IsAffinoidAlgebra.quotient` — BGR 6.1.1/3.
* `Affinoid.TateAlgebra.isClosed_ideal_quotient` — every ideal of `Tₙ ⧸ I` is closed for the
  residue norm (BGR 6.1.1/3, "or simply from the closedness of ideals in `Tₙ`").
-/

open MvPowerSeries MvPowerSeries.Restricted

namespace MvPowerSeries.Restricted

variable {R σ : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] {c : σ → ℝ}
  [Fact (∀ i, 0 < c i)]

/-- Quotients of restricted power series by ideals are complete, as a shortcut instance: Mathlib's
`Submodule.Quotient.completeSpace` does not fire through the opaque `Restricted` type synonym (its
`[Ring R] [Module R M]` arguments are found along `instRingRestricted`, while the ideal's module
structure is spelled through the `NormedCommRing` instance, and the two do not unify at instance
transparency), so the quotient-group form is recorded directly. -/
instance instCompleteSpaceQuotient (I : Ideal (Restricted R c)) :
    CompleteSpace (Restricted R c ⧸ I) :=
  QuotientAddGroup.completeSpace_left _ I.toAddSubgroup

end MvPowerSeries.Restricted

namespace Affinoid

/-! ### Residue norms on quotients of the Tate algebra -/

namespace TateAlgebra

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] {n : ℕ}
  (I : Ideal (TateAlgebra K n))

/-- Every ideal of the Tate algebra is closed (Layer 0), as an instance so that Mathlib's
residue-norm instances on `Tₙ ⧸ I` fire. Source: BGR 5.2.7/2; Bosch 1.3/8. -/
instance instIsClosed : IsClosed (I : Set (TateAlgebra K n)) :=
  isClosed_ideal I

noncomputable example : NormedCommRing (TateAlgebra K n ⧸ I) := inferInstance
noncomputable example : NormedAlgebra K (TateAlgebra K n ⧸ I) := inferInstance
example : CompleteSpace (TateAlgebra K n ⧸ I) := inferInstance
example : IsUltrametricDist (TateAlgebra K n ⧸ I) := inferInstance

/-- The residue norm of a proper quotient of the Tate algebra has `‖1‖ = 1`. Source: BGR 6.1.1
(the residue norm is a `K`-algebra norm), via `Ideal.Quotient.normOneClass_of_ne_top`. -/
theorem normOneClass_quotient (hI : I ≠ ⊤) : NormOneClass (TateAlgebra K n ⧸ I) :=
  Ideal.Quotient.normOneClass_of_ne_top I hI

/-- The residue epimorphism `Tₙ → Tₙ ⧸ I` is contractive. Source: BGR 6.1.1 ("The residue
epimorphism `Tₙ → Tₙ/𝔞` is contractive (hence continuous) and open"). -/
theorem norm_quotient_mk_le (f : TateAlgebra K n) : ‖Ideal.Quotient.mk I f‖ ≤ ‖f‖ :=
  Ideal.Quotient.norm_mk_le I f

/-- The residue norm is attained: `‖f̄‖ = ‖f - a₀‖` for a nearest point `a₀ ∈ I` (strict
closedness of ideals, Layer 0). Source: BGR 6.1.1/2 ("The assertion follows directly from
Corollary 5.2.7/8"). -/
theorem exists_norm_quotient_mk_eq (f : TateAlgebra K n) :
    ∃ a₀ ∈ I, ‖Ideal.Quotient.mk I f‖ = ‖f - a₀‖ := by
  obtain ⟨a₀, ha₀, hmin⟩ := exists_forall_norm_sub_le_ideal I f
  refine ⟨a₀, ha₀, ?_⟩
  have hmk : Ideal.Quotient.mk I f = Ideal.Quotient.mk I (f - a₀) := by
    rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.2 ha₀, sub_zero]
  rw [hmk]
  exact Ideal.Quotient.norm_mk_eq_norm_of_forall_le I fun a ha ↦ by
    rw [sub_sub]
    exact hmin (a₀ + a) (I.add_mem ha₀ ha)

/-- Every ideal of a quotient of the Tate algebra is closed for the residue norm: its preimage in
`Tₙ` is an ideal, hence closed, and the residue map is a quotient map. Source: BGR 6.1.1/3 ("The
closedness of any ideal `𝔞 ⊂ A` follows … simply from the closedness of ideals in `Tₙ`"). -/
theorem isClosed_ideal_quotient (J : Ideal (TateAlgebra K n ⧸ I)) :
    IsClosed (J : Set (TateAlgebra K n ⧸ I)) := by
  have h : IsClosed ((Ideal.Quotient.mk I) ⁻¹' (J : Set (TateAlgebra K n ⧸ I))) :=
    isClosed_ideal (J.comap (Ideal.Quotient.mk I))
  exact (QuotientAddGroup.isQuotientMap_mk I.toAddSubgroup).isCoinducing.isClosed_preimage.1 h

/-- The residue norm of `Tₙ ⧸ I` takes its values in `‖K‖`. Source: BGR 6.1.1/2. -/
theorem norm_quotient_mem_range_norm (x : TateAlgebra K n ⧸ I) :
    ‖x‖ ∈ Set.range (norm : K → ℝ) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact norm_quotient_mk_mem_range_norm I f

/-- Every nonzero element of `Tₙ ⧸ I` can be normed to length one by a scalar.
Source: BGR 6.1.1/2 ("each vector `≠ 0` in `A` can be normed to length 1 by multiplication with a
scalar"). -/
theorem exists_norm_smul_quotient_eq_one {x : TateAlgebra K n ⧸ I} (hx : x ≠ 0) :
    ∃ a : K, ‖a • x‖ = 1 := by
  obtain ⟨a, ha⟩ := norm_quotient_mem_range_norm I x
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  refine ⟨a⁻¹, ?_⟩
  rw [norm_smul, norm_inv, ha, inv_mul_cancel₀ hx0]

end TateAlgebra

end Affinoid

/-! ### Affinoid algebras -/

section IsAffinoidAlgebra

variable (K : Type*) [NormedField K] [IsUltrametricDist K]

open Affinoid in
/-- A `K`-algebra `A` is **affinoid** if it is a quotient of some Tate algebra `Tₙ`: there is a
surjective `K`-algebra homomorphism `Tₙ → A`. The definition is ring-theoretic (roadmap convention
3); the topology comes afterwards from a presentation, and is independent of it by BGR 6.1.3/1.
Source: BGR 6.1.1/1 ("A `k`-Banach algebra `A` is called affinoid … if there exists an integer
`n ≥ 0` and a continuous epimorphism `α : Tₙ → A`"); Bosch 1.4, Definition 1. -/
def IsAffinoidAlgebra (A : Type*) [CommRing A] [Algebra K A] : Prop :=
  ∃ (n : ℕ) (α : TateAlgebra K n →ₐ[K] A), Function.Surjective α

variable {K}

namespace IsAffinoidAlgebra

open Affinoid

variable {A B : Type*} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]

/-- The Tate algebras are affinoid. Source: BGR 6.1.1/1. -/
theorem tateAlgebra (n : ℕ) : IsAffinoidAlgebra K (TateAlgebra K n) :=
  ⟨n, AlgHom.id K _, Function.surjective_id⟩

/-- A surjective image of an affinoid algebra is affinoid. Source: BGR 6.1.1/3 ("`A/𝔞` is
`k`-affinoid, since `Tₙ → A → A/𝔞` is a continuous epimorphism"). -/
theorem of_surjective (hA : IsAffinoidAlgebra K A) (φ : A →ₐ[K] B) (hφ : Function.Surjective φ) :
    IsAffinoidAlgebra K B := by
  obtain ⟨n, α, hα⟩ := hA
  exact ⟨n, φ.comp α, hφ.comp hα⟩

/-- Quotients of affinoid algebras are affinoid. Source: BGR 6.1.1/3; Bosch 1.4, Prop. 2. -/
theorem quotient (hA : IsAffinoidAlgebra K A) (I : Ideal A) : IsAffinoidAlgebra K (A ⧸ I) :=
  hA.of_surjective (Ideal.Quotient.mkₐ K I) Ideal.Quotient.mk_surjective

/-- Affinoidness transports along `K`-algebra isomorphisms. -/
theorem of_algEquiv (hA : IsAffinoidAlgebra K A) (e : A ≃ₐ[K] B) : IsAffinoidAlgebra K B :=
  hA.of_surjective e.toAlgHom e.surjective

/-- Quotients of the Tate algebras are affinoid. Source: BGR 6.1.1 (the opening paragraph). -/
theorem tateAlgebra_quotient (n : ℕ) (I : Ideal (TateAlgebra K n)) :
    IsAffinoidAlgebra K (TateAlgebra K n ⧸ I) :=
  (tateAlgebra n).quotient I

/-- Every affinoid algebra is isomorphic to a quotient `Tₙ ⧸ I` of a Tate algebra; the ideal is
the kernel of the presentation. Source: BGR 6.1.1 ("`A` is isomorphic … to the residue algebra
`Tₙ/ker α`"). -/
theorem exists_algEquiv_quotient (hA : IsAffinoidAlgebra K A) :
    ∃ (n : ℕ) (I : Ideal (TateAlgebra K n)), Nonempty ((TateAlgebra K n ⧸ I) ≃ₐ[K] A) := by
  obtain ⟨n, α, hα⟩ := hA
  exact ⟨n, RingHom.ker α, ⟨Ideal.quotientKerAlgEquivOfSurjective hα⟩⟩

/-- **Affinoid algebras are noetherian.** Source: BGR 6.1.1/3 ("`A ≅ Tₙ/ker α` is a Noetherian
Jacobson ring since `Tₙ` is such a ring"); Bosch 1.4, Prop. 2. -/
theorem isNoetherianRing [CompleteSpace K] (hA : IsAffinoidAlgebra K A) : IsNoetherianRing A := by
  obtain ⟨n, α, hα⟩ := hA
  exact isNoetherianRing_of_surjective _ _ α.toRingHom hα

/-- **Affinoid algebras are Jacobson rings.** Source: BGR 6.1.1/3; Bosch 1.4, Prop. 2. -/
theorem isJacobsonRing [CompleteSpace K] (hA : IsAffinoidAlgebra K A) : IsJacobsonRing A := by
  obtain ⟨n, α, hα⟩ := hA
  exact isJacobsonRing_of_surjective ⟨α.toRingHom, hα⟩

/-- The zero algebra is affinoid (it is `T₀ ⧸ ⊤`). -/
theorem of_subsingleton [Subsingleton A] : IsAffinoidAlgebra K A :=
  ⟨0, { toFun := fun _ ↦ 0, map_one' := Subsingleton.elim _ _,
        map_mul' := fun _ _ ↦ Subsingleton.elim _ _, map_zero' := rfl,
        map_add' := fun _ _ ↦ Subsingleton.elim _ _, commutes' := fun _ ↦ Subsingleton.elim _ _ },
    fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

end IsAffinoidAlgebra

end IsAffinoidAlgebra
