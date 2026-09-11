/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Abstract Hecke operators for a submonoid of a group

Generalisation of FLT's `AbstractHeckeOperator` (FLT/AutomorphicForm/QuaternionAlgebra/
HeckeOperators/Abstract.lean, by Buzzard–Yang–Jasper) from an action of a *group* `G` to an
action of a *submonoid* `Δ ≤ G`.  This is forced by general (non-trivial) weight:
the coefficient module `A` only carries an action of the monoid `Mₜ ⊆ M₂(𝒪ₚ)` of
[Buzzard, *Eigenvarieties*, §9], pulled back to `Δ = {g : gₚ ∈ Mₜ}`; the Hecke element
`η` (e.g. `Uₚ`) has `ηₚ` non-invertible in `Mₜ`.

Setting: `G` a group, `Δ : Submonoid G`, `A` an additive monoid with `DistribMulAction Δ A`,
and subgroups `U, V ≤ G` whose underlying sets are contained in `Δ`.  For `g ∈ Δ` with
`UgV` a finite union of left `V`-cosets, we define `[UgV] : A^V →ₗ[R] A^U` by
`a ↦ ∑ᵢ gᵢ • a` over coset representatives `gᵢ ∈ UgV ⊆ Δ`.

Source (statement shape): Buzzard, *Eigenvarieties* (LMS 320, 2007), §9 p. 69:
"If `η ∈ D^×_f` and `ηₚ ∈ Mₜ` then one can define an endomorphism `[UηU]` of `L(U,A)` as
follows: decompose `UηU = ∐ᵢ U xᵢ` (a finite union) and define `f|[UηU] := ∑ᵢ f|xᵢ`."
-/

open MulAction
open scoped Pointwise

namespace AbstractHeckeOperator

section FixedPointsOfLE

variable {G : Type*} [Group G] {Δ : Submonoid G} {V : Subgroup G}

/-- The submodule of points of `A` fixed by a subgroup `V` of `G` contained in the acting
submonoid `Δ`; `V` acts through the inclusion `V → Δ`. -/
def fixedPointsOfLE (R A : Type*) [Semiring R] [AddCommMonoid A] [Module R A]
    [DistribMulAction Δ A] [SMulCommClass Δ R A] (hV : (V : Set G) ⊆ Δ) : Submodule R A where
  carrier := {a | ∀ v : V, (⟨v.1, hV v.2⟩ : Δ) • a = a}
  add_mem' ha hb v := by rw [smul_add, ha v, hb v]
  zero_mem' v := smul_zero _
  smul_mem' r a ha v := by rw [smul_comm, ha v]

/-- Membership in `fixedPointsOfLE` is being fixed by every element of `V`, acting
through `Δ`. -/
lemma mem_fixedPointsOfLE_iff {R A : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    [DistribMulAction Δ A] [SMulCommClass Δ R A] (hV : (V : Set G) ⊆ Δ) {a : A} :
    a ∈ fixedPointsOfLE R A hV ↔ ∀ v : V, (⟨v.1, hV v.2⟩ : Δ) • a = a := Iff.rfl

end FixedPointsOfLE

variable {G : Type*} [Group G] {Δ : Submonoid G} {A : Type*} [AddCommMonoid A]
  [DistribMulAction Δ A] {U V : Subgroup G} {g : G}

variable (R : Type*) [Semiring R] [Module R A] [SMulCommClass Δ R A]

/-- The double coset `U·g·V` is contained in `Δ` when `U`, `V` and `g` are. -/
lemma mul_singleton_mul_subset (hU : (U : Set G) ⊆ Δ) (hV : (V : Set G) ⊆ Δ)
    (hg : g ∈ Δ) : (U : Set G) * {g} * (V : Set G) ⊆ (Δ : Set G) :=
  Submonoid.mul_subset (Submonoid.mul_subset hU (Set.singleton_subset_iff.2 hg)) hV

/-- Canonical (`Quotient.out`) representatives of left-`V`-coset classes meeting `U·g`
lie in the double coset `U·g·V`. -/
lemma out_mem_mul_singleton_mul {x : G ⧸ V}
    (hx : x ∈ (QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ V))) :
    x.out ∈ (U : Set G) * {g} * (V : Set G) := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul V y
  exact hv ▸ Set.mul_mem_mul hy v.2

variable (hU : (U : Set G) ⊆ Δ) (hV : (V : Set G) ⊆ Δ) {g : G} (hg : g ∈ Δ)

/- Splitting a product inside `Δ` across the action (the proof components are
irrelevant, so any memberships may be used). -/
private lemma subtype_smul_mul (a : A) {y z : G} (hy : y ∈ Δ) (hz : z ∈ Δ)
    (hyz : y * z ∈ Δ) : (⟨y * z, hyz⟩ : Δ) • a = (⟨y, hy⟩ : Δ) • (⟨z, hz⟩ : Δ) • a :=
  mul_smul (⟨y, hy⟩ : Δ) ⟨z, hz⟩ a

/- The image of `U·g` in `G ⧸ V` is stable under left translation by `U`. -/
private lemma smul_mem_image (u : U) {x : G ⧸ V}
    (hx : x ∈ (QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ V))) :
    (u : G) • x ∈ (QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ V)) := by
  obtain ⟨y, ⟨w, hw, g', hg', rfl⟩, rfl⟩ := hx
  exact ⟨(u : G) * (w * g'), mul_assoc (u : G) w g' ▸ Set.mul_mem_mul (U.mul_mem u.2 hw) hg', rfl⟩

/- The `V`-fixedness of `a` makes `⟨q.out⟩ • a` independent of the coset representative:
translating the class by `u ∈ U` multiplies by `⟨u⟩`. -/
private lemma smul_out_smul (a : fixedPointsOfLE R A hV) (u : U) (q : G ⧸ V)
    (hq : q.out ∈ Δ) (hq' : ((u : G) • q).out ∈ Δ) :
    (⟨((u : G) • q).out, hq'⟩ : Δ) • (a : A) =
      (⟨u.1, hU u.2⟩ : Δ) • (⟨q.out, hq⟩ : Δ) • (a : A) := by
  obtain ⟨v, hv⟩ : ∃ v : V, ((u : G) • q).out = (u : G) * q.out * v :=
    Quotient.mk_smul_out V (u : G) q ▸ QuotientGroup.mk_out_eq_mul V ((u : G) * q.out)
  simp only [hv]
  rw [subtype_smul_mul (a : A) (Δ.mul_mem (hU u.2) hq) (hV v.2), a.2 v,
    subtype_smul_mul (a : A) (hU u.2) hq]

/-- The Hecke operator `[UgV] : A^V →ₗ[R] A^U` attached to a double coset `UgV ⊆ Δ`,
given that `UgV` is a finite union of left `V`-cosets.  The value on `a` is
`∑ gᵢ • a` over the canonical representatives `gᵢ = x.out ∈ UgV ⊆ Δ` of the classes
`x ∈ im(U·g) ⊆ G ⧸ V`.

Monoid generalisation of FLT's `AbstractHeckeOperator.heckeOperator`. -/
noncomputable def heckeOperator
    (h : (QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ V)).Finite) :
    fixedPointsOfLE R A hV →ₗ[R] fixedPointsOfLE R A hU where
  toFun a := ⟨∑ᶠ x : (QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ V)),
    (⟨(x : G ⧸ V).out,
        mul_singleton_mul_subset hU hV hg (out_mem_mul_singleton_mul x.2)⟩ : Δ) • (a : A),
    by
    intro u
    have : Fintype ((QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ V))) := h.fintype
    have key : ∀ {x : G ⧸ V}, x ∈ (QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ V)) →
        x.out ∈ Δ := fun hx => mul_singleton_mul_subset hU hV hg (out_mem_mul_singleton_mul hx)
    rw [finsum_eq_sum_of_fintype, Finset.smul_sum]
    exact Fintype.sum_equiv ⟨fun x => ⟨(u : G) • x.1, smul_mem_image u x.2⟩,
      fun x => ⟨(u : G)⁻¹ • x.1, smul_mem_image u⁻¹ x.2⟩,
      fun _ => Subtype.ext (inv_smul_smul _ _), fun _ => Subtype.ext (smul_inv_smul _ _)⟩
      _ _ fun x => (smul_out_smul R hU hV a u x.1 (key x.2) (key (smul_mem_image u x.2))).symm⟩
  map_add' a b := Subtype.ext (by
    have : Fintype ((QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ V))) := h.fintype
    simp only [finsum_eq_sum_of_fintype, Submodule.coe_add, smul_add, Finset.sum_add_distrib])
  map_smul' r a := Subtype.ext (by
    have : Fintype ((QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ V))) := h.fintype
    simp only [finsum_eq_sum_of_fintype, SetLike.val_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun x _ => smul_comm _ _ _)

/-- The defining formula for `heckeOperator`: the sum of `⟨x.out⟩ • a` over the classes
in the image of `U·g`. -/
lemma heckeOperator_apply
    (h : (QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ V)).Finite)
    (a : fixedPointsOfLE R A hV) :
    (heckeOperator R hU hV hg h a : A) =
      ∑ᶠ x : (QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ V)),
        (⟨(x : G ⧸ V).out,
          mul_singleton_mul_subset hU hV hg (out_mem_mul_singleton_mul x.2)⟩ : Δ) • (a : A) :=
  rfl

/-- The Hecke operator computed by any finite set of coset representatives in `Δ`. -/
lemma heckeOperator_eq_finsetSum
    (h : (QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ V)).Finite)
    (a : fixedPointsOfLE R A hV) (s : Finset G) (hsΔ : (s : Set G) ⊆ Δ)
    (hs : Set.BijOn QuotientGroup.mk (s : Set G)
      (QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ V))) :
    (heckeOperator R hU hV hg h a : A) = ∑ i ∈ s.attach, (⟨i.1, hsΔ i.2⟩ : Δ) • (a : A) := by
  have : Fintype ((QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ V))) := h.fintype
  rw [heckeOperator_apply, finsum_eq_sum_of_fintype, ← Finset.univ_eq_attach]
  refine (Fintype.sum_bijective (fun i => ⟨QuotientGroup.mk i.1, hs.mapsTo i.2⟩)
    ⟨fun i j hij => Subtype.ext (hs.injOn i.2 j.2 (congrArg Subtype.val hij)),
      fun y => (hs.surjOn y.2).elim fun x hx => ⟨⟨x, hx.1⟩, Subtype.ext hx.2⟩⟩
    _ _ fun x => ?_).symm
  obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul V x.1
  simp only [hv]
  rw [subtype_smul_mul (a : A) (hsΔ x.2) (hV v.2), a.2 v]

/-- Double cosets of a compact `U` and open `V` decompose into finitely many left cosets;
this is the standing finiteness hypothesis for Hecke operators at compact open levels.
Source: FLT, HeckeOperators/Abstract.lean header remark ("if `G` is a topological group and
`U`, `V` are compact open subgroups of `G`, then our finiteness hypothesis is automatically
satisfied for all `g ∈ G`"). -/
theorem finite_image_doubleCoset_of_isCompact_of_isOpen [TopologicalSpace G]
    [IsTopologicalGroup G] (hUc : IsCompact (U : Set G)) (hVo : IsOpen (V : Set G)) (g : G) :
    (QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ V)).Finite := by
  have : DiscreteTopology (G ⧸ V) := QuotientGroup.discreteTopology hVo
  exact ((hUc.mul isCompact_singleton).image continuous_quotient_mk').finite_of_discrete

end AbstractHeckeOperator
