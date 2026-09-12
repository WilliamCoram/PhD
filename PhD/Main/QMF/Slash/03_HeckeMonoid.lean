/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.QMF.Slash.«02_Basic»
import PhD.Main.QMF.«00_HeckeMonoid»
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Abstract Hecke operators for the right slash

The right-handed mirror of `PhD/Main/QMF/00_HeckeMonoid.lean`, in Buzzard's own shape
[*Eigenvarieties*, §9 p. 69]:

> "If `η ∈ D^×_f` and `ηₚ ∈ Mₜ` then one can define an endomorphism `[UηU]` of `L(U,A)` as
> follows: decompose `UηU = ∐ᵢ U xᵢ` (a finite union) and define `f|[UηU] := ∑ᵢ f|xᵢ`."

Setting: `G` a group, `Δ' : Submonoid G`, `A` an additive monoid with
`RightSlashAction Δ' A`, and subgroups `U, V ≤ G` contained in `Δ'`.  For `g ∈ Δ'` with
`UgV` a finite union of *right* `U`-cosets `U·xᵢ`, we define
`[UgV] : A^{U,∣} →ₗ[R] A^{V,∣}` by `a ↦ ∑ᵢ a ∣ₛ xᵢ`.

**Variance note.**  The left-handed `heckeOperator` uses left cosets `xᵢV` and maps
`L(V) → L(U)`; the right-handed one uses right cosets `U·xᵢ` and maps `L(U) → L(V)`
(well-definedness of the sum uses `U`-fixedness of `a`; equivariance of the result is in
the `V`-direction).  For the Hecke operators of interest (`U = V`) both are endomorphisms.

Right cosets are classes of `QuotientGroup.rightRel U` (`x ≈ y ↔ y·x⁻¹ ∈ U`, so the class
of `x` is `U·x`, and two representatives of a class differ by *left* multiplication by
`U` — exactly what the slash-fixedness of `a` absorbs).  The image of `{g}·V` in the
right-coset space enumerates the cosets covering `UgV`.
-/

open scoped Pointwise QMF
open RightSlashAction

namespace AbstractHeckeOperatorSlash

variable {G : Type*} [Group G] {Δ' : Submonoid G} {A : Type*} [AddCommMonoid A]
  [RightSlashAction Δ' A] {U V : Subgroup G} {g : G}

variable (R : Type*) [Semiring R] [Module R A] [SMulSlashClass R Δ' A]

/-- The submodule of points of `A` fixed by the slash of a subgroup `U ≤ G` contained in
the acting submonoid `Δ'` — Buzzard's `L(U, A)`-condition `a ∣ u = a` in the abstract.
Right-handed mirror of `AbstractHeckeOperator.fixedPointsOfLE`. -/
def slashFixedPointsOfLE (A : Type*) [AddCommMonoid A] [RightSlashAction Δ' A]
    [Module R A] [SMulSlashClass R Δ' A] (hU : (U : Set G) ⊆ Δ') : Submodule R A where
  carrier := {a | ∀ u : U, a ∣ₛ (⟨u.1, hU u.2⟩ : Δ') = a}
  add_mem' ha hb u := by rw [add_slash, ha u, hb u]
  zero_mem' u := zero_slash _
  smul_mem' r a ha u := by rw [SMulSlashClass.smul_slash, ha u]

lemma mem_slashFixedPointsOfLE_iff {A : Type*} [AddCommMonoid A] [RightSlashAction Δ' A]
    [Module R A] [SMulSlashClass R Δ' A] (hU : (U : Set G) ⊆ Δ') {a : A} :
    a ∈ slashFixedPointsOfLE R A hU ↔
      ∀ u : U, a ∣ₛ (⟨u.1, hU u.2⟩ : Δ') = a := Iff.rfl

/-- The double coset `U·g·V` is contained in `Δ'` when `U`, `V` and `g` are. -/
lemma mul_singleton_mul_subset (hU : (U : Set G) ⊆ Δ') (hV : (V : Set G) ⊆ Δ')
    (hg : g ∈ Δ') : (U : Set G) * {g} * (V : Set G) ⊆ (Δ' : Set G) :=
  Submonoid.mul_subset (Submonoid.mul_subset hU (Set.singleton_subset_iff.2 hg)) hV

/-- The right-coset space of `U`: classes are the right cosets `U·x`. -/
abbrev RightCosets (U : Subgroup G) := Quotient (QuotientGroup.rightRel U)

/-- Right translation by an element descends to the right-coset space (representatives
of a class differ by left `U`-multiplication, which commutes with right translation). -/
def rightTranslate (v : G) (x : RightCosets U) : RightCosets U :=
  Quotient.map' (· * v) (fun a b hab => by
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    simpa [mul_assoc] using hab) x

@[simp] lemma rightTranslate_mk (v y : G) :
    rightTranslate (U := U) v (Quotient.mk'' y) = Quotient.mk'' (y * v) := rfl

/-- Canonical (`Quotient.out`) representatives of right-`U`-coset classes meeting `{g}·V`
lie in the double coset `U·g·V`. -/
lemma out_mem_mul_singleton_mul {x : RightCosets U}
    (hx : x ∈ ((Quotient.mk'' : G → RightCosets U) '' ({g} * (V : Set G)))) :
    x.out ∈ (U : Set G) * {g} * (V : Set G) := by
  obtain ⟨y, hy, hxy⟩ := hx
  have hrel : x.out * y⁻¹ ∈ U := by
    rw [← QuotientGroup.rightRel_apply (s := U)]
    exact Quotient.eq''.mp (hxy.trans (Quotient.out_eq' x).symm)
  rw [show (U : Set G) * {g} * (V : Set G) = (U : Set G) * ({g} * (V : Set G)) from
    mul_assoc _ _ _]
  exact ⟨x.out * y⁻¹, hrel, y, hy, by group⟩

variable (hU : (U : Set G) ⊆ Δ') (hV : (V : Set G) ⊆ Δ') {g : G} (hg : g ∈ Δ')

/- Splitting a product inside `Δ'` across the slash (the proof components are
irrelevant, so any memberships may be used). -/
lemma subtype_slash_mul (a : A) {y z : G} (hy : y ∈ Δ') (hz : z ∈ Δ')
    (hyz : y * z ∈ Δ') :
    a ∣ₛ (⟨y * z, hyz⟩ : Δ') = (a ∣ₛ (⟨y, hy⟩ : Δ')) ∣ₛ (⟨z, hz⟩ : Δ') :=
  (congrArg (a ∣ₛ ·) (Subtype.ext rfl :
    (⟨y * z, hyz⟩ : Δ') = (⟨y, hy⟩ : Δ') * ⟨z, hz⟩)).trans (slash_mul a _ _)

/- The image of `{g}·V` in the right-coset space is stable under right translation
by `V`. -/
private lemma rightTranslate_mem_image (v : V) {x : RightCosets U}
    (hx : x ∈ ((Quotient.mk'' : G → RightCosets U) '' ({g} * (V : Set G)))) :
    rightTranslate (v : G) x ∈
      ((Quotient.mk'' : G → RightCosets U) '' ({g} * (V : Set G))) := by
  obtain ⟨y, ⟨g', hg', v', hv', rfl⟩, rfl⟩ := hx
  exact ⟨g' * (v' * (v : G)),
    Set.mul_mem_mul hg' (V.mul_mem hv' v.2), by rw [rightTranslate_mk, mul_assoc]⟩

/- The `U`-slash-fixedness of `a` makes `a ∣ₛ ⟨q.out⟩` independent of the coset
representative: translating the class by `v ∈ V` on the right composes with `∣ₛ v`. -/
private lemma slash_out_slash (a : slashFixedPointsOfLE R A hU) (v : V)
    (q : RightCosets U) (hq : q.out ∈ Δ')
    (hq' : (rightTranslate (v : G) q).out ∈ Δ') :
    (a : A) ∣ₛ (⟨(rightTranslate (v : G) q).out, hq'⟩ : Δ')
      = ((a : A) ∣ₛ (⟨q.out, hq⟩ : Δ')) ∣ₛ (⟨v.1, hV v.2⟩ : Δ') := by
  obtain ⟨u, hu⟩ : ∃ u : U, (rightTranslate (v : G) q).out = u * (q.out * v) := by
    have h1 : (Quotient.mk'' (q.out * (v : G)) : RightCosets U)
        = Quotient.mk'' ((rightTranslate (v : G) q).out) := by
      rw [Quotient.out_eq', ← Quotient.out_eq' q, rightTranslate_mk, Quotient.out_eq']
    have h2 : (rightTranslate (v : G) q).out * (q.out * (v : G))⁻¹ ∈ U := by
      rw [← QuotientGroup.rightRel_apply (s := U)]
      exact Quotient.eq''.mp h1
    exact ⟨⟨_, h2⟩, by group⟩
  simp only [hu]
  rw [subtype_slash_mul (a : A) (hU u.2) (Δ'.mul_mem hq (hV v.2)), a.2 u,
    subtype_slash_mul (a : A) hq (hV v.2)]

/-- The Hecke operator `[UgV] : A^{U,∣} →ₗ[R] A^{V,∣}` attached to a double coset
`UgV ⊆ Δ'`, given that `UgV` is a finite union of right `U`-cosets.  The value on `a` is
`∑ᵢ a ∣ₛ xᵢ` over the canonical representatives `xᵢ = x.out ∈ UgV ⊆ Δ'` of the classes
`x ∈ im({g}·V) ⊆ U\G` — Buzzard's `f|[UηU] := ∑ᵢ f|xᵢ` verbatim.

Right-handed mirror of `AbstractHeckeOperator.heckeOperator` (note the variance flip:
`L(U) → L(V)`). -/
noncomputable def heckeOperatorSlash
    (h : (((Quotient.mk'' : G → RightCosets U) '' ({g} * (V : Set G))) :
      Set (RightCosets U)).Finite) :
    slashFixedPointsOfLE R A hU →ₗ[R] slashFixedPointsOfLE R A hV where
  toFun a := ⟨∑ᶠ x : (((Quotient.mk'' : G → RightCosets U) '' ({g} * (V : Set G))) :
      Set (RightCosets U)),
    (a : A) ∣ₛ (⟨(x : RightCosets U).out,
      mul_singleton_mul_subset hU hV hg (out_mem_mul_singleton_mul x.2)⟩ : Δ'), by
    intro v
    have : Fintype (((Quotient.mk'' : G → RightCosets U) '' ({g} * (V : Set G))) :
        Set (RightCosets U)) := h.fintype
    have key : ∀ {x : RightCosets U},
        x ∈ ((Quotient.mk'' : G → RightCosets U) '' ({g} * (V : Set G))) →
          x.out ∈ Δ' := fun hx =>
      mul_singleton_mul_subset hU hV hg (out_mem_mul_singleton_mul hx)
    rw [finsum_eq_sum_of_fintype, ← slashAddHom_apply (Δ := Δ'), map_sum]
    refine (Fintype.sum_equiv
      (⟨fun x => ⟨rightTranslate (v : G) x.1, rightTranslate_mem_image v x.2⟩,
        fun x => ⟨rightTranslate ((v : G))⁻¹ x.1, by
          simpa using rightTranslate_mem_image v⁻¹ x.2⟩,
        fun x => ?_, fun x => ?_⟩ :
        {x // x ∈ _} ≃ {x // x ∈ _})
      _ _ fun x => by
        simpa using (slash_out_slash R hU hV a v x.1 (key x.2)
          (key (rightTranslate_mem_image v x.2))).symm)
    · obtain ⟨x, hx⟩ := x
      refine Subtype.ext ?_
      induction x using Quotient.ind with
      | _ y => simp [rightTranslate_mk, mul_assoc]
    · obtain ⟨x, hx⟩ := x
      refine Subtype.ext ?_
      induction x using Quotient.ind with
      | _ y => simp [rightTranslate_mk, mul_assoc]⟩
  map_add' a b := Subtype.ext (by
    have : Fintype (((Quotient.mk'' : G → RightCosets U) '' ({g} * (V : Set G))) :
        Set (RightCosets U)) := h.fintype
    simp only [finsum_eq_sum_of_fintype, Submodule.coe_add, add_slash,
      Finset.sum_add_distrib])
  map_smul' r a := Subtype.ext (by
    have : Fintype (((Quotient.mk'' : G → RightCosets U) '' ({g} * (V : Set G))) :
        Set (RightCosets U)) := h.fintype
    simp only [finsum_eq_sum_of_fintype, SetLike.val_smul, Finset.smul_sum,
      RingHom.id_apply]
    exact Finset.sum_congr rfl fun x _ => (SMulSlashClass.smul_slash r _ _))

/-- The defining formula for `heckeOperatorSlash`: the sum of `a ∣ₛ x.out` over the
classes in the image of `{g}·V`. -/
lemma heckeOperatorSlash_apply
    (h : (((Quotient.mk'' : G → RightCosets U) '' ({g} * (V : Set G))) :
      Set (RightCosets U)).Finite)
    (a : slashFixedPointsOfLE R A hU) :
    (heckeOperatorSlash R hU hV hg h a : A) =
      ∑ᶠ x : (((Quotient.mk'' : G → RightCosets U) '' ({g} * (V : Set G))) :
        Set (RightCosets U)),
        (a : A) ∣ₛ (⟨(x : RightCosets U).out,
          mul_singleton_mul_subset hU hV hg (out_mem_mul_singleton_mul x.2)⟩ : Δ') := rfl

/-- The Hecke operator computed by any finite set of right-coset representatives in `Δ'`:
for `s` a system of representatives of the right cosets covering `UgV`,
`[UgV]a = ∑_{x ∈ s} a ∣ₛ x` — the thesis's own summation shape. -/
lemma heckeOperatorSlash_eq_finsetSum
    (h : (((Quotient.mk'' : G → RightCosets U) '' ({g} * (V : Set G))) :
      Set (RightCosets U)).Finite)
    (a : slashFixedPointsOfLE R A hU) (s : Finset G) (hsΔ : (s : Set G) ⊆ Δ')
    (hs : Set.BijOn (Quotient.mk'' : G → RightCosets U) (s : Set G)
      (((Quotient.mk'' : G → RightCosets U) '' ({g} * (V : Set G))) :
        Set (RightCosets U))) :
    (heckeOperatorSlash R hU hV hg h a : A)
      = ∑ i ∈ s.attach, (a : A) ∣ₛ (⟨i.1, hsΔ i.2⟩ : Δ') := by
  have : Fintype (((Quotient.mk'' : G → RightCosets U) '' ({g} * (V : Set G))) :
      Set (RightCosets U)) := h.fintype
  rw [heckeOperatorSlash_apply, finsum_eq_sum_of_fintype, ← Finset.univ_eq_attach]
  refine (Fintype.sum_bijective (fun i => ⟨Quotient.mk'' i.1, hs.mapsTo i.2⟩)
    ⟨fun i j hij => Subtype.ext (hs.injOn i.2 j.2 (congrArg Subtype.val hij)),
      fun y => (hs.surjOn y.2).elim fun x hx => ⟨⟨x, hx.1⟩, Subtype.ext hx.2⟩⟩
    _ _ fun x => ?_).symm
  obtain ⟨u, hu⟩ : ∃ u : U, (Quotient.mk'' x.1 : RightCosets U).out = u * x.1 := by
    have h2 : (Quotient.mk'' x.1 : RightCosets U).out * (x.1)⁻¹ ∈ U := by
      rw [← QuotientGroup.rightRel_apply (s := U)]
      exact Quotient.eq''.mp (Quotient.out_eq' _).symm
    exact ⟨⟨_, h2⟩, by group⟩
  simp only [hu]
  rw [subtype_slash_mul (a : A) (hU u.2) (hsΔ x.2), a.2 u]

/-- Double cosets of an open `U` and compact `V` decompose into finitely many right
cosets; the standing finiteness hypothesis at compact open levels.  Mirror of
`AbstractHeckeOperator.finite_image_doubleCoset_of_isCompact_of_isOpen`. -/
theorem finite_image_doubleCoset_of_isOpen_of_isCompact [TopologicalSpace G]
    [IsTopologicalGroup G] (hUo : IsOpen (U : Set G)) (hVc : IsCompact (V : Set G))
    (g : G) :
    (((Quotient.mk'' : G → RightCosets U) '' ({g} * (V : Set G))) :
      Set (RightCosets U)).Finite := by
  classical
  let f : RightCosets U → G ⧸ U := Quotient.map' (·⁻¹) (fun a b hab => by
    rw [QuotientGroup.rightRel_apply] at hab
    rw [QuotientGroup.leftRel_apply]
    simpa [mul_inv_rev] using U.inv_mem hab)
  have hfinj : Function.Injective f := by
    intro x y
    induction x using Quotient.ind with
    | _ a =>
      induction y using Quotient.ind with
      | _ b =>
        intro hxy
        refine Quotient.sound' ?_
        have h1 : QuotientGroup.leftRel U a⁻¹ b⁻¹ := Quotient.exact' hxy
        rw [QuotientGroup.leftRel_apply] at h1
        rw [QuotientGroup.rightRel_apply]
        simpa [mul_inv_rev] using U.inv_mem h1
  refine Set.Finite.of_finite_image ?_ hfinj.injOn
  have himg : f '' ((Quotient.mk'' : G → RightCosets U) '' ({g} * (V : Set G)))
      = QuotientGroup.mk '' ((V : Set G) * {g⁻¹}) := by
    ext q
    constructor
    · rintro ⟨-, ⟨y, hy, rfl⟩, rfl⟩
      obtain ⟨g', hg', v', hv', rfl⟩ := hy
      simp only [Set.mem_singleton_iff] at hg'
      subst hg'
      refine ⟨v'⁻¹ * g'⁻¹, Set.mul_mem_mul (V.inv_mem hv') rfl, ?_⟩
      show QuotientGroup.mk (v'⁻¹ * g'⁻¹) = f (Quotient.mk'' (g' * v'))
      simp only [f, Quotient.map'_mk'', mul_inv_rev]
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨v', hv', g', hg', rfl⟩ := hy
      simp only [Set.mem_singleton_iff] at hg'
      subst hg'
      refine ⟨Quotient.mk'' (g * v'⁻¹), ⟨g * v'⁻¹,
        Set.mul_mem_mul rfl (V.inv_mem hv'), rfl⟩, ?_⟩
      show f (Quotient.mk'' (g * v'⁻¹)) = _
      simp only [f, Quotient.map'_mk'', mul_inv_rev, inv_inv]
  rw [himg]
  exact AbstractHeckeOperator.finite_image_doubleCoset_of_isCompact_of_isOpen
    hVc hUo g⁻¹

end AbstractHeckeOperatorSlash
