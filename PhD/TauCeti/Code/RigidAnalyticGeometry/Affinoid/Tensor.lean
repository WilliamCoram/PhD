/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.Continuity

/-!
# The affinoid tensor product, by presentations

For an affinoid Banach algebra `A` and affinoid `A`-algebras presented as `B₁ = A⟨X⟩ ⧸ 𝔟₁` and
`B₂ = A⟨Y⟩ ⧸ 𝔟₂`, the affinoid tensor product is `B₁ ⊗̂_A B₂ := A⟨X ⊕ Y⟩ ⧸ (𝔟₁, 𝔟₂)` (BGR 6.1.1/11,
"`T_m/𝔞 ⊗̂_k Tₙ/𝔟 = T_{m+n}/(𝔞, 𝔟)`"). It is affinoid, it is the pushout of `B₁ ← A → B₂` among
`K`-Banach algebras with continuous homomorphisms (the universal property of BGR 3.1.1/2 restricted
to continuous maps, proved through BGR 6.1.1/4), it is unique up to a unique continuous isomorphism,
it receives the algebraic tensor product `B₁ ⊗_A B₂` with dense image, and `B₂ → B₁ ⊗̂_A B₂` is
surjective when `A → B₁` is (BGR 6.1.1/11).

⚠ This is the construction by presentations of roadmap §1.1.5; BGR's complete tensor product with
its norm and its universal property for contractive maps is not built.

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, §1.1.4–1.1.5. Tau Ceti home:
`TauCeti/RingTheory/Affinoid/Tensor.lean`.

## Main definitions and results

* `MvPowerSeries.Restricted.inlAlgHom`, `inrAlgHom` — `A⟨X⟩ → A⟨X ⊕ Y⟩ ← A⟨Y⟩`.
* `Affinoid.TensorQuotient K A 𝔟₁ 𝔟₂` — `A⟨X ⊕ Y⟩ ⧸ (𝔟₁, 𝔟₂)`, with `tensorInl`, `tensorInr`.
* `Affinoid.IsAffinoidTensorProduct` — the pushout property among Banach algebras.
* `Affinoid.isAffinoidTensorProduct_tensorQuotient`,
  `Affinoid.IsAffinoidTensorProduct.exists_algEquiv` — existence and uniqueness.
* `Affinoid.isAffinoidTensorProduct_quotient_map` — `A ⧸ 𝔞 ⊗̂_A B₂ = B₂ ⧸ 𝔞 B₂`.
* `Affinoid.IsAffinoidTensorProduct.surjective_ι₂_of_surjective` — BGR 6.1.1/11.
* `Affinoid.denseRange_tensorLift` — the algebraic tensor product is dense.
-/

open MvPowerSeries MvPowerSeries.Restricted PowerBounded

universe v

namespace MvPowerSeries.Restricted

section Inl

variable {K : Type*} [NontriviallyNormedField K]
  {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
  (σ τ : Type*) [Finite σ] [Finite τ]

variable (K A) in
/-- The inclusion `A⟨X⟩ → A⟨X ⊕ Y⟩`. Source: BGR 6.1.1/7 ("the inclusions
`σ₁ : A ↪ A⟨X₁, …, Xₙ⟩` and `σ₂ : k⟨X₁, …, Xₙ⟩ ↪ A⟨X₁, …, Xₙ⟩`"). -/
noncomputable def inlAlgHom : Restricted A (1 : σ → ℝ) →ₐ[K] Restricted A (1 : σ ⊕ τ → ℝ) :=
  extendAlgHom (IsScalarTower.toAlgHom K A _) (continuous_algebraMap_restricted _)
    (fun i ↦ X A (1 : σ ⊕ τ → ℝ) (Sum.inl i)) fun _ ↦ isPowerBounded_X _

variable (K A) in
/-- The inclusion `A⟨Y⟩ → A⟨X ⊕ Y⟩`. -/
noncomputable def inrAlgHom : Restricted A (1 : τ → ℝ) →ₐ[K] Restricted A (1 : σ ⊕ τ → ℝ) :=
  extendAlgHom (IsScalarTower.toAlgHom K A _) (continuous_algebraMap_restricted _)
    (fun j ↦ X A (1 : σ ⊕ τ → ℝ) (Sum.inr j)) fun _ ↦ isPowerBounded_X _

omit [Finite τ] in
@[simp]
theorem inlAlgHom_C (a : A) : inlAlgHom K A σ τ (C (1 : σ → ℝ) a) = C (1 : σ ⊕ τ → ℝ) a :=
  (extendAlgHom_C _ (continuous_algebraMap_restricted _) _ _ a).trans (algebraMap_apply _ a)

omit [Finite τ] in
@[simp]
theorem inlAlgHom_X (i : σ) :
    inlAlgHom K A σ τ (X A (1 : σ → ℝ) i) = X A (1 : σ ⊕ τ → ℝ) (Sum.inl i) :=
  extendAlgHom_X _ _ _ _ i

omit [Finite σ] in
@[simp]
theorem inrAlgHom_C (a : A) : inrAlgHom K A σ τ (C (1 : τ → ℝ) a) = C (1 : σ ⊕ τ → ℝ) a :=
  (extendAlgHom_C _ (continuous_algebraMap_restricted _) _ _ a).trans (algebraMap_apply _ a)

omit [Finite σ] in
@[simp]
theorem inrAlgHom_X (j : τ) :
    inrAlgHom K A σ τ (X A (1 : τ → ℝ) j) = X A (1 : σ ⊕ τ → ℝ) (Sum.inr j) :=
  extendAlgHom_X _ _ _ _ j

omit [Finite τ] in
theorem continuous_inlAlgHom : Continuous (inlAlgHom K A σ τ) :=
  continuous_extendAlgHom _ _ _ _

omit [Finite σ] in
theorem continuous_inrAlgHom : Continuous (inrAlgHom K A σ τ) :=
  continuous_extendAlgHom _ _ _ _

omit [Finite τ] in
/-- The inclusions are `A`-algebra homomorphisms. -/
theorem inlAlgHom_comp_toAlgHom :
    (inlAlgHom K A σ τ).comp (IsScalarTower.toAlgHom K A _) = IsScalarTower.toAlgHom K A _ :=
  AlgHom.ext fun a ↦ (congrArg (inlAlgHom K A σ τ) (algebraMap_apply _ a)).trans
    ((inlAlgHom_C σ τ a).trans (algebraMap_apply _ a).symm)

omit [Finite σ] in
theorem inrAlgHom_comp_toAlgHom :
    (inrAlgHom K A σ τ).comp (IsScalarTower.toAlgHom K A _) = IsScalarTower.toAlgHom K A _ :=
  AlgHom.ext fun a ↦ (congrArg (inrAlgHom K A σ τ) (algebraMap_apply _ a)).trans
    ((inrAlgHom_C σ τ a).trans (algebraMap_apply _ a).symm)

end Inl

end MvPowerSeries.Restricted

namespace Affinoid

/-! ### The universal property -/

section IsAffinoidTensorProduct

variable {K : Type*} [NontriviallyNormedField K]
  {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
  {B₁ : Type*} [NormedCommRing B₁] [NormedAlgebra K B₁] [IsUltrametricDist B₁] [CompleteSpace B₁]
  {B₂ : Type*} [NormedCommRing B₂] [NormedAlgebra K B₂] [IsUltrametricDist B₂] [CompleteSpace B₂]
  {T : Type*} [NormedCommRing T] [NormedAlgebra K T] [IsUltrametricDist T] [CompleteSpace T]

/-- `T` with the continuous homomorphisms `ι₁ : B₁ → T`, `ι₂ : B₂ → T` is an **affinoid tensor
product** of the `A`-algebras `α₁ : A → B₁` and `α₂ : A → B₂` if it is their pushout among
`K`-Banach algebras with continuous `K`-algebra homomorphisms. Source: BGR 3.1.1/2 (the universal
property of the complete tensor product), 6.1.1/10–11; roadmap §1.1.5 ("the pushout of
`B₁ ← A → B₂` in the category of affinoid algebras"). -/
structure IsAffinoidTensorProduct (α₁ : A →ₐ[K] B₁) (α₂ : A →ₐ[K] B₂) (ι₁ : B₁ →ₐ[K] T)
    (ι₂ : B₂ →ₐ[K] T) : Prop where
  continuous_ι₁ : Continuous ι₁
  continuous_ι₂ : Continuous ι₂
  comp_eq : ι₁.comp α₁ = ι₂.comp α₂
  existsUnique_lift : ∀ {C : Type v} [NormedCommRing C] [NormedAlgebra K C] [IsUltrametricDist C]
    [CompleteSpace C] (f₁ : B₁ →ₐ[K] C) (f₂ : B₂ →ₐ[K] C), Continuous f₁ → Continuous f₂ →
    f₁.comp α₁ = f₂.comp α₂ →
      ∃! F : T →ₐ[K] C, Continuous F ∧ F.comp ι₁ = f₁ ∧ F.comp ι₂ = f₂

variable {α₁ : A →ₐ[K] B₁} {α₂ : A →ₐ[K] B₂} {ι₁ : B₁ →ₐ[K] T} {ι₂ : B₂ →ₐ[K] T}

omit [IsUltrametricDist A] [CompleteSpace A] [IsUltrametricDist B₁] [CompleteSpace B₁]
  [IsUltrametricDist B₂] [CompleteSpace B₂] in
/-- **Uniqueness** of the affinoid tensor product: two pushouts are related by a unique continuous
isomorphism compatible with the structure maps. Source: BGR 3.1.1/2 ("characterizes the complete
tensor product"); roadmap §1.1.5 ("independent of the presentations up to canonical
isomorphism"). -/
theorem IsAffinoidTensorProduct.exists_algEquiv {T T' : Type v} [NormedCommRing T]
    [NormedAlgebra K T] [IsUltrametricDist T] [CompleteSpace T] [NormedCommRing T']
    [NormedAlgebra K T'] [IsUltrametricDist T'] [CompleteSpace T'] {ι₁ : B₁ →ₐ[K] T}
    {ι₂ : B₂ →ₐ[K] T} {ι₁' : B₁ →ₐ[K] T'} {ι₂' : B₂ →ₐ[K] T'}
    (h : IsAffinoidTensorProduct.{v} α₁ α₂ ι₁ ι₂) (h' : IsAffinoidTensorProduct.{v} α₁ α₂ ι₁' ι₂') :
    ∃ e : T ≃ₐ[K] T', Continuous e ∧ Continuous e.symm ∧
      e.toAlgHom.comp ι₁ = ι₁' ∧ e.toAlgHom.comp ι₂ = ι₂' := by
  obtain ⟨F, ⟨hF, hF₁, hF₂⟩, -⟩ :=
    h.existsUnique_lift ι₁' ι₂' h'.continuous_ι₁ h'.continuous_ι₂ h'.comp_eq
  obtain ⟨G, ⟨hG, hG₁, hG₂⟩, -⟩ :=
    h'.existsUnique_lift ι₁ ι₂ h.continuous_ι₁ h.continuous_ι₂ h.comp_eq
  have hGF : G.comp F = AlgHom.id K T := by
    obtain ⟨_, -, hu⟩ := h.existsUnique_lift ι₁ ι₂ h.continuous_ι₁ h.continuous_ι₂ h.comp_eq
    exact (hu _ ⟨hG.comp hF, by rw [AlgHom.comp_assoc, hF₁, hG₁],
      by rw [AlgHom.comp_assoc, hF₂, hG₂]⟩).trans
      (hu _ ⟨continuous_id, AlgHom.id_comp _, AlgHom.id_comp _⟩).symm
  have hFG : F.comp G = AlgHom.id K T' := by
    obtain ⟨_, -, hu⟩ := h'.existsUnique_lift ι₁' ι₂' h'.continuous_ι₁ h'.continuous_ι₂ h'.comp_eq
    exact (hu _ ⟨hF.comp hG, by rw [AlgHom.comp_assoc, hG₁, hF₁],
      by rw [AlgHom.comp_assoc, hG₂, hF₂]⟩).trans
      (hu _ ⟨continuous_id, AlgHom.id_comp _, AlgHom.id_comp _⟩).symm
  exact ⟨AlgEquiv.ofAlgHom F G hFG hGF, hF, hG, hF₁, hF₂⟩

omit [IsUltrametricDist A] [CompleteSpace A] [IsUltrametricDist B₁] [CompleteSpace B₁]
  [IsUltrametricDist B₂] [CompleteSpace B₂] [IsUltrametricDist T] [CompleteSpace T] in
/-- The tensor-product property transports along a continuous isomorphism of the first factor. -/
theorem IsAffinoidTensorProduct.of_algEquiv_left {B₁' : Type*} [NormedCommRing B₁']
    [NormedAlgebra K B₁'] (h : IsAffinoidTensorProduct.{v} α₁ α₂ ι₁ ι₂) (e : B₁' ≃ₐ[K] B₁)
    (he : Continuous e) (he' : Continuous e.symm) :
    IsAffinoidTensorProduct.{v} (e.symm.toAlgHom.comp α₁) α₂ (ι₁.comp e.toAlgHom) ι₂ := by
  refine ⟨h.continuous_ι₁.comp he, h.continuous_ι₂, AlgHom.ext fun a ↦
    (congrArg ι₁ (e.apply_symm_apply (α₁ a))).trans (AlgHom.congr_fun h.comp_eq a), ?_⟩
  intro C _ _ _ _ f₁ f₂ hf₁ hf₂ hcomp
  have hcomp' : (f₁.comp e.symm.toAlgHom).comp α₁ = f₂.comp α₂ := by
    rw [AlgHom.comp_assoc]
    exact hcomp
  obtain ⟨F, ⟨hF, hF₁, hF₂⟩, hu⟩ :=
    h.existsUnique_lift (f₁.comp e.symm.toAlgHom) f₂ (hf₁.comp he') hf₂ hcomp'
  refine ⟨F, ⟨hF, AlgHom.ext fun b ↦ (AlgHom.congr_fun hF₁ (e b)).trans
    (congrArg f₁ (e.symm_apply_apply b)), hF₂⟩, fun F' ⟨hF', hF'₁, hF'₂⟩ ↦ hu F'
      ⟨hF', AlgHom.ext fun x ↦ (congrArg (fun y ↦ F' (ι₁ y)) (e.apply_symm_apply x)).symm.trans
        (AlgHom.congr_fun hF'₁ (e.symm x)), hF'₂⟩⟩

omit [IsUltrametricDist A] [CompleteSpace A] in
/-- The quotient `B₂ ⧸ 𝔞 B₂` is an affinoid tensor product of `A ⧸ 𝔞` and `B₂` over `A`, for a
closed ideal `𝔞` with `B₂` affinoid. Source: BGR 6.1.1/11 (the case `B₁ = A`, `𝔟₁ = 𝔞`,
`𝔟₂ = 0`: `A/𝔞 ⊗̂_A B₂ = B₂/𝔞B₂`). -/
theorem isAffinoidTensorProduct_quotient_map [IsUltrametricDist K] [CompleteSpace K]
    [NormOneClass B₂] (hB₂ : IsAffinoidAlgebra K B₂) (α₂ : A →ₐ[K] B₂) (hα₂ : Continuous α₂)
    (𝔞 : Ideal A) [IsClosed (𝔞 : Set A)] :
    haveI : IsClosed ((𝔞.map α₂ : Ideal B₂) : Set B₂) := hB₂.isClosed_ideal _
    IsAffinoidTensorProduct.{v} (Ideal.Quotient.mkₐ K 𝔞) α₂
      (Ideal.quotientMapₐ (𝔞.map α₂) α₂ Ideal.le_comap_map) (Ideal.Quotient.mkₐ K (𝔞.map α₂)) := by
  haveI : IsClosed ((𝔞.map α₂ : Ideal B₂) : Set B₂) := hB₂.isClosed_ideal _
  refine ⟨(QuotientAddGroup.isQuotientMap_mk 𝔞.toAddSubgroup).continuous_iff.2
    (continuous_quot_mk.comp hα₂), continuous_quot_mk, AlgHom.ext fun a ↦ rfl, ?_⟩
  intro C _ _ _ _ f₁ f₂ hf₁ hf₂ hcomp
  have hle : 𝔞.map α₂ ≤ RingHom.ker f₂ := Ideal.map_le_iff_le_comap.2 fun a ha ↦ by
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have h := AlgHom.congr_fun hcomp a
    rw [AlgHom.comp_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero] at h
    exact h.symm
  refine ⟨Ideal.Quotient.liftₐ _ f₂ fun b hb ↦ hle hb,
    ⟨?_, ?_, Ideal.Quotient.liftₐ_comp _ _ _⟩, ?_⟩
  · exact (QuotientAddGroup.isQuotientMap_mk (𝔞.map α₂).toAddSubgroup).continuous_iff.2 hf₂
  · exact Ideal.Quotient.algHom_ext K (AlgHom.ext fun a ↦ (AlgHom.congr_fun hcomp a).symm)
  · rintro F' ⟨-, -, hF'₂⟩
    exact Ideal.Quotient.algHom_ext K (hF'₂.trans (Ideal.Quotient.liftₐ_comp _ _ _).symm)

omit [IsUltrametricDist A] [IsUltrametricDist B₁] in
/-- **BGR 6.1.1/11**: if `α₁ : A → B₁` is surjective then so is `ι₂ : B₂ → B₁ ⊗̂_A B₂`, for `B₂`
affinoid: the tensor product is `B₂ ⧸ (ker α₁) B₂`. Source: BGR 6.1.1/11 ("the canonical map
`π : B₁ ⊗̂_A B₂ → B₁/𝔟₁ ⊗̂_A B₂/𝔟₂` is surjective"); roadmap §1.1.5. -/
theorem IsAffinoidTensorProduct.surjective_ι₂_of_surjective [IsUltrametricDist K]
    [CompleteSpace K] {B₂ T : Type v} [NormedCommRing B₂] [NormedAlgebra K B₂]
    [IsUltrametricDist B₂] [CompleteSpace B₂] [NormOneClass B₂] [NormedCommRing T]
    [NormedAlgebra K T] [IsUltrametricDist T] [CompleteSpace T] {α₂ : A →ₐ[K] B₂}
    {ι₁ : B₁ →ₐ[K] T} {ι₂ : B₂ →ₐ[K] T} (hB₂ : IsAffinoidAlgebra K B₂)
    (h : IsAffinoidTensorProduct.{v} α₁ α₂ ι₁ ι₂) (hα₁ : Continuous α₁)
    (hα₁' : Function.Surjective α₁) (hα₂ : Continuous α₂) : Function.Surjective ι₂ := by
  have hker : ((RingHom.ker α₁ : Ideal A) : Set A) = α₁ ⁻¹' {0} :=
    Set.ext fun _ ↦ RingHom.mem_ker
  haveI : IsClosed ((RingHom.ker α₁ : Ideal A) : Set A) :=
    hker ▸ isClosed_singleton.preimage hα₁
  haveI : IsClosed (((RingHom.ker α₁).map α₂ : Ideal B₂) : Set B₂) := hB₂.isClosed_ideal _
  let e : (A ⧸ RingHom.ker α₁) ≃ₐ[K] B₁ := Ideal.quotientKerAlgEquivOfSurjective hα₁'
  have he : Continuous e :=
    (QuotientAddGroup.isQuotientMap_mk (RingHom.ker α₁).toAddSubgroup).continuous_iff.2 hα₁
  have he' : Continuous e.symm := e.toLinearEquiv.continuous_symm he
  have hmk : e.symm.toAlgHom.comp α₁ = Ideal.Quotient.mkₐ K (RingHom.ker α₁) :=
    AlgHom.ext fun a ↦ e.symm_apply_eq.2 rfl
  have h' := h.of_algEquiv_left e he he'
  rw [hmk] at h'
  obtain ⟨ε, -, -, -, hε₂⟩ :=
    h'.exists_algEquiv (isAffinoidTensorProduct_quotient_map hB₂ α₂ hα₂ (RingHom.ker α₁))
  intro t
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (ε t)
  refine ⟨b, ε.injective ?_⟩
  rw [← hb]
  exact AlgHom.congr_fun hε₂ b

end IsAffinoidTensorProduct

/-! ### The construction by presentations -/

section TensorQuotient

variable (K : Type*) [NontriviallyNormedField K]
  (A : Type*) [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
  {σ τ : Type*} [Finite σ] [Finite τ]
  (𝔟₁ : Ideal (Restricted A (1 : σ → ℝ))) (𝔟₂ : Ideal (Restricted A (1 : τ → ℝ)))

/-- The ideal `(𝔟₁, 𝔟₂)` of `A⟨X ⊕ Y⟩` generated by the images of `𝔟₁ ⊂ A⟨X⟩` and `𝔟₂ ⊂ A⟨Y⟩`.
Source: BGR 6.1.1/11 ("denote by `(𝔟₁, 𝔟₂) ⊂ B₁ ⊗̂_A B₂` the ideal generated by the images of
`𝔟₁` and `𝔟₂`"). -/
noncomputable def tensorIdeal : Ideal (Restricted A (1 : σ ⊕ τ → ℝ)) :=
  𝔟₁.map (inlAlgHom K A σ τ) ⊔ 𝔟₂.map (inrAlgHom K A σ τ)

/-- **The affinoid tensor product by presentations**: `(A⟨X⟩ ⧸ 𝔟₁) ⊗̂_A (A⟨Y⟩ ⧸ 𝔟₂) :=
A⟨X ⊕ Y⟩ ⧸ (𝔟₁, 𝔟₂)`, with the residue seminorm. Source: BGR 6.1.1/11
("`T_m/𝔞 ⊗̂_k Tₙ/𝔟 = T_{m+n}/(𝔞, 𝔟)`"); roadmap §1.1.5. -/
abbrev TensorQuotient : Type _ :=
  Restricted A (1 : σ ⊕ τ → ℝ) ⧸ tensorIdeal K A 𝔟₁ 𝔟₂

/-- The first structure map `B₁ = A⟨X⟩ ⧸ 𝔟₁ → B₁ ⊗̂_A B₂`. -/
noncomputable def tensorInl : (Restricted A (1 : σ → ℝ) ⧸ 𝔟₁) →ₐ[K] TensorQuotient K A 𝔟₁ 𝔟₂ :=
  Ideal.Quotient.liftₐ 𝔟₁ ((Ideal.Quotient.mkₐ K _).comp (inlAlgHom K A σ τ)) fun _ hf ↦
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))

/-- The second structure map `B₂ = A⟨Y⟩ ⧸ 𝔟₂ → B₁ ⊗̂_A B₂`. -/
noncomputable def tensorInr : (Restricted A (1 : τ → ℝ) ⧸ 𝔟₂) →ₐ[K] TensorQuotient K A 𝔟₁ 𝔟₂ :=
  Ideal.Quotient.liftₐ 𝔟₂ ((Ideal.Quotient.mkₐ K _).comp (inrAlgHom K A σ τ)) fun _ hf ↦
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hf))

theorem tensorInl_mk (f : Restricted A (1 : σ → ℝ)) :
    tensorInl K A 𝔟₁ 𝔟₂ (Ideal.Quotient.mk 𝔟₁ f) =
      Ideal.Quotient.mk _ (inlAlgHom K A σ τ f) :=
  rfl

theorem tensorInr_mk (f : Restricted A (1 : τ → ℝ)) :
    tensorInr K A 𝔟₁ 𝔟₂ (Ideal.Quotient.mk 𝔟₂ f) =
      Ideal.Quotient.mk _ (inrAlgHom K A σ τ f) :=
  rfl

theorem continuous_tensorInl : Continuous (tensorInl K A 𝔟₁ 𝔟₂) :=
  (QuotientAddGroup.isQuotientMap_mk 𝔟₁.toAddSubgroup).continuous_iff.2
    (continuous_quot_mk.comp (continuous_inlAlgHom (K := K) (A := A) σ τ))

theorem continuous_tensorInr : Continuous (tensorInr K A 𝔟₁ 𝔟₂) :=
  (QuotientAddGroup.isQuotientMap_mk 𝔟₂.toAddSubgroup).continuous_iff.2
    (continuous_quot_mk.comp (continuous_inrAlgHom (K := K) (A := A) σ τ))

/-- The two structure maps agree on `A`. -/
theorem tensorInl_comp_eq_tensorInr_comp :
    (tensorInl K A 𝔟₁ 𝔟₂).comp (IsScalarTower.toAlgHom K A _) =
      (tensorInr K A 𝔟₁ 𝔟₂).comp (IsScalarTower.toAlgHom K A _) :=
  AlgHom.ext fun a ↦ (congrArg (Ideal.Quotient.mk _)
    (AlgHom.congr_fun (inlAlgHom_comp_toAlgHom (K := K) (A := A) σ τ) a)).trans
      (congrArg (Ideal.Quotient.mk _)
        (AlgHom.congr_fun (inrAlgHom_comp_toAlgHom (K := K) (A := A) σ τ) a)).symm

/-- The affinoid tensor product is affinoid when `A` is. Source: BGR 6.1.1/10 ("`B₁ ⊗̂_A B₂`,
viewed as a `k`-algebra, belongs to `𝔄`"), through `IsAffinoidAlgebra.restricted`. -/
theorem isAffinoidAlgebra_tensorQuotient [IsUltrametricDist K] [CompleteSpace K] [NormOneClass A]
    (hA : IsAffinoidAlgebra K A) : IsAffinoidAlgebra K (TensorQuotient K A 𝔟₁ 𝔟₂) :=
  hA.restricted.quotient _

/-- The ideal `(𝔟₁, 𝔟₂)` is closed when `A` is affinoid, so that the residue seminorm is a norm and
`B₁ ⊗̂_A B₂` is a Banach algebra. -/
theorem isClosed_tensorIdeal [IsUltrametricDist K] [CompleteSpace K] [NormOneClass A]
    (hA : IsAffinoidAlgebra K A) :
    IsClosed ((tensorIdeal K A 𝔟₁ 𝔟₂ : Ideal _) : Set (Restricted A (1 : σ ⊕ τ → ℝ))) :=
  hA.restricted.isClosed_ideal _

/-- **The universal property**: for continuous `f₁ : B₁ → C`, `f₂ : B₂ → C` into a Banach algebra
agreeing on `A` there is a unique continuous `F : B₁ ⊗̂_A B₂ → C` with `F ∘ ι₁ = f₁` and
`F ∘ ι₂ = f₂`, namely the extension of BGR 6.1.1/4 with `X i ↦ f₁ (X̄ i)`, `Y j ↦ f₂ (Ȳ j)`.
Source: BGR 6.1.1/10–11 ("it is not hard to see that these induced maps satisfy the universal
property characterizing the complete tensor product"). -/
theorem isAffinoidTensorProduct_tensorQuotient [IsUltrametricDist K] [CompleteSpace K]
    [NormOneClass A] (hA : IsAffinoidAlgebra K A) :
    haveI : IsClosed ((tensorIdeal K A 𝔟₁ 𝔟₂ : Ideal _) : Set (Restricted A (1 : σ ⊕ τ → ℝ))) :=
      isClosed_tensorIdeal K A 𝔟₁ 𝔟₂ hA
    haveI : IsClosed (𝔟₁ : Set (Restricted A (1 : σ → ℝ))) := hA.restricted.isClosed_ideal _
    haveI : IsClosed (𝔟₂ : Set (Restricted A (1 : τ → ℝ))) := hA.restricted.isClosed_ideal _
    IsAffinoidTensorProduct.{v} (IsScalarTower.toAlgHom K A (Restricted A (1 : σ → ℝ) ⧸ 𝔟₁))
      (IsScalarTower.toAlgHom K A (Restricted A (1 : τ → ℝ) ⧸ 𝔟₂)) (tensorInl K A 𝔟₁ 𝔟₂)
      (tensorInr K A 𝔟₁ 𝔟₂) := by
  haveI : IsClosed ((tensorIdeal K A 𝔟₁ 𝔟₂ : Ideal _) : Set (Restricted A (1 : σ ⊕ τ → ℝ))) :=
    isClosed_tensorIdeal K A 𝔟₁ 𝔟₂ hA
  haveI : IsClosed (𝔟₁ : Set (Restricted A (1 : σ → ℝ))) := hA.restricted.isClosed_ideal _
  haveI : IsClosed (𝔟₂ : Set (Restricted A (1 : τ → ℝ))) := hA.restricted.isClosed_ideal _
  refine ⟨continuous_tensorInl K A 𝔟₁ 𝔟₂, continuous_tensorInr K A 𝔟₁ 𝔟₂,
    tensorInl_comp_eq_tensorInr_comp K A 𝔟₁ 𝔟₂, ?_⟩
  intro D _ _ _ _ f₁ f₂ hf₁ hf₂ hcomp
  -- the two maps out of the restricted algebras, and the images of the variables
  let g₁ : Restricted A (1 : σ → ℝ) →ₐ[K] D := f₁.comp (Ideal.Quotient.mkₐ K 𝔟₁)
  let g₂ : Restricted A (1 : τ → ℝ) →ₐ[K] D := f₂.comp (Ideal.Quotient.mkₐ K 𝔟₂)
  have hg₁ : Continuous g₁ := hf₁.comp continuous_quot_mk
  have hg₂ : Continuous g₂ := hf₂.comp continuous_quot_mk
  obtain ⟨C₁, hC₁⟩ := exists_forall_norm_le_mul_of_continuous g₁ hg₁
  obtain ⟨C₂, hC₂⟩ := exists_forall_norm_le_mul_of_continuous g₂ hg₂
  let b : σ ⊕ τ → D := Sum.elim (fun i ↦ g₁ (X A (1 : σ → ℝ) i)) fun j ↦ g₂ (X A (1 : τ → ℝ) j)
  have hb : ∀ k, IsPowerBounded (b k) := by
    rintro (i | j)
    · exact IsPowerBounded.map K (φ := g₁.toRingHom) hC₁ (isPowerBounded_X i)
    · exact IsPowerBounded.map K (φ := g₂.toRingHom) hC₂ (isPowerBounded_X j)
  let φ : A →ₐ[K] D := g₁.comp (IsScalarTower.toAlgHom K A (Restricted A (1 : σ → ℝ)))
  have hφ : Continuous φ := hg₁.comp (continuous_algebraMap_restricted _)
  let F₀ := extendAlgHom φ hφ b hb
  have hF₀ : Continuous F₀ := continuous_extendAlgHom φ hφ b hb
  -- `F₀` restricts to `g₁` and `g₂`
  have hinl : F₀.comp (inlAlgHom K A σ τ) = g₁ :=
    AlgHom.coe_ringHom_injective (ringHom_ext_of_continuous
      (hF₀.comp (continuous_inlAlgHom σ τ)) hg₁
      (fun a ↦ (congrArg F₀ (inlAlgHom_C σ τ a)).trans
        ((extendAlgHom_C φ hφ b hb a).trans (congrArg g₁ (algebraMap_apply _ a))))
      fun i ↦ (congrArg F₀ (inlAlgHom_X σ τ i)).trans (extendAlgHom_X φ hφ b hb (Sum.inl i)))
  have hinr : F₀.comp (inrAlgHom K A σ τ) = g₂ :=
    AlgHom.coe_ringHom_injective (ringHom_ext_of_continuous
      (hF₀.comp (continuous_inrAlgHom σ τ)) hg₂
      (fun a ↦ (congrArg F₀ (inrAlgHom_C σ τ a)).trans
        ((extendAlgHom_C φ hφ b hb a).trans
          ((AlgHom.congr_fun hcomp a).trans (congrArg g₂ (algebraMap_apply _ a)))))
      fun j ↦ (congrArg F₀ (inrAlgHom_X σ τ j)).trans (extendAlgHom_X φ hφ b hb (Sum.inr j)))
  -- `F₀` kills `(𝔟₁, 𝔟₂)`
  have hker : tensorIdeal K A 𝔟₁ 𝔟₂ ≤ RingHom.ker F₀ := by
    refine sup_le (Ideal.map_le_iff_le_comap.2 fun g hg ↦ ?_)
      (Ideal.map_le_iff_le_comap.2 fun g hg ↦ ?_)
    · rw [Ideal.mem_comap, RingHom.mem_ker]
      exact (AlgHom.congr_fun hinl g).trans
        ((congrArg f₁ (Ideal.Quotient.eq_zero_iff_mem.2 hg)).trans (map_zero f₁))
    · rw [Ideal.mem_comap, RingHom.mem_ker]
      exact (AlgHom.congr_fun hinr g).trans
        ((congrArg f₂ (Ideal.Quotient.eq_zero_iff_mem.2 hg)).trans (map_zero f₂))
  let F := Ideal.Quotient.liftₐ _ F₀ fun x hx ↦ RingHom.mem_ker.1 (hker hx)
  refine ⟨F, ⟨?_, Ideal.Quotient.algHom_ext K (AlgHom.ext fun g ↦ AlgHom.congr_fun hinl g),
    Ideal.Quotient.algHom_ext K (AlgHom.ext fun g ↦ AlgHom.congr_fun hinr g)⟩, ?_⟩
  · exact (QuotientAddGroup.isQuotientMap_mk (tensorIdeal K A 𝔟₁ 𝔟₂).toAddSubgroup).continuous_iff.2
      hF₀
  · rintro F' ⟨hF', h₁, h₂⟩
    refine Ideal.Quotient.algHom_ext K (.trans ?_ (Ideal.Quotient.liftₐ_comp _ F₀ _).symm)
    refine AlgHom.coe_ringHom_injective (ringHom_ext_of_continuous
      (hF'.comp continuous_quot_mk) hF₀ (fun a ↦ ?_) ?_)
    · exact (congrArg (fun x ↦ F' (Ideal.Quotient.mk _ x)) (inlAlgHom_C σ τ a).symm).trans
        ((AlgHom.congr_fun h₁ (Ideal.Quotient.mk 𝔟₁ (C (1 : σ → ℝ) a))).trans
          ((congrArg g₁ (algebraMap_apply _ a)).symm.trans (extendAlgHom_C φ hφ b hb a).symm))
    · rintro (i | j)
      · exact (congrArg (fun x ↦ F' (Ideal.Quotient.mk _ x)) (inlAlgHom_X σ τ i).symm).trans
          ((AlgHom.congr_fun h₁ (Ideal.Quotient.mk 𝔟₁ (X A (1 : σ → ℝ) i))).trans
            (extendAlgHom_X φ hφ b hb (Sum.inl i)).symm)
      · exact (congrArg (fun x ↦ F' (Ideal.Quotient.mk _ x)) (inrAlgHom_X σ τ j).symm).trans
          ((AlgHom.congr_fun h₂ (Ideal.Quotient.mk 𝔟₂ (X A (1 : τ → ℝ) j))).trans
            (extendAlgHom_X φ hφ b hb (Sum.inr j)).symm)

/-- The first structure map as an `A`-algebra homomorphism. -/
noncomputable def tensorInlₐ :
    (Restricted A (1 : σ → ℝ) ⧸ 𝔟₁) →ₐ[A] TensorQuotient K A 𝔟₁ 𝔟₂ :=
  { tensorInl K A 𝔟₁ 𝔟₂ with
    commutes' := fun a ↦ congrArg (Ideal.Quotient.mk _)
      (AlgHom.congr_fun (inlAlgHom_comp_toAlgHom (K := K) (A := A) σ τ) a) }

/-- The second structure map as an `A`-algebra homomorphism. -/
noncomputable def tensorInrₐ :
    (Restricted A (1 : τ → ℝ) ⧸ 𝔟₂) →ₐ[A] TensorQuotient K A 𝔟₁ 𝔟₂ :=
  { tensorInr K A 𝔟₁ 𝔟₂ with
    commutes' := fun a ↦ congrArg (Ideal.Quotient.mk _)
      (AlgHom.congr_fun (inrAlgHom_comp_toAlgHom (K := K) (A := A) σ τ) a) }

open TensorProduct in
/-- The algebraic tensor product maps to the affinoid tensor product. -/
noncomputable def tensorLift :
    (Restricted A (1 : σ → ℝ) ⧸ 𝔟₁) ⊗[A] (Restricted A (1 : τ → ℝ) ⧸ 𝔟₂) →ₐ[A]
      TensorQuotient K A 𝔟₁ 𝔟₂ :=
  Algebra.TensorProduct.lift (tensorInlₐ K A 𝔟₁ 𝔟₂) (tensorInrₐ K A 𝔟₁ 𝔟₂) fun _ _ ↦
    Commute.all _ _

open TensorProduct in
/-- The algebraic tensor product `B₁ ⊗_A B₂` is dense in `B₁ ⊗̂_A B₂`: its image contains the
residue classes of all polynomials in `X ⊕ Y`. Source: roadmap §1.1.5 ("`B₁ ⊗̂_A B₂` receives the
algebraic tensor product `B₁ ⊗_A B₂` with dense image"). -/
theorem denseRange_tensorLift : DenseRange (tensorLift K A 𝔟₁ 𝔟₂) := by
  let π : MvPolynomial (σ ⊕ τ) A →+* TensorQuotient K A 𝔟₁ 𝔟₂ :=
    (Ideal.Quotient.mk _).comp (MvPolynomial.toRestricted (1 : σ ⊕ τ → ℝ))
  have hX : ∀ k, π (MvPolynomial.X k) ∈ (tensorLift K A 𝔟₁ 𝔟₂).range := by
    rintro (i | j)
    · refine (AlgHom.mem_range _).2 ⟨Ideal.Quotient.mk 𝔟₁ (X A (1 : σ → ℝ) i) ⊗ₜ 1, ?_⟩
      rw [tensorLift, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      exact (congrArg (Ideal.Quotient.mk _) (inlAlgHom_X (K := K) σ τ i)).trans
        (congrArg (Ideal.Quotient.mk _) (MvPolynomial.toRestricted_X _ (Sum.inl i))).symm
    · refine (AlgHom.mem_range _).2 ⟨1 ⊗ₜ Ideal.Quotient.mk 𝔟₂ (X A (1 : τ → ℝ) j), ?_⟩
      rw [tensorLift, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      exact (congrArg (Ideal.Quotient.mk _) (inrAlgHom_X (K := K) σ τ j)).trans
        (congrArg (Ideal.Quotient.mk _) (MvPolynomial.toRestricted_X _ (Sum.inr j))).symm
  have h1 : ∀ p, π p ∈ (tensorLift K A 𝔟₁ 𝔟₂).range := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      refine (AlgHom.mem_range _).2 ⟨algebraMap A _ a, ((tensorLift K A 𝔟₁ 𝔟₂).commutes a).trans ?_⟩
      exact congrArg (Ideal.Quotient.mk _)
        ((algebraMap_apply _ a).trans (MvPolynomial.toRestricted_C _ a).symm)
    | add p q hp hq =>
      rw [map_add]
      exact Subalgebra.add_mem _ hp hq
    | mul_X p k hp =>
      rw [map_mul]
      exact Subalgebra.mul_mem _ hp (hX k)
  have h2 : DenseRange π :=
    Ideal.Quotient.mk_surjective.denseRange.comp (denseRange_toRestricted _) continuous_quot_mk
  refine Dense.mono ?_ h2
  rintro _ ⟨p, rfl⟩
  exact (AlgHom.mem_range _).1 (h1 p)

end TensorQuotient

end Affinoid
