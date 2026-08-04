/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Salvatore Mercuri
-/
import PhD.QMF.FLTstuff.Mathlib.Topology.Algebra.RestrictedProduct.Basic
-- PORT (v4.33): the FLT original inherited `≃ₗ`/`SMulMemClass` through
-- `Mathlib.LinearAlgebra.DFinsupp`/`Mathlib.LinearAlgebra.Matrix.Defs` (needed for the omitted
-- sections); import the lighter modules directly instead.
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.Submodule.Defs

/-!

# Isomorphisms of restricted products

Restricted products of isomorphic things are isomorphic.

Restricted product over a principal filter is isomorphic to a product.

We don't allow topological isomorphisms; they have to go into TopologicalSpace because of imports.

PARTIAL PORT (T016d-2b) of `FLT.Mathlib.Topology.Algebra.RestrictedProduct.Equiv`:
only the `restrictedProductCongrRight` family (`Equiv`/`MulEquiv`/`AddEquiv`/`LinearEquiv`)
and the `flatten` family (`flatten`, `flattenEquiv`, `flattenEquiv'` and their `apply` lemmas)
are ported — these are what
`PhD.QMF.FLTstuff.DedekindDomain.FiniteAdeleRing.BaseChange` needs. The matrix, units
and principal-filter material is omitted.

-- PORT (T016e extension): the `restrictedProductCongrLeft'`/`restrictedProductCongrLeft`
equivalences and the `restrictedProductCongr` family (`Equiv`/`AddEquiv`/`RingEquiv`, with
`RingEquiv.restrictedProductCongr_bijOn_structureSubring`) appended from the same FLT source
file (needed by `PhD.QMF.FLTstuff.NumberField.AdeleRing`). The `MulEquiv`/`LinearEquiv`
congr variants and the `binary`/matrix material remain omitted.

-- PORT (T016f-1 extension): `RestrictedProduct.principalEquivProd` appended from the same FLT
source file (needed by `ContinuousMulEquiv.restrictedProductPrincipal`, used in
`PhD.QMF.FLTstuff.HaarMeasure.HaarChar.AddEquiv`).
-/

open RestrictedProduct

section pi_congr_right

variable {ι : Type*}
variable {R₁ : ι → Type*} {R₂ : ι → Type*} {S₁ : ι → Type*} {S₂ : ι → Type*}
  [(i : ι) → SetLike (S₁ i) (R₁ i)] [(i : ι) → SetLike (S₂ i) (R₂ i)]
variable {A₁ : (i : ι) → Set (R₁ i)} {A₂ : (i : ι) → Set (R₂ i)}
variable {𝓕 : Filter ι}

/-- The equivalence between restricted products on the same index, when
each factor is equivalent, with compatibility on the restricted subsets. -/
@[simps]
def Equiv.restrictedProductCongrRight (φ : (i : ι) → R₁ i ≃ R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) :
    Πʳ i, [R₁ i, A₁ i]_[𝓕] ≃ Πʳ i, [R₂ i, A₂ i]_[𝓕] where
  toFun := map (fun i ↦ φ i) (by filter_upwards [hφ]; exact fun i ↦ Set.BijOn.mapsTo)
  invFun := map (fun i ↦ (φ i).symm)
    (by filter_upwards [hφ]; exact fun i ↦ Set.BijOn.mapsTo ∘ Set.BijOn.equiv_symm)
  -- PORT (v4.33): `by ext; simp` no longer fires `map_apply` here; close componentwise instead.
  left_inv x := by ext i; exact (φ i).symm_apply_apply _
  right_inv x := by ext i; exact (φ i).apply_symm_apply _

section add_mul_equiv

variable [(i : ι) → Monoid (R₁ i)] [(i : ι) → Monoid (R₂ i)]
  [(i : ι) → SubmonoidClass (S₁ i) (R₁ i)] [(i : ι) → SubmonoidClass (S₂ i) (R₂ i)]
variable {A₁ : (i : ι) → S₁ i} {A₂ : (i : ι) → S₂ i}

/-- The `MulEquiv` between restricted products built from `MulEquiv`s on the factors. -/
@[to_additive (attr := simps! apply) /-- The `AddEquiv` between restricted products built from
  `AddEquiv`s on the factors. -/]
def MulEquiv.restrictedProductCongrRight (φ : (i : ι) → R₁ i ≃* R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕]) ≃* (Πʳ i, [R₂ i, A₂ i]_[𝓕]) where
  __ := Equiv.restrictedProductCongrRight _ hφ
  map_mul' _ _ := by ext; simp

end add_mul_equiv

section linear_equiv

variable {T : Type*} [Semiring T]
variable [(i : ι) → AddCommMonoid (R₁ i)] [(i : ι) → AddCommMonoid (R₂ i)]
variable [(i : ι) → Module T (R₁ i)] [(i : ι) → Module T (R₂ i)]
variable [(i : ι) → AddSubmonoidClass (S₁ i) (R₁ i)] [(i : ι) → AddSubmonoidClass (S₂ i) (R₂ i)]
variable {A₁ : (i : ι) → S₁ i} {A₂ : (i : ι) → S₂ i}
variable [(i : ι) → SMulMemClass (S₁ i) T (R₁ i)] [(i : ι) → SMulMemClass (S₂ i) T (R₂ i)]

/-- The `LinearEquiv` between restricted products built from `LinearEquiv`s on the factors. -/
def LinearEquiv.restrictedProductCongrRight (φ : (i : ι) → R₁ i ≃ₗ[T] R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕]) ≃ₗ[T] (Πʳ i, [R₂ i, A₂ i]_[𝓕]) where
  __ := AddEquiv.restrictedProductCongrRight (fun i ↦ (φ i).toAddEquiv)
    (by filter_upwards [hφ]; exact fun i ↦ id)
  map_smul' m x := by
    ext i
    apply map_smul

end linear_equiv

end pi_congr_right

namespace RestrictedProduct

section flatten

variable {ι : Type*}
variable {ℱ : Filter ι}
    {G H : ι → Type*}
    {C : (i : ι) → Set (G i)}
    {D : (i : ι) → Set (H i)}
variable {ι₂ : Type*} {𝒢 : Filter ι₂} {f : ι → ι₂} (C)

variable (hf : Filter.Tendsto f ℱ 𝒢) in
/-- The canonical map from a restricted product of products over fibres of a map on indexing sets
to the restricted product over the original indexing set. -/
def flatten : Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[𝒢] →
    Πʳ i, [G i, C i]_[ℱ] :=
  mapAlong _ G f hf (fun i x ↦ x ⟨i, rfl⟩) (by filter_upwards with x y hy using hy ⟨x, rfl⟩ trivial)

@[simp]
lemma flatten_apply (hf : Filter.Tendsto f ℱ 𝒢) (x) (i : ι) :
    flatten C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

variable (hf : Filter.comap f 𝒢 = ℱ)

/-- The canonical bijection from a restricted product of products over fibres of a map on indexing
sets to the restricted product over the original indexing set. -/
def flattenEquiv :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[𝒢] ≃
    Πʳ i, [G i, C i]_[ℱ] where
  toFun := flatten C (by rw [Filter.tendsto_iff_comap]; exact hf.ge)
  invFun := fun ⟨x, hx⟩ ↦ ⟨fun _ i ↦ x i, by
    rw [← hf, Filter.eventually_comap] at hx
    filter_upwards [hx] with j hj ⟨i, hi⟩ _ using hj i hi⟩
  left_inv := by
    intro ⟨x, hx⟩
    ext _ ⟨i, rfl⟩
    rfl
  right_inv x := by ext i; rfl

@[simp]
lemma flatten_equiv_apply (x) (i : ι) :
    flattenEquiv C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

@[simp]
lemma flatten_equiv_symm_apply (x) (i : ι₂) (j : f ⁻¹' {i}) :
    (flattenEquiv C hf).symm x i j = x j.1 :=
  rfl

variable (hf : Filter.Tendsto f Filter.cofinite Filter.cofinite)

/-- The equivalence given by `flatten` when both restricted products are over the cofinite
filter. -/
def flattenEquiv' :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)] ≃
    Πʳ i, [G i, C i] :=
  flattenEquiv C <| le_antisymm (Filter.comap_cofinite_le f) (Filter.map_le_iff_le_comap.mp hf)

@[simp]
lemma flatten_equiv'_apply (x) (i : ι) :
    flattenEquiv' C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

@[simp]
lemma flatten_equiv'_symm_apply (x) (i : ι₂) (j : f ⁻¹' {i}) :
    (flattenEquiv' C hf).symm x i j = x j.1 :=
  rfl

end flatten

end RestrictedProduct

-- PORT (T016e extension) from here down.

section pi_congr_left

variable {ι₁ ι₂ : Type*}
variable {R₁ : ι₁ → Type*} {S₁ : ι₁ → Type*} {R₂ : ι₂ → Type*} {S₂ : ι₂ → Type*}
  [(i : ι₁) → SetLike (S₁ i) (R₁ i)] [(i : ι₂) → SetLike (S₂ i) (R₂ i)]
variable {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂}
variable {A₁ : (i : ι₁) → Set (R₁ i)} {A₂ : (i : ι₂) → Set (R₂ i)}

/-- The equivalence between restricted products on the same factors on different
indices, when the indices are equivalent, with compatibility on the restriction
filters. Applying the equivalence on the right-hand side. -/
@[simps! apply, simps -isSimp symm_apply]
def Equiv.restrictedProductCongrLeft' (e : ι₁ ≃ ι₂) (h : 𝓕₂ = 𝓕₁.map e) :
    Πʳ i, [R₁ i, A₁ i]_[𝓕₁] ≃ Πʳ j, [R₁ (e.symm j), A₁ (e.symm j)]_[𝓕₂] where
  toFun x := ⟨fun i ↦ e.piCongrLeft' _ x i, by
    have := x.eventually
    simp only [piCongrLeft'_apply, h, Filter.eventually_map]; grind⟩
  invFun y := ⟨fun j ↦ (e.piCongrLeft' _).symm y j, by
    have := y.eventually
    simp_rw [h] at this
    have := Filter.eventually_map.1 this
    simp only [piCongrLeft'_symm_apply]; grind⟩
  left_inv x := by
    ext i
    exact funext_iff.1 ((e.piCongrLeft' _).left_inv x) i
  right_inv y := by
    ext j
    exact funext_iff.1 ((e.piCongrLeft' _).right_inv y) j

@[simp]
theorem Equiv.restrictedProductCongrLeft'_symm_apply_apply (e : ι₁ ≃ ι₂) (h : 𝓕₂ = 𝓕₁.map e)
    (x : Πʳ j, [R₁ (e.symm j), A₁ (e.symm j)]_[𝓕₂]) (j : ι₂) :
    (restrictedProductCongrLeft' e h).symm x (e.symm j) = x j := by
  simp [restrictedProductCongrLeft'_symm_apply]

/-- The equivalence between restricted products on the same factors on different
indices, when the indices are equivalent, with compatibility on the restriction
filters. Applying the equivalence on the left-hand side. -/
def Equiv.restrictedProductCongrLeft (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e) :
    Πʳ i, [R₂ (e i), A₂ (e i)]_[𝓕₁] ≃ Πʳ j, [R₂ j, A₂ j]_[𝓕₂] :=
  ((e.symm).restrictedProductCongrLeft' (𝓕₂.map_equiv_symm _ ▸ h)).symm

@[simp]
theorem Equiv.restrictedProductCongrLeft_apply_apply (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (x : Πʳ i, [R₂ (e i), A₂ (e i)]_[𝓕₁]) (i : ι₁) :
    (restrictedProductCongrLeft e h) x (e i) = x i :=
  restrictedProductCongrLeft'_symm_apply_apply e.symm (𝓕₂.map_equiv_symm _ ▸ h) x _

end pi_congr_left

section pi_congr

variable {ι₁ ι₂ : Type*}
variable {R₁ : ι₁ → Type*} {S₁ : ι₁ → Type*} {R₂ : ι₂ → Type*} {S₂ : ι₂ → Type*}
  [(i : ι₁) → SetLike (S₁ i) (R₁ i)] [(i : ι₂) → SetLike (S₂ i) (R₂ i)]
variable {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂}
variable {A₁ : (i : ι₁) → Set (R₁ i)} {A₂ : (i : ι₂) → Set (R₂ i)}

/-- The equivalence between restricted products when the indices and factors are equivalent,
provided compatibility criteria on the restriction filters and factors. -/
def Equiv.restrictedProductCongr (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (φ : (i : ι₁) → R₁ i ≃ R₂ (e i))
    (hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))) :
    Πʳ i, [R₁ i, A₁ i]_[𝓕₁] ≃ Πʳ j, [R₂ j, A₂ j]_[𝓕₂] :=
  (Equiv.restrictedProductCongrRight φ hφ).trans
    (e.restrictedProductCongrLeft h)

@[simp]
theorem Equiv.restrictedProductCongr_apply_apply {e : ι₁ ≃ ι₂} {h : 𝓕₁ = 𝓕₂.comap e}
    {φ : (i : ι₁) → R₁ i ≃ R₂ (e i)}
    {hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))}
    {x : Πʳ i, [R₁ i, A₁ i]_[𝓕₁]} {i : ι₁} :
    e.restrictedProductCongr h φ hφ x (e i) =
      φ i (x i) := by
  -- PORT (v4.33): the residual goal is `map_apply`, definitional but instance-path
  -- mismatched for `simp`; close by `rfl`.
  simp [restrictedProductCongr]
  rfl

@[simp]
theorem Equiv.restrictedProductCongr_symm_apply {e : ι₁ ≃ ι₂} {h : 𝓕₁ = 𝓕₂.comap e}
    {φ : (i : ι₁) → R₁ i ≃ R₂ (e i)}
    {hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))}
    {x : Πʳ j, [R₂ j, A₂ j]_[𝓕₂]} :
    (e.restrictedProductCongr h φ hφ).symm x = fun a => (φ a).symm (x (e a)) :=
  rfl

section add_equiv

variable [(i : ι₁) → AddMonoid (R₁ i)] [(i : ι₂) → AddMonoid (R₂ i)]
  [(i : ι₁) → AddSubmonoidClass (S₁ i) (R₁ i)] [(i : ι₂) → AddSubmonoidClass (S₂ i) (R₂ i)]
variable {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}

/-- The additive monoid isomorphism between restricted
products when the indices and factors are equivalent, provided compatibility criteria on the
restriction filters and factors. -/
@[simps! apply]
def AddEquiv.restrictedProductCongr (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (φ : (i : ι₁) → R₁ i ≃+ R₂ (e i))
    (hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) ≃+ (Πʳ j, [R₂ j, A₂ j]_[𝓕₂]) where
  __ := Equiv.restrictedProductCongr e h (fun _ ↦ (φ _).toEquiv) hφ
  -- PORT (v4.33): componentwise, both sides are `map_apply`-definitional; close with
  -- `map_add` of the component equivalence.
  map_add' _ _ := by
    ext j
    obtain ⟨i, rfl⟩ := e.surjective j
    simp [Equiv.restrictedProductCongr_apply_apply, RestrictedProduct.add_apply, map_add]

end add_equiv

section ring_equiv

variable [(i : ι₁) → Semiring (R₁ i)] [(i : ι₂) → Semiring (R₂ i)]
  [(i : ι₁) → SubsemiringClass (S₁ i) (R₁ i)] [(i : ι₂) → SubsemiringClass (S₂ i) (R₂ i)]
variable {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}

/-- The ring isomorphism between restricted products when the indices and factors
are equivalent, provided compatibility criteria on the restriction filters and factors. -/
def RingEquiv.restrictedProductCongr (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (φ : (i : ι₁) → R₁ i ≃+* R₂ (e i))
    (hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) ≃+* (Πʳ j, [R₂ j, A₂ j]_[𝓕₂]) where
  __ := AddEquiv.restrictedProductCongr e h (fun _ ↦ (φ _).toAddEquiv) hφ
  -- PORT (v4.33): componentwise, both sides are `map_apply`-definitional; close with
  -- `map_mul` of the component equivalence.
  map_mul' x y := by
    show Equiv.restrictedProductCongr e h (fun i ↦ ((φ i).toAddEquiv).toEquiv) hφ (x * y)
      = Equiv.restrictedProductCongr e h (fun i ↦ ((φ i).toAddEquiv).toEquiv) hφ x
        * Equiv.restrictedProductCongr e h (fun i ↦ ((φ i).toAddEquiv).toEquiv) hφ y
    ext j
    obtain ⟨i, rfl⟩ := e.surjective j
    simp only [RestrictedProduct.mul_apply, Equiv.restrictedProductCongr_apply_apply]
    exact map_mul (φ i) (x i) (y i)

@[simp]
theorem RingEquiv.restrictedProductCongr_apply_apply {e : ι₁ ≃ ι₂} {h : 𝓕₁ = 𝓕₂.comap e}
    {φ : (i : ι₁) → R₁ i ≃+* R₂ (e i)}
    {hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))}
    {x : Πʳ i, [R₁ i, A₁ i]_[𝓕₁]} {i : ι₁} :
    RingEquiv.restrictedProductCongr e h φ hφ x (e i) =
      φ i (x i) := by
  -- PORT (v4.33): the residual goal is `map_apply`, definitional but instance-path
  -- mismatched for `simp`; close by `rfl`.
  simp [restrictedProductCongr]
  rfl

@[simp]
theorem RingEquiv.restrictedProductCongr_symm_apply {e : ι₁ ≃ ι₂} {h : 𝓕₁ = 𝓕₂.comap e}
    {φ : (i : ι₁) → R₁ i ≃+* R₂ (e i)}
    {hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))}
    {x : Πʳ j, [R₂ j, A₂ j]_[𝓕₂]} :
    (RingEquiv.restrictedProductCongr e h φ hφ).symm x = fun a => (φ a).symm (x (e a)) :=
  rfl

end ring_equiv

end pi_congr

section structure_map

variable {ι₁ ι₂ : Type*} {R₁ : ι₁ → Type*} {S₁ : ι₁ → Type*} {R₂ : ι₂ → Type*} {S₂ : ι₂ → Type*}
  [(i : ι₁) → SetLike (S₁ i) (R₁ i)] [(i : ι₂) → SetLike (S₂ i) (R₂ i)]
  {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂} {A₁ : (i : ι₁) → Set (R₁ i)} {A₂ : (i : ι₂) → Set (R₂ i)}

variable [(i : ι₁) → Ring (R₁ i)] [(i : ι₂) → Ring (R₂ i)]
  [(i : ι₁) → SubringClass (S₁ i) (R₁ i)] [(i : ι₂) → SubringClass (S₂ i) (R₂ i)]
  {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}

theorem RingEquiv.restrictedProductCongr_bijOn_structureSubring (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (φ : (i : ι₁) → R₁ i ≃+* R₂ (e i))
    (hφ : ∀ i, Set.BijOn (φ i) (A₁ i) (A₂ (e i))) :
    Set.BijOn (restrictedProductCongr e h φ (.of_forall hφ))
      (structureSubring R₁ A₁ 𝓕₁) (structureSubring R₂ A₂ 𝓕₂) := by
  have hm (i : _) := (hφ i).mapsTo
  have hs (i : _) := (hφ i).symm (φ i).toEquiv.invOn |>.mapsTo
  refine ⟨fun x hx ↦ ?_, (RingEquiv.injective _).injOn, fun y hy ↦ ?_⟩
  · refine mem_structureSubring_iff.2 fun i ↦ ?_
    obtain ⟨j, rfl⟩ := e.surjective i
    aesop
  · exact ⟨(restrictedProductCongr e h φ (.of_forall hφ)).symm y, by aesop⟩

end structure_map

-- PORT (T016f-1 extension): the `principal` section from the FLT source file
-- (`RestrictedProduct.principalEquivProd`), needed by the
-- `restrictedProductPrincipal` homeomorphism in
-- `PhD.QMF.FLTstuff.Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace`.

namespace RestrictedProduct

section principal
/-!

## Principal filters

A restricted product over a principal filter is isomorphic to a product.

-/

variable {ι : Type*} (R : ι → Type*) (S : Set ι) [∀ i, Decidable (i ∈ S)] (A : (i : ι) → Set (R i))

open scoped Filter

section type

/-- The canonical isomorphism between `Πʳ i, [R i, A i]_[𝓟 S]` and
`(Π i ∈ S, R i) × (Π i ∉ S, A i)`
-/
def principalEquivProd : Πʳ i, [R i, A i]_[𝓟 S] ≃
    (Π i : S, A i) × (Π i : (Sᶜ : Set ι), R i) where
  toFun x := (fun i ↦ ⟨x i, x.2 i.2⟩, fun i ↦ x i)
  invFun y := ⟨fun i ↦ if hi : i ∈ S then y.1 ⟨i, hi⟩ else y.2 ⟨i, hi⟩,
  by aesop⟩
  left_inv x := by ext; simp
  right_inv x := by
    ext i
    · simp
    · simp [dif_neg i.2]

end type

end principal

end RestrictedProduct
