/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper, Kevin Buzzard, Bhavik Mehta, Ruben Van de Velde, Bryan Wang Peng Jun,
Pietro Monticone
-/
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import PhD.Main.QMF.FLTstuff.Mathlib.Topology.Algebra.RestrictedProduct.Basic
-- PORT (T016d-2b extension): imports for the appended `flatten`/`single`/`eval` section.
import PhD.Main.QMF.FLTstuff.Mathlib.Topology.Algebra.RestrictedProduct.Equiv
import Mathlib.Topology.Algebra.ContinuousMonoidHom
-- PORT (T016e extension): for `secondCountableTopology_of_countable_cover'`.
import PhD.Main.QMF.FLTstuff.Mathlib.Topology.Bases

/-!
# Topological Space

Material destined for Mathlib.

PARTIAL PORT (T016a) of `FLT.Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace`:
only the declarations needed by
`PhD.Main.QMF.FLTstuff.Mathlib.Topology.Algebra.RestrictedProduct.Module` are ported
(`Continuous.restrictedProduct_congrRight`, the `mem_nhds` lemmas and
`RestrictedProduct.isOpenMap_of_open_components`); everything else from the FLT file either
already exists in Mathlib at this revision or is not needed here.

-- PORT (T016d-2b extension): appended the `flattenHomeomorph`/`flattenHomeomorph'` family and
the `singleContinuousAddMonoidHom`/`evalContinuousAddMonoidHom` declarations from the FLT file
(needed by `PhD.Main.QMF.FLTstuff.{Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing,
DedekindDomain.FiniteAdeleRing.BaseChange}`).

-- PORT (T016f-1 extension): appended `ContinuousMulEquiv.restrictedProductCongrRight` and the
`Homeomorph.restrictedProductPrincipal` / `ContinuousMulEquiv.restrictedProductPrincipal` pair
from the same FLT source file (needed by `PhD.Main.QMF.FLTstuff.HaarMeasure.HaarChar.AddEquiv`).

-- PORT (T016f-2b extension): appended `ContinuousMulEquiv.restrictedProductPi` together with
its `apply` / `symm_apply` lemmas from the same FLT source file (needed by
`PhD.Main.QMF.FLTstuff.HaarMeasure.HaarChar.FiniteAdeleRing`).
-/

open RestrictedProduct

variable {ι : Type*}
variable {ℱ : Filter ι}
    {G H : ι → Type*}
    {C : (i : ι) → Set (G i)}
    {D : (i : ι) → Set (H i)}

variable [Π i, TopologicalSpace (G i)] [Π i, TopologicalSpace (H i)] in
@[fun_prop]
theorem Continuous.restrictedProduct_congrRight {φ : (i : ι) → G i → H i}
    (hφ : ∀ᶠ i in ℱ, Set.MapsTo (φ i) (C i) (D i))
    (hφcont : ∀ i, Continuous (φ i)) :
    Continuous (map φ hφ) :=
  mapAlong_continuous G H id Filter.tendsto_id φ hφ hφcont

section nhds

open scoped Filter

variable [Π i, TopologicalSpace (G i)]

/-- An explicit condition for a set to be in the neighborhood of `x : Πʳ i, [G i, C i]_[𝓟 T]`
in terms of a product of neighbourhoods on the factors. -/
lemma RestrictedProduct.mem_nhds_iff_of_principal {T : Set ι} {x : Πʳ i, [G i, C i]_[𝓟 T]}
    (U : Set Πʳ i, [G i, C i]_[𝓟 T]) :
    U ∈ nhds x ↔ ∃ (I : Set ι) (s : (i : ι) → Set (G i)), I.Finite ∧ (∀ i, s i ∈ nhds (x i)) ∧
    (↑) ⁻¹' I.pi s ⊆ U := by
  rw [isEmbedding_coe_of_principal.nhds_eq_comap, Filter.mem_comap, nhds_pi]
  simp_rw [Filter.mem_pi]
  exact ⟨fun ⟨t, ⟨I, hIf, s, hs, ht⟩, htU⟩ ↦ ⟨I, s, hIf, hs, by grw [ht, htU]⟩,
    fun ⟨I, s, hIf, hs, hU⟩ ↦ ⟨I.pi s, ⟨I, hIf, s, hs, subset_rfl⟩, hU⟩⟩

/-- A condition for a set to be a neighborhood in `Πʳ i, [G i, C i]`, slightly weaker than the
condition in `mem_nhds_iff_of_cofinite`. -/
lemma RestrictedProduct.mem_nhds_of_exists_nhds_of_cofinite {x : Πʳ i, [G i, C i]}
    {U : Set Πʳ i, [G i, C i]} (hCopen : ∀ i, IsOpen (C i : Set (G i))) (s : (i : ι) → Set (G i))
    (hs : ∀ i, s i ∈ nhds (x i)) (hf : ∀ᶠ i in Filter.cofinite, C i ⊆ s i)
    (hU : (↑) ⁻¹' Set.univ.pi s ⊆ U) : U ∈ nhds x := by
  set I := {i | ¬C i ⊆ s i} with hIval
  set T := {i | x i ∉ C i} with hTval
  have hT : Filter.cofinite ≤ Filter.principal Tᶜ := by simpa using x.eventually
  have hT' : ∀ᶠ (i : ι) in Filter.principal Tᶜ, x i ∈ C i := by simp [hTval]
  obtain ⟨x', hx⟩ := RestrictedProduct.exists_inclusion_eq_of_eventually G C hT hT'
  have hs' : ∀ i, s i ∈ nhds (x' i) := by simpa [← hx] using hs
  rw [← hx, nhds_eq_map_inclusion hCopen hT, Filter.mem_map, mem_nhds_iff_of_principal]
  refine ⟨I ∪ T, s, Set.Finite.union hf x.eventually, hs', ?_⟩
  grw [← hU, ← Set.preimage_comp, coe_comp_inclusion, ← Set.image_subset_iff,
      Set.image_preimage_eq_inter_range, range_coe_principal]
  rintro y hy i -
  simp only [Set.mem_inter_iff, Set.mem_pi] at hy
  by_cases h : i ∈ I ∪ T
  · apply hy.left i h
  · simp only [Set.mem_union, not_or] at h
    have hy' : y i ∈ C i := hy.right i h.right
    simp only [hIval, Set.mem_ofPred_eq, not_not] at h
    exact h.left hy'

/-- The classical condition for a set to be a neighborhood in the restricted product. -/
lemma RestrictedProduct.mem_nhds_iff_of_cofinite {x : Πʳ i, [G i, C i]} {U : Set Πʳ i, [G i, C i]}
    (hCopen : ∀ i, IsOpen (C i : Set (G i))) :
    U ∈ nhds x ↔ ∃ (s : (i : ι) → Set (G i)), (∀ i, s i ∈ nhds (x i)) ∧
    (∀ᶠ i in Filter.cofinite, s i = C i) ∧ Set.univ.pi s ⊆ (↑) '' U := by
  refine ⟨fun hn ↦ ?_, fun ⟨s, hs, hsf, hsU⟩ ↦ ?_⟩
  · set T := {i | x i ∉ C i} with hTval
    have hT : Filter.cofinite ≤ Filter.principal Tᶜ := by simpa using x.eventually
    have hT' : ∀ᶠ (i : ι) in Filter.principal Tᶜ, x i ∈ C i := by simp [hTval]
    obtain ⟨x', hx⟩ := RestrictedProduct.exists_inclusion_eq_of_eventually G C hT hT'
    rw [← hx, nhds_eq_map_inclusion hCopen hT, Filter.mem_map, mem_nhds_iff_of_principal] at hn
    obtain ⟨I, s, hIf, hs, hU⟩ := hn
    refine ⟨fun i ↦ (s i ∪ {x | i ∉ I}) ∩ (C i ∪ {x | i ∈ T}), ?_, ?_, ?_⟩
    · intro i
      rw [← hx]
      apply Filter.inter_mem (Filter.mem_of_superset (hs i) Set.subset_union_left)
      apply IsOpen.mem_nhds (IsOpen.union (hCopen i) isOpen_const)
      rw [Set.mem_union, Set.mem_ofPred_eq, or_iff_not_imp_right]
      apply x'.eventually
    · filter_upwards [hIf.compl_mem_cofinite, x.eventually] with i (hI : i ∉ I) hC
      simp [hI, hC, hTval]
    · grw [← image_coe_preimage_inclusion_subset _ _ hT, ← hU, Set.image_preimage_eq_inter_range,
        range_coe_principal]
      simp [Set.subset_def, or_iff_not_imp_right, forall_and]
  · apply mem_nhds_of_exists_nhds_of_cofinite hCopen s hs
    · filter_upwards [hsf] with _ using superset_of_eq
    · exact Set.preimage_subset hsU DFunLike.coe_injective.injOn

end nhds

section openmap

variable [Π i, TopologicalSpace (G i)] [Π i, TopologicalSpace (H i)]

lemma RestrictedProduct.isOpenMap_of_open_components
    (hCopen : ∀ i, IsOpen (C i : Set (G i))) (hDopen : ∀ i, IsOpen (D i : Set (H i)))
    (f : Πʳ i, [G i, C i] → Πʳ i, [H i, D i]) (g : (i : ι) → G i → H i)
    (hcomponent : ∀ x i, f x i = g i (x i)) (hg : ∀ i, IsOpenMap (g i))
    (hsurj : ∀ᶠ i in Filter.cofinite, Set.SurjOn (g i) (C i) (D i)) :
    IsOpenMap f := by
  refine IsOpenMap.of_nhds_le fun x ↦ Filter.le_map fun U hU ↦ ?_
  obtain ⟨s, hf, hs, hU⟩ := (mem_nhds_iff_of_cofinite hCopen).mp hU
  apply mem_nhds_of_exists_nhds_of_cofinite hDopen fun i ↦ (g i) '' (s i)
  · intro i
    rw [hcomponent]
    exact IsOpenMap.image_mem_nhds (hg i) (hf i)
  · filter_upwards [hsurj, hs] with i hsurj' heq using heq ▸ hsurj'
  · apply Set.preimage_subset _ DFunLike.coe_injective.injOn
    grw [← Set.piMap_image_univ_pi, hU, ← Set.image_comp,
      ← Set.image_comp, ← components_comp_coe_eq_coe_apply hcomponent]
    rfl

end openmap

-- PORT (T016d-2b extension): everything below is appended from the FLT file.

section flatten

variable {ι₂ : Type*} {𝒢 : Filter ι₂} {f : ι → ι₂} (C)
variable (hf : Filter.comap f 𝒢 = ℱ)

namespace RestrictedProduct

variable [Π i, TopologicalSpace (G i)]

/-- The canonical homeomorphism from a restricted product of products over fibres of a map on
indexing sets to the restricted product over the original indexing set. -/
def flattenHomeomorph :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[𝒢] ≃ₜ
    Πʳ i, [G i, C i]_[ℱ] where
  __ := flattenEquiv C hf
  continuous_toFun := by
    dsimp only [flattenEquiv]
    apply mapAlong_continuous
    fun_prop
  continuous_invFun := by
    dsimp only [flattenEquiv]
    rw [continuous_dom]
    intro S hS
    set T := (f '' Sᶜ)ᶜ with hTval
    have hT : 𝒢 ≤ Filter.principal T := by
      rwa [Filter.le_principal_iff, hTval, ← Filter.mem_comap_iff_compl, hf,
        ← Filter.le_principal_iff]
    let g : Πʳ i, [G i, C i]_[Filter.principal S] → Πʳ j, [Π (i : f ⁻¹' {j}), G i,
        Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[Filter.principal T] :=
      fun x ↦ ⟨fun _ i ↦ x i, by
        have : Filter.comap f (Filter.principal T) ≤ Filter.principal S := by
          rw [Filter.le_principal_iff, Filter.mem_comap]
          use T
          refine ⟨Filter.mem_principal_self T, ?_⟩
          rw [hTval, Set.preimage_compl, Set.compl_subset_comm]
          apply Set.subset_preimage_image
        have hx := Filter.Eventually.filter_mono this x.prop
        rw [Filter.eventually_comap] at hx
        filter_upwards [hx] with j hj ⟨i, hi⟩ _ using hj i hi⟩
    let hg: Continuous g := by
      rw [continuous_rng_of_principal]
      unfold g
      fun_prop
    apply (continuous_inclusion hT).comp hg

@[simp]
lemma flatten_homeomorph_apply (x) (i : ι) :
    flattenHomeomorph C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

@[simp]
lemma flatten_homeomorph_symm_apply (x) (i : ι₂) (j : f ⁻¹' {i}) :
    (flattenHomeomorph C hf).symm x i j = x j.1 :=
  rfl

variable (hf : Filter.Tendsto f Filter.cofinite Filter.cofinite)

/-- The homeomorphism given by `flatten` when both restricted products are over the cofinite
filter and there's a topology on the factors. -/
def flattenHomeomorph' :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)] ≃ₜ
    Πʳ i, [G i, C i] :=
  flattenHomeomorph C <|
    le_antisymm (Filter.comap_cofinite_le f) (Filter.map_le_iff_le_comap.mp hf)

@[simp]
lemma flatten_homeomorph'_apply (x) (i : ι) :
    flattenHomeomorph' C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

@[simp]
lemma flatten_homeomorph'_symm_apply (x) (i : ι₂) (j : f ⁻¹' {i}) :
    (flattenHomeomorph' C hf).symm x i j = x j.1 :=
  rfl

end RestrictedProduct

end flatten

namespace RestrictedProduct

section single

variable {ι : Type*} [DecidableEq ι] {R : Type*} [Semiring R] (A : ι → Type*) {𝓕 : Filter ι}
    {S : ι → Type*}
    [(i : ι) → SetLike (S i) (A i)] {B : (i : ι) → S i} (j : ι) [(i : ι) → AddCommMonoid (A i)]
    [(i : ι) → Module R (A i)] [∀ (i : ι), AddSubmonoidClass (S i) (A i)]

variable [∀ i, TopologicalSpace (A i)]
open Filter in
/--
The inclusion from a factor into the restricted product of topological additive groups,
as a continuous group homomorphism.
-/
noncomputable def singleContinuousAddMonoidHom (j : ι) : A j →ₜ+ Πʳ i, [A i, B i] where
  __ := singleAddMonoidHom A j
  continuous_toFun := by
    let S : Set ι := {j}ᶜ
    let single' : A j → Πʳ i, [A i, B i]_[𝓟 S] :=
      fun x ↦ ⟨Pi.single j x,
        eventually_principal.mpr
        fun i hi ↦ by simp [Pi.single_eq_of_ne (Set.mem_compl_singleton_iff.mp hi)]⟩
    have : Continuous single' := by
      simpa [continuous_rng_of_principal] using! continuous_single j
    apply (isEmbedding_inclusion_principal
      (le_principal_iff.mpr (Set.finite_singleton j).compl_mem_cofinite)).continuous.comp this

lemma singleContinuousAddMonoidHom_apply_same {j : ι} (x : A j) :
    (singleContinuousAddMonoidHom A j x : Πʳ i, [A i, B i]) j = x :=
  Pi.single_eq_same j x

lemma singleContinuousAddMonoidHom_apply_of_ne {j i : ι} (h : i ≠ j) (x : A j) :
    (singleContinuousAddMonoidHom A j x : Πʳ i, [A i, B i]) i = 0 :=
  Pi.single_eq_of_ne h x

end single

section eval

variable {ι : Type*} [DecidableEq ι] {R : Type*} [Semiring R] (A : ι → Type*) {𝓕 : Filter ι}
    {S : ι → Type*}
    [(i : ι) → SetLike (S i) (A i)] {B : (i : ι) → S i} (j : ι) [(i : ι) → AddCommMonoid (A i)]
    [(i : ι) → Module R (A i)] [∀ (i : ι), AddSubmonoidClass (S i) (A i)]

variable [∀ i, TopologicalSpace (A i)]

/-- The continuous additive projection from a restricted product of topological additive groups
to a factor. -/
def evalContinuousAddMonoidHom (j : ι) : Πʳ i, [A i, B i] →ₜ+ A j := {
  __ := evalAddMonoidHom A j
  continuous_toFun := continuous_eval j
}

end eval

end RestrictedProduct

-- PORT (T016e extension): the second-countability results appended from the FLT file
-- (needed by `PhD.Main.QMF.FLTstuff.Mathlib.NumberTheory.NumberField.FiniteAdeleRing`).

open RestrictedProduct Filter in
instance RestrictedProduct.SecondCountableTopology_of_principal
    {ι : Type*} [Countable ι]
    (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
    (C : (i : ι) → Set (X i))
    [∀ i, SecondCountableTopology (X i)]
    {S : Set ι} :
    SecondCountableTopology (Πʳ i, [X i, C i]_[𝓟 S]) :=
  isEmbedding_coe_of_principal.secondCountableTopology

open Filter RestrictedProduct in
lemma RestrictedProduct.secondCountableTopology {ι : Type*} [Countable ι]
    {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {C : (i : ι) → Set (X i)} (hCopen : ∀ (i : ι), IsOpen (C i))
    [∀ i, SecondCountableTopology (X i)] :
    SecondCountableTopology (Πʳ i, [X i, C i]) := by
  -- PORT (v4.33): `Countable cofinite.sets` no longer found by instance search;
  -- derive it from countability of finite sets via complementation.
  have : Countable ((Filter.cofinite : Filter ι).sets) := by
    refine Set.Countable.to_subtype ((Set.Countable.ofPred_finite.image compl).mono ?_)
    exact fun s hs => ⟨sᶜ, hs, compl_compl s⟩
  exact TopologicalSpace.secondCountableTopology_of_countable_cover'
    (fun S : (.cofinite : Filter ι).sets ↦ inclusion X C (Filter.le_principal_iff.2 S.2))
    (fun S ↦ RestrictedProduct.isOpenEmbedding_inclusion_principal hCopen
        (Filter.le_principal_iff.2 S.2))
    (fun f ↦ ⟨⟨_, f.2⟩, ⟨f.1, by aesop⟩, rfl⟩)

-- PORT (T016f-1 extension): `ContinuousMulEquiv.restrictedProductCongrRight` and the
-- `restrictedProductPrincipal` homeomorphisms, appended from the FLT source file
-- (needed by `PhD.Main.QMF.FLTstuff.HaarMeasure.HaarChar.AddEquiv`).

section groups

variable {ι : Type*} {ℱ : Filter ι} {G H : ι → Type*}
variable {S T : ι → Type*} -- subobject types
variable [Π i, SetLike (S i) (G i)] [Π i, SetLike (T i) (H i)]
variable {A : Π i, S i} {B : Π i, T i}

variable [Π i, Monoid (G i)] [Π i, SubmonoidClass (S i) (G i)]
    [Π i, Monoid (H i)] [Π i, SubmonoidClass (T i) (H i)]
    [Π i, TopologicalSpace (G i)]
    [Π i, TopologicalSpace (H i)] in
/-- The `ContinuousMulEquiv` (that is, group isomorphism and homeomorphism) between restricted
products built from `ContinuousMulEquiv`s on the factors. -/
@[to_additive (attr := simps! symm_apply apply)
/-- The `ContinuousAddEquiv` (that is, additive group isomorphism and homeomorphism)
between restricted products built from `ContinuousAddEquiv`s on the factors. -/]
def ContinuousMulEquiv.restrictedProductCongrRight (φ : (i : ι) → G i ≃ₜ* H i)
    (hφ : ∀ᶠ i in ℱ, Set.BijOn (φ i) (A i) (B i)) :
    (Πʳ i, [G i, A i]_[ℱ]) ≃ₜ* (Πʳ i, [H i, B i]_[ℱ]) where
  __ := MulEquiv.restrictedProductCongrRight (φ ·|>.toMulEquiv) hφ
  continuous_toFun := Continuous.restrictedProduct_congrRight
    (hφ.mono fun _ ↦ Set.BijOn.mapsTo) fun i ↦ (φ i).continuous
  continuous_invFun := Continuous.restrictedProduct_congrRight
    (hφ.mono fun _ ↦ Set.BijOn.mapsTo ∘ Set.BijOn.equiv_symm) fun i ↦ (φ i).continuous_invFun

end groups

section equivs

open Classical Filter in
/-- The canonical homeomorphism between a restricted product `Πʳ i, [R i, A i]_[𝓟 J]` over
a principal filter, and the corresponding product `(Π i : J, A i) × (Π i : Jᶜ, R i)`.
-/
noncomputable def Homeomorph.restrictedProductPrincipal {ι : Type*}
    (R : ι → Type*) (A : Π i, Set (R i)) [∀ i, TopologicalSpace (R i)] (J : Set ι) :
    Πʳ i, [R i, A i]_[𝓟 J] ≃ₜ (Π i : J, A i) × (Π i : (Jᶜ : Set ι), R i) where
  __ := RestrictedProduct.principalEquivProd R J A
  continuous_toFun := continuous_prodMk.mpr
    ⟨continuous_pi fun _ ↦ continuous_induced_rng.mpr <| continuous_eval _,
      continuous_pi fun _ ↦ continuous_eval _⟩
  continuous_invFun := by
    refine continuous_rng_of_principal.mpr <| continuous_pi fun i ↦ ?_
    -- PORT (v4.33): `simp only [principalEquivProd, …]` no longer reduces the `Equiv.symm` of the
    -- structure literal, so restate the coordinate function with an explicit `show` first.
    show Continuous fun (y : (Π i : J, A i) × (Π i : (Jᶜ : Set ι), R i)) ↦
      (dite (α := R i) (i ∈ J) (fun h ↦ ((y.1 ⟨i, h⟩ : A i) : R i)) (fun h ↦ y.2 ⟨i, h⟩))
    by_cases hi : i ∈ J
    · simp only [hi, ↓reduceDIte]
      fun_prop
    · simp only [hi, ↓reduceDIte]
      fun_prop

open Filter in
/-- The canonical homeomorphism of group between a restricted product `Πʳ i, [R i, A i]_[𝓟 J]` over
a principal filter, and the corresponding product `(Π i : J, A i) × (Π i : Jᶜ, R i)`.
-/
@[to_additive /-- The canonical homeomorphism of group between a restricted product
`Πʳ i, [R i, A i]_[𝓟 J]` over a principal filter, and the corresponding product
`(Π i : J, A i) × (Π i : Jᶜ, R i)`. -/]
noncomputable def ContinuousMulEquiv.restrictedProductPrincipal {ι : Type*}
    {R : ι → Type*} [∀ i, Monoid (R i)] [∀ i, TopologicalSpace (R i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (R i)] [∀ i, SubmonoidClass (S i) (R i)] {A : Π i, S i}
    (J : Set ι) :
    Πʳ i, [R i, A i]_[𝓟 J] ≃ₜ* (Π i : J, A i) × (Π i : (Jᶜ : Set ι), R i) where
  toHomeomorph := Homeomorph.restrictedProductPrincipal R (fun i ↦ A i) J
  map_mul' _ _ := rfl

end equivs

-- PORT (T016f-2b extension): `ContinuousMulEquiv.restrictedProductPi` and its `apply` /
-- `symm_apply` lemmas, appended from the FLT source file
-- (needed by `PhD.Main.QMF.FLTstuff.HaarMeasure.HaarChar.FiniteAdeleRing`).

section pi

open Filter RestrictedProduct

/-- The group homeomorphism between a restricted product of finite products of groups,
and a finite product of restricted products of groups, when the products are with respect
to open subgroups.
-/
@[to_additive
/-- The additive group homeomorphism between a restricted product of finite products
of additive groups, and a finite product of restricted products of additive groups, when the
products are with respect to additive open subgroups. -/]
def ContinuousMulEquiv.restrictedProductPi {ι : Type*} {n : Type*} [Fintype n]
    {A : n → ι → Type*} [∀ j i, TopologicalSpace (A j i)] [∀ j i, Group (A j i)]
    {C : (j : n) → (i : ι) → Subgroup (A j i)} (hCopen : ∀ j i, IsOpen (C j i : Set (A j i))) :
    Πʳ i, [Π j, A j i, Subgroup.pi (Set.univ : Set n) (fun j ↦ C j i)] ≃ₜ*
      Π j, (Πʳ i, [A j i, C j i]) where
  toFun x j := map (fun i t ↦ t _)
    (Filter.Eventually.of_forall (fun _ _ ↦ by simp_all [Subgroup.mem_pi])) x
  invFun y := .mk (fun i j ↦ y j i)
    (by simpa [-eventually_cofinite, Subgroup.mem_pi] using! fun j ↦ (y j).property)
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  map_mul' x y := by ext; simp [RestrictedProduct.map]
  continuous_toFun := by
    exact continuous_pi fun j ↦
      Continuous.restrictedProduct_congrRight _ fun _ ↦ continuous_apply j
  continuous_invFun := by
    refine (continuous_dom_pi hCopen).mpr fun S hS ↦ ?_
    change Continuous
      (inclusion (fun i ↦ (j : n) → A j i)
        (fun i ↦ Subgroup.pi Set.univ (fun j ↦ C j i)) hS
      ∘ (fun (y : (j : n) → Πʳ (i : ι), [A j i, C j i]_[𝓟 S]) ↦ .mk (fun i j ↦ y j i)
        (by simpa [-eventually_principal, Subgroup.mem_pi] using! fun j ↦ (y j).property)))
    exact Continuous.comp (by fun_prop) <|
      continuous_rng_of_principal_iff_forall.mpr fun _ ↦ continuous_pi fun _ ↦
        (RestrictedProduct.continuous_eval _).comp (continuous_apply _)

@[to_additive (attr := simp)]
lemma ContinuousMulEquiv.restrictedProductPi_apply {ι : Type*} {n : Type*} [Fintype n]
    {A : n → ι → Type*} [∀ j i, TopologicalSpace (A j i)] [∀ j i, Group (A j i)]
    {C : (j : n) → (i : ι) → Subgroup (A j i)} {hCopen : ∀ j i, IsOpen (C j i : Set (A j i))}
    {x : Πʳ i, [Π j, A j i, Subgroup.pi (Set.univ : Set n) (fun j ↦ C j i)]} {i : ι} {j : n} :
    ContinuousMulEquiv.restrictedProductPi hCopen x j i
    = (x i) j :=
  rfl

@[to_additive (attr := simp)]
lemma ContinuousMulEquiv.restrictedProductPi_symm_apply {ι : Type*} {n : Type*} [Fintype n]
    {A : n → ι → Type*} [∀ j i, TopologicalSpace (A j i)] [∀ j i, Group (A j i)]
    {C : (j : n) → (i : ι) → Subgroup (A j i)} {hCopen : ∀ j i, IsOpen (C j i : Set (A j i))}
    {x : Π j, (Πʳ i, [A j i, C j i])} {i : ι} {j : n} :
    (ContinuousMulEquiv.restrictedProductPi hCopen).symm x i j
    = (x j) i :=
  rfl

end pi
