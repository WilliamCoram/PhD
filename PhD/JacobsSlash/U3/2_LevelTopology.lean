/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.JacobsSlash.U3.«2_Level»
import PhD.QMF.Level

/-!
# The Hurwitz basis, and the levels `U₀(1)`, `U₁(9)` as compact open subgroups

[Buzzard, *Eigenvarieties*, §9 p. 68] takes the level `U ⊆ D_f^×` to be **compact open**;
that hypothesis is what makes the double-coset decomposition `UηU = ∐ U x_i` finite
(`AbstractHeckeOperatorSlash.finite_image_doubleCoset_of_isOpen_of_isCompact`).  This file
supplies it for the fork's levels, on the route of `PhD/QMF/Level.lean`:

* the Hurwitz order is the `ℤ`-span of `1, i, j, ω` with `ω = ½(1 + i + j + k)`
  (`JacobsSlash.hurwitzBasis`, packaging the fork's `hurwitzCoord` /
  `mem_hurwitzOrder_iff_coords` as a `Module.Basis`);
* hence the local order at `w` is the `𝓞_w`-span of that basis, and the everywhere-integral
  elements of `D ⊗ 𝔸_f` are exactly `QMF.integralTensor` of it — a compact set;
* `Units.isCompact_of_isCompact` then gives compactness of `U₀(1)`, and the congruence at `3`
  cuts out `U₁(9)` by a clopen condition.

The topology on `D ⊗[ℚ] 𝔸_f` is the `𝔸_f`-module topology of the `TensorProduct.RightActions`
scope, as in `PhD/QMF/Level.lean`.
-/

open scoped TensorProduct TensorProduct.RightActions Quaternion Pointwise
open IsDedekindDomain NumberField AbstractHeckeOperatorSlash

/- See `1_Setting.lean`: pin the adic `Algebra ℚ K₃` path.  Without this the `⊗ₜ[ℚ]` of this
file elaborates at `DivisionRing.toRatAlgebra` and no statement about `theta` will match. -/
attribute [local instance 2000]
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace JacobsSlash

/-- The Hurwitz coordinates as a `ℚ`-linear equivalence `D ≃ₗ[ℚ] (Fin 4 → ℚ)`:
`x ↦ (re − imK, imI − imK, imJ − imK, 2·imK)`, inverse `c ↦ c₀ + c₁ i + c₂ j + c₃ ω`. -/
noncomputable def hurwitzCoordEquiv : D ≃ₗ[ℚ] (Fin 4 → ℚ) where
  toFun := hurwitzCoord
  map_add' x y := by
    funext m
    fin_cases m <;> simp [hurwitzCoord] <;> ring
  map_smul' c x := by
    funext m
    fin_cases m <;> simp [hurwitzCoord] <;> ring
  invFun c := c 0 • (1 : D) + c 1 • qi + c 2 • qj + c 3 • qomega
  left_inv x := by
    apply QuaternionAlgebra.ext <;> simp [hurwitzCoord] <;> ring
  right_inv c := by
    funext m
    fin_cases m <;> simp [hurwitzCoord] <;> ring

/-- **The Hurwitz basis `1, i, j, ω` of `ℍ[ℚ]`** [Jacobs p. 22].  `hurwitzCoord` is its
coordinate function, so `mem_hurwitzOrder_iff_coords` says the Hurwitz order is exactly the
`ℤ`-lattice it spans. -/
noncomputable def hurwitzBasis : Module.Basis (Fin 4) ℚ D :=
  Module.Basis.ofEquivFun hurwitzCoordEquiv

@[simp] theorem hurwitzBasis_repr (x : D) (m : Fin 4) :
    hurwitzBasis.repr x m = hurwitzCoord x m := rfl

@[simp] theorem hurwitzBasis_apply (m : Fin 4) :
    hurwitzBasis m = ![(1 : D), qi, qj, qomega] m := by
  rw [hurwitzBasis, Module.Basis.coe_ofEquivFun]
  fin_cases m <;>
    · apply QuaternionAlgebra.ext <;> simp [hurwitzCoordEquiv, Pi.single_apply]

/-- The Hurwitz basis lies in the Hurwitz order. -/
theorem hurwitzBasis_mem (m : Fin 4) : hurwitzBasis m ∈ hurwitzOrder := by
  fin_cases m <;> simp only [hurwitzBasis_apply] <;> simp

/-- Reconstruction from the Hurwitz coordinates: `x = ∑ c_m(x) · b_m`. -/
theorem sum_hurwitzCoord_smul (x : D) :
    ∑ m, hurwitzCoord x m • hurwitzBasis m = x := by
  have h := hurwitzBasis.sum_repr x
  simpa only [hurwitzBasis_repr] using h

/-! ### The everywhere-integral elements of `D ⊗ 𝔸_f` -/

/-- A finite adele is integral iff it is integral at every place (the integral adeles are the
range of the structure map of the restricted product). -/
theorem mem_integralAdeles_iff {a : FiniteAdeleRing (RingOfIntegers ℚ) ℚ} :
    a ∈ FiniteAdeleRing.integralAdeles (RingOfIntegers ℚ) ℚ ↔
      ∀ w : HeightOneSpectrum (RingOfIntegers ℚ), a w ∈ w.adicCompletionIntegers ℚ := by
  constructor
  · rintro ⟨y, rfl⟩ w
    exact (y w).2
  · intro h
    exact ⟨fun w => ⟨a w, h w⟩, by ext w; rfl⟩

/-- The adelic extension of a `ℚ`-linear coordinate functional on `D`
(the `𝔸_f`-analogue of `JacobsSlash.coordMap`). -/
noncomputable def coordMapAdelic (φ : D →ₗ[ℚ] ℚ) :
    D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ →ₗ[ℚ]
      FiniteAdeleRing (RingOfIntegers ℚ) ℚ :=
  TensorProduct.lift ((LinearMap.mul ℚ (FiniteAdeleRing (RingOfIntegers ℚ) ℚ)).comp
    ((Algebra.linearMap ℚ (FiniteAdeleRing (RingOfIntegers ℚ) ℚ)).comp φ))

@[simp] theorem coordMapAdelic_tmul (φ : D →ₗ[ℚ] ℚ) (d : D)
    (a : FiniteAdeleRing (RingOfIntegers ℚ) ℚ) :
    coordMapAdelic φ (d ⊗ₜ[ℚ] a)
      = algebraMap ℚ (FiniteAdeleRing (RingOfIntegers ℚ) ℚ) (φ d) * a := rfl

/-- **The coordinates are local-global compatible**: taking the `w`-component of an adelic
coordinate is the `w`-coordinate of the `w`-component. -/
theorem evalAlgHom_coordMapAdelic (φ : D →ₗ[ℚ] ℚ)
    (w : HeightOneSpectrum (RingOfIntegers ℚ))
    (x : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) :
    QMF.evalAlgHom ℚ w (coordMapAdelic φ x) = coordMap w φ (QMF.toLocal ℚ D w x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul d a =>
      rw [coordMapAdelic_tmul, QMF.toLocal_tmul, coordMap_tmul, map_mul, AlgHom.commutes]
  | add u v hu hv => rw [map_add, map_add, map_add, map_add, hu, hv]

/-- **Reconstruction from the Hurwitz coordinates over the adeles**: every element of
`D ⊗ 𝔸_f` is the sum of its Hurwitz coordinates against the basis. -/
theorem sum_coordMapAdelic (x : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) :
    ∑ m, hurwitzBasis m ⊗ₜ[ℚ] coordMapAdelic (hurwitzBasis.coord m) x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul d a =>
      have h : ∀ m : Fin 4, hurwitzBasis m ⊗ₜ[ℚ]
          coordMapAdelic (hurwitzBasis.coord m) (d ⊗ₜ[ℚ] a)
          = (hurwitzCoord d m • hurwitzBasis m) ⊗ₜ[ℚ] a := fun m => by
        rw [coordMapAdelic_tmul, ← Algebra.smul_def, TensorProduct.smul_tmul]
        rfl
      rw [Finset.sum_congr rfl fun m _ => h m, ← TensorProduct.sum_tmul, sum_hurwitzCoord_smul]
  | add u v hu hv =>
      rw [Finset.sum_congr rfl fun m _ => by rw [map_add, TensorProduct.tmul_add],
        Finset.sum_add_distrib, hu, hv]

/-! ### `U₀(1)` is compact -/

/-- The index equivalence `Fin 4 ≃ Fin (finrank ℚ D)`. -/
noncomputable def hurwitzIdx : Fin 4 ≃ Fin (Module.finrank ℚ D) :=
  finCongr (Quaternion.finrank_eq_four (R := ℚ)).symm

/-- The Hurwitz basis, indexed as `QMF.integralTensor` wants it. -/
noncomputable def hurwitzBasis' : Module.Basis (Fin (Module.finrank ℚ D)) ℚ D :=
  hurwitzBasis.reindex hurwitzIdx

@[simp] theorem hurwitzBasis'_apply (m : Fin (Module.finrank ℚ D)) :
    hurwitzBasis' m = hurwitzBasis (hurwitzIdx.symm m) :=
  Module.Basis.reindex_apply _ _ _

theorem hurwitzBasis'_coord (m : Fin (Module.finrank ℚ D)) (d : D) :
    hurwitzBasis'.coord m d = hurwitzCoord d (hurwitzIdx.symm m) := by
  rw [Module.Basis.coord_apply, hurwitzBasis', Module.Basis.repr_reindex_apply,
    hurwitzBasis_repr]

theorem hurwitzBasis'_coord_eq (m : Fin 4) :
    hurwitzBasis'.coord (hurwitzIdx m) = hurwitzBasis.coord m :=
  LinearMap.ext fun d => by
    rw [hurwitzBasis'_coord, Equiv.symm_apply_apply, Module.Basis.coord_apply, hurwitzBasis_repr]

/-- The tuple of Hurwitz coordinates over the adeles, as an `𝔸_f`-linear map. -/
noncomputable def coordsAdelic :
    (D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) →ₗ[FiniteAdeleRing (RingOfIntegers ℚ) ℚ]
      (Fin (Module.finrank ℚ D) → FiniteAdeleRing (RingOfIntegers ℚ) ℚ) where
  toFun x m := coordMapAdelic (hurwitzBasis'.coord m) x
  map_add' x y := by
    funext m
    simp only [map_add, Pi.add_apply]
  map_smul' a x := by
    funext m
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul d z =>
        rw [show a • (d ⊗ₜ[ℚ] z) = d ⊗ₜ[ℚ] (a * z) by
              simp [TensorProduct.RightActions.smul_def, TensorProduct.smul_tmul'],
          coordMapAdelic_tmul, coordMapAdelic_tmul]
        ring
    | add u w hu hw => rw [smul_add, map_add, map_add, hu, hw, mul_add]

@[simp] theorem coordsAdelic_apply (x : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ)
    (m : Fin (Module.finrank ℚ D)) :
    coordsAdelic x m = coordMapAdelic (hurwitzBasis'.coord m) x := rfl

/-- Reconstruction, in the `hurwitzBasis'` indexing. -/
theorem sum_coordsAdelic (x : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) :
    ∑ m, hurwitzBasis' m ⊗ₜ[ℚ] coordsAdelic x m = x := by
  rw [← Equiv.sum_comp hurwitzIdx fun m => hurwitzBasis' m ⊗ₜ[ℚ] coordsAdelic x m]
  refine (Finset.sum_congr rfl fun m _ => ?_).trans (sum_coordMapAdelic x)
  rw [coordsAdelic_apply, hurwitzBasis'_apply, Equiv.symm_apply_apply, hurwitzBasis'_coord_eq]

/-- The coordinates of an explicit combination are the coefficients. -/
theorem coordsAdelic_sum (a : Fin (Module.finrank ℚ D) → FiniteAdeleRing (RingOfIntegers ℚ) ℚ)
    (m : Fin (Module.finrank ℚ D)) :
    coordsAdelic (∑ l, hurwitzBasis' l ⊗ₜ[ℚ] a l) m = a m := by
  rw [coordsAdelic_apply, map_sum]
  rw [Finset.sum_eq_single m]
  · rw [coordMapAdelic_tmul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same, map_one, one_mul]
  · intro l _ hl
    rw [coordMapAdelic_tmul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_of_ne (Ne.symm hl), map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ m) h

/-- `QMF.integralTensor` is cut out by integrality of the Hurwitz coordinates — a *preimage*
description, which is what makes it **open** as well as compact. -/
theorem integralTensor_eq_preimage :
    QMF.integralTensor ℚ D hurwitzBasis'
      = coordsAdelic ⁻¹'
        {a | ∀ m, a m ∈ FiniteAdeleRing.integralAdeles (RingOfIntegers ℚ) ℚ} := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩ m
    show coordsAdelic (∑ l, hurwitzBasis' l ⊗ₜ[ℚ] a l) m ∈ _
    rw [coordsAdelic_sum]
    exact ha m
  · intro h
    exact ⟨fun m => coordsAdelic x m, h, sum_coordsAdelic x⟩

/-- **The everywhere-integral elements of `D ⊗ 𝔸_f` are the integral span of the Hurwitz
basis** — the adelic form of [Jacobs, (1.4.7)]'s lattice argument, and the input that makes
`U₀(1)` compact.  Forward: each Hurwitz coordinate of `x` is integral at every place
(`coordMap_mem_of_mem_localSpan` through `localOrder_le_localSpan`), hence an integral adele.
Backward: a pure tensor `b_m ⊗ a` with `b_m` Hurwitz and `a` integral is locally integral. -/
theorem forall_toLocal_mem_localOrder_iff
    {x : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ} :
    (∀ w : HeightOneSpectrum (RingOfIntegers ℚ), QMF.toLocal ℚ D w x ∈ localOrder w) ↔
      x ∈ QMF.integralTensor ℚ D hurwitzBasis' := by
  constructor
  · intro h
    refine ⟨fun m => coordMapAdelic (hurwitzBasis'.coord m) x, fun m => ?_, ?_⟩
    · refine mem_integralAdeles_iff.mpr fun w => ?_
      have hφ : ∀ d ∈ hurwitzOrder, ∃ n : ℤ, hurwitzBasis'.coord m d = (n : ℚ) := by
        intro d hd
        rw [hurwitzBasis'_coord]
        exact mem_hurwitzOrder_iff_coords.mp hd _
      have hx := coordMap_mem_of_mem_localSpan (hurwitzBasis'.coord m) hφ
        (localOrder_le_localSpan w _ (h w))
      rwa [← evalAlgHom_coordMapAdelic] at hx
    · show ∑ m, hurwitzBasis' m ⊗ₜ[ℚ] coordMapAdelic (hurwitzBasis'.coord m) x = x
      rw [← Equiv.sum_comp hurwitzIdx fun m => hurwitzBasis' m ⊗ₜ[ℚ]
        coordMapAdelic (hurwitzBasis'.coord m) x]
      refine (Finset.sum_congr rfl fun m _ => ?_).trans (sum_coordMapAdelic x)
      rw [hurwitzBasis'_apply, Equiv.symm_apply_apply, hurwitzBasis'_coord_eq]
  · rintro ⟨a, ha, rfl⟩ w
    rw [map_sum]
    refine sum_mem fun m _ => ?_
    rw [hurwitzBasis'_apply, QMF.toLocal_tmul]
    exact tmul_mem_localOrder (hurwitzBasis_mem _)
      ⟨_, mem_integralAdeles_iff.mp (ha m) w⟩

/-- **`U₀(1)` is compact** ([Buzzard, §9 p. 68]: the level is a compact open subgroup).  It is
the unit group of the everywhere-integral elements, which form a compact set by
`forall_toLocal_mem_localOrder_iff` and `QMF.isCompact_integralTensor`. -/
theorem isCompact_U0 : IsCompact (U0 : Set (QMF.Dfx ℚ D)) := by
  haveI : T2Space (D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) :=
    IsModuleTopology.t2Space (FiniteAdeleRing (RingOfIntegers ℚ) ℚ)
  have hset : (U0 : Set (QMF.Dfx ℚ D))
      = {u : (D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ)ˣ |
          (u : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) ∈
              QMF.integralTensor ℚ D hurwitzBasis' ∧
            ((u⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ)ˣ) :
              D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) ∈
              QMF.integralTensor ℚ D hurwitzBasis'} := by
    ext u
    constructor
    · intro hu
      exact ⟨forall_toLocal_mem_localOrder_iff.mp fun w => (hu w).1,
        forall_toLocal_mem_localOrder_iff.mp fun w => (hu w).2⟩
    · rintro ⟨h1, h2⟩ w
      exact ⟨forall_toLocal_mem_localOrder_iff.mpr h1 w,
        forall_toLocal_mem_localOrder_iff.mpr h2 w⟩
  rw [hset]
  exact Units.isCompact_of_isCompact (QMF.isCompact_integralTensor ℚ D hurwitzBasis')

/-! ### `U₀(1)` is open -/

/-- `U₀(1)` as a set of units of the everywhere-integral elements. -/
theorem U0_eq_units_integralTensor :
    (U0 : Set (QMF.Dfx ℚ D))
      = {u : (D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ)ˣ |
          (u : D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) ∈
              QMF.integralTensor ℚ D hurwitzBasis' ∧
            ((u⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ)ˣ) :
              D ⊗[ℚ] FiniteAdeleRing (RingOfIntegers ℚ) ℚ) ∈
              QMF.integralTensor ℚ D hurwitzBasis'} := by
  ext u
  constructor
  · intro hu
    exact ⟨forall_toLocal_mem_localOrder_iff.mp fun w => (hu w).1,
      forall_toLocal_mem_localOrder_iff.mp fun w => (hu w).2⟩
  · rintro ⟨h1, h2⟩ w
    exact ⟨forall_toLocal_mem_localOrder_iff.mpr h1 w,
      forall_toLocal_mem_localOrder_iff.mpr h2 w⟩

/-- The integral order is **open**: integrality of the (continuous) Hurwitz coordinates, the
integral adeles being open in `𝔸_f`. -/
theorem isOpen_integralTensor : IsOpen (QMF.integralTensor ℚ D hurwitzBasis') := by
  rw [integralTensor_eq_preimage]
  refine IsOpen.preimage (IsModuleTopology.continuous_of_linearMap coordsAdelic) ?_
  have hpi : {a : Fin (Module.finrank ℚ D) → FiniteAdeleRing (RingOfIntegers ℚ) ℚ |
      ∀ m, a m ∈ FiniteAdeleRing.integralAdeles (RingOfIntegers ℚ) ℚ}
      = Set.univ.pi fun _ =>
        (FiniteAdeleRing.integralAdeles (RingOfIntegers ℚ) ℚ :
          Set (FiniteAdeleRing (RingOfIntegers ℚ) ℚ)) := by
    ext a
    exact ⟨fun h m _ => h m, fun h m => h m (Set.mem_univ m)⟩
  rw [hpi]
  exact isOpen_set_pi Set.finite_univ fun _ _ => QMF.isOpen_integralAdeles ℚ

/-- **`U₀(1)` is open** ([Buzzard, §9 p. 68]). -/
theorem isOpen_U0 : IsOpen (U0 : Set (QMF.Dfx ℚ D)) := by
  rw [U0_eq_units_integralTensor]
  exact Units.isOpen_of_isOpen isOpen_integralTensor

/-! ### The congruence at `3` is clopen -/

/-- The rigidification at `3` is linear over `K₃` (`theta_one_tmul`), which is what makes it
continuous — see `QMF.RigidificationAt.IsCompletionLinear`. -/
instance : QMF.RigidificationAt.IsCompletionLinear ℚ D v₃ where
  equiv_one_tmul z := by
    show theta ν₃ sq_ν₃ ((1 : D) ⊗ₜ[ℚ] z) = _
    rw [theta_one_tmul]
    refine Matrix.ext fun r c => ?_
    fin_cases r <;> fin_cases c <;> simp [Matrix.algebraMap_matrix_apply]

/-- A closed ball around `0` in `K₃` is clopen (ultrametric). -/
theorem isClopen_valued_le {c : K₃} (hc : c ≠ 0) :
    IsClopen {x : K₃ | Valued.v x ≤ Valued.v c} := by
  have h : {x : K₃ | Valued.v x ≤ Valued.v c} = Metric.closedBall (0 : K₃) ‖c‖ := by
    ext x
    simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
    exact Valued.toNormedField.norm_le_iff.symm
  rw [h]
  exact ⟨Metric.isClosed_closedBall,
    IsUltrametricDist.isOpen_closedBall _ (norm_ne_zero_iff.mpr hc)⟩

/-- The `Σ₁(9)`-condition without the `det ≠ 0` clause — a **clopen** subset of `M₂(K₃)`. -/
def Sigma1Set : Set (Matrix (Fin 2) (Fin 2) K₃) :=
  {g | (∀ i j, Valued.v (g i j) ≤ 1) ∧ Valued.v (g 1 0) ≤ γ₉ ∧ Valued.v (g 1 1 - 1) ≤ γ₉}

theorem isClopen_Sigma1Set : IsClopen Sigma1Set := by
  have hnine : (9 : K₃) ≠ 0 := by
    intro h
    have h9 : Valued.v (9 : K₃) = γ₉ := valued_nine_eq
    rw [h, map_zero] at h9
    exact absurd h9.symm (by simp [γ₉])
  have hone : ∀ i j : Fin 2,
      IsClopen {g : Matrix (Fin 2) (Fin 2) K₃ | Valued.v (g i j) ≤ 1} := fun i j => by
    have h : {g : Matrix (Fin 2) (Fin 2) K₃ | Valued.v (g i j) ≤ 1}
        = (fun g : Matrix (Fin 2) (Fin 2) K₃ => g i j) ⁻¹'
          {x : K₃ | Valued.v x ≤ Valued.v (1 : K₃)} := by
      rw [map_one]
      rfl
    rw [h]
    exact (isClopen_valued_le one_ne_zero).preimage (continuous_apply_apply i j)
  have hc : IsClopen {g : Matrix (Fin 2) (Fin 2) K₃ | Valued.v (g 1 0) ≤ γ₉} := by
    have h : {g : Matrix (Fin 2) (Fin 2) K₃ | Valued.v (g 1 0) ≤ γ₉}
        = (fun g : Matrix (Fin 2) (Fin 2) K₃ => g 1 0) ⁻¹'
          {x : K₃ | Valued.v x ≤ Valued.v (9 : K₃)} := by
      rw [valued_nine_eq]
      rfl
    rw [h]
    exact (isClopen_valued_le hnine).preimage (continuous_apply_apply 1 0)
  have hd : IsClopen {g : Matrix (Fin 2) (Fin 2) K₃ | Valued.v (g 1 1 - 1) ≤ γ₉} := by
    have h : {g : Matrix (Fin 2) (Fin 2) K₃ | Valued.v (g 1 1 - 1) ≤ γ₉}
        = (fun g : Matrix (Fin 2) (Fin 2) K₃ => g 1 1 - 1) ⁻¹'
          {x : K₃ | Valued.v x ≤ Valued.v (9 : K₃)} := by
      rw [valued_nine_eq]
      rfl
    rw [h]
    exact (isClopen_valued_le hnine).preimage
      ((continuous_apply_apply 1 1).sub continuous_const)
  have hall : Sigma1Set
      = (⋂ i, ⋂ j, {g : Matrix (Fin 2) (Fin 2) K₃ | Valued.v (g i j) ≤ 1})
        ∩ ({g : Matrix (Fin 2) (Fin 2) K₃ | Valued.v (g 1 0) ≤ γ₉}
          ∩ {g : Matrix (Fin 2) (Fin 2) K₃ | Valued.v (g 1 1 - 1) ≤ γ₉}) := by
    ext g
    simp only [Sigma1Set, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [hall]
  exact (isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j =>
    hone i j).inter (hc.inter hd)

/-- On matrices with nonzero determinant — in particular on every `toMatrix` of a unit — the
`Σ₁(9)` condition is the clopen one.  (`v (g₁₁ − 1) ≤ γ₉ < 1` already forces `v g₁₁ = 1`.) -/
theorem mem_Sigma1_iff_of_det_ne_zero {g : Matrix (Fin 2) (Fin 2) K₃} (hdet : g.det ≠ 0) :
    g ∈ Sigma1 ↔ g ∈ Sigma1Set := by
  constructor
  · rintro ⟨⟨hint, hc, -, -⟩, hd⟩
    exact ⟨hint, hc, hd⟩
  · rintro ⟨hint, hc, hd⟩
    have h11 : Valued.v (g 1 1) = 1 := by
      have hlt : Valued.v (g 1 1 - 1) < 1 := lt_of_le_of_lt hd γ₉_lt_one
      have : Valued.v ((1 : K₃) + (g 1 1 - 1)) = Valued.v (1 : K₃) := by
        refine Valuation.map_add_eq_of_lt_left _ ?_
        rwa [map_one]
      rwa [add_sub_cancel, map_one] at this
    exact ⟨⟨hint, hc, h11, hdet⟩, hd⟩

/-! ### `U₁(9)` is compact open, and Hecke finiteness -/

/-- `U₁(9)` as an intersection of `U₀(1)` with two clopen congruence conditions. -/
theorem U1_9_eq_inter :
    (U1_9 : Set (QMF.Dfx ℚ D))
      = ((U0 : Set (QMF.Dfx ℚ D)) ∩ (QMF.toMatrix ℚ D v₃ ⁻¹' Sigma1Set))
        ∩ ((fun g : QMF.Dfx ℚ D => QMF.toMatrix ℚ D v₃ g⁻¹) ⁻¹' Sigma1Set) := by
  ext g
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  rw [← mem_Sigma1_iff_of_det_ne_zero (QMF.toMatrix_det_ne_zero ℚ D v₃ g),
    ← mem_Sigma1_iff_of_det_ne_zero (QMF.toMatrix_det_ne_zero ℚ D v₃ g⁻¹)]
  exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

/-- **`U₁(9)` is compact** ([Jacobs, Def 1.20]; [Buzzard, §9 p. 68]). -/
theorem isCompact_U1_9 : IsCompact (U1_9 : Set (QMF.Dfx ℚ D)) := by
  rw [U1_9_eq_inter]
  refine (isCompact_U0.inter_right ?_).inter_right ?_
  · exact isClopen_Sigma1Set.isClosed.preimage (QMF.continuous_toMatrix ℚ D v₃)
  · exact isClopen_Sigma1Set.isClosed.preimage
      ((QMF.continuous_toMatrix ℚ D v₃).comp continuous_inv)

/-- **`U₁(9)` is open** ([Jacobs, Def 1.20]; [Buzzard, §9 p. 68]). -/
theorem isOpen_U1_9 : IsOpen (U1_9 : Set (QMF.Dfx ℚ D)) := by
  rw [U1_9_eq_inter]
  refine (isOpen_U0.inter ?_).inter ?_
  · exact isClopen_Sigma1Set.isOpen.preimage (QMF.continuous_toMatrix ℚ D v₃)
  · exact isClopen_Sigma1Set.isOpen.preimage
      ((QMF.continuous_toMatrix ℚ D v₃).comp continuous_inv)

/-- **Hecke finiteness at `U₁(9)`, from compact-openness alone** ([Buzzard, §9 p. 69]:
"`UηU = ∐ U x_i`, a finite union").  The fork's `finite_image_eta3` proves the same statement
for `η = η₃` by exhibiting the representatives — that explicit form is what computes the
matrix; this one needs no representatives and holds for every `η`. -/
theorem finite_image_doubleCoset_U1_9 (g : QMF.Dfx ℚ D) :
    (((Quotient.mk'' : QMF.Dfx ℚ D → RightCosets U1_9) ''
      (({g} : Set (QMF.Dfx ℚ D)) * (U1_9 : Set (QMF.Dfx ℚ D)))) :
      Set (RightCosets U1_9)).Finite :=
  finite_image_doubleCoset_of_isOpen_of_isCompact isOpen_U1_9 isCompact_U1_9 g

end JacobsSlash
