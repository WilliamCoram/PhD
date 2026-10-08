/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.Basic

/-!
# Extension of the ground field

For a finite extension `K'` of `K` with a norm extending that of `K` (its spectral norm), the
algebraic tensor product `K' ⊗_K A` of an affinoid `K`-algebra is a `K'`-affinoid algebra, and
`K' ⊗_K Tₙ(K) ≅ Tₙ(K')` (BGR 6.1.1/8–9: "`k′ ⊗̂_k Tₙ(k) ≅ Tₙ(k′)`" and "`k′ ⊗̂_k B` is
`k′`-affinoid"). Since `K'` is finite-dimensional over `K`, the complete tensor product is the
algebraic one (roadmap §1.1.6: "`A ⊗̂_K K' := A ⊗_K K'` (already complete)"); the case of an
arbitrary complete extension is BGR 6.1.1/9 with the completion and is not on this board.

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, §1.1.6. Tau Ceti home:
`TauCeti/RingTheory/Affinoid/BaseChange.lean`.

## Main results

* `Affinoid.TateAlgebra.mapBase`, `Affinoid.TateAlgebra.norm_mapBase` — the isometric inclusion
  `Tₙ(K) → Tₙ(K')`.
* `Affinoid.TateAlgebra.exists_forall_norm_coord_le` — the coordinate functionals of a finite
  extension are bounded.
* `Affinoid.TateAlgebra.baseChangeEquiv` — `K' ⊗[K] Tₙ(K) ≃ₐ[K'] Tₙ(K')` (BGR 6.1.1/8).
* `IsAffinoidAlgebra.baseChange` — `K' ⊗[K] A` is `K'`-affinoid (BGR 6.1.1/9).
* `IsAffinoidAlgebra.baseChange_quotient` — `K' ⊗[K] (A ⧸ 𝔞) ≅ (K' ⊗[K] A) ⧸ 𝔞'` (BGR 6.1.1/12),
  from Mathlib's `Algebra.TensorProduct.tensorQuotientEquiv`.
-/

open MvPowerSeries MvPowerSeries.Restricted TensorProduct

namespace Affinoid.TateAlgebra

variable (K : Type*) [NormedField K] [IsUltrametricDist K]
  (K' : Type*) [NormedField K'] [IsUltrametricDist K'] [NormedAlgebra K K'] [NormOneClass K']
  (n : ℕ)

/-- The coefficientwise inclusion `Tₙ(K) → Tₙ(K')`, as a `K`-algebra homomorphism; it is an
isometry since `‖algebraMap K K' x‖ = ‖x‖`. Source: BGR 6.1.1/8. -/
noncomputable def mapBase : TateAlgebra K n →ₐ[K] TateAlgebra K' n :=
  { Restricted.map (1 : Fin n → ℝ) (φ := algebraMap K K') fun x ↦ (norm_algebraMap' K' x).le with
    commutes' := fun a ↦ Restricted.ext <| by
      change MvPowerSeries.map (algebraMap K K') (algebraMap K (TateAlgebra K n) a).1 =
        (algebraMap K (TateAlgebra K' n) a).1
      rw [algebraMap_apply, algebraMap_eq_C_comp (S := K'), RingHom.comp_apply, val_C, val_C,
        MvPowerSeries.map_C] }

theorem mapBase_apply (f : TateAlgebra K n) :
    (mapBase K K' n f).1 = MvPowerSeries.map (algebraMap K K') f.1 :=
  rfl

theorem norm_mapBase (f : TateAlgebra K n) : ‖mapBase K K' n f‖ = ‖f‖ := by
  have hcoeff : ∀ t, ‖coeff t (mapBase K K' n f).1‖ = ‖coeff t f.1‖ := fun t ↦ by
    rw [mapBase_apply, MvPowerSeries.coeff_map, norm_algebraMap']
  exact le_antisymm
    ((norm_le_iff_forall_norm_coeff_le _).2 fun t ↦ (hcoeff t).trans_le (norm_coeff_le f t))
    ((norm_le_iff_forall_norm_coeff_le _).2 fun t ↦ (hcoeff t).symm.trans_le (norm_coeff_le _ t))

/-- The base-change homomorphism `K' ⊗_K Tₙ(K) → Tₙ(K')`, `c ⊗ f ↦ c • f`. -/
noncomputable def baseChangeAlgHom : K' ⊗[K] TateAlgebra K n →ₐ[K'] TateAlgebra K' n :=
  Algebra.TensorProduct.lift (Algebra.ofId K' (TateAlgebra K' n)) (mapBase K K' n) fun _ _ ↦
    Commute.all _ _

@[simp]
theorem baseChangeAlgHom_tmul (c : K') (f : TateAlgebra K n) :
    baseChangeAlgHom K K' n (c ⊗ₜ f) = c • mapBase K K' n f :=
  (Algebra.TensorProduct.lift_tmul _ _ _ c f).trans (Algebra.smul_def c _).symm

omit [NormOneClass K'] in
/-- The coordinate functionals of a basis of a finite extension `K'` of a complete ultrametric
field `K` are bounded. For a nontrivially normed `K` this is the continuity of linear maps on a
finite-dimensional space (BGR 3.7.1); for a trivially normed `K` every element of `K'` is a root of
a monic polynomial with coefficients of norm at most one, so the norm of `K'` is trivial too
(`norm_root_le_spectralValue`). -/
theorem exists_forall_norm_coord_le [CompleteSpace K] [FiniteDimensional K K'] {ι : Type*}
    (b : Module.Basis ι K K') (k : ι) : ∃ C : ℝ, ∀ x, ‖b.coord k x‖ ≤ C * ‖x‖ := by
  by_cases hK : ∃ c : K, 1 < ‖c‖
  · letI : NontriviallyNormedField K := { ‹NormedField K› with non_trivial := hK }
    obtain ⟨C, -, hC⟩ := SemilinearMapClass.bound_of_continuous (b.coord k)
      (LinearMap.continuous_of_finiteDimensional _)
    exact ⟨C, hC⟩
  · simp only [not_exists, not_lt] at hK
    have hle : ∀ y : K', ‖y‖ ≤ 1 := fun y ↦ by
      have hint : IsIntegral K y := Algebra.IsIntegral.isIntegral y
      have h := norm_root_le_spectralValue
        (f := (NormedAlgebra.toMulAlgebraNorm K K').toAlgebraNorm)
        (MulRingNorm.isPowMul (NormedAlgebra.toMulAlgebraNorm K K').toMulRingNorm)
        IsUltrametricDist.isNonarchimedean_norm (minpoly.monic hint) (minpoly.aeval K y)
      exact h.trans ((spectralValue_le_one_iff (minpoly.monic hint)).2 fun _ ↦ hK _)
    refine ⟨1, fun x ↦ ?_⟩
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    have hx1 : 1 ≤ ‖x‖ := (inv_le_one₀ (norm_pos_iff.2 hx)).1 (norm_inv x ▸ hle x⁻¹)
    rw [one_mul]
    exact (hK _).trans hx1

/-- Every series over `K'` is a finite sum `Σ eₖ • gₖ` with `gₖ ∈ Tₙ(K)`, for a `K`-basis `e` of
`K'`: the coordinate functionals of a finite-dimensional normed space are continuous, so the
coordinates of the coefficients tend to zero. Source: BGR 6.1.1/8, with BGR 3.7.1 ("these
extensions carry always the product topology"). -/
theorem exists_sum_smul_mapBase [CompleteSpace K] {ι : Type*} [Fintype ι] (b : Module.Basis ι K K')
    (g : TateAlgebra K' n) : ∃ h : ι → TateAlgebra K n, g = ∑ k, b k • mapBase K K' n (h k) := by
  haveI : FiniteDimensional K K' := Module.Finite.of_basis b
  choose C hC using fun k ↦ exists_forall_norm_coord_le K K' b k
  refine ⟨fun k ↦ ⟨fun ν ↦ b.coord k (coeff ν g.1),
    isRestricted_mk (fun _ ↦ zero_le_one) (b.coord k) (hC k) g.2⟩, ?_⟩
  refine Restricted.ext (MvPowerSeries.ext fun ν ↦ ?_)
  simp only [val_sum, map_sum, val_smul, MvPowerSeries.coeff_smul]
  conv_lhs => rw [← b.sum_repr (coeff ν g.1)]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [Algebra.smul_def, mul_comm]; rfl

theorem bijective_baseChangeAlgHom [CompleteSpace K] [FiniteDimensional K K'] :
    Function.Bijective (baseChangeAlgHom K K' n) := by
  let b := Module.finBasis K K'
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun g ↦ ?_⟩
  · obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left b x
    rw [Finsupp.sum_fintype _ _ fun i ↦ TensorProduct.tmul_zero _ _] at hx ⊢
    have hcoeff : ∀ i ν, coeff ν (c i).1 = 0 := by
      intro i ν
      have hν := congrArg (fun F : TateAlgebra K' n ↦ coeff ν F.1) hx
      simp only [map_sum, baseChangeAlgHom_tmul, val_sum, val_smul, MvPowerSeries.coeff_smul,
        mapBase_apply, MvPowerSeries.coeff_map, val_zero, map_zero] at hν
      refine Fintype.linearIndependent_iff.1 b.linearIndependent (fun i ↦ coeff ν (c i).1) ?_ i
      rw [← hν]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [Algebra.smul_def, mul_comm]
    have hc : ∀ i, c i = 0 := fun i ↦
      Restricted.ext (MvPowerSeries.ext fun ν ↦ by simp [hcoeff i ν])
    simp [hc]
  · obtain ⟨h, rfl⟩ := exists_sum_smul_mapBase K K' n b g
    exact ⟨∑ k, b k ⊗ₜ h k, by simp only [map_sum, baseChangeAlgHom_tmul]⟩

/-- **BGR 6.1.1/8**: `K' ⊗_K Tₙ(K) ≅ Tₙ(K')` for a finite extension `K'/K`. -/
noncomputable def baseChangeEquiv [CompleteSpace K] [FiniteDimensional K K'] :
    K' ⊗[K] TateAlgebra K n ≃ₐ[K'] TateAlgebra K' n :=
  AlgEquiv.ofBijective _ (bijective_baseChangeAlgHom K K' n)

end Affinoid.TateAlgebra

namespace IsAffinoidAlgebra

open Affinoid

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (K' : Type*) [NormedField K'] [IsUltrametricDist K'] [NormedAlgebra K K'] [NormOneClass K']
  [FiniteDimensional K K'] {A : Type*} [CommRing A] [Algebra K A]

/-- A finite extension of a complete nontrivially normed field is complete. -/
theorem completeSpace_of_finiteDimensional {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    (K' : Type*) [NormedField K'] [NormedAlgebra K K'] [FiniteDimensional K K'] :
    CompleteSpace K' :=
  FiniteDimensional.complete K K'

/-- **BGR 6.1.1/9**: `K' ⊗_K A` is `K'`-affinoid for `A` affinoid over `K` and `K'/K` finite: a
presentation `Tₙ(K) → A` tensors to a surjection `K' ⊗ Tₙ(K) → K' ⊗ A`, and
`K' ⊗ Tₙ(K) ≅ Tₙ(K')`. -/
theorem baseChange (hA : IsAffinoidAlgebra K A) : IsAffinoidAlgebra K' (K' ⊗[K] A) := by
  obtain ⟨n, α, hα⟩ := hA
  have hsurj := Algebra.TensorProduct.map_surjective (f := AlgHom.id K' K') (g := α)
    Function.surjective_id hα
  exact ⟨n, (Algebra.TensorProduct.map (AlgHom.id K' K') α).comp
    (TateAlgebra.baseChangeEquiv K K' n).symm.toAlgHom,
    hsurj.comp (TateAlgebra.baseChangeEquiv K K' n).symm.surjective⟩

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist K'] [NormOneClass K']
  [FiniteDimensional K K'] in
/-- **BGR 6.1.1/12**: `K' ⊗_K (A ⧸ 𝔞) ≅ (K' ⊗_K A) ⧸ 𝔞'` where `𝔞'` is the ideal generated by `𝔞`,
from Mathlib's `Algebra.TensorProduct.tensorQuotientEquiv`. -/
theorem baseChange_quotient (𝔞 : Ideal A) :
    Nonempty ((K' ⊗[K] (A ⧸ 𝔞)) ≃ₐ[K']
      (K' ⊗[K] A) ⧸ 𝔞.map (Algebra.TensorProduct.includeRight (A := K') (R := K))) :=
  ⟨Algebra.TensorProduct.tensorQuotientEquiv K' A K' 𝔞⟩

end IsAffinoidAlgebra
