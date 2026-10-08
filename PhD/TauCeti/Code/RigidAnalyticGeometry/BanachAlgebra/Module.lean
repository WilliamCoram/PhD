/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Topology.MetricSpace.Ultra.Pi
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Noetherian.Basic
import PhD.TauCeti.Code.RigidAnalyticGeometry.BanachAlgebra.Noetherian

/-!
# Submodules of finite modules over a noetherian Banach algebra are closed

Layer 2 support (BGR 3.7.2/2 in its module form and 3.7.3/1), the module version of Layer 1's
`Ideal.isClosed_of_isNoetherianRing`: over a noetherian `K`-Banach algebra `A` every `A`-submodule
of `Aⁿ` is closed (Nakayama for the unit ball + the open mapping theorem, exactly as in
`BanachAlgebra/Noetherian.lean`), hence every submodule of a complete finite normed `A`-module is
closed. Needed by BGR 3.8.3/7 (closedness of `A` in `Bⁿ`) and by 6.2.4/1 (closedness of a reduced
affinoid algebra in `⊕ A ⧸ 𝔭ᵢ`).

## Main declarations

* `Submodule.isClosed_of_isNoetherianRing_pi`: BGR 3.7.2/2 for `Fin n → A`.
* `Submodule.isClosed_of_isNoetherianRing_of_finite`: BGR 3.7.3/1 (every submodule of a complete
  finite normed `A`-module with continuous scalar multiplication is closed).
-/

open Filter Topology Subring NormedRing

variable (K : Type*) [NontriviallyNormedField K] {A : Type*} [NormedCommRing A]
  [NormedAlgebra K A] [CompleteSpace A] [IsUltrametricDist A] [NormOneClass A] [IsNoetherianRing A]

omit [IsNoetherianRing A] in
/-- Nakayama for the unit ball in `Aⁿ` (the module form of
`Ideal.forall_mem_of_forall_exists_eq_add_sum_mul_of_norm_lt_one`): if finitely many vectors
`x i` of `Aⁿ` lie in `N + Σ 𝔞 x μ` with `𝔞` the open unit ball ideal, they lie in `N`. -/
theorem Submodule.forall_mem_of_forall_exists_eq_add_sum_smul_of_norm_lt_one {n m : ℕ}
    (N : Submodule A (Fin n → A)) (x : Fin m → Fin n → A)
    (h : ∀ i, ∃ y ∈ N, ∃ c : Fin m → A, (∀ μ, ‖c μ‖ < 1) ∧ x i = y + ∑ μ, c μ • x μ) :
    ∀ i, x i ∈ N := by
  let N' : Submodule (unitClosedBall A) (Fin n → A) := Submodule.span _ (Set.range x)
  let N₀ : Submodule (unitClosedBall A) (Fin n → A) := N.restrictScalars (unitClosedBall A)
  have hle : N' ≤ N₀ ⊔ openUnitBallIdeal A • N' := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨y, hy, c, hc, hxi⟩ := h i
    rw [SetLike.mem_coe, hxi]
    refine Submodule.add_mem_sup hy (Submodule.sum_mem _ fun μ _ ↦ ?_)
    have hmem : c μ ∈ unitClosedBall A := mem_unitClosedBall.2 (hc μ).le
    have hcx : c μ • x μ = (⟨c μ, hmem⟩ : unitClosedBall A) • x μ := rfl
    rw [hcx]
    exact Submodule.smul_mem_smul (mem_openUnitBallIdeal.2 (hc μ))
      (Submodule.subset_span ⟨μ, rfl⟩)
  have hN := Submodule.le_of_le_smul_of_le_jacobson_bot (Submodule.fg_span (Set.finite_range x))
    openUnitBallIdeal_le_jacobson_bot hle
  exact fun i ↦ hN (Submodule.subset_span ⟨i, rfl⟩)

omit [IsUltrametricDist A] [NormOneClass A] [IsNoetherianRing A] in
include K in
/-- Open mapping for a finitely generated closed submodule `N = span (range x)` of `Aⁿ`: every
`z ∈ N` is `Σ aᵢ • xᵢ` with `max ‖aᵢ‖ ≤ C ‖z‖` (the module form of
`Ideal.exists_forall_exists_eq_sum_mul_norm_le`). -/
theorem Submodule.exists_forall_exists_eq_sum_smul_norm_le {n m : ℕ} (x : Fin m → Fin n → A)
    (N : Submodule A (Fin n → A)) (hN : IsClosed (N : Set (Fin n → A)))
    (hx : Submodule.span A (Set.range x) = N) :
    ∃ C : ℝ, ∀ z ∈ N, ∃ a : Fin m → A, z = ∑ i, a i • x i ∧ ∀ i, ‖a i‖ ≤ C * ‖z‖ := by
  let Nk : Submodule K (Fin n → A) := N.restrictScalars K
  haveI : CompleteSpace Nk := (show IsClosed (Nk : Set (Fin n → A)) from hN).completeSpace_coe
  have hmem : ∀ a : Fin m → A, ∑ i, a i • x i ∈ N := fun a ↦
    N.sum_mem fun i _ ↦ N.smul_mem _ (hx ▸ Submodule.subset_span ⟨i, rfl⟩)
  let πl : (Fin m → A) →ₗ[K] Nk :=
    { toFun := fun a ↦ ⟨∑ i, a i • x i, hmem a⟩
      map_add' := fun a b ↦ Subtype.ext (by simp [add_smul, Finset.sum_add_distrib])
      map_smul' := fun c a ↦ Subtype.ext (by simp [Finset.smul_sum, smul_assoc]) }
  have hcont : Continuous πl :=
    Continuous.subtype_mk (continuous_finsetSum _ fun i _ ↦
      (continuous_apply i).smul continuous_const) _
  let π : (Fin m → A) →L[K] Nk := ⟨πl, hcont⟩
  have hsurj : Function.Surjective π := by
    rintro ⟨z, hz⟩
    have hz' : z ∈ Submodule.span A (Set.range x) := hx ▸ hz
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hz'
    exact ⟨a, Subtype.ext ha⟩
  obtain ⟨C, -, hC⟩ := ContinuousLinearMap.exists_preimage_norm_le π hsurj
  refine ⟨C, fun z hz ↦ ?_⟩
  obtain ⟨a, ha, hna⟩ := hC ⟨z, hz⟩
  exact ⟨a, (congrArg Subtype.val ha).symm, fun i ↦ (norm_le_pi_norm a i).trans hna⟩

include K in
/-- **BGR 3.7.2/2 (module form)**: every submodule of `Aⁿ` over a noetherian Banach algebra is
closed. -/
theorem Submodule.isClosed_of_isNoetherianRing_pi {n : ℕ} (N : Submodule A (Fin n → A)) :
    IsClosed (N : Set (Fin n → A)) := by
  -- the closure of `N` is finitely generated (BGR 3.7.2/1)
  haveI : IsNoetherian A (Fin n → A) := isNoetherian_pi
  obtain ⟨m, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    (IsNoetherian.noetherian N.topologicalClosure)
  obtain ⟨C, hC⟩ := Submodule.exists_forall_exists_eq_sum_smul_norm_le K x N.topologicalClosure
    N.isClosed_topologicalClosure hx
  have hC'0 : 0 < max C 1 := lt_max_of_lt_right one_pos
  -- each generator is close to `N`, so lies in `N` by Nakayama
  have hxN : ∀ i, x i ∈ N := by
    refine Submodule.forall_mem_of_forall_exists_eq_add_sum_smul_of_norm_lt_one N x fun i ↦ ?_
    have hxi : x i ∈ N.topologicalClosure := hx ▸ Submodule.subset_span ⟨i, rfl⟩
    have hxi' : x i ∈ _root_.closure (N : Set (Fin n → A)) := by
      rwa [← Submodule.topologicalClosure_coe]
    obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.1 hxi' (max C 1)⁻¹ (inv_pos.2 hC'0)
    obtain ⟨c, hc, hcn⟩ := hC _ (N.topologicalClosure.sub_mem hxi (N.le_topologicalClosure hy))
    refine ⟨y, hy, c, fun μ ↦ ?_, ?_⟩
    · calc ‖c μ‖ ≤ C * ‖x i - y‖ := hcn μ
        _ ≤ max C 1 * ‖x i - y‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ < max C 1 * (max C 1)⁻¹ := mul_lt_mul_of_pos_left (by rwa [← dist_eq_norm]) hC'0
        _ = 1 := mul_inv_cancel₀ hC'0.ne'
    · rw [← hc]
      abel
  refine isClosed_of_closure_subset fun z hz ↦ ?_
  have hz' : z ∈ N.topologicalClosure := by
    rwa [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  rw [← hx] at hz'
  exact (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hxN i)) hz'

section FiniteModule

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace K M] [Module A M] [IsScalarTower K A M]
  [CompleteSpace M] [ContinuousSMul A M]

omit [IsUltrametricDist A] [NormOneClass A] [IsNoetherianRing A] [ContinuousSMul A M] in
include K in
/-- A continuous surjective `K`-linear map from the Banach space `Aⁿ` onto `M` is open, so a
submodule of `M` is closed as soon as its preimage in `Aⁿ` is. -/
theorem Submodule.isClosed_of_isClosed_comap {n : ℕ} (π : (Fin n → A) →ₗ[A] M)
    (hπ : Continuous π) (hs : Function.Surjective π) (N : Submodule A M)
    (hN : IsClosed ((N.comap π : Submodule A (Fin n → A)) : Set (Fin n → A))) :
    IsClosed (N : Set M) := by
  -- Banach's open mapping theorem: `π` is a quotient map
  let πk : (Fin n → A) →L[K] M := ⟨π.restrictScalars K, hπ⟩
  have hq : Topology.IsQuotientMap π :=
    (ContinuousLinearMap.isOpenMap πk hs).isQuotientMap hπ hs
  exact hq.isClosed_preimage.1 hN

include K in
/-- **BGR 3.7.3/1**: every submodule of a complete finite normed module over a noetherian Banach
algebra is closed. -/
theorem Submodule.isClosed_of_isNoetherianRing_of_finite [Module.Finite A M] (N : Submodule A M) :
    IsClosed (N : Set M) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' A M
  have hcont : Continuous π := by
    have h : (π : (Fin n → A) → M) = fun a ↦ ∑ i, a i • π fun j ↦ if i = j then 1 else 0 :=
      funext (LinearMap.pi_apply_eq_sum_univ π)
    rw [h]
    exact continuous_finsetSum _ fun i _ ↦ (continuous_apply i).smul continuous_const
  exact Submodule.isClosed_of_isClosed_comap K π hcont hπ N
    (Submodule.isClosed_of_isNoetherianRing_pi K _)

end FiniteModule
