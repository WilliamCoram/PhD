/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Topology.Baire.CompleteMetrizable
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.Norm

/-!
# The Banach–Steinhaus theorem over a Tate normed ring

A pointwise bounded family of bounded operators out of a Banach module over a Tate normed ring is
uniformly bounded. The proof is the Baire category argument: the closed sets
`{x | ∀ i, ‖uᵢ x‖ ≤ n}` cover `M`, one of them contains a ball, and the scaling trick
(`norm_map_le_div_mul_of_forall_norm_le`) turns a bound on a ball into a bound on the norm, in
place of the scalar division of the field case. Consequently a pointwise limit of bounded
operators out of a Banach module is bounded.

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, §1.2.4. Tau Ceti home:
`TauCeti/Analysis/Normed/Operator/Ultra/BanachSteinhaus.lean`.

## Main results

* `ContinuousLinearMap.Ultra.banach_steinhaus` — the uniform boundedness principle.
* `ContinuousLinearMap.Ultra.continuous_of_tendsto` — pointwise limits are continuous.
-/

open Filter Topology

namespace ContinuousLinearMap.Ultra

open NormedRing

variable {R M N : Type*} [NormedRing R] [NormOneClass R] [IsTate R] [NormedAddCommGroup M]
  [Module R M] [IsBoundedSMul R M] [CompleteSpace M] [NormedAddCommGroup N] [Module R N]
  [IsBoundedSMul R N]

/-- **Banach–Steinhaus.** Source: roadmap §1.2.4; Schneider, Proposition 6.15 ("If `V` is barrelled
then any bounded subset `H ⊆ L_s(V, W)` is equicontinuous") with Example 2 after Corollary 6.16
("If `V` is metrizable and is complete ... then `V` is barrelled. Proof: By Baire's theorem");
Mathlib, `banach_steinhaus`. -/
theorem banach_steinhaus {ι : Type*} (u : ι → M →L[R] N) (h : ∀ x, ∃ C, ∀ i, ‖u i x‖ ≤ C) :
    ∃ C, ∀ i, ‖u i‖ ≤ C := by
  obtain ⟨ϖ⟩ := IsTate.exists_pseudoUniformizer (R := R)
  let A : ℕ → Set M := fun n ↦ ⋂ i, {x | ‖u i x‖ ≤ n}
  have hA (n : ℕ) : IsClosed (A n) :=
    isClosed_iInter fun i ↦ isClosed_le (continuous_norm.comp (u i).continuous) continuous_const
  have hcover : ⋃ n, A n = Set.univ := by
    refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨C, hC⟩ := h x
    obtain ⟨n, hn⟩ := exists_nat_ge C
    exact Set.mem_iUnion.2 ⟨n, Set.mem_iInter.2 fun i ↦ (hC i).trans hn⟩
  obtain ⟨n, x₀, hx₀⟩ := nonempty_interior_of_iUnion_of_closed hA hcover
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx₀
  obtain ⟨ε, εpos, hε⟩ := hx₀
  refine ⟨2 * n / (ε / 2 * ‖(ϖ : R)‖), fun i ↦
    opNorm_le_div_of_forall_norm_le ϖ (u i) (half_pos εpos) fun y hy ↦ ?_⟩
  have h₁ : ‖u i (x₀ + y)‖ ≤ n :=
    Set.mem_iInter.1 (hε (by rw [Metric.mem_ball, dist_self_add_left]; linarith)) i
  have h₂ : ‖u i x₀‖ ≤ n := Set.mem_iInter.1 (hε (Metric.mem_ball_self εpos)) i
  calc ‖u i y‖ = ‖u i (x₀ + y) - u i x₀‖ := by rw [map_add, add_sub_cancel_left]
    _ ≤ ‖u i (x₀ + y)‖ + ‖u i x₀‖ := norm_sub_le _ _
    _ ≤ n + n := add_le_add h₁ h₂
    _ = 2 * n := by ring

/-- Source: roadmap §1.2.4 ("a pointwise limit of continuous linear maps from a Banach module is
continuous"); Mathlib, `continuousLinearMapOfTendsto`. -/
theorem continuous_of_tendsto (u : ℕ → M →L[R] N) (f : M →ₗ[R] N)
    (h : ∀ x, Tendsto (fun n ↦ u n x) atTop (𝓝 (f x))) : Continuous f := by
  obtain ⟨C, hC⟩ := banach_steinhaus u fun x ↦ by
    obtain ⟨C, hC⟩ := (h x).norm.bddAbove_range
    exact ⟨C, fun n ↦ hC ⟨n, rfl⟩⟩
  refine AddMonoidHomClass.continuous_of_bound f C fun x ↦ ?_
  exact le_of_tendsto (h x).norm (Eventually.of_forall fun n ↦
    (le_opNorm (u n) x).trans (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg x)))

end ContinuousLinearMap.Ultra
