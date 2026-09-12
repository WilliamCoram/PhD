import Mathlib.Topology.MetricSpace.HausdorffDistance

open NNReal ENNReal Topology Set Filter Pointwise Bornology

universe u v w

variable {ι : Sort*} {α : Type u} {β : Type v}

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {s t u : Set α} {x y : α} {Φ : α → β}

open Metric

/-- Let `G` be a group with a left-invariant pseudometric. If a subgroup `H` is `ε`-dense for
some `ε < 1`, that is `infDist g H ≤ ε * dist g 1` for every `g : G`, then `H` is
dense. This is [BGR, Prop 1.1.4./2][bosch-guntzer-remmert]. -/
@[to_additive]
lemma _root_.Subgroup.dense_of_infDist_le {G : Type*} [Group G] [PseudoMetricSpace G]
    [IsIsometricSMul G G] (H : Subgroup G) (ε : ℝ) (h1 : 0 < ε) (h2 : ε < 1)
    (h : ∀ g : G, infDist g H ≤ ε * dist g 1) : Dense (H : Set G) := by
  simp only [dense_iff_closure_eq, Set.eq_univ_iff_forall, OneMemClass.coe_nonempty,
    mem_closure_iff_infDist_zero]
  intro g
  by_contra hg
  obtain ⟨y, hy, _⟩ : ∃ y ∈ H, dist g y < ε⁻¹ * infDist g H :=
    (infDist_lt_iff ⟨1, H.one_mem⟩).mp ((lt_mul_iff_one_lt_left (lt_of_le_of_ne infDist_nonneg
      (Ne.symm hg))).mpr ((one_lt_inv₀ h1).mpr h2))
  obtain ⟨z, hz, _⟩ : ∃ z ∈ H, dist (y⁻¹ * g) z < infDist g H := by
    refine (infDist_lt_iff ⟨1, H.one_mem⟩).mp (lt_of_le_of_lt (h (y⁻¹ * g)) ?_)
    calc ε * dist (y⁻¹ * g) 1
      _ = ε * dist g y := by rw [← dist_mul_left, mul_inv_cancel_left, mul_one]
      _ < ε * (ε⁻¹ * infDist g H) := by gcongr
      _ = infDist g (H : Set G) := by rw [← mul_assoc, mul_inv_cancel₀ h1.ne', one_mul]
  have : dist g (y * z) < infDist g (H : Set G) := by
    rwa [← dist_mul_left, inv_mul_cancel_left]
  exact absurd this (not_lt.mpr (infDist_le_dist_of_mem (mul_mem hy hz)))
