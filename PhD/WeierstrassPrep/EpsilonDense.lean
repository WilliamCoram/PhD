import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.Topology.MetricSpace.HausdorffDistance

variable {G : Type*} [SeminormedGroup G] (H : Subgroup G)

lemma Metric.closure_eq {α : Type*} [PseudoMetricSpace α] {s : Set α} (h : s.Nonempty) :
    closure s = {x | Metric.infDist x s = 0} := by
  grind [Metric.mem_closure_iff_infDist_zero]

namespace SeminormedGroup

@[to_additive]
def epsilonDense (ε : ℝ) : Prop := ∀ g : G, ∃ h : H, ‖g⁻¹ * (h : G)‖ ≤ ε * ‖g‖

@[to_additive]
lemma epsilonDense_dist_eq_zero {ε : ℝ} (h1 : 0 < ε) (h2 : ε < 1)
    (h : SeminormedGroup.epsilonDense H ε) (g : G) : Metric.infDist g H = 0 := by
  by_contra
  suffices ∃ h₁ : H, ‖g⁻¹ * h₁‖ < ε⁻¹ * Metric.infDist g H by
    obtain ⟨h₁, h₁_lt⟩ := this
    obtain ⟨h₂, h₂_le⟩ := h ((h₁ : G)⁻¹ * g)
    suffices dist g (↑h₁ * ↑h₂) < Metric.infDist g H by
      grind [Metric.infDist_le_dist_of_mem (x := g) (s := H) (y := h₁ * h₂) (by aesop)]
    calc _ = ‖((h₁ : G)⁻¹ * g)⁻¹ * h₂‖ := by rw [dist_eq]; group
         _ ≤ ε * ‖(h₁ : G)⁻¹ * g‖ := h₂_le
         _ = ε * ‖g⁻¹ * (h₁ : G)‖ := by rw [← dist_eq, dist_comm, dist_eq]
         _ < ε * (ε⁻¹ * Metric.infDist g H) := by gcongr
         _ = Metric.infDist g H := by grind
  suffices Metric.infDist g ↑H < ε⁻¹ * Metric.infDist g ↑H by
    obtain ⟨y, hy, _⟩ := (Metric.infDist_lt_iff ⟨1, H.one_mem⟩).mp this
    exact ⟨⟨y, hy⟩, by rwa [← dist_eq]⟩
  exact (lt_mul_iff_one_lt_left (by grind [Metric.infDist_nonneg])).mpr ((one_lt_inv₀ h1).mpr h2)

@[to_additive]
lemma dense_epsilonDense (ε : ℝ) (h1 : 0 < ε) (h2 : ε < 1) (h : SeminormedGroup.epsilonDense H ε) :
    Dense (H : Set G) := by
  simp [dense_iff_closure_eq, Metric.closure_eq, epsilonDense_dist_eq_zero H h1 h2 h]
