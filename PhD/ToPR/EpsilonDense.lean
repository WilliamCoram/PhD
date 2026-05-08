import Mathlib

variable (G H : Type*) [SeminormedGroup G] (H : Subgroup G)

namespace SeminormedGroup

-- note the definition only makes sense for ε in (0,1)

-- BGR defines this using ‖g * h‖ however, we would like to view this as the dist on the LHS
-- this is fine as if there exists h such ‖g * h‖ ≤ ε * ‖g‖
-- we can write h = (h')⁻¹ and then
-- ‖g * h'⁻¹‖ ≤ ε * ‖g‖ or ‖g⁻¹ * h'‖ ≤ ε * ‖g‖ and the LHS is dist g h'

@[to_additive]
def epsilonDense (ε : ℝ) : Prop := ∀ g : G, ∃ h : H, ‖g⁻¹ * (h : G)‖ ≤ ε * ‖g‖

lemma closure_eq : closure (H : Set G) = {x | Metric.infDist x (H : Set G) = 0} := by
  ext; exact Metric.mem_closure_iff_infDist_zero ⟨1, H.one_mem⟩

lemma dense_epsilonDense (ε : ℝ) (hε : ε ∈ Set.Ioo 0 1) (Hd : SeminormedGroup.epsilonDense G H ε) :
    Dense (H : Set G) := by
  suffices ∀ x : G, Metric.infDist x H = 0 by
    simp [dense_iff_closure_eq, closure_eq, this]
  by_contra
  simp only [not_forall] at this
  obtain ⟨g, hg⟩ := this
  have hg : 0 < Metric.infDist g H := by
    grind [Metric.infDist_nonneg]
  obtain ⟨h₁, h₁_lt⟩ : ∃ h₁ : H, ‖g⁻¹ * h₁‖ < ε⁻¹ * Metric.infDist g H := by
    obtain ⟨y, hy, hyd⟩ := (Metric.infDist_lt_iff ⟨1, H.one_mem⟩).mp (show Metric.infDist g H < ε⁻¹
      * Metric.infDist g H by nlinarith [(one_lt_inv₀ hε.1).mpr hε.2])
    exact ⟨⟨y, hy⟩, by rwa [← dist_eq]⟩
  obtain ⟨h₂, h₂_le⟩ := Hd ((h₁ : G)⁻¹ * g)
  have : ‖g⁻¹ * (h₁ * h₂)‖ < Metric.infDist g H := by
    calc ‖g⁻¹ * ((h₁ : G) * h₂)‖
        = ‖((h₁ : G)⁻¹ * g)⁻¹ * h₂‖ := by group
      _ ≤ ε * ‖(h₁ : G)⁻¹ * g‖ := h₂_le
      _ = ε * ‖g⁻¹ * (h₁ : G)‖ := by rw [← dist_eq, dist_comm, dist_eq]
      _ < ε * (ε⁻¹ * Metric.infDist g H) := by gcongr; exact hε.1
      _ = Metric.infDist g H := by grind
  have : Metric.infDist g H ≤ ‖g⁻¹ * (h₁ * h₂)‖ := by
    simpa [← dist_eq] using Metric.infDist_le_dist_of_mem (x := g) (s := H) (y := h₁ * h₂) (by aesop)
  grind
