import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
open Filter Topology
variable {ι E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E]
-- the strict bound with NO nullity hypothesis
example {f : ι → E} {B : ℝ} (hB : 0 < B) (hlt : ∀ i, ‖f i‖ < B) : ‖∑' i, f i‖ < B := by
  by_cases hs : Summable f
  · rcases isEmpty_or_nonempty ι with hι | hι
    · simpa using hB
    have hf : Tendsto f cofinite (𝓝 0) := hs.tendsto_cofinite_zero
    obtain ⟨i₁⟩ := id hι
    by_cases h0 : ∀ i, ‖f i‖ ≤ ‖f i₁‖
    · exact (IsUltrametricDist.norm_tsum_le f).trans_lt ((ciSup_le h0).trans_lt (hlt i₁))
    · push_neg at h0
      obtain ⟨i₂, hi₂⟩ := h0
      have hpos : 0 < ‖f i₂‖ := (norm_nonneg _).trans_lt hi₂
      have hfin : {i | ‖f i₂‖ ≤ ‖f i‖}.Finite := by
        have h1 := (hf.norm).eventually (gt_mem_nhds (show ‖(0 : E)‖ < ‖f i₂‖ by simpa using hpos))
        rw [Filter.eventually_cofinite] at h1
        refine h1.subset fun i hi => ?_
        simpa using hi
      obtain ⟨i₀, hi₀, hmax⟩ := hfin.toFinset.exists_max_image (fun i ↦ ‖f i‖)
        ⟨i₂, by simp⟩
      refine (IsUltrametricDist.norm_tsum_le f).trans_lt ((ciSup_le fun i ↦ ?_).trans_lt (hlt i₀))
      by_cases hi : ‖f i₂‖ ≤ ‖f i‖
      · exact hmax i (by simpa using hi)
      · have h1 : ‖f i₂‖ ≤ ‖f i₀‖ := by simpa using hi₀
        exact (not_le.1 hi).le.trans h1
  · rw [tsum_eq_zero_of_not_summable hs, norm_zero]; exact hB
