import Mathlib
open Filter Topology
#check @Summable.tsum_prod'
#check @Summable.prod_factor
#check @Summable.tsum_comm'
#check @Ideal.mem_jacobson_bot
#check @IsLocalRing.of_nonunits_add
#check @IsLinearTopology.mk_of_hasBasis
#check @isAdic_iff
#check @Ideal.span_singleton_pow
#check @Ideal.mem_span_singleton
#check @Submodule.smul_induction_on
#check @Submodule.smul_mem_smul
#check @Real.rpow_logb
#check @Real.logb_zpow
#check @Real.logb_mul
#check @Real.logb_self_eq_one
#check @Real.logb_pos_iff_of_base_lt_one
#check @Real.logb_nonneg_iff_of_base_lt_one
#check @Int.floor_le
#check @Int.lt_floor_add_one
#check @Int.floor_intCast_add
#check @ZMod.ringHom_surjective
#check @PadicInt.ker_toZMod
#check @Padic.norm_eq_zpow_neg_valuation
#check @IsAlgClosed.exists_pow_nat_eq
#check @PadicComplex.norm_extends
#check @AddMonoidHomClass.continuous_of_bound
#check @HasSum.map
#check @Finset.exists_max_image
#check @norm_pow_le'
#check @Metric.nhds_basis_closedBall
#check @IsUltrametricDist.isOpen_closedBall
#check @Int.norm_eq_abs
#check @RingHom.quotientKerEquivOfSurjective
#check @Ideal.quotEquivOfEq
#check @AddGroupNorm.toNormedAddCommGroup
#check @Monotone.map_max
#check @zpow_le_zpow_right_of_le_one₀
#check @zpow_lt_zpow_right_of_lt_one₀
#check @Real.sInf_nonneg
#check @csInf_le
#check @le_csInf
#check @Filter.Tendsto.norm
#check @squeeze_zero
#check @tendsto_pow_atTop_nhds_zero_of_lt_one
#check @Real.zero_rpow
#check @Real.rpow_le_rpow
#check @NormedField.exists_norm_lt_one
#check @Units.map
#check @norm_algebraMap'
#check @Algebra.smul_def
#check @Subring.coe_mul
#check @PadicInt.isUnit_iff
#check @PadicInt.norm_p
#check @Nat.Prime.one_lt
#check @mul_neg_geom_series
#check @summable_geometric_of_norm_lt_one
#check @Summable.tsum_eq_zero_add
#check @AntilipschitzWith.isUniformEmbedding
#check @IsUniformEmbedding.completeSpace_iff
#check @completeSpace_congr

-- spot proofs of riskier leaves
section
variable {ι E : Type*} [SeminormedAddCommGroup E]
example {f : ι → E} (hf : Tendsto f cofinite (𝓝 0)) : BddAbove (Set.range fun i ↦ ‖f i‖) := by
  have := hf.norm
  rw [norm_zero] at this
  exact this.bddAbove_range_of_cofinite
end
section
variable {ι E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E]
-- the strict bound with NO nullity hypothesis
example {f : ι → E} {B : ℝ} (hB : 0 < B) (hlt : ∀ i, ‖f i‖ < B) : ‖∑' i, f i‖ < B := by
  by_cases hs : Summable f
  · rcases isEmpty_or_nonempty ι with hι | hι
    · simpa using hB
    have hf : Tendsto f cofinite (𝓝 0) := hs.tendsto_cofinite_zero
    have hbdd : BddAbove (Set.range fun i ↦ ‖f i‖) := by
      have := hf.norm; rw [norm_zero] at this; exact this.bddAbove_range_of_cofinite
    -- the sup is attained
    obtain ⟨i₁⟩ := hι
    by_cases h0 : ∀ i, ‖f i‖ ≤ ‖f i₁‖
    · exact (IsUltrametricDist.norm_tsum_le f).trans_lt ((ciSup_le h0).trans_lt (hlt i₁))
    · push_neg at h0
      obtain ⟨i₂, hi₂⟩ := h0
      have hpos : 0 < ‖f i₂‖ := (norm_nonneg _).trans_lt hi₂
      have hfin : {i | ‖f i₂‖ ≤ ‖f i‖}.Finite := by
        have := (hf.norm).eventually (gt_mem_nhds (by simpa using hpos))
        rw [Filter.eventually_cofinite] at this
        refine this.subset fun i hi => ?_
        simpa using hi
      obtain ⟨i₀, hi₀, hmax⟩ := hfin.toFinset.exists_max_image (fun i ↦ ‖f i‖)
        ⟨i₂, by simp⟩
      refine (IsUltrametricDist.norm_tsum_le f).trans_lt ((ciSup_le fun i ↦ ?_).trans_lt (hlt i₀))
      by_cases hi : ‖f i₂‖ ≤ ‖f i‖
      · exact hmax i (by simpa using hi)
      · have h1 : ‖f i₂‖ ≤ ‖f i₀‖ := by simpa using hi₀
        exact (not_le.1 hi).le.trans h1
  · rw [tsum_eq_zero_of_not_summable hs, norm_zero]; exact hB
end
