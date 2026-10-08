import Mathlib
open Filter Topology
-- §0.1
#check @NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero
#check @NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
#check @NonarchimedeanAddGroup.cauchySeq_sum_of_tendsto_cofinite_zero
#check @IsUltrametricDist.nonarchimedeanAddGroup
#check @IsUltrametricDist.norm_tsum_le
#check @IsUltrametricDist.nnnorm_tsum_le
#check @IsUltrametricDist.norm_tsum_le_of_forall_le
#check @IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
#check @IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
#check @IsUltrametricDist.norm_add_le_max
#check @IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
#check @IsUltrametricDist.exists_norm_finsetSum_le
#check @Filter.Tendsto.bddAbove_range_of_cofinite
#check @Summable.tendsto_cofinite_zero
#check @HasSum.prod_fiberwise
#check @Summable.tsum_prod'
#check @Summable.prod_factor
#check @HasSum.mul_of_nonarchimedean
#check @tsum_mul_tsum_of_nonarchimedean
#check @Summable.mul_of_nonarchimedean
#check @Filter.coprod_cofinite
#check @Function.Injective.tendsto_cofinite
#check @HasSum.map
#check @Summable.tsum_sub
#check @Summable.tsum_eq_add_tsum_ite
#check @Summable.tsum_eq_add_tsum_ite'
#check @tsum_eq_add_tsum_ite
#check @Set.Finite.exists_maximal_wrt
#check @Finite.exists_max
#check @tendsto_norm_zero
#check @tendsto_zero_iff_norm_tendsto_zero
-- §0.2
#check @IsTopologicallyNilpotent
#check @topologicalNilradical
#check @mem_topologicalNilradical_iff
#check @Units.oneSub
#check @NormedRing.tsum_geometric_of_norm_lt_one
#check @NormedRing.summable_geometric_of_norm_lt_one
#check @geom_series_mul_neg
#check @mul_neg_geom_series
#check @Ideal.jacobson
#check @Ideal.mem_jacobson_bot
#check @IsLocalRing
#check @IsLinearTopology
#check @tendsto_pow_atTop_nhds_zero_of_norm_lt_one
#check @tendsto_pow_atTop_nhds_zero_iff_norm_lt_one
#check @NormedRing.inverse_one_sub
-- §0.3
#check @Submodule.Quotient.normedAddCommGroup
#check @Submodule.Quotient.completeSpace
#check @Submodule.Quotient.instIsBoundedSMul
#check @Submodule.Quotient.norm_mk_le
#check @QuotientAddGroup.norm_lt_iff
#check @QuotientAddGroup.le_norm_iff
#check @Pi.instIsUltrametricDist
#check @IsUltrametricDist.subtype
#check @IsClosed.completeSpace_coe
#check @completeSpace_congr
#check @AntilipschitzWith.isUniformInducing
#check @AntilipschitzWith.isUniformEmbedding
#check @LipschitzWith.uniformContinuous
#check @AddMonoidHomClass.lipschitz_of_bound
#check @AddMonoidHomClass.antilipschitz_of_bound
#check @exists_mem_Ico_zpow
#check @exists_mem_Ioc_zpow
#check @zpow_lt_zpow_iff_right_of_lt_one₀
#check @zpow_le_zpow_iff_right_of_lt_one₀
-- §0.4
#check @NormedField.exists_norm_lt_one
#check @norm_algebraMap'
#check @IsAdic
#check @isAdic_iff
#check @Ideal.span_singleton_pow
#check @Ideal.mem_span_singleton
#check @IsUltrametricDist.isOpen_closedBall
#check @Subring.module
#check @PadicInt.isUnit_iff
#check @PadicInt.norm_le_one
#check @IsAlgClosed.exists_pow_nat_eq
#check @PadicComplex.norm_extends
example (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) :
    Module (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)) := inferInstance
example (E F : Type*) [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [IsUltrametricDist E]
    [IsUltrametricDist F] : IsUltrametricDist (E × F) := inferInstance
example (R M : Type*) [NormedRing R] [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
    (S : Submodule R M) : IsBoundedSMul R S := inferInstance
example (R M : Type*) [NormedRing R] [NormedAddCommGroup M] [Module R M] [IsUltrametricDist M]
    (S : Submodule R M) : IsUltrametricDist S := inferInstance
example (R : Type*) [NormedRing R] (S : Subring R) : NormedRing S := inferInstance
example (R : Type*) [NormedCommRing R] (S : Subring R) : NormedCommRing S := inferInstance
example (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] (S : Subring R) : Module S M :=
  inferInstance
