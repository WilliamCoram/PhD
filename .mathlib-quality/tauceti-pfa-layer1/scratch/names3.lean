import Mathlib
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.Examples
open Filter Topology
open scoped ENNReal
#check @Real.iSup_nonneg
#check @Real.iSup_of_isEmpty
#check @Finset.univ_sum_single
#check @Pi.single_smul
#check @Pi.single_smul'
#check @LinearMap.continuous_of_bound
#check @completeSpace_coe_iff_isComplete
#check @Submodule.le_topologicalClosure
#check @Submodule.topologicalClosure_coe
#check @Submodule.topologicalClosure_minimal
#check @Units.inv_eq_of_mul_eq_one_right
#check @Units.inv_unique
#check @IsUnit.unit
#check @Padic.norm_p_lt_one
#check @norm_fst_le
#check @norm_snd_le
#check @Prod.norm_def
#check @ciSup_le'
#check @Real.sSup_nonneg
#check @LinearMap.mkContinuous_apply
#check @LinearMap.mkContinuous_norm_le
#check @LinearEquiv.ofBijective_apply
#check @Function.LeftInverse
#check @IsOpenMap.isQuotientMap
#check @Metric.mem_closure_iff
#check @NormedRing.norm_one_sub_of_norm_lt_one
#check @NormedRing.isUnit_of_norm_one_sub_lt_one
#check @Summable.hasSum
#check @HasSum.tsum_eq
#check @HasSum.map
#check @ContinuousLinearMap.Ultra.le_opNorm
#check @ContinuousLinearMap.Ultra.instNormedRing
#check @Submodule.isClosed_of_isNoetherianRing
#check @lp.single_apply
#check @lp.norm_apply_le_norm
#check @lp.norm_le_of_forall_le
#check @lp.inftyNormedCommRing
#check @lp.inftyNormedAlgebra
#check @mul_le_of_le_one_left
#check @mul_le_of_le_one_right
#check @norm_smul
#check @ContinuousLinearMap.norm_id
#check @Metric.ball_subset_closedBall
#check @ContinuousLinearMap.isClosed_ker
#check @IsClosed.completeSpace_coe
#check @Submodule.Quotient.norm_mk_lt
#check @Submodule.Quotient.mk_surjective
#check @LinearMap.quotKerEquivRange_apply_mk
#check @LinearMap.quotKerEquivRange_symm_apply_image
#check @Filter.Tendsto.bddAbove_range
#check @nonempty_interior_of_iUnion_of_closed
#check @Nat.cast_le
#check @Padic.norm_p_pow
#check @NormedRing.PseudoUniformizer.existsUnique_zpow_norm_smul_mem_Ioc
#check @NormedRing.PseudoUniformizer.norm_zpow_smul
#check @Module.Finite.exists_fin'
#check @Submodule.fg_iff_exists_fin_generating_family
#check @IsNoetherian.noetherian
#check @isNoetherian_of_isNoetherianRing_of_finite
#check @Submodule.le_of_le_smul_of_le_jacobson_bot
#check @NormedRing.openUnitBallIdeal_le_jacobson_bot
#check @IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
#check @pi_eq_sum_univ
#check @Pi.norm_single
#check @norm_le_pi_norm
#check @Units.val_oneSub
#check @Units.oneSub
#check @Units.isOpen
#check @NormedRing.norm_tsum_geometric
#check @geom_series_mul_neg
#check @mul_neg_geom_series
#check @summable_geometric_of_norm_lt_one
#check @tsum_geometric_two
#check @norm_tsum_le_tsum_norm
#check @HasSum.tendsto_sum_nat
#check @LinearEquiv.ofLeftInverse
#check @LinearMap.graph_eq_range_prod
#check @IsSeqClosed.isClosed
#check @MetricSpace.ext
#check @PseudoMetricSpace.ext
-- the trivial-ring / instance sanity checks for the skeleton
section
open scoped ContinuousLinearMap.Ultra
variable {R M N : Type*} [NormedRing R] [NormOneClass R] [NormedRing.IsTate R] [NormedAddCommGroup M]
  [Module R M] [IsBoundedSMul R M] [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  [IsUltrametricDist N] [CompleteSpace N]
#synth NormedAddCommGroup (M →L[R] N)
#synth IsUltrametricDist (M →L[R] N)
#synth CompleteSpace (M →L[R] N)
#synth NormedRing (M →L[R] M)
#synth HasSummableGeomSeries (M →L[R] N)
end
