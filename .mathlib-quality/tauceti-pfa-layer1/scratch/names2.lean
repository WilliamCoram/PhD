import Mathlib
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Examples
import PhD.TauCeti.Code.PadicFunctionalAnalysis.NormComparison
open Filter Topology
open scoped ENNReal ZeroAtInfty

section
variable {R M N : Type*} [NormedRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [IsUltrametricDist M] [CompleteSpace M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N] [IsUltrametricDist N] [CompleteSpace N]
  {ι : Type*} [Fintype ι]
#synth IsUltrametricDist (ι → R)
#synth IsUltrametricDist (M × N)
#synth CompleteSpace (M × N)
#synth CompleteSpace (ι → R)
#synth IsUltrametricDist (Subtype fun x : M => x = x)
#synth Module (Subring.unitClosedBall R) M
#synth IsScalarTower (Subring.unitClosedBall R) R M
#synth BaireSpace M
#synth HasSummableGeomSeries R
example (S : Submodule R M) : Submodule (Subring.unitClosedBall R) M := S.restrictScalars _
#synth TopologicalSpace (M →L[R] N)
#synth Norm (M →L[R] N)
end

section
variable (p : ℕ) [Fact p.Prime]
#synth NormedRing (lp (fun _ : ℕ => ℚ_[p]) ∞)
#synth NormedAlgebra ℚ_[p] (lp (fun _ : ℕ => ℚ_[p]) ∞)
#synth NormOneClass (lp (fun _ : ℕ => ℚ_[p]) ∞)
#synth CompleteSpace (lp (fun _ : ℕ => ℚ_[p]) ∞)
#synth IsUltrametricDist (lp (fun _ : ℕ => ℚ_[p]) ∞)
#check @Padic.norm_p_pow
#check @PadicInt.norm_p_pow
#check @padicNormE.norm_p_pow
#check @Padic.norm_p
end

namespace ContinuousLinearMap.Ultra
variable {R M N : Type*} [Semiring R] [SeminormedAddCommGroup M] [Module R M]
  [SeminormedAddCommGroup N] [Module R N]
scoped instance instNorm : Norm (M →L[R] N) :=
  ⟨fun u => sInf {c : ℝ | 0 ≤ c ∧ ∀ x, ‖u x‖ ≤ c * ‖x‖}⟩
end ContinuousLinearMap.Ultra

section
open scoped ContinuousLinearMap.Ultra
variable {K M N : Type*} [NontriviallyNormedField K] [NormedAddCommGroup M] [NormedSpace K M]
  [NormedAddCommGroup N] [NormedSpace K N]
example (u : M →L[K] N) : @norm _ ContinuousLinearMap.Ultra.instNorm u = ‖u‖ := rfl
#synth Norm (M →L[K] N)
#synth NormedAddCommGroup (M →L[K] N)
end

#check @MetricSpace.ext
#check @PseudoMetricSpace.ext
#check @UniformSpace.ext
#check @NormedAddCommGroup.ofSeparation
#check @AddGroupSeminorm.toSeminormedAddCommGroup
#check @continuousLinearMapOfTendsto
#check @pi_eq_sum_univ
#check @Pi.nnnorm_single
#check @Pi.norm_single
#check @Filter.Tendsto.bddAbove_range
#check @exists_nat_ge
#check @Module.Finite.equiv
#check @LinearMap.ker_eq_bot
#check @LinearMap.range_eq_top
#check @ContinuousLinearMap.coprod
#check @ContinuousLinearMap.inl
#check @Submodule.Quotient.mk_surjective
#check @Submodule.mkQ_surjective
#check @IsSeqClosed.isClosed
#check @LinearEquiv.ofLeftInverse
#check @LinearMap.graph_eq_range_prod
#check @lp.single
#check @memℓp_infty
#check @lp.norm_le_of_forall_le
#check @lp.eq_zero_iff_coeFn_eq_zero
#check @lp.coeFn_add
#check @lp.infty_coeFn_mul
#check @Ideal.mem_span_singleton'
#check @ContinuousLinearMap.ring
#print Units.oneSub
#check @Units.val_oneSub
#check @ContinuousLinearMap.toNormedAddCommGroup
#check @ContinuousLinearMap.toNormedRing
#check @ContinuousLinearMap.toSeminormedAddCommGroup
#check @ContinuousLinearMap.opNorm_comp_le
#check @ContinuousLinearMap.opNorm_zero_iff
#check @ContinuousLinearMap.norm_id_of_nontrivial_seminorm
#check @ContinuousLinearMap.opNorm_le_of_ball
#check @ContinuousLinearMap.opNorm_le_of_shell
#check @IsUltrametricDist.nonarchimedeanAddGroup
#check @NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
#check @Metric.closedBall
#check @ContinuousLinearMap.isOpenMap
#check @LinearMap.continuous_of_isClosed_graph
#check @Submodule.Quotient.norm_mk_le
#check @Submodule.Quotient.norm_mk_lt
#check @QuotientAddGroup.norm_lt_iff
#check @NormedAddGroupHom.lift
#check @Submodule.liftQ
#check @Submodule.liftQ_mkQ
#check @LinearMap.quotKerEquivRange_apply_mk
#check @LinearMap.quotKerEquivRange_symm_apply_image
#check @Submodule.subtypeL
#check @Submodule.subtype
#check @NormedRing.norm_tsum_geometric
#check @NormedRing.openUnitBallIdeal_le_jacobson_bot
#check @NormedRing.PseudoUniformizer.existsUnique_zpow_norm_smul_mem_Ioc
#check @NormedRing.PseudoUniformizer.norm_zpow_smul
#check @NormedRing.IsMultiplicative.norm_smul
#check @NormedRing.IsTate.exists_pseudoUniformizer
#check @NormedRing.isTate_of_normedAlgebra
#check @Prod.instIsUltrametricDist
#check @Submodule.Quotient.instIsUltrametricDist
#check @AddEquiv.completeSpace_congr_of_bounds
#check @NormedRing.PseudoUniformizer.normOneClass_of_nontrivial
#check @Metric.ball_subset_ball
#check @norm_pow_le'
#check @Finset.sum_le_sum
#check @Fintype.sum_apply
#check @Finset.smul_sum
#check @Finset.sum_smul
#check @map_sum
#check @LinearMap.map_smul
#check @AddMonoidHomClass.continuous_of_bound
#check @NormedAddCommGroup.ext
#check @ContinuousLinearMap.norm_id_le
