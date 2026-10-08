import Mathlib
open Filter Topology
open scoped ZeroAtInfty

-- §1.1 instance landscape over a ring
section
variable {R M N : Type*} [NormedRing R] [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
#synth ContinuousConstSMul R N
#synth Ring (M →L[R] M)
#synth IsBoundedSMul R (M × N)
#synth IsUltrametricDist (Subtype fun x : M => x = x)
#synth CompleteSpace (M × N)
end
section
variable {R M N : Type*} [NormedCommRing R] [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
#synth Module R (M →L[R] N)
#synth Algebra R (M →L[R] M)
#synth SMulCommClass R R N
end
section
variable {R : Type*} [NormedRing R] {ι : Type*} [Fintype ι]
#synth IsUltrametricDist (ι → R)
#synth IsBoundedSMul R (ι → R)
#synth NormedAddCommGroup (ι → R)
#synth Module (Subring.unitClosedBall R) R
end
section
variable {R M : Type*} [NormedCommRing R] [NormedAddCommGroup M] [Module R M] (S : Subring R)
#synth Module S M
#synth IsScalarTower S R M
end
section
variable {R : Type*} [NormedRing R] [NormOneClass R]
#synth Module R C₀(ℕ, R)
#synth IsBoundedSMul R C₀(ℕ, R)
#synth NormedAddCommGroup C₀(ℕ, R)
end
section
variable (p : ℕ) [Fact p.Prime]
#synth NormedRing (lp (fun _ : ℕ => ℚ_[p]) ∞)
#synth NormedAlgebra ℚ_[p] (lp (fun _ : ℕ => ℚ_[p]) ∞)
#synth NormOneClass (lp (fun _ : ℕ => ℚ_[p]) ∞)
#synth CompleteSpace (lp (fun _ : ℕ => ℚ_[p]) ∞)
#synth NormedRing C(ℤ_[p], ℚ_[p])
end

-- names
#check @nonempty_interior_of_iUnion_of_closed
#check @Metric.mem_closure_iff
#check @Metric.mem_nhds_iff
#check @mem_interior_iff_mem_nhds
#check @exists_mem_Ioc_zpow
#check @exists_mem_Ico_zpow
#check @IsUltrametricDist.norm_add_le_max
#check @IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
#check @IsUltrametricDist.norm_tsum_le
#check @IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
#check @IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
#check @AddGroupNorm.toNormedAddCommGroup
#check @NormedAddCommGroup.ext
#check @SeminormedAddCommGroup.ext
#check @NormedRing.ext
#check @Units.oneSub
#check @Units.isOpen
#check @NormedRing.inverse_add
#check @NormedRing.tsum_geometric_of_norm_lt_one
#check @summable_geometric_of_lt_one
#check @summable_geometric_two
#check @tsum_geometric_two
#check @norm_tsum_le_tsum_norm
#check @Summable.of_norm
#check @Summable.tsum_le_tsum
#check @tsum_mul_right
#check @tendsto_pow_atTop_nhds_zero_of_lt_one
#check @squeeze_zero
#check @tendsto_nhds_unique
#check @tendsto_iff_norm_sub_tendsto_zero
#check @HasSum.tendsto_sum_nat
#check @Metric.complete_of_cauchySeq_tendsto
#check @cauchySeq_tendsto_of_complete
#check @Metric.cauchySeq_iff
#check @Metric.tendsto_atTop
#check @LinearMap.mkContinuous
#check @LinearMap.mkContinuousOfExistsBound
#check @LinearMap.mkContinuous_apply
#check @AddMonoidHomClass.continuous_of_bound
#check @AddMonoidHomClass.lipschitz_of_bound
#check @continuous_of_linear_of_bound
#check @ContinuousLinearMap.ext
#check @ContinuousLinearMap.coe_inj
#check @ContinuousLinearMap.sub_apply
#check @ContinuousLinearMap.comp_apply
#check @ContinuousLinearMap.mul_def
#check @ContinuousLinearMap.one_def
#check @ContinuousLinearMap.smul_apply
#check @ContinuousLinearMap.fst
#check @ContinuousLinearMap.snd
#check @ContinuousLinearMap.prod
#check @ContinuousLinearMap.isClosed_ker
#check @ContinuousLinearMap.opNorm_le_bound
#check @ContinuousLinearMap.le_opNorm
#check @ContinuousLinearMap.norm_def
#check @ContinuousLinearMap.exists_preimage_norm_le
#check @ContinuousLinearMap.isOpenMap
#check @ContinuousLinearMap.bound
#check @ContinuousLinearMap.opNorm_eq_of_bounds
#check @ContinuousLinearMap.norm_smul
#check @ContinuousLinearMap.norm_id
#check @ContinuousLinearMap.sSup_unit_ball_eq_norm
#check @ContinuousLinearEquiv.ofBijective
#check @ContinuousLinearEquiv.equivOfInverse
#check @ContinuousLinearEquiv.mk
#check @LinearEquiv.ofBijective
#check @LinearEquiv.continuous_symm
#check @LinearMap.graph
#check @LinearMap.mem_graph_iff
#check @LinearMap.continuous_of_isClosed_graph
#check @LinearMap.continuous_of_seq_closed_graph
#check @LinearMap.quotKerEquivRange
#check @LinearMap.quotKerEquivOfSurjective
#check @Submodule.liftQ
#check @Submodule.mkQ
#check @Submodule.liftQ_apply
#check @Submodule.mkQ_apply
#check @Submodule.Quotient.normedAddCommGroup
#check @Submodule.Quotient.instIsBoundedSMul
#check @Submodule.Quotient.completeSpace
#check @QuotientAddGroup.norm_mk_le_norm
#check @QuotientAddGroup.norm_lt_iff
#check @Submodule.Quotient.norm_mk_le
#check @NormedAddGroupHom.lift
#check @NormedAddGroupHom.lift_norm_le
#check @NormedAddGroupHom.lift_norm_noninc
#check @QuotientAddGroup.norm_mk
#check @Submodule.topologicalClosure
#check @Submodule.isClosed_topologicalClosure
#check @Submodule.le_topologicalClosure
#check @Submodule.topologicalClosure_coe
#check @Submodule.le_of_le_smul_of_le_jacobson_bot
#check @Submodule.fg_iff_exists_fin_generating_family
#check @Submodule.fg_span
#check @IsNoetherian.noetherian
#check @isNoetherian_of_isNoetherianRing_of_finite
#check @Module.Finite.exists_fin'
#check @Module.Finite.exists_fin
#check @Submodule.add_mem_sup
#check @Submodule.smul_mem_smul
#check @Submodule.sum_mem
#check @Submodule.mem_span_range_iff_exists_fun
#check @Submodule.span_le
#check @Submodule.subset_span
#check @Submodule.restrictScalars
#check @Fintype.linearCombination
#check @Fintype.linearCombination_apply
#check @pi_norm_le_iff_of_nonneg
#check @norm_le_pi_norm
#check @Pi.norm_def
#check @Pi.single
#check @LinearMap.pi
#check @Pi.basisFun
#check @IsClosed.completeSpace_coe
#check @IsClosed.isComplete
#check @isClosed_of_closure_subset
#check @Metric.isOpen_iff
#check @Real.sInf_nonneg
#check @csInf_le
#check @le_csInf
#check @le_csInf_iff
#check @ciSup_le
#check @le_ciSup
#check @Real.iSup_le
#check @Real.le_iSup_of_le
#check @IsOpenMap.isQuotientMap
#check @NormedField.exists_norm_lt_one
#check @NormedField.exists_one_lt_norm
#check @banach_steinhaus
#check @continuousLinearMapOfTendsto
#check @LinearMap.continuous_of_finiteDimensional
#check @FiniteDimensional.complete
#check @Submodule.closed_of_finiteDimensional
#check @LinearMap.exists_antilipschitzWith
#check @ContinuousLinearMap.isOpen_injective
#check @LinearEquiv.toContinuousLinearEquiv
#check @FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
#check @Pi.instIsUltrametricDist
#check @IsBoundedSMul.of_norm_smul_le
#check @norm_smul_le
#check @NormOneClass.nontrivial
#check @Metric.continuousAt_iff
#check @Metric.continuous_iff
#check @NormedAddCommGroup.tendsto_nhds_zero
#check @Filter.Tendsto.norm
#check @le_of_tendsto
#check @Filter.eventually_atTop
#check @Finset.sum_range_succ
#check @Function.iterate_succ'
#check @Function.iterate_succ_apply'
#check @geom_sum_Ico_le_of_lt_one
#check @mul_geom_sum
#check @geom_sum_mul
#check @Finset.sum_Ico_eq_sub
#check @exists_nat_gt
#check @Submodule.Quotient.mk_eq_zero
#check @Submodule.Quotient.eq
#check @Submodule.ker_mkQ
#check @Submodule.range_mkQ
#check @HasSum.map
#check @Summable.map
#check @tsum_apply
#check @ContinuousLinearMap.apply
#check @AddMonoidHom.mk'
#check @ContinuousLinearMap.evalAddMonoidHom
#check @lp.inftyNormedRing
#check @lp.infty_coeFn_mul
#check @lp.norm_apply_le_norm
#check @lp.norm_le_of_forall_le
#check @lp.norm_le_of_forall_le'
#check @lp.norm_apply_le_of_tendsto
#check @lp.memℓp_infty_iff
#check @lp.single
#check @Memℓp
#check @lp.norm_eq_ciSup
#check @lp.isLUB_norm
#check @memℓp_infty
#check @padicNormE.norm_p_inv
#check @Padic.norm_p
#check @Padic.norm_p_pow
#check @Padic.norm_p_zpow
#check @PadicInt.norm_p
#check @PadicInt.norm_le_one
#check @PadicInt.norm_p_pow
#check @IsUltrametricDist.norm_sum_le
#check @Finset.sup_le
#check @Finset.exists_max_image
#check @ContinuousLinearMap.norm_smul_le
#check @NormedSpace.toIsBoundedSMul
#check @ZeroAtInftyContinuousMap.norm_le
#check @ContinuousMap.instNormedRing
#check @IsNoetherianRing
#check @Ideal.span_singleton_le_iff_mem
#check @Ideal.mem_span_singleton
#check @Ideal.mem_span_singleton'
#check @ContinuousLinearMap.graph
#check @IsUltrametricDist.subtype
#check @QuotientAddGroup.instIsUltrametricDist
