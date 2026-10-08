import Mathlib
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.Examples
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Orthonormal
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Residue
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Rescale
open Filter Topology
open scoped ZeroAtInfty ENNReal BoundedContinuousFunction

section
variable {R E I : Type*} [NormedRing R] [NormedAddCommGroup E] [Module R E] [IsBoundedSMul R E]
  [TopologicalSpace I] [DiscreteTopology I]
#synth Module R C₀(I, E)
#synth NormedAddCommGroup C₀(I, E)
#synth CompleteSpace C₀(I, E)
#synth Module R (I →ᵇ E)
#synth IsBoundedSMul R (I →ᵇ E)
#synth NormedAddCommGroup (I →ᵇ E)
#synth Module R (lp (fun _ : I => R) ∞)
#synth IsBoundedSMul R (lp (fun _ : I => R) ∞)
#synth IsBoundedSMul R C₀(I, E)
end
section
variable {K I : Type*} [NontriviallyNormedField K] [TopologicalSpace I] [DiscreteTopology I]
#synth NormedSpace K C₀(I, K)
#synth NormedSpace K (lp (fun _ : I => K) ∞)
#synth Module K (lp (fun _ : I => K) ∞)
end
#check @ZeroAtInftyContinuousMap.zero_at_infty
#check @ZeroAtInftyContinuousMap.norm_toBCF_eq_norm
#check @ZeroAtInftyContinuousMap.toBCF
#check @ZeroAtInftyContinuousMap.coe_toBCF
#check @ZeroAtInftyContinuousMap.ext
#check @ZeroAtInftyContinuousMap.coe_mk
#check @ZeroAtInftyContinuousMap.isometry_toBCF
#check @ZeroAtInftyContinuousMap.tendsto_iff_tendstoUniformly
#check @ZeroAtInftyContinuousMap.coe_smul
#check @ZeroAtInftyContinuousMap.coe_add
#check @ZeroAtInftyContinuousMap.coe_sub
#check @ZeroAtInftyContinuousMap.coe_zero
#check @ZeroAtInftyContinuousMap.instModule
#check @ZeroAtInftyContinuousMap.comp
#check @ZeroAtInftyContinuousMap.compStarAlgHom
#check @ZeroAtInftyContinuousMap.eval
#check @BoundedContinuousFunction.norm_eq_iSup_norm
#check @BoundedContinuousFunction.norm_coe_le_norm
#check @BoundedContinuousFunction.norm_le
#check @BoundedContinuousFunction.norm_lt_iff_of_compact
#check @BoundedContinuousFunction.coe_smul
#check @BoundedContinuousFunction.norm_smul_le
#check @BoundedContinuousFunction.instIsBoundedSMul
#check @BoundedContinuousFunction.evalCLM
#check @BoundedContinuousFunction.eval
#check @Filter.cocompact_eq_cofinite
#check @continuous_of_discreteTopology
#check @Filter.Tendsto.exists_norm_eq_iSup
#check @Filter.Tendsto.exists_forall_norm_le
#check @lp.single
#check @lp.norm_apply_le_norm
#check @lp.norm_le_of_forall_le
#check @lp.isLUB_norm
#check @lp.instModule
#check @lp.memℓp_infty_iff
#check @Submodule.ClosedComplemented
#check @Submodule.ClosedComplemented.isClosed
#check @Submodule.closedComplemented_of_finiteDimensional
#check @ContinuousLinearMap.closedComplemented_ker_of_rightInverse
#check @Module.Projective
#check @Module.Projective.of_lifting_property'
#check @Module.Projective.of_split
#check @Module.projective_of_lifting_property'
#check @Module.projective_lifting_property
#check @Module.Projective.of_free
#check @Module.Free
#check @Module.Free.of_basis
#check @Module.Free.chooseBasis
#check @Module.Free.of_divisionRing
#check @Module.Basis
#check @Module.Basis.ofVectorSpace
#check @Basis.ofVectorSpace
#check @Module.Basis.mk
#check @Module.Basis.span_eq
#check @Module.Basis.linearIndependent
#check @Module.Basis.repr
#check @Module.Basis.ext_elem
#check @Module.Basis.mem_span
#check @Ideal.Quotient.field
#check @Ideal.Quotient.isField
#check @Cardinal.mk_iUnion_le
#check @Cardinal.mk_iUnion_le_sum_mk
#check @Cardinal.mul_eq_left
#check @Cardinal.aleph0_le_mk
#check @Cardinal.eq
#check @Cardinal.mk_le_of_injective
#check @Cardinal.mk_le_aleph0_iff
#check @Set.Countable
#check @Set.countable_iUnion
#check @Set.Countable.mono
#check @Cardinal.mk_le_of_surjective
#check @LinearIsometryEquiv
#check @LinearIsometryEquiv.prodAssoc
#check @LinearIsometryEquiv.piLpCongrLeft
#check @ContinuousLinearEquiv.prod
#check @ContinuousLinearEquiv.piCongrLeft
#check @LinearIsometryEquiv.ofBounds
#check @LinearIsometryEquiv.toContinuousLinearEquiv
#check @LinearIsometryEquiv.mk
#check @LinearIsometryEquiv.ofSurjective
#check @LinearEquiv.toLinearIsometryEquiv
#check @ContinuousLinearMap.prod
#check @Pi.normedAddCommGroup
#check @Prod.normedAddCommGroup
#check @Prod.norm_def
#check @Pi.norm_def
#check @pi_norm_le_iff_of_nonneg
#check @Equiv.sumCompl
#check @Equiv.ulift
#check @hasSum_single
#check @HasSum.map
#check @HasSum.smul_const
#check @tsum_add
#check @tsum_smul_const
#check @Summable.tsum_add
#check @NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
#check @IsUltrametricDist.norm_tsum_le
#check @IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
#check @Finset.nnnorm_sum_le_sup_nnnorm
#check @IsUltrametricDist.nnnorm_sum_le_sup_nnnorm
#check @Valuation.IsRankOneDiscrete
#check @Valuation.IsRankOneDiscrete.exists_generator_lt_one
#check @Valuation.IsRankOneDiscrete.generator
#check @NormedField.valuation
#check @NormedField.valuation_apply
#check @Valuation.IsUniformizer
#check @Valuation.exists_isUniformizer
#check @Valuation.isUniformizer_iff
#check @Padic.isUniformizer_p
#check @Valuation.valueGroup
#check @Valuation.IsRankOneDiscrete.exists_isUniformizer
#check @NormedField.exists_norm_lt_one
#check @Submodule.Quotient.mk_surjective
#check @Submodule.mkQ_surjective
#check @Submodule.Quotient.mk
#check @Submodule.Quotient.eq
#check @Submodule.Quotient.mk_eq_zero
#check @NormedRing.PseudoUniformizer.ResidueModule
#check @NormedRing.PseudoUniformizer.ResidueRing
#check @NormedRing.PseudoUniformizer.mem_ideal_smul_top_iff_norm_lt_one
#check @NormedRing.PseudoUniformizer.Rescaled
#check @NormedRing.PseudoUniformizer.isBoundedSMul_rescaled
#check @NormedRing.PseudoUniformizer.norm_toRescaled_eq_of_forall_exists_zpow
#check @NormedRing.PseudoUniformizer.exists_norm_rescaled_eq_zpow
#check @NormedRing.maximalIdeal_unitClosedBall
#check @NormedRing.PseudoUniformizer.ideal_eq_openUnitBallIdeal
#check @Ideal.Quotient.maximal_ideal_iff_isField_quotient
#check @ContinuousLinearMap.Ultra.ofBounded
#check @LinearMap.mkContinuous
#check @ContinuousLinearMap.Ultra.le_opNorm
#check @ContinuousLinearMap.Ultra.exists_preimage_norm_le
#check @ContinuousLinearMap.Ultra.exists_bound_of_finite
#check @Submodule.isClosed_of_isNoetherianRing
#check @ContinuousLinearMap.Ultra.continuous_pi
#check @IsOrthonormalFamily
#check @IsOrthonormalBasis
#check @IsOrthonormalBasis.exists_hasSum
#check @Set.indicator
#check @Finset.sup_le_iff
#check @Finset.le_sup
#check @NNReal.coe_le_coe
#check @Module.Finite.exists_fin'
#check @Submodule.fg_iff_exists_fin_generating_family
#check @IsNoetherian.noetherian
#check @ContinuousLinearMap.isClosed_ker
#check @IsClosed.completeSpace_coe
#check @Dense
#check @DenseRange
#check @Submodule.topologicalClosure
#check @Submodule.dense_iff_topologicalClosure_eq_top
#check @Set.Finite.subset
#check @Function.support
#check @Finsupp.linearCombination
#check @Finsupp.mem_span_range_iff_exists_finsupp
#check @Real.iSup_le
#check @ciSup_le
#check @le_ciSup
#check @Real.iSup_nonneg
#check @mul_iSup_of_nonneg
#check @Real.mul_iSup_of_nonneg
#check @Finite.of_injective
#check @Set.Finite.of_finite_image
#check @Cardinal.mk_eq_aleph0
#check @Equiv.Perm
#check @Function.Injective.tendsto_cofinite
#check @Filter.Tendsto.comp
#check @Filter.cofinite
#check @Equiv.tendsto_cofinite_iff
