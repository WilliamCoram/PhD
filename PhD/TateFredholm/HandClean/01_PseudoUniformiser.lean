import PhD.TateFredholm.HandClean.TateRings
import PhD.ForMathlib.Analysis.Normed.Ring.NegLogNorm

open TateFredholm

variable {A : Type*} [NormedRing A]

/-- The logarithm of `‖ϖ‖` is negative — the normalising constant of `PseudoUniformizer.val`. -/
theorem PseudoUniformizer.log_norm_neg [Nontrivial A] (ϖ : PseudoUniformizer A) :
    Real.log ‖(ϖ : A)‖ < 0 :=
  Real.log_neg ϖ.norm_pos (by rw [PseudoUniformizer.coe_eq]; exact ϖ.norm_lt_one)

/-- The additive valuation `v_ϖ(r) = −log_a ‖r‖`, `a = ‖ϖ‖⁻¹`, normalised so `v_ϖ(ϖ) = 1`
([JN] Definition 2.1.2). -/
noncomputable def PseudoUniformizer.val (ϖ : PseudoUniformizer A) (r : A) : WithTop ℝ :=
  (AddMonoidHom.mulRight (-Real.log ‖(ϖ : A)‖)⁻¹).withTopMap (negLogNorm r)
  -- note this is not actujally an additive valuation in Leans sense (norm is only sub muliplicative
  -- in our working assumptions.)
