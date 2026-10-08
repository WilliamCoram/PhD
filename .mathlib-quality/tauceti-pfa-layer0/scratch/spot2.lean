import PhD.TauCeti.Code.PadicFunctionalAnalysis.Tate

open NormedRing

example {R : Type*} [NormedRing R] [Nontrivial R] (ϖ : PseudoUniformizer R) : NormOneClass R := by
  refine ⟨?_⟩
  have h := ϖ.isMultiplicative 1
  rw [mul_one] at h
  have h0 : ‖(ϖ.unit : R)‖ ≠ 0 := norm_ne_zero_iff.2 ϖ.unit.ne_zero
  exact (mul_right_eq_self₀.1 h.symm).resolve_right h0
