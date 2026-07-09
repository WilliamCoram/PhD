import PhD.TateFredholm.Fredholm

/-!
# Property (Pr) as a lifting property; the one Noetherian statement
([Bel] Exercise II.1.19, Propositions II.1.20–II.1.21.  See `Tate.lean` for the
development's overview and dictionary.) -/

open Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace TateFredholm

variable (R : Type*) [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormOneClass R]

section Pr

variable {R}
variable {P : Type*} [NormedAddCommGroup P] [Module R P] [IsBoundedSMul R P]

/-- (Pr) as a lifting property, forward direction ([Bel] Exercise II.1.19): a (Pr)
module lifts continuous maps through continuous surjections of Banach `R`-modules.

*Proof sketch.*  Reduce to `P = c_R(I)`; lift basis vectors with norm control
(`exists_preimage_norm_le`) and assemble via `exists_coeffEquiv`. -/
theorem HasPr.exists_lift [IsTate R] [IsUltrametricDist P] [CompleteSpace P]
    (hP : HasPr R P)
    {M N : Type*}
    [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [IsUltrametricDist M]
    [CompleteSpace M]
    [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N] [IsUltrametricDist N]
    [CompleteSpace N]
    (f : M →L[R] N) (hf : Function.Surjective f) (α : P →L[R] N) :
    ∃ β : P →L[R] M, f.comp β = α := by
  sorry

/-- Finitely generated (Pr) modules are projective ([Bel] Proposition II.1.20). -/
theorem HasPr.projective [IsTate R] [IsUltrametricDist P] [CompleteSpace P]
    (hP : HasPr R P) [Module.Finite R P] :
    Module.Projective R P := by
  sorry

/-- **The only Noetherian statement of the merged theory** ([Bel] Proposition II.1.21):
if `P` has (Pr) and carries a compact `u` with `1 − u` nilpotent, then `P` is finitely
generated and projective — the germ of Riesz theory. -/
theorem finite_projective_of_one_sub_compact_nilpotent [IsTate R] [IsNoetherianRing R]
    [IsUltrametricDist P] [CompleteSpace P]
    (hP : HasPr R P) (u : P →L[R] P) (hu : IsCompletelyContinuous u)
    (hnil : ∃ n : ℕ, (ContinuousLinearMap.id R P - u) ^ n = 0) :
    Module.Finite R P ∧ Module.Projective R P := by
  sorry

end Pr

end TateFredholm

end
