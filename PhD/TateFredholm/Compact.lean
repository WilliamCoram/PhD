import PhD.TateFredholm.OperatorNorm

/-!
# Finite-rank and completely continuous operators
([Bel] Definition II.1.3, Lemma II.1.4; [JN] Definition 2.1.5; blueprint 6.13.  See
`Tate.lean` for the development's overview and dictionary.) -/

open Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace TateFredholm

variable (R : Type*) [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormOneClass R]

section Compact

variable {R}
variable {M N P : Type*}
  [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  [NormedAddCommGroup P] [Module R P] [IsBoundedSMul R P]

/-- *Finite rank*: the image is contained in a finitely generated submodule. -/
def IsFiniteRank (u : M →L[R] N) : Prop :=
  ∃ Q : Submodule R N, Q.FG ∧ LinearMap.range (u : M →ₗ[R] N) ≤ Q

/-- *Completely continuous* (= compact): an operator-norm limit of finite-rank operators,
phrased metrically.  (Not Mathlib's `IsCompactOperator` — see the parent files.) -/
def IsCompletelyContinuous (u : M →L[R] N) : Prop :=
  ∀ ε > 0, ∃ v : M →L[R] N, IsFiniteRank v ∧ ‖u - v‖ < ε

theorem IsFiniteRank.isCompletelyContinuous {u : M →L[R] N} (hu : IsFiniteRank u) :
    IsCompletelyContinuous u := by
  intro ε hε
  refine ⟨u, hu, ?_⟩
  sorry -- `‖u - u‖ = ‖0‖ = 0 < ε`.

/-- Compacts are stable under operator-norm limits (`ε/2` + `norm_add_le`). -/
theorem isCompletelyContinuous_of_tendsto (u : ℕ → M →L[R] N) (v : M →L[R] N)
    (hu : ∀ n, IsCompletelyContinuous (u n))
    (huv : Tendsto (fun n => ‖u n - v‖) atTop (𝓝 0)) :
    IsCompletelyContinuous v := by
  sorry

/-- Finite-rank operators are stable under sums (`range (u+v) ≤ range u ⊔ range v`). -/
theorem IsFiniteRank.add {u v : M →L[R] N} (hu : IsFiniteRank u) (hv : IsFiniteRank v) :
    IsFiniteRank (u + v) := by
  sorry

/-- Two-sided-ideal property, finite-rank half, post-composition ([Bel] Lemma II.1.4). -/
theorem IsFiniteRank.comp_left {u : M →L[R] N} (hu : IsFiniteRank u) (f : N →L[R] P) :
    IsFiniteRank (f.comp u) := by
  obtain ⟨Q, hQ, hle⟩ := hu
  refine ⟨Q.map (f : N →ₗ[R] P), hQ.map _, ?_⟩
  rintro x ⟨m, rfl⟩
  exact Submodule.mem_map_of_mem (hle ⟨m, rfl⟩)

/-- Two-sided-ideal property, finite-rank half, pre-composition ([Bel] Lemma II.1.4). -/
theorem IsFiniteRank.comp_right {u : M →L[R] N} (hu : IsFiniteRank u) (f : P →L[R] M) :
    IsFiniteRank (u.comp f) := by
  obtain ⟨Q, hQ, hle⟩ := hu
  refine ⟨Q, hQ, ?_⟩
  rintro x ⟨m, rfl⟩
  exact hle ⟨f m, rfl⟩

/-- Two-sided-ideal property, compact half, post-composition ([Bel] Lemma II.1.4;
`‖f∘u − f∘v‖ ≤ ‖f‖‖u − v‖` via `le_opNorm`, whence `[IsTate R]`). -/
theorem IsCompletelyContinuous.comp_left [IsTate R] {u : M →L[R] N}
    (hu : IsCompletelyContinuous u) (f : N →L[R] P) :
    IsCompletelyContinuous (f.comp u) := by
  sorry

/-- Two-sided-ideal property, compact half, pre-composition ([Bel] Lemma II.1.4). -/
theorem IsCompletelyContinuous.comp_right [IsTate R] {u : M →L[R] N}
    (hu : IsCompletelyContinuous u) (f : P →L[R] M) :
    IsCompletelyContinuous (u.comp f) := by
  sorry

end Compact

end TateFredholm

end
