import PhD.TateFredholm.ModelSpace

/-!
# Matrices, truncations, and the compactness criterion
([Bel] §II.1.3: Lemma II.1.8, Proposition II.1.9, Scholium II.1.10; blueprint 6.11,
6.14.  See `Tate.lean` for the development's overview and dictionary.)

The headline of the merge is `isCompletelyContinuous_iff_rowNorm`: [JN] state it over
Noetherian Banach–Tate rings (inheriting Buzzard's proof); Bellaïche's truncation/OMT
proof needs no Noetherian hypothesis and runs verbatim under `[IsTate R]`. -/

open Filter Topology
open scoped BoundedContinuousFunction

set_option linter.unusedSectionVars false

noncomputable section

namespace TateFredholm

variable (R : Type*) [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormOneClass R]

section Matrix

variable {R}
variable {I J : Type*} [DecidableEq I] [DecidableEq J]

/-- Matrix coefficients in the canonical bases: `matrixCoeff u j i = (u eᵢ)_j`. -/
def matrixCoeff (u : c(I, R) →L[R] c(J, R)) (j : J) (i : I) : R :=
  u (cSpace.single i 1) j

/-- Columns decay cofinitely. -/
theorem tendsto_matrixCoeff_column (u : c(I, R) →L[R] c(J, R)) (i : I) :
    Tendsto (fun j => matrixCoeff u j i) cofinite (𝓝 0) :=
  cSpace.tendsto_cofinite (u (cSpace.single i 1))

/-- `‖u‖ = sup_{i,j} ‖a_{ij}‖` ([Buz07, p. 65]; [Bel] §II.1.3). -/
theorem norm_eq_iSup_matrixCoeff [IsTate R] (u : c(I, R) →L[R] c(J, R)) :
    ‖u‖ = ⨆ j : J, ⨆ i : I, ‖matrixCoeff u j i‖ := by
  sorry

/-- Bounded families = operators out of the model space, norm-preservingly
([Bel] §II.1.3; blueprint Proposition 6.11). -/
theorem exists_coeffEquiv [IsTate R] (N : Type*) [NormedAddCommGroup N] [Module R N]
    [IsBoundedSMul R N] [IsUltrametricDist N] [CompleteSpace N] :
    ∃ φ : (c(I, R) →L[R] N) ≃ₗ[R] (Ix I →ᵇ N), ∀ u, ‖φ u‖ = ‖u‖ := by
  sorry

/-- The coordinate truncation `π_S` — Bellaïche's workhorse, now over a Tate ring. -/
def truncation (S : Finset I) : c(I, R) →L[R] c(I, R) :=
  ⟨⟨⟨fun f => (⟨⟨fun i => if i ∈ S then f i else 0, continuous_of_discreteTopology⟩,
      by sorry⟩ : c(I, R)),
    by sorry⟩, by sorry⟩, by sorry⟩

@[simp] theorem truncation_apply (S : Finset I) (f : c(I, R)) (i : I) :
    truncation S f i = if i ∈ S then f i else 0 := rfl

/-- Truncations are contractions. -/
theorem norm_truncation_apply_le (S : Finset I) (f : c(I, R)) :
    ‖truncation S f‖ ≤ ‖f‖ := by
  sorry

/-- Truncations have finite rank. -/
theorem isFiniteRank_truncation (S : Finset I) :
    IsFiniteRank (truncation (R := R) S) := by
  sorry

/-- **[Bel] Lemma II.1.8 over a Tate ring.**  Finitely generated submodules of `c_R(I)`
are uniformly approximated by coordinate truncations.

*Proof sketch.*  Exactly Bellaïche's: a continuous surjection `Rʳ → P`, norm-controlled
preimages from the quantitative OMT (`exists_preimage_norm_le` — the only input needing
`[IsTate R]`), truncate the `r` generators, estimate ultrametrically. -/
theorem exists_truncation_near [IsTate R] (P : Submodule R c(I, R)) (hP : P.FG)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset I, ∀ p ∈ P, ‖truncation S p - p‖ ≤ ε * ‖p‖ := by
  sorry

/-- The row sup `r_j(u) = sup_i ‖a_{ij}‖`. -/
def rowNorm (u : c(I, R) →L[R] c(J, R)) (j : J) : ℝ :=
  ⨆ i : I, ‖matrixCoeff u j i‖

/-- **The compactness criterion, Noetherian-free over a Banach–Tate ring** — the merge's
headline.  `u` is compact iff its row sups tend to `0` cofinitely.  ([Bel]
Proposition II.1.9's truncation proof under [JN]'s hypotheses; strictly generalises
[JN]'s statement, which carries `[IsNoetherianRing R]`, and both field-based files'
statements via `isTate_of_normedAlgebra`.)

*Proof sketch.*  (⇐) `π_S ∘ u → u` directly.  (⇒) given `ε`, take finite-rank `v` with
`‖u − v‖ < ε`; `exists_truncation_near` gives `π_S` with `‖π_S∘v − v‖ < ε`, whence
`‖π_S∘u − u‖ ≤ ε` ultrametrically, and the rows off `S` have sup `≤ ε`. -/
theorem isCompletelyContinuous_iff_rowNorm [IsTate R] (u : c(I, R) →L[R] c(J, R)) :
    IsCompletelyContinuous u ↔ Tendsto (rowNorm u) cofinite (𝓝 0) := by
  sorry

/-- **[Bel] Scholium II.1.10 over a Tate ring.**  Truncations of a compact operator
converge to it in operator norm along the directed family of finite sets. -/
theorem tendsto_truncation_comp [IsTate R] (u : c(I, R) →L[R] c(J, R))
    (hu : IsCompletelyContinuous u) :
    Tendsto (fun S : Finset J => ‖(truncation S).comp u - u‖) atTop (𝓝 0) := by
  sorry

end Matrix

end TateFredholm

end
