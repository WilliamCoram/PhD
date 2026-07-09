import PhD.TateFredholm.Residue

/-!
# Changing the norm, base change, and the classical specialisations
([JN] Lemmas 2.1.6–2.1.7, Proposition 2.1.8; [Buz07, Corollaries 2.9–2.10];
[Bel] Lemma II.1.23, matrix-wise; [Bel] Theorem II.1.13 (Serre).  See `Tate.lean` for
the development's overview and dictionary.)

The Tate-specific norm-comparison lemmas hold in the merged setting as stated by [JN];
the invariance and base-change statements lose their Noetherian hypotheses. -/

open Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace TateFredholm

variable (R : Type*) [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormOneClass R]

section NormChange

variable {R}
variable (S : Type*) [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]
  [NormOneClass S]

/-- **[JN] Lemma 2.1.6** (the erratum lemma): two equivalent Tate norms, with possibly
different pseudo-uniformizers, are *power*-comparable — `‖a‖ ≤ C₂‖a‖'^s` on `‖a‖' ≥ 1` —
but in general **not** bounded-equivalent. -/
theorem norm_le_pow_of_equiv (e : R ≃+* S) (he : Continuous (e : R → S))
    (he' : Continuous (e.symm : S → R))
    (ϖ : PseudoUniformizer R) (π : PseudoUniformizer S) :
    ∃ C₁ C₂ s : ℝ, 0 < s ∧ (∀ a : R, ‖e a‖ < 1 → ‖a‖ ≤ C₁) ∧
      ∀ a : R, 1 ≤ ‖e a‖ → ‖a‖ ≤ C₂ * ‖e a‖ ^ s := by
  sorry

/-- **[JN] Lemma 2.1.7**: with a common multiplicative pseudo-uniformizer, the comparison
is two-sided of pure power type, `C₁‖a‖^s ≤ ‖e a‖ ≤ C₂‖a‖^s` (`s` pinned by
`‖e ϖ‖ = ‖ϖ‖^s`). -/
theorem norm_comparison_of_common_uniformizer (e : R ≃+* S)
    (he : Continuous (e : R → S)) (he' : Continuous (e.symm : S → R))
    (ϖ : PseudoUniformizer R)
    (hmul : IsMultiplicative (e (ϖ : R)))
    (hlt : ‖e (ϖ : R)‖ < 1) :
    ∃ C₁ C₂ s : ℝ, 0 < C₁ ∧ 0 < s ∧
      ∀ a : R, C₁ * ‖a‖ ^ s ≤ ‖e a‖ ∧ ‖e a‖ ≤ C₂ * ‖a‖ ^ s := by
  sorry

variable {I : Type*} [DecidableEq I]

/-- Norm-invariance of compactness ([JN] Proposition 2.1.8, Noetherian-free): a
bicontinuous ring isomorphism relating the matrices transfers compactness (row decay is
topological). -/
theorem isCompletelyContinuous_map_equiv [IsTate R] [IsTate S]
    (e : R ≃+* S) (he : Continuous (e : R → S)) (he' : Continuous (e.symm : S → R))
    (u : c(I, R) →L[R] c(I, R)) (hu : IsCompletelyContinuous u)
    (v : c(I, S) →L[S] c(I, S))
    (hv : ∀ j i, matrixCoeff v j i = e (matrixCoeff u j i)) :
    IsCompletelyContinuous v := by
  sorry

/-- Norm-invariance of the Fredholm determinant ([JN] Proposition 2.1.8,
Noetherian-free): `det(1 − Tv) = e(det(1 − Tu))` for a bicontinuous `e`.  Note this is a
*topological* statement (summability transfer) — `e` is only power-comparable
(`norm_le_pow_of_equiv`), not bounded, so it is **not** a special case of
`charPowerSeries_baseChange`. -/
theorem charPowerSeries_map_equiv [IsTate R] [IsTate S]
    (e : R ≃+* S) (he : Continuous (e : R → S)) (he' : Continuous (e.symm : S → R))
    (u : c(I, R) →L[R] c(I, R)) (hu : IsCompletelyContinuous u)
    (v : c(I, S) →L[S] c(I, S))
    (hv : ∀ j i, matrixCoeff v j i = e (matrixCoeff u j i)) :
    charPowerSeries v = PowerSeries.map (e : R →+* S) (charPowerSeries u) := by
  sorry

/-- Base change along a bounded homomorphism, compactness half
(`r_j(v) ≤ C·r_j(u) → 0`). -/
theorem isCompletelyContinuous_baseChange [IsTate R] [IsTate S]
    (ψ : R →+* S) (C : ℝ) (hψ : ∀ r, ‖ψ r‖ ≤ C * ‖r‖)
    (u : c(I, R) →L[R] c(I, R)) (hu : IsCompletelyContinuous u)
    (v : c(I, S) →L[S] c(I, S))
    (hv : ∀ j i, matrixCoeff v j i = ψ (matrixCoeff u j i)) :
    IsCompletelyContinuous v := by
  sorry

/-- Base change along a bounded homomorphism, coefficientwise: `cₙ(v) = ψ(cₙ(u))`
(`ψ` commutes with finite determinants and, being continuous, with the `tsum`). -/
theorem charCoeff_baseChange [IsTate R] [IsTate S]
    (ψ : R →+* S) (C : ℝ) (hψ : ∀ r, ‖ψ r‖ ≤ C * ‖r‖)
    (u : c(I, R) →L[R] c(I, R)) (hu : IsCompletelyContinuous u)
    (v : c(I, S) →L[S] c(I, S))
    (hv : ∀ j i, matrixCoeff v j i = ψ (matrixCoeff u j i)) (n : ℕ) :
    charCoeff v n = ψ (charCoeff u n) := by
  sorry

/-- Base change, assembled: `det(1 − Tv) = ψ(det(1 − Tu))` in `S⟦T⟧`. -/
theorem charPowerSeries_baseChange [IsTate R] [IsTate S]
    (ψ : R →+* S) (C : ℝ) (hψ : ∀ r, ‖ψ r‖ ≤ C * ‖r‖)
    (u : c(I, R) →L[R] c(I, R)) (hu : IsCompletelyContinuous u)
    (v : c(I, S) →L[S] c(I, S))
    (hv : ∀ j i, matrixCoeff v j i = ψ (matrixCoeff u j i)) :
    charPowerSeries v = PowerSeries.map ψ (charPowerSeries u) := by
  ext n
  simp [charCoeff_baseChange S ψ C hψ u hu v hv n, PowerSeries.coeff_map]

end NormChange

/-! ## Classical specialisations

Statements that are intrinsically about the field case, phrased against the merged
definitions so that the parent files' versions are literal instances.  The residue
machinery feeding the proof lives in `Residue.lean`. -/

section Classical

/-- **Serre's theorem** ([Bel] Theorem II.1.13 for `ℚ_p`; [Serre] Prop. 1; blueprint
Lemma 6.7): over a **discretely valued** nontrivially normed field `K`, every Banach
`K`-space is potentially ON-able.  Intrinsically a field statement: over a general
Banach–Tate ring not every Banach module is potentially ON-able (which is exactly why
property (Pr) exists).

*Proof sketch.*  Rescale the norm into `‖K‖` (`rescale`, lemmas R7a–R7c of
`Residue.lean`), then apply `isONable_of_discrete_norms` to the rescaled space and
transport along the identity homeomorphism. -/
theorem isPotentiallyONable_of_uniformizer (K : Type*) [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K]
    (hd : ∃ π : K, 0 < ‖π‖ ∧ ‖π‖ < 1 ∧ ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace K E] [IsUltrametricDist E]
    [CompleteSpace E] :
    IsPotentiallyONable K E := by
  sorry

end Classical

end TateFredholm

end
