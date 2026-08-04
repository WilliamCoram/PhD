/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Jacobs.U3.KappaAction
import PhD.Jacobs.U3.Factorisations
import PhD.QMF.HeckeMatrix

/-!
# AG-B: the matrix of `U₃` is the transcribed matrix

The endpoint of the identification tranche.  [Jacobs, p. 28]:

> "Thus, the matrix of U₃ will have the form A = (ε_{i,j}) = (0 ε₀,₁ ε₀,₂; ε₁,₀ 0 ε₁,₂;
> ε₂,₀ ε₂,₁ 0) … Our next aim is to calculate the generating functions of the non-zero
> ε_{i,j}."  — with the generating functions (2.1.4)–(2.1.9), transcribed (misprint
> corrected) as `Jacobs.h01 … h21` in `PhD.Jacobs.U3Data`.

Two layers:

* `heckeU3_apply_classRep` — **unconditional**: the value of the Hecke operator
  `[U₁(9)·η₃·U₁(9)]` on the weight-`κ` automorphic space at each representative `cᵢ` is
  the `i`-th row of the block matrix, with blocks the `κ`-actions assembled from the nine
  certificates.  This is the certificate-driven computation of [Jacobs, pp. 25–28].
* `eval_classRep_injective` — needs `HClassNumberOne` (Theorem 2.1): the `(cᵢ)` are a
  complete section with trivial stabilisers, so evaluation at them is injective and the
  block matrix *determines* the operator.  This is what makes the first layer "the
  matrix of `U₃`" rather than "a matrix identity at three points".

Downstream (AG-W, `PhD.Jacobs.DiamondW`): the blocks' generating functions being the
`h_{i,j}` ties `heckeU3` to the `3×3` block operator `U3MatrixOp` whose characteristic
power series the slopes tranche analyses.
-/

open Quaternion IsDedekindDomain NumberField QMF TateFredholm

namespace Jacobs.U3

/-- The wild-level monoid refined to `Σ₁(9)`-components: the acting monoid of the
weight-`κ` theory.  (`Σ₀` supports the polynomial weights; `κ` needs the `1`-unit
condition on the `(0,0)`-entry, so the automorphic machinery is instantiated at this
smaller `Δ`.) -/
noncomputable def levelMonoid1 : Submonoid (Dfx ℚ D) :=
  Sigma1.comap (toMatrix ℚ D v₃)

theorem U1_9_subset_levelMonoid1 : (U1_9 : Set (Dfx ℚ D)) ⊆ levelMonoid1 := sorry

theorem eta3_mem_levelMonoid1 : eta3 ∈ levelMonoid1 := sorry

/-- The space of weight-`κ` quaternionic modular forms of level `U₁(9)`
(`L(U₁(9), A₃)` of [Jacobs, Def 1.30] at `p = 3`): the level submodule of
`c(ℕ, K₃)`-valued automorphic functions under the `κ`-action of `levelMonoid1`. -/
noncomputable def kappaForms (t : K₃) (ht : ‖t‖ < 1) :
    Submodule K₃ (AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) := sorry

/-- The Hecke operator `U₃ = [U₁(9)·η₃·U₁(9)]` on weight-`κ` forms
[Jacobs, Def 1.32 + p. 24]. -/
noncomputable def heckeU3 (t : K₃) (ht : ‖t‖ < 1) :
    kappaForms t ht →ₗ[K₃] kappaForms t ht := sorry

/-- The `(i,j)` block of the transcribed matrix: `0` on the diagonal, and off the
diagonal the `κ`-action operator with generating function `h_{i,j}` — assembled from the
certificates as `∑_{t' : σ(i,t') = j} kappaOp (etaRep t' · u(i,t')⁻¹)₃`. -/
noncomputable def blockOp (t : K₃) (ht : ‖t‖ < 1) (i j : Fin 3) :
    c(ℕ, K₃) →L[K₃] c(ℕ, K₃) := sorry

/-- The blocks in generating-function form: `blockOp i j = ofGenFun h_{i,j}` for
`i ≠ j` (the transcription of [Jacobs, (2.1.4)–(2.1.9)] in `PhD.Jacobs.U3Data`), and
`blockOp i i = 0` [Jacobs p. 28]. -/
theorem matrixCoeff_blockOp (t : K₃) (ht : ‖t‖ < 1) (i j : Fin 3) (m r : ℕ) :
    matrixCoeff (blockOp t ht i j) m r
      = MvPowerSeries.coeff (Jacobs.idx m r)
          (![![0, Jacobs.h01 t ν₃, Jacobs.h02 t ν₃],
             ![Jacobs.h10 t ν₃, 0, Jacobs.h12 t ν₃],
             ![Jacobs.h20 t ν₃, Jacobs.h21 t ν₃, 0]] i j) := sorry

/-- **AG-B headline (unconditional)**: on the weight-`κ` space, the Hecke operator `U₃`
evaluated at the class representatives is given by the transcribed block matrix:

  `(U₃ φ)(cᵢ) = ∑ⱼ blockOp i j (φ(cⱼ))`.

[Jacobs, pp. 25–28]: the computation `(U₃φ)(cᵢ) = Σ_t φ(cᵢ·wₜ)-action
= Σ_t (action of the certificate) φ(c_{σ(i,t)})`, grouped by target class. -/
theorem heckeU3_apply_classRep (t : K₃) (ht : ‖t‖ < 1) (φ : kappaForms t ht) (i : Fin 3) :
    ((heckeU3 t ht φ : kappaForms t ht) :
        AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) (classRep i)
      = ∑ j : Fin 3, blockOp t ht i j
          ((φ : AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) (classRep j)) :=
  sorry

/-- **Completeness** (needs Theorem 2.1, hence `HClassNumberOne`): evaluation at the
three representatives is injective on `kappaForms` — the block matrix determines `U₃`.
With `stabilizerAt_classRep` this is [Jacobs, (2.1.1)]: `L(U, A₃) ≅ ⊕ᵢ A₃`. -/
theorem eval_classRep_injective (t : K₃) (ht : ‖t‖ < 1)
    (hcn : HClassNumberOne) (φ ψ : kappaForms t ht)
    (h : ∀ i : Fin 3,
      ((φ : kappaForms t ht) :
          AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) (classRep i)
        = ((ψ : kappaForms t ht) :
          AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) (classRep i)) :
    φ = ψ := sorry

/-- Convenience form of `eval_classRep_injective` with the class-number-one hypothesis
discharged by the FLT interface `hClassNumberOne`.

**Depends on the tranche's single external `sorry`** (see `hClassNumberOne`'s contract):
`#print axioms` shows `sorryAx` with exactly that one source until FLT's proof is
ported.  The hypothesis form above is the axiom-clean, board-gradable statement. -/
theorem eval_classRep_injective' (t : K₃) (ht : ‖t‖ < 1) (φ ψ : kappaForms t ht)
    (h : ∀ i : Fin 3,
      ((φ : kappaForms t ht) :
          AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) (classRep i)
        = ((ψ : kappaForms t ht) :
          AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D) c(ℕ, K₃)) (classRep i)) :
    φ = ψ :=
  eval_classRep_injective t ht hClassNumberOne φ ψ h

end Jacobs.U3
