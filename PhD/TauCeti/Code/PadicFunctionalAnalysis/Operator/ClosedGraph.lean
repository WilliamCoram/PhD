/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Module
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.OpenMapping

/-!
# The closed graph theorem over a Tate normed ring

A linear map between Banach modules over a Tate normed ring whose graph is closed is continuous.
The proof is Mathlib's proof of `LinearMap.continuous_of_isClosed_graph`: the graph is a closed,
hence complete, submodule of `M × N`, its first projection is a continuous linear bijection onto
`M`, hence a continuous linear equivalence by the open mapping theorem, and `f` is the second
projection composed with the inverse. Schneider proves the closed graph theorem first and deduces
the open mapping theorem (Propositions 8.5–8.6); here the order is reversed, as in Mathlib.

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, §1.2.3. Tau Ceti home:
`TauCeti/Analysis/Normed/Operator/Ultra/ClosedGraph.lean`.

## Main results

* `ContinuousLinearMap.Ultra.continuous_of_isClosed_graph` — the closed graph theorem.
* `ContinuousLinearMap.Ultra.continuous_of_seq_closed_graph` — its sequential form.
-/

open Filter Topology

namespace ContinuousLinearMap.Ultra

open NormedRing

variable {R M N : Type*} [NormedRing R] [NormOneClass R] [IsTate R] [NormedAddCommGroup M]
  [Module R M] [IsBoundedSMul R M] [CompleteSpace M] [NormedAddCommGroup N] [Module R N]
  [IsBoundedSMul R N] [CompleteSpace N]

/-- **The closed graph theorem.** Source: roadmap §1.2.3; Schneider, Proposition 8.5 ("if the
graph `Γ(f)` is closed then the map `f` is continuous"); Mathlib,
`LinearMap.continuous_of_isClosed_graph`. -/
theorem continuous_of_isClosed_graph (f : M →ₗ[R] N) (hf : IsClosed (f.graph : Set (M × N))) :
    Continuous f := by
  haveI : CompleteSpace f.graph := completeSpace_coe_iff_isComplete.mpr hf.isComplete
  let φ₀ : M →ₗ[R] M × N := LinearMap.id.prod f
  have hφ₀ : Function.LeftInverse Prod.fst φ₀ := fun _ ↦ rfl
  let φ : M ≃ₗ[R] f.graph :=
    (LinearEquiv.ofLeftInverse hφ₀).trans (LinearEquiv.ofEq _ _ f.graph_eq_range_prod.symm)
  let ψ : f.graph ≃L[R] M := toContinuousLinearEquivOfContinuous φ.symm continuous_subtype_val.fst
  exact (continuous_subtype_val.comp ψ.symm.continuous).snd

/-- Source: Mathlib, `LinearMap.continuous_of_seq_closed_graph` ("for any convergent sequence
`uₙ ⟶ x`, if `f(uₙ) ⟶ y` then `y = f(x)`"). -/
theorem continuous_of_seq_closed_graph (f : M →ₗ[R] N)
    (hf : ∀ (u : ℕ → M) (x : M) (y : N), Tendsto u atTop (𝓝 x) → Tendsto (f ∘ u) atTop (𝓝 y) →
      y = f x) :
    Continuous f := by
  refine continuous_of_isClosed_graph f (IsSeqClosed.isClosed ?_)
  rintro φ ⟨x, y⟩ hφg hφ
  refine hf (Prod.fst ∘ φ) x y ((continuous_fst.tendsto _).comp hφ) ?_
  have hfφ : f ∘ Prod.fst ∘ φ = Prod.snd ∘ φ := funext fun n ↦ (hφg n).symm
  rw [hfφ]
  exact (continuous_snd.tendsto _).comp hφ

end ContinuousLinearMap.Ultra
