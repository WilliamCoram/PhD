/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.PadicFunctionalAnalysis.ModelSpace.Reindex

/-!
# Functoriality of the model space in the ring

A bounded ring homomorphism `φ : R →+* S` (`‖φ r‖ ≤ C * ‖r‖`) induces a `φ`-semilinear map
`map φ C hφ : C₀(I, R) →SL[φ] C₀(I, S)`, `f ↦ φ ∘ f`, of norm at most `C`, an isometry when `φ`
is, compatible with the coordinate vectors, the coordinate functionals and reindexing.

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, §2.1.5.
Tau Ceti home: `TauCeti/Analysis/Normed/Module/Ultra/ModelSpace/Map.lean`.
-/

open Filter Topology
open scoped ZeroAtInfty

namespace ZeroAtInftyContinuousMap

variable {R S : Type*} [NormedRing R] [NormedRing S] {I : Type*} [TopologicalSpace I]
  [DiscreteTopology I]

/-- The `φ`-semilinear map `f ↦ φ ∘ f` induced by a bounded ring homomorphism. Source: roadmap
§2.1.5 ("A bounded ring homomorphism `φ : R → S` induces `C₀(I, R) → C₀(I, S)`"). -/
noncomputable def map (φ : R →+* S) (C : ℝ) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) :
    C₀(I, R) →SL[φ] C₀(I, S) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ofTendsto (fun i ↦ φ (f i)) (by sorry)
      map_add' := by sorry
      map_smul' := by sorry }
    (max C 0) (by sorry)

@[simp]
theorem map_apply (φ : R →+* S) (C : ℝ) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (f : C₀(I, R)) (i : I) :
    map φ C hφ f i = φ (f i) := rfl

theorem map_single [DecidableEq I] (φ : R →+* S) (C : ℝ) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (i : I)
    (r : R) : map φ C hφ (single i r) = single i (φ r) := by
  sorry

/-- Source: roadmap §2.1.5 ("of norm at most the bound of `φ`"). -/
theorem norm_map_apply_le (φ : R →+* S) {C : ℝ} (hC : 0 ≤ C) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
    (f : C₀(I, R)) : ‖map φ C hφ f‖ ≤ C * ‖f‖ := by
  sorry

/-- Source: roadmap §2.1.5 ("an isometry when `φ` is"). -/
theorem norm_map_apply_of_forall_norm_eq (φ : R →+* S) (hφ : ∀ r, ‖φ r‖ = ‖r‖) (f : C₀(I, R)) :
    ‖map φ 1 (fun r ↦ by rw [one_mul, hφ]) f‖ = ‖f‖ := by
  sorry

/-- Compatibility with reindexing. Source: roadmap §2.1.5 ("compatible with `single`, `eval`, and
reindexing"). -/
theorem map_reindex {J : Type*} [TopologicalSpace J] [DiscreteTopology J] (φ : R →+* S) (C : ℝ)
    (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (e : I ≃ J) (f : C₀(I, R)) :
    map φ C hφ (reindex (R := R) e f) = reindex (R := S) e (map φ C hφ f) := by
  sorry

end ZeroAtInftyContinuousMap
