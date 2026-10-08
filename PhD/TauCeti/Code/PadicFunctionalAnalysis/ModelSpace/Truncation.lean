/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Topology.Algebra.Module.Complement
import PhD.TauCeti.Code.PadicFunctionalAnalysis.ModelSpace.Basic

/-!
# Coordinate truncations

For a subset `S ⊆ I`, the truncation `truncation S : C₀(I, R) →L[R] C₀(I, R)` keeps the coordinates
in `S` and sets the others to `0`. It is idempotent, of norm at most `1`, its range (the functions
supported in `S`) is a closed direct summand, and for finite `S` the range is the finite free module
on `S`; the truncations to finite sets converge to the identity pointwise along the filter of finite
subsets. The compact-operators roadmap characterises the operators for which this convergence holds
in operator norm.

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, §2.6.3 and §2.2.5
(the model-space half).
Tau Ceti home: `TauCeti/Analysis/Normed/Module/Ultra/ModelSpace/Truncation.lean`.
-/

open Filter Topology
open scoped ZeroAtInfty ContinuousLinearMap.Ultra

namespace ZeroAtInftyContinuousMap

variable {R : Type*} [NormedRing R] {I : Type*} [TopologicalSpace I] [DiscreteTopology I]

/-- The truncation to a subset `S`: `(truncation S f) i = f i` for `i ∈ S` and `0` otherwise.
Source: roadmap §2.6.3 ("the truncation `π_S : C₀(I, R) →L[R] C₀(I, R)` (restriction of
coordinates to `S`)"). -/
noncomputable def truncation (S : Set I) [DecidablePred (· ∈ S)] : C₀(I, R) →L[R] C₀(I, R) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ofTendsto (fun i ↦ if i ∈ S then f i else 0) (by sorry)
      map_add' := by sorry
      map_smul' := by sorry }
    1 (by sorry)

variable (S : Set I) [DecidablePred (· ∈ S)]

@[simp]
theorem truncation_apply (f : C₀(I, R)) (i : I) :
    truncation S f i = if i ∈ S then f i else 0 := rfl

theorem truncation_apply_of_mem (f : C₀(I, R)) {i : I} (hi : i ∈ S) : truncation S f i = f i := by
  sorry

theorem truncation_apply_of_notMem (f : C₀(I, R)) {i : I} (hi : i ∉ S) :
    truncation S f i = 0 := by
  sorry

/-- Source: roadmap §2.6.3 ("has norm at most `1`"). -/
theorem norm_truncation_apply_le (f : C₀(I, R)) : ‖truncation S f‖ ≤ ‖f‖ := by
  sorry

/-- Source: roadmap §2.6.3 ("has norm at most `1`"), as an operator-norm bound. -/
theorem norm_truncation_le : ‖(truncation S : C₀(I, R) →L[R] C₀(I, R))‖ ≤ 1 := by
  sorry

theorem truncation_truncation (f : C₀(I, R)) : truncation S (truncation S f) = truncation S f := by
  sorry

theorem truncation_single [DecidableEq I] (i : I) (r : R) :
    truncation S (single i r) = if i ∈ S then single i r else 0 := by
  sorry

/-- The distance from `f` to its truncation is the supremum of `‖f i‖` off `S`. -/
theorem norm_sub_truncation_le (f : C₀(I, R)) {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ i ∉ S, ‖f i‖ ≤ ε) :
    ‖f - truncation S f‖ ≤ ε := by
  sorry

theorem mem_range_truncation_iff {f : C₀(I, R)} :
    f ∈ LinearMap.range (truncation (R := R) S : C₀(I, R) →ₗ[R] C₀(I, R)) ↔ ∀ i ∉ S, f i = 0 := by
  sorry

/-- The range of a truncation is a closed direct summand, complemented by the range of the
truncation to the complement. Source: roadmap §2.2.5 ("the closed span of `e|_S` is a closed direct
summand with the projection `π_S` of norm at most `1`"), the model-space case. -/
theorem closedComplemented_range_truncation :
    (LinearMap.range (truncation (R := R) S : C₀(I, R) →ₗ[R] C₀(I, R))).ClosedComplemented := by
  sorry

/-- For a finite `S` the range of the truncation is the finite free module on `S`, spanned by the
coordinate vectors. Source: roadmap §2.6.3 ("has range the finite free module on `S`"). -/
theorem range_truncation_finset [DecidableEq I] (s : Finset I) :
    LinearMap.range (truncation (R := R) (↑s : Set I) : C₀(I, R) →ₗ[R] C₀(I, R)) =
      Submodule.span R (Set.range fun i : s ↦ single (i : I) (1 : R)) := by
  sorry

/-- The truncations to finite sets converge to the identity pointwise along the filter of finite
subsets. Source: roadmap §2.6.3 ("`π_S ∘ u → u` pointwise along the filter of finite subsets for
every bounded `u` into `C₀(I, R)`"). -/
theorem tendsto_truncation_finset [DecidableEq I] (f : C₀(I, R)) :
    Tendsto (fun s : Finset I ↦ truncation (↑s : Set I) f) atTop (𝓝 f) := by
  sorry

/-- Source: roadmap §2.6.3, the form "`π_S ∘ u → u` pointwise". -/
theorem tendsto_truncation_finset_comp [DecidableEq I] {M : Type*} [NormedAddCommGroup M]
    [Module R M] (u : M →L[R] C₀(I, R)) (x : M) :
    Tendsto (fun s : Finset I ↦ truncation (↑s : Set I) (u x)) atTop (𝓝 (u x)) :=
  tendsto_truncation_finset (u x)

end ZeroAtInftyContinuousMap
