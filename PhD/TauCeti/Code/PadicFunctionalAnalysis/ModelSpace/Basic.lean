/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Sums
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.Norm

/-!
# The model space `C₀(I, R)` on a discrete index set

The model space `c₀(I, R)` of the `p`-adic functional analysis roadmap — families `I → R` tending
to `0` cofinitely, with the sup norm — is Mathlib's `C₀(I, R)` for `I` carrying the discrete
topology (roadmap convention 3): no new type is introduced. This file adds the instances Mathlib
lacks (`IsUltrametricDist`, and `IsBoundedSMul R` for a normed *ring* `R`), the sup-norm formula and
its companions, the coordinate vectors `single i x`, the coordinate functionals `evalCLM R i`, and
the expansion `f = ∑' i, single i (f i)` with its consequence that finitely supported families are
dense.

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, §2.1.1–2.1.2.
Tau Ceti home: `TauCeti/Analysis/Normed/Module/Ultra/ModelSpace/Basic.lean`.

## Main declarations

* `ZeroAtInftyContinuousMap.instIsUltrametricDist`, `ZeroAtInftyContinuousMap.instIsBoundedSMul`,
  `ZeroAtInftyContinuousMap.instNormSMulClass` — the missing instances (§2.1.1).
* `ZeroAtInftyContinuousMap.norm_eq_iSup`, `norm_apply_le`, `norm_le_of_forall_le`,
  `exists_norm_apply_eq_norm`, `tendsto_cofinite` — the sup norm (§2.1.1).
* `ZeroAtInftyContinuousMap.ofTendsto`, `ZeroAtInftyContinuousMap.single`,
  `ZeroAtInftyContinuousMap.evalCLM`, `norm_evalCLM` — coordinates (§2.1.2).
* `ZeroAtInftyContinuousMap.hasSum_single_apply`, `hasSum_smul_single_one`,
  `dense_span_range_single` — the expansion in coordinates (§2.1.2).
-/

open Filter Topology
open scoped ZeroAtInfty

namespace ZeroAtInftyContinuousMap

/-! ### The sup norm -/

section Norm

variable {I E : Type*} [TopologicalSpace I] [SeminormedAddCommGroup E]

/-- The norm of `C₀(I, E)` is the supremum of the norms of the values. Source: roadmap §2.1.1
("the sup-norm formula `‖f‖ = ⨆ i, ‖f i‖`"); Mathlib, `BoundedContinuousFunction.norm_eq_iSup_norm`
through `ZeroAtInftyContinuousMap.norm_toBCF_eq_norm`. -/
theorem norm_eq_iSup (f : C₀(I, E)) : ‖f‖ = ⨆ i, ‖f i‖ := by
  sorry

/-- Source: Mathlib, `BoundedContinuousFunction.norm_coe_le_norm`. -/
theorem norm_apply_le (f : C₀(I, E)) (i : I) : ‖f i‖ ≤ ‖f‖ := by
  sorry

/-- Source: Mathlib, `BoundedContinuousFunction.norm_le`. -/
theorem norm_le_of_forall_le {f : C₀(I, E)} {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, ‖f i‖ ≤ C) :
    ‖f‖ ≤ C := by
  sorry

/-- Evaluation of a finite sum. -/
theorem sum_apply {ι : Type*} (s : Finset ι) (F : ι → C₀(I, E)) (i : I) :
    (∑ j ∈ s, F j) i = ∑ j ∈ s, F j i := by
  sorry

/-- The sup norm of ultrametric-valued functions is ultrametric. Source: roadmap §2.1.1 ("the
instances Mathlib lacks: `IsUltrametricDist`"). -/
instance instIsUltrametricDist [IsUltrametricDist E] : IsUltrametricDist C₀(I, E) := by
  sorry

end Norm

/-! ### The module structure over a normed ring -/

section Module

variable {I E R : Type*} [TopologicalSpace I] [SeminormedAddCommGroup E] [SeminormedRing R]
  [Module R E] [IsBoundedSMul R E]

/-- The action of a normed ring on `C₀(I, E)` is bounded: `‖r • f‖ ≤ ‖r‖ * ‖f‖`. Source: roadmap
§2.1.1 ("`Module R C₀(I, E)` with `IsBoundedSMul R C₀(I, E)`"). -/
instance instIsBoundedSMul : IsBoundedSMul R C₀(I, E) := by
  sorry

/-- When the action on `E` is multiplicative, so is the action on `C₀(I, E)`. Source: roadmap
§2.1.1 ("and `NormSMulClass` when `E` has it"). -/
instance instNormSMulClass [NormSMulClass R E] : NormSMulClass R C₀(I, E) := by
  sorry

/-- The coordinate functional `f ↦ f i`, continuous of norm at most `1`. Source: roadmap §2.1.2
("the coordinate functionals `eval i`"). -/
noncomputable def evalCLM (R : Type*) [SeminormedRing R] [Module R E] [IsBoundedSMul R E] (i : I) :
    C₀(I, E) →L[R] E :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ f i
      map_add' := fun f g ↦ rfl
      map_smul' := fun r f ↦ rfl }
    1 (fun f ↦ by rw [one_mul]; exact norm_apply_le f i)

@[simp]
theorem evalCLM_apply (i : I) (f : C₀(I, E)) : evalCLM R i f = f i := rfl

end Module

/-! ### Discrete index sets -/

section Discrete

variable {I E : Type*} [TopologicalSpace I] [DiscreteTopology I] [SeminormedAddCommGroup E]

/-- On a discrete index set, "vanishing at infinity" is "tending to `0` cofinitely". Source:
roadmap §2.1.1 ("that `f → 0` cofinitely"); Mathlib, `cocompact_eq_cofinite`. -/
theorem tendsto_cofinite (f : C₀(I, E)) : Tendsto f cofinite (𝓝 0) := by
  sorry

/-- The sup norm is attained. Source: roadmap §2.1.1 ("the supremum is attained when `f ≠ 0`");
Layer 0, `Filter.Tendsto.exists_norm_eq_iSup`. -/
theorem exists_norm_apply_eq_norm [Nonempty I] (f : C₀(I, E)) : ∃ i, ‖f i‖ = ‖f‖ := by
  sorry

/-- A family tending to `0` cofinitely, as an element of `C₀(I, E)`: continuity is automatic on a
discrete domain. Source: roadmap convention 3. -/
def ofTendsto (g : I → E) (hg : Tendsto g cofinite (𝓝 0)) : C₀(I, E) :=
  ⟨⟨g, continuous_of_discreteTopology⟩, by rwa [cocompact_eq_cofinite]⟩

@[simp]
theorem coe_ofTendsto (g : I → E) (hg : Tendsto g cofinite (𝓝 0)) : ⇑(ofTendsto g hg) = g := rfl

variable [DecidableEq I]

/-- The coordinate vector `single i x`, supported at `i` with value `x`. Source: roadmap §2.1.2
("The coordinate vectors `single i r`"). -/
def single (i : I) (x : E) : C₀(I, E) :=
  ofTendsto (Pi.single i x) (by sorry)

@[simp]
theorem coe_single (i : I) (x : E) : ⇑(single i x) = Pi.single i x := rfl

theorem single_apply_self (i : I) (x : E) : single i x i = x := by
  sorry

theorem single_apply_of_ne {i j : I} (h : j ≠ i) (x : E) : single i x j = 0 := by
  sorry

@[simp]
theorem single_zero (i : I) : single i (0 : E) = 0 := by
  sorry

@[simp]
theorem norm_single (i : I) (x : E) : ‖single i x‖ = ‖x‖ := by
  sorry

theorem smul_single {R : Type*} [SeminormedRing R] [Module R E] [IsBoundedSMul R E] (r : R)
    (i : I) (x : E) : r • single i x = single i (r • x) := by
  sorry

/-- The expansion of `f` in the coordinate vectors, convergent in norm: the partial sum over a
finite `s` is the truncation of `f` to `s`, which is within `sup_{i ∉ s} ‖f i‖` of `f`. Source:
roadmap §2.1.2 ("the expansion `f = ∑' i, f i • single i 1`, convergent in norm"). -/
theorem hasSum_single_apply (f : C₀(I, E)) : HasSum (fun i ↦ single i (f i)) f := by
  sorry

/-- Finitely supported families are dense. Source: roadmap §2.1.2 ("finitely supported families
are dense"). -/
theorem dense_span_range_single (R : Type*) [SeminormedRing R] [Module R E] [IsBoundedSMul R E] :
    Dense (Submodule.span R (Set.range fun p : I × E ↦ single p.1 p.2) : Set C₀(I, E)) := by
  sorry

end Discrete

/-! ### The model space `C₀(I, R)` itself -/

section Ring

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [NormedRing R] [DecidableEq I]

/-- The expansion `f = ∑' i, f i • single i 1` in `C₀(I, R)`. Source: roadmap §2.1.2. -/
theorem hasSum_smul_single_one (f : C₀(I, R)) : HasSum (fun i ↦ f i • single i (1 : R)) f := by
  sorry

/-- The span of the coordinate vectors `single i 1` is dense in `C₀(I, R)`. Source: roadmap
§2.1.2. -/
theorem dense_span_range_single_one :
    Dense (Submodule.span R (Set.range fun i : I ↦ single i (1 : R)) : Set C₀(I, R)) := by
  sorry

open scoped ContinuousLinearMap.Ultra in
/-- The coordinate functional has operator norm exactly `1`: it is bounded by `1` and takes the
value `1` at `single i 1`. Source: roadmap §2.1.2 ("the coordinate functionals
`eval i : C₀(I, R) →L[R] R` of norm `1`"), roadmap Layer 1 Examples ("coordinate evaluation of
norm `1`"). -/
theorem norm_evalCLM [NormOneClass R] (i : I) : ‖(evalCLM R i : C₀(I, R) →L[R] R)‖ = 1 := by
  sorry

end Ring

end ZeroAtInftyContinuousMap

namespace ZeroAtInftyContinuousMap

/-- The support of an element of `C₀(I, E)` on a discrete `I` is countable: it is the union over
`n` of the finite sets `{i | 1 / (n + 1) < ‖f i‖}`. Source: Schneider §3, Example after Cor. 3.2
("each `Y_x` is finite or countable", used in Lemma 10.3). -/
theorem countable_support {I E : Type*} [TopologicalSpace I] [DiscreteTopology I]
    [SeminormedAddCommGroup E] (f : C₀(I, E)) : {i | f i ≠ 0}.Countable := by
  sorry

end ZeroAtInftyContinuousMap
