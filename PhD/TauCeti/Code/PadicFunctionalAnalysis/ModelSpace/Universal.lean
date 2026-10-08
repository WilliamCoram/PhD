/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import PhD.TauCeti.Code.PadicFunctionalAnalysis.ModelSpace.Basic

/-!
# The universal property of the model space

A bounded family `m : I → M` in a Banach module `M` over a nonarchimedean normed ring `R` induces
the continuous linear map `ofBounded m : C₀(I, R) →L[R] M`, `f ↦ ∑' i, f i • m i`, of norm
`sup ‖m i‖`; it sends `single i 1` to `m i`, and a continuous linear map out of `C₀(I, R)` is
determined by its values on the `single i 1`. Over a Tate ring every continuous linear map out of
`C₀(I, R)` arises this way, because its values on the `single i 1` are bounded by its operator
norm. This is Buzzard's description of maps out of `c_A(I)` and Schneider's universal property of
`c₀(X)`.

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, §2.1.3.
Tau Ceti home: `TauCeti/Analysis/Normed/Module/Ultra/ModelSpace/Universal.lean`.

## Main declarations

* `ZeroAtInftyContinuousMap.ofBounded` — the map `f ↦ ∑' i, f i • m i`.
* `ZeroAtInftyContinuousMap.norm_ofBounded` — its norm is `⨆ i, ‖m i‖`.
* `ZeroAtInftyContinuousMap.ext_single` — uniqueness.
* `ZeroAtInftyContinuousMap.eq_ofBounded` — over a Tate ring, every map is of this form.
-/

open Filter Topology
open scoped ZeroAtInfty ContinuousLinearMap.Ultra

namespace ZeroAtInftyContinuousMap

open NormedRing

section Uniqueness

variable {R I M : Type*} [NormedRing R] [TopologicalSpace I] [DiscreteTopology I]
  [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [DecidableEq I]

/-- A continuous linear map out of `C₀(I, R)` is determined by its values on the coordinate
vectors, by the expansion `hasSum_smul_single_one` and continuity. Source: Schneider §3,
universal property of `c₀(X)` ("`f` is uniquely determined by its values on the `1_x`"); Buzzard
§2 ("a continuous linear map `c_A(I) → M` is determined by the images of the `e_i`"). -/
theorem ext_single {u v : C₀(I, R) →L[R] M} (h : ∀ i, u (single i 1) = v (single i 1)) : u = v := by
  sorry

/-- The expansion of `u f` along the coordinate expansion of `f`. -/
theorem hasSum_smul_apply_single (u : C₀(I, R) →L[R] M) (f : C₀(I, R)) :
    HasSum (fun i ↦ f i • u (single i 1)) (u f) := by
  sorry

/-- Over a Tate ring the values of a continuous linear map on the coordinate vectors are bounded
by its operator norm. Source: roadmap §2.1.3; Layer 1, `ContinuousLinearMap.Ultra.le_opNorm`. -/
theorem exists_bound_single [NormOneClass R] [IsTate R] (u : C₀(I, R) →L[R] M) :
    ∃ C, ∀ i, ‖u (single i 1)‖ ≤ C := by
  sorry

end Uniqueness

section OfBounded

variable {R I M : Type*} [NormedRing R] [TopologicalSpace I] [DiscreteTopology I]
  [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [IsUltrametricDist M] [CompleteSpace M]

/-- The family `i ↦ f i • m i` is summable for `f ∈ C₀(I, R)` and bounded `m`, in a complete
ultrametric module. Source: Schneider §3 (universal property: "`∑ (x) v_x` converges since
`(x) → 0` and the `v_x` are bounded"); Mathlib,
`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`. -/
theorem summable_smul_of_bounded (f : C₀(I, R)) (m : I → M) (hm : ∃ C, ∀ i, ‖m i‖ ≤ C) :
    Summable fun i ↦ f i • m i := by
  sorry

/-- The sum of a coordinate expansion against a bounded family is bounded by the supremum of the
family times the sup norm. Source: Schneider §3 ("`‖f()‖ ≤ sup ‖v_x‖ · ‖‖_∞`"). -/
theorem norm_tsum_smul_le (f : C₀(I, R)) (m : I → M) (hm : ∃ C, ∀ i, ‖m i‖ ≤ C) :
    ‖∑' i, f i • m i‖ ≤ (⨆ i, ‖m i‖) * ‖f‖ := by
  sorry

variable (R) in
/-- **The universal property of the model space**: a bounded family `m : I → M` induces the
continuous linear map `f ↦ ∑' i, f i • m i`. Source: roadmap §2.1.3; Schneider §3 ("for any map
`x ↦ v_x` into a bounded subset of `V` there is a unique continuous linear map `f : c₀(X) → V`
with `f(1_x) = v_x`"); Buzzard §2. -/
noncomputable def ofBounded (m : I → M) (hm : ∃ C, ∀ i, ‖m i‖ ≤ C) : C₀(I, R) →L[R] M :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ∑' i, f i • m i
      map_add' := by sorry
      map_smul' := by sorry }
    (⨆ i, ‖m i‖) (fun f ↦ norm_tsum_smul_le f m hm)

@[simp]
theorem ofBounded_apply (m : I → M) (hm : ∃ C, ∀ i, ‖m i‖ ≤ C) (f : C₀(I, R)) :
    ofBounded R m hm f = ∑' i, f i • m i := rfl

theorem hasSum_ofBounded (m : I → M) (hm : ∃ C, ∀ i, ‖m i‖ ≤ C) (f : C₀(I, R)) :
    HasSum (fun i ↦ f i • m i) (ofBounded R m hm f) := by
  sorry

theorem norm_ofBounded_apply_le (m : I → M) (hm : ∃ C, ∀ i, ‖m i‖ ≤ C) (f : C₀(I, R)) :
    ‖ofBounded R m hm f‖ ≤ (⨆ i, ‖m i‖) * ‖f‖ :=
  norm_tsum_smul_le f m hm

variable (R) in
/-- Source: roadmap §2.1.3 ("with `‖u‖ = sup ‖m i‖`"), the inequality `≤`. -/
theorem norm_ofBounded_le (m : I → M) (hm : ∃ C, ∀ i, ‖m i‖ ≤ C) :
    ‖ofBounded R m hm‖ ≤ ⨆ i, ‖m i‖ := by
  sorry

variable [DecidableEq I]

/-- The induced map sends the coordinate vector `single i 1` to `m i`. Source: Schneider §3
("`f(1_x) = v_x`"). -/
@[simp]
theorem ofBounded_single (m : I → M) (hm : ∃ C, ∀ i, ‖m i‖ ≤ C) (i : I) :
    ofBounded R m hm (single i (1 : R)) = m i := by
  sorry

variable (R) in
/-- The norm of the induced map is the supremum of the family. Source: roadmap §2.1.3 ("with
`‖u‖ = sup ‖m i‖`"); Buzzard §2 ("the norm of the map is `sup_i ‖m_i‖`"). -/
theorem norm_ofBounded [NormOneClass R] (m : I → M) (hm : ∃ C, ∀ i, ‖m i‖ ≤ C) :
    ‖ofBounded R m hm‖ = ⨆ i, ‖m i‖ := by
  sorry

/-- Over a Tate ring, every continuous linear map out of the model space is induced by the bounded
family of its values on the coordinate vectors. Source: roadmap §2.1.3 ("bounded families `I → M`
correspond to continuous linear maps `C₀(I, R) →L[R] M`"). -/
theorem eq_ofBounded [NormOneClass R] [IsTate R] (u : C₀(I, R) →L[R] M) :
    u = ofBounded R (fun i ↦ u (single i 1)) (exists_bound_single u) := by
  sorry

end OfBounded

end ZeroAtInftyContinuousMap
