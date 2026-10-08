/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.Norm

/-!
# Bounded maps out of a finite free module

Every linear map `ι → R → M` out of a finite free module with the sup norm, into an ultrametric
normed `R`-module, is bounded by the largest norm of the images of the basis vectors, hence
continuous, and its operator norm is that largest norm. No Tate hypothesis is needed. This is the
input to Buzzard's Lemma 2.2 and to the closedness theorems of `Operator/Finite.lean`.

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, §1.2.5. Tau Ceti home:
`TauCeti/Analysis/Normed/Operator/Ultra/Pi.lean`.

## Main results

* `ContinuousLinearMap.Ultra.norm_map_le_iSup_mul` — the bound.
* `ContinuousLinearMap.Ultra.continuous_pi` — continuity.
* `ContinuousLinearMap.Ultra.opNorm_pi_eq` — the operator norm is the maximum over the basis.
-/

open Filter Topology

namespace ContinuousLinearMap.Ultra

variable {R M : Type*} [NormedRing R] [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [IsUltrametricDist M] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Source: Schneider, Proposition 4.13, Step 1 ("`q(v) ≤ (max_{1≤i≤n} q(eᵢ)) ⋅ ‖v‖` for any
`v ∈ V`"); BGR 3.7.3/2 ("Since addition and scalar multiplication are continuous operations in
normed modules, both maps `π` and `φ'` are continuous"). -/
theorem norm_map_le_iSup_mul (f : (ι → R) →ₗ[R] M) (x : ι → R) :
    ‖f x‖ ≤ (⨆ i, ‖f (Pi.single i 1)‖) * ‖x‖ := by
  have hS : 0 ≤ ⨆ i, ‖f (Pi.single i 1)‖ := Real.iSup_nonneg fun i ↦ norm_nonneg _
  have hbdd : BddAbove (Set.range fun i ↦ ‖f (Pi.single i 1)‖) := (Set.finite_range _).bddAbove
  have hx : ∑ i, x i • Pi.single i (1 : R) = x := by
    simp_rw [← Pi.single_smul, smul_eq_mul, mul_one]
    exact Finset.univ_sum_single x
  conv_lhs => rw [← hx]
  rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hS (norm_nonneg x))
    fun i _ ↦ ?_
  rw [map_smul]
  calc ‖x i • f (Pi.single i 1)‖ ≤ ‖x i‖ * ‖f (Pi.single i 1)‖ := norm_smul_le _ _
    _ ≤ ‖x‖ * ⨆ j, ‖f (Pi.single j 1)‖ :=
      mul_le_mul (norm_le_pi_norm x i) (le_ciSup hbdd i) (norm_nonneg _) (norm_nonneg _)
    _ = (⨆ j, ‖f (Pi.single j 1)‖) * ‖x‖ := mul_comm _ _

/-- Source: roadmap §1.2.5 ("Every `R`-linear map `R ^ n → M` is continuous"). -/
theorem continuous_pi (f : (ι → R) →ₗ[R] M) : Continuous f :=
  AddMonoidHomClass.continuous_of_bound f _ (norm_map_le_iSup_mul f)

/-- Source: roadmap §1.2.5 ("with norm the maximum of the norms of the images of the basis
vectors"). -/
theorem opNorm_pi_eq [NormOneClass R] (u : (ι → R) →L[R] M) :
    ‖u‖ = ⨆ i, ‖u (Pi.single i 1)‖ := by
  refine le_antisymm (opNorm_le_bound u (Real.iSup_nonneg fun i ↦ norm_nonneg _)
    (norm_map_le_iSup_mul (u : (ι → R) →ₗ[R] M))) ?_
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Real.iSup_of_isEmpty]
    exact opNorm_nonneg u
  refine ciSup_le fun i ↦ ?_
  have h := le_opNorm_of_bound u ⟨_, norm_map_le_iSup_mul (u : (ι → R) →ₗ[R] M)⟩ (Pi.single i 1)
  rwa [Pi.norm_single, norm_one, mul_one] at h

end ContinuousLinearMap.Ultra
