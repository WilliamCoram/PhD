/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Topology.MetricSpace.Ultra.Pi
import PhD.TauCeti.Code.PadicFunctionalAnalysis.UnitBall
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.OpenMapping
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.Pi

/-!
# Finitely generated modules over Banach–Tate rings

Two groups of results. First, without any Noetherian hypothesis: every linear map out of a
finitely generated Banach module over a Banach–Tate ring is bounded (Buzzard's Lemma 2.2 — a
surjection `Rⁿ → P` is continuous and open by the open mapping theorem), so any two complete norms
on a finitely generated module are bounded-equivalent. Second, over a *Noetherian* Banach–Tate
ring: every submodule of a finitely generated Banach module is closed (BGR 3.7.2/1, through the
nonarchimedean Nakayama lemma BGR 1.2.4/6), in particular every ideal is closed, and every
finitely generated module is a quotient of some `Rⁿ` by a closed submodule, which is the existence
of a Banach norm on it (BGR 3.7.3/3).

⚠ **Seam.** Roadmap §1.4.1 cites the adic-spaces roadmap for the topological statements of
BGR §3.7.2–§3.7.3 over Banach–Tate rings; that development is not a dependency of this repository,
and the normed readings proved here do not use it. ⚠ The matrix lemma
`TauCeti.Huber.isUnit_one_sub_of_isTopologicallyNilpotent_entries` named in §1.4.2 is likewise
unavailable; the proof uses Mathlib's Nakayama lemma over the unit ball instead, as
`RigidAnalyticGeometry/BanachAlgebra/Noetherian.lean` does for ideals of a Banach algebra over a
field.

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, §1.4.1–§1.4.2. Tau Ceti home:
`TauCeti/Analysis/Normed/Operator/Ultra/Finite.lean`.

## Main results

* `ContinuousLinearMap.Ultra.exists_bound_of_finite` — Buzzard's Lemma 2.2.
* `NormedRing.forall_mem_of_forall_exists_eq_add_sum_smul_of_norm_lt_one` — the nonarchimedean
  Nakayama lemma (BGR 1.2.4/6).
* `Submodule.isClosed_of_fg_topologicalClosure` — BGR 3.7.2/1.
* `Submodule.isClosed_of_isNoetherianRing` — submodules of finitely generated Banach modules over a
  Noetherian Banach–Tate ring are closed.
* `Module.Finite.exists_surjective_isClosed_ker` — the Banach norm of a finitely generated module.
-/

open Filter Topology

open scoped ContinuousLinearMap.Ultra

/-! ### Maps out of finitely generated Banach modules -/

namespace ContinuousLinearMap.Ultra

open NormedRing

variable {R P M : Type*} [NormedRing R] [NormOneClass R] [IsTate R] [CompleteSpace R]
  [NormedAddCommGroup P] [Module R P] [IsBoundedSMul R P] [IsUltrametricDist P] [CompleteSpace P]
  [Module.Finite R P] [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [IsUltrametricDist M]

/-- Source: Buzzard, Lemma 2.2 ("any abstract `A`-module homomorphism `φ : P → M` is continuous.
Proof. Let `π : Aʳ → P` be a surjection of `A`-modules ... Then `π` is open by the Open Mapping
Theorem, and `φπ` is bounded and hence continuous"); Ludwig, Lemma 2.14; BGR 3.7.3/2. -/
theorem exists_bound_of_finite (φ : P →ₗ[R] M) : ∃ C, ∀ x, ‖φ x‖ ≤ C * ‖x‖ := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R P
  obtain ⟨C, -, hC⟩ :=
    exists_preimage_norm_le (⟨π, continuous_pi π⟩ : (Fin n → R) →L[R] P) hπ
  have hS : 0 ≤ ⨆ i, ‖(φ ∘ₗ π) (Pi.single i 1)‖ := Real.iSup_nonneg fun i ↦ norm_nonneg _
  refine ⟨(⨆ i, ‖(φ ∘ₗ π) (Pi.single i 1)‖) * C, fun p ↦ ?_⟩
  obtain ⟨a, rfl, ha⟩ := hC p
  calc ‖φ (π a)‖ = ‖(φ ∘ₗ π) a‖ := rfl
    _ ≤ (⨆ i, ‖(φ ∘ₗ π) (Pi.single i 1)‖) * ‖a‖ := norm_map_le_iSup_mul _ a
    _ ≤ (⨆ i, ‖(φ ∘ₗ π) (Pi.single i 1)‖) * (C * ‖π a‖) := mul_le_mul_of_nonneg_left ha hS
    _ = (⨆ i, ‖(φ ∘ₗ π) (Pi.single i 1)‖) * C * ‖π a‖ := (mul_assoc _ _ _).symm

/-- Source: Buzzard, Lemma 2.2; roadmap §1.4.1 ("any two Banach norms on a finitely generated
module are bounded-equivalent"). -/
theorem continuous_of_finite (φ : P →ₗ[R] M) : Continuous φ := by
  obtain ⟨C, hC⟩ := exists_bound_of_finite φ
  exact AddMonoidHomClass.continuous_of_bound φ C hC

end ContinuousLinearMap.Ultra

/-! ### The nonarchimedean Nakayama lemma -/

section Nakayama

open NormedRing

variable {R M : Type*} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R] [CompleteSpace R]
  [AddCommGroup M] [Module R M]

/-- **The nonarchimedean Nakayama lemma** for submodules. Source: BGR 1.2.4/6 ("Let `N` be a
submodule of `M` such that there are elements `x₁, …, xₙ` in `M` with the property
`M ⊂ N + Σ Ǎ x_μ`. Then `N = M`"), through Mathlib's `Submodule.le_of_le_smul_of_le_jacobson_bot`
over the unit ball with `NormedRing.openUnitBallIdeal_le_jacobson_bot`. -/
theorem NormedRing.forall_mem_of_forall_exists_eq_add_sum_smul_of_norm_lt_one (N : Submodule R M)
    {n : ℕ} (x : Fin n → M)
    (h : ∀ i, ∃ y ∈ N, ∃ c : Fin n → R, (∀ j, ‖c j‖ < 1) ∧ x i = y + ∑ j, c j • x j) :
    ∀ i, x i ∈ N := by
  let N' : Submodule (Subring.unitClosedBall R) M := Submodule.span _ (Set.range x)
  let N₀ : Submodule (Subring.unitClosedBall R) M := N.restrictScalars (Subring.unitClosedBall R)
  have hle : N' ≤ N₀ ⊔ openUnitBallIdeal R • N' := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨y, hy, c, hc, hxi⟩ := h i
    rw [SetLike.mem_coe, hxi]
    refine Submodule.add_mem_sup hy (sum_mem fun j _ ↦ ?_)
    have hcx : c j • x j =
        (⟨c j, Subring.mem_unitClosedBall.2 (hc j).le⟩ : Subring.unitClosedBall R) • x j := rfl
    rw [hcx]
    exact Submodule.smul_mem_smul (mem_openUnitBallIdeal.2 (hc j)) (Submodule.subset_span ⟨j, rfl⟩)
  have hN := Submodule.le_of_le_smul_of_le_jacobson_bot (Submodule.fg_span (Set.finite_range x))
    openUnitBallIdeal_le_jacobson_bot hle
  exact fun i ↦ hN (Submodule.subset_span ⟨i, rfl⟩)

end Nakayama

/-! ### Closedness of submodules -/

section Closed

open NormedRing

variable {R M : Type*} [NormedCommRing R] [NormOneClass R] [IsTate R] [IsUltrametricDist R]
  [CompleteSpace R] [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [IsUltrametricDist M]
  [CompleteSpace M]

omit [IsUltrametricDist R] in
/-- Source: BGR 3.7.2/1 ("By BANACH's Theorem, `π` is open, and therefore `Σ Ǎ xᵢ = π(Ǎⁿ)` is a
neighborhood of `0` in `M̂`"). -/
theorem NormedRing.exists_forall_exists_eq_sum_smul_norm_le {n : ℕ} (x : Fin n → M)
    (J : Submodule R M) (hJ : IsClosed (J : Set M)) (hx : Submodule.span R (Set.range x) = J) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ J, ∃ a : Fin n → R, y = ∑ i, a i • x i ∧ ∀ i, ‖a i‖ ≤ C * ‖y‖ := by
  have hmem (a : Fin n → R) : ∑ i, a i • x i ∈ J :=
    J.sum_mem fun i _ ↦ J.smul_mem _ (hx ▸ Submodule.subset_span ⟨i, rfl⟩)
  let πl : (Fin n → R) →ₗ[R] J :=
    { toFun := fun a ↦ ⟨∑ i, a i • x i, hmem a⟩
      map_add' := fun a b ↦ Subtype.ext (by simp [add_smul, Finset.sum_add_distrib])
      map_smul' := fun c a ↦ Subtype.ext (by simp [Finset.smul_sum, smul_smul]) }
  haveI : CompleteSpace J := hJ.completeSpace_coe
  have hsurj : Function.Surjective πl := by
    rintro ⟨y, hy⟩
    rw [← hx] at hy
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hy
    exact ⟨a, Subtype.ext ha⟩
  obtain ⟨C, hC0, hC⟩ := ContinuousLinearMap.Ultra.exists_preimage_norm_le
    (⟨πl, ContinuousLinearMap.Ultra.continuous_pi πl⟩ : (Fin n → R) →L[R] J) hsurj
  refine ⟨C, hC0, fun y hy ↦ ?_⟩
  obtain ⟨a, ha, hna⟩ := hC ⟨y, hy⟩
  exact ⟨a, (congrArg Subtype.val ha).symm, fun i ↦ (norm_le_pi_norm a i).trans hna⟩

/-- **BGR 3.7.2/1.** Source: BGR 3.7.2/1 ("Let `M` be a normed `A`-module such that the completion
`M̂` of `M` is a finite `A`-module. Then `M` is complete"), for a submodule and its closure. -/
theorem Submodule.isClosed_of_fg_topologicalClosure (N : Submodule R M)
    (hfg : N.topologicalClosure.FG) : IsClosed (N : Set M) := by
  obtain ⟨n, x, hx⟩ := fg_iff_exists_fin_generating_family.1 hfg
  obtain ⟨C, hC0, hC⟩ :=
    exists_forall_exists_eq_sum_smul_norm_le x _ N.isClosed_topologicalClosure hx
  have hxN : ∀ i, x i ∈ N := by
    refine forall_mem_of_forall_exists_eq_add_sum_smul_of_norm_lt_one N x fun i ↦ ?_
    have hxi : x i ∈ N.topologicalClosure := hx ▸ subset_span ⟨i, rfl⟩
    have hxi' : x i ∈ closure (N : Set M) := by
      rw [← topologicalClosure_coe]
      exact hxi
    obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.1 hxi' C⁻¹ (inv_pos.2 hC0)
    obtain ⟨c, hc, hcn⟩ := hC _ (N.topologicalClosure.sub_mem hxi (N.le_topologicalClosure hy))
    refine ⟨y, hy, c, fun j ↦ ?_, ?_⟩
    · calc ‖c j‖ ≤ C * ‖x i - y‖ := hcn j
        _ < C * C⁻¹ := mul_lt_mul_of_pos_left (by rwa [← dist_eq_norm]) hC0
        _ = 1 := mul_inv_cancel₀ hC0.ne'
    · rw [← hc]
      abel
  refine isClosed_of_closure_subset fun z hz ↦ ?_
  have hz' : z ∈ N.topologicalClosure := by
    rw [← SetLike.mem_coe, topologicalClosure_coe]
    exact hz
  rw [← hx] at hz'
  exact span_le.2 (by rintro _ ⟨i, rfl⟩; exact hxN i) hz'

/-- Source: roadmap §1.4.2 ("Every submodule of a module-finite Banach `R`-module is closed");
BGR 3.7.2/1–2 ("all submodules of a Noetherian complete normed module over a Banach algebra `A`
are closed"); Fresnel–van der Put, Lemma 1.2.3; Johansson–Newton, §2.1 ("The results of
[BGR84, §3.7.2] hold in the context of Banach–Tate rings with the same proofs"). -/
theorem Submodule.isClosed_of_isNoetherianRing [IsNoetherianRing R] [Module.Finite R M]
    (N : Submodule R M) : IsClosed (N : Set M) := by
  haveI := isNoetherian_of_isNoetherianRing_of_finite R M
  exact N.isClosed_of_fg_topologicalClosure (IsNoetherian.noetherian _)

/-- Source: roadmap §1.4.1 ("every ideal of `R` is closed"); BGR 3.7.2/2; Buzzard, §2 ("all ideals
of `A` are closed, by Proposition 3.7.2/2 of [1]"). -/
theorem Ideal.isClosed_of_isTate_of_isNoetherianRing [IsNoetherianRing R] (I : Ideal R) :
    IsClosed (I : Set R) :=
  Submodule.isClosed_of_isNoetherianRing (M := R) I

/-- Source: roadmap §1.4.1 ("a Banach norm exists (the quotient norm from `R ^ n`)"); BGR 3.7.3/3
("Take any `A`-linear epimorphism `π : Aⁿ → M`. Since `Aⁿ ∈ 𝔐_A`, the kernel `ker π` is closed.
The residue norm on `Aⁿ/ker π` gives rise to a complete `A`-module norm on `M`"). -/
theorem Module.Finite.exists_surjective_isClosed_ker [IsNoetherianRing R] (P : Type*)
    [AddCommGroup P] [Module R P] [Module.Finite R P] :
    ∃ (n : ℕ) (π : (Fin n → R) →ₗ[R] P),
      Function.Surjective π ∧ IsClosed (LinearMap.ker π : Set (Fin n → R)) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R P
  exact ⟨n, π, hπ, Submodule.isClosed_of_isNoetherianRing _⟩

end Closed
