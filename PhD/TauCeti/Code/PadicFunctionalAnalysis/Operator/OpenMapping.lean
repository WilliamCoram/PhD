/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Baire.CompleteMetrizable
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Module
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.Norm

/-!
# The open mapping theorem over a Tate normed ring

A surjective continuous linear map `u : M →L[R] N` between Banach modules over a Tate normed ring
admits a constant `C > 0` such that every `y` has a preimage of norm at most `C * ‖y‖`
(`exists_preimage_norm_le`), hence is open. The proof is Mathlib's proof of
`ContinuousLinearMap.exists_preimage_norm_le` — Baire's theorem on `N`, then a geometric series in
`M` — with the scaling trick (`PseudoUniformizer.existsUnique_zpow_norm_smul_mem_Ioc`) in place of
Mathlib's `rescale_to_shell`; neither completeness of `R` nor the ultrametric inequality is used.

⚠ **Seam.** The roadmap (§1.2.1) derives this theorem from Tau Ceti's topological open mapping
theorem over a Tate ring (`TauCeti.HasZeroSequenceOfUnits.isOpenMap`, Henkel's theorem). That
development is not a dependency of this repository, so the theorem is proved directly here; at
migration the direct proof may be replaced by that derivation.

Consequences (roadmap §1.2.2): a bijective continuous linear map is a continuous linear equivalence
(`continuousLinearEquivOfBijective`), and a continuous linear map with closed range is strict — the
induced map `M ⧸ ker u → range u` is a continuous linear equivalence (`quotKerEquivRangeL`), so
the quotient norm and the subspace norm are bounded-equivalent.

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, §1.2.1–§1.2.2. Tau Ceti home:
`TauCeti/Analysis/Normed/Operator/Ultra/OpenMapping.lean`.

## Main results

* `ContinuousLinearMap.Ultra.exists_preimage_norm_le` — the quantitative open mapping theorem.
* `ContinuousLinearMap.Ultra.isOpenMap` — a surjective bounded operator is open.
* `ContinuousLinearMap.Ultra.continuousLinearEquivOfBijective` — bijective implies isomorphism.
* `ContinuousLinearMap.Ultra.quotKerEquivRangeL` — strictness of maps with closed range.
-/

open Filter Topology Metric Function

namespace ContinuousLinearMap.Ultra

open NormedRing

variable {R M N : Type*} [NormedRing R] [NormOneClass R] [IsTate R] [NormedAddCommGroup M]
  [Module R M] [IsBoundedSMul R M] [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]

/-! ### The open mapping theorem -/

section OpenMapping

variable [CompleteSpace N]

/-- Source: Mathlib, `ContinuousLinearMap.exists_approx_preimage_norm_le` ("by Baire's theorem,
there exists a ball in `E` whose image closure has nonempty interior. Rescaling everything, it
follows that any `y ∈ F` is arbitrarily well approached by images of elements of norm at most
`C * ‖y‖`"). -/
theorem exists_approx_preimage_norm_le (u : M →L[R] N) (hu : Surjective u) :
    ∃ C ≥ 0, ∀ y, ∃ x, dist (u x) y ≤ 1 / 2 * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖ := by
  have A : ⋃ n : ℕ, closure (u '' ball 0 n) = Set.univ := by
    refine Set.Subset.antisymm (Set.subset_univ _) fun y _ ↦ ?_
    obtain ⟨x, rfl⟩ := hu y
    obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
    exact Set.mem_iUnion.2 ⟨n, subset_closure ⟨x, by rwa [mem_ball, dist_zero_right], rfl⟩⟩
  obtain ⟨n, a, ha⟩ := nonempty_interior_of_iUnion_of_closed (fun n ↦ isClosed_closure) A
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at ha
  obtain ⟨ε, εpos, H⟩ := ha
  obtain ⟨ϖ⟩ := IsTate.exists_pseudoUniformizer (R := R)
  have hεϖ : 0 < ε * ‖(ϖ : R)‖ := mul_pos εpos ϖ.norm_pos
  refine ⟨4 * n / (ε * ‖(ϖ : R)‖), div_nonneg (by positivity) hεϖ.le, fun y ↦ ?_⟩
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨0, by simp, by simp⟩
  obtain ⟨j, ⟨hj₁, hj₂⟩, -⟩ := ϖ.existsUnique_zpow_norm_smul_mem_Ioc (half_pos εpos) hy
  have ht : 0 < ‖(ϖ : R)‖ ^ j := zpow_pos ϖ.norm_pos j
  have hdy : ‖((ϖ.unit ^ j : Rˣ) : R) • y‖ = ‖(ϖ : R)‖ ^ j * ‖y‖ := ϖ.norm_zpow_smul j y
  have hδ : 0 < ‖((ϖ.unit ^ j : Rˣ) : R) • y‖ / 4 := by
    rw [hdy]
    exact div_pos (mul_pos ht (norm_pos_iff.2 hy)) four_pos
  have h₁ : a + ((ϖ.unit ^ j : Rˣ) : R) • y ∈ ball a ε := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hj₂.trans_lt (half_lt_self εpos)
  obtain ⟨_, ⟨x₁, hx₁, rfl⟩, hz₁⟩ := Metric.mem_closure_iff.1 (H h₁) _ hδ
  obtain ⟨_, ⟨x₂, hx₂, rfl⟩, hz₂⟩ := Metric.mem_closure_iff.1 (H (mem_ball_self εpos)) _ hδ
  rw [mem_ball, dist_zero_right] at hx₁ hx₂
  have hI : ‖u (x₁ - x₂) - ((ϖ.unit ^ j : Rˣ) : R) • y‖ ≤
      2 * (‖((ϖ.unit ^ j : Rˣ) : R) • y‖ / 4) := by
    have e : u (x₁ - x₂) - ((ϖ.unit ^ j : Rˣ) : R) • y =
        (u x₁ - (a + ((ϖ.unit ^ j : Rˣ) : R) • y)) - (u x₂ - a) := by
      rw [map_sub]
      abel
    rw [e, two_mul]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [← dist_eq_norm, dist_comm]
      exact hz₁.le
    · rw [← dist_eq_norm, dist_comm]
      exact hz₂.le
  have hcancel : ((ϖ.unit ^ (-j) : Rˣ) : R) • ((ϖ.unit ^ j : Rˣ) : R) • y = y := by
    rw [smul_smul, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one,
      one_smul]
  refine ⟨((ϖ.unit ^ (-j) : Rˣ) : R) • (x₁ - x₂), ?_, ?_⟩
  · have hsub : u (((ϖ.unit ^ (-j) : Rˣ) : R) • (x₁ - x₂)) - y =
        ((ϖ.unit ^ (-j) : Rˣ) : R) • (u (x₁ - x₂) - ((ϖ.unit ^ j : Rˣ) : R) • y) := by
      rw [map_smul, smul_sub, hcancel]
    rw [dist_eq_norm, hsub, ϖ.norm_zpow_smul, zpow_neg]
    calc (‖(ϖ : R)‖ ^ j)⁻¹ * ‖u (x₁ - x₂) - ((ϖ.unit ^ j : Rˣ) : R) • y‖
        ≤ (‖(ϖ : R)‖ ^ j)⁻¹ * (2 * (‖((ϖ.unit ^ j : Rˣ) : R) • y‖ / 4)) :=
          mul_le_mul_of_nonneg_left hI (inv_nonneg.2 ht.le)
      _ = 1 / 2 * ‖y‖ := by
        rw [hdy]
        field_simp
        ring
  · rw [ϖ.norm_zpow_smul, zpow_neg]
    have hx : ‖x₁ - x₂‖ ≤ 2 * n := by linarith [norm_sub_le x₁ x₂]
    have key : (‖(ϖ : R)‖ ^ j)⁻¹ ≤ 2 * ‖y‖ / (ε * ‖(ϖ : R)‖) := by
      rw [le_div_iff₀ hεϖ, inv_mul_le_iff₀ ht]
      rw [hdy] at hj₁
      calc ε * ‖(ϖ : R)‖ = 2 * (ε / 2 * ‖(ϖ : R)‖) := by ring
        _ ≤ 2 * (‖(ϖ : R)‖ ^ j * ‖y‖) := by linarith
        _ = ‖(ϖ : R)‖ ^ j * (2 * ‖y‖) := by ring
    calc (‖(ϖ : R)‖ ^ j)⁻¹ * ‖x₁ - x₂‖ ≤ 2 * ‖y‖ / (ε * ‖(ϖ : R)‖) * (2 * n) :=
          mul_le_mul key hx (norm_nonneg _) (div_nonneg (by positivity) hεϖ.le)
      _ = 4 * n / (ε * ‖(ϖ : R)‖) * ‖y‖ := by ring

variable [CompleteSpace M]

/-- **The quantitative open mapping theorem.** Source: roadmap §1.2.1; Bellaïche, §II.1.1 ("there
exists a constant `c > 0` such that for every `n` in `N` we can find `m ∈ M` with `f(m) = n` and
`|m| ≤ c|n|`"); Johansson–Newton, Definition 2.1.4 ("The open mapping theorem holds in this
context; see e.g. [Hub94, Lemma 2.4(i)]"); Mathlib,
`ContinuousLinearMap.exists_preimage_norm_le`. -/
theorem exists_preimage_norm_le (u : M →L[R] N) (hu : Surjective u) :
    ∃ C > 0, ∀ y, ∃ x, u x = y ∧ ‖x‖ ≤ C * ‖y‖ := by
  obtain ⟨C, C0, hC⟩ := exists_approx_preimage_norm_le u hu
  choose g hg using hC
  let h y := y - u (g y)
  have hle (y : N) : ‖h y‖ ≤ 1 / 2 * ‖y‖ := by
    rw [← dist_eq_norm, dist_comm]
    exact (hg y).1
  refine ⟨2 * C + 1, by linarith, fun y ↦ ?_⟩
  have hnle (n : ℕ) : ‖h^[n] y‖ ≤ (1 / 2) ^ n * ‖y‖ := by
    induction n with
    | zero => simp only [one_div, one_mul, iterate_zero_apply, pow_zero, le_rfl]
    | succ n IH =>
      rw [iterate_succ']
      refine (hle _).trans ?_
      rw [pow_succ', mul_assoc]
      gcongr
  let v n := g (h^[n] y)
  have vle (n : ℕ) : ‖v n‖ ≤ (1 / 2) ^ n * (C * ‖y‖) := by
    refine (hg _).2.trans ?_
    calc C * ‖h^[n] y‖ ≤ C * ((1 / 2) ^ n * ‖y‖) := by gcongr; exact hnle n
      _ = (1 / 2) ^ n * (C * ‖y‖) := by ring
  have sNv : Summable fun n ↦ ‖v n‖ := by
    refine .of_nonneg_of_le (fun n ↦ norm_nonneg _) vle ?_
    exact Summable.mul_right _ (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have sv : Summable v := sNv.of_norm
  have x_ineq : ‖∑' n, v n‖ ≤ (2 * C + 1) * ‖y‖ :=
    calc ‖∑' n, v n‖ ≤ ∑' n, ‖v n‖ := norm_tsum_le_tsum_norm sNv
      _ ≤ ∑' n, (1 / 2) ^ n * (C * ‖y‖) :=
        sNv.tsum_le_tsum vle <| Summable.mul_right _ summable_geometric_two
      _ = (∑' n : ℕ, (1 / 2 : ℝ) ^ n) * (C * ‖y‖) := tsum_mul_right
      _ = 2 * C * ‖y‖ := by rw [tsum_geometric_two, mul_assoc]
      _ ≤ 2 * C * ‖y‖ + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
      _ = (2 * C + 1) * ‖y‖ := by ring
  have fsumeq (n : ℕ) : u (∑ i ∈ Finset.range n, v i) = y - h^[n] y := by
    induction n with
    | zero => simp
    | succ n IH => rw [Finset.sum_range_succ, map_add, IH, iterate_succ_apply', sub_add]
  have L₁ : Tendsto (fun n ↦ u (∑ i ∈ Finset.range n, v i)) atTop (𝓝 (u (∑' n, v n))) :=
    (u.continuous.tendsto _).comp sv.hasSum.tendsto_sum_nat
  simp only [fsumeq] at L₁
  have L₂ : Tendsto (fun n ↦ y - h^[n] y) atTop (𝓝 (y - 0)) := by
    refine tendsto_const_nhds.sub ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) hnle ?_
    rw [← zero_mul ‖y‖]
    refine (tendsto_pow_atTop_nhds_zero_of_lt_one ?_ ?_).mul tendsto_const_nhds <;> norm_num
  have feq : u (∑' n, v n) = y - 0 := tendsto_nhds_unique L₁ L₂
  rw [sub_zero] at feq
  exact ⟨∑' n, v n, feq, x_ineq⟩

/-- Source: Schneider, Proposition 8.6 ("every surjective continuous linear map `f : V → W` is
open"); Mathlib, `ContinuousLinearMap.isOpenMap`. -/
protected theorem isOpenMap (u : M →L[R] N) (hu : Surjective u) : IsOpenMap u := by
  intro s hs
  obtain ⟨C, Cpos, hC⟩ := exists_preimage_norm_le u hu
  refine Metric.isOpen_iff.2 fun y ⟨x, xs, fxy⟩ ↦ ?_
  obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.1 hs x xs
  refine ⟨ε / C, div_pos εpos Cpos, fun z hz ↦ ?_⟩
  obtain ⟨w, wim, wnorm⟩ := hC (z - y)
  have hw : u (x + w) = z := by rw [map_add, wim, fxy, add_sub_cancel]
  have hxw : x + w ∈ ball x ε :=
    calc dist (x + w) x = ‖w‖ := by simp
      _ ≤ C * ‖z - y‖ := wnorm
      _ < C * (ε / C) := by
        refine mul_lt_mul_of_pos_left ?_ Cpos
        rwa [mem_ball, dist_eq_norm] at hz
      _ = ε := mul_div_cancel₀ _ Cpos.ne'
  exact hw ▸ Set.mem_image_of_mem _ (hε hxw)

/-- Source: Mathlib, `ContinuousLinearMap.isQuotientMap`. -/
theorem isQuotientMap (u : M →L[R] N) (hu : Surjective u) : IsQuotientMap u :=
  (Ultra.isOpenMap u hu).isQuotientMap u.continuous hu

end OpenMapping

/-! ### Bijective operators are isomorphisms -/

section Equiv

variable [CompleteSpace M] [CompleteSpace N]

/-- Source: Schneider, Corollary 8.7 ("Any continuous linear bijection between two `K`-Fréchet
spaces is a topological isomorphism"); Mathlib, `LinearEquiv.continuous_symm`. -/
theorem continuous_symm (e : M ≃ₗ[R] N) (he : Continuous e) : Continuous e.symm := by
  obtain ⟨C, -, hC⟩ := exists_preimage_norm_le (⟨e.toLinearMap, he⟩ : M →L[R] N) e.surjective
  refine AddMonoidHomClass.continuous_of_bound e.symm C fun y ↦ ?_
  obtain ⟨x, hx, hle⟩ := hC y
  have hxy : e.symm y = x := by
    rw [← hx]
    exact e.symm_apply_apply x
  rw [hxy]
  exact hle

/-- A continuous linear equivalence of Banach modules is a continuous linear equivalence. Source:
Schneider, Corollary 8.7; Mathlib, `LinearEquiv.toContinuousLinearEquivOfContinuous`. -/
noncomputable def toContinuousLinearEquivOfContinuous (e : M ≃ₗ[R] N) (he : Continuous e) :
    M ≃L[R] N :=
  { e with
    continuous_toFun := he
    continuous_invFun := continuous_symm e he }

@[simp]
theorem coe_toContinuousLinearEquivOfContinuous (e : M ≃ₗ[R] N) (he : Continuous e) :
    ⇑(toContinuousLinearEquivOfContinuous e he) = e := rfl

/-- Source: roadmap §1.2.2 ("A bijective `u : M →L[R] N` is a continuous linear equivalence");
Mathlib, `ContinuousLinearEquiv.ofBijective`. -/
noncomputable def continuousLinearEquivOfBijective (u : M →L[R] N) (hu : Bijective u) :
    M ≃L[R] N :=
  toContinuousLinearEquivOfContinuous (LinearEquiv.ofBijective (u : M →ₗ[R] N) hu) u.continuous

@[simp]
theorem coe_continuousLinearEquivOfBijective (u : M →L[R] N) (hu : Bijective u) :
    ⇑(continuousLinearEquivOfBijective u hu) = u := rfl

end Equiv

end ContinuousLinearMap.Ultra

/-! ### Strictness -/

namespace ContinuousLinearMap.Ultra

open NormedRing

section Strict

variable {R M N : Type*} [NormedCommRing R] [NormOneClass R] [IsTate R] [NormedAddCommGroup M]
  [Module R M] [IsBoundedSMul R M] [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  (u : M →L[R] N)

/-- Source: BGR 3.7.3/4 (strictness); Schneider, Proposition 8.3 (the quotient norm). -/
theorem norm_quotKerEquivRange_apply_le (x : M ⧸ LinearMap.ker (u : M →ₗ[R] N)) :
    ‖(LinearMap.quotKerEquivRange (u : M →ₗ[R] N) x : N)‖ ≤ ‖u‖ * ‖x‖ := by
  have hu₁ : 0 < ‖u‖ + 1 := add_pos_of_nonneg_of_pos (opNorm_nonneg u) one_pos
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  obtain ⟨m, rfl, hm⟩ := Submodule.Quotient.norm_mk_lt x (div_pos hε hu₁)
  rw [LinearMap.quotKerEquivRange_apply_mk]
  have hfrac : ‖u‖ / (‖u‖ + 1) < 1 := (div_lt_one hu₁).2 (lt_add_one _)
  calc ‖(u : M →ₗ[R] N) m‖ ≤ ‖u‖ * ‖m‖ := le_opNorm u m
    _ ≤ ‖u‖ * (‖(Submodule.Quotient.mk m : M ⧸ LinearMap.ker (u : M →ₗ[R] N))‖ +
          ε / (‖u‖ + 1)) := mul_le_mul_of_nonneg_left hm.le (opNorm_nonneg u)
    _ = ‖u‖ * ‖(Submodule.Quotient.mk m : M ⧸ LinearMap.ker (u : M →ₗ[R] N))‖ +
          ε * (‖u‖ / (‖u‖ + 1)) := by ring
    _ < ‖u‖ * ‖(Submodule.Quotient.mk m : M ⧸ LinearMap.ker (u : M →ₗ[R] N))‖ + ε :=
      by linarith [mul_lt_of_lt_one_right hε hfrac]

variable [CompleteSpace M] [CompleteSpace N]

/-- Source: roadmap §1.2.2 ("the quotient norm and the subspace norm are bounded-equivalent");
BGR 3.7.3/4 ("A continuous `k`-linear map `φ : X → Y` between `k`-Banach spaces is strict if and
only if `φ(X)` is closed in `Y`"). -/
theorem exists_norm_quotKerEquivRange_symm_le
    (hu : IsClosed (LinearMap.range (u : M →ₗ[R] N) : Set N)) :
    ∃ C : ℝ, ∀ y : LinearMap.range (u : M →ₗ[R] N),
      ‖(LinearMap.quotKerEquivRange (u : M →ₗ[R] N)).symm y‖ ≤ C * ‖y‖ := by
  haveI : IsClosed (LinearMap.ker (u : M →ₗ[R] N) : Set M) := u.isClosed_ker
  haveI : CompleteSpace (LinearMap.range (u : M →ₗ[R] N)) := hu.completeSpace_coe
  let ū : (M ⧸ LinearMap.ker (u : M →ₗ[R] N)) →L[R] LinearMap.range (u : M →ₗ[R] N) :=
    LinearMap.mkContinuous (LinearMap.quotKerEquivRange (u : M →ₗ[R] N)).toLinearMap ‖u‖
      (norm_quotKerEquivRange_apply_le u)
  obtain ⟨C, -, hC⟩ := exists_preimage_norm_le ū (LinearMap.quotKerEquivRange _).surjective
  refine ⟨C, fun y ↦ ?_⟩
  obtain ⟨x, hx, hle⟩ := hC y
  have hxy : (LinearMap.quotKerEquivRange (u : M →ₗ[R] N)).symm y = x := by
    rw [← hx]
    exact LinearEquiv.symm_apply_apply _ x
  rw [hxy]
  exact hle

/-- **Strictness.** The map induced on `M ⧸ ker u` by a continuous linear map with closed range is a
continuous linear equivalence onto the range. Source: roadmap §1.2.2; BGR 3.7.3/4. -/
noncomputable def quotKerEquivRangeL (hu : IsClosed (LinearMap.range (u : M →ₗ[R] N) : Set N)) :
    (M ⧸ LinearMap.ker (u : M →ₗ[R] N)) ≃L[R] LinearMap.range (u : M →ₗ[R] N) :=
  haveI : IsClosed (LinearMap.ker (u : M →ₗ[R] N) : Set M) := u.isClosed_ker
  haveI : CompleteSpace (LinearMap.range (u : M →ₗ[R] N)) := hu.completeSpace_coe
  toContinuousLinearEquivOfContinuous (LinearMap.quotKerEquivRange (u : M →ₗ[R] N))
    (AddMonoidHomClass.continuous_of_bound _ ‖u‖ (norm_quotKerEquivRange_apply_le u))

end Strict

end ContinuousLinearMap.Ultra
