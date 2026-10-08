/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# Sums in ultrametric normed groups

In a complete ultrametric normed group a family is summable exactly when it tends to `0` along the
cofinite filter (Mathlib: `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`), and the sum
is bounded by the largest term (Mathlib: `IsUltrametricDist.norm_tsum_le`). This file adds what the
rest of the development uses on top of those two facts: the largest term is attained, the strict
bound, the *unique dominant term* principle, null families on a product and their iterated sums,
and the sum of a bounded biadditive map applied to two summable families.

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, §0.1. Tau Ceti home:
`TauCeti/Analysis/Normed/Group/Ultra/InfiniteSum.lean`.

## Main results

* `Filter.Tendsto.exists_forall_norm_le` — a null family attains its largest norm.
* `IsUltrametricDist.norm_tsum_lt_of_forall_lt` — the strict bound.
* `IsUltrametricDist.norm_tsum_eq_of_forall_lt` — a unique dominant term carries the norm of the
  sum.
* `IsUltrametricDist.tsum_prod_eq_tsum_tsum`, `IsUltrametricDist.tsum_tsum_comm` — iterated sums of
  a null family on a product.
* `IsUltrametricDist.tsum_prod_map₂` — the sum of `b (f i) (g j)` for a bounded biadditive `b`.
-/

open Filter Topology NNReal

variable {ι κ E F G : Type*}

/-! ### Null families attain their largest norm -/

section Seminormed

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]

/-- Source: roadmap §0.1.1. -/
theorem Filter.Tendsto.bddAbove_range_norm {f : ι → E} (hf : Tendsto f cofinite (𝓝 0)) :
    BddAbove (Set.range fun i ↦ ‖f i‖) := by
  have h := hf.norm
  rw [norm_zero] at h
  exact h.bddAbove_range_of_cofinite

/-- A null family has only finitely many terms of norm at least `δ > 0`. -/
private theorem finite_setOf_le_norm {f : ι → E} (hf : Tendsto f cofinite (𝓝 0)) {δ : ℝ}
    (hδ : 0 < δ) : {i | δ ≤ ‖f i‖}.Finite := by
  have h := hf.norm.eventually (gt_mem_nhds (show ‖(0 : E)‖ < δ by simpa using hδ))
  rw [Filter.eventually_cofinite] at h
  exact h.subset fun i hi ↦ by simpa using hi

/-- Source: roadmap §0.1.2 ("the supremum is attained"). -/
theorem Filter.Tendsto.exists_forall_norm_le [Nonempty ι] {f : ι → E}
    (hf : Tendsto f cofinite (𝓝 0)) : ∃ i₀, ∀ i, ‖f i‖ ≤ ‖f i₀‖ := by
  obtain ⟨i₁⟩ := ‹Nonempty ι›
  by_cases h0 : ∀ i, ‖f i‖ ≤ ‖f i₁‖
  · exact ⟨i₁, h0⟩
  obtain ⟨i₂, hi₂⟩ := not_forall.1 h0
  rw [not_le] at hi₂
  have hfin := finite_setOf_le_norm hf ((norm_nonneg _).trans_lt hi₂)
  obtain ⟨i₀, hi₀, hmax⟩ := hfin.toFinset.exists_max_image (fun i ↦ ‖f i‖) ⟨i₂, by simp⟩
  refine ⟨i₀, fun i ↦ ?_⟩
  by_cases hi : ‖f i₂‖ ≤ ‖f i‖
  · exact hmax i (by simpa using hi)
  · exact (not_le.1 hi).le.trans (by simpa using hi₀)

/-- Source: roadmap §0.1.2 ("the supremum is attained"). -/
theorem Filter.Tendsto.exists_norm_eq_iSup [Nonempty ι] {f : ι → E}
    (hf : Tendsto f cofinite (𝓝 0)) : ∃ i₀, ‖f i₀‖ = ⨆ i, ‖f i‖ := by
  obtain ⟨i₀, h⟩ := hf.exists_forall_norm_le
  exact ⟨i₀, le_antisymm (le_ciSup hf.bddAbove_range_norm i₀) (ciSup_le h)⟩

/-! ### Null families on a product -/

/-- Source: roadmap §0.1.4–§0.1.5. -/
theorem Filter.Tendsto.iSup_norm_cofinite_left {f : ι × κ → E}
    (hf : Tendsto f cofinite (𝓝 0)) : Tendsto (fun i ↦ ⨆ j, ‖f (i, j)‖) cofinite (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  refine ((finite_setOf_le_norm hf (half_pos hε)).image Prod.fst).subset fun i hi ↦ ?_
  by_contra hmem
  apply hi
  have hle : ⨆ j, ‖f (i, j)‖ ≤ ε / 2 := by
    rcases isEmpty_or_nonempty κ with hκ | hκ
    · rw [Real.iSup_of_isEmpty]
      exact (half_pos hε).le
    · refine ciSup_le fun j ↦ ?_
      by_contra h
      exact hmem ⟨(i, j), (not_le.1 h).le, rfl⟩
  rw [Real.dist_0_eq_abs, abs_of_nonneg (Real.iSup_nonneg fun _ ↦ norm_nonneg _)]
  linarith

/-- Source: roadmap §0.1.4–§0.1.5. -/
theorem Filter.Tendsto.iSup_norm_cofinite_right {f : ι × κ → E}
    (hf : Tendsto f cofinite (𝓝 0)) : Tendsto (fun j ↦ ⨆ i, ‖f (i, j)‖) cofinite (𝓝 0) := by
  exact (hf.comp Prod.swap_injective.tendsto_cofinite).iSup_norm_cofinite_left

/-- Source: roadmap §0.1.5 ("a null family of null families"). -/
theorem tendsto_cofinite_prod_of_tendsto_iSup_norm {f : ι × κ → E}
    (h₁ : ∀ i, Tendsto (fun j ↦ f (i, j)) cofinite (𝓝 0))
    (h₂ : Tendsto (fun i ↦ ⨆ j, ‖f (i, j)‖) cofinite (𝓝 0)) : Tendsto f cofinite (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  have hI : {i | ε ≤ ⨆ j, ‖f (i, j)‖}.Finite := by
    have h := Metric.tendsto_nhds.1 h₂ ε hε
    rw [Filter.eventually_cofinite] at h
    refine h.subset fun i hi ↦ ?_
    have h0 := Real.iSup_nonneg fun j ↦ norm_nonneg (f (i, j))
    simpa [Real.dist_0_eq_abs, abs_of_nonneg h0] using hi
  refine (hI.biUnion fun i _ ↦ (finite_setOf_le_norm (h₁ i) hε).image fun j ↦ (i, j)).subset
    fun p hp ↦ ?_
  have hp' : ε ≤ ‖f p‖ := by simpa using hp
  exact Set.mem_biUnion (x := p.1) (hp'.trans (le_ciSup (h₁ p.1).bddAbove_range_norm p.2))
    ⟨p.2, hp', rfl⟩

/-- Source: roadmap §0.1.4 (the null-family half of the biadditive clause). -/
theorem tendsto_cofinite_prod_of_norm_le_mul {f : ι → E} {g : κ → F} {b : E → F → G}
    (hb : ∀ x y, ‖b x y‖ ≤ ‖x‖ * ‖y‖) (hf : Tendsto f cofinite (𝓝 0))
    (hg : Tendsto g cofinite (𝓝 0)) :
    Tendsto (fun p : ι × κ ↦ b (f p.1) (g p.2)) cofinite (𝓝 0) := by
  refine squeeze_zero_norm (fun p ↦ hb _ _) ?_
  obtain ⟨Cf, hCf⟩ := hf.bddAbove_range_norm
  obtain ⟨Cg, hCg⟩ := hg.bddAbove_range_norm
  have hA : 0 < max Cf 0 + 1 := by linarith [le_max_right Cf 0]
  have hB : 0 < max Cg 0 + 1 := by linarith [le_max_right Cg 0]
  have hfA : ∀ i, ‖f i‖ ≤ max Cf 0 + 1 := fun i ↦ by linarith [hCf ⟨i, rfl⟩, le_max_left Cf 0]
  have hgB : ∀ j, ‖g j‖ ≤ max Cg 0 + 1 := fun j ↦ by linarith [hCg ⟨j, rfl⟩, le_max_left Cg 0]
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  refine ((finite_setOf_le_norm hf (div_pos hε hB)).prod
    (finite_setOf_le_norm hg (div_pos hε hA))).subset fun p hp ↦ ?_
  have hp' : ε ≤ ‖f p.1‖ * ‖g p.2‖ := by
    simpa [Real.dist_0_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg (f p.1))
      (norm_nonneg (g p.2)))] using hp
  refine ⟨?_, ?_⟩
  · change ε / (max Cg 0 + 1) ≤ ‖f p.1‖
    by_contra! h
    have : ‖f p.1‖ * ‖g p.2‖ < ε := calc
      ‖f p.1‖ * ‖g p.2‖ ≤ ‖f p.1‖ * (max Cg 0 + 1) :=
        mul_le_mul_of_nonneg_left (hgB _) (norm_nonneg _)
      _ < ε / (max Cg 0 + 1) * (max Cg 0 + 1) := mul_lt_mul_of_pos_right h hB
      _ = ε := div_mul_cancel₀ ε hB.ne'
    linarith
  · change ε / (max Cf 0 + 1) ≤ ‖g p.2‖
    by_contra! h
    have : ‖f p.1‖ * ‖g p.2‖ < ε := calc
      ‖f p.1‖ * ‖g p.2‖ ≤ (max Cf 0 + 1) * ‖g p.2‖ :=
        mul_le_mul_of_nonneg_right (hfA _) (norm_nonneg _)
      _ < (max Cf 0 + 1) * (ε / (max Cf 0 + 1)) := mul_lt_mul_of_pos_left h hA
      _ = ε := mul_div_cancel₀ ε hA.ne'
    linarith

end Seminormed

namespace IsUltrametricDist

/-! ### The strict bound and the unique dominant term -/

section Seminormed

variable [SeminormedAddCommGroup E] [IsUltrametricDist E]

/-- Source: roadmap §0.1.3. -/
theorem norm_tsum_lt_of_forall_lt {f : ι → E} {B : ℝ} (hB : 0 < B) (hlt : ∀ i, ‖f i‖ < B) :
    ‖∑' i, f i‖ < B := by
  by_cases hs : Summable f
  · rcases isEmpty_or_nonempty ι with hι | hι
    · simpa using hB
    obtain ⟨i₀, h⟩ := hs.tendsto_cofinite_zero.exists_forall_norm_le
    exact (norm_tsum_le f).trans_lt ((ciSup_le h).trans_lt (hlt i₀))
  · rw [tsum_eq_zero_of_not_summable hs, norm_zero]
    exact hB

/-- Source: roadmap §0.1.3 (`nnnorm` form). -/
theorem nnnorm_tsum_lt_of_forall_lt {f : ι → E} {B : ℝ≥0} (hB : 0 < B)
    (hlt : ∀ i, ‖f i‖₊ < B) : ‖∑' i, f i‖₊ < B := by
  have := norm_tsum_lt_of_forall_lt (f := f) (B := B) (by exact_mod_cast hB)
    fun i ↦ by exact_mod_cast hlt i
  exact_mod_cast this

/-- Source: roadmap §0.1.4–§0.1.5. -/
theorem tendsto_tsum_cofinite_left {f : ι × κ → E} (hf : Tendsto f cofinite (𝓝 0)) :
    Tendsto (fun i ↦ ∑' j, f (i, j)) cofinite (𝓝 0) := by
  exact squeeze_zero_norm (fun i ↦ norm_tsum_le fun j ↦ f (i, j)) hf.iSup_norm_cofinite_left

/-- Source: roadmap §0.1.4–§0.1.5. -/
theorem tendsto_tsum_cofinite_right {f : ι × κ → E} (hf : Tendsto f cofinite (𝓝 0)) :
    Tendsto (fun j ↦ ∑' i, f (i, j)) cofinite (𝓝 0) := by
  exact squeeze_zero_norm (fun j ↦ norm_tsum_le fun i ↦ f (i, j)) hf.iSup_norm_cofinite_right

end Seminormed

section Normed

variable [NormedAddCommGroup E] [IsUltrametricDist E]

/-- Source: roadmap §0.1.3; Schneider, *Nonarchimedean Functional Analysis*, §1 (the strict
triangle inequality). -/
theorem norm_tsum_eq_of_forall_lt {f : ι → E} (hf : Summable f) {i₀ : ι}
    (hlt : ∀ i, i ≠ i₀ → ‖f i‖ < ‖f i₀‖) : ‖∑' i, f i‖ = ‖f i₀‖ := by
  classical
  rw [hf.tsum_eq_add_tsum_ite i₀]
  rcases (norm_nonneg (f i₀)).eq_or_lt with h0 | h0
  · have hzero : ∀ i, (if i = i₀ then 0 else f i) = 0 := fun i ↦ by
      split_ifs with h
      · rfl
      · have := hlt i h
        rw [← h0] at this
        exact absurd this (not_lt.2 (norm_nonneg _))
    simp only [hzero, tsum_zero, add_zero]
  · have hlt' : ‖∑' i, (if i = i₀ then 0 else f i)‖ < ‖f i₀‖ :=
      norm_tsum_lt_of_forall_lt h0 fun i ↦ by
        split_ifs with h
        · simpa using h0
        · exact hlt i h
    rw [norm_add_eq_max_of_norm_ne_norm hlt'.ne', max_eq_left hlt'.le]

/-- Source: roadmap §0.1.3 (`nnnorm` form). -/
theorem nnnorm_tsum_eq_of_forall_lt {f : ι → E} (hf : Summable f) {i₀ : ι}
    (hlt : ∀ i, i ≠ i₀ → ‖f i‖₊ < ‖f i₀‖₊) : ‖∑' i, f i‖₊ = ‖f i₀‖₊ := by
  exact NNReal.eq (norm_tsum_eq_of_forall_lt hf fun i hi ↦ by exact_mod_cast hlt i hi)

/-- Source: roadmap §0.1.5. -/
theorem norm_tsum_sub_tsum_le {f g : ι → E} (hf : Summable f) (hg : Summable g) :
    ‖∑' i, f i - ∑' i, g i‖ ≤ ⨆ i, ‖f i - g i‖ := by
  rw [← hf.tsum_sub hg]
  exact norm_tsum_le _

/-! ### Iterated sums -/

/-- Source: roadmap §0.1.4. -/
theorem tsum_prod_eq_tsum_tsum [CompleteSpace E] {f : ι × κ → E}
    (hf : Tendsto f cofinite (𝓝 0)) : ∑' p, f p = ∑' i, ∑' j, f (i, j) := by
  have hs : Summable f := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hf
  exact hs.tsum_prod' fun i ↦ hs.prod_factor i

/-- Source: roadmap §0.1.4. -/
theorem tsum_tsum_comm [CompleteSpace E] {f : ι × κ → E} (hf : Tendsto f cofinite (𝓝 0)) :
    ∑' i, ∑' j, f (i, j) = ∑' j, ∑' i, f (i, j) := by
  have hs : Summable f := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hf
  exact (Summable.tsum_comm' (f := fun i j ↦ f (i, j)) hs (fun i ↦ hs.prod_factor i)
    fun j ↦ (hs.comp_injective Prod.swap_injective).prod_factor j).symm

/-! ### Bounded biadditive maps -/

variable [NormedAddCommGroup F] [NormedAddCommGroup G] [IsUltrametricDist G] [CompleteSpace G]

/-- Source: roadmap §0.1.4. -/
theorem summable_prod_map₂ {H : Type*} [NormedAddCommGroup H] {f : ι → H} {g : κ → F}
    {b : H → F → G} (hb : ∀ x y, ‖b x y‖ ≤ ‖x‖ * ‖y‖) (hf : Summable f) (hg : Summable g) :
    Summable fun p : ι × κ ↦ b (f p.1) (g p.2) := by
  exact NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (tendsto_cofinite_prod_of_norm_le_mul hb hf.tendsto_cofinite_zero hg.tendsto_cofinite_zero)

/-- Source: roadmap §0.1.4; the ring case is Mathlib's `tsum_mul_tsum_of_nonarchimedean`. -/
theorem tsum_prod_map₂ {H : Type*} [NormedAddCommGroup H] {f : ι → H} {g : κ → F}
    (b : H →+ F →+ G) (hb : ∀ x y, ‖b x y‖ ≤ ‖x‖ * ‖y‖) (hf : Summable f) (hg : Summable g) :
    ∑' p : ι × κ, b (f p.1) (g p.2) = b (∑' i, f i) (∑' j, g j) := by
  have hnull : Tendsto (fun p : ι × κ ↦ b (f p.1) (g p.2)) cofinite (𝓝 0) :=
    tendsto_cofinite_prod_of_norm_le_mul hb hf.tendsto_cofinite_zero hg.tendsto_cofinite_zero
  have hinner : ∀ i, ∑' j, b (f i) (g j) = b (f i) (∑' j, g j) := fun i ↦
    (hg.hasSum.map (b (f i)) (AddMonoidHomClass.continuous_of_bound (b (f i)) ‖f i‖
      (hb (f i)))).tsum_eq
  have hcont : Continuous (b.flip (∑' j, g j)) :=
    AddMonoidHomClass.continuous_of_bound _ ‖∑' j, g j‖ fun x ↦ by
      rw [AddMonoidHom.flip_apply, mul_comm]
      exact hb x _
  refine (tsum_prod_eq_tsum_tsum hnull).trans ((tsum_congr hinner).trans ?_)
  exact (hf.hasSum.map (b.flip (∑' j, g j)) hcont).tsum_eq

end Normed

end IsUltrametricDist
