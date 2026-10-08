/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.TopologicallyNilpotent

/-!
# Power-bounded and topologically nilpotent elements of a normed ring

The norm criteria for power-boundedness and topological nilpotency: an element of norm at most `1`
is power-bounded and an element of norm less than `1` is topologically nilpotent, and both
converses hold when the norm is multiplicative and `0` is not isolated.

⚠ **Seam.** The definitions `TopologicalRing.IsBounded` and `PowerBounded.IsPowerBounded` are
reproduced verbatim from mathlib4#40013, because neither Mathlib nor this chain has them. In Tau
Ceti they are `TauCeti.Huber.IsBounded` and `TauCeti.Huber.IsPowerBounded` (adic-spaces roadmap,
Layer 0), shaped as the same pull request. At migration the first section of this file is deleted
in favour of that import, and only the norm criteria move.

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, §0.2.1–§0.2.2. Tau Ceti home:
`TauCeti/Analysis/Normed/Ring/Ultra/PowerBounded.lean`.

## Main results

* `TopologicalRing.isBounded_of_forall_norm_le` — a norm-bounded set is bounded.
* `PowerBounded.isPowerBounded_of_norm_le_one`, `PowerBounded.isPowerBounded_iff_norm_le_one`.
* `TopologicalRing.IsBounded.exists_norm_le_of_normedAlgebra` — in a normed algebra over a
  nontrivially normed field, bounded sets are norm-bounded.
* `PowerBounded.isPowerBounded_iff_exists_norm_pow_le` — over a nontrivially normed field,
  power-boundedness is boundedness of the norms of the powers.
* `PowerBounded.IsPowerBounded.map` — a bounded ring homomorphism preserves power-boundedness
  (BGR 6.1.1).
* `IsTopologicallyNilpotent.of_norm_lt_one`, `isTopologicallyNilpotent_iff_norm_lt_one`.
-/

open Filter Topology Pointwise

/-! ### Seam: the definitions of mathlib4#40013 -/

namespace TopologicalRing

variable {M : Type*} [MonoidWithZero M] [TopologicalSpace M]

/-- A subset `S` of a topological monoid with zero is *bounded* if every neighbourhood `U` of `0`
admits a neighbourhood `V` of `0` with `V * S ⊆ U`. Source: Wedhorn, *Adic Spaces*,
Definition 5.27; mathlib4#40013. -/
def IsBounded (S : Set M) : Prop := ∀ U ∈ 𝓝 (0 : M), ∃ V ∈ 𝓝 (0 : M), V * S ⊆ U

end TopologicalRing

namespace PowerBounded

variable {M : Type*} [MonoidWithZero M] [TopologicalSpace M]

/-- An element is *power-bounded* if the set of its powers is bounded. Source: Wedhorn,
*Adic Spaces*, Definition 5.27; mathlib4#40013. -/
def IsPowerBounded (a : M) : Prop :=
  TopologicalRing.IsBounded (Set.range (a ^ · : ℕ → M))

end PowerBounded

/-! ### Norm criteria -/

/-- For a multiplicative norm, `‖x ^ (n + 1)‖ = ‖x‖ ^ (n + 1)`; no `‖1‖ = 1` is needed. -/
private theorem norm_pow_succ_of_normMulClass {R : Type*} [SeminormedRing R] [NormMulClass R]
    (x : R) (n : ℕ) : ‖x ^ (n + 1)‖ = ‖x‖ ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, norm_mul, ih, ← pow_succ]

namespace TopologicalRing

variable {R : Type*} [SeminormedRing R]

/-- Source: roadmap §0.2.1; Wedhorn, Example 5.29(2). -/
theorem isBounded_of_forall_norm_le {S : Set R} {C : ℝ} (h : ∀ s ∈ S, ‖s‖ ≤ C) :
    IsBounded S := by
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
  have hC : 0 < max C 0 + 1 := by linarith [le_max_right C 0]
  refine ⟨Metric.ball 0 (ε / (max C 0 + 1)), Metric.ball_mem_nhds _ (div_pos hε hC), ?_⟩
  rintro _ ⟨v, hv, s, hs, rfl⟩
  apply hεU
  rw [mem_ball_zero_iff] at hv ⊢
  calc ‖v * s‖ ≤ ‖v‖ * ‖s‖ := norm_mul_le v s
    _ ≤ ‖v‖ * (max C 0 + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [h s hs, le_max_left C 0]) (norm_nonneg v)
    _ < ε / (max C 0 + 1) * (max C 0 + 1) := mul_lt_mul_of_pos_right hv hC
    _ = ε := div_mul_cancel₀ ε hC.ne'

end TopologicalRing

namespace TopologicalRing

variable {R : Type*} [NormedRing R] [NormMulClass R] [NeBot (𝓝[≠] (0 : R))]

/-- Source: roadmap §0.2.2; Wedhorn, Example 5.29(2). -/
theorem IsBounded.exists_norm_le {S : Set R} (hS : IsBounded S) : ∃ C, ∀ s ∈ S, ‖s‖ ≤ C := by
  obtain ⟨V, hV, hVS⟩ := hS _ (Metric.ball_mem_nhds (0 : R) one_pos)
  obtain ⟨v, hv0, hvV⟩ := Filter.nonempty_of_mem (inter_mem_nhdsWithin {(0 : R)}ᶜ hV)
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
  refine ⟨‖v‖⁻¹, fun s hs ↦ ?_⟩
  have h1 : ‖v * s‖ < 1 := mem_ball_zero_iff.1 (hVS (Set.mul_mem_mul hvV hs))
  rw [norm_mul] at h1
  rw [← mul_one ‖v‖⁻¹, le_inv_mul_iff₀ hvpos]
  exact h1.le

end TopologicalRing

namespace PowerBounded

section Seminormed

variable {R : Type*} [SeminormedRing R]

/-- Source: roadmap §0.2.1. -/
theorem isPowerBounded_of_norm_pow_le {a : R} {C : ℝ} (hC : ∀ n : ℕ, ‖a ^ n‖ ≤ C) :
    IsPowerBounded a := by
  exact TopologicalRing.isBounded_of_forall_norm_le (C := C) (by rintro _ ⟨n, rfl⟩; exact hC n)

/-- Source: roadmap §0.2.1 ("every element of `R⁰` is power-bounded"); Wedhorn,
Example 5.29(2). -/
theorem isPowerBounded_of_norm_le_one {a : R} (ha : ‖a‖ ≤ 1) : IsPowerBounded a := by
  refine isPowerBounded_of_norm_pow_le (C := max ‖(1 : R)‖ 1) fun n ↦ ?_
  rcases n with _ | n
  · rw [pow_zero]
    exact le_max_left _ _
  · exact (norm_pow_le' a n.succ_pos).trans
      ((pow_le_one₀ (norm_nonneg a) ha).trans (le_max_right _ _))

end Seminormed

section NormMul

variable {R : Type*} [NormedRing R] [NormMulClass R] [NeBot (𝓝[≠] (0 : R))]

/-- Source: roadmap §0.2.2; Wedhorn, Example 5.29(2). -/
theorem IsPowerBounded.norm_le_one {a : R} (ha : IsPowerBounded a) : ‖a‖ ≤ 1 := by
  obtain ⟨C, hC⟩ := TopologicalRing.IsBounded.exists_norm_le ha
  by_contra h
  rw [not_le] at h
  obtain ⟨n, hn, hn1⟩ :=
    ((tendsto_pow_atTop_atTop_of_one_lt h).eventually_gt_atTop C).and (eventually_ge_atTop 1)
      |>.exists
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn1
  have := hC _ ⟨m + 1, rfl⟩
  rw [norm_pow_succ_of_normMulClass] at this
  linarith

/-- Source: roadmap §0.2.2; Wedhorn, Example 5.29(2) (`A° = {x | |x| ≤ 1}`). -/
theorem isPowerBounded_iff_norm_le_one {a : R} : IsPowerBounded a ↔ ‖a‖ ≤ 1 := by
  exact ⟨IsPowerBounded.norm_le_one, isPowerBounded_of_norm_le_one⟩

end NormMul

section NormedAlgebra

variable (K : Type*) [NontriviallyNormedField K] {R : Type*} [NormedRing R] [NormedAlgebra K R]

include K in
/-- In a normed algebra over a nontrivially normed field, a bounded set is bounded in norm: a
scalar of small norm multiplies it into the unit ball. Source: BGR 1.2.5/1 (power-boundedness as
boundedness of `{|aⁿ|}`), Wedhorn, Example 5.29(2). -/
theorem _root_.TopologicalRing.IsBounded.exists_norm_le_of_normedAlgebra {S : Set R}
    (hS : TopologicalRing.IsBounded S) : ∃ C, ∀ s ∈ S, ‖s‖ ≤ C := by
  obtain ⟨V, hV, hVS⟩ := hS _ (Metric.ball_mem_nhds (0 : R) one_pos)
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV
  have h1 : 0 < ‖(1 : R)‖ + 1 := by positivity
  obtain ⟨c, hc0, hcε⟩ := NormedField.exists_norm_lt K (div_pos hε h1)
  refine ⟨‖c‖⁻¹, fun s hs ↦ ?_⟩
  have hcV : algebraMap K R c ∈ V := by
    apply hεV
    rw [Metric.mem_ball, dist_zero_right, norm_algebraMap]
    calc ‖c‖ * ‖(1 : R)‖ ≤ ‖c‖ * (‖(1 : R)‖ + 1) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hc0.le
      _ < ε / (‖(1 : R)‖ + 1) * (‖(1 : R)‖ + 1) := mul_lt_mul_of_pos_right hcε h1
      _ = ε := div_mul_cancel₀ _ h1.ne'
  have h := hVS (Set.mul_mem_mul hcV hs)
  rw [Metric.mem_ball, dist_zero_right, ← Algebra.smul_def, norm_smul] at h
  rw [← one_div, le_div_iff₀ hc0, mul_comm]
  exact h.le

include K in
/-- A power-bounded element of a normed algebra over a nontrivially normed field has bounded
powers in norm. Source: BGR 1.2.5/1. -/
theorem IsPowerBounded.exists_norm_pow_le {a : R} (ha : IsPowerBounded a) :
    ∃ C, ∀ n : ℕ, ‖a ^ n‖ ≤ C := by
  obtain ⟨C, hC⟩ := TopologicalRing.IsBounded.exists_norm_le_of_normedAlgebra K ha
  exact ⟨C, fun n ↦ hC _ (Set.mem_range_self n)⟩

include K in
/-- Power-boundedness in a normed algebra over a nontrivially normed field is boundedness of the
norms of the powers. -/
theorem isPowerBounded_iff_exists_norm_pow_le {a : R} :
    IsPowerBounded a ↔ ∃ C, ∀ n : ℕ, ‖a ^ n‖ ≤ C :=
  ⟨IsPowerBounded.exists_norm_pow_le K, fun ⟨_, hC⟩ ↦ isPowerBounded_of_norm_pow_le hC⟩

include K in
/-- A bounded ring homomorphism maps power-bounded elements to power-bounded elements.
Source: BGR 6.1.1 ("Morphisms of `𝔄` map power-bounded elements into power-bounded elements"). -/
theorem IsPowerBounded.map {S : Type*} [SeminormedRing S] {φ : R →+* S}
    {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) {a : R} (ha : IsPowerBounded a) :
    IsPowerBounded (φ a) := by
  obtain ⟨M, hM⟩ := ha.exists_norm_pow_le K
  refine isPowerBounded_of_norm_pow_le (C := max 0 C * M) fun n ↦ ?_
  rw [← map_pow]
  calc ‖φ (a ^ n)‖ ≤ C * ‖a ^ n‖ := hφ _
    _ ≤ max 0 C * ‖a ^ n‖ := mul_le_mul_of_nonneg_right (le_max_right 0 C) (norm_nonneg _)
    _ ≤ max 0 C * M := mul_le_mul_of_nonneg_left (hM n) (le_max_left 0 C)

end NormedAlgebra

end PowerBounded

namespace IsTopologicallyNilpotent

/-- Source: roadmap §0.2.1 ("every element of `R⁰⁰` is topologically nilpotent"). -/
theorem of_norm_lt_one {R : Type*} [SeminormedRing R] {x : R} (hx : ‖x‖ < 1) :
    IsTopologicallyNilpotent x := by
  exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx

/-- Source: roadmap §0.2.2; Wedhorn, Example 5.29(2). -/
theorem norm_lt_one {R : Type*} [NormedRing R] [NormMulClass R] {x : R}
    (hx : IsTopologicallyNilpotent x) : ‖x‖ < 1 := by
  by_contra h
  rw [not_lt] at h
  have h1 := Filter.Tendsto.norm hx
  rw [norm_zero] at h1
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 (h1.eventually (gt_mem_nhds one_pos))
  have h2 := hn (n + 1) (by omega)
  rw [norm_pow_succ_of_normMulClass] at h2
  linarith [one_le_pow₀ (n := n + 1) h]

end IsTopologicallyNilpotent

/-- Source: roadmap §0.2.2; Wedhorn, Example 5.29(2) (`A°° = {x | |x| < 1}`). -/
theorem isTopologicallyNilpotent_iff_norm_lt_one {R : Type*} [NormedRing R] [NormMulClass R]
    {x : R} : IsTopologicallyNilpotent x ↔ ‖x‖ < 1 := by
  exact ⟨IsTopologicallyNilpotent.norm_lt_one, IsTopologicallyNilpotent.of_norm_lt_one⟩
