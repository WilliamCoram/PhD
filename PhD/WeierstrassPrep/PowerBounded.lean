import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import PhD.PR'd.PowerBounded
import PhD.WeierstrassPrep.TopologicallyNilpotent

import Mathlib.RingTheory.Localization.FractionRing

open TopologicalRing PowerBounded
open scoped Topology

namespace IsPowerBounded

section SeminormedRing

-- this maybe needs to be in a NormedRing.PowerBounded file?
-- the namespace should then be NormedRing?

variable {R : Type*} [SeminormedRing R]

theorem isPowerBounded_of_norm_le {a : R} {C : ℝ} (hC : ∀ n : ℕ, ‖a ^ n‖ ≤ C) :
    IsPowerBounded a := by
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  set C' := max C 0
  refine ⟨Metric.ball 0 (ε / (C' + 1)), Metric.ball_mem_nhds 0 (by positivity), ?_⟩
  rintro _ ⟨v, hv, _, ⟨n, rfl⟩, rfl⟩
  apply hεU
  rw [Metric.mem_ball, dist_zero_right] at hv ⊢
  calc
    _ ≤ ‖v‖ * ‖a ^ n‖ := norm_mul_le _ _
    _ ≤ ‖v‖ * (C' + 1) := mul_le_mul_of_nonneg_left (by grind) (norm_nonneg _)
    _ < (ε / (C' + 1)) * (C' + 1) := mul_lt_mul_of_pos_right hv (by grind)
    _ = ε := div_mul_cancel₀ ε (by grind)

/-- Every element of norm `≤ 1` is power-bounded. -/
lemma isPowerBounded_of_norm_le_one [NormOneClass R] {a : R} (ha : ‖a‖ ≤ 1) : IsPowerBounded a :=
  isPowerBounded_of_norm_le (fun n ↦ (norm_pow_le a n).trans (pow_le_one₀ (norm_nonneg _) ha))

/-- In a normed ring, every element of norm `< 1` is power-bounded. -/
lemma isPowerBounded_of_norm_lt_one {x : R} (hx : ‖x‖ < 1) : IsPowerBounded x :=
  IsTopologicallyNilpotent.isPowerBounded (IsTopologicallyNilpotent.of_norm_lt_one hx)

lemma ball_zero_one_subset_subring :
    Metric.ball (0 : R) 1 ⊆ {x | IsPowerBounded x} := fun x hx => by
  rw [Metric.mem_ball, dist_zero_right] at hx
  exact isPowerBounded_of_norm_lt_one hx

end SeminormedRing

section NormedRing

variable {R : Type*} [NormedRing R] [NormMulClass R] [NormOneClass R] [Filter.NeBot (𝓝[≠] (0 : R))]

/-- In a normed commutative ring with multiplicative norm whose origin is not isolated, every
power-bounded element has norm `≤ 1`.
The non-isolation hypothesis rules out the
discrete-topology case (e.g. `R = ℤ`, where the topology is discrete, so every set is
`IsBounded` and every element power-bounded — yet `‖2‖ = 2`). -/
lemma norm_le_one_of_neBot {a : R} (ha : IsPowerBounded a) : ‖a‖ ≤ 1 := by
  by_contra
  obtain ⟨V, hV, hVU⟩ := ha (Metric.ball 0 1) (Metric.ball_mem_nhds 0 one_pos)
  obtain ⟨v, hv, _⟩ : (V ∩ {0}ᶜ).Nonempty := Filter.nonempty_of_mem
    (Filter.inter_mem (mem_nhdsWithin_of_mem_nhds hV) self_mem_nhdsWithin)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖v‖⁻¹ < ‖a‖ ^ N := pow_unbounded_of_one_lt _ (not_le.mp this)
  have : ‖v‖ * ‖a‖ ^ N < 1 := by
    rw [← norm_pow, ← norm_mul, ← dist_zero_right, ← Metric.mem_ball]
    exact hVU (Set.mul_mem_mul hv ⟨N, rfl⟩)
  have : 1 < ‖v‖ * ‖a‖ ^ N := by
    rw [← mul_inv_cancel₀ (a := ‖v‖) (norm_ne_zero_iff.mpr (by grind))]
    exact mul_lt_mul_of_pos_left hN (norm_pos_iff.mpr (by grind))
  grind

-- this seems to be the minimal assumptions I can get

-- seminormedring does not work: take a nilpotent 2x2 matrix e.g. (0,2;0;0), this has operator norm
-- at least 2 (take v = (0;1))... but nilpotent implies powerbounded

-- the Filter.NeBot is consider in the docstring above
-- e.g. need {0} to not be a neighbourhood meaning everything is power bounded

-- just submultiplicative is not sufficient.
-- l¹ norm on ℝ[x]/(x^2 - x); a = 1 - 2x; a^2 = 1; ‖a‖ = 3, ‖a^2‖ = 1
-- but its power bounded as we have the powers are bounded (first lemma in this file)

-- for restricting to power multiplicative could look at Gelfan-Beurling spectral radius
-- but this would require completeness (e.g. Banach algebras)

-- however this needs NormOneClass; perhaps it can be removed but have not worked out how
lemma norm_pow_bounded {a : R} (ha : IsPowerBounded a) : ∃ C, ∀ n, ‖a ^ n‖ ≤ C := by
  suffices ha_le : ‖a‖ ≤ 1 by
    exact ⟨1, (fun n ↦ (norm_pow_le a n).trans (pow_le_one₀ (norm_nonneg _) ha_le))⟩
  exact norm_le_one_of_neBot ha

lemma isPowerBounded_iff {a : R} : IsPowerBounded a ↔ ∃ C, ∀ n, ‖a ^ n‖ ≤ C :=
  ⟨norm_pow_bounded, fun h ↦ isPowerBounded_of_norm_le h.choose_spec⟩

lemma isPowerBounded_iff' {a : R} : IsPowerBounded a ↔ ‖a‖ ≤ 1 :=
  ⟨norm_le_one_of_neBot, isPowerBounded_of_norm_le_one⟩

end NormedRing

section NormedCommRing

variable {R : Type*} [NormedCommRing R]

lemma subring_isOpen (S : Type*) [Ring S] [Module S R] [IsLinearTopology S R] :
    IsOpen (subring R (S := S) : Set R) := by
  rw [isOpen_iff_mem_nhds]
  intro a ha
  filter_upwards [Metric.ball_mem_nhds a one_pos] with b hb
  rw [(add_sub_cancel a b).symm]
  exact (subring R).add_mem ha (ball_zero_one_subset_subring
    (by simpa [Metric.mem_ball, dist_eq_norm] using hb))

lemma subring_isClosed (S : Type*) [Ring S] [Module S R] [IsLinearTopology S R] :
    IsClosed (subring R (S := S) : Set R) :=
  (subring R (S := S)).toAddSubgroup.isClosed_of_isOpen (subring_isOpen S)

end NormedCommRing
