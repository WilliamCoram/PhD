import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import PhD.PR'd.TopologicallyNilpotent

import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

open Filter Topology Pointwise Polynomial

namespace IsTopologicallyNilpotent

section SemiormedRing

variable {R : Type*} [SeminormedRing R]

/-- In a seminormed ring, an element of norm `< 1` is topologically nilpotent. -/
lemma of_norm_lt_one {x : R} (hx : ‖x‖ < 1) : IsTopologicallyNilpotent x := by
  rw [IsTopologicallyNilpotent, tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero' (Filter.Eventually.of_forall (by grind)) (eventually_norm_pow_le x)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg x) hx)

variable [NormMulClass R]

lemma norm_lt_one {x : R} (hx : IsTopologicallyNilpotent x) : ‖x‖ < 1 := by
  by_contra H
  -- If we assume NormOneClass R we can use norm_pow in the below avoiding the induction
  -- Since we do not, using n in the below would give ‖1‖ = 1 (which is not assumed)
  suffices ∀ n, 1 ≤ ‖x ^ (n + 1)‖ by
    have h : Filter.Tendsto (fun n : ℕ => ‖x ^ (n + 1)‖) Filter.atTop (𝓝 0) := by
      simpa [← tendsto_zero_iff_norm_tendsto_zero] using (tendsto_add_atTop_iff_nat 1).mpr hx
    grind [le_of_tendsto_of_tendsto' tendsto_const_nhds h this]
  exact fun n ↦ by induction n with
  | zero => grind
  | succ _ h => rw [pow_succ x _, norm_mul, ← mul_one 1]
                exact mul_le_mul h (not_lt.mp H) (zero_le_one' _) (norm_nonneg _)

lemma iff_norm_lt_one {x : R} : IsTopologicallyNilpotent x ↔ ‖x‖ < 1 :=
  ⟨norm_lt_one, of_norm_lt_one⟩

end SemiormedRing

section NormedRing

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] [CompleteSpace R]

lemma isUnit_one_sub_of_isTopologicallyNilpotent {y : R} (hy : IsTopologicallyNilpotent y) :
    IsUnit (1 - y) := by
  have := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (by rwa [Nat.cofinite_eq_atTop])
  exact ⟨⟨1 - y, ∑' n, y ^ n, this.one_sub_mul_tsum_pow, this.tsum_pow_mul_one_sub⟩, rfl⟩

end NormedRing

section NormedCommRing

variable {R : Type*} [NormedCommRing R]

lemma topNil_isOpen (S : Type*) [Ring S] [Module S R] [IsLinearTopology S R] :
    IsOpen {a : R | IsTopologicallyNilpotent a} := by
  rw [isOpen_iff_mem_nhds]
  intro a ha
  filter_upwards [Metric.ball_mem_nhds a one_pos] with b hb
  rw [(add_sub_cancel a b).symm]
  exact add' S ha (of_norm_lt_one (by simpa [Metric.mem_ball, dist_eq_norm] using hb))

lemma topNil_isClosed (S : Type*) [Ring S] [Module S R] [IsLinearTopology S R] :
    IsClosed {a : R | IsTopologicallyNilpotent a} :=
  let G : AddSubgroup R :=
    { carrier := {a : R | IsTopologicallyNilpotent a}
      add_mem' := fun ha hb ↦ add' S ha hb
      zero_mem' := zero
      neg_mem' := fun ha ↦ by
        rw [Set.mem_setOf_eq, ← neg_one_mul]
        exact mul_left_of_isPowerBounded
          (PowerBounded.isPowerBounded_neg PowerBounded.isPowerBounded_one) ha }
  G.isClosed_of_isOpen (topNil_isOpen S)

end NormedCommRing
