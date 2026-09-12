/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import PhD.Main.ForMathlib.Topology.Algebra.TopologicallyNilpotent

/-! # Topologically nilpotent elements of normed rings

This file characterises topological nilpotency in terms of the norm.

Let `R` be a seminormed ring.

* `IsTopologicallyNilpotent.of_norm_lt_one`: an element of norm `< 1` is topologically nilpotent.

If moreover the norm on `R` is multiplicative:

* `IsTopologicallyNilpotent.norm_lt_one`: a topologically nilpotent element has norm `< 1`.

* `isTopologicallyNilpotent_iff_norm_lt_one`: an element is topologically nilpotent if and only if
  its norm is `< 1`.

Let `R` be a complete normed ring whose distance is ultrametric.

* `IsTopologicallyNilpotent.isUnit_one_sub`: if `y` is topologically nilpotent then `1 - y` is a
  unit, with inverse the geometric series `∑' n, y ^ n`.

Let `R` be a seminormed commutative ring whose topology is `S`-linear for some ring `S`.

* `isOpen_setOf_isTopologicallyNilpotent`: the set of topologically nilpotent elements is open.

* `isClosed_setOf_isTopologicallyNilpotent`: the set of topologically nilpotent elements is closed.
-/

open Filter Topology

namespace IsTopologicallyNilpotent

section SeminormedRing

variable {R : Type*} [SeminormedRing R]

/-- In a seminormed ring, an element of norm `< 1` is topologically nilpotent. -/
theorem of_norm_lt_one {x : R} (hx : ‖x‖ < 1) : IsTopologicallyNilpotent x := by
  rw [IsTopologicallyNilpotent, tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _) (eventually_norm_pow_le x)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg x) hx)

variable [NormMulClass R]

/-- In a seminormed ring with multiplicative norm, a topologically nilpotent element has
norm `< 1`. -/
theorem norm_lt_one {x : R} (hx : IsTopologicallyNilpotent x) : ‖x‖ < 1 := by
  by_contra H
  have h1 : ∀ n, 1 ≤ ‖x ^ (n + 1)‖ := by
    intro n
    induction n with
    | zero => simpa using not_lt.mp H
    | succ n ih =>
      rw [pow_succ, norm_mul, ← mul_one 1]
      exact mul_le_mul ih (not_lt.mp H) zero_le_one (norm_nonneg _)
  have h : Tendsto (fun n : ℕ ↦ ‖x ^ (n + 1)‖) atTop (𝓝 0) := by
    simpa [← tendsto_zero_iff_norm_tendsto_zero] using (tendsto_add_atTop_iff_nat 1).mpr hx
  exact absurd (le_of_tendsto_of_tendsto' tendsto_const_nhds h h1) (by norm_num)

/-- In a seminormed ring with multiplicative norm, an element is topologically nilpotent if and
only if its norm is `< 1`. -/
theorem _root_.isTopologicallyNilpotent_iff_norm_lt_one {x : R} :
    IsTopologicallyNilpotent x ↔ ‖x‖ < 1 :=
  ⟨norm_lt_one, of_norm_lt_one⟩

end SeminormedRing

section NormedRing

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] [CompleteSpace R]

/-- In a complete ultrametric normed ring, `1 - y` is a unit whenever `y` is topologically
nilpotent, with inverse the geometric series `∑' n, y ^ n`. -/
theorem isUnit_one_sub {y : R} (hy : IsTopologicallyNilpotent y) : IsUnit (1 - y) := by
  have hs := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (f := (y ^ ·)) (by rwa [Nat.cofinite_eq_atTop])
  exact ⟨⟨1 - y, ∑' n, y ^ n, hs.one_sub_mul_tsum_pow, hs.tsum_pow_mul_one_sub⟩, rfl⟩

end NormedRing

section SeminormedCommRing

variable {R : Type*} [SeminormedCommRing R]

/-- In a seminormed commutative ring with `S`-linear topology, the set of topologically nilpotent
elements is open. -/
theorem _root_.isOpen_setOf_isTopologicallyNilpotent (S : Type*) [Ring S] [Module S R]
    [IsLinearTopology S R] : IsOpen {a : R | IsTopologicallyNilpotent a} := by
  rw [isOpen_iff_mem_nhds]
  intro a ha
  filter_upwards [Metric.ball_mem_nhds a one_pos] with b hb
  rw [show b = a + (b - a) by ring]
  exact add' S ha (of_norm_lt_one (mem_ball_iff_norm.mp hb))

/-- In a seminormed commutative ring with `S`-linear topology, the set of topologically nilpotent
elements is closed. -/
theorem _root_.isClosed_setOf_isTopologicallyNilpotent (S : Type*) [Ring S] [Module S R]
    [IsLinearTopology S R] : IsClosed {a : R | IsTopologicallyNilpotent a} :=
  let G : AddSubgroup R :=
    { carrier := {a : R | IsTopologicallyNilpotent a}
      add_mem' := fun ha hb ↦ add' S ha hb
      zero_mem' := zero
      neg_mem' := fun ha ↦ by
        rw [Set.mem_ofPred_eq, ← neg_one_mul]
        exact mul_left_of_isPowerBounded
          (PowerBounded.isPowerBounded_neg PowerBounded.isPowerBounded_one) ha }
  G.isClosed_of_isOpen (isOpen_setOf_isTopologicallyNilpotent S)

end SeminormedCommRing

end IsTopologicallyNilpotent
