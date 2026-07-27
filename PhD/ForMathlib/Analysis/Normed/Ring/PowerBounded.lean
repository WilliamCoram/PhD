/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.RingTheory.Ideal.Quotient.Basic
import PhD.ForMathlib.Analysis.Normed.Ring.TopologicallyNilpotent
import PhD.ForMathlib.Analysis.Normed.Ring.Ultra
import PhD.ForMathlib.Topology.Algebra.Nonarchimedean.LinearTopology

/-! # Power-bounded elements of normed rings

This file characterises power-boundedness in terms of the norm.

Let `R` be a seminormed ring.

* `PowerBounded.isPowerBounded_of_norm_le`: an element whose powers have uniformly bounded norm is
  power-bounded.

* `PowerBounded.isPowerBounded_of_norm_le_one`: with `NormOneClass R`, an element of norm `≤ 1` is
  power-bounded.

* `PowerBounded.isPowerBounded_of_norm_lt_one`: an element of norm `< 1` is power-bounded.

Let `R` be a normed ring with multiplicative norm, `‖1‖ = 1`, whose origin is not isolated.

* `PowerBounded.IsPowerBounded.norm_le_one_of_neBot`: a power-bounded element has norm `≤ 1`.

* `PowerBounded.isPowerBounded_iff_norm_le_one`: an element is power-bounded if and only if its
  norm is `≤ 1`.

Let `R` be a seminormed commutative ring whose topology is `S`-linear for some ring `S`.

* `PowerBounded.isOpen_subring` / `PowerBounded.isClosed_subring`: the subring `R°` of
  power-bounded elements is open and closed.

Let `R` moreover be a complete normed commutative ring whose distance is ultrametric.

* `PowerBounded.isUnit_iff_isUnit_mk_topologicalNilradical`: an element of `R°` is a unit if and
  only if its image in the quotient by the topological nilradical is a unit.

## Implementation notes

The hypothesis `NeBot (𝓝[≠] (0 : R))` in the norm-`≤ 1` characterisation rules out the discrete
topology: on `R = ℤ` every subset is bounded, so every element is power-bounded, yet `‖2‖ = 2`.
Multiplicativity of the norm cannot be weakened to submultiplicativity: for the `ℓ¹` norm on
`ℝ[X]/(X² - X)` the element `a = 1 - 2X` satisfies `a ^ 2 = 1` (so `a` is power-bounded) but
`‖a‖ = 3`.
-/

open Filter Topology

namespace PowerBounded

section SeminormedRing

variable {R : Type*} [SeminormedRing R]

/-- An element whose powers have uniformly bounded norm is power-bounded. -/
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

/-- An element of norm `≤ 1` is power-bounded. -/
theorem isPowerBounded_of_norm_le_one [NormOneClass R] {a : R} (ha : ‖a‖ ≤ 1) :
    IsPowerBounded a :=
  isPowerBounded_of_norm_le fun n ↦ (norm_pow_le a n).trans (pow_le_one₀ (norm_nonneg _) ha)

/-- An element of norm `< 1` is power-bounded. -/
theorem isPowerBounded_of_norm_lt_one {a : R} (ha : ‖a‖ < 1) : IsPowerBounded a :=
  (IsTopologicallyNilpotent.of_norm_lt_one ha).isPowerBounded

end SeminormedRing

section NormedRing

variable {R : Type*} [NormedRing R] [NormMulClass R] [NormOneClass R] [NeBot (𝓝[≠] (0 : R))]

/-- In a normed ring with multiplicative norm whose origin is not isolated, every power-bounded
element has norm `≤ 1`. -/
theorem IsPowerBounded.norm_le_one_of_neBot {a : R} (ha : IsPowerBounded a) : ‖a‖ ≤ 1 := by
  by_contra H
  obtain ⟨V, hV, hVU⟩ := ha (Metric.ball 0 1) (Metric.ball_mem_nhds 0 one_pos)
  obtain ⟨v, hv, hv0⟩ : (V ∩ {0}ᶜ).Nonempty :=
    Filter.nonempty_of_mem (Filter.inter_mem (mem_nhdsWithin_of_mem_nhds hV) self_mem_nhdsWithin)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖v‖⁻¹ < ‖a‖ ^ N := pow_unbounded_of_one_lt _ (not_le.mp H)
  have h1 : ‖v‖ * ‖a‖ ^ N < 1 := by
    rw [← norm_pow, ← norm_mul, ← dist_zero_right, ← Metric.mem_ball]
    exact hVU (Set.mul_mem_mul hv ⟨N, rfl⟩)
  have h2 : 1 < ‖v‖ * ‖a‖ ^ N := by
    rw [← mul_inv_cancel₀ (a := ‖v‖) (norm_ne_zero_iff.mpr hv0)]
    exact mul_lt_mul_of_pos_left hN (norm_pos_iff.mpr hv0)
  exact h1.asymm h2

/-- The norms of the powers of a power-bounded element are uniformly bounded. -/
theorem IsPowerBounded.exists_norm_pow_le {a : R} (ha : IsPowerBounded a) :
    ∃ C, ∀ n, ‖a ^ n‖ ≤ C :=
  ⟨1, fun n ↦ (norm_pow_le a n).trans (pow_le_one₀ (norm_nonneg _) ha.norm_le_one_of_neBot)⟩

/-- An element is power-bounded if and only if the norms of its powers are uniformly bounded. -/
theorem isPowerBounded_iff_exists_norm_pow_le {a : R} :
    IsPowerBounded a ↔ ∃ C, ∀ n, ‖a ^ n‖ ≤ C :=
  ⟨IsPowerBounded.exists_norm_pow_le, fun h ↦ isPowerBounded_of_norm_le h.choose_spec⟩

/-- An element is power-bounded if and only if its norm is `≤ 1`. -/
theorem isPowerBounded_iff_norm_le_one {a : R} : IsPowerBounded a ↔ ‖a‖ ≤ 1 :=
  ⟨IsPowerBounded.norm_le_one_of_neBot, isPowerBounded_of_norm_le_one⟩

end NormedRing

section SeminormedCommRing

variable {R : Type*} [SeminormedCommRing R]

/-- In a seminormed commutative ring with `S`-linear topology, the subring of power-bounded
elements is open. -/
theorem isOpen_subring (S : Type*) [Ring S] [Module S R] [IsLinearTopology S R] :
    IsOpen (subring R (S := S) : Set R) := by
  rw [isOpen_iff_mem_nhds]
  intro a ha
  filter_upwards [Metric.ball_mem_nhds a one_pos] with b hb
  rw [show b = a + (b - a) by ring]
  exact (subring R).add_mem ha (isPowerBounded_of_norm_lt_one (mem_ball_iff_norm.mp hb))

/-- In a seminormed commutative ring with `S`-linear topology, the subring of power-bounded
elements is closed. -/
theorem isClosed_subring (S : Type*) [Ring S] [Module S R] [IsLinearTopology S R] :
    IsClosed (subring R (S := S) : Set R) :=
  (subring R (S := S)).toAddSubgroup.isClosed_of_isOpen (isOpen_subring S)

end SeminormedCommRing

section Complete

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]

instance : CompleteSpace ↥(subring R (S := ℤ)) :=
  (isClosed_subring (R := R) ℤ).completeSpace_coe

/-- In a complete ultrametric normed commutative ring, an element of the power-bounded subring is
a unit if and only if its image in the quotient by the topological nilradical is a unit. -/
theorem isUnit_iff_isUnit_mk_topologicalNilradical (a : ↥(subring R (S := ℤ))) :
    IsUnit a ↔ IsUnit (Ideal.Quotient.mk (topologicalNilradical ℤ) a) := by
  refine ⟨fun h ↦ h.map _, fun h ↦ ?_⟩
  obtain ⟨b, hbr, -⟩ := isUnit_iff_exists.mp h
  obtain ⟨z, hz, hz_eq⟩ : ∃ z, IsTopologicallyNilpotent z ∧ a * Quotient.out b = 1 - z := by
    refine ⟨1 - a * Quotient.out b, ?_, by ring⟩
    have hmem : 1 - a * Quotient.out b ∈ topologicalNilradical (R := R) ℤ := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_mul, Ideal.Quotient.mk_out,
        hbr, sub_self]
    rw [IsTopologicallyNilpotent, tendsto_subtype_rng]
    simpa [IsTopologicallyNilpotent] using (mem_topologicalNilradical_iff ℤ _).mp hmem
  exact isUnit_of_mul_isUnit_left (y := Quotient.out b)
    (by simpa [hz_eq] using hz.isUnit_one_sub)

end Complete

section Units

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] [NormOneClass R]

/-- An element of the power-bounded subring of norm `1` is a unit there if and only if it is a
unit of the ambient ring: the inverse of a norm-one element has norm one, hence is
power-bounded. -/
theorem isUnit_iff_isUnit_coe {a : ↥(subring R (S := ℤ))} (ha : ‖(a : R)‖ = 1) :
    IsUnit a ↔ IsUnit (a : R) := by
  refine ⟨fun h ↦ h.map (subring R (S := ℤ)).subtype, fun h ↦ ?_⟩
  obtain ⟨u, hu⟩ := h
  have h1 : ‖(u : R)‖ * ‖((u⁻¹ : Rˣ) : R)‖ = 1 := by
    rw [← norm_mul, u.mul_inv, norm_one]
  refine isUnit_iff_exists.mpr ⟨⟨((u⁻¹ : Rˣ) : R), isPowerBounded_of_norm_le_one ?_⟩,
    Subtype.ext (by simp [hu]), Subtype.ext (by simp [hu])⟩
  rw [hu, ha, one_mul] at h1
  exact h1.le

/-- The quotient of the power-bounded subring by its topological nilradical is reduced: if a
power of `a` is topologically nilpotent then `‖a‖ ^ k < 1`, so `‖a‖ < 1` and `a` is itself
topologically nilpotent. -/
instance : IsReduced (↥(subring R (S := ℤ)) ⧸ topologicalNilradical (R := R) ℤ) where
  eq_zero x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rintro ⟨k, hk⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, mem_topologicalNilradical_iff,
      isTopologicallyNilpotent_iff_norm_lt_one, SubmonoidClass.coe_pow, norm_pow] at hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact absurd hk (by simp)
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_topologicalNilradical_iff,
      isTopologicallyNilpotent_iff_norm_lt_one]
    exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hk0.ne').mp hk

end Units

section IdealBalls

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] [NormOneClass R]
  [NeBot (𝓝[≠] (0 : R))] {ε : ℝ}

/-- The closed ball of radius `ε` around `0` as an ideal of the power-bounded subring:
power-bounded elements have norm at most `1`, so multiplication preserves the ball. -/
def closedBall_ideal (hε : 0 ≤ ε) : Ideal ↥(subring R (S := ℤ)) where
  carrier := Metric.closedBall 0 ε
  add_mem' {a b} ha hb := by
    rw [Metric.mem_closedBall, dist_zero_right] at ha hb ⊢
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := Metric.mem_closedBall_self hε
  smul_mem' c a ha := by
    rw [Metric.mem_closedBall, dist_zero_right] at ha ⊢
    show ‖(c : R) * (a : R)‖ ≤ ε
    rw [norm_mul]
    calc ‖(c : R)‖ * ‖(a : R)‖
        ≤ 1 * ε := mul_le_mul (IsPowerBounded.norm_le_one_of_neBot c.2) ha (norm_nonneg _)
          zero_le_one
      _ = ε := one_mul ε

@[simp]
lemma mem_closedBall_ideal (hε : 0 ≤ ε) {a : ↥(subring R (S := ℤ))} :
    a ∈ closedBall_ideal hε ↔ ‖(a : R)‖ ≤ ε := by
  show a ∈ Metric.closedBall 0 ε ↔ _
  rw [Metric.mem_closedBall, dist_zero_right]
  exact Iff.rfl

/-- The open ball of radius `ε` around `0` as an ideal of the power-bounded subring. -/
def ball_ideal (hε : 0 < ε) : Ideal ↥(subring R (S := ℤ)) where
  carrier := Metric.ball 0 ε
  add_mem' {a b} ha hb := by
    rw [Metric.mem_ball, dist_zero_right] at ha hb ⊢
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
  zero_mem' := Metric.mem_ball_self hε
  smul_mem' c a ha := by
    rw [Metric.mem_ball, dist_zero_right] at ha ⊢
    show ‖(c : R) * (a : R)‖ < ε
    rw [norm_mul]
    calc ‖(c : R)‖ * ‖(a : R)‖
        < 1 * ε := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos
          (IsPowerBounded.norm_le_one_of_neBot c.2) ha (norm_nonneg _) one_pos
      _ = ε := one_mul ε

@[simp]
lemma mem_ball_ideal (hε : 0 < ε) {a : ↥(subring R (S := ℤ))} :
    a ∈ ball_ideal hε ↔ ‖(a : R)‖ < ε := by
  show a ∈ Metric.ball 0 ε ↔ _
  rw [Metric.mem_ball, dist_zero_right]
  exact Iff.rfl

lemma coe_closedBall_ideal (hε : 0 ≤ ε) :
    (closedBall_ideal (R := R) hε : Set ↥(subring R (S := ℤ))) = Metric.closedBall 0 ε := rfl

lemma coe_ball_ideal (hε : 0 < ε) :
    (ball_ideal (R := R) hε : Set ↥(subring R (S := ℤ))) = Metric.ball 0 ε := rfl

lemma isOpen_closedBall_ideal (hε : 0 < ε) :
    IsOpen (closedBall_ideal (R := R) hε.le : Set ↥(subring R (S := ℤ))) :=
  IsUltrametricDist.isOpen_closedBall _ hε.ne'

lemma isOpen_ball_ideal (hε : 0 < ε) :
    IsOpen (ball_ideal (R := R) hε : Set ↥(subring R (S := ℤ))) :=
  Metric.isOpen_ball

/-- The topological nilradical of the power-bounded subring is the open unit ball. -/
theorem topologicalNilradical_eq_ball_ideal_one :
    topologicalNilradical (R := R) ℤ = ball_ideal one_pos := by
  ext a
  rw [mem_topologicalNilradical_iff, mem_ball_ideal, isTopologicallyNilpotent_iff_norm_lt_one]

/-- The topological nilradical of the power-bounded subring is open: it is the open unit
ball. -/
theorem isOpen_topologicalNilradical :
    IsOpen (topologicalNilradical (R := R) ℤ : Set ↥(subring R (S := ℤ))) := by
  rw [topologicalNilradical_eq_ball_ideal_one]
  exact isOpen_ball_ideal one_pos

end IdealBalls

end PowerBounded
