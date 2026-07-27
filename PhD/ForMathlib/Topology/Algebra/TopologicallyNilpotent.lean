/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Topology.Algebra.TopologicallyNilpotent
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.RingTheory.Ideal.Basic
import PhD.ForMathlib.Topology.Algebra.PowerBounded

/-! # Topologically nilpotent elements (project additions)

The core `IsTopologicallyNilpotent` API (definition, `map`, `zero`, the `mul_*`/`add_*` lemmas for
linear topologies, and `topologicalNilradical`) now lives upstream in
`Mathlib.Topology.Algebra.TopologicallyNilpotent`. This file keeps only the additions that have
not (yet) been upstreamed.

Let `R` be a semiring, endowed with a topology, that has continuous multiplication.

* `IsTopologicallyNilpotent.of_pow`: if `a ^ m` is topologically nilpotent, then so is `a`.

Let `R` be a semiring, endowed with a topology.

* `IsTopologicallyNilpotent.isPowerBounded`: topologically nilpotent elements are power bounded.

Let `R` be a commutative ring, endowed with a topology.

* `IsTopologicallyNilpotent.mul_left_of_isPowerBounded` : if `a : R` is topologically nilpotent and
  `b : R` is power bounded then `b * a` is topologically nilpotent.

* `IsTopologicallyNilpotent.mul_right_of_isPowerBounded` : if `a : R` is topologically nilpotent and
  `b : R` is power bounded then `a * b` is topologically nilpotent.

Note the above mul lemmas do not rely on any linear topology, but restrict the element we are
multiplying by to be power bounded.

Let `S` be a ring such that `R` is an `S`-module and `R` has the `S`-linear topology and `R` now
has continuous multiplication.

The key examples will be:
    · `S = R`: i.e., we have `[IsLinearTopology R R]`
    · `S = ℤ`: which can be infered from `[Ring R] [TopologicalSpace R] [NonarchimedeanRing R]`

* `IsTopologicallyNilpotent.add'`: if `a b` are topologically nilpotent then so is `a + b`.

Note the requirement of continuous multiplication, means that this does not imply the upstream `.add`.

-/

open Filter

open scoped Topology

namespace IsTopologicallyNilpotent

section Ring

variable {R : Type*} [TopologicalSpace R] [Ring R]

/-- If `a` and `b` commute and `b` is topologically nilpotent,
  then `a * b` is topologically nilpotent. -/
theorem smul_of_commute (S : Type*) [Ring S] [Module S R] [IsLinearTopology S R]
    [IsScalarTower S R R] {a : S} {b : R} (hb : IsTopologicallyNilpotent b)
    (hab : ∀ n, (a • b) ^ n = a ^ n • b ^ n) : IsTopologicallyNilpotent (a • b) := by
  simp_rw [IsTopologicallyNilpotent, hab]
  exact IsLinearTopology.tendsto_smul_zero (R := S) _ _ hb

end Ring

section ContinuousMul

open TopologicalRing

variable {R : Type*} [Semiring R] [TopologicalSpace R] [ContinuousMul R]

/-- If `a ^ m` for positive `m` is topologically nilpotent, then so is `a`. -/
theorem of_pow {a : R} {m : ℕ} (hm : 0 < m)
    (ha : IsTopologicallyNilpotent (a ^ m)) : IsTopologicallyNilpotent a := by
  intro U hU
  obtain ⟨V, hV, hSV⟩ := (isBounded_finite (Set.finite_range fun i : Fin m ↦ a ^ (i : ℕ))) U hU
  obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.mp (ha hV)
  refine Filter.mem_atTop_sets.mpr ⟨m * N, fun n hn ↦ ?_⟩
  rw [Set.mem_preimage, show a ^ n = (a ^ m) ^ (n / m) * a ^ (n % m) by
    rw [← pow_mul, ← pow_add, add_comm, Nat.mod_add_div]]
  exact hSV (Set.mul_mem_mul (hN _ ((Nat.le_div_iff_mul_le hm).mpr (by linarith)))
    ⟨⟨n % m, Nat.mod_lt n hm⟩, rfl⟩)

end ContinuousMul

section PowerBounded

section Semiring

variable {R : Type*} [Semiring R] [TopologicalSpace R]

open PowerBounded TopologicalRing

/-- Topologically nilpotent elements are power bounded. -/
theorem isPowerBounded [ContinuousMul R] {a : R} (ha : IsTopologicallyNilpotent a) :
    IsPowerBounded a := by
  intro U hU
  have : (fun p : R × R ↦ p.1 * p.2) ⁻¹' U ∈ 𝓝 ((0 : R), (0 : R)) :=
    continuous_mul.continuousAt.preimage_mem_nhds (by simp [hU])
  rw [nhds_prod_eq] at this
  obtain ⟨U₁, hU₁, U₂, hU₂, hprod⟩ := Filter.mem_prod_iff.mp this
  obtain ⟨N, hN⟩ := (ha.eventually hU₂).exists_forall_of_atTop
  choose V hV_mem hV_sub using (fun (i : Fin N) ↦ isBounded_singleton (a ^ (i : ℕ)) U hU)
  refine ⟨U₁ ∩ ⋂ i, V i, inter_mem hU₁ (Filter.iInter_mem.mpr hV_mem), ?_⟩
  intro x hx
  obtain ⟨c, hc, _, ⟨n, rfl⟩, rfl⟩ := Set.mem_mul.mp hx
  by_cases hn : n < N
  · exact hV_sub ⟨n, hn⟩ (Set.mem_mul.mpr ⟨c, Set.mem_iInter.mp hc.2 ⟨n, hn⟩, a ^ n, rfl, rfl⟩)
  · exact hprod (Set.mk_mem_prod hc.1 (hN n (by omega)))

/-- Product of power-bounded and topologically nilpotent is topologically nilpotent. -/
theorem mul_left_of_commute_isPowerBounded {a b : R} (h : Commute a b) (ha : IsPowerBounded a)
    (hb : IsTopologicallyNilpotent b) : IsTopologicallyNilpotent (a * b) := by
  intro U hU
  obtain ⟨V, hV, hSV⟩ := ha U hU
  rw [Filter.mem_map, h]
  refine Filter.mem_of_superset (Filter.mem_map.mp (hb hV)) ?_
  intro n hn
  simpa [Commute.mul_pow h.symm] using hSV (Set.mul_mem_mul hn ⟨n, rfl⟩)

/-- Product of topologically nilpotent and power bounded is topologically nilpotent. -/
theorem mul_right_of_commute_isPowerBounded {a b : R} (h : Commute a b)
    (ha : IsTopologicallyNilpotent a) (hb : IsPowerBounded b) :
    IsTopologicallyNilpotent (a * b) := by
  rw [h]
  exact mul_left_of_commute_isPowerBounded h.symm hb ha

end Semiring

section Ring

variable {R : Type*} [Ring R] [TopologicalSpace R]

/-- If `a` and `b` are topologically nilpotent and commute,
  then `a + b` is topologically nilpotent. -/
theorem add_of_commute' (S : Type*) [Ring S] [Module S R] [IsLinearTopology S R] {a b : R}
    [ContinuousMul R] (ha : IsTopologicallyNilpotent a) (hb : IsTopologicallyNilpotent b)
    (h : Commute a b) : IsTopologicallyNilpotent (a + b) := by
  intro U hU
  obtain ⟨V, hV_mem, hVU⟩ := (IsLinearTopology.hasBasis_submodule S).mem_iff.mp hU
  obtain ⟨W₁, hW₁_mem, hW₁_sub⟩ := IsTopologicallyNilpotent.isPowerBounded ha _ hV_mem
  obtain ⟨W₂, hW₂_mem, hW₂_sub⟩ := IsTopologicallyNilpotent.isPowerBounded hb _ hV_mem
  obtain ⟨Na, hNa⟩ := (ha.eventually hW₂_mem).exists_forall_of_atTop
  obtain ⟨Nb, hNb⟩ := (hb.eventually hW₁_mem).exists_forall_of_atTop
  refine Filter.mem_atTop_sets.mpr ⟨Na + Nb, fun n hn ↦ ?_⟩
  apply hVU
  simp_rw [SetLike.mem_coe, h.add_pow]
  refine V.toAddSubgroup.sum_mem fun k _ ↦ ?_
  rw [(Nat.cast_commute _ _).symm, ← nsmul_eq_mul]
  refine V.toAddSubgroup.nsmul_mem ?_ _
  by_cases hkNa : Na ≤ k
  · exact hW₂_sub (Set.mul_mem_mul (hNa k hkNa) ⟨n - k, rfl⟩)
  · rw [((h.pow_left k).pow_right (n - k)).eq]
    exact hW₁_sub (Set.mul_mem_mul (hNb (n - k) (by omega)) ⟨k, rfl⟩)

end Ring

section CommRing

variable {R : Type*} [CommRing R] [TopologicalSpace R]

open PowerBounded

/-- Product of power-bounded and topologically nilpotent is topologically nilpotent. -/
theorem mul_left_of_isPowerBounded {a b : R} (ha : IsPowerBounded a)
    (hb : IsTopologicallyNilpotent b) : IsTopologicallyNilpotent (a * b) :=
  mul_left_of_commute_isPowerBounded (Commute.all ..) ha hb

/-- Product of topologically nilpotent and power bounded is topologically nilpotent. -/
theorem mul_right_of_isPowerBounded {a b : R} (ha : IsTopologicallyNilpotent a)
    (hb : IsPowerBounded b) : IsTopologicallyNilpotent (a * b) :=
  mul_right_of_commute_isPowerBounded (Commute.all ..) ha hb

theorem add' (S : Type*) [Ring S] [Module S R] [IsLinearTopology S R] {a b : R} [ContinuousMul R]
    (ha : IsTopologicallyNilpotent a) (hb : IsTopologicallyNilpotent b) :
    IsTopologicallyNilpotent (a + b) :=
  add_of_commute' S ha hb (Commute.all ..)

variable [IsTopologicalRing R]

variable (S : Type*) [Ring S] [Module S R] [IsLinearTopology S R]

theorem subset_powerBoundedSubring :
    {a : R | IsTopologicallyNilpotent a} ⊆ PowerBounded.subring R (S := S) :=
  fun _ ↦ isPowerBounded

/-- The topological nilradical as an ideal of `PowerBounded.subring`. -/
def _root_.PowerBounded.topologicalNilradical : Ideal ↥(PowerBounded.subring R (S := S)) where
  carrier := Set.range (Set.inclusion (subset_powerBoundedSubring S))
  add_mem' := by
    simp only [Set.mem_range, Subtype.exists, Set.inclusion_mk, forall_exists_index, Subtype.forall,
      Subtype.mk.injEq, AddMemClass.mk_add_mk, exists_prop, exists_eq_right]
    intro _ _ _ _ _ hx rfl _ hy rfl
    simp_rw [Set.mem_ofPred_eq] at ⊢ hx hy
    exact add_of_commute' S hx hy (Commute.all ..)
  zero_mem' := by simpa using zero
  smul_mem' := by
    simp only [Set.mem_range, Subtype.exists, Set.inclusion_mk, smul_eq_mul, forall_exists_index,
      Subtype.forall, Subtype.mk.injEq, MulMemClass.mk_mul_mk, exists_prop, exists_eq_right]
    intro _ hb _ _ _ hx rfl
    simp_rw [Set.mem_ofPred_eq] at ⊢ hx
    exact mul_left_of_commute_isPowerBounded (Commute.all ..) hb hx

theorem _root_.PowerBounded.mem_topologicalNilradical_iff
    (x : ↥(PowerBounded.subring R (S := S))) :
    x ∈ PowerBounded.topologicalNilradical S ↔ IsTopologicallyNilpotent (x : R) :=
  ⟨by rintro ⟨⟨_, _⟩, rfl⟩; assumption, fun hx ↦ ⟨⟨_, hx⟩, rfl⟩⟩

/-- The residue field of power bounded elements quotiented by the topological nilradical. -/
def _root_.PowerBounded.residueField :=
  ↥(PowerBounded.subring R (S := S)) ⧸ (PowerBounded.topologicalNilradical S)

end CommRing

end PowerBounded

end IsTopologicallyNilpotent
