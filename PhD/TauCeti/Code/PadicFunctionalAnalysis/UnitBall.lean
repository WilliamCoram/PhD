/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Field.UnitBall
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Topology.Algebra.TopologicallyNilpotent
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Sums

/-!
# The unit ball of a nonarchimedean normed ring

For a nonarchimedean normed ring `R` with `‖1‖ = 1`, the closed unit ball `R⁰ = {r | ‖r‖ ≤ 1}` is
a subring (`Subring.unitClosedBall`, extending Mathlib's `Submonoid.unitClosedBall`), the closed
balls of radius `ε ≤ 1` are ideals of it (`NormedRing.closedBallIdeal`), and so is the open unit
ball `R⁰⁰` (`NormedRing.openUnitBallIdeal`). The topology of `R⁰` is linear, `R⁰⁰` consists of
topologically nilpotent elements, and when `R` is complete the Neumann series shows that `R⁰⁰` lies
in the Jacobson radical of `R⁰` and that units of `R⁰` are detected modulo `R⁰⁰`.

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, §0.2.1 and §0.2.3. Tau Ceti home:
`TauCeti/Analysis/Normed/Ring/Ultra/UnitBall.lean`.

## Main definitions

* `Subring.unitClosedBall R` — the closed unit ball `R⁰`, as a subring.
* `NormedRing.closedBallIdeal R ε` — the ideal `{a ∈ R⁰ | ‖a‖ ≤ ε}` of `R⁰`.
* `NormedRing.openUnitBallIdeal R` — the ideal `R⁰⁰ = {a ∈ R⁰ | ‖a‖ < 1}` of `R⁰`.

## Main results

* `NormedRing.norm_tsum_geometric`, `NormedRing.norm_tsum_geometric_sub_one` — the ultrametric
  norms of the Neumann series.
* `NormedRing.isUnit_iff_isUnit_mk` — units of `R⁰` are detected modulo `R⁰⁰`.
* `NormedRing.openUnitBallIdeal_le_jacobson_bot` — `R⁰⁰` lies in the Jacobson radical of `R⁰`.
* `NormedRing.maximalIdeal_unitClosedBall` — for a normed field, `R⁰` is local with maximal ideal
  `R⁰⁰`.
-/

open Filter Topology NNReal Metric

/-! ### The closed unit ball as a subring -/

namespace Subring

variable (R : Type*) [SeminormedRing R] [NormOneClass R] [IsUltrametricDist R]

/-- The closed unit ball `R⁰` of a nonarchimedean seminormed ring with `‖1‖ = 1`, as a subring.
Source: roadmap §0.2.1; Schneider, Lemma 1.2.i. -/
def unitClosedBall : Subring R where
  carrier := closedBall 0 1
  mul_mem' := (Submonoid.unitClosedBall R).mul_mem'
  one_mem' := (Submonoid.unitClosedBall R).one_mem'
  add_mem' {x y} hx hy := by
    rw [mem_closedBall_zero_iff] at *
    exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  zero_mem' := by simp
  neg_mem' {x} hx := by simpa using hx

variable {R}

@[simp]
theorem mem_unitClosedBall {x : R} : x ∈ unitClosedBall R ↔ ‖x‖ ≤ 1 := by
  exact mem_closedBall_zero_iff

@[simp]
theorem coe_unitClosedBall : (unitClosedBall R : Set R) = closedBall 0 1 := rfl

@[simp]
theorem unitClosedBall_toSubmonoid :
    (unitClosedBall R).toSubmonoid = Submonoid.unitClosedBall R := rfl

theorem norm_le_one (x : unitClosedBall R) : ‖(x : R)‖ ≤ 1 := by
  exact mem_unitClosedBall.1 x.2

/-- Source: roadmap §0.4.5 (the ring of definition is open); Wedhorn, Example 6.13. -/
theorem isOpen_unitClosedBall : IsOpen (unitClosedBall R : Set R) := by
  rw [coe_unitClosedBall]
  exact IsUltrametricDist.isOpen_closedBall 0 one_ne_zero

theorem isClosed_unitClosedBall : IsClosed (unitClosedBall R : Set R) := by
  rw [coe_unitClosedBall]
  exact isClosed_closedBall

end Subring

namespace NormedRing

open Subring

/-! ### Ball ideals of the unit ball -/

section Ideals

variable (R : Type*) [SeminormedRing R] [NormOneClass R] [IsUltrametricDist R]

/-- The ideal `{a ∈ R⁰ | ‖a‖ ≤ ε}` of the closed unit ball. Source: roadmap §0.2.1, §0.4.5. -/
def closedBallIdeal (ε : ℝ≥0) : Ideal (unitClosedBall R) where
  carrier := {a | ‖(a : R)‖₊ ≤ ε}
  add_mem' {a b} ha hb := (IsUltrametricDist.nnnorm_add_le_max (a : R) b).trans (max_le ha hb)
  zero_mem' := by simp
  smul_mem' r a ha := by
    change ‖(r : R) * a‖₊ ≤ ε
    exact ((nnnorm_mul_le _ _).trans (mul_le_of_le_one_left (by positivity)
      (by exact_mod_cast Subring.norm_le_one r))).trans ha

/-- The open unit ball `R⁰⁰ = {a ∈ R⁰ | ‖a‖ < 1}`, as an ideal of the closed unit ball.
Source: roadmap §0.2.1; Schneider, Lemma 1.2.ii. -/
def openUnitBallIdeal : Ideal (unitClosedBall R) where
  carrier := {a | ‖(a : R)‖ < 1}
  add_mem' {a b} ha hb := (IsUltrametricDist.norm_add_le_max (a : R) b).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' r a ha := by
    have ha' : ‖(a : R)‖ < 1 := ha
    change ‖(r : R) * a‖ < 1
    calc ‖(r : R) * a‖ ≤ ‖(r : R)‖ * ‖(a : R)‖ := _root_.norm_mul_le _ _
      _ ≤ ‖(a : R)‖ := mul_le_of_le_one_left (norm_nonneg _) (Subring.norm_le_one r)
      _ < 1 := ha'

variable {R}

@[simp]
theorem mem_closedBallIdeal {ε : ℝ≥0} {a : unitClosedBall R} :
    a ∈ closedBallIdeal R ε ↔ ‖(a : R)‖ ≤ ε := by
  change ‖(a : R)‖₊ ≤ ε ↔ _
  rw [← NNReal.coe_le_coe, coe_nnnorm]

@[simp]
theorem mem_openUnitBallIdeal {a : unitClosedBall R} :
    a ∈ openUnitBallIdeal R ↔ ‖(a : R)‖ < 1 := by
  exact Iff.rfl

theorem closedBallIdeal_mono {ε δ : ℝ≥0} (h : ε ≤ δ) :
    closedBallIdeal R ε ≤ closedBallIdeal R δ := by
  exact fun a ha ↦ le_trans ha h

theorem closedBallIdeal_one : closedBallIdeal R 1 = ⊤ := by
  refine eq_top_iff.2 fun a _ ↦ mem_closedBallIdeal.2 ?_
  simpa using Subring.norm_le_one a

theorem closedBallIdeal_mul_le (ε δ : ℝ≥0) :
    closedBallIdeal R ε * closedBallIdeal R δ ≤ closedBallIdeal R (ε * δ) := by
  refine Ideal.mul_le.2 fun a ha b hb ↦ ?_
  change ‖(a : R) * b‖₊ ≤ ε * δ
  exact (nnnorm_mul_le _ _).trans (mul_le_mul' ha hb)

theorem closedBallIdeal_le_openUnitBallIdeal {ε : ℝ≥0} (hε : ε < 1) :
    closedBallIdeal R ε ≤ openUnitBallIdeal R := by
  exact fun a ha ↦ mem_openUnitBallIdeal.2
    ((mem_closedBallIdeal.1 ha).trans_lt (by exact_mod_cast hε))

theorem isOpen_closedBallIdeal {ε : ℝ≥0} (hε : 0 < ε) :
    IsOpen (closedBallIdeal R ε : Set (unitClosedBall R)) := by
  have h : (closedBallIdeal R ε : Set (unitClosedBall R)) = (↑) ⁻¹' closedBall (0 : R) ε := by
    ext a
    simp
  rw [h]
  exact (IsUltrametricDist.isOpen_closedBall 0 (by exact_mod_cast hε.ne')).preimage
    continuous_subtype_val

theorem isOpen_openUnitBallIdeal : IsOpen (openUnitBallIdeal R : Set (unitClosedBall R)) := by
  have h : (openUnitBallIdeal R : Set (unitClosedBall R)) = (↑) ⁻¹' ball (0 : R) 1 := by
    ext a
    simp
  rw [h]
  exact isOpen_ball.preimage continuous_subtype_val

/-- The closed balls of positive radius are a basis of neighbourhoods of `0` in `R⁰`. -/
theorem hasBasis_nhds_zero_closedBallIdeal :
    (𝓝 (0 : unitClosedBall R)).HasBasis (fun ε : ℝ≥0 ↦ 0 < ε)
      fun ε ↦ (closedBallIdeal R ε : Set (unitClosedBall R)) := by
  refine nhds_basis_closedBall.to_hasBasis
    (fun ε hε ↦ ⟨ε.toNNReal, Real.toNNReal_pos.2 hε, fun a ha ↦ ?_⟩)
    fun ε hε ↦ ⟨ε, by exact_mod_cast hε, fun a ha ↦ ?_⟩
  · rw [SetLike.mem_coe, mem_closedBallIdeal, Real.coe_toNNReal _ hε.le] at ha
    exact mem_closedBall_zero_iff.2 ha
  · rw [SetLike.mem_coe, mem_closedBallIdeal]
    exact mem_closedBall_zero_iff.1 ha

/-- Source: roadmap §0.2.1 (the topology of `R⁰` is linear: the ball ideals are a basis). -/
instance instIsLinearTopologyUnitClosedBall :
    IsLinearTopology (unitClosedBall R) (unitClosedBall R) := by
  exact IsLinearTopology.mk_of_hasBasis (unitClosedBall R) hasBasis_nhds_zero_closedBallIdeal

end Ideals

/-! ### The linear topology of the unit ball, and topological nilpotency -/

section Comm

variable {R : Type*} [SeminormedCommRing R] [NormOneClass R] [IsUltrametricDist R]

/-- Source: roadmap §0.2.1; Wedhorn, Example 5.29(2). -/
theorem openUnitBallIdeal_le_topologicalNilradical :
    openUnitBallIdeal R ≤ topologicalNilradical (unitClosedBall R) := by
  exact fun a ha ↦ IsTopologicallyNilpotent.mem_topologicalNilradical_iff.2
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (mem_openUnitBallIdeal.1 ha))

/-- Source: roadmap §0.2.2 (`R⁰⁰ = R°°` for a multiplicative norm); Wedhorn, Example 5.29(2). -/
theorem openUnitBallIdeal_eq_topologicalNilradical [NormMulClass R] :
    openUnitBallIdeal R = topologicalNilradical (unitClosedBall R) := by
  refine le_antisymm openUnitBallIdeal_le_topologicalNilradical fun a ha ↦ ?_
  rw [IsTopologicallyNilpotent.mem_topologicalNilradical_iff] at ha
  have h := ha.norm
  rw [norm_zero] at h
  have h' : Tendsto (fun n : ℕ ↦ ‖(a : R)‖ ^ n) atTop (𝓝 0) := by
    refine h.congr fun n ↦ ?_
    change ‖((a ^ n : unitClosedBall R) : R)‖ = _
    rw [SubmonoidClass.coe_pow, norm_pow]
  have h'' := tendsto_pow_atTop_nhds_zero_iff.1 h'
  rw [abs_norm] at h''
  exact mem_openUnitBallIdeal.2 h''

end Comm

/-! ### The Neumann series -/

section Neumann

variable {R : Type*} [NormedRing R] [NormOneClass R] [IsUltrametricDist R]

/-- Source: roadmap §0.2.3. -/
theorem norm_one_sub_of_norm_lt_one {x : R} (h : ‖x‖ < 1) : ‖1 - x‖ = 1 := by
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
    (by rw [norm_one, norm_neg]; exact h.ne'), norm_one, norm_neg, max_eq_left h.le]

/-- Source: roadmap §0.2.3 (`‖(1 − x)⁻¹‖ = 1`). -/
theorem norm_tsum_geometric [CompleteSpace R] {x : R} (h : ‖x‖ < 1) :
    ‖∑' n : ℕ, x ^ n‖ = 1 := by
  refine (IsUltrametricDist.norm_tsum_eq_of_forall_lt (summable_geometric_of_norm_lt_one h)
    (i₀ := 0) fun n hn ↦ ?_).trans (by simp)
  rw [pow_zero, norm_one]
  exact (norm_pow_le' x (Nat.pos_of_ne_zero hn)).trans_lt (pow_lt_one₀ (norm_nonneg _) h hn)

omit [NormOneClass R] in
/-- Source: roadmap §0.2.3 (`‖(1 − x)⁻¹ − 1‖ = ‖x‖`). -/
theorem norm_tsum_geometric_sub_one [CompleteSpace R] {x : R} (h : ‖x‖ < 1) :
    ‖∑' n : ℕ, x ^ n - 1‖ = ‖x‖ := by
  rw [← geom_series_succ x h]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hs : Summable fun i : ℕ ↦ x ^ (i + 1) :=
    (summable_geometric_of_norm_lt_one h).comp_injective (add_left_injective 1)
  refine (IsUltrametricDist.norm_tsum_eq_of_forall_lt hs (i₀ := 0) fun i hi ↦ ?_).trans (by simp)
  rw [zero_add, pow_one]
  exact (norm_pow_le' x i.succ_pos).trans_lt
    (pow_lt_self_of_lt_one₀ (norm_pos_iff.2 hx) h (by omega))

/-- Source: roadmap §0.2.3 (an element of `R⁰` congruent to `1` modulo `R⁰⁰` is a unit of `R⁰`). -/
theorem isUnit_of_norm_one_sub_lt_one [CompleteSpace R] {a : unitClosedBall R}
    (h : ‖(1 : R) - a‖ < 1) : IsUnit a := by
  obtain ⟨x, hx⟩ : ∃ x : R, x = 1 - a := ⟨_, rfl⟩
  rw [← hx] at h
  have hmem : ∑' n : ℕ, x ^ n ∈ unitClosedBall R :=
    Subring.mem_unitClosedBall.2 (norm_tsum_geometric h).le
  have hax : (1 : R) - x = a := by rw [hx, sub_sub_cancel]
  refine ⟨⟨a, ⟨_, hmem⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
  · change (a : R) * ∑' n : ℕ, x ^ n = 1
    rw [← hax]
    exact mul_neg_geom_series x h
  · change (∑' n : ℕ, x ^ n) * (a : R) = 1
    rw [← hax]
    exact geom_series_mul_neg x h

end Neumann

/-! ### Units of the unit ball -/

section Units

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R] [CompleteSpace R]

/-- Source: roadmap §0.2.3 ("the units of `R⁰` are exactly the elements whose image in `R⁰/R⁰⁰` is a
unit"). -/
theorem isUnit_iff_isUnit_mk (a : unitClosedBall R) :
    IsUnit a ↔ IsUnit (Ideal.Quotient.mk (openUnitBallIdeal R) a) := by
  refine ⟨fun h ↦ h.map _, fun h ↦ ?_⟩
  obtain ⟨u, hu⟩ := h
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : unitClosedBall R ⧸ openUnitBallIdeal R)
  have h1 : Ideal.Quotient.mk (openUnitBallIdeal R) (a * b) = 1 := by
    rw [map_mul, hb, ← hu, Units.mul_inv]
  have h2 : (1 : unitClosedBall R) - a * b ∈ openUnitBallIdeal R :=
    Ideal.Quotient.eq.1 (by rw [map_one, h1])
  exact isUnit_of_mul_isUnit_left (isUnit_of_norm_one_sub_lt_one (mem_openUnitBallIdeal.1 h2))

/-- Source: roadmap §0.2.3 (corrected form: the Jacobson radical, not "the unique maximal
ideal"). -/
theorem openUnitBallIdeal_le_jacobson_bot :
    openUnitBallIdeal R ≤ Ideal.jacobson (⊥ : Ideal (unitClosedBall R)) := by
  intro x hx
  refine Ideal.mem_jacobson_bot.2 fun y ↦ isUnit_of_norm_one_sub_lt_one ?_
  change ‖(1 : R) - ((x : R) * y + 1)‖ < 1
  rw [show (1 : R) - ((x : R) * y + 1) = -((x : R) * y) by abel, norm_neg]
  exact ((_root_.norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _)
    (Subring.norm_le_one y))).trans_lt (mem_openUnitBallIdeal.1 hx)

end Units

/-! ### Normed fields -/

section Field

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- Source: Schneider, Lemma 1.2.iii (`o× = o ∖ m`). -/
theorem isUnit_iff_norm_eq_one {a : unitClosedBall K} : IsUnit a ↔ ‖(a : K)‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ‖((u : unitClosedBall K) : K)‖ * ‖((↑u⁻¹ : unitClosedBall K) : K)‖ = 1 := by
      rw [← norm_mul, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one, norm_one]
    have h3 := Subring.norm_le_one (↑u⁻¹ : unitClosedBall K)
    by_contra hne
    have h4 : ‖((u : unitClosedBall K) : K)‖ < 1 := lt_of_le_of_ne (Subring.norm_le_one _) hne
    have : ‖((u : unitClosedBall K) : K)‖ * ‖((↑u⁻¹ : unitClosedBall K) : K)‖ < 1 :=
      (mul_le_of_le_one_right (norm_nonneg _) h3).trans_lt h4
    linarith
  · intro h
    have ha : (a : K) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h
      exact zero_ne_one h
    refine ⟨⟨a, ⟨(a : K)⁻¹, Subring.mem_unitClosedBall.2 (by rw [norm_inv, h, inv_one])⟩,
      Subtype.ext (mul_inv_cancel₀ ha), Subtype.ext (inv_mul_cancel₀ ha)⟩, rfl⟩

/-- Source: Schneider, Lemma 1.2.ii. -/
instance instIsLocalRingUnitClosedBall : IsLocalRing (unitClosedBall K) := by
  refine IsLocalRing.of_nonunits_add fun a b ha hb ↦ ?_
  rw [mem_nonunits_iff, isUnit_iff_norm_eq_one] at ha hb ⊢
  exact ((IsUltrametricDist.norm_add_le_max (a : K) b).trans_lt
    (max_lt (lt_of_le_of_ne (Subring.norm_le_one a) ha)
      (lt_of_le_of_ne (Subring.norm_le_one b) hb))).ne

/-- Source: roadmap §0.2.3 (field case); Schneider, Lemma 1.2.ii (`m` is the unique maximal
ideal of `o`). -/
theorem maximalIdeal_unitClosedBall :
    IsLocalRing.maximalIdeal (unitClosedBall K) = openUnitBallIdeal K := by
  ext a
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_norm_eq_one,
    mem_openUnitBallIdeal]
  exact ⟨fun h ↦ lt_of_le_of_ne (Subring.norm_le_one a) h, fun h ↦ h.ne⟩

end Field

end NormedRing
