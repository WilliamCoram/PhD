/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import PhD.TauCeti.Code.PadicFunctionalAnalysis.GaugeNorm
import PhD.TauCeti.Code.PadicFunctionalAnalysis.PowerBounded
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Rescale
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Residue

/-!
# A Tate normed ring is a Tate ring in Huber's sense

Let `R` be a nonarchimedean normed commutative ring with `‖1‖ = 1` and a multiplicative
pseudo-uniformiser `ϖ`. Then the unit ball `R⁰` is an open subring, `ϖ` is a topologically
nilpotent unit, the powers of the ideal `(ϖ) ⊆ R⁰` are the norm balls
`(ϖ) ^ n = {r ∈ R⁰ | ‖r‖ ≤ ‖ϖ‖ ^ n}`, and hence the `(ϖ)`-adic topology of `R⁰` is the norm
topology: `(R⁰, (ϖ))` is a pair of definition and `R` is a Tate ring.

⚠ **Seam.** Neither Mathlib nor this chain has Huber rings. The four facts that make up a pair of
definition are stated here in Mathlib's vocabulary — `IsOpen`, `Ideal.FG`, `IsAdic`,
`IsTopologicallyNilpotent` — and at migration they assemble `TauCeti.Huber.PairOfDefinition` and
the instances `TauCeti.Huber.IsTateRing R`, `TauCeti.Huber.IsPseudoUniformizer ϖ`.

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, §0.4.5. Tau Ceti home:
`TauCeti/Analysis/Normed/Ring/Ultra/Huber.lean`.

## Main results

* `NormedRing.PseudoUniformizer.ideal_pow_eq_closedBallIdeal` — the ideal powers are the balls.
* `NormedRing.PseudoUniformizer.isAdic_ideal` — the topology of `R⁰` is `(ϖ)`-adic.
* `NormedRing.PseudoUniformizer.hasBasis_nhds_zero_smul_unitClosedBall` — `(ϖ ^ n R⁰)ₙ` is a basis
  of neighbourhoods of `0` in `R`.
* `NormedRing.PseudoUniformizer.gaugeNorm_unitClosedBall` — the gauge norm of `(R⁰, ϖ)` is the
  rescaled norm.
-/

open Filter Topology NNReal Pointwise

namespace NormedRing.PseudoUniformizer

open Subring

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R]
  (ϖ : PseudoUniformizer R)

omit [NormOneClass R] [IsUltrametricDist R] in
/-- Source: Johansson–Newton, Remark 2.1.3(1) ("`ϖ` is a topologically nilpotent unit"). -/
theorem isTopologicallyNilpotent : IsTopologicallyNilpotent (ϖ : R) := by
  exact IsTopologicallyNilpotent.of_norm_lt_one ϖ.norm_lt_one

/-- Source: roadmap §0.4.5 (`ϖⁿ R⁰ = {r ∈ R⁰ | ‖r‖ ≤ ‖ϖ‖ ^ n}`). -/
theorem mem_ideal_pow_iff {n : ℕ} {a : unitClosedBall R} :
    a ∈ ϖ.ideal ^ n ↔ ‖(a : R)‖ ≤ ‖(ϖ : R)‖ ^ n := by
  rw [ideal, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  have hpow :
      ((ϖ.toUnitClosedBall ^ n : unitClosedBall R) : R) = ((ϖ.unit ^ (n : ℤ) : Rˣ) : R) := by
    rw [SubmonoidClass.coe_pow, coe_toUnitClosedBall, zpow_natCast, Units.val_pow_eq_pow_val]
  constructor
  · rintro ⟨b, rfl⟩
    calc ‖((b * ϖ.toUnitClosedBall ^ n : unitClosedBall R) : R)‖
        = ‖(b : R) * ((ϖ.unit ^ (n : ℤ) : Rˣ) : R)‖ := by rw [Subring.coe_mul, hpow]
      _ ≤ ‖(b : R)‖ * ‖((ϖ.unit ^ (n : ℤ) : Rˣ) : R)‖ := _root_.norm_mul_le _ _
      _ ≤ ‖((ϖ.unit ^ (n : ℤ) : Rˣ) : R)‖ :=
        mul_le_of_le_one_left (norm_nonneg _) (Subring.norm_le_one b)
      _ = ‖(ϖ : R)‖ ^ n := by rw [ϖ.norm_zpow, zpow_natCast]
  · intro h
    have hb : ((ϖ.unit ^ (-(n : ℤ)) : Rˣ) : R) * a ∈ unitClosedBall R := by
      rw [Subring.mem_unitClosedBall, (ϖ.isMultiplicative.zpow _).norm_mul, ϖ.norm_zpow, zpow_neg,
        zpow_natCast]
      exact (inv_mul_le_iff₀ (pow_pos ϖ.norm_pos n)).2 (by rwa [mul_one])
    refine ⟨⟨_, hb⟩, Subtype.ext ?_⟩
    rw [Subring.coe_mul, hpow]
    change ((ϖ.unit ^ (-(n : ℤ)) : Rˣ) : R) * a * ((ϖ.unit ^ (n : ℤ) : Rˣ) : R) = a
    rw [mul_right_comm, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one,
      one_mul]

/-- Source: roadmap §0.4.5 ("the ideal powers are the norm balls"). -/
theorem ideal_pow_eq_closedBallIdeal (n : ℕ) :
    ϖ.ideal ^ n = closedBallIdeal R (‖(ϖ : R)‖₊ ^ n) := by
  ext a
  rw [ϖ.mem_ideal_pow_iff, mem_closedBallIdeal, NNReal.coe_pow, coe_nnnorm]

/-- Source: Wedhorn, Proposition and Definition 6.1(ii) (the ideal of definition is finitely
generated). -/
theorem ideal_fg : ϖ.ideal.FG := by
  exact Submodule.fg_span_singleton _

/-- Source: roadmap §0.4.5 ("the `(ϖ)`-adic topology of `R⁰` is the norm topology");
Johansson–Newton, Remark 2.1.3(1) ("the unit ball `R₀` is a ring of definition"). -/
theorem isAdic_ideal : IsAdic ϖ.ideal := by
  have hpos : (0 : ℝ≥0) < ‖(ϖ : R)‖₊ := by
    rw [← NNReal.coe_pos, coe_nnnorm]
    exact ϖ.norm_pos
  have hlt : ‖(ϖ : R)‖₊ < 1 := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
    exact ϖ.norm_lt_one
  rw [isAdic_iff]
  refine ⟨fun n ↦ ?_, fun s hs ↦ ?_⟩
  · rw [ϖ.ideal_pow_eq_closedBallIdeal]
    exact isOpen_closedBallIdeal (pow_pos hpos n)
  · obtain ⟨ε, hε, hεs⟩ := hasBasis_nhds_zero_closedBallIdeal.mem_iff.1 hs
    obtain ⟨n, hn⟩ := NNReal.exists_pow_lt_of_lt_one hε hlt
    refine ⟨n, fun a ha ↦ hεs ?_⟩
    rw [ϖ.ideal_pow_eq_closedBallIdeal] at ha
    exact closedBallIdeal_mono hn.le ha

/-- Source: Wedhorn, Proposition 6.14 (`A = B_s`: for every `a ∈ A` there is `n` with
`a sⁿ ∈ B`). -/
theorem exists_pow_mul_mem_unitClosedBall (a : R) :
    ∃ n : ℕ, (ϖ : R) ^ n * a ∈ unitClosedBall R := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact ⟨0, by simp⟩
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (norm_pos_iff.2 ha)) ϖ.norm_lt_one
  refine ⟨n, Subring.mem_unitClosedBall.2 ?_⟩
  rw [ϖ.isMultiplicative.norm_pow_mul]
  calc ‖(ϖ : R)‖ ^ n * ‖a‖ ≤ ‖a‖⁻¹ * ‖a‖ := mul_le_mul_of_nonneg_right hn.le (norm_nonneg a)
    _ = 1 := inv_mul_cancel₀ (norm_ne_zero_iff.2 ha)

/-- Source: Wedhorn, Example 6.13 ("`(rⁿ A₀)ₙ` is a fundamental system of neighbourhoods of
`0`"). -/
theorem hasBasis_nhds_zero_smul_unitClosedBall :
    (𝓝 (0 : R)).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ ((ϖ : R) ^ n) • (unitClosedBall R : Set R) := by
  have hset : ∀ n : ℕ, ((ϖ : R) ^ n) • (unitClosedBall R : Set R) =
      Metric.closedBall 0 (‖(ϖ : R)‖ ^ n) := by
    intro n
    ext x
    rw [Set.mem_smul_set, mem_closedBall_zero_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [smul_eq_mul, ϖ.isMultiplicative.norm_pow_mul]
      exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) n) (Subring.mem_unitClosedBall.1 hy)
    · intro hx
      refine ⟨((ϖ.unit ^ (-(n : ℤ)) : Rˣ) : R) * x, Subring.mem_unitClosedBall.2 ?_, ?_⟩
      · rw [(ϖ.isMultiplicative.zpow _).norm_mul, ϖ.norm_zpow, zpow_neg, zpow_natCast]
        exact (inv_mul_le_iff₀ (pow_pos ϖ.norm_pos n)).2 (by rwa [mul_one])
      · rw [smul_eq_mul, ← mul_assoc, ← Units.val_pow_eq_pow_val, ← zpow_natCast,
          ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one, one_mul]
  rw [show (fun n : ℕ ↦ ((ϖ : R) ^ n) • (unitClosedBall R : Set R)) =
    fun n ↦ Metric.closedBall 0 (‖(ϖ : R)‖ ^ n) from funext hset]
  exact Metric.nhds_basis_closedBall_pow ϖ.norm_pos ϖ.norm_lt_one

/-- **The round trip.** Passing from the norm of a Tate normed ring to its topology and back to
the gauge norm of `(R⁰, ϖ)` with `a = ‖ϖ‖⁻¹` returns the *rescaled* norm, not the norm: the two
bridges are inverse up to the power comparison of Johansson–Newton's Lemma 2.1.7. Source:
Johansson–Newton, Remark 2.1.3(1), read against the rescaled norm of §0.3.3. -/
theorem gaugeNorm_unitClosedBall (r : R) :
    (unitClosedBall R).gaugeNorm ϖ.unit ‖(ϖ : R)‖⁻¹ r = Real.zpowCeil ‖(ϖ : R)‖ ‖r‖ := by
  have hmem : ∀ n : ℤ, r ∈ ((ϖ.unit ^ n : Rˣ) : R) • (unitClosedBall R : Set R) ↔
      ‖r‖ ≤ ‖(ϖ : R)‖ ^ n := by
    intro n
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [smul_eq_mul, (ϖ.isMultiplicative.zpow n).norm_mul, ϖ.norm_zpow]
      exact mul_le_of_le_one_right (zpow_pos ϖ.norm_pos n).le (Subring.mem_unitClosedBall.1 hy)
    · intro hr
      refine ⟨((ϖ.unit ^ (-n) : Rˣ) : R) * r, Subring.mem_unitClosedBall.2 ?_, ?_⟩
      · rw [(ϖ.isMultiplicative.zpow _).norm_mul, ϖ.norm_zpow, zpow_neg]
        exact (inv_mul_le_iff₀ (zpow_pos ϖ.norm_pos n)).2 (by rwa [mul_one])
      · rw [smul_eq_mul, ← mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero,
          Units.val_one, one_mul]
  have hset : {y | ∃ n : ℤ, y = ‖(ϖ : R)‖⁻¹ ^ (-n) ∧
      r ∈ ((ϖ.unit ^ n : Rˣ) : R) • (unitClosedBall R : Set R)} =
      {y | ∃ n : ℤ, y = ‖(ϖ : R)‖ ^ n ∧ ‖r‖ ≤ ‖(ϖ : R)‖ ^ n} :=
    Set.ext fun y ↦ exists_congr fun n ↦ and_congr (by rw [inv_zpow', neg_neg]) (hmem n)
  exact congrArg sInf hset

end NormedRing.PseudoUniformizer

namespace NormedRing

/-- Source: roadmap §0.2.1 (`R⁰ ⊆ R°`). -/
theorem isPowerBounded_of_mem_unitClosedBall {R : Type*} [SeminormedRing R] [NormOneClass R]
    [IsUltrametricDist R] {a : R} (ha : a ∈ Subring.unitClosedBall R) :
    PowerBounded.IsPowerBounded a := by
  exact PowerBounded.isPowerBounded_of_norm_le_one (Subring.mem_unitClosedBall.1 ha)

end NormedRing
