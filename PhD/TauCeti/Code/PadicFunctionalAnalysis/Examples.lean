/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.Padics.RingHoms
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Huber

/-!
# Examples for Layer 0

The worked examples of the roadmap's Layer 0, as theorems: `ℚ_p`, `ℤ_p` and `ℂ_p` as nonarchimedean
normed rings, with their unit balls, open unit balls and residue rings; the shells
`‖p‖ < ‖pⁿ x‖ ≤ 1` in `ℚ_p`; the Neumann series of `1 - p` in `ℤ_p`; the rescaled norm on `ℂ_p`,
which is not the norm; the non-example `ℤ_p`, which is not Tate; and the two counterexamples to the
norm characterisation of power-boundedness.

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, Layer 0 "Examples", §0.2.2
(counterexamples) and §0.4.7. Tau Ceti home: the test files next to
`TauCeti/Analysis/Normed/Ring/Ultra/`.
-/

open Filter Topology NNReal

namespace NormedRing

open Subring PseudoUniformizer

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### `ℚ_p` and `ℤ_p` -/

/-- Source: roadmap, Layer 0 Examples (`R⁰` for `R = ℚ_p`). -/
theorem unitClosedBall_padic : unitClosedBall ℚ_[p] = PadicInt.subring p := by
  ext x
  rw [Subring.mem_unitClosedBall, PadicInt.mem_subring_iff]

/-- Source: roadmap, Layer 0 Examples (`R⁰⁰ = p R⁰` for `R = ℚ_p`). -/
theorem ideal_padic_eq_openUnitBallIdeal (hc₀ : (p : ℚ_[p]) ≠ 0) (hc₁ : ‖(p : ℚ_[p])‖ < 1) :
    (ofNormedAlgebra ℚ_[p] hc₀ hc₁ : PseudoUniformizer ℚ_[p]).ideal =
      openUnitBallIdeal ℚ_[p] := by
  refine PseudoUniformizer.ideal_eq_openUnitBallIdeal _ fun r hr ↦ ⟨r.valuation, ?_⟩
  rw [coe_ofNormedAlgebra, Algebra.algebraMap_self, RingHom.id_apply, Padic.norm_p,
    Padic.norm_eq_zpow_neg_valuation hr, inv_zpow']

/-- Source: roadmap, Layer 0 Examples (the residue ring of `ℚ_p`). -/
theorem nonempty_residueRing_padic_equiv_zmod :
    Nonempty ((unitClosedBall ℚ_[p] ⧸ openUnitBallIdeal ℚ_[p]) ≃+* ZMod p) := by
  let e : unitClosedBall ℚ_[p] ≃+* ℤ_[p] :=
    { toFun := fun x ↦ ⟨x, Subring.mem_unitClosedBall.1 x.2⟩
      invFun := fun z ↦ ⟨z, Subring.mem_unitClosedBall.2 z.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  let f : unitClosedBall ℚ_[p] →+* ZMod p := PadicInt.toZMod.comp e.toRingHom
  have hker : RingHom.ker f = openUnitBallIdeal ℚ_[p] := by
    ext x
    rw [RingHom.mem_ker, mem_openUnitBallIdeal]
    change PadicInt.toZMod (e x) = 0 ↔ _
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal,
      PadicInt.mem_nonunits]
    rfl
  exact ⟨(Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective f))⟩

/-- Source: roadmap, Layer 0 Examples ("the shells `‖ϖ‖ < ‖ϖⁿ x‖ ≤ 1` in `ℚ_p` with `ϖ = p`"). -/
theorem norm_zpow_mul_mem_Ioc_iff {x : ℚ_[p]} (hx : x ≠ 0) (n : ℤ) :
    ‖(p : ℚ_[p]) ^ n * x‖ ∈ Set.Ioc ‖(p : ℚ_[p])‖ 1 ↔ n = -x.valuation := by
  have hp' : (1 : ℝ) < p := Nat.one_lt_cast.2 hp.out.one_lt
  have hnorm : ‖(p : ℚ_[p]) ^ n * x‖ = (p : ℝ) ^ (-(n + x.valuation)) := by
    rw [_root_.norm_mul, _root_.norm_zpow, Padic.norm_p, Padic.norm_eq_zpow_neg_valuation hx,
      inv_zpow', ← zpow_add₀ (by positivity), neg_add]
  rw [hnorm, Padic.norm_p, Set.mem_Ioc, ← zpow_neg_one, zpow_lt_zpow_iff_right₀ hp',
    zpow_le_one_iff_right₀ hp']
  omega

/-- Source: roadmap §0.4.7 (the non-example): `ℤ_p` has no unit of norm less than `1`. -/
theorem not_isTate_padicInt : ¬ IsTate ℤ_[p] := by
  rintro ⟨⟨ϖ⟩⟩
  have h1 : ‖(ϖ : ℤ_[p])‖ = 1 := PadicInt.isUnit_iff.1 ϖ.unit.isUnit
  linarith [ϖ.norm_lt_one]

private theorem norm_p_padicInt_lt_one : ‖(p : ℤ_[p])‖ < 1 := by
  rw [PadicInt.norm_p]
  exact inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 hp.out.one_lt)

/-- Source: roadmap, Layer 0 Examples and acceptance examples (`‖∑' n, pⁿ‖ = 1` in `ℤ_p`). -/
theorem norm_tsum_pow_padicInt : ‖∑' n : ℕ, (p : ℤ_[p]) ^ n‖ = 1 := by
  exact norm_tsum_geometric (norm_p_padicInt_lt_one p)

/-- Source: roadmap, Layer 0 Examples ("the Neumann inverse of `1 − p` in `ℤ_p`"). -/
theorem norm_tsum_pow_padicInt_sub_one : ‖∑' n : ℕ, (p : ℤ_[p]) ^ n - 1‖ = (p : ℝ)⁻¹ := by
  rw [norm_tsum_geometric_sub_one (norm_p_padicInt_lt_one p), PadicInt.norm_p]

/-! ### `ℂ_p` -/

private theorem norm_p_padicComplex : ‖(p : ℂ_[p])‖ = ‖(p : ℚ_[p])‖ := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]) p, norm_algebraMap']

/-- Source: roadmap, Layer 0 Examples (`ℂ_p` is not discretely valued: `‖√p‖ = p ^ (-1/2)`). -/
theorem exists_norm_p_lt_norm_lt_one_padicComplex :
    ∃ x : ℂ_[p], ‖(p : ℂ_[p])‖ < ‖x‖ ∧ ‖x‖ < 1 := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (p : ℂ_[p]) two_pos
  have hp' : (1 : ℝ) < p := Nat.one_lt_cast.2 hp.out.one_lt
  have ht0 : 0 < (p : ℝ)⁻¹ := inv_pos.2 (zero_lt_one.trans hp')
  have ht1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp'
  have hx2 : ‖x‖ ^ 2 = (p : ℝ)⁻¹ := by
    rw [← _root_.norm_pow, hx, norm_p_padicComplex, Padic.norm_p]
  rw [norm_p_padicComplex, Padic.norm_p]
  refine ⟨x, lt_of_not_ge fun h ↦ ?_, lt_of_not_ge fun h ↦ ?_⟩
  · have h1 : ‖x‖ ^ 2 ≤ ((p : ℝ)⁻¹) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    have h2 : ((p : ℝ)⁻¹) ^ 2 < (p : ℝ)⁻¹ := by
      rw [sq]
      exact mul_lt_of_lt_one_right ht0 ht1
    linarith
  · have h1 : 1 ≤ ‖x‖ ^ 2 := one_le_pow₀ h
    linarith

/-- Source: roadmap, Layer 0 Examples ("the rescaled norm on `ℂ_p` with `π = p` ... is not the
original norm"). -/
theorem exists_zpowCeil_norm_ne_padicComplex :
    ∃ x : ℂ_[p], Real.zpowCeil ‖(p : ℂ_[p])‖ ‖x‖ ≠ ‖x‖ := by
  obtain ⟨x, hx1, hx2⟩ := exists_norm_p_lt_norm_lt_one_padicComplex p
  have hc₀ : 0 < ‖(p : ℂ_[p])‖ := by
    rw [norm_p_padicComplex, Padic.norm_p]
    exact inv_pos.2 (Nat.cast_pos.2 hp.out.pos)
  have hc₁ : ‖(p : ℂ_[p])‖ < 1 := hx1.trans hx2
  refine ⟨x, fun h ↦ ?_⟩
  obtain ⟨n, hn⟩ := Real.exists_zpowCeil_eq_zpow hc₀ hc₁ (hc₀.trans hx1)
  rw [hn] at h
  have h1 : ‖(p : ℂ_[p])‖ ^ (1 : ℤ) < ‖(p : ℂ_[p])‖ ^ n := by rw [zpow_one, h]; exact hx1
  have h2 : ‖(p : ℂ_[p])‖ ^ n < ‖(p : ℂ_[p])‖ ^ (0 : ℤ) := by rw [zpow_zero, h]; exact hx2
  rw [zpow_lt_zpow_iff_right_of_lt_one₀ hc₀ hc₁] at h1 h2
  omega

/-- Source: roadmap, Layer 0 Examples (`p R⁰ ≠ R⁰⁰` for `R = ℂ_p`). -/
theorem ideal_padicComplex_ne_openUnitBallIdeal (hc₀ : (p : ℚ_[p]) ≠ 0)
    (hc₁ : ‖(p : ℚ_[p])‖ < 1) :
    (ofNormedAlgebra ℚ_[p] hc₀ hc₁ : PseudoUniformizer ℂ_[p]).ideal ≠
      openUnitBallIdeal ℂ_[p] := by
  intro h
  obtain ⟨x, hx1, hx2⟩ := exists_norm_p_lt_norm_lt_one_padicComplex p
  have hmem : (⟨x, Subring.mem_unitClosedBall.2 hx2.le⟩ : unitClosedBall ℂ_[p]) ∈
      openUnitBallIdeal ℂ_[p] := mem_openUnitBallIdeal.2 hx2
  rw [← h, PseudoUniformizer.mem_ideal_iff, coe_ofNormedAlgebra, norm_algebraMap'] at hmem
  change ‖x‖ ≤ _ at hmem
  rw [norm_p_padicComplex] at hx1
  linarith

/-! ### The two counterexamples of §0.2.2 -/

/-- Source: roadmap §0.2.2 ("over `ℤ` with the discrete topology every element is
power-bounded"). -/
theorem isPowerBounded_int (n : ℤ) : PowerBounded.IsPowerBounded n := by
  intro U hU
  refine ⟨{0}, (isOpen_discrete _).mem_nhds (Set.mem_singleton 0), ?_⟩
  rintro _ ⟨a, ha, b, -, rfl⟩
  rw [Set.mem_singleton_iff.1 ha]
  change (0 : ℤ) * b ∈ U
  rw [zero_mul]
  exact mem_of_mem_nhds hU

/-- Source: roadmap §0.2.2 ("while `‖2‖ = 2`"). -/
theorem norm_two_int : ‖(2 : ℤ)‖ = 2 := by
  rw [Int.norm_eq_abs]
  norm_num

/-- Source: roadmap §0.2.2 (the hypothesis of `isPowerBounded_iff_norm_le_one` that fails for
`ℤ`). -/
theorem not_neBot_nhdsNE_zero_int : ¬ NeBot (𝓝[≠] (0 : ℤ)) := by
  intro h
  exact h.ne (discreteTopology_iff_nhds_ne.1 inferInstance 0)

end NormedRing

/-- The ring `ℝ[X]/(X² - X)`, realised on `ℝ × ℝ` by `a + bX ↦ (a, a + b)`, to carry the `ℓ¹` norm
`‖a + bX‖ = |a| + |b|` in the basis `1, X`. Source: roadmap §0.2.2 (second counterexample). -/
def L1Pair : Type := ℝ × ℝ

namespace L1Pair

instance : CommRing L1Pair := inferInstanceAs (CommRing (ℝ × ℝ))

/-- The `ℓ¹` norm of `a + bX` in the coordinates `(u, v) = (a, a + b)`: `|u| + |v - u|`. -/
noncomputable def addGroupNorm : AddGroupNorm L1Pair where
  toFun x := |x.1| + |x.2 - x.1|
  map_zero' := by
    change |(0 : ℝ)| + |(0 : ℝ) - 0| = 0
    simp
  add_le' x y := by
    change |x.1 + y.1| + |(x.2 + y.2) - (x.1 + y.1)| ≤ |x.1| + |x.2 - x.1| + (|y.1| + |y.2 - y.1|)
    have h1 := abs_add_le x.1 y.1
    have h2 : |(x.2 + y.2) - (x.1 + y.1)| ≤ |x.2 - x.1| + |y.2 - y.1| := by
      rw [show (x.2 + y.2) - (x.1 + y.1) = (x.2 - x.1) + (y.2 - y.1) by ring]
      exact abs_add_le _ _
    linarith
  neg' x := by
    change |-x.1| + |-x.2 - -x.1| = |x.1| + |x.2 - x.1|
    rw [abs_neg, show -x.2 - -x.1 = -(x.2 - x.1) by ring, abs_neg]
  eq_zero_of_map_eq_zero' x hx := by
    change |x.1| + |x.2 - x.1| = 0 at hx
    have h1 : |x.1| = 0 := by linarith [abs_nonneg x.1, abs_nonneg (x.2 - x.1)]
    have h2 : |x.2 - x.1| = 0 := by linarith [abs_nonneg x.1, abs_nonneg (x.2 - x.1)]
    rw [abs_eq_zero] at h1 h2
    exact Prod.ext h1 (show x.2 = 0 by linarith)

noncomputable instance : NormedAddCommGroup L1Pair := addGroupNorm.toNormedAddCommGroup

theorem norm_def (x : L1Pair) : ‖x‖ = |x.1| + |x.2 - x.1| := rfl

/-- The `ℓ¹` norm is submultiplicative. -/
theorem norm_mul_le (x y : L1Pair) : ‖x * y‖ ≤ ‖x‖ * ‖y‖ := by
  rw [norm_def, norm_def, norm_def]
  change |x.1 * y.1| + |x.2 * y.2 - x.1 * y.1| ≤ _
  have key : x.2 * y.2 - x.1 * y.1 =
      x.1 * (y.2 - y.1) + (x.2 - x.1) * y.1 + (x.2 - x.1) * (y.2 - y.1) := by ring
  rw [key, abs_mul]
  have h3 := abs_add_three (x.1 * (y.2 - y.1)) ((x.2 - x.1) * y.1) ((x.2 - x.1) * (y.2 - y.1))
  rw [abs_mul, abs_mul, abs_mul] at h3
  calc |x.1| * |y.1| + |x.1 * (y.2 - y.1) + (x.2 - x.1) * y.1 + (x.2 - x.1) * (y.2 - y.1)|
      ≤ |x.1| * |y.1| + (|x.1| * |y.2 - y.1| + |x.2 - x.1| * |y.1| +
          |x.2 - x.1| * |y.2 - y.1|) := by linarith [h3]
    _ = (|x.1| + |x.2 - x.1|) * (|y.1| + |y.2 - y.1|) := by ring

noncomputable instance : NormedCommRing L1Pair where
  __ := (inferInstance : NormedAddCommGroup L1Pair)
  __ := (inferInstance : CommRing L1Pair)
  norm_mul_le := norm_mul_le

/-- The element `1 - 2X`, i.e. `(1, -1)`. -/
def oneSubTwoX : L1Pair := ((1 : ℝ), (-1 : ℝ))

/-- Source: roadmap §0.2.2 ("the element `1 − 2X` squares to `1`"). -/
theorem oneSubTwoX_sq : oneSubTwoX ^ 2 = 1 := by
  exact Prod.ext (show (1 : ℝ) ^ 2 = 1 by norm_num) (show (-1 : ℝ) ^ 2 = 1 by norm_num)

/-- Source: roadmap §0.2.2 ("and has norm `3`"). -/
theorem norm_oneSubTwoX : ‖oneSubTwoX‖ = 3 := by
  rw [norm_def]
  change |(1 : ℝ)| + |(-1 : ℝ) - 1| = 3
  norm_num

/-- Source: roadmap §0.2.2 (power-bounded of norm greater than `1`: submultiplicativity does not
suffice in `PowerBounded.isPowerBounded_iff_norm_le_one`). -/
theorem isPowerBounded_oneSubTwoX : PowerBounded.IsPowerBounded oneSubTwoX := by
  refine PowerBounded.isPowerBounded_of_norm_pow_le (C := 3) fun n ↦ ?_
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [pow_mul, oneSubTwoX_sq, one_pow, norm_def]
    change |(1 : ℝ)| + |(1 : ℝ) - 1| ≤ 3
    norm_num
  · rw [pow_succ, pow_mul, oneSubTwoX_sq, one_pow, one_mul, norm_oneSubTwoX]

end L1Pair
