/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.RingTheory.Valuation.Discrete.Basic
import PhD.QMF.FLTstuff.Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Topology.Algebra.Valued.ValuedField
-- PORT: added for `Valued.integer.finite_quotient_maximalIdeal_pow_of_finite_residueField`,
-- which landed in mathlib with the relaxed hypotheses of the FLT copy.
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-! # Topological results for integer-valued rings

This file contains topological results for valuation rings taking values in the
multiplicative integers with zero adjoined. These are useful for cases where there
is a `Valued K ℤᵐ⁰` instance but no canonical base with which to embed this into
`NNReal`.
-/

open Multiplicative WithZero

open scoped Topology

namespace Valued.WithZeroMulInt

variable {K : Type*} [Field K] [hv : Valued K ℤᵐ⁰]

theorem irreducible_valuation_lt_one {ϖ : 𝒪[K]} (h : Irreducible ϖ) : v ϖ.1 < 1 := by
  have := mt (Valuation.integer.integers _).isUnit_iff_valuation_eq_one.2 h.not_isUnit
  exact lt_of_le_of_ne (Valuation.mem_integer_iff _ _ |>.1 ϖ.2) this

theorem irreducible_valuation_le_ofAdd_neg_one {ϖ : 𝒪[K]} (h : Irreducible ϖ) :
    v ϖ.1 ≤ ofAdd (-1 : ℤ) := by
  letI := (lt_ofAdd_iff (show v ϖ.1 ≠ 0 by simp [h.ne_zero])).1 (irreducible_valuation_lt_one h)
  rw [le_ofAdd_iff (show v ϖ.1 ≠ 0 by simp [h.ne_zero])]
  omega

theorem mem_maximalIdeal_pow_valuation [IsDiscreteValuationRing 𝒪[K]]
    {x : 𝒪[K]} {n : ℕ} (hx : x ∈ 𝓂[K] ^ n) {ϖ : 𝒪[K]} (h : Irreducible ϖ) :
    v x.val ≤ v ϖ.1 ^ n := by
  by_cases hx₀ : x = 0
  · simp [hx₀]
  · simp_rw [h.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    let ⟨y, hy⟩ := hx
    simp only [hy, Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, ge_iff_le]
    exact le_trans (mul_le_of_le_one_right' <| (Valuation.mem_integer_iff _ _).1 y.2) le_rfl

-- PORT: the FLT copy of `finite_quotient_maximalIdeal_pow_of_finite_residueField` is skipped:
-- `Valued.integer.finite_quotient_maximalIdeal_pow_of_finite_residueField` landed in mathlib
-- (Mathlib.Topology.Algebra.Valued.LocallyCompact) with the identical relaxed hypotheses.

/-- The ring of integers `𝒪[K]` of a `ℤᵐ⁰`-valued field `K` with finite residue
field has a finite covering by elements of the basis of uniformity of `K`, whenever
`𝒪[K]` is a discrete valuation ring. -/
theorem finite_cover_of_uniformity_basis [IsDiscreteValuationRing 𝒪[K]] (γ : ℤᵐ⁰ˣ)
    (h : Finite 𝓀[K]) :
    ∃ t : Set K, Set.Finite t ∧
      (𝒪[K]).carrier ⊆ ⋃ y ∈ t, { x | (x, y) ∈ { p | v (p.2 - p.1) < γ.val } } := by
  classical
  let ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  let ⟨m, hm⟩ := exists_pow_lt_of_le_exp_neg_one (irreducible_valuation_le_ofAdd_neg_one hϖ) γ
  letI := integer.finite_quotient_maximalIdeal_pow_of_finite_residueField h m
  have h := Fintype.ofFinite (𝒪[K] ⧸ 𝓂[K] ^ m)
  let T := Subtype.val '' (h.elems.image Quotient.out : Set 𝒪[K])
  refine ⟨T, (Set.Finite.image _ (Finset.finite_toSet _)), fun x hx => ?_⟩
  simp only [Set.mem_iUnion]
  let y := (Ideal.Quotient.mk (𝓂[K] ^ m) ⟨x, hx⟩).out
  refine ⟨y, Set.mem_image_of_mem _ <| Finset.mem_image_of_mem Quotient.out (h.complete _),
    lt_of_le_of_lt (mem_maximalIdeal_pow_valuation (Ideal.Quotient.out_sub _ _) hϖ) hm⟩

variable (K)

open Valuation.IsRankOneDiscrete in
/-- The ring of integers `𝒪[K]` of a complete `ℤᵐ⁰`-valued field `K` with finite residue
field is compact, whenever `𝒪[K]` is a discrete valuation ring. -/
theorem integer_compactSpace [CompleteSpace K] [IsDiscreteValuationRing 𝒪[K]]
    [hv.v.IsRankOneDiscrete] (h : Finite 𝓀[K]) (hsurj : Function.Surjective hv.v) :
    CompactSpace 𝒪[K] where
  isCompact_univ := by
    refine isCompact_iff_isCompact_univ.1 <| isCompact_iff_totallyBounded_isComplete.2
      ⟨(hasBasis_uniformity _ _).totallyBounded_iff.2 fun γ _ ↦ ?_, (isClosed_integer K).isComplete⟩
    obtain ⟨t, htf, ht⟩ := finite_cover_of_uniformity_basis
      (Units.mapEquiv (valueGroup₀_equiv_withZeroMulInt v).toMulEquiv γ) h
    refine ⟨t, htf, ht.trans fun x hx ↦ ?_⟩
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hit, hi⟩ := hx
    use i, hit
    rw [← (valueGroup₀_equiv_withZeroMulInt_strictMono _).lt_iff_lt,
      valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective hsurj]
    simpa using hi

end Valued.WithZeroMulInt
