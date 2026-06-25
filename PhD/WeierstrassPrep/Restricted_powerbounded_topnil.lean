import PhD.WeierstrassPrep.PowerBounded
import PhD.WeierstrassPrep.TopologicallyNilpotent

import PhD.ToPR.MvRestricted
import PhD.ToPR.Restricted
import PhD.ToPR.RestrictedIso
import PhD.ToPR.GaussNorm
import PhD.ToPR.MvGaussNorm

-- I want here the statements that

-- Rᵒ<x> = (R<x>)ᵒ
-- (R<x>)ᵒ = {f | ‖f‖ ≤ 1}

-- top_nil versions of these statements

-- residue ring are polynomials

section toMove

noncomputable instance MvPowerSeries.Restricted.normMulClass {R : Type*} [NormedRing R]
    [IsUltrametricDist R] [NormMulClass R] {σ : Type*} [LinearOrder σ] (c : σ → ℝ)
    [StrongPos c] :
    NormMulClass (MvPowerSeries.Restricted R c) where
  norm_mul a b :=
    (MvRestricted.isAbsoluteValue (R := R) c NormMulClass.norm_mul).abv_mul' a b

end toMove

-- is there a reason this is not in mathlib?
local instance {S : Type*} [NormedCommRing S] [IsUltrametricDist S] : NonarchimedeanRing S where
  is_nonarchimedean := (IsUltrametricDist.nonarchimedeanAddGroup).is_nonarchimedean

-- this needs to maybe exist somewhere in mathlib?
local instance (S : Type*) [Ring S] [TopologicalSpace S] [NonarchimedeanRing S] :
    IsLinearTopology ℤ S := by
  apply IsLinearTopology.mk_of_hasBasis' (R := ℤ)
    (p := fun U : AddSubgroup S => (U : Set S) ∈ nhds 0)
    (s := fun U : AddSubgroup S => U)
  · refine ⟨fun U => ⟨fun hU => ?_,
      fun ⟨_, hN_mem, hN⟩ => Filter.mem_of_superset hN_mem hN⟩⟩
    obtain ⟨V, hV⟩ := NonarchimedeanRing.is_nonarchimedean U hU
    exact ⟨V.toAddSubgroup, V.mem_nhds_zero, hV⟩
  · intro _ n _ hm
    exact zsmul_mem hm n

-- still need to get around this
local instance : StrongPos (fun _ : Unit ↦ (1 : ℝ)) where
  pos := by simp

lemma Restricted.monomial_partial_sums_coeff {R : Type*} [NormedCommRing R] [IsUltrametricDist R]
    (f : PowerSeries.Restricted R 1) (n : ℕ) :
    (∑ i ∈ Finset.range n, Restricted.monomial 1 i (PowerSeries.coeff i f.1) :
      PowerSeries.Restricted R 1).1
    = ∑ i ∈ Finset.range n, PowerSeries.monomial i (PowerSeries.coeff i f.1) := by
  induction n with
    | zero => simp; rfl
    | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      show (_ + _ : PowerSeries R) = _
      rw [← ih]
      rfl

/-- The partial sums of the monomials of a restricted power series `f` converge to `f` in the
Gauss norm: their difference is the tail of `f`, whose Gauss norm tends to `0` because `f` is
restricted. -/
lemma Restricted.monomial_partial_sums_tendsto {R : Type*} [NormedCommRing R] [IsUltrametricDist R]
    (f : PowerSeries.Restricted R 1) : Filter.Tendsto
    (fun n => ∑ i ∈ Finset.range n, Restricted.monomial 1 i (PowerSeries.coeff i f.1))
    Filter.atTop (nhds f) := by

  /-
  have : Summable (fun i ↦ monomial 1 i ((PowerSeries.coeff i) f.1)) := by

    sorry
  have := Summable.tendsto_sum_tsum_nat this
  convert this
  -- perhaps this should be an API?

  I think this should be the way to do it... I need the summable statement
  and the API saying that f is the sum of its monomials definitionally

  -/




  -- maybe theres a more direct filter way to do this...
  -- each of the monomials tendsto
  -- so this is a sum of tendsto


  -- The underlying power series of the `n`-th partial sum.
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hf := (PowerSeries.isRestricted_iff 1 f.1).mp f.2
  simp_rw [one_pow, mul_one, Nat.cofinite_eq_atTop, Metric.tendsto_atTop] at hf
  obtain ⟨N, hN⟩ := hf (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ?_ (show ε / 2 < ε from by grind)
  rw [Restricted.norm_eq, PowerSeries.gaussNorm_eq]
  apply ciSup_le
  intro j
  rw [one_pow, mul_one]
  -- maybe I want API saying that (Restricted + Restricted).1 = Restricted.1 + Restricted.1
  -- then same for mul, sub, etc
  rw [show (∑ i ∈ Finset.range n, Restricted.monomial 1 i (PowerSeries.coeff i f.1) - f :
      PowerSeries.Restricted R 1).1 =
      (∑ i ∈ Finset.range n, Restricted.monomial 1 i (PowerSeries.coeff i f.1) :
        PowerSeries.Restricted R 1).1 - f.1 from by rfl]
  -- decide on need for the API above
  simp_rw [map_sub, Restricted.monomial_partial_sums_coeff, map_sum, PowerSeries.coeff_monomial,
    Finset.sum_ite_eq]
  by_cases hj : j < n
  · simp only [Finset.mem_range.mpr hj, ↓reduceIte, sub_self, norm_zero]
    grind
  · push Not at hj
    rw [if_neg (by simp [Finset.mem_range, not_lt.mpr hj]), zero_sub, norm_neg]
    specialize hN j (by grind)
    simp only [dist_eq_norm, sub_zero, norm_norm] at hN
    grind

namespace Restricted

section PowerBounded

open PowerBounded

section NormedRing

open Topology

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] [NormOneClass R]
  [Filter.NeBot (𝓝[≠] (0 : R))]

local instance : NormMulClass (PowerSeries.Restricted R 1) :=
  MvPowerSeries.Restricted.normMulClass (σ := Unit) (fun _ ↦ 1)

local instance : NormOneClass (PowerSeries.Restricted R 1) := by
  -- to fill in when I make the general API instance
  sorry

-- This should maybe get moved elsewhere... I think I want Restricted/MvRestricted folders
local instance : Filter.NeBot (𝓝[≠] (0 : (PowerSeries.Restricted R 1))) := by
  -- `0` not being isolated is equivalent to `0 ∈ closure {0}ᶜ`.
  rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
  intro ε hε
  -- `0` is not isolated in `R`, so pick a nonzero `r` with `‖r‖ < ε`.
  obtain ⟨r, hr_ne, hr⟩ : ∃ r : R, r ≠ 0 ∧ ‖r‖ < ε := by
    have hR : (0 : R) ∈ closure ({0}ᶜ : Set R) :=
      mem_closure_iff_nhdsWithin_neBot.mpr inferInstance
    obtain ⟨r, hr_mem, hr_dist⟩ := Metric.mem_closure_iff.mp hR ε hε
    rw [dist_comm, dist_zero_right] at hr_dist
    exact ⟨r, hr_mem, hr_dist⟩
  -- The constant series `monomial 1 0 r` witnesses that `0` is not isolated in `Restricted R 1`.
  have hcoe : (Restricted.monomial 1 0 r).1 = PowerSeries.monomial 0 r := rfl

  -- this can probably be simplified when I make the API for the gauss norm of a monomial API

  -- Its Gauss norm is bounded by `‖r‖` (the only nonzero coefficient is the constant term).
  have hub : ‖Restricted.monomial 1 0 r‖ ≤ ‖r‖ := by
    rw [Restricted.norm_eq, hcoe, PowerSeries.gaussNorm_eq]
    refine ciSup_le (fun i => ?_)
    rw [PowerSeries.coeff_monomial, one_pow, mul_one]
    split_ifs with h
    · exact le_refl _
    · simp
  -- It is nonzero: its Gauss norm is at least `‖r‖ > 0`.
  have hlb : ‖r‖ ≤ ‖Restricted.monomial 1 0 r‖ := by
    rw [Restricted.norm_eq, hcoe]
    have h := PowerSeries.le_gaussNorm (norm : R → ℝ) 1 (Restricted.monomial 1 0 r).1
      (Restricted.hasGaussNorm 1 (Restricted.monomial 1 0 r)) 0
    rw [hcoe] at h
    simpa [PowerSeries.coeff_monomial] using h
  have hne : Restricted.monomial 1 0 r ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le (norm_pos_iff.mpr hr_ne) hlb)
  exact ⟨Restricted.monomial 1 0 r, hne,
    by rw [dist_comm, dist_zero_right]; exact lt_of_le_of_lt hub hr⟩

lemma powerBounded_coeffs_of_powerBounded (f : PowerSeries.Restricted R 1) (h : IsPowerBounded f)
    (i : ℕ) : IsPowerBounded (PowerSeries.coeff i f.1) := by
  have : ‖PowerSeries.coeff i f.1‖ ≤ 1 := by
    simpa [Restricted.norm_eq, one_pow, mul_one] using (PowerSeries.le_gaussNorm _ 1 f.1
      (Restricted.hasGaussNorm 1 f) i).trans (IsPowerBounded.norm_le_one_of_neBot h)
  exact IsPowerBounded.isPowerBounded_of_norm_le_one this

lemma bar' (f : PowerSeries.Restricted R 1) (i : ℕ) (h : IsPowerBounded (PowerSeries.coeff i f.1)) :
    IsPowerBounded (Restricted.monomial 1 i (PowerSeries.coeff i f.1)) := by
  refine IsPowerBounded.isPowerBounded_of_norm_le_one ?_
  simp_rw [Restricted.norm_eq]
  have H : PowerSeries.gaussNorm norm 1 (monomial 1 i ((PowerSeries.coeff i) f.1)).1 =
      ‖(PowerSeries.coeff i) f.1‖ := by
    -- this should be extracted as a general lemma
    -- i.e. the gauss norm of a monomial is obtained at the single value
    sorry
  simpa [H] using IsPowerBounded.norm_le_one_of_neBot h

lemma bar (f : PowerSeries.Restricted R 1) (h : ∀ i, IsPowerBounded (PowerSeries.coeff i f.1)) :
      IsPowerBounded f := by
  -- The sequence of partial sums of the first `n` monomials of `f`.
  let s : ℕ → PowerSeries.Restricted R 1 :=
    fun n => ∑ i ∈ Finset.range n, Restricted.monomial 1 i (PowerSeries.coeff i f.1)
  -- Each partial sum is power-bounded: a sum of power-bounded monomials (via `bar'`).
  have hs_pb : ∀ n, IsPowerBounded (s n) := by
    intro n
    induction n with
    | zero =>
      show IsPowerBounded (∑ i ∈ Finset.range 0, _)
      rw [Finset.sum_range_zero]
      exact isPowerBounded_zero
    | succ k ih =>
      show IsPowerBounded (∑ i ∈ Finset.range (k + 1), _)
      rw [Finset.sum_range_succ]
      exact isPowerBounded_add ℤ ih (bar' f k (h k))
  -- Closedness of the power-bounded subring concludes the proof.
  exact (IsPowerBounded.subring_isClosed (R := PowerSeries.Restricted R 1) ℤ).mem_of_tendsto
    (Restricted.monomial_partial_sums_tendsto f) (Filter.Eventually.of_forall hs_pb)

end NormedRing

end PowerBounded

section TopologicallyNilpotent

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R]

local instance : NormMulClass (PowerSeries.Restricted R 1) := by
  exact MvPowerSeries.Restricted.normMulClass (σ := Unit) (fun _ ↦ 1)

lemma topologicallyNilpotent_coeffs_of_topologicallyNilpotent (f : PowerSeries.Restricted R 1)
    (h : IsTopologicallyNilpotent f) (i : ℕ) :
  IsTopologicallyNilpotent (PowerSeries.coeff i f.1) := by
  have : ‖PowerSeries.coeff i f.1‖ < 1 := by
    simpa [Restricted.norm_eq, one_pow, mul_one] using
      (IsTopologicallyNilpotent.norm_lt_one h).trans_le'
      (PowerSeries.le_gaussNorm _ 1 f.1 (Restricted.hasGaussNorm 1 f) i)
  exact IsTopologicallyNilpotent.of_norm_lt_one this

lemma foo' (f : PowerSeries.Restricted R 1) (i : ℕ)
    (h : IsTopologicallyNilpotent (PowerSeries.coeff i f.1)) :
    IsTopologicallyNilpotent (Restricted.monomial 1 i (PowerSeries.coeff i f.1)) := by
  refine IsTopologicallyNilpotent.of_norm_lt_one ?_
  simp_rw [Restricted.norm_eq]
  have H : PowerSeries.gaussNorm norm 1 (monomial 1 i ((PowerSeries.coeff i) f.1)).1 =
      ‖(PowerSeries.coeff i) f.1‖ := by
    -- this should be extracted as a general lemma
    -- i.e. the gauss norm of a monomial is obtained at the single value
    sorry
  simpa [H] using IsTopologicallyNilpotent.norm_lt_one h

lemma foo (f : PowerSeries.Restricted R 1)
    (h : ∀ i, IsTopologicallyNilpotent (PowerSeries.coeff i f.1)) :
    IsTopologicallyNilpotent f := by
  -- Closedness of the topological nilradical (as a `Set (Restricted R 1)`).
  have hclosed := IsTopologicallyNilpotent.topNil_isClosed (R := PowerSeries.Restricted R 1) ℤ
  -- The sequence of partial sums of the first `n` monomials of `f`.
  let s : ℕ → PowerSeries.Restricted R 1 :=
    fun n => ∑ i ∈ Finset.range n, Restricted.monomial 1 i (PowerSeries.coeff i f.1)
  -- Each partial sum is power-bounded: a sum of power-bounded monomials (via `bar'`).
  have hs_pb : ∀ n, IsTopologicallyNilpotent (s n) := by
    intro n
    induction n with
    | zero =>
      show IsTopologicallyNilpotent (∑ i ∈ Finset.range 0, _)
      rw [Finset.sum_range_zero]
      exact IsTopologicallyNilpotent.zero
    | succ k ih =>
      show IsTopologicallyNilpotent (∑ i ∈ Finset.range (k + 1), _)
      rw [Finset.sum_range_succ]
      exact IsTopologicallyNilpotent.add' ℤ ih (foo' f k (h k))
  -- Closedness of the topological nilradical concludes the proof.
  exact hclosed.mem_of_tendsto (Restricted.monomial_partial_sums_tendsto f)
    (Filter.Eventually.of_forall hs_pb)

end TopologicallyNilpotent


-- Note I could potentially push these to isomorphisms / equivalences
-- but I think it should be fine to ignore this
-- and rather just use this for API
