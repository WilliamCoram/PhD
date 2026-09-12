/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.ForMathlib.RingTheory.PowerSeries.Restricted.GaussNorm

/-! # The division set of a restricted power series

Hypothesis-light primitives shared by every flavour of Weierstrass division: the set
`divisionSet g s = {g * q + r : deg r < s}` of series divisible by `g` with polynomial
remainder of degree `< s`, packaged as an additive subgroup, together with the two
continuity/closedness facts used to prove it closed.

None of these mention any distinguishedness hypothesis; they are consumed both by the
canonical (`IsMulDistinguished`) Weierstrass development and by the legacy
(`IsDistinguished`) one.
-/

open Filter
open scoped Topology

namespace PowerSeries.Restricted

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- Coefficient extraction is continuous on restricted power series. -/
lemma coeff_continuous (c : ℝ) [Fact (0 < c)] (v : ℕ) :
    Continuous fun f : Restricted R c ↦ coeff v f.1 := by
  have hcv : (0 : ℝ) < c ^ v := pow_pos Fact.out v
  refine Metric.continuous_iff.mpr fun f ε hε ↦ ⟨ε * c ^ v, mul_pos hε hcv, fun g hg ↦ ?_⟩
  rw [dist_eq_norm, ← LinearMap.map_sub (PowerSeries.coeff v) g.1 f.1]
  have h1 : ‖coeff v (g.1 - f.1)‖ * c ^ v ≤ ‖g - f‖ := norm_coeff_mul_pow_le c (g - f) v
  exact lt_of_mul_lt_mul_right (h1.trans_lt (by rwa [← dist_eq_norm])) hcv.le

/-- The set of restricted power series whose coefficients from degree `s` on all vanish is
closed. -/
lemma isClosed_setOf_coeff_eq_zero (c : ℝ) [Fact (0 < c)] (s : ℕ) :
    IsClosed {f : Restricted R c | ∀ v, s ≤ v → coeff v f.1 = 0} := by
  refine IsSeqClosed.isClosed fun f_seq f hf_mem hf_lim v hv ↦ ?_
  have : Tendsto (fun n ↦ coeff v (f_seq n).1) atTop (𝓝 (coeff v f.1)) :=
    ((coeff_continuous c v).tendsto _).comp hf_lim
  simp_all

variable {c : ℝ}

/-- The set of elements divisible by `g` with polynomial remainder of degree `< s`. -/
abbrev divisionSet (g : Restricted R c) (s : ℕ) : Set (Restricted R c) :=
  {f | ∃ q, ∃ r : Polynomial R, r.degree < s ∧ f = g * q + Polynomial.toRestricted c r}

/-- `divisionSet g s` as an additive subgroup. -/
def divisionAddSubgroup (g : Restricted R c) (s : ℕ) : AddSubgroup (Restricted R c) where
  carrier := divisionSet g s
  zero_mem' := ⟨0, 0, by simp, by simp⟩
  add_mem' := by
    rintro _ _ ⟨qa, ra, hra, rfl⟩ ⟨qb, rb, hrb, rfl⟩
    refine ⟨qa + qb, ra + rb, (Polynomial.degree_add_le _ _).trans_lt (max_lt hra hrb), ?_⟩
    rw [map_add, mul_add]
    abel
  neg_mem' := by
    rintro _ ⟨q, r, hr, rfl⟩
    exact ⟨-q, -r, by rwa [Polynomial.degree_neg], by rw [map_neg, mul_neg]; abel⟩

end PowerSeries.Restricted
