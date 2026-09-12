/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.ForMathlib.Analysis.Normed.Ring.PowerBounded
import PhD.Main.ForMathlib.RingTheory.MvPowerSeries.Restricted.GaussNorm

/-! # Power-bounded and topologically nilpotent restricted power series

This file characterises power-boundedness and topological nilpotency in
`MvPowerSeries.Restricted R c` coefficientwise.  Each direction holds under a sharp one-sided
bound on the radii: coefficients of power-bounded series are power-bounded when `∀ i, 1 ≤ c i`,
and series with power-bounded coefficients are power-bounded when `∀ i, c i ≤ 1`.  The
equivalences hold for the Tate algebra radii, `∀ i, c i = 1`.

Let `R` be a normed commutative ring with ultrametric distance and multiplicative norm.

* `MvPowerSeries.Restricted.isTopologicallyNilpotent_iff_forall_isTopologicallyNilpotent_coeff`:
  a restricted power series is topologically nilpotent if and only if all its coefficients are.

If moreover `‖1‖ = 1` and the origin of `R` is not isolated:

* `MvPowerSeries.Restricted.isPowerBounded_iff_forall_isPowerBounded_coeff`: a restricted power
  series is power-bounded if and only if all its coefficients are.

Both directions of each equivalence are also available as standalone lemmas with their sharp
radius hypotheses, together with the monomial versions `isPowerBounded_monomial` and
`isTopologicallyNilpotent_monomial`.  The forward directions are the coefficient bound
`‖coeff t f.1‖ * ∏ᵢ (c i) ^ (t i) ≤ ‖f‖`, and the reverse directions write `f` as the sum
of its monomials (`hasSum_monomial`) and use closedness of the power-bounded subring,
respectively of the set of topologically nilpotent elements.
-/

open Filter PowerBounded
open scoped Topology

namespace MvPowerSeries.Restricted

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] {σ : Type*}
  (c : σ → ℝ) [hc : Fact (∀ i, 0 < c i)]

section PowerBounded

variable [NormOneClass R] [NeBot (𝓝[≠] (0 : R))]

/-- If all radii are at least `1`, the coefficients of a power-bounded restricted power series
are power-bounded. -/
theorem isPowerBounded_coeff (h1 : ∀ i, 1 ≤ c i) {f : Restricted R c} (hf : IsPowerBounded f)
    (t : σ →₀ ℕ) : IsPowerBounded (coeff t f.1) :=
  isPowerBounded_of_norm_le_one <|
    (le_mul_of_one_le_right (norm_nonneg _)
      (Finset.one_le_prod fun i _ ↦ one_le_pow₀ (h1 i))).trans
      ((le_gaussNorm norm c f.1 (hasGaussNorm c f) t).trans hf.norm_le_one_of_neBot)

/-- If all radii are at most `1`, a monomial with power-bounded coefficient is power-bounded in
`Restricted R c`. -/
theorem isPowerBounded_monomial (h2 : ∀ i, c i ≤ 1) {a : R} (ha : IsPowerBounded a)
    (t : σ →₀ ℕ) : IsPowerBounded (monomial c t a) :=
  isPowerBounded_of_norm_le_one <| by
    rw [norm_monomial]
    exact mul_le_one₀ ha.norm_le_one_of_neBot
      (Finset.prod_nonneg fun i _ ↦ pow_nonneg (hc.out i).le _)
      (Finset.prod_le_one (fun i _ ↦ pow_nonneg (hc.out i).le _)
        (fun i _ ↦ pow_le_one₀ (hc.out i).le (h2 i)))

/-- If all radii are at most `1`, a restricted power series with power-bounded coefficients is
power-bounded: it is the sum of its monomials, and the power-bounded subring is closed. -/
theorem isPowerBounded_of_forall_isPowerBounded_coeff (h2 : ∀ i, c i ≤ 1) {f : Restricted R c}
    (h : ∀ t, IsPowerBounded (coeff t f.1)) : IsPowerBounded f := by
  refine (isClosed_subring (R := Restricted R c) ℤ).mem_of_tendsto (hasSum_monomial c f)
    (.of_forall fun s ↦ ?_)
  exact Subring.sum_mem _ fun t _ ↦ isPowerBounded_monomial c h2 (h t) t

/-- For the Tate algebra radii `c = 1`, a restricted power series is power-bounded if and only
if all its coefficients are. -/
theorem isPowerBounded_iff_forall_isPowerBounded_coeff (h : ∀ i, c i = 1)
    {f : Restricted R c} : IsPowerBounded f ↔ ∀ t, IsPowerBounded (coeff t f.1) :=
  ⟨fun hf t ↦ isPowerBounded_coeff c (fun i ↦ (h i).ge) hf t,
    isPowerBounded_of_forall_isPowerBounded_coeff c fun i ↦ (h i).le⟩

end PowerBounded

section TopologicallyNilpotent

/-- If all radii are at least `1`, the coefficients of a topologically nilpotent restricted
power series are topologically nilpotent. -/
theorem isTopologicallyNilpotent_coeff (h1 : ∀ i, 1 ≤ c i) {f : Restricted R c}
    (hf : IsTopologicallyNilpotent f) (t : σ →₀ ℕ) :
    IsTopologicallyNilpotent (coeff t f.1) :=
  .of_norm_lt_one <|
    (le_mul_of_one_le_right (norm_nonneg _)
      (Finset.one_le_prod fun i _ ↦ one_le_pow₀ (h1 i))).trans_lt
      ((le_gaussNorm norm c f.1 (hasGaussNorm c f) t).trans_lt hf.norm_lt_one)

/-- If all radii are at most `1`, a monomial with topologically nilpotent coefficient is
topologically nilpotent in `Restricted R c`. -/
theorem isTopologicallyNilpotent_monomial (h2 : ∀ i, c i ≤ 1) {a : R}
    (ha : IsTopologicallyNilpotent a) (t : σ →₀ ℕ) :
    IsTopologicallyNilpotent (monomial c t a) :=
  .of_norm_lt_one <| by
    rw [norm_monomial]
    exact (mul_le_of_le_one_right (norm_nonneg _)
      (Finset.prod_le_one (fun i _ ↦ pow_nonneg (hc.out i).le _)
        (fun i _ ↦ pow_le_one₀ (hc.out i).le (h2 i)))).trans_lt ha.norm_lt_one

/-- If all radii are at most `1`, a restricted power series with topologically nilpotent
coefficients is topologically nilpotent: it is the sum of its monomials, and the set of
topologically nilpotent elements is closed. -/
theorem isTopologicallyNilpotent_of_forall_isTopologicallyNilpotent_coeff (h2 : ∀ i, c i ≤ 1)
    {f : Restricted R c} (h : ∀ t, IsTopologicallyNilpotent (coeff t f.1)) :
    IsTopologicallyNilpotent f := by
  refine (isClosed_setOf_isTopologicallyNilpotent (R := Restricted R c) ℤ).mem_of_tendsto
    (hasSum_monomial c f) (.of_forall fun s ↦ ?_)
  exact Finset.sum_induction _ _ (fun a b ha hb ↦ IsTopologicallyNilpotent.add' ℤ ha hb)
    IsTopologicallyNilpotent.zero fun t _ ↦ isTopologicallyNilpotent_monomial c h2 (h t) t

/-- For the Tate algebra radii `c = 1`, a restricted power series is topologically nilpotent if
and only if all its coefficients are. -/
theorem isTopologicallyNilpotent_iff_forall_isTopologicallyNilpotent_coeff (h : ∀ i, c i = 1)
    {f : Restricted R c} :
    IsTopologicallyNilpotent f ↔ ∀ t, IsTopologicallyNilpotent (coeff t f.1) :=
  ⟨fun hf t ↦ isTopologicallyNilpotent_coeff c (fun i ↦ (h i).ge) hf t,
    isTopologicallyNilpotent_of_forall_isTopologicallyNilpotent_coeff c fun i ↦ (h i).le⟩

end TopologicallyNilpotent

end MvPowerSeries.Restricted
