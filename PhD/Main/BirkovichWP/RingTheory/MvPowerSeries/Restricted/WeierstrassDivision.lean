/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.BirkovichWP.RingTheory.MvPowerSeries.Restricted.Distinguished
import PhD.Main.BirkovichWP.RingTheory.PowerSeries.Restricted.WeierstrassDivision

/-! # Multivariate Weierstrass division: bounds and uniqueness

The unit-free core of the multivariate Weierstrass theory: division bounds and quotient
uniqueness for series distinguished in `X 0`, together with the discharge of the scaling
hypothesis over the coefficient Tate algebra when every radius is realised in the value
group of the bottom field.  Every proof is transport along the splitting isomorphism
`MvPowerSeries.Restricted.finSuccEquiv` to the corresponding univariate statement over the
Tate algebra `Restricted R (Fin.tail c)` at parameter `c 0`.

## Main results

* `MvPowerSeries.Restricted.norm_q_le_of_eq_mul_add`,
  `MvPowerSeries.Restricted.norm_r_le_of_eq_mul_add`: the division bounds `‖q‖ ≤ ‖g‖⁻¹ ‖f‖`
  and `‖r‖ ≤ ‖f‖` for any division witness — no scaling hypotheses.
* `MvPowerSeries.Restricted.weierstrassDivision_q_unique`: the quotient is unique — no
  scaling hypotheses.
* `MvPowerSeries.Restricted.exists_norm_inv_isUnit`: over a field bottom with every radius
  realised in the value group, the scaling hypothesis of univariate Weierstrass division
  holds over the coefficient Tate algebra (witnessed by constants).
-/

namespace MvPowerSeries.Restricted

section Bounds

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] {n : ℕ}
  {c : Fin (n + 1) → ℝ} [Fact (∀ i, 0 < c i)]

omit [NormMulClass R] in
private lemma finSuccEquiv_division_eq {g f q : Restricted R c}
    {r : Polynomial (Restricted R (Fin.tail c))}
    (hf : f = g * q + Polynomial.toMvRestrictedX0 c r) :
    finSuccEquiv R c f = finSuccEquiv R c g * finSuccEquiv R c q
      + Polynomial.toRestricted (c 0) r := by
  rw [hf, map_add, map_mul, Polynomial.finSuccEquiv_toMvRestrictedX0]

/-- **Division bound for the quotient** (unit-free): for any witness of a multivariate
Weierstrass division by a series distinguished in `X 0`, `‖q‖ ≤ ‖g‖⁻¹ * ‖f‖`. -/
lemma norm_q_le_of_eq_mul_add {g : Restricted R c} {s : ℕ} (hg : IsDistinguishedX0 g s)
    {f q : Restricted R c} {r : Polynomial (Restricted R (Fin.tail c))}
    (hr : r.degree < s) (hf : f = g * q + Polynomial.toMvRestrictedX0 c r) :
    ‖q‖ ≤ ‖g‖⁻¹ * ‖f‖ := by
  simpa only [norm_finSuccEquiv c] using
    PowerSeries.Restricted.norm_q_le_of_eq_mul_add (c 0) hg hr (finSuccEquiv_division_eq hf)

/-- **Division bound for the remainder** (unit-free): for any witness of a multivariate
Weierstrass division by a series distinguished in `X 0`, `‖r‖ ≤ ‖f‖`. -/
lemma norm_r_le_of_eq_mul_add {g : Restricted R c} {s : ℕ} (hg : IsDistinguishedX0 g s)
    {f q : Restricted R c} {r : Polynomial (Restricted R (Fin.tail c))}
    (hr : r.degree < s) (hf : f = g * q + Polynomial.toMvRestrictedX0 c r) :
    ‖Polynomial.toMvRestrictedX0 c r‖ ≤ ‖f‖ := by
  have h := PowerSeries.Restricted.norm_r_le_of_eq_mul_add (c 0) hg hr
    (finSuccEquiv_division_eq hf)
  rw [← Polynomial.norm_toMvRestrictedX0] at h
  simpa only [norm_finSuccEquiv c] using h

/-- **Uniqueness of the quotient** in multivariate Weierstrass division (unit-free). -/
lemma weierstrassDivision_q_unique {g : Restricted R c} {s : ℕ}
    (hg : IsDistinguishedX0 g s) {f : Restricted R c} {q₁ q₂ : Restricted R c}
    {r₁ r₂ : Polynomial (Restricted R (Fin.tail c))}
    (hr₁ : r₁.degree < s) (hf₁ : f = g * q₁ + Polynomial.toMvRestrictedX0 c r₁)
    (hr₂ : r₂.degree < s) (hf₂ : f = g * q₂ + Polynomial.toMvRestrictedX0 c r₂) :
    q₁ = q₂ :=
  (finSuccEquiv R c).injective
    (PowerSeries.Restricted.weierstrassDivision_q_unique (c 0) hg hr₁
      (finSuccEquiv_division_eq hf₁) hr₂ (finSuccEquiv_division_eq hf₂))

/-- **Uniqueness of the remainder** in multivariate Weierstrass division (unit-free).
Transport of `PowerSeries.Restricted.weierstrassDivision_r_unique` along `finSuccEquiv`; the
remainder type is already the univariate one, so no back-transport is needed. -/
lemma weierstrassDivision_r_unique {g : Restricted R c} {s : ℕ}
    (hg : IsDistinguishedX0 g s) {f : Restricted R c} {q₁ q₂ : Restricted R c}
    {r₁ r₂ : Polynomial (Restricted R (Fin.tail c))}
    (hr₁ : r₁.degree < s) (hf₁ : f = g * q₁ + Polynomial.toMvRestrictedX0 c r₁)
    (hr₂ : r₂.degree < s) (hf₂ : f = g * q₂ + Polynomial.toMvRestrictedX0 c r₂) :
    r₁ = r₂ :=
  PowerSeries.Restricted.weierstrassDivision_r_unique (c 0) hg hr₁
    (finSuccEquiv_division_eq hf₁) hr₂ (finSuccEquiv_division_eq hf₂)

end Bounds

section ScalingHypothesis

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {n : ℕ}
  {c : Fin (n + 1) → ℝ} [Fact (∀ i, 0 < c i)]

/-- **The scaling hypothesis over the Tate algebra.**  With every radius realised in the
value group of the bottom field `K`, the Gauss norm of a nonzero univariate restricted
series over the coefficient Tate algebra is attained twice over — once in the `X 0`-index,
once in the remaining exponents — so its inverse is realised by a constant unit. -/
lemma exists_norm_inv_isUnit (hc : ∀ i, ∃ u : Kˣ, ‖(u : K)‖ = c i)
    (F : PowerSeries.Restricted (Restricted K (Fin.tail c)) (c 0)) (hF : F ≠ 0) :
    ∃ a : Restricted K (Fin.tail c), ‖a‖ = ‖F‖⁻¹ ∧ IsUnit a := by
  choose x hx using hc
  obtain ⟨k, hcoeffk, hnormF⟩ := PowerSeries.Restricted.exists_coeff_ne_zero_norm_eq (c 0) F hF
  obtain ⟨t, hlam, hnormT⟩ :=
    exists_coeff_ne_zero_norm_eq (Fin.tail c) (PowerSeries.coeff k F.1) hcoeffk
  have hprod : ‖∏ i ∈ t.support, (x i.succ : K) ^ t i‖
      = t.prod (fun i e ↦ Fin.tail c i ^ e) := by
    simp only [norm_prod, norm_pow, hx, Finsupp.prod, Fin.tail]
  set b := MvPowerSeries.coeff t (PowerSeries.coeff k F.1).1 * (x 0 : K) ^ k
    * ∏ i ∈ t.support, (x i.succ : K) ^ t i with hb
  have hna : ‖b‖ = ‖F‖ := by
    rw [hb, norm_mul, norm_mul, norm_pow, hx 0, hprod, hnormF, hnormT]
    ring
  have ha_ne : b ≠ 0 :=
    mul_ne_zero (mul_ne_zero hlam (pow_ne_zero _ (x 0).ne_zero))
      (Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (x i.succ).ne_zero)
  exact ⟨C (Fin.tail c) b⁻¹, by rw [norm_C, norm_inv, hna],
    (C (Fin.tail c)).isUnit_map (isUnit_iff_ne_zero.mpr (inv_ne_zero ha_ne))⟩

end ScalingHypothesis

end MvPowerSeries.Restricted
