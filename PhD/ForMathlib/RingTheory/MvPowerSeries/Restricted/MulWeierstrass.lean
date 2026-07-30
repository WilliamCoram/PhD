/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.MulWeierstrassPrep
import PhD.ForMathlib.RingTheory.MvPowerSeries.Restricted.X0Polynomial

/-! # Multivariate Weierstrass division and preparation at Martin generality

[Mar16]'s closing remark of §1.3 made formal: applying the univariate theorems over the
coefficient Tate algebra `Restricted R (Fin.tail c)` and transporting along the splitting
isomorphism `finSuccEquiv` yields multivariate Weierstrass division and preparation over
**any** ultrametric complete normed commutative ring `R`, at **every** polyradius `c`,
for series Martin-distinguished in `X 0` — the coefficient of `X 0 ^ s`, an element of
the tail Tate algebra, is a multiplicative unit.

Over a `NormMulClass` base — in particular over a complete nontrivially normed field —
`IsMulDistinguishedX0` coincides with the project's `IsDistinguishedX0`; the compatibility
corollaries recovering that field-facing form live in
`PhD.BirkovichWP.…MvPowerSeries.Restricted.MulWeierstrassCompat`.

Source: F. Martin, *Overconvergent subanalytic subsets in the framework of Berkovich
spaces*, J. EMS 18 (2016), §1.3, closing remark.
-/

namespace MvPowerSeries.Restricted

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R]
  {n : ℕ} {c : Fin (n + 1) → ℝ} [Fact (∀ i, 0 < c i)]

/-- `f` is **Martin-distinguished in `X 0` of degree `s`**: its image under the splitting
isomorphism — a univariate restricted series over the tail Tate algebra — is
Martin-distinguished (`PowerSeries.IsMulDistinguished`) of degree `s` at parameter
`c 0`.  Source: [Mar16, Definition 1.24] over the coefficient ring of the closing
remark. -/
def IsMulDistinguishedX0 (f : Restricted R c) (s : ℕ) : Prop :=
  PowerSeries.IsMulDistinguished (c 0) (finSuccEquiv R c f).1 s

/-- Multiplicative units transport along the (isometric) inverse of the splitting
isomorphism. -/
lemma isNormMulUnit_finSuccEquiv_symm
    {x : PowerSeries.Restricted (Restricted R (Fin.tail c)) (c 0)}
    (hx : IsNormMulUnit x) : IsNormMulUnit ((finSuccEquiv R c).symm x) := by
  refine ⟨(isUnit_finSuccEquiv_symm_iff x).mpr hx.isUnit, fun a ↦ ?_⟩
  have h : (finSuccEquiv R c).symm x * a
      = (finSuccEquiv R c).symm (x * finSuccEquiv R c a) := by
    rw [map_mul, RingEquiv.symm_apply_apply]
  rw [h, norm_finSuccEquiv_symm, hx.norm_mul, norm_finSuccEquiv_symm,
    norm_finSuccEquiv c a]

/-! ## Division -/

/-- **Multivariate Weierstrass division, existence, at every polyradius over any
ultrametric complete normed commutative ring** ([Mar16, Proposition 1.27 and the closing
remark of §1.3]): for `g` Martin-distinguished in `X 0` of degree `s`, every `f` divides
as `f = g * q + r` with `r` an `X 0`-polynomial of degree `< s`. -/
theorem weierstrassDivision_exists_of_isMulDistinguishedX0 [CompleteSpace R]
    {g : Restricted R c} {s : ℕ} (hg : IsMulDistinguishedX0 g s) (f : Restricted R c) :
    ∃ (q : Restricted R c) (r : Polynomial (Restricted R (Fin.tail c))),
      r.degree < s ∧ f = g * q + Polynomial.toMvRestrictedX0 c r := by
  obtain ⟨q', r', hr', hf'⟩ :=
    PowerSeries.Restricted.weierstrassDivision_exists_of_isMulDistinguished
      (hg : PowerSeries.IsMulDistinguished (c 0) (finSuccEquiv R c g).1 s)
      (finSuccEquiv R c f)
  refine ⟨(finSuccEquiv R c).symm q', r', hr', ?_⟩
  have h := congrArg (finSuccEquiv R c).symm hf'
  rw [map_add, map_mul, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply] at h
  exact h

/-- Uniqueness of the multivariate Weierstrass quotient. -/
theorem weierstrassDivision_q_unique_of_isMulDistinguishedX0
    {g : Restricted R c} {s : ℕ} (hg : IsMulDistinguishedX0 g s) {f : Restricted R c}
    {q₁ q₂ : Restricted R c} {r₁ r₂ : Polynomial (Restricted R (Fin.tail c))}
    (hr₁ : r₁.degree < s) (hf₁ : f = g * q₁ + Polynomial.toMvRestrictedX0 c r₁)
    (hr₂ : r₂.degree < s) (hf₂ : f = g * q₂ + Polynomial.toMvRestrictedX0 c r₂) :
    q₁ = q₂ := by
  have h₁ := congrArg (finSuccEquiv R c) hf₁
  have h₂ := congrArg (finSuccEquiv R c) hf₂
  rw [map_add, map_mul, Polynomial.finSuccEquiv_toMvRestrictedX0] at h₁ h₂
  exact (finSuccEquiv R c).injective
    (PowerSeries.Restricted.weierstrassDivision_q_unique_of_isMulDistinguished
      (hg : PowerSeries.IsMulDistinguished (c 0) (finSuccEquiv R c g).1 s) hr₁ h₁ hr₂ h₂)

/-- Uniqueness of the multivariate Weierstrass remainder. -/
theorem weierstrassDivision_r_unique_of_isMulDistinguishedX0
    {g : Restricted R c} {s : ℕ} (hg : IsMulDistinguishedX0 g s) {f : Restricted R c}
    {q₁ q₂ : Restricted R c} {r₁ r₂ : Polynomial (Restricted R (Fin.tail c))}
    (hr₁ : r₁.degree < s) (hf₁ : f = g * q₁ + Polynomial.toMvRestrictedX0 c r₁)
    (hr₂ : r₂.degree < s) (hf₂ : f = g * q₂ + Polynomial.toMvRestrictedX0 c r₂) :
    r₁ = r₂ := by
  have h₁ := congrArg (finSuccEquiv R c) hf₁
  have h₂ := congrArg (finSuccEquiv R c) hf₂
  rw [map_add, map_mul, Polynomial.finSuccEquiv_toMvRestrictedX0] at h₁ h₂
  exact PowerSeries.Restricted.weierstrassDivision_r_unique_of_isMulDistinguished
    (hg : PowerSeries.IsMulDistinguished (c 0) (finSuccEquiv R c g).1 s) hr₁ h₁ hr₂ h₂

/-! ## Preparation -/

/-- **Multivariate Weierstrass preparation, existence, at every polyradius over any
ultrametric complete normed commutative ring** ([Mar16, Corollary 1.28 and the closing
remark of §1.3]): `g` Martin-distinguished in `X 0` of degree `s` factors as a
multiplicative unit times a monic `X 0`-polynomial of degree `s` and norm `(c 0) ^ s`. -/
theorem weierstrassPreparation_exists_of_isMulDistinguishedX0 [CompleteSpace R]
    [NormOneClass R] {g : Restricted R c} {s : ℕ} (hg : IsMulDistinguishedX0 g s) :
    ∃ (ω : Polynomial (Restricted R (Fin.tail c))) (e : Restricted R c), ω.Monic ∧
      ω.degree = s ∧ ‖Polynomial.toMvRestrictedX0 c ω‖ = (c 0) ^ s ∧ IsNormMulUnit e ∧
      g = e * Polynomial.toMvRestrictedX0 c ω := by
  obtain ⟨ω, e', ωm, ωd, ωn, he', hgeq⟩ :=
    PowerSeries.Restricted.weierstrassPreparation_exists_of_isMulDistinguished
      (hg : PowerSeries.IsMulDistinguished (c 0) (finSuccEquiv R c g).1 s)
  refine ⟨ω, (finSuccEquiv R c).symm e', ωm, ωd, ?_,
    isNormMulUnit_finSuccEquiv_symm he', ?_⟩
  · rw [Polynomial.norm_toMvRestrictedX0]
    exact ωn
  · have h := congrArg (finSuccEquiv R c).symm hgeq
    rw [RingEquiv.symm_apply_apply, map_mul] at h
    exact h

/-- Uniqueness of the distinguished polynomial in multivariate Weierstrass preparation
(only `IsUnit e` is needed, and no completeness). -/
theorem weierstrassPreparation_omega_unique_of_isMulDistinguishedX0
    {g : Restricted R c} {s : ℕ} (hg : IsMulDistinguishedX0 g s)
    {ω₁ ω₂ : Polynomial (Restricted R (Fin.tail c))} {e₁ e₂ : Restricted R c}
    (hm₁ : ω₁.Monic) (hd₁ : ω₁.degree = s) (he₁ : IsUnit e₁)
    (hg₁ : g = e₁ * Polynomial.toMvRestrictedX0 c ω₁)
    (hm₂ : ω₂.Monic) (hd₂ : ω₂.degree = s) (he₂ : IsUnit e₂)
    (hg₂ : g = e₂ * Polynomial.toMvRestrictedX0 c ω₂) :
    ω₁ = ω₂ := by
  have h₁ := congrArg (finSuccEquiv R c) hg₁
  have h₂ := congrArg (finSuccEquiv R c) hg₂
  rw [map_mul, Polynomial.finSuccEquiv_toMvRestrictedX0] at h₁ h₂
  exact PowerSeries.Restricted.weierstrassPreparation_omega_unique_of_isMulDistinguished
    (hg : PowerSeries.IsMulDistinguished (c 0) (finSuccEquiv R c g).1 s)
    hm₁ hd₁ (he₁.map (finSuccEquiv R c)) h₁ hm₂ hd₂ (he₂.map (finSuccEquiv R c)) h₂

/-- Uniqueness of the unit in multivariate Weierstrass preparation. -/
theorem weierstrassPreparation_e_unique_of_isMulDistinguishedX0
    {g : Restricted R c} {s : ℕ} (hg : IsMulDistinguishedX0 g s)
    {ω₁ ω₂ : Polynomial (Restricted R (Fin.tail c))} {e₁ e₂ : Restricted R c}
    (hm₁ : ω₁.Monic) (hd₁ : ω₁.degree = s) (he₁ : IsUnit e₁)
    (hg₁ : g = e₁ * Polynomial.toMvRestrictedX0 c ω₁)
    (hm₂ : ω₂.Monic) (hd₂ : ω₂.degree = s) (he₂ : IsUnit e₂)
    (hg₂ : g = e₂ * Polynomial.toMvRestrictedX0 c ω₂) :
    e₁ = e₂ := by
  have h₁ := congrArg (finSuccEquiv R c) hg₁
  have h₂ := congrArg (finSuccEquiv R c) hg₂
  rw [map_mul, Polynomial.finSuccEquiv_toMvRestrictedX0] at h₁ h₂
  exact (finSuccEquiv R c).injective
    (PowerSeries.Restricted.weierstrassPreparation_e_unique_of_isMulDistinguished
      (hg : PowerSeries.IsMulDistinguished (c 0) (finSuccEquiv R c g).1 s)
      hm₁ hd₁ (he₁.map (finSuccEquiv R c)) h₁ hm₂ hd₂ (he₂.map (finSuccEquiv R c)) h₂)

/-! ## Polynomial corollaries -/

/-- Nested-`∃!` congruence along a pointwise `Iff`; local plumbing for transporting the
univariate polynomial corollaries through the splitting isomorphism. -/
private lemma existsUnique_congr' {α : Sort*} {p q : α → Prop} (h : ∀ a, p a ↔ q a) :
    (∃! a, p a) ↔ ∃! a, q a :=
  ⟨fun ⟨a, ha, hu⟩ ↦ ⟨a, (h a).mp ha, fun b hb ↦ hu b ((h b).mpr hb)⟩,
   fun ⟨a, ha, hu⟩ ↦ ⟨a, (h a).mpr ha, fun b hb ↦ hu b ((h b).mp hb)⟩⟩

/-- **Multivariate Weierstrass division for polynomials at every polyradius**: the
Weierstrass quotient of `X 0`-polynomials by a Martin-distinguished `X 0`-polynomial divisor
is itself an `X 0`-polynomial.  (Completeness-free: Euclidean division over the coefficient
Tate algebra, transported through the splitting isomorphism.) -/
theorem weierstrassDivision_polynomial_of_isMulDistinguishedX0
    {g₀ : Polynomial (Restricted R (Fin.tail c))} {s : ℕ}
    (hg : IsMulDistinguishedX0 (Polynomial.toMvRestrictedX0 c g₀) s) (hgs : g₀.degree ≤ s)
    (f₀ : Polynomial (Restricted R (Fin.tail c))) :
    ∃! q : Polynomial (Restricted R (Fin.tail c)),
    ∃! r : Polynomial (Restricted R (Fin.tail c)), r.degree < s ∧
      Polynomial.toMvRestrictedX0 c f₀ =
        Polynomial.toMvRestrictedX0 c g₀ * Polynomial.toMvRestrictedX0 c q +
          Polynomial.toMvRestrictedX0 c r := by
  have hg' : PowerSeries.IsMulDistinguished (c 0) (Polynomial.toRestricted (c 0) g₀).1 s := by
    have h := hg
    unfold IsMulDistinguishedX0 at h
    rwa [Polynomial.finSuccEquiv_toMvRestrictedX0] at h
  have h := PowerSeries.Restricted.weierstrassDivision_polynomial_of_isMulDistinguished hg' hgs f₀
  refine (existsUnique_congr' fun q ↦ existsUnique_congr' fun r ↦
    and_congr_right fun _ ↦ ?_).mpr h
  constructor
  · intro heq
    have h2 := congrArg (finSuccEquiv R c) heq
    simp only [map_add, map_mul, Polynomial.finSuccEquiv_toMvRestrictedX0] at h2
    exact h2
  · intro heq
    have h2 := congrArg (finSuccEquiv R c).symm heq
    rw [map_add, map_mul] at h2
    exact h2

/-- **Multivariate Weierstrass preparation for polynomials at every polyradius**: if `g` is
an `X 0`-polynomial, the unit `e` of its preparation is itself an `X 0`-polynomial.
(Unit-ness of `e` is in the restricted power series ring, not in the polynomial ring.) -/
theorem weierstrassPreparation_polynomial_of_isMulDistinguishedX0 [CompleteSpace R]
    [NormOneClass R] {g₀ : Polynomial (Restricted R (Fin.tail c))} {s : ℕ}
    (hg : IsMulDistinguishedX0 (Polynomial.toMvRestrictedX0 c g₀) s) :
    ∃! ω : Polynomial (Restricted R (Fin.tail c)),
    ∃! e : Polynomial (Restricted R (Fin.tail c)), ω.Monic ∧ ω.degree = s ∧
      ‖Polynomial.toMvRestrictedX0 c ω‖ = (c 0) ^ s ∧
      IsUnit (Polynomial.toMvRestrictedX0 c e) ∧
      Polynomial.toMvRestrictedX0 c g₀ =
        Polynomial.toMvRestrictedX0 c e * Polynomial.toMvRestrictedX0 c ω := by
  have hg' : PowerSeries.IsMulDistinguished (c 0) (Polynomial.toRestricted (c 0) g₀).1 s := by
    have h := hg
    unfold IsMulDistinguishedX0 at h
    rwa [Polynomial.finSuccEquiv_toMvRestrictedX0] at h
  have h := PowerSeries.Restricted.weierstrassPreparation_polynomial_of_isMulDistinguished hg'
  refine (existsUnique_congr' fun ω ↦ existsUnique_congr' fun e ↦ ?_).mpr h
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
  rw [Polynomial.norm_toMvRestrictedX0]
  refine and_congr_right fun _ ↦ and_congr ?_ ?_
  · exact isUnit_finSuccEquiv_symm_iff (Polynomial.toRestricted (c 0) e)
  · constructor
    · intro heq
      have h2 := congrArg (finSuccEquiv R c) heq
      simp only [map_mul, Polynomial.finSuccEquiv_toMvRestrictedX0] at h2
      exact h2
    · intro heq
      have h2 := congrArg (finSuccEquiv R c).symm heq
      rw [map_mul] at h2
      exact h2

end MvPowerSeries.Restricted
