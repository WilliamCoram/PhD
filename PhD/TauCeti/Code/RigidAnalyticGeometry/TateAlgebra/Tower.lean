/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.RigidAnalyticGeometry.Restricted.MulWeierstrass
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Basic

/-!
# The tower of Tate algebras

The Tate algebra in `n + 1` variables is the ring of restricted power series in the variable `X 0`
over the Tate algebra in the remaining `n` variables. This file states that tower in the vocabulary
of `Affinoid.TateAlgebra`: the coefficients `coeffX0 g ν` of a series `g` in `X 0`, the polynomials
`ofPolynomial` in `X 0`, and Weierstrass division and preparation by an `X 0`-distinguished series.

Everything here is a restatement of the restricted-series seam (`Restricted/Iso.lean`,
`Restricted/X0Polynomial.lean`, `Restricted/MulWeierstrass.lean`) at the unit polyradius. The seam
is stated at an arbitrary polyradius `c`, with the remaining variables at the polyradius
`Fin.tail c`; at `c = 1` the tail `Fin.tail 1` is definitionally, but not syntactically, the unit
polyradius. ⚠ Crossing that identification costs nothing when the polyradius is given explicitly
(`(c := 1)`) and can time out when it is left to unification, so it is crossed here, once, and the
rest of the development uses the statements of this file and never mentions `Fin.tail`.

The distinguished variable is `X 0`, the one split off by Mathlib's `MvPowerSeries.finSuccEquiv`;
BGR and Bosch distinguish the last variable `Xₙ`.

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, Layer 0 (the adic-spaces roadmap's
§0.5.3 and §0.5.5; BGR 5.1.1, 5.2.1/1–2, 5.2.2/1; Bosch 1.2/6, 1.2/8, 1.2/9). Tau Ceti home:
`TauCeti/RingTheory/TateAlgebra/Tower.lean`.

## Main definitions

* `Affinoid.TateAlgebra.coeffX0 g ν` — the coefficient of `X 0 ^ ν` in `g`, a series in the
  remaining variables.
* `Affinoid.TateAlgebra.ofPolynomial K n` — polynomials in `X 0` over `Tₙ`, inside `T_{n+1}`.
* `Affinoid.TateAlgebra.ofTail K n` — the inclusion `Tₙ →+* T_{n+1}` on the last `n` variables.

## Main results

* `Affinoid.TateAlgebra.isMulDistinguishedX0_iff` — BGR's Definition 5.2.1/1.
* `Affinoid.TateAlgebra.weierstrassDivision_exists`, `weierstrassDivision_q_unique`,
  `weierstrassDivision_r_unique` — the Weierstrass division theorem (BGR 5.2.1/2).
* `Affinoid.TateAlgebra.weierstrassPreparation_exists`, `weierstrassPreparation_omega_unique`,
  `weierstrassPreparation_e_unique` — the Weierstrass preparation theorem (BGR 5.2.2/1).
-/

open MvPowerSeries MvPowerSeries.Restricted

namespace Affinoid.TateAlgebra

variable (K : Type*) [NormedField K] [IsUltrametricDist K] (n : ℕ)

/-- Polynomials in the variable `X 0` with coefficients in the Tate algebra in the remaining
variables, as elements of the Tate algebra. -/
noncomputable def ofPolynomial : Polynomial (TateAlgebra K n) →+* TateAlgebra K (n + 1) :=
  Polynomial.toMvRestrictedX0 (1 : Fin (n + 1) → ℝ)

/-- The inclusion of the Tate algebra in the last `n` variables: a series in `n` variables as a
series in `n + 1` variables not involving `X 0`. -/
noncomputable def ofTail : TateAlgebra K n →+* TateAlgebra K (n + 1) :=
  (ofPolynomial K n).comp Polynomial.C

variable {K n}

/-- The coefficient of `X 0 ^ ν` in a series of the Tate algebra in `n + 1` variables, a series in
the remaining `n` variables. Source: BGR 5.2.1/1 (the `g_ν` of `g = Σ g_ν Xₙ^ν`). -/
noncomputable def coeffX0 (g : TateAlgebra K (n + 1)) (ν : ℕ) : TateAlgebra K n :=
  PowerSeries.coeff ν (MvPowerSeries.Restricted.finSuccEquiv K (1 : Fin (n + 1) → ℝ) g).1

/-- The coefficients of the coefficient of `X 0 ^ ν`. -/
theorem coeff_coeffX0 (g : TateAlgebra K (n + 1)) (ν : ℕ) (t : Fin n →₀ ℕ) :
    MvPowerSeries.coeff t (coeffX0 g ν).1 = MvPowerSeries.coeff (Finsupp.cons ν t) g.1 := by
  have h := MvPowerSeries.Restricted.coeff_finSuccEquiv (1 : Fin (n + 1) → ℝ) g ν
  exact (congrArg (MvPowerSeries.coeff t) h).trans (MvPowerSeries.coeff_coeff_finSuccEquiv g.1)

/-- The coefficients of a polynomial in `X 0`. -/
theorem coeff_ofPolynomial (p : Polynomial (TateAlgebra K n)) (t : Fin (n + 1) →₀ ℕ) :
    MvPowerSeries.coeff t (ofPolynomial K n p).1 =
      MvPowerSeries.coeff (Finsupp.tail t) (p.coeff (t 0)).1 :=
  Polynomial.coeff_toMvRestrictedX0 (c := (1 : Fin (n + 1) → ℝ)) p t

@[simp]
theorem coeffX0_ofPolynomial (p : Polynomial (TateAlgebra K n)) (ν : ℕ) :
    coeffX0 (ofPolynomial K n p) ν = p.coeff ν := by
  refine Restricted.ext (MvPowerSeries.ext fun t ↦ ?_)
  rw [coeff_coeffX0, coeff_ofPolynomial, Finsupp.tail_cons, Finsupp.cons_zero]

theorem ofPolynomial_injective : Function.Injective (ofPolynomial K n) :=
  Polynomial.toMvRestrictedX0_injective

/-! ### Distinguished series -/

/-- A series is `X 0`-distinguished of order `s` if and only if its `s`-th coefficient is a unit,
has the Gauss norm of the series, and strictly dominates all later coefficients.
Source: BGR 5.2.1/1; Bosch 1.2/6. -/
theorem isMulDistinguishedX0_iff {g : TateAlgebra K (n + 1)} {s : ℕ} :
    IsMulDistinguishedX0 g s ↔
      IsUnit (coeffX0 g s) ∧ ‖coeffX0 g s‖ = ‖g‖ ∧
        ∀ ν, s < ν → ‖coeffX0 g ν‖ < ‖coeffX0 g s‖ := by
  have hn : PowerSeries.gaussNorm norm ((1 : Fin (n + 1) → ℝ) 0)
      (MvPowerSeries.Restricted.finSuccEquiv K (1 : Fin (n + 1) → ℝ) g).1 = ‖g‖ :=
    MvPowerSeries.Restricted.gaussNorm_finSuccEquiv (1 : Fin (n + 1) → ℝ) g
  constructor
  · intro h
    refine ⟨h.isNormMulUnit_coeff.isUnit, ?_, fun ν hν ↦ ?_⟩
    · have h2 := h.gaussNorm_eq
      rw [hn] at h2
      have h3 : ‖g‖ = ‖coeffX0 g s‖ * 1 ^ s := h2
      rw [one_pow, mul_one] at h3
      exact h3.symm
    · have h2 : ‖coeffX0 g ν‖ * 1 ^ ν < ‖coeffX0 g s‖ * 1 ^ s := h.gaussTerm_lt ν hν
      simpa using h2
  · rintro ⟨hu, hnorm, hlt⟩
    refine ⟨hu.isNormMulUnit, ?_, fun ν hν ↦ ?_⟩
    · rw [hn]
      show ‖g‖ = ‖coeffX0 g s‖ * 1 ^ s
      rw [one_pow, mul_one]
      exact hnorm.symm
    · show ‖coeffX0 g ν‖ * 1 ^ ν < ‖coeffX0 g s‖ * 1 ^ s
      simpa using hlt ν hν

/-! ### Weierstrass division -/

/-- **Weierstrass division theorem**, existence: for `g` an `X 0`-distinguished series of order
`s`, every series is `g * q + r` with `r` a polynomial in `X 0` of degree less than `s`.
Source: BGR 5.2.1/2; Bosch 1.2/8. -/
theorem weierstrassDivision_exists [CompleteSpace K] {g : TateAlgebra K (n + 1)} {s : ℕ}
    (hg : IsMulDistinguishedX0 g s) (f : TateAlgebra K (n + 1)) :
    ∃ (q : TateAlgebra K (n + 1)) (r : Polynomial (TateAlgebra K n)),
      r.degree < s ∧ f = g * q + ofPolynomial K n r := by
  obtain ⟨q, r, hr, hf⟩ := weierstrassDivision_exists_of_isMulDistinguishedX0 hg f
  exact ⟨q, r, hr, hf⟩

/-- **Weierstrass division theorem**, uniqueness of the quotient. Source: BGR 5.2.1/2. -/
theorem weierstrassDivision_q_unique {g : TateAlgebra K (n + 1)} {s : ℕ}
    (hg : IsMulDistinguishedX0 g s) {f q₁ q₂ : TateAlgebra K (n + 1)}
    {r₁ r₂ : Polynomial (TateAlgebra K n)}
    (hr₁ : r₁.degree < s) (hf₁ : f = g * q₁ + ofPolynomial K n r₁)
    (hr₂ : r₂.degree < s) (hf₂ : f = g * q₂ + ofPolynomial K n r₂) : q₁ = q₂ :=
  weierstrassDivision_q_unique_of_isMulDistinguishedX0 hg hr₁ hf₁ hr₂ hf₂

/-- **Weierstrass division theorem**, uniqueness of the remainder. Source: BGR 5.2.1/2. -/
theorem weierstrassDivision_r_unique {g : TateAlgebra K (n + 1)} {s : ℕ}
    (hg : IsMulDistinguishedX0 g s) {f q₁ q₂ : TateAlgebra K (n + 1)}
    {r₁ r₂ : Polynomial (TateAlgebra K n)}
    (hr₁ : r₁.degree < s) (hf₁ : f = g * q₁ + ofPolynomial K n r₁)
    (hr₂ : r₂.degree < s) (hf₂ : f = g * q₂ + ofPolynomial K n r₂) : r₁ = r₂ :=
  weierstrassDivision_r_unique_of_isMulDistinguishedX0 hg hr₁ hf₁ hr₂ hf₂

/-! ### Weierstrass preparation -/

/-- **Weierstrass preparation theorem**, existence: an `X 0`-distinguished series of order `s` is a
unit times a monic polynomial in `X 0` of degree `s` and Gauss norm one.
Source: BGR 5.2.2/1; Bosch 1.2/9. -/
theorem weierstrassPreparation_exists [CompleteSpace K] {g : TateAlgebra K (n + 1)} {s : ℕ}
    (hg : IsMulDistinguishedX0 g s) :
    ∃ (ω : Polynomial (TateAlgebra K n)) (e : TateAlgebra K (n + 1)), ω.Monic ∧ ω.degree = s ∧
      ‖ofPolynomial K n ω‖ = 1 ∧ IsUnit e ∧ g = e * ofPolynomial K n ω := by
  obtain ⟨ω, e, hm, hd, hn, he, hge⟩ := weierstrassPreparation_exists_of_isMulDistinguishedX0 hg
  refine ⟨ω, e, hm, hd, ?_, he.isUnit, hge⟩
  have h1 : ((1 : Fin (n + 1) → ℝ) 0) ^ s = 1 := by simp
  exact hn.trans h1

/-- **Weierstrass preparation theorem**, uniqueness of the polynomial. Source: BGR 5.2.2/1. -/
theorem weierstrassPreparation_omega_unique {g : TateAlgebra K (n + 1)} {s : ℕ}
    (hg : IsMulDistinguishedX0 g s) {ω₁ ω₂ : Polynomial (TateAlgebra K n)}
    {e₁ e₂ : TateAlgebra K (n + 1)}
    (hm₁ : ω₁.Monic) (hd₁ : ω₁.degree = s) (he₁ : IsUnit e₁) (hg₁ : g = e₁ * ofPolynomial K n ω₁)
    (hm₂ : ω₂.Monic) (hd₂ : ω₂.degree = s) (he₂ : IsUnit e₂) (hg₂ : g = e₂ * ofPolynomial K n ω₂) :
    ω₁ = ω₂ :=
  weierstrassPreparation_omega_unique_of_isMulDistinguishedX0 hg hm₁ hd₁ he₁ hg₁ hm₂ hd₂ he₂ hg₂

/-- **Weierstrass preparation theorem**, uniqueness of the unit. Source: BGR 5.2.2/1. -/
theorem weierstrassPreparation_e_unique {g : TateAlgebra K (n + 1)} {s : ℕ}
    (hg : IsMulDistinguishedX0 g s) {ω₁ ω₂ : Polynomial (TateAlgebra K n)}
    {e₁ e₂ : TateAlgebra K (n + 1)}
    (hm₁ : ω₁.Monic) (hd₁ : ω₁.degree = s) (he₁ : IsUnit e₁) (hg₁ : g = e₁ * ofPolynomial K n ω₁)
    (hm₂ : ω₂.Monic) (hd₂ : ω₂.degree = s) (he₂ : IsUnit e₂) (hg₂ : g = e₂ * ofPolynomial K n ω₂) :
    e₁ = e₂ :=
  weierstrassPreparation_e_unique_of_isMulDistinguishedX0 hg hm₁ hd₁ he₁ hg₁ hm₂ hd₂ he₂ hg₂

end Affinoid.TateAlgebra
