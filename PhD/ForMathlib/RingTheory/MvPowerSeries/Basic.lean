/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.RingTheory.MvPowerSeries.Basic

/-! # A projection formula and coefficientwise descent for multivariate power series

For an `R`-algebra `S` and a base-ring-linear functional `π : S →ₗ[R] R`, applying `π`
coefficientwise sends a power series in `MvPowerSeries σ S` to one in `MvPowerSeries σ R`.
This pushforward is `MvPowerSeries σ R`-linear: pulling back a product
`map (algebraMap R S) g * h` factors the base-ring part `g` out through `π` (the projection /
Frobenius formula, `MvPowerSeries.coeff_map_mul_retraction`).

Consequently a base-changed additive identity `map f = map g * q + rr` **descends**: applying
`π` coefficientwise recovers `f = g * Q + RR` for any coefficientwise retractions `Q` of `q`
and `RR` of `rr` (`MvPowerSeries.eq_of_map_eq_of_retraction`).  The retractions are supplied
abstractly (by their coefficients) so the caller may present them in whatever concrete form is
convenient — a plain `mk`, or the underlying series of a subtype element.

The univariate specialisation (`σ = Unit`) is `PowerSeries.eq_of_map_eq_of_retraction`,
deduced from these.
-/

namespace MvPowerSeries

variable {R S σ : Type*} [CommSemiring R] [Semiring S] [Algebra R S]

/-- **Projection formula.** For a base-ring-linear functional `π : S →ₗ[R] R` and any
coefficientwise retraction `Q` of `h` (`coeff t Q = π (coeff t h)`), applying `π`
coefficientwise to `map (algebraMap R S) g * h` factors the base-ring part `g` out:
`π (coeff t (map g * h)) = coeff t (g * Q)`. -/
lemma coeff_map_mul_retraction (π : S →ₗ[R] R) (g : MvPowerSeries σ R) (h : MvPowerSeries σ S)
    {Q : MvPowerSeries σ R} (hQ : ∀ t, coeff t Q = π (coeff t h)) (t : σ →₀ ℕ) :
    π (coeff t (map (algebraMap R S) g * h)) = coeff t (g * Q) := by
  classical
  rw [coeff_mul, coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [coeff_map, hQ p.2, ← Algebra.smul_def, map_smul, smul_eq_mul]

/-- **Coefficientwise descent of a base-changed identity.** If
`map f = map g * q + rr` over `S` and `Q`, `RR` are coefficientwise retractions of `q`, `rr`
along a base-ring-linear `π` retracting the structure map (`hπ`), then `f = g * Q + RR`
over `R`. -/
lemma eq_of_map_eq_of_retraction (π : S →ₗ[R] R) (hπ : ∀ a : R, π (algebraMap R S a) = a)
    {f g : MvPowerSeries σ R} {q rr : MvPowerSeries σ S} {Q RR : MvPowerSeries σ R}
    (hQ : ∀ t, coeff t Q = π (coeff t q)) (hRR : ∀ t, coeff t RR = π (coeff t rr))
    (hf : map (algebraMap R S) f = map (algebraMap R S) g * q + rr) :
    f = g * Q + RR := by
  ext t
  have : π (coeff t (map (algebraMap R S) f)) = coeff t (g * Q + RR) := by
    simp only [hf, map_add, coeff_map_mul_retraction π g q hQ t, hRR t]
  rwa [coeff_map, hπ] at this

end MvPowerSeries
