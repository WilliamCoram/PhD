/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.RingTheory.PowerSeries.Basic
import PhD.Main.ForMathlib.RingTheory.MvPowerSeries.Basic

/-! # Coefficientwise descent of a base-changed identity for power series

For an `R`-algebra `S` and a base-ring-linear functional `π : S →ₗ[R] R`, applying `π`
coefficientwise sends a power series in `S⟦X⟧` to one in `R⟦X⟧`.  A base-changed additive
identity `map f = map g * q + rr` then descends to `f = g * Q + RR` for coefficientwise
retractions `Q`, `RR`, because the product term factors the `R⟦X⟧`-part `g` out through `π`
(the projection / Frobenius formula).

This is the univariate (`σ = Unit`) specialisation of
`MvPowerSeries.eq_of_map_eq_of_retraction` (resting on `MvPowerSeries.coeff_map_mul_retraction`);
`PowerSeries.map`, `PowerSeries.coeff` are definitionally the `MvPowerSeries` operations
over `Unit`.
-/

namespace PowerSeries

variable {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]

/-- **Coefficientwise descent of a base-changed identity** (univariate specialisation of
`MvPowerSeries.eq_of_map_eq_of_retraction`).  If `map f = map g * q + rr` over `S` and `Q`,
`RR` are coefficientwise retractions of `q`, `rr` along a base-ring-linear `π` retracting the
structure map (`hπ`), then `f = g * Q + RR` over `R`. -/
lemma eq_of_map_eq_of_retraction (π : S →ₗ[R] R) (hπ : ∀ a : R, π (algebraMap R S a) = a)
    {f g : PowerSeries R} {q rr : PowerSeries S} {Q RR : PowerSeries R}
    (hQ : ∀ n, coeff n Q = π (coeff n q)) (hRR : ∀ n, coeff n RR = π (coeff n rr))
    (hf : map (algebraMap R S) f = map (algebraMap R S) g * q + rr) :
    f = g * Q + RR :=
  MvPowerSeries.eq_of_map_eq_of_retraction π hπ
    (fun t ↦ by simpa [← coeff_def rfl, ← coeff_def rfl] using hQ (t ()))
    (fun t ↦ by simpa [← coeff_def rfl, ← coeff_def rfl] using hRR (t ())) hf

end PowerSeries
