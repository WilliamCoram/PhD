/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Polynomial.RationalRoot
import PhD.TauCeti.Code.RigidAnalyticGeometry.Rueckert
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Chart
import PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Finiteness

/-!
# Rückert's applications to the Tate algebra

The Tate algebra `T_{n+1}` is a Rückert overring of `Tₙ` for the family of Weierstrass polynomials
in `X 0`: the three axioms are BGR 5.2.3/2, BGR 5.2.3/3 and the distinguished charts together with
Weierstrass preparation. By induction on the number of variables `Tₙ` is noetherian, factorial,
hence normal, a Jacobson ring, and of Krull dimension `n`.

Roadmap: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, §0.3.2–0.3.4 (BGR 5.2.6/1–3,
6.1.2 (Remark); Bosch 1.2/13–15). Tau Ceti home: `TauCeti/RingTheory/TateAlgebra/Rueckert.lean`.

## Main results

* `Affinoid.TateAlgebra.isRueckert_ofPolynomial` — `T_{n+1}` is Rückert over `Tₙ`.
* The instances `IsNoetherianRing`, `UniqueFactorizationMonoid` and `IsJacobsonRing` on
  `TateAlgebra K n` (BGR 5.2.6/1 and 5.2.6/3), whence `IsIntegrallyClosed` (BGR 5.2.6/2).
* `Affinoid.TateAlgebra.ringKrullDim_eq` — the Krull dimension of `Tₙ` is `n`.
-/

open MvPowerSeries MvPowerSeries.Restricted

namespace Affinoid.TateAlgebra

/-- The Tate algebra in `n + 1` variables is Rückert over the Tate algebra in `n` variables, for
the family of Weierstrass polynomials in `X 0`. Source: BGR 5.2.5 ("According to the results of
(5.2.2), (5.2.3) and (5.2.4), the algebra `Tₙ` is Rückert over `T_{n−1}`"), 5.2.6. -/
theorem isRueckert_ofPolynomial (K : Type*) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (n : ℕ) :
    IsRueckert (ofPolynomial K n) {ω | IsWeierstrassPolynomial K n ω} := by
  refine ⟨ofPolynomial_injective, fun _ hω ↦ hω.monic,
    fun _ _ hp hq h ↦ IsWeierstrassPolynomial.of_mul hp hq h,
    fun _ hω ↦ IsWeierstrassPolynomial.bijective_quotientMap hω, fun f hf ↦ ?_⟩
  obtain ⟨e, s, hs⟩ := exists_shear_isMulDistinguishedX0 hf
  obtain ⟨ω, u, hω, -, hu⟩ := exists_isWeierstrassPolynomial_of_isMulDistinguishedX0 hs
  refine ⟨(shear K n e).toRingEquiv, u⁻¹, ω, hω, ?_⟩
  change ↑u⁻¹ * shear K n e f = ofPolynomial K n ω
  rw [hu, Units.inv_mul_cancel_left]

/-- **The Tate algebra is noetherian.** Source: BGR 5.2.6/1; Bosch 1.2/13. -/
instance instIsNoetherianRing (K : Type*) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (n : ℕ) : IsNoetherianRing (TateAlgebra K n) := by
  induction n with
  | zero => exact isNoetherianRing_of_ringEquiv K (Restricted.isEmptyEquiv K (1 : Fin 0 → ℝ)).symm
  | succ n ih => exact (isRueckert_ofPolynomial K n).isNoetherianRing

/-- **The Tate algebra is factorial.** Source: BGR 5.2.6/1; Bosch 1.2/14. -/
instance instUniqueFactorizationMonoid (K : Type*) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (n : ℕ) : UniqueFactorizationMonoid (TateAlgebra K n) := by
  induction n with
  | zero =>
    exact (Restricted.isEmptyEquiv K (1 : Fin 0 → ℝ)).toMulEquiv.symm.uniqueFactorizationMonoid
      inferInstance
  | succ n ih => exact (isRueckert_ofPolynomial K n).uniqueFactorizationMonoid

/-- The Tate algebra is normal. Source: BGR 5.2.6/2; Bosch 1.2/14. -/
example (K : Type*) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (n : ℕ) :
    IsIntegrallyClosed (TateAlgebra K n) := inferInstance

/-- **The Tate algebra is a Jacobson ring.** Source: BGR 5.2.6/3; Bosch 1.2/15. -/
instance instIsJacobsonRing (K : Type*) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (n : ℕ) : IsJacobsonRing (TateAlgebra K n) := by
  induction n with
  | zero =>
    exact isJacobsonRing_of_surjective ⟨((Restricted.isEmptyEquiv K (1 : Fin 0 → ℝ)).symm :
      K →+* TateAlgebra K 0), (Restricted.isEmptyEquiv K (1 : Fin 0 → ℝ)).symm.surjective⟩
  | succ n ih => exact (isRueckert_ofPolynomial K n).isJacobsonRing jacobson_bot

/-- **The Krull dimension of the Tate algebra `Tₙ` is `n`.** Source: BGR 6.1.2 (Remark);
Bosch 1.2/10. -/
theorem ringKrullDim_eq (K : Type*) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (n : ℕ) : ringKrullDim (TateAlgebra K n) = n := by
  induction n with
  | zero =>
    rw [ringKrullDim_eq_of_ringEquiv (Restricted.isEmptyEquiv K (1 : Fin 0 → ℝ)),
      ringKrullDim_eq_zero_of_field, Nat.cast_zero]
  | succ n ih =>
    rw [(isRueckert_ofPolynomial K n).ringKrullDim_eq
      (by simpa using isWeierstrassPolynomial_X_pow (K := K) (n := n) 1), ih, Nat.cast_succ]

end Affinoid.TateAlgebra
