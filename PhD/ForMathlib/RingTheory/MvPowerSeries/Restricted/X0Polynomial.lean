/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.ForMathlib.RingTheory.MvPowerSeries.Restricted.Iso

/-! # The `X 0`-polynomial embedding and the splitting-isomorphism transport dictionary

The transport machinery that the multivariate Weierstrass theory consumes, none of which
mentions any distinguishedness hypothesis:

* `Polynomial.toMvRestrictedX0`: the multivariate restricted series attached to a polynomial
  in `X 0` with coefficients in the Tate algebra of the remaining variables, as a ring
  homomorphism (the shape of the remainder in division and the distinguished factor in
  preparation).
* `MvPowerSeries.Restricted.norm_finSuccEquiv_symm`,
  `MvPowerSeries.Restricted.isUnit_finSuccEquiv_symm_iff`: the inverse splitting isomorphism
  is a Gauss-norm isometry and transports units.
* `Polynomial.norm_toMvRestrictedX0`, `Polynomial.toMvRestrictedX0_injective`,
  `Polynomial.coeff_toMvRestrictedX0`.
-/

namespace MvPowerSeries.Restricted

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {n : ℕ}
  {c : Fin (n + 1) → ℝ} [Fact (∀ i, 0 < c i)]

/-- The inverse of the splitting isomorphism is a Gauss-norm isometry. -/
lemma norm_finSuccEquiv_symm
    (x : PowerSeries.Restricted (Restricted R (Fin.tail c)) (c 0)) :
    ‖(finSuccEquiv R c).symm x‖ = ‖x‖ := by
  have h := norm_finSuccEquiv c ((finSuccEquiv R c).symm x)
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

/-- Units transport along the inverse of the splitting isomorphism. -/
lemma isUnit_finSuccEquiv_symm_iff
    (x : PowerSeries.Restricted (Restricted R (Fin.tail c)) (c 0)) :
    IsUnit ((finSuccEquiv R c).symm x) ↔ IsUnit x := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map (finSuccEquiv R c).symm⟩
  have h2 := h.map (finSuccEquiv R c)
  rwa [RingEquiv.apply_symm_apply] at h2

end MvPowerSeries.Restricted

namespace Polynomial

open MvPowerSeries.Restricted in
/-- The multivariate restricted series attached to a **polynomial in `X 0`** with
coefficients in the Tate algebra of the remaining variables: embed as a univariate
restricted series and pull back through the splitting isomorphism.  This is the shape of
the remainder in multivariate Weierstrass division and of the distinguished factor in
multivariate preparation. -/
noncomputable def toMvRestrictedX0 {R : Type*} [NormedCommRing R] [IsUltrametricDist R]
    {n : ℕ} (c : Fin (n + 1) → ℝ) [Fact (∀ i, 0 < c i)] :
    Polynomial (MvPowerSeries.Restricted R (Fin.tail c)) →+* MvPowerSeries.Restricted R c :=
  ((finSuccEquiv R c).symm : PowerSeries.Restricted (MvPowerSeries.Restricted R
    (Fin.tail c)) (c 0) ≃+* MvPowerSeries.Restricted R c).toRingHom.comp
    (Polynomial.toRestricted (c 0))

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {n : ℕ}
  {c : Fin (n + 1) → ℝ} [Fact (∀ i, 0 < c i)]

open MvPowerSeries MvPowerSeries.Restricted

/-- The splitting isomorphism sends an `X 0`-polynomial to the corresponding univariate
polynomial over the coefficient Tate algebra. -/
@[simp]
lemma finSuccEquiv_toMvRestrictedX0 (ω : Polynomial (Restricted R (Fin.tail c))) :
    finSuccEquiv R c (toMvRestrictedX0 c ω) = Polynomial.toRestricted (c 0) ω :=
  (finSuccEquiv R c).apply_symm_apply _

/-- The norm of an `X 0`-polynomial is the norm of the corresponding univariate polynomial
over the coefficient Tate algebra. -/
lemma norm_toMvRestrictedX0 (ω : Polynomial (Restricted R (Fin.tail c))) :
    ‖toMvRestrictedX0 c ω‖ = ‖Polynomial.toRestricted (c 0) ω‖ :=
  norm_finSuccEquiv_symm (Polynomial.toRestricted (c 0) ω)

lemma toMvRestrictedX0_injective :
    Function.Injective (toMvRestrictedX0 (R := R) c) := fun _ _ h ↦
  Polynomial.toRestricted_injective (c 0) ((finSuccEquiv R c).symm.injective h)

/-- Intrinsic coefficient description of an `X 0`-polynomial: its multivariate coefficient
at an exponent `t` is the `Finsupp.tail t`-coefficient of the coefficient of `ω` in
`X 0`-degree `t 0`. -/
lemma coeff_toMvRestrictedX0 (ω : Polynomial (Restricted R (Fin.tail c)))
    (t : Fin (n + 1) →₀ ℕ) :
    MvPowerSeries.coeff t (toMvRestrictedX0 c ω).1 =
      MvPowerSeries.coeff (Finsupp.tail t) ((ω.coeff (t 0)).1) := by
  have hval : (toMvRestrictedX0 c ω).1 = (MvPowerSeries.finSuccEquiv R n).symm
      (PowerSeries.map (IsRestricted.subring (R := R) (Fin.tail c)).subtype
        (Polynomial.toRestricted (c 0) ω).1) := by
    have h := map_finSuccEquiv c (toMvRestrictedX0 c ω)
    rw [finSuccEquiv_toMvRestrictedX0] at h
    exact (AlgEquiv.eq_symm_apply _).mpr h.symm
  have h2 : PowerSeries.coeff (t 0) (Polynomial.toRestricted (c 0) ω).1 = ω.coeff (t 0) := by
    rw [Polynomial.val_toRestricted, Polynomial.coeff_coe]
  rw [hval, MvPowerSeries.coeff_finSuccEquiv_symm]
  exact congrArg (MvPowerSeries.coeff (Finsupp.tail t))
    ((PowerSeries.coeff_map _ _ _).trans
      (congrArg (fun z : Restricted R (Fin.tail c) ↦
        (IsRestricted.subring (R := R) (Fin.tail c)).subtype z) h2))

end Polynomial
