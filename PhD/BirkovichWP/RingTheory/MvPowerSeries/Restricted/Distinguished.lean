/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.ForMathlib.RingTheory.MvPowerSeries.Restricted.Iso
import PhD.ForMathlib.RingTheory.PowerSeries.Restricted.Distinguished

/-! # Distinguished multivariate restricted power series

A restricted multivariate power series is **distinguished in the variable `X 0` of degree
`s`** when its image under the splitting isomorphism
`MvPowerSeries.Restricted.finSuccEquiv` — a univariate restricted series over the Tate
algebra `T = Restricted R (Fin.tail c)` in the remaining variables — is distinguished of
degree `s` at parameter `c 0`.  This file defines the predicate, the embedding of
`X 0`-polynomials, and the transport dictionary along the splitting isomorphism that the
multivariate Weierstrass theory consumes.

## Main definitions

* `MvPowerSeries.Restricted.IsDistinguishedX0`: distinguished in `X 0` of degree `s`.
* `Polynomial.toMvRestrictedX0`: the multivariate restricted series attached to a polynomial
  in `X 0` with coefficients in the Tate algebra of the remaining variables, as a ring
  homomorphism.

## Main results

* `MvPowerSeries.Restricted.norm_finSuccEquiv_symm`,
  `MvPowerSeries.Restricted.isUnit_finSuccEquiv_symm_iff`: the inverse splitting isomorphism
  is an isometry and transports units.
* `Polynomial.norm_toMvRestrictedX0`, `Polynomial.toMvRestrictedX0_injective`,
  `Polynomial.coeff_toMvRestrictedX0`: norm, injectivity and coefficients of the
  `X 0`-polynomial embedding.
* `MvPowerSeries.Restricted.isDistinguishedX0_toMvRestrictedX0_of_monic`: a monic
  `X 0`-polynomial of degree `s` with `‖ω‖ = (c 0) ^ s` is distinguished in `X 0`.
-/

namespace MvPowerSeries.Restricted

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {n : ℕ}
  {c : Fin (n + 1) → ℝ} [Fact (∀ i, 0 < c i)]

/-- `f` is **distinguished in the variable `X 0` of degree `s`**: its image under the
splitting isomorphism `finSuccEquiv` — a univariate restricted series over the Tate algebra
`Restricted R (Fin.tail c)` of the remaining variables — is distinguished of degree `s` at
parameter `c 0`. -/
def IsDistinguishedX0 (f : Restricted R c) (s : ℕ) : Prop :=
  PowerSeries.IsDistinguished norm (c 0) (finSuccEquiv R c f).1 s

/-- A pulled-back univariate series is distinguished in `X 0` iff it is distinguished at
parameter `c 0`. -/
lemma isDistinguishedX0_finSuccEquiv_symm
    (x : PowerSeries.Restricted (Restricted R (Fin.tail c)) (c 0)) (s : ℕ) :
    IsDistinguishedX0 ((finSuccEquiv R c).symm x) s ↔
      PowerSeries.IsDistinguished norm (c 0) x.1 s := by
  unfold IsDistinguishedX0
  rw [RingEquiv.apply_symm_apply]

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

namespace MvPowerSeries.Restricted

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {n : ℕ}
  {c : Fin (n + 1) → ℝ} [Fact (∀ i, 0 < c i)]

/-- A monic `X 0`-polynomial of degree `s` with `‖ω‖ = (c 0) ^ s` is distinguished in `X 0`
of degree `s`. -/
lemma isDistinguishedX0_toMvRestrictedX0_of_monic [NormOneClass R]
    {ω : Polynomial (Restricted R (Fin.tail c))} {s : ℕ} (ωm : ω.Monic) (ωd : ω.degree = s)
    (ωn : ‖Polynomial.toMvRestrictedX0 c ω‖ = (c 0) ^ s) :
    IsDistinguishedX0 (Polynomial.toMvRestrictedX0 c ω) s :=
  (isDistinguishedX0_finSuccEquiv_symm (Polynomial.toRestricted (c 0) ω) s).mpr
    (PowerSeries.Restricted.isDistinguished_toRestricted_of_monic ωm ωd
      (by rw [← Polynomial.norm_toMvRestrictedX0]; exact ωn))

end MvPowerSeries.Restricted
