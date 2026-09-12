/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.BirkovichWP.RingTheory.PowerSeries.Restricted.Distinguished

/-! # Rescaling restricted power series

For a unit `u : Rˣ` with `‖u‖ * c' = c`, the substitution `x ↦ ux` — mathlib's
`PowerSeries.rescale`, coefficientwise `aₖ ↦ uᵏ aₖ` — is an isometric ring isomorphism
`Restricted R c ≃+* Restricted R c'`: the `k`-th Gauss term `‖uᵏ aₖ‖ c'ᵏ` at radius `c'`
equals `‖aₖ‖ cᵏ` at radius `c`.  It matches the `IsDistinguished` structures on the nose and
sends polynomials to polynomials (`ω(x) ↦ ω(ux)`).

This is the rung-1 transport of the Weierstrass theory: division and preparation at a radius
`c = ‖u‖` are the radius-`1` theorems conjugated by `rescaleEquiv`.
-/

namespace PowerSeries

section Predicate

variable {R : Type*} [NormedCommRing R] [NormMulClass R] [NormOneClass R] {c c' : ℝ}

/-- The `k`-th Gauss term of `rescale a f` at radius `c₂` is the `k`-th Gauss term of `f` at
radius `c₁ = ‖a‖ * c₂`. -/
lemma norm_coeff_rescale_mul_pow {c₁ c₂ : ℝ} (a : R) (ha : ‖a‖ * c₂ = c₁) (f : PowerSeries R)
    (k : ℕ) : ‖coeff k (rescale a f)‖ * c₂ ^ k = ‖coeff k f‖ * c₁ ^ k := by
  rw [coeff_rescale, norm_mul, norm_pow, ← ha, mul_pow]
  ring

/-- Rescaling by `a` carries series restricted at `c₁` to series restricted at `c₂` whenever
`‖a‖ * c₂ = c₁`: the `k`-th Gauss terms are then equal. -/
lemma isRestricted_rescale {c₁ c₂ : ℝ} (a : R) (ha : ‖a‖ * c₂ = c₁) {f : PowerSeries R}
    (hf : IsRestricted c₁ f) : IsRestricted c₂ (rescale a f) := by
  rw [isRestricted_iff] at hf ⊢
  exact hf.congr fun k ↦ (norm_coeff_rescale_mul_pow a ha f k).symm

/-- Rescaling by `a` carries the Gauss norm at radius `c₂` to the Gauss norm at radius
`c₁ = ‖a‖ * c₂`. -/
lemma gaussNorm_rescale (a : R) (ha : ‖a‖ * c' = c) (f : PowerSeries R) :
    gaussNorm norm c' (rescale a f) = gaussNorm norm c f := by
  rw [gaussNorm_eq, gaussNorm_eq]
  exact iSup_congr (norm_coeff_rescale_mul_pow a ha f)

end Predicate

section NormUnitsInv

variable {R : Type*} [NormedRing R] [NormMulClass R] [NormOneClass R]

/-- The norm of the inverse of a unit is the inverse of its norm. -/
lemma _root_.norm_units_inv (u : Rˣ) : ‖((u⁻¹ : Rˣ) : R)‖ = ‖(u : R)‖⁻¹ :=
  map_units_inv normHom u

end NormUnitsInv

namespace Restricted

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R]
  [NormOneClass R] {c c' : ℝ}

/-- **Rescaling as a ring isomorphism** `Restricted R c ≃+* Restricted R c'` for a unit `u`
with `‖u‖ * c' = c`: the substitution `x ↦ ux` on series, `aₖ ↦ uᵏ aₖ` on coefficients
(mathlib's `PowerSeries.rescale`), with inverse `x ↦ u⁻¹x`. -/
noncomputable def rescaleEquiv (u : Rˣ) (hu : ‖(u : R)‖ * c' = c) :
    Restricted R c ≃+* Restricted R c' where
  toFun f := ⟨rescale (u : R) f.1, isRestricted_rescale (u : R) hu f.2⟩
  invFun g := ⟨rescale ((u⁻¹ : Rˣ) : R) g.1, isRestricted_rescale _ (by
    rw [← hu, ← mul_assoc, ← norm_mul, Units.inv_mul, norm_one, one_mul]) g.2⟩
  left_inv f := Subtype.ext <| by
    change rescale _ (rescale _ f.1) = f.1
    rw [rescale_rescale, Units.mul_inv, rescale_one, RingHom.id_apply]
  right_inv g := Subtype.ext <| by
    change rescale _ (rescale _ g.1) = g.1
    rw [rescale_rescale, Units.inv_mul, rescale_one, RingHom.id_apply]
  map_mul' f g := Subtype.ext (map_mul (rescale (u : R)) f.1 g.1)
  map_add' f g := Subtype.ext (map_add (rescale (u : R)) f.1 g.1)

/-- The underlying power series of a rescaling is `PowerSeries.rescale`. -/
@[simp]
lemma val_rescaleEquiv (u : Rˣ) (hu : ‖(u : R)‖ * c' = c) (f : Restricted R c) :
    (rescaleEquiv u hu f).1 = rescale (u : R) f.1 := rfl

/-- The underlying power series of an inverse rescaling is `PowerSeries.rescale` by `u⁻¹`. -/
@[simp]
lemma val_rescaleEquiv_symm (u : Rˣ) (hu : ‖(u : R)‖ * c' = c) (g : Restricted R c') :
    ((rescaleEquiv u hu).symm g).1 = rescale ((u⁻¹ : Rˣ) : R) g.1 := rfl

/-- Rescaling is a **Gauss-norm isometry**. -/
lemma norm_rescaleEquiv (u : Rˣ) [Fact (0 < c)] [Fact (0 < c')] (hu : ‖(u : R)‖ * c' = c)
    (f : Restricted R c) : ‖rescaleEquiv u hu f‖ = ‖f‖ := by
  rw [norm_def, norm_def, val_rescaleEquiv]
  exact gaussNorm_rescale (u : R) hu f.1

/-- The inverse rescaling is a **Gauss-norm isometry**. -/
lemma norm_rescaleEquiv_symm (u : Rˣ) [Fact (0 < c)] [Fact (0 < c')] (hu : ‖(u : R)‖ * c' = c)
    (g : Restricted R c') : ‖(rescaleEquiv u hu).symm g‖ = ‖g‖ := by
  rw [← norm_rescaleEquiv u hu ((rescaleEquiv u hu).symm g), RingEquiv.apply_symm_apply]

/-- The scaling hypothesis of Weierstrass division — every nonzero norm value is realised by
a unit of `R` — transports along the (isometric) rescaling. -/
lemma hunit_transport (u : Rˣ) [Fact (0 < c)] [Fact (0 < c')] (hu : ‖(u : R)‖ * c' = c)
    (hunit : ∀ f : Restricted R c, f ≠ 0 → ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a) :
    ∀ f : Restricted R c', f ≠ 0 → ∃ a : R, ‖a‖ = ‖f‖⁻¹ ∧ IsUnit a := by
  intro f' hf'
  have hne : (rescaleEquiv u hu).symm f' ≠ 0 := fun h0 ↦ hf' (by
    simpa using congrArg (rescaleEquiv u hu) h0)
  have h := hunit _ hne
  rwa [norm_rescaleEquiv_symm u hu] at h

/-- Rescaling matches the `IsDistinguished` structures at the two radii. -/
lemma isDistinguished_rescaleEquiv_iff (u : Rˣ) (hu : ‖(u : R)‖ * c' = c)
    (f : Restricted R c) (s : ℕ) :
    IsDistinguished norm c' (rescaleEquiv u hu f).1 s ↔ IsDistinguished norm c f.1 s := by
  rw [val_rescaleEquiv]
  have hcoeff := norm_coeff_rescale_mul_pow (u : R) hu f.1
  have hunit : ∀ k, IsUnit (coeff k (rescale (u : R) f.1)) ↔ IsUnit (coeff k f.1) := fun k ↦ by
    rw [coeff_rescale, ← Units.val_pow_eq_pow_val, Units.isUnit_units_mul]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(hunit s).mp h1, ?_, fun t ht ↦ ?_⟩
    · rw [← gaussNorm_rescale (u : R) hu f.1, h2, hcoeff s]
    · rw [← hcoeff t, ← hcoeff s]
      exact h3 t ht
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(hunit s).mpr h1, ?_, fun t ht ↦ ?_⟩
    · rw [gaussNorm_rescale (u : R) hu f.1, h2, hcoeff s]
    · rw [hcoeff t, hcoeff s]
      exact h3 t ht

section Polynomial

variable {A : Type*} [Semiring A]

/-- Composition with `ux` and then `u⁻¹x` is the identity. -/
lemma _root_.Polynomial.comp_C_mul_X_comp_C_inv_mul_X (p : Polynomial A) (u : Aˣ) :
    (p.comp (Polynomial.C (u : A) * Polynomial.X)).comp
      (Polynomial.C ((u⁻¹ : Aˣ) : A) * Polynomial.X) = p := by
  ext k
  rw [Polynomial.comp_C_mul_X_coeff, Polynomial.comp_C_mul_X_coeff, mul_assoc,
    ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow,
    mul_inv_cancel, Units.val_one, mul_one]

/-- Composition with `ax` does not increase the degree bound. -/
lemma _root_.Polynomial.degree_comp_C_mul_X_lt {r : Polynomial A} {s : ℕ} (hr : r.degree < s)
    (a : A) : (r.comp (Polynomial.C a * Polynomial.X)).degree < s := by
  rw [Polynomial.degree_lt_iff_coeff_zero] at hr ⊢
  intro m hm
  rw [Polynomial.comp_C_mul_X_coeff, hr m hm, zero_mul]

/-- Composition with `ux` for a unit `u` preserves the degree. -/
lemma _root_.Polynomial.degree_comp_C_mul_X (p : Polynomial A) (u : Aˣ) :
    (p.comp (Polynomial.C (u : A) * Polynomial.X)).degree = p.degree := by
  have hsupp : (p.comp (Polynomial.C (u : A) * Polynomial.X)).support = p.support := by
    ext k
    simp [Polynomial.mem_support_iff, Polynomial.comp_C_mul_X_coeff,
      ← Units.val_pow_eq_pow_val, Units.mul_left_eq_zero]
  rw [Polynomial.degree, Polynomial.degree, hsupp]

/-- The leading coefficient of `p(ux)` for a unit `u`. -/
lemma _root_.Polynomial.leadingCoeff_comp_C_mul_X (p : Polynomial A) (u : Aˣ) :
    (p.comp (Polynomial.C (u : A) * Polynomial.X)).leadingCoeff
      = p.leadingCoeff * (u : A) ^ p.natDegree := by
  have hnd : (p.comp (Polynomial.C (u : A) * Polynomial.X)).natDegree = p.natDegree := by
    rw [Polynomial.natDegree, Polynomial.natDegree, Polynomial.degree_comp_C_mul_X]
  rw [Polynomial.leadingCoeff, hnd, Polynomial.comp_C_mul_X_coeff]
  rfl

end Polynomial

/-- Rescaling sends polynomials to polynomials: `ω(x) ↦ ω(ux)`. -/
lemma rescaleEquiv_toRestricted (u : Rˣ) (hu : ‖(u : R)‖ * c' = c) (ω : Polynomial R) :
    rescaleEquiv u hu (Polynomial.toRestricted c ω)
      = Polynomial.toRestricted c' (ω.comp (Polynomial.C (u : R) * Polynomial.X)) := by
  refine Subtype.ext ?_
  change rescale (u : R) (ω : PowerSeries R)
    = ((ω.comp (Polynomial.C (u : R) * Polynomial.X) : Polynomial R) : PowerSeries R)
  ext k
  rw [coeff_rescale, Polynomial.coeff_coe, Polynomial.coeff_coe, Polynomial.comp_C_mul_X_coeff]
  exact mul_comm _ _

/-- The inverse rescaling also sends polynomials to polynomials: `r(x) ↦ r(u⁻¹x)`. -/
lemma rescaleEquiv_symm_toRestricted (u : Rˣ) (hu : ‖(u : R)‖ * c' = c) (r : Polynomial R) :
    (rescaleEquiv u hu).symm (Polynomial.toRestricted c' r)
      = Polynomial.toRestricted c
          (r.comp (Polynomial.C ((u⁻¹ : Rˣ) : R) * Polynomial.X)) := by
  rw [RingEquiv.symm_apply_eq, rescaleEquiv_toRestricted]
  congr 1
  simpa using (Polynomial.comp_C_mul_X_comp_C_inv_mul_X r u⁻¹).symm

end Restricted

end PowerSeries
