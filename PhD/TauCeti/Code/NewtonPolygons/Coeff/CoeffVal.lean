/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.RingTheory.Polynomial.GaussNorm
import PhD.TauCeti.Code.RigidAnalyticGeometry.Restricted.PowerSeries.GaussNorm
import PhD.TauCeti.Code.NewtonPolygons.Basic
import PhD.TauCeti.Code.NewtonPolygons.Coeff.NormedAddValuation

/-!
# Coefficient valuations

The **coefficient valuation sequence** of a power series `f` with respect to a normed additive
valuation `v`: `i ↦ e (v (coeff i f))`, pushed into `WithTop ℝ` (roadmap §2.1.1), and the same for a
polynomial. Its value is `⊤` exactly at a vanishing coefficient, the sequence of a polynomial is
finitely supported, and — roadmap §2.1.3 — the sequence of a polynomial is admissible, while the
sequence of a power series is admissible exactly when `f` is bounded at some positive radius,
equivalently restricted at some positive radius; a series with a nonzero coefficient which is
restricted at no positive radius is *vertical* (radius of convergence `0`).

Roadmap: §2.1.1, §2.1.3 (the term dictionary §2.1.2 is in `NormedAddValuation.lean`). Tau Ceti
home: `TauCeti/NumberTheory/NewtonPolygon/CoeffVal.lean`.

## Main definitions

* `PowerSeries.coeffVal v f`, `Polynomial.coeffVal v f` — the coefficient valuation sequences.

## Main results

* `PowerSeries.coeffVal_eq_top_iff`, `Polynomial.finiteSupport_coeffVal_finite`;
* `PowerSeries.isAdmissible_coeffVal_iff_exists_isRestricted` — admissible iff restricted at some
  positive radius; `PowerSeries.IsRestricted.isAdmissible_coeffVal`;
* `Polynomial.isAdmissible_coeffVal`, `Polynomial.hasGaussNorm_coe`.

Restrictedness is the rigid-analytic-geometry chain's `PowerSeries.IsRestricted` (the `σ = Unit`
case of Mathlib's multivariate predicate, with `isRestricted_iff` along `cofinite` and
`isRestricted_iff'` along `atTop`, as the roadmap describes); that chain already provides
`PowerSeries.IsRestricted.hasGaussNorm` and `Polynomial.isRestricted_toPowerSeries`.
-/

open NormedField
open NewtonPolygon (IsAdmissible IsVertical finiteSupport)

variable {K : Type*} [NormedField K] {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] (v : NormedAddValuation K Γ)

namespace PowerSeries

variable (f : PowerSeries K)

/-- The coefficient valuation sequence of a power series: `i ↦ e (v (coeff i f))` in `WithTop ℝ`
(roadmap §2.1.1). -/
noncomputable def coeffVal : ℕ → WithTop ℝ := fun i ↦ v.embedTop (v (coeff i f))

lemma coeffVal_apply (i : ℕ) : coeffVal v f i = v.embedTop (v (coeff i f)) := rfl

variable {f}

/-- The value is `⊤` exactly at a vanishing coefficient. -/
@[simp] lemma coeffVal_eq_top_iff {i : ℕ} : coeffVal v f i = ⊤ ↔ coeff i f = 0 := by sorry

lemma coeffVal_ne_top_iff {i : ℕ} : coeffVal v f i ≠ ⊤ ↔ coeff i f ≠ 0 := by sorry

lemma coeffVal_eq_coe_iff {i : ℕ} {γ : Γ} :
    coeffVal v f i = (v.embed γ : WithTop ℝ) ↔ v (coeff i f) = (γ : WithTop Γ) := by sorry

lemma finiteSupport_coeffVal : finiteSupport (coeffVal v f) = {i | coeff i f ≠ 0} := by sorry

@[simp] lemma coeffVal_zero : coeffVal v (0 : PowerSeries K) = fun _ ↦ ⊤ := by sorry

lemma coeffVal_zero_of_coeff_zero_eq_one (h : coeff 0 f = 1) : coeffVal v f 0 = 0 := by sorry

lemma exists_coeffVal_ne_top (hf : f ≠ 0) : ∃ i, coeffVal v f i ≠ ⊤ := by sorry

/-! ### The term dictionary at the coefficients (roadmap §2.1.2) -/

lemma norm_coeff_mul_rpow_pow_le_one_iff (m : ℝ) (k : ℕ) :
    ‖coeff k f‖ * (v.base ^ m) ^ k ≤ 1 ↔ ((m * k : ℝ) : WithTop ℝ) ≤ coeffVal v f k := by sorry

lemma norm_coeff_mul_rpow_pow_lt_one_iff (m : ℝ) (k : ℕ) :
    ‖coeff k f‖ * (v.base ^ m) ^ k < 1 ↔ ((m * k : ℝ) : WithTop ℝ) < coeffVal v f k := by sorry

lemma norm_coeff_mul_rpow_pow_eq_one_iff (m : ℝ) (k : ℕ) :
    ‖coeff k f‖ * (v.base ^ m) ^ k = 1 ↔ coeffVal v f k = ((m * k : ℝ) : WithTop ℝ) := by sorry

/-! ### Admissibility (roadmap §2.1.3) -/

/-- Boundedness of the Gauss-norm terms at the radius `b ^ m` is a line of slope `m` on or below
every point. -/
theorem hasGaussNorm_rpow_iff_exists_line (m : ℝ) :
    HasGaussNorm norm (v.base ^ m) f ↔
      ∃ y : ℝ, ∀ k : ℕ, ((y + m * k : ℝ) : WithTop ℝ) ≤ coeffVal v f k := by sorry

/-- The coefficient valuation sequence is admissible exactly when `f` is bounded at some positive
radius. -/
theorem isAdmissible_coeffVal_iff_exists_hasGaussNorm :
    IsAdmissible (coeffVal v f) ↔ ∃ c : ℝ, 0 < c ∧ HasGaussNorm norm c f := by sorry

/-- A series bounded at a radius is restricted at every smaller nonnegative radius. -/
theorem isRestricted_of_hasGaussNorm {c c' : ℝ} (hc : 0 ≤ c) (hcc' : c < c')
    (hf : HasGaussNorm norm c' f) : IsRestricted c f := by sorry

/-- **Admissibility is restrictedness at some positive radius** (roadmap §2.1.3). -/
theorem isAdmissible_coeffVal_iff_exists_isRestricted :
    IsAdmissible (coeffVal v f) ↔ ∃ c : ℝ, 0 < c ∧ IsRestricted c f := by sorry

/-- A series restricted at some positive radius has an admissible coefficient valuation sequence. -/
theorem IsRestricted.isAdmissible_coeffVal {c : ℝ} (hc : 0 < c) (hf : IsRestricted c f) :
    IsAdmissible (coeffVal v f) := by sorry

/-- The vertical case: a nonzero series restricted at no positive radius. -/
theorem isVertical_coeffVal_iff :
    IsVertical (coeffVal v f) ↔ f ≠ 0 ∧ ∀ c : ℝ, 0 < c → ¬ IsRestricted c f := by sorry

end PowerSeries

namespace Polynomial

variable (f : Polynomial K)

/-- The coefficient valuation sequence of a polynomial (roadmap §2.1.1). -/
noncomputable def coeffVal : ℕ → WithTop ℝ := fun i ↦ v.embedTop (v (f.coeff i))

lemma coeffVal_apply (i : ℕ) : coeffVal v f i = v.embedTop (v (f.coeff i)) := rfl

variable {f}

@[simp] lemma coeffVal_eq_top_iff {i : ℕ} : coeffVal v f i = ⊤ ↔ f.coeff i = 0 := by sorry

lemma coeffVal_ne_top_iff {i : ℕ} : coeffVal v f i ≠ ⊤ ↔ f.coeff i ≠ 0 := by sorry

lemma coeffVal_eq_coe_iff {i : ℕ} {γ : Γ} :
    coeffVal v f i = (v.embed γ : WithTop ℝ) ↔ v (f.coeff i) = (γ : WithTop Γ) := by sorry

/-- The finiteness set is the support of the polynomial. -/
lemma finiteSupport_coeffVal : finiteSupport (coeffVal v f) = ↑f.support := by sorry

/-- The sequence of a polynomial is finitely supported. -/
lemma finiteSupport_coeffVal_finite : (finiteSupport (coeffVal v f)).Finite := by sorry

/-- The coefficient valuation sequence of a polynomial, viewed as a power series. -/
lemma coeffVal_coe : PowerSeries.coeffVal v (f : PowerSeries K) = coeffVal v f := by sorry

/-- The sequence of a polynomial is admissible (roadmap §2.1.3). -/
theorem isAdmissible_coeffVal : IsAdmissible (coeffVal v f) := by sorry

/-- A polynomial is bounded at every radius. -/
theorem hasGaussNorm_coe (c : ℝ) : PowerSeries.HasGaussNorm norm c (f : PowerSeries K) := by sorry

end Polynomial
