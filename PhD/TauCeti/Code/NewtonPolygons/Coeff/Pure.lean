/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.NewtonPolygons.Coeff.GaussNorm

/-!
# Pure series and first breaks

`PowerSeries.IsPure v f m` and `Polynomial.IsPure v f m` say the polygon of `f` is pure of slope `m`
(Layer 0's `NewtonPolygon.IsPure`): a single segment, or a single ray, of slope `m`. For a polynomial
with `coeff 0 f ≠ 0` this is the Gauss-norm condition of [Gou20, Problem 341]: every term at the
radius `b ^ m` is at most the constant term's and the leading term's equals it; for a series with
infinitely many nonzero coefficients the second clause becomes unboundedness at every larger radius
(roadmap §2.4.1). `HasFirstBreak v f m l` says the polygon has first break of slope `m` and length
`l`; the line bounds it gives are those of [Gou20, §7.4]: `e (v aₖ) ≥ e (v a₀) + m k` for all `k`,
equality at the break index, and strict inequality *beyond* it (roadmap §2.4.2, corrected — interior
points may be collinear; see the board's plan).

Roadmap: §2.4.1–§2.4.2. Tau Ceti home: `TauCeti/NumberTheory/NewtonPolygon/Pure.lean`.

## Main definitions

* `PowerSeries.IsPure v f m`, `PowerSeries.HasFirstBreak v f m l`, and the polynomial versions.

## Main results

* `Polynomial.isPure_iff`, `Polynomial.isPure_iff_gaussNorm`, `Polynomial.isPure_of_bounds`;
* `PowerSeries.isPure_iff_of_infinite`;
* `PowerSeries.HasFirstBreak.le_coeffVal`, `coeffVal_eq`, `lt_coeffVal` — the line bounds;
* `PowerSeries.HasFirstBreak.gaussNorm_rpow_eq` — the Gauss norm at the first slope.
-/

open NormedField
open NewtonPolygon (IsAdmissible IsConvexSeq unitSlope IsVertex SlopesUnbounded faceRight)

variable {K : Type*} [NormedField K] {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] (v : NormedAddValuation K Γ)

namespace PowerSeries

variable (f : PowerSeries K) (m : ℝ)

/-- **A pure series**: the polygon of `f` is pure of slope `m` (roadmap §2.4.1). -/
def IsPure : Prop := NewtonPolygon.IsPure (newtonPolygon v f) m

/-- **The first break**: the polygon of `f` has first break of slope `m` and length `l` (roadmap
§2.4.2). -/
def HasFirstBreak (l : ℕ) : Prop := NewtonPolygon.HasFirstBreak (newtonPolygon v f) m l

variable {f m}

/-! ### Purity (roadmap §2.4.1) -/

/-- A pure series of slope `m` has all its points on or above the line of slope `m` through the first
point: its coefficients are controlled by the line. -/
theorem IsPure.le_coeffVal (hf : IsAdmissible (coeffVal v f)) (h0 : coeff 0 f ≠ 0)
    (hp : IsPure v f m) (k : ℕ) :
    coeffVal v f 0 + ((m * k : ℝ) : WithTop ℝ) ≤ coeffVal v f k := by sorry

/-- Every Gauss-norm term of a pure series at the radius `b ^ m` is at most the constant term's. -/
theorem IsPure.norm_coeff_mul_rpow_pow_le (hf : IsAdmissible (coeffVal v f)) (h0 : coeff 0 f ≠ 0)
    (hp : IsPure v f m) (k : ℕ) : ‖coeff k f‖ * (v.base ^ m) ^ k ≤ ‖coeff 0 f‖ := by sorry

/-- The Gauss norm of a pure series at the radius `b ^ m` is the norm of its constant term. -/
theorem IsPure.gaussNorm_rpow_eq (hf : IsAdmissible (coeffVal v f)) (h0 : coeff 0 f ≠ 0)
    (hp : IsPure v f m) : gaussNorm norm (v.base ^ m) f = ‖coeff 0 f‖ := by sorry

/-- **Purity of a genuine series, in Gauss-norm terms**: every term at `b ^ m` is dominated by the
constant one, and the series is unbounded at every larger radius. -/
theorem isPure_iff_of_infinite (hf : IsAdmissible (coeffVal v f)) (h0 : coeff 0 f ≠ 0)
    (hinf : {k | coeff k f ≠ 0}.Infinite) :
    IsPure v f m ↔ (∀ k, ‖coeff k f‖ * (v.base ^ m) ^ k ≤ ‖coeff 0 f‖) ∧
      ∀ c : ℝ, v.base ^ m < c → ¬ HasGaussNorm norm c f := by sorry

/-! ### The first break (roadmap §2.4.2) -/

/-- **The line bound**: every point lies on or above the line of slope `m` through the first point. -/
theorem HasFirstBreak.le_coeffVal (hf : IsAdmissible (coeffVal v f)) (h0 : coeff 0 f ≠ 0) {l : ℕ}
    (hb : HasFirstBreak v f m l) (k : ℕ) :
    coeffVal v f 0 + ((m * k : ℝ) : WithTop ℝ) ≤ coeffVal v f k := by sorry

/-- **Equality at the break index.** -/
theorem HasFirstBreak.coeffVal_eq (hf : IsAdmissible (coeffVal v f)) (h0 : coeff 0 f ≠ 0) {l : ℕ}
    (hb : HasFirstBreak v f m l) : coeffVal v f l = coeffVal v f 0 + ((m * l : ℝ) : WithTop ℝ) := by
  sorry

/-- **Strict inequality beyond the break index** ([Gou20, §7.4]: "the subsequent points are really
above the line"). -/
theorem HasFirstBreak.lt_coeffVal (hf : IsAdmissible (coeffVal v f)) (h0 : coeff 0 f ≠ 0) {l : ℕ}
    (hb : HasFirstBreak v f m l) {k : ℕ} (hk : l < k) :
    coeffVal v f 0 + ((m * k : ℝ) : WithTop ℝ) < coeffVal v f k := by sorry

theorem HasFirstBreak.coeff_ne_zero (hf : IsAdmissible (coeffVal v f)) (h0 : coeff 0 f ≠ 0) {l : ℕ}
    (hb : HasFirstBreak v f m l) : coeff l f ≠ 0 := by sorry

/-- The Gauss-norm reading of the line bound: `‖aₖ‖ cᵏ ≤ ‖a₀‖` at `c = b ^ m`. -/
theorem HasFirstBreak.norm_coeff_mul_rpow_pow_le (hf : IsAdmissible (coeffVal v f))
    (h0 : coeff 0 f ≠ 0) {l : ℕ} (hb : HasFirstBreak v f m l) (k : ℕ) :
    ‖coeff k f‖ * (v.base ^ m) ^ k ≤ ‖coeff 0 f‖ := by sorry

/-- The Gauss-norm reading of the equality at the break: `‖aₗ‖ cˡ = ‖a₀‖`. -/
theorem HasFirstBreak.norm_coeff_mul_rpow_pow_eq (hf : IsAdmissible (coeffVal v f))
    (h0 : coeff 0 f ≠ 0) {l : ℕ} (hb : HasFirstBreak v f m l) :
    ‖coeff l f‖ * (v.base ^ m) ^ l = ‖coeff 0 f‖ := by sorry

/-- The Gauss-norm reading of the strict inequality beyond the break: `‖aₖ‖ cᵏ < ‖a₀‖` for `k > l`. -/
theorem HasFirstBreak.norm_coeff_mul_rpow_pow_lt (hf : IsAdmissible (coeffVal v f))
    (h0 : coeff 0 f ≠ 0) {l : ℕ} (hb : HasFirstBreak v f m l) {k : ℕ} (hk : l < k) :
    ‖coeff k f‖ * (v.base ^ m) ^ k < ‖coeff 0 f‖ := by sorry

/-- The Gauss norm at the radius of the first slope is the norm of the constant term. -/
theorem HasFirstBreak.gaussNorm_rpow_eq (hf : IsAdmissible (coeffVal v f)) (h0 : coeff 0 f ≠ 0)
    {l : ℕ} (hb : HasFirstBreak v f m l) : gaussNorm norm (v.base ^ m) f = ‖coeff 0 f‖ := by sorry

end PowerSeries

namespace Polynomial

variable (f : Polynomial K) (m : ℝ)

/-- **A pure polynomial**: the polygon of `f` is pure of slope `m` ([Gou20, Definition 7.4.1]). -/
def IsPure : Prop := NewtonPolygon.IsPure (newtonPolygon v f) m

/-- **The first break** of a polynomial: slope `m`, length `l`. -/
def HasFirstBreak (l : ℕ) : Prop := NewtonPolygon.HasFirstBreak (newtonPolygon v f) m l

variable {f m}

theorem isPure_coe_iff : PowerSeries.IsPure v (f : PowerSeries K) m ↔ IsPure v f m := by sorry

theorem hasFirstBreak_coe_iff {l : ℕ} :
    PowerSeries.HasFirstBreak v (f : PowerSeries K) m l ↔ HasFirstBreak v f m l := by sorry

/-- A pure polynomial has its coefficients controlled by the line. -/
theorem IsPure.le_coeffVal (h0 : f.coeff 0 ≠ 0) (hp : IsPure v f m) (k : ℕ) :
    coeffVal v f 0 + ((m * k : ℝ) : WithTop ℝ) ≤ coeffVal v f k := by sorry

theorem IsPure.norm_coeff_mul_rpow_pow_le (h0 : f.coeff 0 ≠ 0) (hp : IsPure v f m) (k : ℕ) :
    ‖f.coeff k‖ * (v.base ^ m) ^ k ≤ ‖f.coeff 0‖ := by sorry

/-- The leading term of a pure polynomial at the radius `b ^ m` equals the constant term. -/
theorem IsPure.norm_coeff_natDegree_mul_rpow_pow_eq (h0 : f.coeff 0 ≠ 0) (hp : IsPure v f m) :
    ‖f.coeff f.natDegree‖ * (v.base ^ m) ^ f.natDegree = ‖f.coeff 0‖ := by sorry

/-- **Purity from the bounds**: all terms at most the constant one and the leading term equal to it
make a polynomial pure of slope `m`. -/
theorem isPure_of_bounds (h0 : f.coeff 0 ≠ 0) (hd : 0 < f.natDegree)
    (hle : ∀ k, ‖f.coeff k‖ * (v.base ^ m) ^ k ≤ ‖f.coeff 0‖)
    (heq : ‖f.coeff f.natDegree‖ * (v.base ^ m) ^ f.natDegree = ‖f.coeff 0‖) : IsPure v f m := by sorry

/-- **Purity of a polynomial, in Gauss-norm terms** ([Gou20, Problem 341], roadmap §2.4.1). -/
theorem isPure_iff (h0 : f.coeff 0 ≠ 0) (hd : 0 < f.natDegree) :
    IsPure v f m ↔ (∀ k, ‖f.coeff k‖ * (v.base ^ m) ^ k ≤ ‖f.coeff 0‖) ∧
      ‖f.coeff f.natDegree‖ * (v.base ^ m) ^ f.natDegree = ‖f.coeff 0‖ := by sorry

/-- Gouvêa's form for `f(0) = 1`: pure of slope `m` iff `‖f‖_{b^m} = ‖a_n‖ (b^m)^n = 1`. -/
theorem isPure_iff_gaussNorm (h0 : f.coeff 0 = 1) (hd : 0 < f.natDegree) :
    IsPure v f m ↔
      PowerSeries.gaussNorm norm (v.base ^ m) (f : PowerSeries K) =
          ‖f.coeff f.natDegree‖ * (v.base ^ m) ^ f.natDegree ∧
        PowerSeries.gaussNorm norm (v.base ^ m) (f : PowerSeries K) = 1 := by sorry

/-- A polynomial is pure of slope `m` exactly when its first break has slope `m` and the full
length `natDegree f`. -/
theorem isPure_iff_hasFirstBreak (h0 : f.coeff 0 ≠ 0) (hd : 0 < f.natDegree) :
    IsPure v f m ↔ HasFirstBreak v f m f.natDegree := by sorry

end Polynomial
