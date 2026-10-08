/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.RigidAnalyticGeometry.Restricted.PowerSeries.MulDistinguished
import PhD.TauCeti.Code.NewtonPolygons.Coeff.Pure

/-!
# First breaks and distinguished series

A series whose first break is at index `l` with slope `m` is **distinguished at the radius `b ^ m`
of degree `l`**: its Gauss norm at `b ^ m` is attained at `l` and nowhere later (roadmap §2.4.3;
[Gou20, §7.4]: "`i` is the largest integer such that `‖f(X)‖_c = |a_i| c^i`", the hypothesis on `N`
of [Gou20, Proposition 7.2.3]). The predicate is the one the rigid-analytic-geometry chain of this
repository adopts for Weierstrass division at an arbitrary radius,
`PowerSeries.IsMulDistinguished c f s` ([Mar16, Definition 1.24]), as roadmap §2.4.3 asks; its
unit clause is automatic over a field (`IsUnit.isNormMulUnit`). It is the normed analogue of
`Polynomial.IsWeaklyEisensteinAt`. More generally the distinguished degree at `b ^ m` is the right
endpoint of the face of slope `m`, which is the reading Layer 3 uses to factor a series at a vertex
of its polygon.

Roadmap: §2.4.3. Tau Ceti home: `TauCeti/NumberTheory/NewtonPolygon/Distinguished.lean`.

## Main results

* `PowerSeries.HasFirstBreak.isMulDistinguished`, `Polynomial.HasFirstBreak.isMulDistinguished`;
* `Polynomial.IsPure.isMulDistinguished` — a pure polynomial is distinguished of its degree;
* `PowerSeries.isMulDistinguished_rpow_iff_faceRight_eq`,
  `Polynomial.isMulDistinguished_rpow_iff_faceRight_eq` — distinguished degree = face endpoint.
-/

open NormedField
open NewtonPolygon (IsAdmissible SlopesUnbounded faceRight)

variable {K : Type*} [NormedField K] {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] (v : NormedAddValuation K Γ)

namespace PowerSeries

variable {f : PowerSeries K} {m : ℝ}

/-- Over a field, a series is distinguished exactly when its Gauss norm is attained at `i` and
strictly dominates every later term: the unit clause is automatic. -/
theorem isMulDistinguished_iff {c : ℝ} {i : ℕ} :
    IsMulDistinguished c f i ↔
      gaussNorm norm c f = ‖coeff i f‖ * c ^ i ∧
        ∀ t, i < t → ‖coeff t f‖ * c ^ t < ‖coeff i f‖ * c ^ i := by sorry

/-- **A series with first break at `l` of slope `m` is distinguished of degree `l` at the radius
`b ^ m`.** -/
theorem HasFirstBreak.isMulDistinguished (hf : IsAdmissible (coeffVal v f)) (h0 : coeff 0 f ≠ 0)
    {l : ℕ} (hb : HasFirstBreak v f m l) : IsMulDistinguished (v.base ^ m) f l := by sorry

/-- **The distinguished degree at `b ^ m` is the right endpoint of the face of slope `m`.** -/
theorem isMulDistinguished_rpow_iff_faceRight_eq (hf : IsAdmissible (coeffVal v f))
    (h0 : coeff 0 f ≠ 0) (hu : SlopesUnbounded (newtonPolygon v f)) {i : ℕ} :
    IsMulDistinguished (v.base ^ m) f i ↔ faceRight (newtonPolygon v f) m = i := by sorry

end PowerSeries

namespace Polynomial

variable {f : Polynomial K} {m : ℝ}

/-- **A polynomial with first break at `l` of slope `m` is distinguished of degree `l` at the radius
`b ^ m`** (roadmap §2.4.3). -/
theorem HasFirstBreak.isMulDistinguished (h0 : f.coeff 0 ≠ 0) {l : ℕ} (hb : HasFirstBreak v f m l) :
    PowerSeries.IsMulDistinguished (v.base ^ m) (f : PowerSeries K) l := by sorry

/-- A pure polynomial of slope `m` is distinguished of degree `natDegree f` at the radius `b ^ m`. -/
theorem IsPure.isMulDistinguished (h0 : f.coeff 0 ≠ 0) (hd : 0 < f.natDegree) (hp : IsPure v f m) :
    PowerSeries.IsMulDistinguished (v.base ^ m) (f : PowerSeries K) f.natDegree := by sorry

/-- **The distinguished degree of a polynomial at `b ^ m` is the right endpoint of the face of slope
`m`.** -/
theorem isMulDistinguished_rpow_iff_faceRight_eq (h0 : f.coeff 0 ≠ 0) {i : ℕ} :
    PowerSeries.IsMulDistinguished (v.base ^ m) (f : PowerSeries K) i ↔
      faceRight (newtonPolygon v f) m = i := by sorry

end Polynomial
