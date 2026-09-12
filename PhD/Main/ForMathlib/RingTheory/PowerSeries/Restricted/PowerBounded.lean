/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.ForMathlib.RingTheory.MvPowerSeries.Restricted.PowerBounded
import PhD.Main.ForMathlib.RingTheory.PowerSeries.Restricted.GaussNorm

/-! # Power-bounded and topologically nilpotent restricted power series

This file restates the coefficientwise characterisations of power-boundedness and topological
nilpotency from `MvPowerSeries.Restricted` with `ℕ`-indexed coefficients.  Each direction
holds under a sharp one-sided bound on the radius (`1 ≤ c` for the coefficient direction,
`c ≤ 1` for the monomial direction); the equivalences hold at the Tate algebra radius `c = 1`.

Let `R` be a normed commutative ring with ultrametric distance and multiplicative norm.

* `PowerSeries.Restricted.isTopologicallyNilpotent_iff_forall_isTopologicallyNilpotent_coeff`:
  a restricted power series is topologically nilpotent if and only if all its coefficients are.

If moreover `‖1‖ = 1` and the origin of `R` is not isolated:

* `PowerSeries.Restricted.isPowerBounded_iff_forall_isPowerBounded_coeff`: a restricted power
  series is power-bounded if and only if all its coefficients are.

All proofs are transports of the multivariate lemmas along `ℕ ≃ (Unit →₀ ℕ)`.
-/

open Filter PowerBounded
open scoped Topology

namespace PowerSeries.Restricted

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] (c : ℝ)
  [Fact (0 < c)]

section PowerBounded

variable [NormOneClass R] [NeBot (𝓝[≠] (0 : R))]

/-- If the radius is at least `1`, the coefficients of a power-bounded restricted power series
are power-bounded. -/
theorem isPowerBounded_coeff (h1 : 1 ≤ c) {f : Restricted R c} (hf : IsPowerBounded f)
    (i : ℕ) : IsPowerBounded (coeff i f.1) :=
  MvPowerSeries.Restricted.isPowerBounded_coeff (fun _ ↦ c) (fun _ ↦ h1) hf
    (Finsupp.single () i)

/-- If the radius is at most `1`, a monomial with power-bounded coefficient is power-bounded in
`Restricted R c`. -/
theorem isPowerBounded_monomial (h2 : c ≤ 1) {a : R} (ha : IsPowerBounded a) (n : ℕ) :
    IsPowerBounded (monomial c n a) :=
  MvPowerSeries.Restricted.isPowerBounded_monomial (fun _ ↦ c) (fun _ ↦ h2) ha
    (Finsupp.single () n)

/-- If the radius is at most `1`, a restricted power series with power-bounded coefficients is
power-bounded. -/
theorem isPowerBounded_of_forall_isPowerBounded_coeff (h2 : c ≤ 1) {f : Restricted R c}
    (h : ∀ i, IsPowerBounded (coeff i f.1)) : IsPowerBounded f :=
  MvPowerSeries.Restricted.isPowerBounded_of_forall_isPowerBounded_coeff (fun _ ↦ c)
    (fun _ ↦ h2) fun t ↦ by
      obtain ⟨n, rfl⟩ : ∃ n, t = Finsupp.single () n := ⟨t (), Finsupp.unique_single t⟩
      exact h n

/-- At the Tate algebra radius `c = 1`, a restricted power series is power-bounded if and only
if all its coefficients are. -/
theorem isPowerBounded_iff_forall_isPowerBounded_coeff (hc : c = 1) {f : Restricted R c} :
    IsPowerBounded f ↔ ∀ i, IsPowerBounded (coeff i f.1) :=
  ⟨fun hf i ↦ isPowerBounded_coeff c hc.ge hf i,
    isPowerBounded_of_forall_isPowerBounded_coeff c hc.le⟩

end PowerBounded

section TopologicallyNilpotent

/-- If the radius is at least `1`, the coefficients of a topologically nilpotent restricted
power series are topologically nilpotent. -/
theorem isTopologicallyNilpotent_coeff (h1 : 1 ≤ c) {f : Restricted R c}
    (hf : IsTopologicallyNilpotent f) (i : ℕ) : IsTopologicallyNilpotent (coeff i f.1) :=
  MvPowerSeries.Restricted.isTopologicallyNilpotent_coeff (fun _ ↦ c) (fun _ ↦ h1) hf
    (Finsupp.single () i)

/-- If the radius is at most `1`, a monomial with topologically nilpotent coefficient is
topologically nilpotent in `Restricted R c`. -/
theorem isTopologicallyNilpotent_monomial (h2 : c ≤ 1) {a : R}
    (ha : IsTopologicallyNilpotent a) (n : ℕ) :
    IsTopologicallyNilpotent (monomial c n a) :=
  MvPowerSeries.Restricted.isTopologicallyNilpotent_monomial (fun _ ↦ c) (fun _ ↦ h2) ha
    (Finsupp.single () n)

/-- If the radius is at most `1`, a restricted power series with topologically nilpotent
coefficients is topologically nilpotent. -/
theorem isTopologicallyNilpotent_of_forall_isTopologicallyNilpotent_coeff (h2 : c ≤ 1)
    {f : Restricted R c} (h : ∀ i, IsTopologicallyNilpotent (coeff i f.1)) :
    IsTopologicallyNilpotent f :=
  MvPowerSeries.Restricted.isTopologicallyNilpotent_of_forall_isTopologicallyNilpotent_coeff
    (fun _ ↦ c) (fun _ ↦ h2) fun t ↦ by
      obtain ⟨n, rfl⟩ : ∃ n, t = Finsupp.single () n := ⟨t (), Finsupp.unique_single t⟩
      exact h n

/-- At the Tate algebra radius `c = 1`, a restricted power series is topologically nilpotent if
and only if all its coefficients are. -/
theorem isTopologicallyNilpotent_iff_forall_isTopologicallyNilpotent_coeff (hc : c = 1)
    {f : Restricted R c} :
    IsTopologicallyNilpotent f ↔ ∀ i, IsTopologicallyNilpotent (coeff i f.1) :=
  ⟨fun hf i ↦ isTopologicallyNilpotent_coeff c hc.ge hf i,
    isTopologicallyNilpotent_of_forall_isTopologicallyNilpotent_coeff c hc.le⟩

end TopologicallyNilpotent

end PowerSeries.Restricted
