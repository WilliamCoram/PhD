/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TateFredholm.«12_RieszColeman»
import PhD.TateFredholm.«00_Charpoly»

/-!
# The finite factor of a Fredholm determinant — SKELETON

If a compactoid operator `u` commutes with an idempotent `pr` whose range is finite free, the
Fredholm determinant splits as the reversed characteristic polynomial of the finite piece times the
determinant of the complement:

  `charPowerSeries u = charPowerSeries (u * (1 − pr)) * (Q (u·pr) P).charpolyRev`

along any rank factorisation `pr = P Q`, `Q P = 1`.  The first factorisation is
`TateFredholm.charPowerSeries_eq_mul_of_comm`; identifying `charPowerSeries (u * pr)` with a finite
`charpolyRev` is `Matrix.charpolyRev_eq_of_mul_eq`.  Both already exist and are sorry-free; this
file only assembles them.

[LWX, §3.23 Step I] uses exactly this: the classical subspace is a finite-dimensional
`U_p`-stable piece of the overconvergent space, and Step I compares *its* slopes with the first
`n_{k+1}` slopes of the whole space.  The comparison itself — that the finite factor contributes an
initial segment of the Newton polygon — is a separate gap (AG3), recorded on this board.

## Main declarations

* `TateFredholm.charPowerSeries_eq_mul_charpolyRev` — the split.
-/

noncomputable section

namespace TateFredholm

open Polynomial

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R]
  [IsTate R] {I : Type*} [DecidableEq I]

/-- **The finite factor of a Fredholm determinant.**  If the compactoid `u` commutes with an
idempotent `pr` and `u * pr` has range inside the span of a finite set `s`, then the Fredholm
determinant splits as the complement's determinant times a *polynomial* of degree at most
`s.card` — the characteristic polynomial of the finite piece. -/
theorem charPowerSeries_eq_mul_polynomial
    {u pr : c(I, R) →L[R] c(I, R)} (hu : IsCompactoid u) (hpr : pr * pr = pr)
    (hcomm : u * pr = pr * u) {s : Finset c(I, R)}
    (hs : LinearMap.range ((u * pr : c(I, R) →L[R] c(I, R)) : c(I, R) →ₗ[R] c(I, R))
        ≤ Submodule.span R (s : Set c(I, R))) :
    ∃ G : R[X], G.natDegree ≤ s.card ∧
      charPowerSeries u = charPowerSeries (u * (1 - pr)) * (G : PowerSeries R) := by
  obtain ⟨G, hdeg, hG⟩ := exists_polynomial_charPowerSeries_of_range_le hs
  exact ⟨G, hdeg, by rw [charPowerSeries_eq_mul_of_comm hu hpr hcomm, hG]⟩

end TateFredholm
