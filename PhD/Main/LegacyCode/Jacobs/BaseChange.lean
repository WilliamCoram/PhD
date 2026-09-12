/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Jacobs.U3Data
import PhD.Main.TateFredholm.«05_Fredholm»

/-!
# Base change of Fredholm determinants and of the Jacobs analytic layer

Two layers, both consumed by `PhD.Jacobs.U3.HeckeSlopes` (the endgame board
`.mathlib-quality/jacobs-endgame/`):

* `TateFredholm.charCoeff_map` / `TateFredholm.charPowerSeries_map` — an isometric ring
  homomorphism `f : R →+* S` transports the characteristic power series: if the matrix of
  `v` is the entrywise `f`-image of the matrix of a compactoid `u`, then
  `charPowerSeries v = PowerSeries.map f (charPowerSeries u)`.  The proof is
  coefficientwise: minors are finite determinants (`RingHom.map_det`), and the tsum over
  minors transports along the continuous (isometric) `f` using `summable_minor`.

* The `Jacobs` analytic layer commutes with isometric field embeddings: `padicLog`,
  `padicExp`, `unitPow`, `binomialCoeff` and the generating-function layer
  (`kappaSeries₂`, `linSeries`, `quadSeries`, `weightGenFun`, the six `h_{i,j}`) are all
  defined by tsums of field expressions in their arguments, so an isometric `f : K →+* L`
  maps each one to its counterpart at the image parameters.  (Isometry transports
  summability in both directions over complete ultrametric fields, so no disc hypotheses
  are needed: on the junk region both sides are the junk value `0`.)

The `M`-eigenblocks (`M11genFun`, `M22genFun`, `M33genFun`) need no map lemmas: they only
exist over fields containing `ω` and are instantiated directly over the extension field.
-/

open scoped TateFredholm

namespace TateFredholm

variable {R S : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormOneClass R] [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]
  [NormOneClass S]

variable {I : Type*} [DecidableEq I]

omit [IsUltrametricDist S] [CompleteSpace S] [NormOneClass S] in
/-- Coefficientwise base change of the Fredholm determinant along an isometric ring
homomorphism: if the matrix of `v` is the entrywise `f`-image of the matrix of a
compactoid `u`, then `charCoeff v n = f (charCoeff u n)`. -/
theorem charCoeff_map [IsTate R] (f : R →+* S) (hf : ∀ x, ‖f x‖ = ‖x‖)
    {u : c(I, R) →L[R] c(I, R)} {v : c(I, S) →L[S] c(I, S)} (hu : IsCompactoid u)
    (hmatch : ∀ j i, matrixCoeff v j i = f (matrixCoeff u j i)) (n : ℕ) :
    charCoeff v n = f (charCoeff u n) := by
  have htsum : ∑' S : {S : Finset I // S.card = n}, f (minor u (S : Finset I))
      = f (∑' S : {S : Finset I // S.card = n}, minor u (S : Finset I)) :=
    ((summable_minor u hu n).hasSum.map f
      (AddMonoidHomClass.isometry_of_norm f hf).continuous).tsum_eq
  have hminor (S : Finset I) : minor v S = f (minor u S) := by
    rw [minor, minor, RingHom.map_det]
    congr 1
    ext j i
    exact hmatch _ _
  rw [charCoeff, charCoeff, map_mul, map_pow, map_neg, map_one, ← htsum]
  exact congrArg ((-1 : S) ^ n * ·) (tsum_congr fun s ↦ hminor s)

/-- **Base change of the Fredholm determinant** along an isometric ring homomorphism:
if the matrix of `v` is the entrywise `f`-image of the matrix of a compactoid `u`, the
characteristic power series of `v` is the coefficientwise `f`-image of that of `u`. -/
theorem charPowerSeries_map [IsTate R] (f : R →+* S) (hf : ∀ x, ‖f x‖ = ‖x‖)
    {u : c(I, R) →L[R] c(I, R)} {v : c(I, S) →L[S] c(I, S)} (hu : IsCompactoid u)
    (hmatch : ∀ j i, matrixCoeff v j i = f (matrixCoeff u j i)) :
    charPowerSeries v = PowerSeries.map f (charPowerSeries u) := by
  ext n
  rw [PowerSeries.coeff_map, charPowerSeries_coeff, charPowerSeries_coeff]
  exact charCoeff_map f hf hu hmatch n

end TateFredholm

/-- A ring homomorphism of `MvPowerSeries` coefficients over fields commutes with the
junk-valued inverse: both sides are the genuine inverse when the constant coefficient is
nonzero, and both are the junk value `0` otherwise.  (Not in mathlib as of
2026-08-05.) -/
theorem MvPowerSeries.map_inv₀ {σ : Type*} {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (φ : MvPowerSeries σ K) :
    MvPowerSeries.map f φ⁻¹ = (MvPowerSeries.map f φ)⁻¹ := by
  by_cases h : MvPowerSeries.constantCoeff φ = 0
  · rw [MvPowerSeries.inv_eq_zero.mpr h, map_zero, eq_comm, MvPowerSeries.inv_eq_zero,
      MvPowerSeries.constantCoeff_map, h, map_zero]
  · have h' : MvPowerSeries.constantCoeff (MvPowerSeries.map f φ) ≠ 0 := by
      rwa [MvPowerSeries.constantCoeff_map, f.injective.ne_iff' (map_zero f)]
    rw [eq_comm, MvPowerSeries.inv_eq_iff_mul_eq_one h', ← map_mul,
      MvPowerSeries.inv_mul_cancel φ h, map_one]

namespace Jacobs

variable {K L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [CharZero L]

section Analytic

-- The analytic layer never needs completeness of the TARGET field: tsums transport
-- along the isometry, with the junk value `0` on both sides off the summable region.
omit [CompleteSpace L]

private theorem map_tsum (f : K →+* L) (hf : ∀ x, ‖f x‖ = ‖x‖) (g : ℕ → K) :
    f (∑' n, g n) = ∑' n, f (g n) := by
  by_cases hg : Summable g
  · exact (hg.hasSum.map f
      (AddMonoidHomClass.isometry_of_norm f hf).continuous).tsum_eq.symm
  · have hfg : ¬ Summable fun n ↦ f (g n) := fun hsum ↦ hg <| by
      refine TateFredholm.summable_of_tendsto_cofinite ?_
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simpa only [hf, norm_zero] using hsum.tendsto_cofinite_zero.norm
    rw [tsum_eq_zero_of_not_summable hg, tsum_eq_zero_of_not_summable hfg, map_zero]

/-- Isometric field embeddings commute with the `p`-adic logarithm.  Unconditional: on
the non-summable region both sides are the junk value `0`. -/
theorem map_padicLog (f : K →+* L) (hf : ∀ x, ‖f x‖ = ‖x‖) (u : K) :
    f (padicLog u) = padicLog (f u) := by
  rw [padicLog, padicLog, map_neg, map_tsum f hf]
  exact congrArg Neg.neg (tsum_congr fun n ↦ by simp)

/-- Isometric field embeddings commute with the `p`-adic exponential (unconditional, as
for `map_padicLog`). -/
theorem map_padicExp (f : K →+* L) (hf : ∀ x, ‖f x‖ = ‖x‖) (w : K) :
    f (padicExp w) = padicExp (f w) := by
  rw [padicExp, padicExp, map_tsum f hf]
  exact tsum_congr fun n ↦ by simp

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] in
/-- Field homomorphisms commute with the binomial coefficient series coefficients
`(t choose n) = (1/n!) ∏_{k<n} (t − k)` (a finite field expression; no isometry
needed). -/
theorem map_binomialCoeff (f : K →+* L) (t : K) (n : ℕ) :
    f (binomialCoeff t n) = binomialCoeff (f t) n := by
  simp [binomialCoeff]

/-- Isometric field embeddings commute with `unitPow`:
`f (u^t) = (f u)^(f t)` in the notation `unitPow t u = exp₃(t·log₃ u)`. -/
theorem map_unitPow (f : K →+* L) (hf : ∀ x, ‖f x‖ = ‖x‖) (t u : K) :
    f (unitPow t u) = unitPow (f t) (f u) := by
  rw [unitPow, unitPow, map_padicExp f hf, map_mul, map_padicLog f hf]

end Analytic

section Series

/-- `kappaSeries₂` maps coefficientwise to `kappaSeries₂` at the image parameters. -/
theorem map_kappaSeries₂ (f : K →+* L) (hf : ∀ x, ‖f x‖ = ‖x‖) (t c d : K) :
    MvPowerSeries.map f (kappaSeries₂ t c d) = kappaSeries₂ (f t) (f c) (f d) := by
  refine MvPowerSeries.ext fun p ↦ ?_
  rw [MvPowerSeries.coeff_map, coeff_kappaSeries₂, coeff_kappaSeries₂]
  split_ifs
  · rw [map_mul, map_mul, map_unitPow f hf, map_binomialCoeff, map_pow, map_div₀]
  · exact map_zero f

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [IsUltrametricDist L]
  [CompleteSpace L] [CharZero L] in
/-- The linear denominator series maps entrywise. -/
theorem map_linSeries (f : K →+* L) (γ : Matrix (Fin 2) (Fin 2) K) :
    MvPowerSeries.map f (linSeries γ) = linSeries (γ.map f) := by
  simp [linSeries]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [IsUltrametricDist L]
  [CompleteSpace L] [CharZero L] in
/-- The quadratic denominator series maps entrywise. -/
theorem map_quadSeries (f : K →+* L) (γ : Matrix (Fin 2) (Fin 2) K) :
    MvPowerSeries.map f (quadSeries γ) = quadSeries (γ.map f) := by
  simp [quadSeries]

/-- **The weight generating function commutes with isometric embeddings**: [Jacobs,
Prop 2.6]'s formula `κ(cx+d)/((cx+d)(cx+d−axy−by))` is a field expression in the matrix
entries, so `f` moves through it. -/
theorem map_weightGenFun (f : K →+* L) (hf : ∀ x, ‖f x‖ = ‖x‖) (t : K)
    (γ : Matrix (Fin 2) (Fin 2) K) :
    MvPowerSeries.map f (weightGenFun t γ) = weightGenFun (f t) (γ.map f) := by
  rw [weightGenFun, weightGenFun, map_mul, map_mul, MvPowerSeries.map_inv₀,
    MvPowerSeries.map_inv₀, map_kappaSeries₂ f hf, map_linSeries, map_quadSeries]
  rfl

end Series

section BlockGenFun

-- The nine transcribed `ε`-matrices have entries rational in `ν`, so they map entrywise
-- to the same matrices at `f ν`.  Purely algebraic; discharged per entry by `simp`'s
-- `map_*` set.  (Linter silenced for the block: these use no analytic instances.)
section EpsEntrywise
set_option linter.unusedSectionVars false

private theorem map_eps01M1 (f : K →+* L) (ν : K) :
    (eps01M1 ν).map f = eps01M1 (f ν) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eps01M1, map_div₀, map_ofNat]

private theorem map_eps01M2 (f : K →+* L) (ν : K) :
    (eps01M2 ν).map f = eps01M2 (f ν) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eps01M2, map_div₀, map_ofNat]

private theorem map_eps02M (f : K →+* L) (ν : K) :
    (eps02M ν).map f = eps02M (f ν) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eps02M, map_div₀, map_ofNat]

private theorem map_eps10M (f : K →+* L) (ν : K) :
    (eps10M ν).map f = eps10M (f ν) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eps10M, map_ofNat]

private theorem map_eps12M1 (f : K →+* L) (ν : K) :
    (eps12M1 ν).map f = eps12M1 (f ν) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eps12M1, map_div₀, map_ofNat]

private theorem map_eps12M2 (f : K →+* L) (ν : K) :
    (eps12M2 ν).map f = eps12M2 (f ν) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eps12M2, map_div₀, map_ofNat]

private theorem map_eps20M1 (f : K →+* L) (ν : K) :
    (eps20M1 ν).map f = eps20M1 (f ν) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eps20M1, map_div₀, map_ofNat]

private theorem map_eps20M2 (f : K →+* L) (ν : K) :
    (eps20M2 ν).map f = eps20M2 (f ν) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eps20M2, map_div₀, map_ofNat]

private theorem map_eps21M (f : K →+* L) (ν : K) :
    (eps21M ν).map f = eps21M (f ν) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eps21M, map_div₀, map_ofNat]

end EpsEntrywise

/-- `h₀,₁` maps to `h₀,₁` at the image parameters. -/
theorem map_h01 (f : K →+* L) (hf : ∀ x, ‖f x‖ = ‖x‖) (t ν : K) :
    MvPowerSeries.map f (h01 t ν) = h01 (f t) (f ν) := by
  rw [h01, h01, map_add, map_weightGenFun f hf, map_weightGenFun f hf, map_eps01M1,
    map_eps01M2]

/-- `h₀,₂` maps to `h₀,₂` at the image parameters. -/
theorem map_h02 (f : K →+* L) (hf : ∀ x, ‖f x‖ = ‖x‖) (t ν : K) :
    MvPowerSeries.map f (h02 t ν) = h02 (f t) (f ν) := by
  rw [h02, h02, map_weightGenFun f hf, map_eps02M]

/-- `h₁,₀` maps to `h₁,₀` at the image parameters. -/
theorem map_h10 (f : K →+* L) (hf : ∀ x, ‖f x‖ = ‖x‖) (t ν : K) :
    MvPowerSeries.map f (h10 t ν) = h10 (f t) (f ν) := by
  rw [h10, h10, map_weightGenFun f hf, map_eps10M]

/-- `h₁,₂` maps to `h₁,₂` at the image parameters. -/
theorem map_h12 (f : K →+* L) (hf : ∀ x, ‖f x‖ = ‖x‖) (t ν : K) :
    MvPowerSeries.map f (h12 t ν) = h12 (f t) (f ν) := by
  rw [h12, h12, map_add, map_weightGenFun f hf, map_weightGenFun f hf, map_eps12M1,
    map_eps12M2]

/-- `h₂,₀` maps to `h₂,₀` at the image parameters. -/
theorem map_h20 (f : K →+* L) (hf : ∀ x, ‖f x‖ = ‖x‖) (t ν : K) :
    MvPowerSeries.map f (h20 t ν) = h20 (f t) (f ν) := by
  rw [h20, h20, map_add, map_weightGenFun f hf, map_weightGenFun f hf, map_eps20M1,
    map_eps20M2]

/-- `h₂,₁` maps to `h₂,₁` at the image parameters. -/
theorem map_h21 (f : K →+* L) (hf : ∀ x, ‖f x‖ = ‖x‖) (t ν : K) :
    MvPowerSeries.map f (h21 t ν) = h21 (f t) (f ν) := by
  rw [h21, h21, map_weightGenFun f hf, map_eps21M]

end BlockGenFun

end Jacobs
