/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.JacobsSlash.«3_Slopes»
import PhD.NewtonPolygons.OfSlopes

/-!
# The slope reading (AG-NP): from valuation sequences to Newton-polygon slopes

Discharges the AG-NP seam of the Jacobs board: our proved valuation identities
(`val_charCoeff_of_unit_minors` : `v₃(cₘ) = m(m−1)/2`; `val_charCoeff_M22op` :
`v₃(cₘ(M₂,₂)) = m²/2`) give the *points* of a Newton polygon; here we show the polygon
those points determine has the wanted slopes (`0, 1, 2, …` resp. `1/2, 3/2, 5/2, …`).

Method ("explicit witness against the spec"): for a monotone slope sequence `s`, build the
explicit polygon `NewtonPolygon₀.ofSlopes s` and prove `IsNewtonPolygonOf v (ofSlopes s)`
whenever `v` is the partial-sum sequence of `s`; uniqueness then transports the reading to the
polygon our algorithm constructs.  **That machinery is general and lives in
`PhD.NewtonPolygons.OfSlopes`** (moved there on 2026-08-20, slopes-hecke board A0); this file
is now only the two Jacobs applications — cases A and B — plus the arithmetic that identifies
their partial sums as `C(m,2)` and `m²/2`.

## The normalisation `ϖ₃`

The valuation used below is `(ϖ₃ h3).val`, where `JacobsSlash.ϖ₃` (`PhD/Jacobs/SlopeTheorem.lean`)
is `3` viewed as a pseudo-uniformizer.  `PseudoUniformizer.val` is
`v_ϖ(x) = log‖x‖ / log‖ϖ‖`, so `v_ϖ(ϖ) = 1`; taking `ϖ = 3` makes it the thesis's `v₃`, and
the numbers `0, 1, 2, …` / `1/2, 3/2, 5/2, …` below are slopes *in that normalisation*.

`ϖ₃` is a **definition**, not a hypothesis: `PseudoUniformizer` (`PhD/TateFredholm/Tate.lean`)
asks only for a unit with `‖ϖ‖ < 1` and multiplicative norm, all three of which `3` satisfies
under `h3 : ‖(3 : K)‖ < 1` and `[CharZero K]` (see `PseudoUniformizer.ofNormLtOne`).  So the
only hypothesis the statements carry is `h3`, the residue-characteristic-`3` condition (in
`ℚ₃`, `‖3‖ = 1/3 < 1`), which is in any case already a *term-level* argument of
`JacobsSlash.M22op`.  Earlier versions took `(ϖ : PseudoUniformizer K) (hϖ : (ϖ : K) = 3)` as
arguments; that pair was redundant — a normalisation is a choice, not a hypothesis.

**Why a pseudo-uniformizer and not a uniformizer.**  `3` *is* a uniformizer of `ℚ₃`, but case
B's `hω : ω ^ 2 + ω + 1 = 0` puts `ζ₃` in `K`, and `ℚ₃(ζ₃)/ℚ₃` is ramified of degree `2`: a
uniformizer there is `2ω + 1 = √−3` (`JacobsSlash.sq_two_omega_add_one`), with `3 = −(2ω + 1)²`, so
`v₃(K^×) = (1/2)ℤ` and `3` is topologically nilpotent but not a generator.  This is
load-bearing rather than a technicality — case B's slopes `1/2, 3/2, 5/2, …` are
half-integers, so they are values of `v₃` only because `e = 2`; over `ℚ₃` itself
`isNewtonPolygonOf_val_charCoeff_M22op` would be vacuous.  See the `PhD.JacobsSlash.U3Data` module
header for the `ω` side of this.

`[CharZero K]` is what supplies `(3 : K) ≠ 0` now that `ϖ` no longer does.  Case A could
avoid it — `hmin` already forces `3 ≠ 0` (`three_ne_zero_of_unit_minors`) — but uniformity
with `Slopes`/`U3Data`/`DiamondW`, which all assume it, is worth more than the saving.

Sources: [Jacobs, *Slopes of Compact Hecke Operators*, proof of Thm 2.12, pp. 34–35] (the
"points on the parabola ⇒ vertices ⇒ slopes" step); [Kob84, Ch. IV §3] (the classical
Newton-polygon reading); the blueprint Definition 1 via `PhD.NewtonPolygons.Spec`.
-/

open Finset


/-! ### Two arithmetic bridges

The partial sums of the two slope sequences of interest, in closed form. -/

/-- Gauss's sum in the shape needed here: `∑_{i<m} i = C(m, 2)`. -/
private lemma sum_range_id_eq_choose_two (m : ℕ) : ∑ i ∈ range m, i = m.choose 2 := by
  rw [Finset.sum_range_id, Nat.choose_two_right]

/-- `m² = m + 2·C(m, 2)` (the case-B exponent bookkeeping). -/
private lemma add_two_mul_choose_two (m : ℕ) : m + 2 * m.choose 2 = m ^ 2 := by
  induction m with
  | zero => simp
  | succ k ih =>
    have hch : (k + 1).choose 2 = k + k.choose 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
    have hsq : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
    rw [hch, hsq, ← ih]
    ring

/-- Case A's partial sums: `∑_{i<m} i = C(m, 2)`, over `ℝ`. -/
private lemma sum_range_cast_id (m : ℕ) :
    (0 : ℝ) + ∑ i ∈ range m, (i : ℝ) = ((m.choose 2 : ℕ) : ℝ) := by
  rw [zero_add, ← Nat.cast_sum, sum_range_id_eq_choose_two]

/-- Case B's partial sums: `∑_{i<m} (i + 1/2) = m²/2`. -/
private lemma sum_range_cast_add_half (m : ℕ) :
    (0 : ℝ) + ∑ i ∈ range m, ((i : ℝ) + 1 / 2) = (m : ℝ) ^ 2 / 2 := by
  have h1 : (0 : ℝ) + ∑ i ∈ range m, (i : ℝ) = ((m.choose 2 : ℕ) : ℝ) := sum_range_cast_id m
  have h2 : (m : ℝ) + 2 * ((m.choose 2 : ℕ) : ℝ) = (m : ℝ) ^ 2 := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (add_two_mul_choose_two m)
  rw [zero_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [zero_add] at h1
  rw [h1]
  linarith

namespace JacobsSlash

open NewtonPolygon₀ TateFredholm
open scoped TateFredholm


section CaseA

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

/-- **AG-NP, case A (proof of concept — [Jacobs, Thm 2.12] slope statement)**: under the
unit-minor hypotheses, the polygon with slopes `0, 1, 2, …` is the Newton polygon of the
valuation sequence `m ↦ v₃(cₘ(u))`.  The valuation identity supplies the points
`(m, m(m−1)/2)`; this theorem is the slope reading. -/
theorem isNewtonPolygonOf_val_charCoeff
    (h3 : ‖(3 : K)‖ < 1) (u : c(ℕ, K) →L[K] c(ℕ, K))
    (hdiv : ∀ j i, ‖matrixCoeff u j i‖ ≤ ‖(3 : K)‖ ^ j)
    (hmin : ∀ n : ℕ,
      ‖(Matrix.of fun j i : Fin n => (3 : K)⁻¹ ^ (j : ℕ) * matrixCoeff u j i).det‖ = 1) :
    IsNewtonPolygonOf (fun m => (ϖ₃ h3).val (charCoeff u m))
      (ofSlopes (fun n => (n : ℝ)) Nat.mono_cast 0) := by
  refine isNewtonPolygonOf_ofSlopes _ _ _ _ fun m => ?_
  show (ϖ₃ h3).val (charCoeff u m) = (((0 : ℝ) + ∑ i ∈ range m, (i : ℝ) : ℝ) : WithTop ℝ)
  rw [val_charCoeff_of_unit_minors (ϖ₃ h3) u hdiv hmin m, sum_range_cast_id m]

/-- Case A transport: the polygon the step algorithm constructs from the characteristic
power series of `u` (coefficients valued by `v₃`) has unit slopes `0, 1, 2, …` — the
slope sequence of [Jacobs, Thm 2.12]. -/
theorem unitSlope_newtonPolygon₀OfPowerSeries_charPowerSeries
    (h3 : ‖(3 : K)‖ < 1) (u : c(ℕ, K) →L[K] c(ℕ, K))
    (hdiv : ∀ j i, ‖matrixCoeff u j i‖ ≤ ‖(3 : K)‖ ^ j)
    (hmin : ∀ n : ℕ,
      ‖(Matrix.of fun j i : Fin n => (3 : K)⁻¹ ^ (j : ℕ) * matrixCoeff u j i).det‖ = 1)
    (j : ℕ) :
    (newtonPolygon₀OfPowerSeries (ϖ₃ h3).val (charPowerSeries u)).unitSlope j =
      ((j : ℝ) : WithBotTop ℝ) := by
  have hv : ∀ m, coeffSeq (ϖ₃ h3).val (charPowerSeries u) m
      = (((0 : ℝ) + ∑ i ∈ range m, (i : ℝ) : ℝ) : WithTop ℝ) := fun m => by
    rw [coeffSeq_apply, charPowerSeries_coeff,
      val_charCoeff_of_unit_minors (ϖ₃ h3) u hdiv hmin m, sum_range_cast_id m]
  exact unitSlope_newtonPolygon₀OfSeq_ofSlopes (fun n => (n : ℝ)) Nat.mono_cast 0 _ hv j

end CaseA

/- Case B carries the `M₂,₂` parameter pack `(t, ν, ω)` with the hypotheses of
`val_charCoeff_M22op`; `ν` is the thesis's `√−2` (`hν2` the algebraic identity, `hνc` the
3-adic location `ν ≡ 2695 mod 3¹⁰` selecting the Hensel root), and `hω : ω ^ 2 + ω + 1 = 0`
makes `ω = ζ₃`, which indexes the eigenblock and puts `K` over `ℚ₃(ζ₃)` — the ramification
that makes the half-integer slopes below possible (module header, "normalisation pack").
See `PhD.JacobsSlash.U3Data`'s module docstring for the full account. -/
section CaseB

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

variable {t ν : K} (ω : K)

/-- **AG-NP, case B ([Jacobs, Cor 2.16] slope statement)**: the polygon with slopes
`1/2, 3/2, 5/2, …` is the Newton polygon of the valuation sequence `m ↦ v₃(cₘ(M₂,₂))`.

This is the thesis's headline, and it is a statement about the genuine Hecke operator:
`M₂,₂` is the middle factor of `det(1 − T·U₃)` (`JacobsSlash.charPowerSeries_U3MatrixOp`,
`PhD.JacobsSlash.DiamondW`) and `U₃`'s matrix is identified in `PhD.JacobsSlash.U3.Matrix`
(`heckeU3_apply_classRep`, `charPowerSeries_blockOp_eq_U3MatrixOp`).  The further reading
"these are the slopes of `U₃` on the `ω²`-eigenspace of the diamond operator" is *not*
formalised — it needs [Jacobs, Lemma 2.9]; see `PhD.JacobsSlash.DiamondW`'s module header. -/
theorem isNewtonPolygonOf_val_charCoeff_M22op
    (hω : ω ^ 2 + ω + 1 = 0) (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1) (hν2 : ν ^ 2 = -2)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) :
    IsNewtonPolygonOf (fun m => (ϖ₃ h3).val (charCoeff (M22op ω hω h3 ht hνc) m))
      (ofSlopes (fun n => (n : ℝ) + 1 / 2) (Nat.mono_cast.add_const _) 0) := by
  refine isNewtonPolygonOf_ofSlopes _ _ _ _ fun m => ?_
  show (ϖ₃ h3).val (charCoeff (M22op ω hω h3 ht hνc) m)
      = (((0 : ℝ) + ∑ i ∈ range m, ((i : ℝ) + 1 / 2) : ℝ) : WithTop ℝ)
  rw [val_charCoeff_M22op ω h3 ht hν2 hνc hω m, sum_range_cast_add_half m]

/-- Case B transport: the polygon the step algorithm constructs from
`det(1 − T·M₂,₂)` has unit slopes `1/2, 3/2, 5/2, …` — [Jacobs, Cor 2.16]. -/
theorem unitSlope_newtonPolygon₀OfPowerSeries_M22op
    (hω : ω ^ 2 + ω + 1 = 0) (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1) (hν2 : ν ^ 2 = -2)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) (j : ℕ) :
    (newtonPolygon₀OfPowerSeries (ϖ₃ h3).val
        (charPowerSeries (M22op ω hω h3 ht hνc))).unitSlope j =
      (((j : ℝ) + 1 / 2 : ℝ) : WithBotTop ℝ) := by
  have hv : ∀ m, coeffSeq (ϖ₃ h3).val (charPowerSeries (M22op ω hω h3 ht hνc)) m
      = (((0 : ℝ) + ∑ i ∈ range m, ((i : ℝ) + 1 / 2) : ℝ) : WithTop ℝ) := fun m => by
    rw [coeffSeq_apply, charPowerSeries_coeff, val_charCoeff_M22op ω h3 ht hν2 hνc hω m,
      sum_range_cast_add_half m]
  exact unitSlope_newtonPolygon₀OfSeq_ofSlopes (fun n => (n : ℝ) + 1 / 2)
    (Nat.mono_cast.add_const _) 0 _ hv j

end CaseB

end JacobsSlash
