/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Jacobs.U3Data
import PhD.Jacobs.SlopeTheorem

/-!
# The slopes of `M₂,₂` are `1/2, 3/2, 5/2, …` ([Jacobs, Theorem 2.14, Corollary 2.16])

The endgame of [Jacobs, *Slopes of Compact Hecke Operators*, §2.1, pp. 34–39].  Set

  `M′₂,₂ = (1/(ω(2ω+1))) · D(1/(2ω+1)) M₂,₂ D(2ω+1)`,   `N = D(1/3) M′₂,₂`.

* [Jacobs, Lemma 2.13]: `N` is integral — `H′₂,₂(x/3, y) ∈ 𝒪₃[[x, y]]`.
* [Jacobs, Theorem 2.14]: `H′₂,₂(x/3, y) ≡ −1/(1 − xy) mod 𝔪₃`; equivalently
  ([Jacobs, Corollary 2.15]) `N ≡ −D(1) mod 𝔪₃`, so every top-left minor of `N` is a
  unit.
* [Jacobs, Theorem 2.12] then gives `v₃(cₘ(M′₂,₂)) = m(m−1)/2`; undoing the scalar
  `1/(ω(2ω+1))` (norm `‖3‖^{1/2}`) and the diagonal conjugation (which fixes the
  characteristic series, by the trace property `det(1−Tuv) = det(1−Tvu)` — [Jacobs,
  Proposition 1.14] = `TateFredholm.charPowerSeries_comm`) yields
  ([Jacobs, Corollary 2.16]) the `n`-th slope of `M₂,₂` is `n − 1/2`:

  `‖cₘ(M₂,₂)‖² = ‖3‖^(m²)`,   i.e.   `v₃(cₘ(M₂,₂)) = m²/2`.

Everything "mod `𝔪₃`" is phrased as strict norm inequalities `‖· − ·‖ < 1`; no residue
rings appear.  The parameters `ν` (with `hν2 : ν² = −2`, `hνc : ‖ν − 2695‖ ≤ ‖3‖¹⁰` —
the thesis's `√−2 ≡ 508 mod 3⁷`, refined to `2695 mod 3¹⁰` per its p. 39 substitution)
and `ω` are documented where they are introduced, in `PhD.Jacobs.U3Data`'s module
docstring.  Note `(2ω + 1)² = −3` (from `ω² + ω + 1 = 0`), so `‖2ω + 1‖² = ‖3‖`.

## How this connects to the genuine Hecke operator (PROVED elsewhere)

`M₂,₂` is *defined* here by its generating function, so the theorems below are
unconditional statements about that defined operator.  Two separate results, both now
proved, turn them into statements about `U₃ = [U₁(9)·η₃·U₁(9)]`:

* the **identification** — the transcribed matrix is the matrix of `U₃`
  (`Jacobs.U3.heckeU3_apply_classRep`, `Jacobs.U3.charPowerSeries_blockOp_eq_U3MatrixOp`
  in `PhD.Jacobs.U3.Matrix`; see `PhD.Jacobs.U3Data`'s module header for the full list of
  formalised inputs, Thm 2.1 – Prop 2.6);
* the **factorisation** — `M₂,₂` is the middle factor of
  `det(1 − T·U₃) = det(1 − T·M₁,₁)·det(1 − T·M₂,₂)·det(1 − T·M₃,₃)`
  (`Jacobs.charPowerSeries_U3MatrixOp` in `PhD.Jacobs.DiamondW`, via [Jacobs, Lemma 2.10]
  and Serre's partition lemma).

Caveat on wording: the *factorisation* is proved, but calling `M₂,₂` "the `ω²`-eigenblock
of the diamond operator" is an interpretation that is not formalised — the derivation of
`W`'s matrix from `[UμU]` ([Jacobs, Lemma 2.9, §B.2]) is not done (see
`PhD.Jacobs.DiamondW`'s module header).  Nothing downstream depends on it: the
block-diagonalisation `lemma210` is proved directly from the Lemma 2.11 identities.

## Slope reading (proved in `PhD.Jacobs.SlopeReading`)

The endpoint theorems below compute the exact valuations `v₃(cₘ(M₂,₂)) = m²/2` — the
*points* `(m, m²/2)` of the Newton polygon of `det(1 − T·M₂,₂)`.  Reading off the slopes
`1/2, 3/2, 5/2, …` from those points (points on a strictly convex parabola ⇒ all
vertices ⇒ slopes = successive differences) is `Jacobs.unitSlope_newtonPolygon₀OfPowerSeries_M22op`
(the AG-NP tranche, `PhD.Jacobs.SlopeReading`), which is where [Jacobs, Corollary 2.16]
is stated in full.
-/

open TateFredholm MvPowerSeries
open scoped TateFredholm

namespace Jacobs

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

section NormLe

/-!
### A coefficientwise norm calculus

Everything "mod `𝔪₃`" in [Jacobs, §2.1] is a statement about the size of the coefficients of a
two-variable power series.  `NormLe ε φ` says every coefficient of `φ` has norm at most `ε`;
`NormLe 1` is integrality and `NormLe ε` with `ε < 1` is "`≡ 0 mod 𝔪₃`".  The class is closed
under sums, products (the convolution is an ultrametric sum) and — for a unit constant
coefficient — inversion, and it comes with the two Taylor expansions of `φ ↦ φ⁻¹` used to
linearise the three denominators of [Jacobs, pp. 37–38].

The estimates are *not* uniform in the naive sense: the three scalars of `NgenFun` have norm
`‖3‖^{-1/2}`, so all errors have to be pushed below `‖3‖^{1/2}` before they are multiplied in.
This is why the calculus carries an explicit real bound instead of a `Prop`-valued "small".
-/

set_option linter.unusedSectionVars false

/-- Every coefficient of `φ` has norm at most `ε`. -/
private def NormLe (ε : ℝ) (φ : MvPowerSeries (Fin 2) K) : Prop :=
  ∀ p : Fin 2 →₀ ℕ, ‖coeff p φ‖ ≤ ε

private lemma normLe_nonneg {ε : ℝ} {φ : MvPowerSeries (Fin 2) K} (h : NormLe ε φ) : 0 ≤ ε :=
  (norm_nonneg _).trans (h 0)

private lemma normLe_mono {ε δ : ℝ} {φ : MvPowerSeries (Fin 2) K} (h : NormLe ε φ)
    (hle : ε ≤ δ) : NormLe δ φ := fun p => (h p).trans hle

private lemma normLe_add {ε : ℝ} {φ ψ : MvPowerSeries (Fin 2) K} (hφ : NormLe ε φ)
    (hψ : NormLe ε ψ) : NormLe ε (φ + ψ) := fun p => by
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hφ p) (hψ p))

private lemma normLe_neg {ε : ℝ} {φ : MvPowerSeries (Fin 2) K} (hφ : NormLe ε φ) :
    NormLe ε (-φ) := fun p => by rw [map_neg, norm_neg]; exact hφ p

private lemma normLe_sub {ε : ℝ} {φ ψ : MvPowerSeries (Fin 2) K} (hφ : NormLe ε φ)
    (hψ : NormLe ε ψ) : NormLe ε (φ - ψ) := by
  rw [sub_eq_add_neg]; exact normLe_add hφ (normLe_neg hψ)

/-- Products: the convolution defining `coeff p (φ * ψ)` is an ultrametric sum of terms of
norm at most `ε * δ`. -/
private lemma normLe_mul {ε δ ζ : ℝ} {φ ψ : MvPowerSeries (Fin 2) K} (hφ : NormLe ε φ)
    (hψ : NormLe δ ψ) (h : ε * δ ≤ ζ) : NormLe ζ (φ * ψ) := by
  intro p
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    ((mul_nonneg (normLe_nonneg hφ) (normLe_nonneg hψ)).trans h) fun x _ => ?_
  rw [norm_mul]
  exact (mul_le_mul (hφ _) (hψ _) (norm_nonneg _) (normLe_nonneg hφ)).trans h

private lemma normLe_C {ε : ℝ} {v : K} (h : ‖v‖ ≤ ε) :
    NormLe ε (C v : MvPowerSeries (Fin 2) K) := fun p => by
  rw [coeff_C]
  split_ifs
  · exact h
  · simpa using (norm_nonneg v).trans h

private lemma normLe_one : NormLe (1 : ℝ) (1 : MvPowerSeries (Fin 2) K) := fun p => by
  rw [coeff_one]
  split_ifs <;> simp

private lemma normLe_X (s : Fin 2) : NormLe (1 : ℝ) (X s : MvPowerSeries (Fin 2) K) := fun p => by
  rw [coeff_X]
  split_ifs <;> simp

/-- Inverses of integral series with unit constant coefficient are integral: strong induction on
`p 0 + p 1` through the recurrence `MvPowerSeries.coeff_inv` (compare `Jacobs.rowInt_inv`). -/
private lemma normLe_inv {φ : MvPowerSeries (Fin 2) K} (hφ : NormLe 1 φ)
    (h1 : ‖constantCoeff φ‖ = 1) : NormLe 1 φ⁻¹ := by
  have key : ∀ N : ℕ, ∀ p : Fin 2 →₀ ℕ, p 0 + p 1 = N → ‖coeff p φ⁻¹‖ ≤ 1 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro p hp
      rw [coeff_inv]
      split_ifs with hp0
      · simp [norm_inv, h1]
      · rw [norm_mul, norm_neg, norm_inv, h1, inv_one, one_mul]
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x hx => ?_
        rw [Finset.mem_antidiagonal] at hx
        split_ifs with hlt
        · have hne : x.1 ≠ 0 := by
            rintro h
            rw [h, zero_add] at hx
            exact absurd hx (ne_of_lt hlt)
          have hpos : 0 < x.1 0 + x.1 1 := by
            rcases Nat.eq_zero_or_pos (x.1 0 + x.1 1) with h | h
            · exact absurd (fin2_eq_zero (by omega) (by omega)) hne
            · exact h
          have e0 : x.1 0 + x.2 0 = p 0 := by rw [← hx]; simp
          have e1 : x.1 1 + x.2 1 = p 1 := by rw [← hx]; simp
          rw [norm_mul]
          exact mul_le_one₀ (hφ _) (norm_nonneg _) (ih (x.2 0 + x.2 1) (by omega) x.2 rfl)
        · simp
  exact fun p => key _ p rfl

/-- First-order expansion: `A⁻¹ - B⁻¹ = -A⁻¹ (A - B) B⁻¹`. -/
private lemma normLe_inv_sub_inv {A B : MvPowerSeries (Fin 2) K} {δ ζ : ℝ}
    (hA : NormLe 1 A) (hB : NormLe 1 B) (hA0 : ‖constantCoeff A‖ = 1)
    (hB0 : ‖constantCoeff B‖ = 1) (h : NormLe δ (A - B)) (hζ : δ ≤ ζ) :
    NormLe ζ (A⁻¹ - B⁻¹) := by
  have hAc : constantCoeff A ≠ 0 := by
    intro hc; rw [hc, norm_zero] at hA0; exact zero_ne_one hA0
  have hBc : constantCoeff B ≠ 0 := by
    intro hc; rw [hc, norm_zero] at hB0; exact zero_ne_one hB0
  have h1 : A⁻¹ * A = 1 := MvPowerSeries.inv_mul_cancel _ hAc
  have h2 : B * B⁻¹ = 1 := MvPowerSeries.mul_inv_cancel _ hBc
  have key : A⁻¹ - B⁻¹ = -(A⁻¹ * (A - B) * B⁻¹) := by
    linear_combination (norm := ring_nf) B⁻¹ * h1 - A⁻¹ * h2
  rw [key]
  exact normLe_neg (normLe_mul (normLe_mul (normLe_inv hA hA0) h (le_of_eq (one_mul δ)))
    (normLe_inv hB hB0) (by rw [mul_one]; exact hζ))

/-- Second-order expansion: `A⁻¹ - B⁻¹ + B⁻¹ (A - B) B⁻¹ = A⁻¹ (A-B) B⁻¹ (A-B) B⁻¹`, whose
size is quadratic in `‖A - B‖`.  This is what turns the `θ`-linear model denominators of
[Jacobs, p. 39] into an exact computation, since `θ² = -3`. -/
private lemma normLe_inv_sub_inv_two {A B : MvPowerSeries (Fin 2) K} {δ ζ : ℝ}
    (hA : NormLe 1 A) (hB : NormLe 1 B) (hA0 : ‖constantCoeff A‖ = 1)
    (hB0 : ‖constantCoeff B‖ = 1) (h : NormLe δ (A - B)) (hζ : δ * δ ≤ ζ) :
    NormLe ζ (A⁻¹ - B⁻¹ + B⁻¹ * (A - B) * B⁻¹) := by
  have hAc : constantCoeff A ≠ 0 := by
    intro hc; rw [hc, norm_zero] at hA0; exact zero_ne_one hA0
  have hBc : constantCoeff B ≠ 0 := by
    intro hc; rw [hc, norm_zero] at hB0; exact zero_ne_one hB0
  have h1 : A⁻¹ * A = 1 := MvPowerSeries.inv_mul_cancel _ hAc
  have h2 : B * B⁻¹ = 1 := MvPowerSeries.mul_inv_cancel _ hBc
  have key : A⁻¹ * (A - B) * B⁻¹ = B⁻¹ - A⁻¹ := by
    linear_combination (norm := ring_nf) B⁻¹ * h1 - A⁻¹ * h2
  have expand : A⁻¹ - B⁻¹ + B⁻¹ * (A - B) * B⁻¹ =
      A⁻¹ * (A - B) * B⁻¹ * ((A - B) * B⁻¹) := by
    calc A⁻¹ - B⁻¹ + B⁻¹ * (A - B) * B⁻¹
        = B⁻¹ * (A - B) * B⁻¹ - (B⁻¹ - A⁻¹) := by ring
      _ = B⁻¹ * (A - B) * B⁻¹ - A⁻¹ * (A - B) * B⁻¹ := by rw [key]
      _ = (B⁻¹ - A⁻¹) * ((A - B) * B⁻¹) := by ring
      _ = A⁻¹ * (A - B) * B⁻¹ * ((A - B) * B⁻¹) := by rw [key]
  rw [expand]
  refine normLe_mul (normLe_mul (normLe_mul (normLe_inv hA hA0) h (le_of_eq (one_mul δ)))
    (normLe_inv hB hB0) (le_of_eq (mul_one δ)))
    (normLe_mul h (normLe_inv hB hB0) (le_of_eq (mul_one δ))) hζ

end NormLe

section Scaled

variable (t ν ω : K)

/-- The generating function of `N = D(1/3) M′₂,₂`, namely
`(1/(ω(2ω+1))) · H₂,₂(x/(3(2ω+1)), (2ω+1) y)` — the object [Jacobs, pp. 35–36] denotes
`H′₂,₂(x/3, y)`. -/
noncomputable def NgenFun : MvPowerSeries (Fin 2) K :=
  (ω * (2 * ω + 1))⁻¹ •
    diagRescale ((3 * (2 * ω + 1) : K))⁻¹ (2 * ω + 1) (M22genFun t ν ω)

/-- The target `−1/(1 − xy)` of [Jacobs, Theorem 2.14] — the geometric series
`−∑ₘ (xy)^m`. -/
noncomputable def negGeom : MvPowerSeries (Fin 2) K :=
  -(1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹

section Reduction

set_option linter.unusedSectionVars false

/-!
### Normalising `NgenFun` to three weight generating functions

Pushing `D(1/(3(2ω+1)))·—·D(2ω+1)` through `M22genFun` ([Jacobs, p. 36]) and applying
`diagRescale_weightGenFun` writes `NgenFun` as `∑ₖ cₖ · weightGenFun t γₖ` for the three
matrices below.  Writing `θ = 2ω + 1` (so `θ² = -3`), the joint `xy`-weight is
`(3θ)⁻¹ · θ = 1/3` exactly, so each `a`-entry gets divided by `3` and becomes a *unit*, while
the `b`- and `c`-entries acquire a single factor `θ`, i.e. have norm `‖3‖^{1/2}` — small, but
not small enough to be dropped, since each scalar `cₖ` has norm `‖3‖^{-1/2}`.
-/

/-- `γ₁ = rescaleMat (7/(12θ)) θ (ε₀,₂)`: the matrix of `h₀,₂` after the substitution. -/
private noncomputable def gam1 : Matrix (Fin 2) (Fin 2) K :=
  !![(ν - 1) / 12, 2 * (2 * ω + 1) / 7; 0, -(ν + 1) / 4]

/-- `γ₂ = rescaleMat (7/(30θ)) θ (ε₁,₂ first matrix)`.  (`1/θ = -θ/3` clears the denominator.) -/
private noncomputable def gam2 : Matrix (Fin 2) (Fin 2) K :=
  !![ν / 4, -((2 * ω + 1) * (ν - 2)) / 7;
     7 * (ν - 4) * (2 * ω + 1) / 144, -(3 * ν + 2) / 4]

/-- `γ₃ = rescaleMat (7/(30θ)) θ (ε₁,₂ second matrix)`. -/
private noncomputable def gam3 : Matrix (Fin 2) (Fin 2) K :=
  !![-(ν + 2) / 12, (2 * ω + 1) * (ν + 2) / 7;
     -(7 * (ν - 4) * (2 * ω + 1)) / 144, ν / 4]

/-- The reduction of `γ₁` modulo `𝔪₃`: `((ν-1)/12, 2θ/7; 0, -(ν+1)/4) ≡ (1, -θ; 0, 1)`. -/
private noncomputable def gmod1 : Matrix (Fin 2) (Fin 2) K := !![1, -(2 * ω + 1); 0, 1]

/-- The reduction of `γ₂` modulo `𝔪₃`. -/
private noncomputable def gmod2 : Matrix (Fin 2) (Fin 2) K := !![1, 2 * ω + 1; -(2 * ω + 1), 1]

/-- The reduction of `γ₃` modulo `𝔪₃`. -/
private noncomputable def gmod3 : Matrix (Fin 2) (Fin 2) K := !![1, 0; 2 * ω + 1, 1]

private lemma omega_ne_zero (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 0 := by
  intro h; rw [h] at hω; norm_num at hω

private lemma two_omega_add_one_ne_zero (hω : ω ^ 2 + ω + 1 = 0) : 2 * ω + 1 ≠ 0 := by
  intro h
  have hs := sq_two_omega_add_one hω
  rw [h] at hs
  norm_num at hs

/-- Composing two substitutions composes the two matrix rescalings. -/
private lemma rescaleMat_rescaleMat (α β α' β' : K) (γ : Matrix (Fin 2) (Fin 2) K) :
    rescaleMat α β (rescaleMat α' β' γ) = rescaleMat (α * α') (β * β') γ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rescaleMat] <;> ring

/-- Rescaling commutes with scalar multiplication. -/
private lemma diagRescale_smul (α β c : K) (F : MvPowerSeries (Fin 2) K) :
    diagRescale α β (c • F) = c • diagRescale α β F := by
  ext p
  simp only [coeff_diagRescale, MvPowerSeries.coeff_smul]
  ring

/-- **Step 1 of [Jacobs, Theorem 2.14]**: `NgenFun` is a sum of three weight generating
functions with explicit scalars of norm `‖3‖^{-1/2}`. -/
private lemma ngenFun_eq (hω : ω ^ 2 + ω + 1 = 0) :
    NgenFun t ν ω =
      C (ω * unitPow t 4 / (16 * (2 * ω + 1))) * weightGenFun t (gam1 ν ω)
        + C (unitPow t (-2) / (4 * (2 * ω + 1))) * weightGenFun t (gam2 ν ω)
        + C (unitPow t (-2) / (4 * (2 * ω + 1))) * weightGenFun t (gam3 ν ω) := by
  have hθ : (2 * ω + 1 : K) ≠ 0 := two_omega_add_one_ne_zero ω hω
  have hω0 : ω ≠ 0 := omega_ne_zero ω hω
  have h3' : (3 : K) ≠ 0 := by norm_num
  have hM1 : rescaleMat ((3 * (2 * ω + 1) : K)⁻¹ * (7 / 4)) ((2 * ω + 1) * 1) (eps02M ν)
      = gam1 ν ω := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rescaleMat, eps02M, gam1] <;> field_simp <;> ring
  have hM2 : rescaleMat ((3 * (2 * ω + 1) : K)⁻¹ * (7 / 10)) ((2 * ω + 1) * 1) (eps12M1 ν)
      = gam2 ν ω := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [rescaleMat, eps12M1, gam2]; field_simp; ring
    · simp [rescaleMat, eps12M1, gam2]; field_simp; ring
    · simp [rescaleMat, eps12M1, gam2]
      field_simp
      linear_combination (7680 - 1920 * ν) * hω
    · simp [rescaleMat, eps12M1, gam2]; field_simp; ring
  have hM3 : rescaleMat ((3 * (2 * ω + 1) : K)⁻¹ * (7 / 10)) ((2 * ω + 1) * 1) (eps12M2 ν)
      = gam3 ν ω := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [rescaleMat, eps12M2, gam3]; field_simp; ring
    · simp [rescaleMat, eps12M2, gam3]; field_simp
    · simp [rescaleMat, eps12M2, gam3]
      field_simp
      linear_combination (1920 * ν - 7680) * hω
    · simp [rescaleMat, eps12M2, gam3]; field_simp
  have hs1 : (ω * (2 * ω + 1) : K)⁻¹ * ((16 : K)⁻¹ * ω ^ 2 * unitPow t 4)
      = ω * unitPow t 4 / (16 * (2 * ω + 1)) := by field_simp
  have hs2 : (ω * (2 * ω + 1) : K)⁻¹ * ((4 : K)⁻¹ * ω * unitPow t (-2))
      = unitPow t (-2) / (4 * (2 * ω + 1)) := by field_simp
  simp only [NgenFun, M22genFun, h02, h12, diagRescale_add, diagRescale_smul,
    diagRescale_weightGenFun, rescaleMat_rescaleMat, hM1, hM2, hM3, smul_add, smul_smul,
    hs1, hs2]
  simp only [MvPowerSeries.smul_eq_C_mul]
  ring

/-! ### The `ν`-congruences and the norms of the entries -/

private lemma norm_three_pos' : (0 : ℝ) < ‖(3 : K)‖ := norm_pos_iff.mpr (by norm_num)

/-- `2695 - 13 = 2682 = 3² · 298`. -/
private lemma norm_nu_sub_thirteen (h3 : ‖(3 : K)‖ < 1)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) : ‖ν - 13‖ ≤ ‖(3 : K)‖ ^ 2 := by
  have h2682 : ‖(2682 : K)‖ = ‖(3 : K)‖ ^ 2 :=
    norm_ofNat_eq_pow h3 (n := 2682) (e := 2) (k := 298) (by norm_num) (by norm_num) (by norm_num)
  refine norm_le_of_sub (y := (2682 : K)) ?_ h2682.le
  rw [show ν - 13 - 2682 = ν - 2695 by ring]
  exact hνc.trans (pow_le_pow_of_le_one (norm_nonneg (3 : K)) h3.le (by norm_num))

/-- `2695 + 14 = 2709 = 3² · 301`. -/
private lemma norm_nu_add_fourteen (h3 : ‖(3 : K)‖ < 1)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) : ‖ν + 14‖ ≤ ‖(3 : K)‖ ^ 2 := by
  have h2709 : ‖(2709 : K)‖ = ‖(3 : K)‖ ^ 2 :=
    norm_ofNat_eq_pow h3 (n := 2709) (e := 2) (k := 301) (by norm_num) (by norm_num) (by norm_num)
  refine norm_le_of_sub (y := (2709 : K)) ?_ h2709.le
  rw [show ν + 14 - 2709 = ν - 2695 by ring]
  exact hνc.trans (pow_le_pow_of_le_one (norm_nonneg (3 : K)) h3.le (by norm_num))

/-- `7 · 2695 + 116 = 18981 = 3³ · 703`: the congruence behind `c ≡ ∓(2ω+1) mod 𝔪₃`. -/
private lemma norm_seven_nu_add (h3 : ‖(3 : K)‖ < 1)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) : ‖7 * ν + 116‖ ≤ ‖(3 : K)‖ ^ 3 := by
  have h7 : ‖(7 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 7) (by norm_num) (by norm_num)
  have h18981 : ‖(18981 : K)‖ = ‖(3 : K)‖ ^ 3 :=
    norm_ofNat_eq_pow h3 (n := 18981) (e := 3) (k := 703) (by norm_num) (by norm_num) (by norm_num)
  refine norm_le_of_sub (y := (18981 : K)) ?_ h18981.le
  rw [show 7 * ν + 116 - 18981 = 7 * (ν - 2695) by ring, norm_mul, h7, one_mul]
  exact hνc.trans (pow_le_pow_of_le_one (norm_nonneg (3 : K)) h3.le (by norm_num))

/-! ### Norm bounds for the three factors of a weight generating function -/

private lemma linSeries_sub (γ δ : Matrix (Fin 2) (Fin 2) K) :
    linSeries γ - linSeries δ = C (γ 1 1 - δ 1 1) + C (γ 1 0 - δ 1 0) * X 0 := by
  simp only [linSeries, map_sub]; ring

private lemma quadSeries_sub (γ δ : Matrix (Fin 2) (Fin 2) K) :
    quadSeries γ - quadSeries δ = C (γ 1 1 - δ 1 1) + C (γ 1 0 - δ 1 0) * X 0
      - C (γ 0 0 - δ 0 0) * (X 0 * X 1) - C (γ 0 1 - δ 0 1) * X 1 := by
  simp only [quadSeries, map_sub]; ring

private lemma normLe_linForm {ε : ℝ} {a b : K} (ha : ‖a‖ ≤ ε) (hb : ‖b‖ ≤ ε) :
    NormLe ε (C a + C b * X 0 : MvPowerSeries (Fin 2) K) :=
  normLe_add (normLe_C ha) (normLe_mul (normLe_C hb) (normLe_X 0) (le_of_eq (mul_one ε)))

private lemma normLe_quadForm {ε : ℝ} {a b c d : K} (ha : ‖a‖ ≤ ε) (hb : ‖b‖ ≤ ε)
    (hc : ‖c‖ ≤ ε) (hd : ‖d‖ ≤ ε) :
    NormLe ε (C a + C b * X 0 - C c * (X 0 * X 1) - C d * X 1 : MvPowerSeries (Fin 2) K) :=
  normLe_sub (normLe_sub (normLe_linForm ha hb)
      (normLe_mul (normLe_C hc)
        (normLe_mul (normLe_X 0) (normLe_X 1) (le_of_eq (mul_one 1))) (le_of_eq (mul_one ε))))
    (normLe_mul (normLe_C hd) (normLe_X 1) (le_of_eq (mul_one ε)))

/-- `κ(cx + d) ≡ 1 mod t·𝔪₃^{1/2}`: the constant term is `d^t ≡ 1` and the `x`-tails carry the
small ratio `c/d` ([Jacobs, p. 38]'s "`1 + (2ω+1)t𝒪₃[[x]]`"). -/
private lemma normLe_kappaSeries_sub_one (h3 : ‖(3 : K)‖ < 1) {c d θ : K} (ht : ‖t‖ < 1)
    (hθsq : ‖θ‖ ^ 2 = ‖(3 : K)‖) (hd1 : ‖d - 1‖ ≤ ‖(3 : K)‖)
    (hcd : ‖c / d‖ ^ 2 ≤ ‖(3 : K)‖) :
    NormLe (‖t‖ * ‖θ‖) (kappaSeries₂ t c d - 1) := by
  have hθnn : 0 ≤ ‖θ‖ := norm_nonneg _
  have hθ1 : ‖θ‖ ≤ 1 := by nlinarith [h3.le, hθsq]
  have hu : ‖unitPow t d‖ ≤ 1 := norm_unitPow_le_one h3 ht hd1
  have hnn : 0 ≤ ‖t‖ * ‖θ‖ := mul_nonneg (norm_nonneg _) hθnn
  intro p
  rw [map_sub, coeff_kappaSeries₂, coeff_one]
  rcases eq_or_ne p 0 with rfl | hp
  · simp only [Finsupp.coe_zero, Pi.zero_apply, binomialCoeff_zero, pow_zero, mul_one]
    calc ‖unitPow t d - 1‖ ≤ ‖t‖ * ‖(3 : K)‖ := norm_unitPow_sub_one_le h3 ht hd1
      _ = ‖t‖ * (‖θ‖ * ‖θ‖) := by rw [← sq, hθsq]
      _ ≤ ‖t‖ * ‖θ‖ := by nlinarith [norm_nonneg t]
  · rw [if_neg hp, sub_zero]
    by_cases hp1 : p 1 = 0
    · rw [if_pos hp1]
      have hp0 : p 0 ≠ 0 := fun h => hp (fin2_eq_zero h hp1)
      have hsq := sq_norm_binomialCoeff_mul_pow_le h3 ht hcd hp0
      have hb : ‖binomialCoeff t (p 0) * (c / d) ^ p 0‖ ≤ ‖t‖ * ‖θ‖ := by
        refine (pow_le_pow_iff_left₀ (norm_nonneg _) hnn two_ne_zero).mp ?_
        calc ‖binomialCoeff t (p 0) * (c / d) ^ p 0‖ ^ 2 ≤ ‖t‖ ^ 2 * ‖(3 : K)‖ := hsq
          _ = (‖t‖ * ‖θ‖) ^ 2 := by rw [mul_pow, hθsq]
      calc ‖unitPow t d * (binomialCoeff t (p 0) * (c / d) ^ p 0)‖
          = ‖unitPow t d‖ * ‖binomialCoeff t (p 0) * (c / d) ^ p 0‖ := norm_mul _ _
        _ ≤ 1 * (‖t‖ * ‖θ‖) := mul_le_mul hu hb (norm_nonneg _) zero_le_one
        _ = ‖t‖ * ‖θ‖ := one_mul _
    · rw [if_neg hp1, norm_zero]
      exact hnn

/-- **Step 2**: one weight generating function against the model attached to its reduction
modulo `𝔪₃`.  All three factors are compared separately: `κ ≡ 1`, and the two denominators
change by `O(‖3‖)`, which the first-order inverse expansion transports. -/
private lemma normLe_weightGenFun_sub_model (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1)
    {γ δ : Matrix (Fin 2) (Fin 2) K} {θ : K} {ε : ℝ} (hθsq : ‖θ‖ ^ 2 = ‖(3 : K)‖)
    (h00 : ‖γ 0 0 - δ 0 0‖ ≤ ‖(3 : K)‖) (h01 : ‖γ 0 1 - δ 0 1‖ ≤ ‖(3 : K)‖)
    (h10 : ‖γ 1 0 - δ 1 0‖ ≤ ‖(3 : K)‖) (h11 : ‖γ 1 1 - δ 1 1‖ ≤ ‖(3 : K)‖)
    (hδ00 : ‖δ 0 0‖ ≤ 1) (hδ01 : ‖δ 0 1‖ ≤ 1) (hδ10 : ‖δ 1 0‖ ≤ 1) (hδ11 : δ 1 1 = 1)
    (hcd : ‖γ 1 0 / γ 1 1‖ ^ 2 ≤ ‖(3 : K)‖)
    (hε1 : ‖t‖ * ‖θ‖ ≤ ε) (hε2 : ‖(3 : K)‖ ≤ ε) :
    NormLe ε (weightGenFun t γ - (linSeries δ)⁻¹ * (quadSeries δ)⁻¹) := by
  have h31 : ‖(3 : K)‖ ≤ 1 := h3.le
  -- the entries of `γ` are integral and `γ 1 1` is a unit
  have hγ11' : ‖γ 1 1 - 1‖ ≤ ‖(3 : K)‖ := by rw [← hδ11]; exact h11
  have hγ11 : ‖γ 1 1‖ = 1 := by
    have : ‖γ 1 1 - 1‖ < ‖(1 : K)‖ := by rw [norm_one]; exact lt_of_le_of_lt hγ11' h3
    rw [norm_eq_of_sub_lt this, norm_one]
  have hγ00 : ‖γ 0 0‖ ≤ 1 := norm_le_of_sub (h00.trans h31) hδ00
  have hγ01 : ‖γ 0 1‖ ≤ 1 := norm_le_of_sub (h01.trans h31) hδ01
  have hγ10 : ‖γ 1 0‖ ≤ 1 := norm_le_of_sub (h10.trans h31) hδ10
  have hδ11' : ‖δ 1 1‖ = 1 := by rw [hδ11, norm_one]
  -- integrality of the four denominators
  have hLγ : NormLe 1 (linSeries γ) := normLe_linForm hγ11.le hγ10
  have hQγ : NormLe 1 (quadSeries γ) := normLe_quadForm hγ11.le hγ10 hγ00 hγ01
  have hLδ : NormLe 1 (linSeries δ) := normLe_linForm hδ11'.le hδ10
  have hQδ : NormLe 1 (quadSeries δ) := normLe_quadForm hδ11'.le hδ10 hδ00 hδ01
  have hcLγ : ‖constantCoeff (linSeries γ)‖ = 1 := by rw [constantCoeff_linSeries]; exact hγ11
  have hcQγ : ‖constantCoeff (quadSeries γ)‖ = 1 := by rw [constantCoeff_quadSeries]; exact hγ11
  have hcLδ : ‖constantCoeff (linSeries δ)‖ = 1 := by rw [constantCoeff_linSeries]; exact hδ11'
  have hcQδ : ‖constantCoeff (quadSeries δ)‖ = 1 := by rw [constantCoeff_quadSeries]; exact hδ11'
  -- the two denominators agree modulo `𝔪₃`
  have hLd : NormLe ‖(3 : K)‖ (linSeries γ - linSeries δ) := by
    rw [linSeries_sub]; exact normLe_linForm h11 h10
  have hQd : NormLe ‖(3 : K)‖ (quadSeries γ - quadSeries δ) := by
    rw [quadSeries_sub]; exact normLe_quadForm h11 h10 h00 h01
  have hLinv : NormLe ε ((linSeries γ)⁻¹ - (linSeries δ)⁻¹) :=
    normLe_inv_sub_inv hLγ hLδ hcLγ hcLδ hLd hε2
  have hQinv : NormLe ε ((quadSeries γ)⁻¹ - (quadSeries δ)⁻¹) :=
    normLe_inv_sub_inv hQγ hQδ hcQγ hcQδ hQd hε2
  have hκ : NormLe ε (kappaSeries₂ t (γ 1 0) (γ 1 1) - 1) :=
    normLe_mono (normLe_kappaSeries_sub_one t h3 ht hθsq hγ11' hcd) hε1
  have hLγi : NormLe 1 (linSeries γ)⁻¹ := normLe_inv hLγ hcLγ
  have hQγi : NormLe 1 (quadSeries γ)⁻¹ := normLe_inv hQγ hcQγ
  have hLδi : NormLe 1 (linSeries δ)⁻¹ := normLe_inv hLδ hcLδ
  have key : weightGenFun t γ - (linSeries δ)⁻¹ * (quadSeries δ)⁻¹ =
      (kappaSeries₂ t (γ 1 0) (γ 1 1) - 1) * ((linSeries γ)⁻¹ * (quadSeries γ)⁻¹)
        + ((linSeries γ)⁻¹ - (linSeries δ)⁻¹) * (quadSeries γ)⁻¹
        + (linSeries δ)⁻¹ * ((quadSeries γ)⁻¹ - (quadSeries δ)⁻¹) := by
    rw [weightGenFun]; ring
  rw [key]
  refine normLe_add (normLe_add ?_ ?_) ?_
  · exact normLe_mul hκ (normLe_mul hLγi hQγi (le_of_eq (mul_one 1))) (le_of_eq (mul_one ε))
  · exact normLe_mul hLinv hQγi (le_of_eq (mul_one ε))
  · exact normLe_mul hLδi hQinv (le_of_eq (one_mul ε))

/-! ### The three instances

The entries of `γₖ` against their reductions `γ̃ₖ`, using the table
`v₃(ν-1) = v₃(ν+2) = 1`, `v₃(ν-4) ≥ 2`, `v₃(ν+5) ≥ 1`, `v₃(7ν+116) ≥ 3`. -/

private lemma normLe_term1 (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) (hω : ω ^ 2 + ω + 1 = 0) {ε : ℝ}
    (hε1 : ‖t‖ * ‖2 * ω + 1‖ ≤ ε) (hε2 : ‖(3 : K)‖ ≤ ε) :
    NormLe ε (weightGenFun t (gam1 ν ω)
      - (linSeries (gmod1 ω))⁻¹ * (quadSeries (gmod1 ω))⁻¹) := by
  have h3pos : (0 : ℝ) < ‖(3 : K)‖ := norm_three_pos'
  have hθsq : ‖2 * ω + 1‖ ^ 2 = ‖(3 : K)‖ := sq_norm_two_omega_add_one hω
  have hθ1 : ‖2 * ω + 1‖ ≤ 1 := by nlinarith [h3.le, norm_nonneg (2 * ω + 1 : K)]
  have hn4 : ‖(4 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 4) (by norm_num) (by norm_num)
  have hn7 : ‖(7 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 7) (by norm_num) (by norm_num)
  have hn9 : ‖(9 : K)‖ = ‖(3 : K)‖ ^ 2 :=
    norm_ofNat_eq_pow h3 (n := 9) (e := 2) (k := 1) (by norm_num) (by norm_num) (by norm_num)
  have hn12 : ‖(12 : K)‖ = ‖(3 : K)‖ ^ 1 :=
    norm_ofNat_eq_pow h3 (n := 12) (e := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num)
  rw [pow_one] at hn12
  have e00 : gam1 ν ω 0 0 = (ν - 1) / 12 := by simp [gam1]
  have e01 : gam1 ν ω 0 1 = 2 * (2 * ω + 1) / 7 := by simp [gam1]
  have e10 : gam1 ν ω 1 0 = 0 := by simp [gam1]
  have e11 : gam1 ν ω 1 1 = -(ν + 1) / 4 := by simp [gam1]
  have m00 : gmod1 ω 0 0 = 1 := by simp [gmod1]
  have m01 : gmod1 ω 0 1 = -(2 * ω + 1) := by simp [gmod1]
  have m10 : gmod1 ω 1 0 = 0 := by simp [gmod1]
  have m11 : gmod1 ω 1 1 = 1 := by simp [gmod1]
  refine normLe_weightGenFun_sub_model t h3 ht hθsq ?_ ?_ ?_ ?_ ?_ ?_ ?_ m11 ?_ hε1 hε2
  · rw [e00, m00, show ((ν - 1) / 12 - 1 : K) = (ν - 13) / 12 by ring, norm_div, hn12,
      div_le_iff₀ h3pos]
    calc ‖ν - 13‖ ≤ ‖(3 : K)‖ ^ 2 := norm_nu_sub_thirteen ν h3 hνc
      _ = ‖(3 : K)‖ * ‖(3 : K)‖ := sq _
  · rw [e01, m01, show (2 * (2 * ω + 1) / 7 - -(2 * ω + 1) : K) = (2 * ω + 1) * 9 / 7 by ring,
      norm_div, norm_mul, hn7, hn9, div_one]
    nlinarith [norm_nonneg (2 * ω + 1 : K), h3.le, h3pos]
  · rw [e10, m10, sub_zero, norm_zero]; exact h3pos.le
  · rw [e11, m11, show (-(ν + 1) / 4 - 1 : K) = -((ν + 5) / 4) by ring, norm_neg, norm_div, hn4,
      div_one]
    exact norm_nu_add_five h3 hνc
  · rw [m00, norm_one]
  · rw [m01, norm_neg]; exact hθ1
  · rw [m10, norm_zero]; exact zero_le_one
  · rw [e10, zero_div, norm_zero]
    simp

private lemma normLe_term2 (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) (hω : ω ^ 2 + ω + 1 = 0) {ε : ℝ}
    (hε1 : ‖t‖ * ‖2 * ω + 1‖ ≤ ε) (hε2 : ‖(3 : K)‖ ≤ ε) :
    NormLe ε (weightGenFun t (gam2 ν ω)
      - (linSeries (gmod2 ω))⁻¹ * (quadSeries (gmod2 ω))⁻¹) := by
  have h3pos : (0 : ℝ) < ‖(3 : K)‖ := norm_three_pos'
  have hθsq : ‖2 * ω + 1‖ ^ 2 = ‖(3 : K)‖ := sq_norm_two_omega_add_one hω
  have hθ1 : ‖2 * ω + 1‖ ≤ 1 := by nlinarith [h3.le, norm_nonneg (2 * ω + 1 : K)]
  have hn4 : ‖(4 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 4) (by norm_num) (by norm_num)
  have hn7 : ‖(7 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 7) (by norm_num) (by norm_num)
  have hn144 : ‖(144 : K)‖ = ‖(3 : K)‖ ^ 2 :=
    norm_ofNat_eq_pow h3 (n := 144) (e := 2) (k := 16) (by norm_num) (by norm_num) (by norm_num)
  have hν4 : ‖ν - 4‖ ≤ ‖(3 : K)‖ ^ 2 := norm_nu_sub_four h3 hνc
  have e00 : gam2 ν ω 0 0 = ν / 4 := by simp [gam2]
  have e01 : gam2 ν ω 0 1 = -((2 * ω + 1) * (ν - 2)) / 7 := by simp [gam2]
  have e10 : gam2 ν ω 1 0 = 7 * (ν - 4) * (2 * ω + 1) / 144 := by simp [gam2]
  have e11 : gam2 ν ω 1 1 = -(3 * ν + 2) / 4 := by simp [gam2]
  have m00 : gmod2 ω 0 0 = 1 := by simp [gmod2]
  have m01 : gmod2 ω 0 1 = 2 * ω + 1 := by simp [gmod2]
  have m10 : gmod2 ω 1 0 = -(2 * ω + 1) := by simp [gmod2]
  have m11 : gmod2 ω 1 1 = 1 := by simp [gmod2]
  have hd : ‖gam2 ν ω 1 1‖ = 1 := by
    rw [e11, show (-(3 * ν + 2) / 4 : K) = -((3 * ν + 2) / 4) by ring, norm_neg, norm_div, hn4,
      div_one, norm_three_mul_nu_add_two h3 hνc]
  have hc : ‖gam2 ν ω 1 0‖ = ‖ν - 4‖ * ‖2 * ω + 1‖ / ‖(3 : K)‖ ^ 2 := by
    rw [e10, norm_div, hn144, norm_mul, norm_mul, hn7, one_mul]
  refine normLe_weightGenFun_sub_model t h3 ht hθsq ?_ ?_ ?_ ?_ ?_ ?_ ?_ m11 ?_ hε1 hε2
  · rw [e00, m00, show (ν / 4 - 1 : K) = (ν - 4) / 4 by ring, norm_div, hn4, div_one]
    nlinarith [h3.le, h3pos, norm_nonneg (ν - 4 : K)]
  · rw [e01, m01,
      show (-((2 * ω + 1) * (ν - 2)) / 7 - (2 * ω + 1) : K) = -((2 * ω + 1) * (ν + 5)) / 7 by ring,
      norm_div, hn7, div_one, norm_neg, norm_mul]
    nlinarith [norm_nu_add_five h3 hνc, norm_nonneg (2 * ω + 1 : K), norm_nonneg (ν + 5 : K),
      h3pos.le]
  · rw [e10, m10,
      show (7 * (ν - 4) * (2 * ω + 1) / 144 - -(2 * ω + 1) : K)
        = (2 * ω + 1) * (7 * ν + 116) / 144 by ring, norm_div, hn144, norm_mul,
      div_le_iff₀ (by positivity)]
    have h116 : ‖7 * ν + 116‖ ≤ ‖(3 : K)‖ ^ 3 := norm_seven_nu_add ν h3 hνc
    nlinarith [norm_nonneg (2 * ω + 1 : K), norm_nonneg (7 * ν + 116 : K), h3pos, h3.le]
  · rw [e11, m11, show (-(3 * ν + 2) / 4 - 1 : K) = -(3 * (ν + 2)) / 4 by ring, norm_div, hn4,
      div_one, norm_neg, norm_mul]
    nlinarith [norm_nu_add_two h3 hνc, h3pos.le, h3.le, norm_nonneg (ν + 2 : K)]
  · rw [m00, norm_one]
  · rw [m01]; exact hθ1
  · rw [m10, norm_neg]; exact hθ1
  · rw [norm_div, hd, div_one, hc, div_pow, div_le_iff₀ (by positivity), mul_pow, hθsq]
    nlinarith [pow_le_pow_left₀ (norm_nonneg (ν - 4 : K)) hν4 2, h3pos]

private lemma normLe_term3 (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) (hω : ω ^ 2 + ω + 1 = 0) {ε : ℝ}
    (hε1 : ‖t‖ * ‖2 * ω + 1‖ ≤ ε) (hε2 : ‖(3 : K)‖ ≤ ε) :
    NormLe ε (weightGenFun t (gam3 ν ω)
      - (linSeries (gmod3 ω))⁻¹ * (quadSeries (gmod3 ω))⁻¹) := by
  have h3pos : (0 : ℝ) < ‖(3 : K)‖ := norm_three_pos'
  have hθsq : ‖2 * ω + 1‖ ^ 2 = ‖(3 : K)‖ := sq_norm_two_omega_add_one hω
  have hθ1 : ‖2 * ω + 1‖ ≤ 1 := by nlinarith [h3.le, norm_nonneg (2 * ω + 1 : K)]
  have hn4 : ‖(4 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 4) (by norm_num) (by norm_num)
  have hn7 : ‖(7 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 7) (by norm_num) (by norm_num)
  have hn12 : ‖(12 : K)‖ = ‖(3 : K)‖ ^ 1 :=
    norm_ofNat_eq_pow h3 (n := 12) (e := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num)
  rw [pow_one] at hn12
  have hn144 : ‖(144 : K)‖ = ‖(3 : K)‖ ^ 2 :=
    norm_ofNat_eq_pow h3 (n := 144) (e := 2) (k := 16) (by norm_num) (by norm_num) (by norm_num)
  have hν4 : ‖ν - 4‖ ≤ ‖(3 : K)‖ ^ 2 := norm_nu_sub_four h3 hνc
  have e00 : gam3 ν ω 0 0 = -(ν + 2) / 12 := by simp [gam3]
  have e01 : gam3 ν ω 0 1 = (2 * ω + 1) * (ν + 2) / 7 := by simp [gam3]
  have e10 : gam3 ν ω 1 0 = -(7 * (ν - 4) * (2 * ω + 1)) / 144 := by simp [gam3]
  have e11 : gam3 ν ω 1 1 = ν / 4 := by simp [gam3]
  have m00 : gmod3 ω 0 0 = 1 := by simp [gmod3]
  have m01 : gmod3 ω 0 1 = 0 := by simp [gmod3]
  have m10 : gmod3 ω 1 0 = 2 * ω + 1 := by simp [gmod3]
  have m11 : gmod3 ω 1 1 = 1 := by simp [gmod3]
  have hd : ‖gam3 ν ω 1 1‖ = 1 := by rw [e11, norm_div, hn4, div_one, norm_nu h3 hνc]
  have hc : ‖gam3 ν ω 1 0‖ = ‖ν - 4‖ * ‖2 * ω + 1‖ / ‖(3 : K)‖ ^ 2 := by
    rw [e10, norm_div, hn144, norm_neg, norm_mul, norm_mul, hn7, one_mul]
  refine normLe_weightGenFun_sub_model t h3 ht hθsq ?_ ?_ ?_ ?_ ?_ ?_ ?_ m11 ?_ hε1 hε2
  · rw [e00, m00, show (-(ν + 2) / 12 - 1 : K) = -((ν + 14) / 12) by ring, norm_neg, norm_div,
      hn12, div_le_iff₀ h3pos]
    calc ‖ν + 14‖ ≤ ‖(3 : K)‖ ^ 2 := norm_nu_add_fourteen ν h3 hνc
      _ = ‖(3 : K)‖ * ‖(3 : K)‖ := sq _
  · rw [e01, m01, sub_zero, norm_div, hn7, div_one, norm_mul]
    nlinarith [norm_nu_add_two h3 hνc, norm_nonneg (2 * ω + 1 : K), norm_nonneg (ν + 2 : K),
      h3pos.le]
  · rw [e10, m10,
      show (-(7 * (ν - 4) * (2 * ω + 1)) / 144 - (2 * ω + 1) : K)
        = -((2 * ω + 1) * (7 * ν + 116)) / 144 by ring, norm_div, hn144, norm_neg, norm_mul,
      div_le_iff₀ (by positivity)]
    have h116 : ‖7 * ν + 116‖ ≤ ‖(3 : K)‖ ^ 3 := norm_seven_nu_add ν h3 hνc
    nlinarith [norm_nonneg (2 * ω + 1 : K), norm_nonneg (7 * ν + 116 : K), h3pos, h3.le]
  · rw [e11, m11, show (ν / 4 - 1 : K) = (ν - 4) / 4 by ring, norm_div, hn4, div_one]
    nlinarith [h3.le, h3pos, norm_nonneg (ν - 4 : K)]
  · rw [m00, norm_one]
  · rw [m01, norm_zero]; exact zero_le_one
  · rw [m10]; exact hθ1
  · rw [norm_div, hd, div_one, hc, div_pow, div_le_iff₀ (by positivity), mul_pow, hθsq]
    nlinarith [pow_le_pow_left₀ (norm_nonneg (ν - 4 : K)) hν4 2, h3pos]

/-! ### The residue computation

The three models are `θ`-linear perturbations of `u = 1 - xy`, so the second-order expansion of
`φ ↦ φ⁻¹` computes them modulo `θ² = -3`.  The `θ`-linear terms then cancel against each other
and against `ω + 2 + ωθ = 2(ω² + ω + 1) = 0`, leaving `θ(1-ω)(Q + yQ²)` of norm `‖3‖`
([Jacobs, p. 39]: "divide by `3⁶(2ω+1)` and reduce mod `𝔪₃`"). -/

/-- The first-order model of `(linSeries δ)⁻¹ (quadSeries δ)⁻¹` for `δ = (1, b; c, 1)`. -/
private noncomputable def appr (c b : K) (Q : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 2) K :=
  (1 - C c * X 0) * (Q - (C c * X 0 - C b * X 1) * (Q * Q))

private lemma normLe_model_one (h3 : ‖(3 : K)‖ < 1) {δ : Matrix (Fin 2) (Fin 2) K} {θ : K}
    (hθsq : ‖θ‖ ^ 2 = ‖(3 : K)‖) (hδ00 : δ 0 0 = 1) (hδ11 : δ 1 1 = 1)
    (hb : ‖δ 0 1‖ ≤ ‖θ‖) (hc : ‖δ 1 0‖ ≤ ‖θ‖) :
    NormLe 1 ((linSeries δ)⁻¹ * (quadSeries δ)⁻¹) := by
  have hθ1 : ‖θ‖ ≤ 1 := by nlinarith [h3.le, norm_nonneg θ]
  have hδ11' : ‖δ 1 1‖ = 1 := by rw [hδ11, norm_one]
  refine normLe_mul (normLe_inv (normLe_linForm hδ11'.le (hc.trans hθ1)) ?_)
    (normLe_inv (normLe_quadForm hδ11'.le (hc.trans hθ1) (by rw [hδ00, norm_one]) (hb.trans hθ1))
      ?_) (le_of_eq (mul_one 1))
  · rw [constantCoeff_linSeries]; exact hδ11'
  · rw [constantCoeff_quadSeries]; exact hδ11'

private lemma normLe_model_expand (h3 : ‖(3 : K)‖ < 1) {δ : Matrix (Fin 2) (Fin 2) K} {θ : K}
    (hθsq : ‖θ‖ ^ 2 = ‖(3 : K)‖) (hδ00 : δ 0 0 = 1) (hδ11 : δ 1 1 = 1)
    (hb : ‖δ 0 1‖ ≤ ‖θ‖) (hc : ‖δ 1 0‖ ≤ ‖θ‖) :
    NormLe ‖(3 : K)‖ ((linSeries δ)⁻¹ * (quadSeries δ)⁻¹
      - appr (δ 1 0) (δ 0 1) (1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹) := by
  have hθnn : 0 ≤ ‖θ‖ := norm_nonneg _
  have hθ1 : ‖θ‖ ≤ 1 := by nlinarith [h3.le]
  have hu : NormLe 1 (1 - X 0 * X 1 : MvPowerSeries (Fin 2) K) :=
    normLe_sub normLe_one (normLe_mul (normLe_X 0) (normLe_X 1) (le_of_eq (mul_one 1)))
  have hcu : ‖constantCoeff (1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)‖ = 1 := by simp
  have hQ : NormLe 1 (1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹ := normLe_inv hu hcu
  have hδ11' : ‖δ 1 1‖ = 1 := by rw [hδ11, norm_one]
  have hL : NormLe 1 (linSeries δ) := normLe_linForm hδ11'.le (hc.trans hθ1)
  have hQd : NormLe 1 (quadSeries δ) :=
    normLe_quadForm hδ11'.le (hc.trans hθ1) (by rw [hδ00, norm_one]) (hb.trans hθ1)
  have hcL : ‖constantCoeff (linSeries δ)‖ = 1 := by rw [constantCoeff_linSeries]; exact hδ11'
  have hcQ : ‖constantCoeff (quadSeries δ)‖ = 1 := by rw [constantCoeff_quadSeries]; exact hδ11'
  have hcone : ‖constantCoeff (1 : MvPowerSeries (Fin 2) K)‖ = 1 := by simp
  have hθmul : ‖θ‖ * ‖θ‖ ≤ ‖(3 : K)‖ := by rw [← sq, hθsq]
  have hnDL : NormLe ‖θ‖ (linSeries δ - 1) := by
    rw [show linSeries δ - 1 = C (δ 1 0) * X 0 by rw [linSeries, hδ11, map_one]; ring]
    exact normLe_mul (normLe_C hc) (normLe_X 0) (le_of_eq (mul_one _))
  have hnDQ : NormLe ‖θ‖ (quadSeries δ - (1 - X 0 * X 1)) := by
    rw [show quadSeries δ - (1 - X 0 * X 1) = C (δ 1 0) * X 0 - C (δ 0 1) * X 1 by
      rw [quadSeries, hδ00, hδ11, map_one]; ring]
    exact normLe_sub (normLe_mul (normLe_C hc) (normLe_X 0) (le_of_eq (mul_one _)))
      (normLe_mul (normLe_C hb) (normLe_X 1) (le_of_eq (mul_one _)))
  -- the two second-order expansions
  have hexpL : NormLe ‖(3 : K)‖ ((linSeries δ)⁻¹ - (1 - C (δ 1 0) * X 0)) := by
    have h := normLe_inv_sub_inv_two hL normLe_one hcL hcone hnDL hθmul
    rw [inv_one, one_mul, mul_one,
      show linSeries δ - 1 = C (δ 1 0) * X 0 by rw [linSeries, hδ11, map_one]; ring] at h
    exact normLe_mono (by rw [show (linSeries δ)⁻¹ - (1 - C (δ 1 0) * X 0)
      = (linSeries δ)⁻¹ - 1 + C (δ 1 0) * X 0 by ring]; exact h) le_rfl
  have hexpQ : NormLe ‖(3 : K)‖ ((quadSeries δ)⁻¹
      - ((1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹
        - (C (δ 1 0) * X 0 - C (δ 0 1) * X 1) *
          ((1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹ *
            (1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹))) := by
    have h := normLe_inv_sub_inv_two hQd hu hcQ hcu hnDQ hθmul
    rw [show quadSeries δ - (1 - X 0 * X 1) = C (δ 1 0) * X 0 - C (δ 0 1) * X 1 by
      rw [quadSeries, hδ00, hδ11, map_one]; ring] at h
    refine normLe_mono (?_ : NormLe ‖(3 : K)‖ _) le_rfl
    rw [show (quadSeries δ)⁻¹ - ((1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹
        - (C (δ 1 0) * X 0 - C (δ 0 1) * X 1) *
          ((1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹ *
            (1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹))
      = (quadSeries δ)⁻¹ - (1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹
        + (1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹ *
          (C (δ 1 0) * X 0 - C (δ 0 1) * X 1) *
          (1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹ by ring]
    exact h
  -- the product
  have hLmod : NormLe 1 (1 - C (δ 1 0) * X 0 : MvPowerSeries (Fin 2) K) :=
    normLe_sub normLe_one (normLe_mul (normLe_C (hc.trans hθ1)) (normLe_X 0) (le_of_eq (mul_one 1)))
  have key : (linSeries δ)⁻¹ * (quadSeries δ)⁻¹
      - appr (δ 1 0) (δ 0 1) (1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹
      = ((linSeries δ)⁻¹ - (1 - C (δ 1 0) * X 0)) * (quadSeries δ)⁻¹
        + (1 - C (δ 1 0) * X 0) * ((quadSeries δ)⁻¹
          - ((1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹
            - (C (δ 1 0) * X 0 - C (δ 0 1) * X 1) *
              ((1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹ *
                (1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹))) := by
    rw [appr]; ring
  rw [key]
  exact normLe_add (normLe_mul hexpL (normLe_inv hQd hcQ) (le_of_eq (mul_one _)))
    (normLe_mul hLmod hexpQ (le_of_eq (one_mul _)))

/-- The exact polynomial identity behind [Jacobs, Theorem 2.14]: with `θ = 2ω + 1` the three
first-order models sum to `θ(1-ω)(Q + yQ²)` plus a multiple of `θ² = -3`.  The `Q`-coefficient
is `ω + 2 + ωθ = 2(ω² + ω + 1) = 0` and the `θ`-linear `Q²`-terms cancel. -/
private lemma bracket_identity (Q : MvPowerSeries (Fin 2) K) (hω : ω ^ 2 + ω + 1 = 0) :
    C ω * appr 0 (-(2 * ω + 1)) Q + appr (-(2 * ω + 1)) (2 * ω + 1) Q + appr (2 * ω + 1) 0 Q
        + C (2 * ω + 1) * Q
      = C ((2 * ω + 1) * (1 - ω)) * (Q + X 1 * (Q * Q))
        + C (-6 : K) * (X 0 * X 0 * (Q * Q)) + C (-3 : K) * (X 0 * X 1 * (Q * Q)) := by
  have hw : (C ω : MvPowerSeries (Fin 2) K) ^ 2 + C ω + 1 = 0 := by
    have h : (C ω : MvPowerSeries (Fin 2) K) ^ 2 + C ω + 1 = C (ω ^ 2 + ω + 1) := by simp
    rw [h, hω, map_zero]
  simp only [appr, map_neg, map_zero, map_mul, map_sub, map_add, map_one, map_ofNat]
  linear_combination (norm := ring_nf)
    (2 * Q + 4 * (X 0 * X 0 + X 0 * X 0 + X 0 * X 1) * (Q * Q)) * hw

/-- **Step 3**: the three models plus `θ · (1 - xy)⁻¹` are `≡ 0 mod 𝔪₃` — the residue
computation of [Jacobs, p. 39], whose output `-(x²y² + xy + 1)/(1 - x³y³) = -1/(1 - xy)` is
here the surviving `(1 - xy)⁻¹` in `NgenFun - negGeom`. -/
private lemma normLe_model_sum (h3 : ‖(3 : K)‖ < 1) (hω : ω ^ 2 + ω + 1 = 0) :
    NormLe ‖(3 : K)‖
      (C ω * ((linSeries (gmod1 ω))⁻¹ * (quadSeries (gmod1 ω))⁻¹)
        + (linSeries (gmod2 ω))⁻¹ * (quadSeries (gmod2 ω))⁻¹
        + (linSeries (gmod3 ω))⁻¹ * (quadSeries (gmod3 ω))⁻¹
        + C (2 * ω + 1) * (1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹) := by
  have h3pos : (0 : ℝ) < ‖(3 : K)‖ := norm_three_pos'
  have hθsq : ‖2 * ω + 1‖ ^ 2 = ‖(3 : K)‖ := sq_norm_two_omega_add_one hω
  have hθ1 : ‖2 * ω + 1‖ ≤ 1 := by nlinarith [h3.le, norm_nonneg (2 * ω + 1 : K)]
  have hnω : ‖ω‖ = 1 := norm_omega hω
  have hu : NormLe 1 (1 - X 0 * X 1 : MvPowerSeries (Fin 2) K) :=
    normLe_sub normLe_one (normLe_mul (normLe_X 0) (normLe_X 1) (le_of_eq (mul_one 1)))
  have hcu : ‖constantCoeff (1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)‖ = 1 := by simp
  have hQ : NormLe 1 (1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹ := normLe_inv hu hcu
  -- the entries of the three reduced matrices
  have a00 : gmod1 ω 0 0 = 1 := by simp [gmod1]
  have a01 : gmod1 ω 0 1 = -(2 * ω + 1) := by simp [gmod1]
  have a10 : gmod1 ω 1 0 = 0 := by simp [gmod1]
  have a11 : gmod1 ω 1 1 = 1 := by simp [gmod1]
  have b00 : gmod2 ω 0 0 = 1 := by simp [gmod2]
  have b01 : gmod2 ω 0 1 = 2 * ω + 1 := by simp [gmod2]
  have b10 : gmod2 ω 1 0 = -(2 * ω + 1) := by simp [gmod2]
  have b11 : gmod2 ω 1 1 = 1 := by simp [gmod2]
  have c00 : gmod3 ω 0 0 = 1 := by simp [gmod3]
  have c01 : gmod3 ω 0 1 = 0 := by simp [gmod3]
  have c10 : gmod3 ω 1 0 = 2 * ω + 1 := by simp [gmod3]
  have c11 : gmod3 ω 1 1 = 1 := by simp [gmod3]
  have ha01 : ‖gmod1 ω 0 1‖ ≤ ‖2 * ω + 1‖ := le_of_eq (by rw [a01, norm_neg])
  have ha10 : ‖gmod1 ω 1 0‖ ≤ ‖2 * ω + 1‖ := by rw [a10, norm_zero]; exact norm_nonneg _
  have hb01 : ‖gmod2 ω 0 1‖ ≤ ‖2 * ω + 1‖ := le_of_eq (by rw [b01])
  have hb10 : ‖gmod2 ω 1 0‖ ≤ ‖2 * ω + 1‖ := le_of_eq (by rw [b10, norm_neg])
  have hc01 : ‖gmod3 ω 0 1‖ ≤ ‖2 * ω + 1‖ := by rw [c01, norm_zero]; exact norm_nonneg _
  have hc10 : ‖gmod3 ω 1 0‖ ≤ ‖2 * ω + 1‖ := le_of_eq (by rw [c10])
  have e1 := normLe_model_expand h3 hθsq a00 a11 ha01 ha10
  have e2 := normLe_model_expand h3 hθsq b00 b11 hb01 hb10
  have e3 := normLe_model_expand h3 hθsq c00 c11 hc01 hc10
  rw [a01, a10] at e1
  rw [b01, b10] at e2
  rw [c01, c10] at e3
  -- the residue is a multiple of `3`
  have hprod : (2 * ω + 1) * (1 - ω) = 3 * (ω + 1) := by linear_combination (-2 : K) * hω
  have hω1 : ‖ω + 1‖ = 1 := by
    have h : ω + 1 = -ω ^ 2 := by linear_combination hω
    rw [h, norm_neg, norm_pow, hnω, one_pow]
  have hres : ‖(2 * ω + 1) * (1 - ω)‖ ≤ ‖(3 : K)‖ := by
    rw [hprod, norm_mul, hω1, mul_one]
  have hsix : ‖(-6 : K)‖ ≤ ‖(3 : K)‖ := by
    have h6 : ‖(6 : K)‖ = ‖(3 : K)‖ ^ 1 :=
      norm_ofNat_eq_pow h3 (n := 6) (e := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num)
    rw [norm_neg, h6, pow_one]
  have hthree : ‖(-3 : K)‖ ≤ ‖(3 : K)‖ := by rw [norm_neg]
  -- split into the three model errors and the residue
  have key : C ω * ((linSeries (gmod1 ω))⁻¹ * (quadSeries (gmod1 ω))⁻¹)
        + (linSeries (gmod2 ω))⁻¹ * (quadSeries (gmod2 ω))⁻¹
        + (linSeries (gmod3 ω))⁻¹ * (quadSeries (gmod3 ω))⁻¹
        + C (2 * ω + 1) * (1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹
      = (C ω * ((linSeries (gmod1 ω))⁻¹ * (quadSeries (gmod1 ω))⁻¹
            - appr 0 (-(2 * ω + 1)) (1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹)
          + ((linSeries (gmod2 ω))⁻¹ * (quadSeries (gmod2 ω))⁻¹
            - appr (-(2 * ω + 1)) (2 * ω + 1) (1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹)
          + ((linSeries (gmod3 ω))⁻¹ * (quadSeries (gmod3 ω))⁻¹
            - appr (2 * ω + 1) 0 (1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹))
        + (C ω * appr 0 (-(2 * ω + 1)) (1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹
          + appr (-(2 * ω + 1)) (2 * ω + 1) (1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹
          + appr (2 * ω + 1) 0 (1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹
          + C (2 * ω + 1) * (1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹) := by ring
  rw [key, bracket_identity ω _ hω]
  refine normLe_add (normLe_add (normLe_add ?_ e2) e3) (normLe_add (normLe_add ?_ ?_) ?_)
  · exact normLe_mul (normLe_C (le_of_eq hnω)) e1 (le_of_eq (one_mul _))
  · exact normLe_mul (normLe_C hres)
      (normLe_add hQ (normLe_mul (normLe_X 1) (normLe_mul hQ hQ (le_of_eq (mul_one 1)))
        (le_of_eq (mul_one 1)))) (le_of_eq (mul_one _))
  · exact normLe_mul (normLe_C hsix)
      (normLe_mul (normLe_mul (normLe_X 0) (normLe_X 0) (le_of_eq (mul_one 1)))
        (normLe_mul hQ hQ (le_of_eq (mul_one 1))) (le_of_eq (mul_one 1))) (le_of_eq (mul_one _))
  · exact normLe_mul (normLe_C hthree)
      (normLe_mul (normLe_mul (normLe_X 0) (normLe_X 1) (le_of_eq (mul_one 1)))
        (normLe_mul hQ hQ (le_of_eq (mul_one 1))) (le_of_eq (mul_one 1))) (le_of_eq (mul_one _))

/-! ### The assembly of [Jacobs, Theorem 2.14] -/

/-- **[Jacobs, Theorem 2.14]** in the quantitative form proved here: every coefficient of
`NgenFun - negGeom` has norm at most `max ‖t‖ ‖2ω+1‖ < 1`.  The three scalars have norm
`‖3‖^{-1/2}`, so each term is compared with its model to precision `‖3‖^{1/2}·(that bound)`. -/
private lemma normLe_ngenFun_sub_negGeom (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1)
    (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) (hω : ω ^ 2 + ω + 1 = 0) :
    NormLe (max ‖t‖ ‖2 * ω + 1‖) (NgenFun t ν ω - negGeom (K := K)) := by
  have h3pos : (0 : ℝ) < ‖(3 : K)‖ := norm_three_pos'
  have hθsq : ‖2 * ω + 1‖ ^ 2 = ‖(3 : K)‖ := sq_norm_two_omega_add_one hω
  have hθnn : (0 : ℝ) ≤ ‖2 * ω + 1‖ := norm_nonneg _
  have hθ1 : ‖2 * ω + 1‖ ≤ 1 := by nlinarith [h3.le]
  have hθpos : (0 : ℝ) < ‖2 * ω + 1‖ := by nlinarith
  have hθne : (2 * ω + 1 : K) ≠ 0 := two_omega_add_one_ne_zero ω hω
  have hnω : ‖ω‖ = 1 := norm_omega hω
  have hεt : ‖t‖ ≤ max ‖t‖ ‖2 * ω + 1‖ := le_max_left _ _
  have hεθ : ‖2 * ω + 1‖ ≤ max ‖t‖ ‖2 * ω + 1‖ := le_max_right _ _
  have hεnn : (0 : ℝ) ≤ max ‖t‖ ‖2 * ω + 1‖ := (norm_nonneg t).trans hεt
  have hε3 : ‖(3 : K)‖ ≤ max ‖t‖ ‖2 * ω + 1‖ := by nlinarith
  have hεa : ‖t‖ * ‖2 * ω + 1‖ ≤ ‖2 * ω + 1‖ * max ‖t‖ ‖2 * ω + 1‖ := by nlinarith
  have hεb : ‖(3 : K)‖ ≤ ‖2 * ω + 1‖ * max ‖t‖ ‖2 * ω + 1‖ := by nlinarith
  have hn4 : ‖(4 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 4) (by norm_num) (by norm_num)
  have hn16 : ‖(16 : K)‖ = 1 := norm_ofNat_eq_one h3 (n := 16) (by norm_num) (by norm_num)
  have hd4 : ‖(4 : K) - 1‖ ≤ ‖(3 : K)‖ := le_of_eq (by rw [show (4 : K) - 1 = 3 by norm_num])
  have hd2 : ‖(-2 : K) - 1‖ ≤ ‖(3 : K)‖ :=
    le_of_eq (by rw [show (-2 : K) - 1 = -3 by norm_num, norm_neg])
  have hu4 : ‖unitPow t (4 : K)‖ ≤ 1 := norm_unitPow_le_one h3 ht hd4
  have hu2 : ‖unitPow t (-2 : K)‖ ≤ 1 := norm_unitPow_le_one h3 ht hd2
  have ht3 : ‖t‖ * ‖(3 : K)‖ ≤ ‖(3 : K)‖ := by nlinarith [ht.le, norm_nonneg t]
  -- the three comparisons with the models
  have hT1 := normLe_term1 t ν ω h3 ht hνc hω hεa hεb
  have hT2 := normLe_term2 t ν ω h3 ht hνc hω hεa hεb
  have hT3 := normLe_term3 t ν ω h3 ht hνc hω hεa hεb
  -- the models are integral
  have a00 : gmod1 ω 0 0 = 1 := by simp [gmod1]
  have a01e : gmod1 ω 0 1 = -(2 * ω + 1) := by simp [gmod1]
  have a10e : gmod1 ω 1 0 = 0 := by simp [gmod1]
  have a11 : gmod1 ω 1 1 = 1 := by simp [gmod1]
  have b00 : gmod2 ω 0 0 = 1 := by simp [gmod2]
  have b01e : gmod2 ω 0 1 = 2 * ω + 1 := by simp [gmod2]
  have b10e : gmod2 ω 1 0 = -(2 * ω + 1) := by simp [gmod2]
  have b11 : gmod2 ω 1 1 = 1 := by simp [gmod2]
  have c00 : gmod3 ω 0 0 = 1 := by simp [gmod3]
  have c01e : gmod3 ω 0 1 = 0 := by simp [gmod3]
  have c10e : gmod3 ω 1 0 = 2 * ω + 1 := by simp [gmod3]
  have c11 : gmod3 ω 1 1 = 1 := by simp [gmod3]
  have hM1 : NormLe 1 ((linSeries (gmod1 ω))⁻¹ * (quadSeries (gmod1 ω))⁻¹) :=
    normLe_model_one h3 hθsq a00 a11 (le_of_eq (by rw [a01e, norm_neg]))
      (by rw [a10e, norm_zero]; exact hθnn)
  have hM2 : NormLe 1 ((linSeries (gmod2 ω))⁻¹ * (quadSeries (gmod2 ω))⁻¹) :=
    normLe_model_one h3 hθsq b00 b11 (le_of_eq (by rw [b01e]))
      (le_of_eq (by rw [b10e, norm_neg]))
  have hM3 : NormLe 1 ((linSeries (gmod3 ω))⁻¹ * (quadSeries (gmod3 ω))⁻¹) :=
    normLe_model_one h3 hθsq c00 c11 (by rw [c01e, norm_zero]; exact hθnn)
      (le_of_eq (by rw [c10e]))
  have hMS := normLe_model_sum ω h3 hω
  -- `‖3‖ = ‖2ω+1‖²` in the two shapes needed below
  have h3θ : ‖(3 : K)‖ ≤ max ‖t‖ ‖2 * ω + 1‖ * ‖2 * ω + 1‖ := by
    calc ‖(3 : K)‖ = ‖2 * ω + 1‖ * ‖2 * ω + 1‖ := by rw [← sq, hθsq]
      _ ≤ max ‖t‖ ‖2 * ω + 1‖ * ‖2 * ω + 1‖ := mul_le_mul_of_nonneg_right hεθ hθnn
  -- the two scalars have norm `‖2ω+1‖⁻¹` and are `≡ ω/(2ω+1)`, `1/(2ω+1)` mod `𝔪₃`
  have hs1 : ‖ω * unitPow t 4 / (16 * (2 * ω + 1))‖ * (‖2 * ω + 1‖
      * max ‖t‖ ‖2 * ω + 1‖) ≤ max ‖t‖ ‖2 * ω + 1‖ := by
    have hmul : ‖ω * unitPow t 4 / (16 * (2 * ω + 1))‖ * ‖2 * ω + 1‖ ≤ 1 := by
      rw [norm_div, norm_mul, norm_mul, hnω, one_mul, hn16, one_mul,
        div_mul_cancel₀ _ (ne_of_gt hθpos)]
      exact hu4
    calc ‖ω * unitPow t 4 / (16 * (2 * ω + 1))‖ * (‖2 * ω + 1‖ * max ‖t‖ ‖2 * ω + 1‖)
        = ‖ω * unitPow t 4 / (16 * (2 * ω + 1))‖ * ‖2 * ω + 1‖ * max ‖t‖ ‖2 * ω + 1‖ := by ring
      _ ≤ 1 * max ‖t‖ ‖2 * ω + 1‖ := mul_le_mul_of_nonneg_right hmul hεnn
      _ = max ‖t‖ ‖2 * ω + 1‖ := one_mul _
  have hs2 : ‖unitPow t (-2) / (4 * (2 * ω + 1))‖ * (‖2 * ω + 1‖
      * max ‖t‖ ‖2 * ω + 1‖) ≤ max ‖t‖ ‖2 * ω + 1‖ := by
    have hmul : ‖unitPow t (-2) / (4 * (2 * ω + 1))‖ * ‖2 * ω + 1‖ ≤ 1 := by
      rw [norm_div, norm_mul, hn4, one_mul, div_mul_cancel₀ _ (ne_of_gt hθpos)]
      exact hu2
    calc ‖unitPow t (-2) / (4 * (2 * ω + 1))‖ * (‖2 * ω + 1‖ * max ‖t‖ ‖2 * ω + 1‖)
        = ‖unitPow t (-2) / (4 * (2 * ω + 1))‖ * ‖2 * ω + 1‖ * max ‖t‖ ‖2 * ω + 1‖ := by ring
      _ ≤ 1 * max ‖t‖ ‖2 * ω + 1‖ := mul_le_mul_of_nonneg_right hmul hεnn
      _ = max ‖t‖ ‖2 * ω + 1‖ := one_mul _
  have hδ1 : ‖ω * unitPow t 4 / (16 * (2 * ω + 1)) - ω / (2 * ω + 1)‖
      ≤ max ‖t‖ ‖2 * ω + 1‖ := by
    have h16 : ‖unitPow t (4 : K) - 16‖ ≤ ‖(3 : K)‖ := by
      refine norm_le_of_sub (y := (-15 : K)) ?_ ?_
      · rw [show unitPow t (4 : K) - 16 - (-15) = unitPow t 4 - 1 by ring]
        exact (norm_unitPow_sub_one_le h3 ht hd4).trans ht3
      · rw [norm_neg,
          show ‖(15 : K)‖ = ‖(3 : K)‖ ^ 1 from
            norm_ofNat_eq_pow h3 (n := 15) (e := 1) (k := 5) (by norm_num) (by norm_num)
              (by norm_num), pow_one]
    rw [show ω * unitPow t 4 / (16 * (2 * ω + 1)) - ω / (2 * ω + 1)
      = ω * (unitPow t 4 - 16) / (16 * (2 * ω + 1)) by field_simp, norm_div, norm_mul,
      norm_mul, hn16, one_mul, hnω, one_mul, div_le_iff₀ hθpos]
    exact h16.trans h3θ
  have hδ2 : ‖unitPow t (-2) / (4 * (2 * ω + 1)) - 1 / (2 * ω + 1)‖
      ≤ max ‖t‖ ‖2 * ω + 1‖ := by
    have h4 : ‖unitPow t (-2 : K) - 4‖ ≤ ‖(3 : K)‖ := by
      refine norm_le_of_sub (y := (-3 : K)) ?_ ?_
      · rw [show unitPow t (-2 : K) - 4 - (-3) = unitPow t (-2) - 1 by ring]
        exact (norm_unitPow_sub_one_le h3 ht hd2).trans ht3
      · rw [norm_neg]
    rw [show unitPow t (-2) / (4 * (2 * ω + 1)) - 1 / (2 * ω + 1)
      = (unitPow t (-2) - 4) / (4 * (2 * ω + 1)) by field_simp, norm_div,
      norm_mul, hn4, one_mul, div_le_iff₀ hθpos]
    exact h4.trans h3θ
  have hδ3 : ‖(1 : K) / (2 * ω + 1)‖ * ‖(3 : K)‖ ≤ max ‖t‖ ‖2 * ω + 1‖ := by
    rw [norm_div, norm_one, div_mul_eq_mul_div, one_mul, div_le_iff₀ hθpos]
    exact h3θ
  -- the decomposition into three model errors, three scalar errors and the residue
  have e1 : (C (1 / (2 * ω + 1)) : MvPowerSeries (Fin 2) K) * C ω = C (ω / (2 * ω + 1)) := by
    rw [← map_mul]; congr 1; field_simp
  have e2 : (C (1 / (2 * ω + 1)) : MvPowerSeries (Fin 2) K) * C (2 * ω + 1) = 1 := by
    rw [← map_mul, show (1 / (2 * ω + 1) * (2 * ω + 1) : K) = 1 by field_simp, map_one]
  rw [ngenFun_eq t ν ω hω, negGeom]
  set Q := (1 - X 0 * X 1 : MvPowerSeries (Fin 2) K)⁻¹ with hQdef
  set M1 := (linSeries (gmod1 ω))⁻¹ * (quadSeries (gmod1 ω))⁻¹ with hM1def
  set M2 := (linSeries (gmod2 ω))⁻¹ * (quadSeries (gmod2 ω))⁻¹ with hM2def
  set M3 := (linSeries (gmod3 ω))⁻¹ * (quadSeries (gmod3 ω))⁻¹ with hM3def
  set F1 := weightGenFun t (gam1 ν ω) with hF1def
  set F2 := weightGenFun t (gam2 ν ω) with hF2def
  set F3 := weightGenFun t (gam3 ν ω) with hF3def
  set s1 := ω * unitPow t 4 / (16 * (2 * ω + 1)) with hs1def
  set s2 := unitPow t (-2) / (4 * (2 * ω + 1)) with hs2def
  have key : C s1 * F1 + C s2 * F2 + C s2 * F3 - -Q
      = (C s1 * (F1 - M1) + C s2 * (F2 - M2) + C s2 * (F3 - M3))
        + (C (s1 - ω / (2 * ω + 1)) * M1 + C (s2 - 1 / (2 * ω + 1)) * M2
          + C (s2 - 1 / (2 * ω + 1)) * M3)
        + C (1 / (2 * ω + 1)) * (C ω * M1 + M2 + M3 + C (2 * ω + 1) * Q) := by
    simp only [map_sub]
    linear_combination (-Q) * e2 - M1 * e1
  rw [key]
  refine normLe_add (normLe_add (normLe_add (normLe_add ?_ ?_) ?_)
    (normLe_add (normLe_add ?_ ?_) ?_)) ?_
  · exact normLe_mul (normLe_C le_rfl) hT1 hs1
  · exact normLe_mul (normLe_C le_rfl) hT2 hs2
  · exact normLe_mul (normLe_C le_rfl) hT3 hs2
  · exact normLe_mul (normLe_C hδ1) hM1 (le_of_eq (mul_one _))
  · exact normLe_mul (normLe_C hδ2) hM2 (le_of_eq (mul_one _))
  · exact normLe_mul (normLe_C hδ2) hM3 (le_of_eq (mul_one _))
  · exact normLe_mul (normLe_C le_rfl) hMS hδ3

/-- The bound produced by the estimates of [Jacobs, pp. 37–39]: `max ‖t‖ ‖2ω+1‖ < 1`
(the weight disc `v₃(t) > 0` and the ramification `v₃(2ω+1) = 1/2`). -/
private lemma max_norm_lt_one (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1) (hω : ω ^ 2 + ω + 1 = 0) :
    max ‖t‖ ‖2 * ω + 1‖ < 1 := by
  refine max_lt ht ?_
  nlinarith [sq_norm_two_omega_add_one hω, norm_nonneg (2 * ω + 1 : K), h3]

/-! ### The coefficients of `negGeom`, and determinants of entrywise-close matrices -/

/-- The explicit geometric series `∑ₘ (xy)^m`. -/
private noncomputable def geomFun : MvPowerSeries (Fin 2) K :=
  fun p => if p 0 = p 1 then 1 else 0

private lemma coeff_geomFun (p : Fin 2 →₀ ℕ) :
    coeff p (geomFun (K := K)) = if p 0 = p 1 then 1 else 0 := rfl

private lemma geomFun_mul : (geomFun (K := K)) * (1 - X 0 * X 1) = 1 := by
  have hX : (X 0 * X 1 : MvPowerSeries (Fin 2) K) = monomial (idx 1 1) 1 := by
    rw [X_def, X_def, monomial_mul_monomial, mul_one]; rfl
  ext p
  rw [mul_sub, mul_one, map_sub, hX, coeff_mul_monomial, coeff_geomFun, coeff_one]
  by_cases h : idx 1 1 ≤ p
  · have h0 : 1 ≤ p 0 := by simpa using h 0
    have h1 : 1 ≤ p 1 := by simpa using h 1
    have hp : p ≠ 0 := by
      intro hzero
      rw [hzero] at h0
      simp at h0
    rw [if_pos h, if_neg hp, coeff_geomFun, mul_one]
    have e0 : (p - idx 1 1) 0 = p 0 - 1 := by simp
    have e1 : (p - idx 1 1) 1 = p 1 - 1 := by simp
    rw [e0, e1]
    by_cases hpp : p 0 = p 1
    · rw [if_pos hpp, if_pos (by omega)]; ring
    · rw [if_neg hpp, if_neg (by omega)]; ring
  · rw [if_neg h, sub_zero]
    have hnot : p 0 = 0 ∨ p 1 = 0 := by
      rcases Nat.eq_zero_or_pos (p 0) with h0 | h0
      · exact Or.inl h0
      · rcases Nat.eq_zero_or_pos (p 1) with h1 | h1
        · exact Or.inr h1
        · exact absurd (by intro j; fin_cases j <;> simp <;> omega) h
    by_cases hpp : p 0 = p 1
    · have hz : p = 0 := by
        rcases hnot with h0 | h0
        · exact fin2_eq_zero h0 (by omega)
        · exact fin2_eq_zero (by omega) h0
      rw [if_pos hpp, if_pos hz]
    · have hz : p ≠ 0 := by
        intro hzero
        exact hpp (by rw [hzero]; simp)
      rw [if_neg hpp, if_neg hz]

/-- The coefficients of `-1/(1 - xy)`: `-1` on the diagonal `j = i`, zero elsewhere — the
matrix `-D(1)` of [Jacobs, Corollary 2.15]. -/
private lemma coeff_negGeom (p : Fin 2 →₀ ℕ) :
    coeff p (negGeom (K := K)) = if p 0 = p 1 then -1 else 0 := by
  have hc : constantCoeff (1 - X 0 * X 1 : MvPowerSeries (Fin 2) K) ≠ 0 := by simp
  have h : (geomFun : MvPowerSeries (Fin 2) K) = (1 - X 0 * X 1)⁻¹ :=
    (MvPowerSeries.eq_inv_iff_mul_eq_one hc).mpr geomFun_mul
  rw [negGeom, ← h, map_neg, coeff_geomFun]
  split_ifs <;> simp

private lemma normLe_negGeom : NormLe (1 : ℝ) (negGeom (K := K)) := by
  intro p
  rw [coeff_negGeom]
  split_ifs <;> simp

/-- Ultrametric telescoping: two products of integral entries differ by at most the largest
entrywise difference. -/
private lemma norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → K) {ε : ℝ}
    (hε : 0 ≤ ε) (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) (hb : ∀ i ∈ s, ‖b i‖ ≤ 1)
    (hab : ∀ i ∈ s, ‖a i - b i‖ ≤ ε) : ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ ε := by
  induction s using Finset.cons_induction with
  | empty => simpa using hε
  | cons i s hi ih =>
    have hpa : ‖∏ j ∈ s, a j‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one (fun j _ => norm_nonneg _)
        (fun j hj => ha j (Finset.mem_cons_of_mem hj))
    have hrec : ‖∏ j ∈ s, a j - ∏ j ∈ s, b j‖ ≤ ε :=
      ih (fun j hj => ha j (Finset.mem_cons_of_mem hj))
        (fun j hj => hb j (Finset.mem_cons_of_mem hj))
        (fun j hj => hab j (Finset.mem_cons_of_mem hj))
    rw [Finset.prod_cons, Finset.prod_cons,
      show a i * ∏ j ∈ s, a j - b i * ∏ j ∈ s, b j
        = (a i - b i) * (∏ j ∈ s, a j) + b i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j) by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖a i - b i‖ * ‖∏ j ∈ s, a j‖ ≤ ε * 1 :=
            mul_le_mul (hab i (Finset.mem_cons_self i s)) hpa (norm_nonneg _) hε
        _ = ε := mul_one ε
    · rw [norm_mul]
      calc ‖b i‖ * ‖∏ j ∈ s, a j - ∏ j ∈ s, b j‖ ≤ 1 * ε :=
            mul_le_mul (hb i (Finset.mem_cons_self i s)) hrec (norm_nonneg _) zero_le_one
        _ = ε := one_mul ε

/-- Determinants of entrywise-close integral matrices are close (Leibniz expansion plus the
ultrametric sum bound). -/
private lemma norm_det_sub_det_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) {ε : ℝ} (hε : 0 ≤ ε)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ ≤ 1) (hAB : ∀ i j, ‖A i j - B i j‖ ≤ ε) :
    ‖A.det - B.det‖ ≤ ε := by
  rw [Matrix.det_apply', Matrix.det_apply', ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε fun σ _ => ?_
  rw [← mul_sub, norm_mul]
  have hsign : ‖((Equiv.Perm.sign σ : ℤ) : K)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
  rw [hsign, one_mul]
  exact norm_prod_sub_prod_le _ _ _ hε (fun i _ => hA _ _) (fun i _ => hB _ _)
    (fun i _ => hAB _ _)

end Reduction

variable {t ν ω : K} (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1) (hν2 : ν ^ 2 = -2)
  (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) (hω : ω ^ 2 + ω + 1 = 0)
include h3 ht hν2 hνc hω

set_option linter.unusedSectionVars false in
/-- **[Jacobs, Lemma 2.13]**: `H′₂,₂(x/3, y)` is integral — every coefficient of
`NgenFun` has norm `≤ 1`. -/
theorem norm_coeff_NgenFun_le (p : Fin 2 →₀ ℕ) :
    ‖coeff p (NgenFun t ν ω)‖ ≤ 1 := by
  refine norm_le_of_sub (y := coeff p (negGeom (K := K))) ?_ (normLe_negGeom p)
  rw [← map_sub]
  exact (normLe_ngenFun_sub_negGeom t ν ω h3 ht hνc hω p).trans
    (max_norm_lt_one t ω h3 ht hω).le

set_option linter.unusedSectionVars false in
/-- **[Jacobs, Theorem 2.14]**: `H′₂,₂(x/3, y) ≡ −1/(1 − xy) mod 𝔪₃`, phrased as a
strict coefficientwise norm inequality. -/
theorem norm_coeff_NgenFun_sub_negGeom_lt (p : Fin 2 →₀ ℕ) :
    ‖coeff p (NgenFun t ν ω) - coeff p (negGeom (K := K))‖ < 1 := by
  rw [← map_sub]
  exact lt_of_le_of_lt (normLe_ngenFun_sub_negGeom t ν ω h3 ht hνc hω p)
    (max_norm_lt_one t ω h3 ht hω)

/-- **[Jacobs, Corollary 2.15]** consumed form: the top-left minors of `N` are units —
`N ≡ −D(1) mod 𝔪₃`, and a matrix congruent to `−1` mod `𝔪₃` has unit determinant. -/
theorem norm_det_NgenFun_minor (n : ℕ) :
    ‖(Matrix.of fun j i : Fin n =>
      coeff (idx (j : ℕ) (i : ℕ)) (NgenFun t ν ω)).det‖ = 1 := by
  set A : Matrix (Fin n) (Fin n) K :=
    Matrix.of fun j i : Fin n => coeff (idx (j : ℕ) (i : ℕ)) (NgenFun t ν ω) with hAdef
  set B : Matrix (Fin n) (Fin n) K :=
    Matrix.of fun j i : Fin n => coeff (idx (j : ℕ) (i : ℕ)) (negGeom (K := K)) with hBdef
  have hBentry : ∀ j i : Fin n, B j i = if j = i then -1 else 0 := by
    intro j i
    show coeff (idx (j : ℕ) (i : ℕ)) (negGeom (K := K)) = _
    rw [coeff_negGeom, idx_apply_zero, idx_apply_one]
    by_cases h : j = i
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (by simpa using fun hc => h (Fin.ext hc))]
  have hBeq : B = (-1 : K) • (1 : Matrix (Fin n) (Fin n) K) := by
    ext j i
    rw [hBentry]
    by_cases h : j = i
    · simp [h]
    · simp [h]
  have hdetB : ‖B.det‖ = 1 := by
    rw [hBeq, Matrix.det_smul, Matrix.det_one, mul_one, norm_pow, norm_neg, norm_one, one_pow]
  have hAbd : ∀ j i : Fin n, ‖A j i‖ ≤ 1 := fun j i =>
    norm_coeff_NgenFun_le h3 ht hν2 hνc hω _
  have hBbd : ∀ j i : Fin n, ‖B j i‖ ≤ 1 := by
    intro j i
    rw [hBentry]
    split_ifs <;> simp
  have hAB : ∀ j i : Fin n, ‖A j i - B j i‖ ≤ max ‖t‖ ‖2 * ω + 1‖ := by
    intro j i
    show ‖coeff (idx (j : ℕ) (i : ℕ)) (NgenFun t ν ω)
      - coeff (idx (j : ℕ) (i : ℕ)) (negGeom (K := K))‖ ≤ _
    rw [← map_sub]
    exact normLe_ngenFun_sub_negGeom t ν ω h3 ht hνc hω _
  have hlt : max ‖t‖ ‖2 * ω + 1‖ < 1 := max_norm_lt_one t ω h3 ht hω
  have hclose : ‖A.det - B.det‖ ≤ max ‖t‖ ‖2 * ω + 1‖ :=
    norm_det_sub_det_le A B ((norm_nonneg t).trans (le_max_left _ _)) hAbd hBbd hAB
  have := norm_eq_of_sub_lt (x := A.det) (y := B.det) (by rw [hdetB]; exact hclose.trans_lt hlt)
  rw [this, hdetB]

end Scaled

section CharSeries

variable {t ν : K} (ω : K) (h3 : ‖(3 : K)‖ < 1) (ht : ‖t‖ < 1) (hν2 : ν ^ 2 = -2)
  (hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) (hω : ω ^ 2 + ω + 1 = 0)

/-!
### Operator identities from matrix identities

[Jacobs, p. 36]'s conjugation `M₂,₂ = D(2ω+1) ∘ D(1/(2ω+1)) M₂,₂` is an identity of
*operators* checked on matrix coefficients; `ext_matrixCoeff` is the extensionality that
makes that legitimate, and the two one-sided lemmas below are the halves of
[Jacobs, Proposition 1.3] (`Jacobs.matrixCoeff_diagOp_comp` is the two-sided version).
-/

-- Operators on `c(ℕ, K)` are determined by their matrices: `Jacobs.ext_matrixCoeff`
-- (`GenFun.lean`), whose index-generic statement subsumes the copy that used to live
-- here (removed 2026-08-05 — the two declarations collided once `GenFun` gained the
-- general form).

omit [CharZero K] in
/-- Post-composing with a diagonal operator scales the rows: `D(a) ∘ u`
([Jacobs, Proposition 1.3], left half). -/
private theorem matrixCoeff_diagOp_comp_left (a : ℕ → K) (ha : ∀ n, ‖a n‖ ≤ 1)
    (u : c(ℕ, K) →L[K] c(ℕ, K)) (j i : ℕ) :
    matrixCoeff ((diagOp a ha).comp u) j i = a j * matrixCoeff u j i := by
  have key : ((diagOp a ha).comp u) (cSpace.single i 1) j = a j * (u (cSpace.single i 1)) j := by
    rw [ContinuousLinearMap.comp_apply, diagOp_apply]
  exact key

omit [CharZero K] in
/-- Pre-composing with a diagonal operator scales the columns: `u ∘ D(b)`
([Jacobs, Proposition 1.3], right half). -/
private theorem matrixCoeff_comp_diagOp (b : ℕ → K) (hb : ∀ n, ‖b n‖ ≤ 1)
    (u : c(ℕ, K) →L[K] c(ℕ, K)) (j i : ℕ) :
    matrixCoeff (u.comp (diagOp b hb)) j i = matrixCoeff u j i * b i := by
  have hin : diagOp b hb (cSpace.single i (1 : K)) = b i • cSpace.single i (1 : K) := by
    refine DFunLike.ext _ _ fun j' => ?_
    rw [diagOp_apply]
    show b j' * cSpace.single i (1 : K) j' = b i * cSpace.single i (1 : K) j'
    rcases eq_or_ne j' i with rfl | hj'
    · rfl
    · rw [cSpace.single_apply_of_ne hj', mul_zero, mul_zero]
  have key : (u.comp (diagOp b hb)) (cSpace.single i 1) j
      = (u (cSpace.single i 1)) j * b i := by
    rw [ContinuousLinearMap.comp_apply, hin, map_smul]
    show b i * (u (cSpace.single i 1)) j = (u (cSpace.single i 1)) j * b i
    rw [mul_comm]
  exact key

/-- `m² = m + 2·C(m, 2)`: the exponent bookkeeping behind `v₃(cₘ) = m²/2 = m/2 + m(m−1)/2`
(the half-power of the conjugating scalar plus the slope-theorem exponent). -/
private theorem add_two_mul_choose_two (m : ℕ) : m + 2 * m.choose 2 = m ^ 2 := by
  induction m with
  | zero => simp
  | succ k ih =>
      have hch : (k + 1).choose 2 = k + k.choose 2 := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
      have hsq : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
      rw [hch, hsq, ← ih]
      ring

/-!
### The half-power `v₃(2ω + 1) = 1/2`

Everything in this section is bookkeeping for `‖2ω + 1‖² = ‖3‖`: the rescaling
`D(1/(2ω+1))` spends exactly half of what a row of `M₂,₂` gains.
-/

include h3 hω in
/-- `‖2ω + 1‖ < 1`, since its square is `‖3‖ < 1`. -/
private theorem norm_theta_lt_one : ‖(2 * ω + 1 : K)‖ < 1 := by
  nlinarith [sq_norm_two_omega_add_one hω, norm_nonneg (2 * ω + 1 : K), h3]

include hω in
/-- `2ω + 1 ≠ 0`: its square is `−3 ≠ 0`. -/
private theorem theta_ne_zero : (2 * ω + 1 : K) ≠ 0 := by
  intro h
  have h30 : ‖(3 : K)‖ = 0 := by
    rw [← sq_norm_two_omega_add_one hω, h, norm_zero]
    simp
  exact (by norm_num : (3 : K) ≠ 0) (norm_eq_zero.1 h30)

include hω in
/-- `‖(2ω+1)⁻¹‖ · ‖3‖ ≤ ‖2ω+1‖` (with equality unless `2ω + 1 = 0`): dividing a row gain
`‖3‖` by the rescaling cost `‖2ω+1‖` leaves exactly `‖2ω+1‖`. -/
private theorem norm_inv_theta_mul_norm_three_le :
    ‖(2 * ω + 1 : K)⁻¹‖ * ‖(3 : K)‖ ≤ ‖(2 * ω + 1 : K)‖ := by
  rcases eq_or_ne (2 * ω + 1 : K) 0 with h | h
  · rw [h]
    simp
  · rw [norm_inv, ← sq_norm_two_omega_add_one hω, sq, ← mul_assoc,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 h), one_mul]

include h3 ht hνc hω in
/-- Row decay of `H₂,₂(x/(2ω+1), y)`: the coefficients of `M₂,₂` gain `‖3‖ ^ j` down the
rows ([Jacobs, Lemma 2.7]) while `D(1/(2ω+1))` only spends `‖2ω+1‖ ^ (-j) = ‖3‖ ^ (-j/2)`. -/
private theorem norm_coeff_M22halfGenFun_le (j i : ℕ) :
    ‖coeff (idx j i) (diagRescale (2 * ω + 1)⁻¹ 1 (M22genFun t ν ω))‖
      ≤ ‖(1 : K)‖ * ‖(2 * ω + 1 : K)‖ ^ j := by
  rw [coeff_diagRescale, idx_apply_zero, idx_apply_one, one_pow, mul_one, norm_mul, norm_pow,
    norm_one, one_mul]
  calc ‖(2 * ω + 1 : K)⁻¹‖ ^ j * ‖coeff (idx j i) (M22genFun t ν ω)‖
      ≤ ‖(2 * ω + 1 : K)⁻¹‖ ^ j * ‖(3 : K)‖ ^ j :=
        mul_le_mul_of_nonneg_left (norm_coeff_M22genFun_le ω hω h3 ht hνc j i) (by positivity)
    _ = (‖(2 * ω + 1 : K)⁻¹‖ * ‖(3 : K)‖) ^ j := (mul_pow _ _ _).symm
    _ ≤ ‖(2 * ω + 1 : K)‖ ^ j :=
        pow_le_pow_left₀ (by positivity) (norm_inv_theta_mul_norm_three_le ω hω) j

open Classical in
/-- The half-scaled operator `u = D(1/(2ω+1)) ∘ M₂,₂` of [Jacobs, p. 36] — bounded and
compactoid because the entries of `M₂,₂` gain `‖3‖^j` down the rows while
`D(1/(2ω+1))` only spends `‖3‖^{j/2}` ([Jacobs, proof of Lemma 2.7 / p. 36]).

Off the locus `ω² + ω + 1 = 0` the rescaling need not be bounded at all (nothing then
prevents `‖2ω+1‖ < ‖3‖`), so the construction is guarded by that equation and takes the
junk value `0` elsewhere; every statement about it carries `hω`, and
`matrixCoeff_M22half` is the only interface to the definition. -/
noncomputable def M22half (_h3 : ‖(3 : K)‖ < 1) (_ht : ‖t‖ < 1)
    (_hνc : ‖ν - 2695‖ ≤ ‖(3 : K)‖ ^ 10) : c(ℕ, K) →L[K] c(ℕ, K) :=
  if hcube : ω ^ 2 + ω + 1 = 0 then
    ofGenFun (diagRescale (2 * ω + 1)⁻¹ 1 (M22genFun t ν ω))
      (hyps_of_row_decay
        (M := fun j i => coeff (idx j i) (diagRescale (2 * ω + 1)⁻¹ 1 (M22genFun t ν ω)))
        (q := 2 * ω + 1) (c := 1) (norm_theta_lt_one ω _h3 hcube)
        (norm_coeff_M22halfGenFun_le ω _h3 _ht _hνc hcube)).1
      (hyps_of_row_decay
        (M := fun j i => coeff (idx j i) (diagRescale (2 * ω + 1)⁻¹ 1 (M22genFun t ν ω)))
        (q := 2 * ω + 1) (c := 1) (norm_theta_lt_one ω _h3 hcube)
        (norm_coeff_M22halfGenFun_le ω _h3 _ht _hνc hcube)).2
  else 0

include h3 ht hνc hω in
/-- The matrix of `M22half` reads off the rescaled generating function `H₂,₂(x/(2ω+1), y)`. -/
theorem matrixCoeff_M22half (j i : ℕ) :
    matrixCoeff (M22half ω h3 ht hνc) j i =
      coeff (idx j i) (diagRescale (2 * ω + 1)⁻¹ 1 (M22genFun t ν ω)) := by
  simp only [M22half]
  rw [dif_pos hω]
  exact matrixCoeff_ofGenFun _ _ _ j i

include h3 ht hνc hω in
/-- The matrix of `M22half` in product form: `(2ω+1)⁻ʲ · a_{j,i}`. -/
theorem matrixCoeff_M22half_eq (j i : ℕ) :
    matrixCoeff (M22half ω h3 ht hνc) j i =
      (2 * ω + 1 : K)⁻¹ ^ j * coeff (idx j i) (M22genFun t ν ω) := by
  rw [matrixCoeff_M22half ω h3 ht hνc hω, coeff_diagRescale, idx_apply_zero, idx_apply_one,
    one_pow, mul_one]

include h3 ht hνc hω in
/-- `M22half` is compactoid: its rows decay like `‖2ω+1‖ ^ j = ‖3‖ ^ (j/2)`
([Jacobs, Corollary 1.10]). -/
private theorem isCompactoid_M22half : IsCompactoid (M22half ω h3 ht hνc) :=
  isCompactoid_of_row_decay (q := 2 * ω + 1) (c := 1) (norm_theta_lt_one ω h3 hω) fun j i => by
    rw [matrixCoeff_M22half ω h3 ht hνc hω]
    exact norm_coeff_M22halfGenFun_le ω h3 ht hνc hω j i

include hω in
/-- `charPowerSeries (M₂,₂) = charPowerSeries (D(1/(2ω+1)) M₂,₂ D(2ω+1))`:
[Jacobs, p. 36]'s application of the trace property [Prop. 1.14]
(`TateFredholm.charPowerSeries_comm` with `u = M22half`, `v = D(2ω+1)`;
`v ∘ u = M₂,₂` and `u ∘ v` is the conjugate). -/
theorem charCoeff_conj_eq (m : ℕ) :
    charCoeff ((M22half ω h3 ht hνc).comp
        (diagOp (fun n => (2 * ω + 1) ^ n) (fun n => by
          rw [norm_pow]
          refine pow_le_one₀ (norm_nonneg _) ?_
          nlinarith [sq_norm_two_omega_add_one hω, h3.le, norm_nonneg (2 * ω + 1)]))) m =
      charCoeff (M22op ω hω h3 ht hνc) m := by
  -- The bound on the diagonal is a proof of a `Prop`, so it may be generalised away.
  have key : ∀ hbnd : ∀ n : ℕ, ‖(2 * ω + 1 : K) ^ n‖ ≤ 1,
      charCoeff ((M22half ω h3 ht hνc).comp (diagOp (fun n => (2 * ω + 1) ^ n) hbnd)) m =
        charCoeff (M22op ω hω h3 ht hνc) m := by
    intro hbnd
    -- `D(2ω+1) ∘ D(1/(2ω+1)) M₂,₂ = M₂,₂`, on matrix coefficients.
    have hcomp : (diagOp (fun n => (2 * ω + 1 : K) ^ n) hbnd).comp (M22half ω h3 ht hνc)
        = M22op ω hω h3 ht hνc := by
      refine ext_matrixCoeff fun j i => ?_
      rw [matrixCoeff_diagOp_comp_left, matrixCoeff_M22half_eq ω h3 ht hνc hω,
        matrixCoeff_M22op, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (theta_ne_zero ω hω),
        one_pow, one_mul]
    -- The trace property [Jacobs, Proposition 1.14].
    have hcs := charPowerSeries_comm (M22half ω h3 ht hνc)
      (diagOp (fun n => (2 * ω + 1 : K) ^ n) hbnd) (isCompactoid_M22half ω h3 ht hνc hω)
    rw [hcomp] at hcs
    have hco := congrArg (PowerSeries.coeff m) hcs
    rwa [charPowerSeries_coeff, charPowerSeries_coeff] at hco
  exact key _

/-!
### The scaled operator `M′₂,₂ = (1/(ω(2ω+1))) D(1/(2ω+1)) M₂,₂ D(2ω+1)`

Its generating function is `NgenFun` with the `1/3` put back into the rows, so its matrix
is `3 ^ j` times the integral matrix `N` of [Jacobs, Lemma 2.13] — exactly the hypothesis
of the abstract slope theorem `norm_charCoeff_of_unit_minors`.
-/

omit [CharZero K] in
/-- The `(j, i)` coefficient of the generating function of `M′₂,₂`. -/
private theorem coeff_M22scaledGenFun (j i : ℕ) :
    coeff (idx j i) ((ω * (2 * ω + 1))⁻¹ •
        diagRescale (2 * ω + 1)⁻¹ (2 * ω + 1) (M22genFun t ν ω)) =
      (ω * (2 * ω + 1))⁻¹ * ((2 * ω + 1 : K)⁻¹ ^ j * (2 * ω + 1) ^ i *
        coeff (idx j i) (M22genFun t ν ω)) := by
  rw [MvPowerSeries.coeff_smul, coeff_diagRescale, idx_apply_zero, idx_apply_one]

include h3 ht hνc hω in
/-- Row decay of the generating function of `M′₂,₂`: the columns cost `‖2ω+1‖ ^ i ≤ 1` and
the rows are the ones of `M22half` up to the scalar `(ω(2ω+1))⁻¹` of norm `‖2ω+1‖⁻¹`. -/
private theorem norm_coeff_M22scaledGenFun_le (j i : ℕ) :
    ‖coeff (idx j i) ((ω * (2 * ω + 1))⁻¹ •
        diagRescale (2 * ω + 1)⁻¹ (2 * ω + 1) (M22genFun t ν ω))‖
      ≤ ‖(2 * ω + 1 : K)⁻¹‖ * ‖(2 * ω + 1 : K)‖ ^ j := by
  have hscalar : ‖((ω * (2 * ω + 1) : K))⁻¹‖ = ‖(2 * ω + 1 : K)⁻¹‖ := by
    rw [norm_inv, norm_inv, norm_mul, norm_omega hω, one_mul]
  have hcol : ‖(2 * ω + 1 : K)‖ ^ i ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (norm_theta_lt_one ω h3 hω).le
  rw [coeff_M22scaledGenFun, norm_mul, hscalar]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [norm_mul, norm_mul, norm_pow, norm_pow]
  calc ‖(2 * ω + 1 : K)⁻¹‖ ^ j * ‖(2 * ω + 1 : K)‖ ^ i * ‖coeff (idx j i) (M22genFun t ν ω)‖
      ≤ ‖(2 * ω + 1 : K)⁻¹‖ ^ j * 1 * ‖(3 : K)‖ ^ j :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcol (by positivity))
          (norm_coeff_M22genFun_le ω hω h3 ht hνc j i) (norm_nonneg _) (by positivity)
    _ = (‖(2 * ω + 1 : K)⁻¹‖ * ‖(3 : K)‖) ^ j := by rw [mul_one, mul_pow]
    _ ≤ ‖(2 * ω + 1 : K)‖ ^ j :=
        pow_le_pow_left₀ (by positivity) (norm_inv_theta_mul_norm_three_le ω hω) j

/-- The matrix of `M′₂,₂` is `3 ^ j` times the integral matrix `N` of [Jacobs, Lemma 2.13]:
`N = D(1/3) M′₂,₂`, i.e. `(3(2ω+1))⁻ʲ = 3⁻ʲ (2ω+1)⁻ʲ`. -/
private theorem coeff_M22scaledGenFun_eq (j i : ℕ) :
    coeff (idx j i) ((ω * (2 * ω + 1))⁻¹ •
        diagRescale (2 * ω + 1)⁻¹ (2 * ω + 1) (M22genFun t ν ω)) =
      (3 : K) ^ j * coeff (idx j i) (NgenFun t ν ω) := by
  have h3ne : (3 : K) ≠ 0 := by norm_num
  have hcancel : (3 : K) ^ j * ((3 : K) * (2 * ω + 1))⁻¹ ^ j = (2 * ω + 1 : K)⁻¹ ^ j := by
    rw [mul_inv, mul_pow, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ h3ne, one_pow, one_mul]
  rw [coeff_M22scaledGenFun]
  simp only [NgenFun, MvPowerSeries.coeff_smul, coeff_diagRescale, idx_apply_zero,
    idx_apply_one]
  rw [← hcancel]
  ring

include hω in
/-- The scaled operator `M′₂,₂` and `N` have matrix `NgenFun`; its `charCoeff` relates to
`M₂,₂`'s by the scalar `(ω(2ω+1))^{-m}` and the conjugation above:
`cₘ(M₂,₂) = (ω(2ω+1))^m · cₘ(M′₂,₂)` ([Jacobs, pp. 35–36]). -/
theorem charCoeff_M22op_eq (m : ℕ) :
    charCoeff (M22op ω hω h3 ht hνc) m =
      (ω * (2 * ω + 1)) ^ m *
        charCoeff (ofGenFun ((ω * (2 * ω + 1))⁻¹ •
            diagRescale (2 * ω + 1)⁻¹ (2 * ω + 1) (M22genFun t ν ω))
          (by
            exact (hyps_of_row_decay
              (M := fun j i => coeff (idx j i) ((ω * (2 * ω + 1))⁻¹ •
                diagRescale (2 * ω + 1)⁻¹ (2 * ω + 1) (M22genFun t ν ω)))
              (q := 2 * ω + 1) (c := (2 * ω + 1)⁻¹) (norm_theta_lt_one ω h3 hω)
              (norm_coeff_M22scaledGenFun_le ω h3 ht hνc hω)).1)
          (by
            exact (hyps_of_row_decay
              (M := fun j i => coeff (idx j i) ((ω * (2 * ω + 1))⁻¹ •
                diagRescale (2 * ω + 1)⁻¹ (2 * ω + 1) (M22genFun t ν ω)))
              (q := 2 * ω + 1) (c := (2 * ω + 1)⁻¹) (norm_theta_lt_one ω h3 hω)
              (norm_coeff_M22scaledGenFun_le ω h3 ht hνc hω)).2)) m := by
  -- The two boundedness proofs are `Prop`s, so they may be generalised away.
  have key : ∀ (hbd : ∃ C, ∀ j i, ‖coeff (idx j i) ((ω * (2 * ω + 1))⁻¹ •
        diagRescale (2 * ω + 1)⁻¹ (2 * ω + 1) (M22genFun t ν ω))‖ ≤ C)
      (hcol : ∀ i, Filter.Tendsto (fun j => coeff (idx j i) ((ω * (2 * ω + 1))⁻¹ •
        diagRescale (2 * ω + 1)⁻¹ (2 * ω + 1) (M22genFun t ν ω))) Filter.cofinite (nhds 0)),
      charCoeff (M22op ω hω h3 ht hνc) m =
        (ω * (2 * ω + 1)) ^ m * charCoeff (ofGenFun ((ω * (2 * ω + 1))⁻¹ •
          diagRescale (2 * ω + 1)⁻¹ (2 * ω + 1) (M22genFun t ν ω)) hbd hcol) m := by
    intro hbd hcol
    have hbnd : ∀ n : ℕ, ‖(2 * ω + 1 : K) ^ n‖ ≤ 1 := fun n => by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (norm_theta_lt_one ω h3 hω).le
    have hω0 : (ω : K) ≠ 0 := by
      intro h
      have hn := norm_omega hω
      rw [h, norm_zero] at hn
      exact zero_ne_one hn
    -- `D(1/(2ω+1)) M₂,₂ D(2ω+1) = ω(2ω+1) · M′₂,₂`, on matrix coefficients.
    have hcomp : (M22half ω h3 ht hνc).comp (diagOp (fun n => (2 * ω + 1 : K) ^ n) hbnd)
        = (ω * (2 * ω + 1)) • ofGenFun ((ω * (2 * ω + 1))⁻¹ •
            diagRescale (2 * ω + 1)⁻¹ (2 * ω + 1) (M22genFun t ν ω)) hbd hcol := by
      refine ext_matrixCoeff fun j i => ?_
      rw [matrixCoeff_comp_diagOp, matrixCoeff_M22half_eq ω h3 ht hνc hω, matrixCoeff_smul,
        matrixCoeff_ofGenFun, coeff_M22scaledGenFun, ← mul_assoc,
        mul_inv_cancel₀ (mul_ne_zero hω0 (theta_ne_zero ω hω)), one_mul]
      ring
    calc charCoeff (M22op ω hω h3 ht hνc) m
        = charCoeff ((M22half ω h3 ht hνc).comp
            (diagOp (fun n => (2 * ω + 1 : K) ^ n) hbnd)) m :=
          (charCoeff_conj_eq ω h3 ht hνc hω m).symm
      _ = charCoeff ((ω * (2 * ω + 1)) • ofGenFun ((ω * (2 * ω + 1))⁻¹ •
            diagRescale (2 * ω + 1)⁻¹ (2 * ω + 1) (M22genFun t ν ω)) hbd hcol) m := by
          rw [hcomp]
      _ = (ω * (2 * ω + 1)) ^ m * charCoeff (ofGenFun ((ω * (2 * ω + 1))⁻¹ •
            diagRescale (2 * ω + 1)⁻¹ (2 * ω + 1) (M22genFun t ν ω)) hbd hcol) m :=
          charCoeff_smul _ _ _
  exact key _ _

include h3 ht hν2 hνc hω in
/-- **[Jacobs, Theorem 2.12] applied to `M′₂,₂`** (via [Jacobs, Lemma 2.13 and
Corollary 2.15]): `‖cₘ(M′₂,₂)‖ = ‖3‖ ^ (m(m−1)/2)`.  The matrix of `M′₂,₂` is `3 ^ j`
times the matrix `N` of `NgenFun`, which is integral (`norm_coeff_NgenFun_le`) and has
unit top-left minors (`norm_det_NgenFun_minor`) — exactly the two hypotheses of
`norm_charCoeff_of_unit_minors`. -/
private theorem norm_charCoeff_M22scaled
    (hbd : ∃ C, ∀ j i, ‖coeff (idx j i) ((ω * (2 * ω + 1))⁻¹ •
      diagRescale (2 * ω + 1)⁻¹ (2 * ω + 1) (M22genFun t ν ω))‖ ≤ C)
    (hcol : ∀ i, Filter.Tendsto (fun j => coeff (idx j i) ((ω * (2 * ω + 1))⁻¹ •
      diagRescale (2 * ω + 1)⁻¹ (2 * ω + 1) (M22genFun t ν ω))) Filter.cofinite (nhds 0))
    (m : ℕ) :
    ‖charCoeff (ofGenFun ((ω * (2 * ω + 1))⁻¹ •
        diagRescale (2 * ω + 1)⁻¹ (2 * ω + 1) (M22genFun t ν ω)) hbd hcol) m‖
      = ‖(3 : K)‖ ^ m.choose 2 := by
  have h3ne : (3 : K) ≠ 0 := by norm_num
  set u := ofGenFun ((ω * (2 * ω + 1))⁻¹ •
    diagRescale (2 * ω + 1)⁻¹ (2 * ω + 1) (M22genFun t ν ω)) hbd hcol with hu
  have hmc : ∀ j i : ℕ, matrixCoeff u j i = (3 : K) ^ j * coeff (idx j i) (NgenFun t ν ω) := by
    intro j i
    rw [hu, matrixCoeff_ofGenFun, coeff_M22scaledGenFun_eq ω]
  refine norm_charCoeff_of_unit_minors h3 u (fun j i => ?_) (fun n => ?_) m
  · rw [hmc, norm_mul, norm_pow]
    calc ‖(3 : K)‖ ^ j * ‖coeff (idx j i) (NgenFun t ν ω)‖
        ≤ ‖(3 : K)‖ ^ j * 1 :=
          mul_le_mul_of_nonneg_left (norm_coeff_NgenFun_le h3 ht hν2 hνc hω _) (by positivity)
      _ = ‖(3 : K)‖ ^ j := mul_one _
  · have hmat : (Matrix.of fun j i : Fin n => (3 : K)⁻¹ ^ (j : ℕ) * matrixCoeff u j i)
        = Matrix.of fun j i : Fin n => coeff (idx (j : ℕ) (i : ℕ)) (NgenFun t ν ω) := by
      refine Matrix.ext fun j i => ?_
      show (3 : K)⁻¹ ^ (j : ℕ) * matrixCoeff u (j : ℕ) (i : ℕ) = _
      rw [hmc, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ h3ne, one_pow, one_mul]
      rfl
    rw [hmat]
    exact norm_det_NgenFun_minor h3 ht hν2 hνc hω n

include hν2 hω in
/-- **[Jacobs, Corollary 2.16] (milestone, vertex data)**: `‖cₘ(M₂,₂)‖² = ‖3‖^(m²)`,
i.e. `det(1 − T·M₂,₂)` has `v₃(cₘ) = m²/2` — the points `(m, m²/2)` of its Newton
polygon.  NOTE (module header): the *slope* statement — that the polygon through these
points has slopes `1/2, 3/2, 5/2, …` — is the separate AG-NP step, not proved here. -/
theorem sq_norm_charCoeff_M22op (m : ℕ) :
    ‖charCoeff (M22op ω hω h3 ht hνc) m‖ ^ 2 = ‖(3 : K)‖ ^ (m ^ 2) := by
  have hθ : ‖(2 * ω + 1 : K)‖ ^ 2 = ‖(3 : K)‖ := sq_norm_two_omega_add_one hω
  rw [charCoeff_M22op_eq ω h3 ht hνc hω m, norm_mul,
    norm_charCoeff_M22scaled ω h3 ht hν2 hνc hω _ _ m, norm_pow, norm_mul, norm_omega hω,
    one_mul]
  calc (‖(2 * ω + 1 : K)‖ ^ m * ‖(3 : K)‖ ^ m.choose 2) ^ 2
      = (‖(2 * ω + 1 : K)‖ ^ 2) ^ m * (‖(3 : K)‖ ^ m.choose 2) ^ 2 := by ring
    _ = ‖(3 : K)‖ ^ m * ‖(3 : K)‖ ^ (2 * m.choose 2) := by
        rw [hθ, ← pow_mul, Nat.mul_comm (m.choose 2) 2]
    _ = ‖(3 : K)‖ ^ (m + 2 * m.choose 2) := (pow_add _ _ _).symm
    _ = ‖(3 : K)‖ ^ (m ^ 2) := by rw [add_two_mul_choose_two]

include hν2 hω in
/-- [Jacobs, Corollary 2.16] in valuation language: `v₃(cₘ(M₂,₂)) = m²/2` for the
additive valuation normalised by `v₃(3) = 1` — the exact valuation-sequence input the
Newton-polygon machinery (`ForMathlib.NumberTheory.NewtonPolygon`) will consume for the
slope reading; that reading itself is the separate AG-NP step (module header).

`m²/2` is a half-integer for odd `m`, which is possible only because `hω` makes `K` ramified
over `ℚ₃` (`2ω + 1 = √−3` a uniformizer, `3 = −(2ω + 1)²`, `v₃(K^×) = (1/2)ℤ`); this is why the
normalisation `ϖ₃` is a `PseudoUniformizer` and not a uniformizer — `3` normalises the
valuation but does not generate the value group.  See the `PhD.Jacobs.U3Data` module header. -/
theorem val_charCoeff_M22op (m : ℕ) :
    (ϖ₃ h3).val (charCoeff (M22op ω hω h3 ht hνc) m) = (((m ^ 2 : ℝ) / 2 : ℝ) : WithTop ℝ) := by
  have hsq := sq_norm_charCoeff_M22op ω h3 ht hν2 hνc hω m
  have h30 : (0 : ℝ) < ‖(3 : K)‖ := (ϖ₃ h3).norm_pos
  have hlog : Real.log ‖(3 : K)‖ ≠ 0 := (ϖ₃ h3).log_norm_neg.ne
  have hne : charCoeff (M22op ω hω h3 ht hνc) m ≠ 0 := by
    intro h
    rw [h, norm_zero] at hsq
    refine (pow_pos h30 (m ^ 2)).ne' ?_
    rw [← hsq]
    ring
  -- `‖cₘ‖² = ‖3‖^(m²)` becomes `2 log ‖cₘ‖ = m² log ‖3‖`, and `v₃ = log ‖·‖ / log ‖3‖`.
  have hlogeq : 2 * Real.log ‖charCoeff (M22op ω hω h3 ht hνc) m‖
      = (m : ℝ) ^ 2 * Real.log ‖(3 : K)‖ := by
    have hc := congrArg Real.log hsq
    rw [Real.log_pow, Real.log_pow] at hc
    push_cast at hc
    linarith
  rw [PseudoUniformizer.val_of_ne_zero (ϖ₃ h3) hne, coe_ϖ₃, WithTop.coe_eq_coe]
  field_simp
  linarith

end CharSeries

end Jacobs
