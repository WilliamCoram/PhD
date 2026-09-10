/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.Theta

/-!
# Bol's identity, and the repaired theta equivariance

[Bu04, §7]'s displayed identity — the well-definedness of `θ^{1−k}` — is

> `(d^{k−1}/dz^{k−1})((cz + d)^{k−2} F((az + b)/(cz + d)))
>   = (ad − bc)^{k−1} (cz + d)^{−k} (d^{k−1}F/dz^{k−1})((az + b)/(cz + d))`,

classically **Bol's identity**.  Read column by column against the generating function of
`QMF.WeightSeries.kappaSlash` (whose `i`-th column is `autFactor γ · mobius γ ^ i`, by
`QMF.WeightSeries.yCoeff_genFun`) it becomes a statement about one-variable power series, with
`u = numX γ = a·x + b`, `L = linX γ = c·x + d` and `D = det γ`:

`∂^r (u^{j+r} · (L⁻¹)^{j+1}) = D^r · (j+r)_r · u^j · (L⁻¹)^{j+r+1}`.

Parametrised by `j` rather than by the column index `i = j + r`, the statement is
**subtraction-free** and the induction on `r` closes on the nose: one derivative produces two
terms, the induction hypothesis applies to them at `j` and at `j + 1`, and the two
`Nat.descFactorial` recurrences make both coefficients `(j+r+1)_{r+1}`, leaving the cocycle
constant `C a · L − C c · u = C (det γ)`.  No Leibniz rule and no binomial theorem are needed.

## Why this file exists

A first draft of the equivariance (in `PhD/LWX/Theta.lean`, removed on 2026-09-09) let the two
weights share an arbitrary finite part `ν : UK →* Kˣ`.  That is false: `ν` is only a monoid hom, so
`ν(cz + d)` need not be constant in `z`, and differentiating leaves a term the other side cannot
match.  Counterexample at `r = 1`: take `ν` to be the inclusion `UK ↪ Kˣ`, so `κ = (·)^3` and
`κ' = (·)^1`, `g` with lower-left entry `c ≠ 0` and `f = 1`; the left side is `c ≠ 0` and the right
side is `0`.  [Bu04, §7]'s displayed identity carries no nebentypus factor at all.  The statements
here are the correct ones, phrased against `autFactor` so that no `ExpansionData` for an integer
power character is needed (that is the deferred ticket B8); the counterexample is recorded in
`.mathlib-quality/lwx-theta/b2_log.jsonl`.

## Main declarations

* `LWX.coeff_iterate_derivative` — `∂^r` on coefficients, the bridge to `LWX.thetaOne`.
* `LWX.bol` — **Bol's identity** for the columns of the weight action.
* `LWX.iterate_derivative_numX_pow_mul_linX_pow` — the vanishing case `i < r`.
* `LWX.thetaOne_comp_kappaSlash_of_autFactor` — the repaired equivariance on one disc.
-/

open AbstractHeckeOperatorSlash RightSlashAction TateFredholm QMF QMF.Weight

open scoped Pointwise QMF TateFredholm

noncomputable section

namespace LWX

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-! ### The iterated formal derivative -/

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **[B1]** The `r`-th formal derivative on coefficients: `∂^r` is the `descFactorial`-weighted
shift, which is exactly the matrix of `LWX.thetaOne`. -/
theorem coeff_iterate_derivative (F : PowerSeries K) (r j : ℕ) :
    PowerSeries.coeff j ((PowerSeries.derivative K)^[r] F)
      = ((Nat.descFactorial (j + r) r : ℕ) : K) * PowerSeries.coeff (j + r) F := by
  induction r generalizing F with
  | zero => simp
  | succ r ih =>
    have hdf : Nat.descFactorial (j + (r + 1)) (r + 1)
        = (j + r + 1) * Nat.descFactorial (j + r) r := by
      rw [show j + (r + 1) = (j + r) + 1 by omega, Nat.succ_descFactorial_succ]
    rw [Function.iterate_succ_apply, ih, PowerSeries.coeff_derivative, hdf,
      show j + r + 1 = j + (r + 1) by omega]
    push_cast
    ring

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The derivative of `numX γ = a·x + b` is the constant `a`. -/
@[simp] theorem derivative_numX (γ : Matrix (Fin 2) (Fin 2) K) :
    PowerSeries.derivative K (numX γ) = PowerSeries.C (γ 0 0) := by
  rw [numX]
  simp

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The derivative of `linX γ = c·x + d` is the constant `c`. -/
@[simp] theorem derivative_linX (γ : Matrix (Fin 2) (Fin 2) K) :
    PowerSeries.derivative K (linX γ) = PowerSeries.C (γ 1 0) := by
  rw [linX]
  simp

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **[B2, first half]** `∂(u^{n+1}) = (n+1)·a·u^n`. -/
theorem derivative_numX_pow (γ : Matrix (Fin 2) (Fin 2) K) (n : ℕ) :
    PowerSeries.derivative K (numX γ ^ (n + 1))
      = ((n : PowerSeries K) + 1) * PowerSeries.C (γ 0 0) * numX γ ^ n := by
  rw [PowerSeries.derivative_pow, derivative_numX, Nat.add_sub_cancel]
  push_cast
  ring

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **[B2, second half]** `∂((L⁻¹)^m) = −m·c·(L⁻¹)^{m+1}`. -/
theorem derivative_linX_inv_pow (γ : Matrix (Fin 2) (Fin 2) K) (m : ℕ) :
    PowerSeries.derivative K (((linX γ)⁻¹) ^ m)
      = -(m : PowerSeries K) * PowerSeries.C (γ 1 0) * ((linX γ)⁻¹) ^ (m + 1) := by
  cases m with
  | zero => simp
  | succ m =>
    rw [PowerSeries.derivative_pow, PowerSeries.derivative_inv', derivative_linX,
      Nat.add_sub_cancel]
    push_cast
    ring

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **[B3]** The cocycle constant: `a·L − c·u = det γ`. -/
theorem C_mul_linX_sub_C_mul_numX (γ : Matrix (Fin 2) (Fin 2) K) :
    PowerSeries.C (γ 0 0) * linX γ - PowerSeries.C (γ 1 0) * numX γ
      = PowerSeries.C γ.det := by
  rw [linX, numX, Matrix.det_fin_two, map_sub, map_mul, map_mul]
  ring

/-! ### The vanishing case: below the order of the derivative -/

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Coefficients of a power of a linear series vanish above the exponent.  (The same statement is
`private` in `PhD/QMF/Weight/Algebraic.lean`; reproved here rather than de-privatising it, which
would rebuild the whole `QMF` tree.) -/
private theorem coeff_linear_pow_eq_zero {c d : K} {k j : ℕ} (hjk : k < j) :
    PowerSeries.coeff j ((PowerSeries.C d + PowerSeries.C c * PowerSeries.X) ^ k) = 0 := by
  induction k generalizing j with
  | zero => rw [pow_zero, PowerSeries.coeff_one, if_neg (by omega)]
  | succ k ih =>
    rw [pow_succ, mul_add, map_add, mul_comm _ (PowerSeries.C d),
      PowerSeries.coeff_C_mul, ih (by omega), mul_zero, ← mul_assoc,
      mul_comm _ (PowerSeries.C c), mul_assoc, PowerSeries.coeff_C_mul]
    obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [mul_comm (_ ^ k) PowerSeries.X, PowerSeries.coeff_succ_X_mul, ih (by omega),
      mul_zero, add_zero]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **[B4]** `u^i · L^t` has `X`-degree at most `i + t`. -/
theorem coeff_numX_pow_mul_linX_pow_eq_zero (γ : Matrix (Fin 2) (Fin 2) K) {i t n : ℕ}
    (hn : i + t < n) : PowerSeries.coeff n (numX γ ^ i * linX γ ^ t) = 0 := by
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun q hq => ?_
  rw [Finset.mem_antidiagonal] at hq
  rcases Nat.lt_or_ge i q.1 with h1 | h1
  · rw [show numX γ = PowerSeries.C (γ 0 1) + PowerSeries.C (γ 0 0) * PowerSeries.X from rfl,
      coeff_linear_pow_eq_zero h1, zero_mul]
  · rw [show linX γ = PowerSeries.C (γ 1 1) + PowerSeries.C (γ 1 0) * PowerSeries.X from rfl,
      coeff_linear_pow_eq_zero (by omega), mul_zero]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **[B5]** Differentiating `u^i · L^t` more than `i + t` times kills it.  This is the `i < r`
half of [Bu04, §7]'s display: there the left-hand series is a polynomial of degree below the order
of the derivative, and the right-hand side is zero because `θ^r` has no column `i < r`. -/
theorem iterate_derivative_numX_pow_mul_linX_pow (γ : Matrix (Fin 2) (Fin 2) K) (i t : ℕ) :
    (PowerSeries.derivative K)^[i + t + 1] (numX γ ^ i * linX γ ^ t) = 0 := by
  refine PowerSeries.ext fun j => ?_
  rw [coeff_iterate_derivative, coeff_numX_pow_mul_linX_pow_eq_zero γ (by omega), mul_zero,
    map_zero]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The iterated derivative is additive. -/
private theorem iterate_derivative_sub (r : ℕ) (A B : PowerSeries K) :
    (PowerSeries.derivative K)^[r] (A - B)
      = (PowerSeries.derivative K)^[r] A - (PowerSeries.derivative K)^[r] B := by
  induction r generalizing A B with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply, map_sub, ih, Function.iterate_succ_apply,
      Function.iterate_succ_apply]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The iterated derivative commutes with multiplication by a constant. -/
theorem iterate_derivative_C_mul (r : ℕ) (k : K) (G : PowerSeries K) :
    (PowerSeries.derivative K)^[r] (PowerSeries.C k * G)
      = PowerSeries.C k * (PowerSeries.derivative K)^[r] G := by
  have hstep : ∀ H : PowerSeries K, PowerSeries.derivative K (PowerSeries.C k * H)
      = PowerSeries.C k * PowerSeries.derivative K H := fun H => by
    rw [Derivation.leibniz, PowerSeries.derivative_C, smul_zero, add_zero, smul_eq_mul]
  induction r generalizing G with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply, hstep, ih, Function.iterate_succ_apply]

/-! ### Bol's identity -/

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **[B6] Bol's identity** ([Bu04, §7]'s displayed identity, column by column).  With
`u = numX γ`, `L = linX γ` and `D = det γ`,
`∂^r (u^{j+r}·(L⁻¹)^{j+1}) = D^r·(j+r)_r·u^j·(L⁻¹)^{j+r+1}`.
The `j`-parametrisation is what makes the induction close: one derivative produces two terms to
which the induction hypothesis applies at `j` and at `j + 1`, and the coefficients
`(j+r+1)·(j+r)_r` and `(j+1)·(j+r+1)_r` are both `(j+r+1)_{r+1}`, leaving `a·L − c·u = det γ`. -/
theorem bol (γ : Matrix (Fin 2) (Fin 2) K) (hd : γ 1 1 ≠ 0) (r j : ℕ) :
    (PowerSeries.derivative K)^[r] (numX γ ^ (j + r) * ((linX γ)⁻¹) ^ (j + 1))
      = PowerSeries.C γ.det ^ r * ((Nat.descFactorial (j + r) r : ℕ) : PowerSeries K)
          * numX γ ^ j * ((linX γ)⁻¹) ^ (j + r + 1) := by
  have hL : linX γ * (linX γ)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_linX]; exact hd)
  induction r generalizing j with
  | zero => simp
  | succ r ih =>
    have hLM : ((linX γ)⁻¹) ^ (j + r + 2) * linX γ = ((linX γ)⁻¹) ^ (j + r + 1) := by
      rw [show j + r + 2 = (j + r + 1) + 1 from rfl, pow_succ, mul_assoc,
        mul_comm ((linX γ)⁻¹) (linX γ), hL, mul_one]
    have hd1 : PowerSeries.derivative K (numX γ ^ (j + (r + 1)) * ((linX γ)⁻¹) ^ (j + 1))
        = PowerSeries.C (((j + r + 1 : ℕ) : K) * γ 0 0)
            * (numX γ ^ (j + r) * ((linX γ)⁻¹) ^ (j + 1))
          - PowerSeries.C (((j + 1 : ℕ) : K) * γ 1 0)
            * (numX γ ^ (j + 1 + r) * ((linX γ)⁻¹) ^ (j + 1 + 1)) := by
      have hexp : j + (r + 1) = (j + r) + 1 := rfl
      rw [Derivation.leibniz, hexp, derivative_numX_pow, derivative_linX_inv_pow, smul_eq_mul,
        smul_eq_mul]
      push_cast
      simp only [map_add, map_mul, map_natCast, map_one]
      ring
    have hdf1 : Nat.descFactorial (j + (r + 1)) (r + 1)
        = (j + r + 1) * Nat.descFactorial (j + r) r := by
      rw [show j + (r + 1) = (j + r) + 1 by omega, Nat.succ_descFactorial_succ]
    have hdf2 : (j + 1) * Nat.descFactorial (j + 1 + r) r
        = (j + r + 1) * Nat.descFactorial (j + r) r := by
      rw [← hdf1, show j + (r + 1) = j + 1 + r by omega, Nat.descFactorial_succ,
        Nat.add_sub_cancel]
    have hcast : ((j + 1 : ℕ) : PowerSeries K)
          * ((Nat.descFactorial (j + 1 + r) r : ℕ) : PowerSeries K)
        = ((j + r + 1 : ℕ) : PowerSeries K)
          * ((Nat.descFactorial (j + r) r : ℕ) : PowerSeries K) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, hdf2]
    rw [Function.iterate_succ_apply, hd1, iterate_derivative_sub, iterate_derivative_C_mul,
      iterate_derivative_C_mul, ih, ih, ← hLM, hdf1,
      show j + 1 + r + 1 = j + r + 2 by omega, show j + (r + 1) + 1 = j + r + 2 by omega,
      map_mul, map_mul, map_natCast, map_natCast, Nat.cast_mul]
    linear_combination
      (((j + r + 1 : ℕ) : PowerSeries K) * ((Nat.descFactorial (j + r) r : ℕ) : PowerSeries K)
          * PowerSeries.C γ.det ^ r * numX γ ^ j * ((linX γ)⁻¹) ^ (j + r + 2))
            * C_mul_linX_sub_C_mul_numX γ
        - (PowerSeries.C (γ 1 0) * PowerSeries.C γ.det ^ r * numX γ ^ (j + 1)
            * ((linX γ)⁻¹) ^ (j + r + 2)) * hcast

/-! ### The repaired equivariance -/

section Equivariance

variable {UK UK' : Subgroup Kˣ} {S : Submonoid (Matrix (Fin 2) (Fin 2) K)} {ρ ρ' : ℝ}

/-- Column `i` of the weight action, as a coefficient of `autFactor · mobius^i`. -/
theorem matrixCoeff_kappaSlash_eq_coeff (κ : AnalyticWeight UK S ρ) (g : S) (j i : ℕ) :
    matrixCoeff (κ.kappaSlash g) j i
      = PowerSeries.coeff j
          (κ.toWeightSeries.autFactor (g : Matrix (Fin 2) (Fin 2) K)
            * mobius (g : Matrix (Fin 2) (Fin 2) K) ^ i) := by
  rw [AnalyticWeight.matrixCoeff_kappaSlash, ← coeff_yCoeff,
    WeightSeries.yCoeff_genFun _ (κ.toWeightSeries.bounds.d_ne_zero g.2) i]

/-- `θ^r` on the left of a composition picks out row `j + r`. -/
private theorem matrixCoeff_thetaOne_comp (T : c(ℕ, K) →L[K] c(ℕ, K)) (r j i : ℕ) :
    matrixCoeff ((thetaOne K r).comp T) j i
      = ((Nat.descFactorial (j + r) r : ℕ) : K) * matrixCoeff T (j + r) i := by
  rw [matrixCoeff_comp,
    tsum_eq_single (j + r) (fun m hm => by rw [matrixCoeff_thetaOne, if_neg hm, mul_zero]),
    matrixCoeff_thetaOne, if_pos rfl, mul_comm]

/-- `θ^r` on the right of a composition picks out column `j'` from column `j' + r`. -/
private theorem matrixCoeff_comp_thetaOne (T : c(ℕ, K) →L[K] c(ℕ, K)) (r j j' : ℕ) :
    matrixCoeff (T.comp (thetaOne K r)) j (j' + r)
      = ((Nat.descFactorial (j' + r) r : ℕ) : K) * matrixCoeff T j j' := by
  rw [matrixCoeff_comp,
    tsum_eq_single j' (fun m hm => by
      rw [matrixCoeff_thetaOne, if_neg (by omega : ¬ j' + r = m + r), zero_mul]),
    matrixCoeff_thetaOne, if_pos rfl]

/-- `θ^r` has no column below `r`. -/
private theorem matrixCoeff_comp_thetaOne_of_lt (T : c(ℕ, K) →L[K] c(ℕ, K)) {r i : ℕ}
    (hi : i < r) (j : ℕ) : matrixCoeff (T.comp (thetaOne K r)) j i = 0 := by
  have hzero : ∀ m : ℕ,
      matrixCoeff (thetaOne K r) m i * matrixCoeff T j m = (0 : K) := fun m => by
    rw [matrixCoeff_thetaOne, if_neg (by omega), zero_mul]
  rw [matrixCoeff_comp, tsum_congr hzero, tsum_zero]

/-- **[B7] The repaired equivariance on one disc** — [Bu04, §7]'s displayed identity as an
operator identity on the Tate algebra.  The hypotheses say that `κ` is the classical weight of
exponent `r + 1` and `κ'` that of exponent `1 − r`, phrased through the automorphy factors
`A_κ = L^{r−1}` and `A_{κ'} = L^{−r−1}` so that no `ExpansionData` for an integer power character
is needed. -/
theorem thetaOne_comp_kappaSlash_of_autFactor (κ : AnalyticWeight UK S ρ)
    (κ' : AnalyticWeight UK' S ρ') (r : ℕ) (g : S)
    {u : K}
    (hA : κ.toWeightSeries.autFactor (g : Matrix (Fin 2) (Fin 2) K)
      * linX (g : Matrix (Fin 2) (Fin 2) K)
      = PowerSeries.C u * linX (g : Matrix (Fin 2) (Fin 2) K) ^ r)
    (hA' : κ'.toWeightSeries.autFactor (g : Matrix (Fin 2) (Fin 2) K)
      * linX (g : Matrix (Fin 2) (Fin 2) K) ^ (r + 1) = PowerSeries.C u) :
    (thetaOne K r).comp (κ.kappaSlash g)
      = ((g : Matrix (Fin 2) (Fin 2) K).det ^ r) • ((κ'.kappaSlash g).comp (thetaOne K r)) := by
  set γ : Matrix (Fin 2) (Fin 2) K := (g : Matrix (Fin 2) (Fin 2) K) with hγ
  have hd : γ 1 1 ≠ 0 := κ.toWeightSeries.bounds.d_ne_zero g.2
  have hL : linX γ * (linX γ)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_linX]; exact hd)
  -- the two automorphy factors in closed form
  have hAκ : κ.toWeightSeries.autFactor γ = PowerSeries.C u * linX γ ^ r * (linX γ)⁻¹ := by
    rw [← hA, mul_assoc, hL, mul_one]
  have hAκ' : κ'.toWeightSeries.autFactor γ = PowerSeries.C u * ((linX γ)⁻¹) ^ (r + 1) := by
    rw [← hA', mul_assoc, ← mul_pow, hL, one_pow, mul_one]
  refine ext_matrixCoeff fun j i => ?_
  rw [matrixCoeff_thetaOne_comp, matrixCoeff_smul, matrixCoeff_kappaSlash_eq_coeff]
  rcases Nat.lt_or_ge i r with hi | hi
  · -- below the order of the derivative: both sides vanish
    rw [matrixCoeff_comp_thetaOne_of_lt _ hi, mul_zero]
    obtain ⟨t, ht⟩ : ∃ t, r = i + t + 1 := ⟨r - i - 1, by omega⟩
    have hshape : κ.toWeightSeries.autFactor γ * mobius γ ^ i
        = PowerSeries.C u * (numX γ ^ i * linX γ ^ t) := by
      rw [hAκ, mobius, mul_pow, ht]
      calc PowerSeries.C u * linX γ ^ (i + t + 1) * (linX γ)⁻¹
            * (numX γ ^ i * ((linX γ)⁻¹) ^ i)
          = PowerSeries.C u * (numX γ ^ i * linX γ ^ t) * (linX γ ^ i * ((linX γ)⁻¹) ^ i)
            * (linX γ * (linX γ)⁻¹) := by ring
        _ = PowerSeries.C u * (numX γ ^ i * linX γ ^ t) := by
            rw [← mul_pow, hL, one_pow, mul_one, mul_one]
    rw [hshape, ← coeff_iterate_derivative, ht, iterate_derivative_C_mul,
      iterate_derivative_numX_pow_mul_linX_pow, mul_zero, map_zero]
  · -- the generic case: Bol's identity
    obtain ⟨j', rfl⟩ : ∃ j', i = j' + r := ⟨i - r, by omega⟩
    have hshape : κ.toWeightSeries.autFactor γ * mobius γ ^ (j' + r)
        = PowerSeries.C u * (numX γ ^ (j' + r) * ((linX γ)⁻¹) ^ (j' + 1)) := by
      rw [hAκ, mobius, mul_pow]
      calc PowerSeries.C u * linX γ ^ r * (linX γ)⁻¹
            * (numX γ ^ (j' + r) * ((linX γ)⁻¹) ^ (j' + r))
          = PowerSeries.C u * (numX γ ^ (j' + r) * ((linX γ)⁻¹) ^ (j' + 1))
              * (linX γ ^ r * ((linX γ)⁻¹) ^ r) := by
            rw [show j' + r = r + j' by omega]
            ring
        _ = PowerSeries.C u * (numX γ ^ (j' + r) * ((linX γ)⁻¹) ^ (j' + 1)) := by
            rw [← mul_pow, hL, one_pow, mul_one]
    have hshape' : κ'.toWeightSeries.autFactor γ * mobius γ ^ j'
        = PowerSeries.C u * (numX γ ^ j' * ((linX γ)⁻¹) ^ (j' + r + 1)) := by
      rw [hAκ', mobius, mul_pow]
      ring
    have hcollect : PowerSeries.C u * (PowerSeries.C γ.det ^ r
          * ((Nat.descFactorial (j' + r) r : ℕ) : PowerSeries K) * numX γ ^ j'
          * ((linX γ)⁻¹) ^ (j' + r + 1))
        = PowerSeries.C (γ.det ^ r * ((Nat.descFactorial (j' + r) r : ℕ) : K))
          * (PowerSeries.C u * (numX γ ^ j' * ((linX γ)⁻¹) ^ (j' + r + 1))) := by
      rw [map_mul, map_pow, map_natCast]
      ring
    rw [hshape, ← coeff_iterate_derivative, iterate_derivative_C_mul, bol γ hd r j', hcollect,
      PowerSeries.coeff_C_mul, matrixCoeff_comp_thetaOne, matrixCoeff_kappaSlash_eq_coeff,
      hshape']
    ring
end Equivariance

/-! ### The disc model -/

section Disc

variable {p : ℕ} [hp : Fact p.Prime] [CharZero K]

/-- The determinant is unchanged by the disc conjugation `t_{a'}⁻¹·δ·t_a`: the two
parametrisations have reciprocal determinants.  (The computation already occurs inside
`LWX.discConjMat_mem_Mh`; it is isolated here because the equivariance needs it on its own.  Its
proper home is `PhD/LWX/DiscModel.lean`; stated here to avoid rebuilding that tree.) -/
theorem det_discConjMat (h : ℕ) (δ : M1 p) (a : ZMod (p ^ h)) :
    (discConjMat h δ a).det = (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]).det := by
  have hpne : ((p : ℚ_[p])) ^ h ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  rw [discConjMat, Matrix.det_fin_two_of, Matrix.det_fin_two]
  field_simp
  ring

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The determinant of the `K`-side disc conjugate is `ψ (det δ)`. -/
theorem det_discConjK (h : ℕ) (ψ : ℚ_[p] →+* K) (δ : M1 p) (a : ZMod (p ^ h)) :
    ((discConjK h δ a ψ : M1Kh h ψ) : Matrix (Fin 2) (Fin 2) K).det
      = ψ ((δ : Matrix (Fin 2) (Fin 2) ℚ_[p]).det) := by
  rw [coe_discConjK, ← RingHom.map_det, coe_discConj, det_discConjMat]

omit hp [CharZero K] in
/-- A scalar passes through a rectangular block operator.  (Its proper home is
`PhD/TateFredholm/BlockMap.lean`; kept here to avoid rebuilding that tree.) -/
theorem smul_blockOpMap {σ : Type*} [Fintype σ] [DecidableEq σ] {I I' : Type*}
    [DecidableEq I] [DecidableEq I'] (c : K) (T : σ → σ → (c(I, K) →L[K] c(I', K))) :
    c • blockOpMap T = blockOpMap fun a b => c • T a b := by
  refine ext_matrixCoeff fun x y => ?_
  obtain ⟨a, j⟩ := x
  obtain ⟨b, i⟩ := y
  rw [matrixCoeff_smul, matrixCoeff_blockOpMap, matrixCoeff_blockOpMap, matrixCoeff_smul]

variable {UK UK' : Subgroup Kˣ} {ρ ρ' : ℝ}

omit [CharZero K] in
/-- **[B9] The repaired equivariance on the disc model.**  `discSlash` is a `blockOp` of
`kappaSlash`s and `thetaDisc` is a `blockMap` of `thetaOne`s, so both sides are rectangular block
operators and the identity is `thetaOne_comp_kappaSlash_of_autFactor` in every block, at the disc
conjugate `discConjK h δ a ψ`; the scalar matches because the disc conjugation preserves the
determinant (`det_discConjK`). -/
theorem thetaDisc_comp_discSlash_of_autFactor (h r : ℕ) (ψ : ℚ_[p] →+* K)
    (κ : AnalyticWeight UK (M1Kh h ψ) ρ) (κ' : AnalyticWeight UK' (M1Kh h ψ) ρ') (δ : M1 p)
    {u : ZMod (p ^ h) → K}
    (hA : ∀ a : ZMod (p ^ h),
      κ.toWeightSeries.autFactor ((discConjK h δ a ψ : M1Kh h ψ) : Matrix (Fin 2) (Fin 2) K)
          * linX ((discConjK h δ a ψ : M1Kh h ψ) : Matrix (Fin 2) (Fin 2) K)
        = PowerSeries.C (u a)
          * linX ((discConjK h δ a ψ : M1Kh h ψ) : Matrix (Fin 2) (Fin 2) K) ^ r)
    (hA' : ∀ a : ZMod (p ^ h),
      κ'.toWeightSeries.autFactor ((discConjK h δ a ψ : M1Kh h ψ) : Matrix (Fin 2) (Fin 2) K)
          * linX ((discConjK h δ a ψ : M1Kh h ψ) : Matrix (Fin 2) (Fin 2) K) ^ (r + 1)
        = PowerSeries.C (u a)) :
    (thetaDisc p K h r).comp (discSlash h ψ κ δ)
      = (ψ ((δ : Matrix (Fin 2) (Fin 2) ℚ_[p]).det) ^ r) •
        ((discSlash h ψ κ' δ).comp (thetaDisc p K h r)) := by
  rw [thetaDisc, discSlash, discSlash, blockMap_comp_blockOp, blockOp_comp_blockMap,
    smul_blockOpMap]
  refine congrArg blockOpMap (funext fun a => funext fun b => ?_)
  by_cases hb : b = discImage h δ a
  · rw [if_pos hb, if_pos hb, thetaOne_comp_kappaSlash_of_autFactor κ κ' r _ (hA a) (hA' a),
      det_discConjK]
  · rw [if_neg hb, if_neg hb, ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_comp,
      smul_zero]

omit hp [CharZero K] in
/-- Composition distributes over a finite sum on the right. -/
private theorem comp_sum {I J H : Type*} [DecidableEq I] [DecidableEq J] [DecidableEq H]
    {α : Type*} (T : c(I, K) →L[K] c(J, K)) (s : Finset α) (f : α → (c(H, K) →L[K] c(I, K))) :
    T.comp (∑ t ∈ s, f t) = ∑ t ∈ s, T.comp (f t) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ContinuousLinearMap.comp_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ContinuousLinearMap.comp_add, ih]

omit hp [CharZero K] in
/-- Composition distributes over a finite sum on the left. -/
private theorem sum_comp' {I J H : Type*} [DecidableEq I] [DecidableEq J] [DecidableEq H]
    {α : Type*} (T : c(H, K) →L[K] c(I, K)) (s : Finset α) (f : α → (c(I, K) →L[K] c(J, K))) :
    (∑ t ∈ s, f t).comp T = ∑ t ∈ s, (f t).comp T := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ContinuousLinearMap.zero_comp]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ContinuousLinearMap.add_comp, ih]

variable {G : Type*} [Group G] {Γ : Subgroup G} (θG : G →* Matrix (Fin 2) (Fin 2) ℚ_[p])
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [CharZero K] in
/-- **[B10] The repaired `U_p` intertwining** ([Bu04, §7]:
"`[UηU]θ^{1−k} = |ν(η)|^{k−1}θ^{1−k}[UηU]`").
`discHeckeBlock` is a finite sum of `discSlash`es over the coset representatives, so this is
`thetaDisc_comp_discSlash_of_autFactor` termwise plus `Finset.smul_sum`; the uniform scalar is the
hypothesis `hdet`. -/
theorem thetaDisc_comp_discHeckeBlock_of_autFactor (h r : ℕ) (ψ : ℚ_[p] →+* K)
    (κ : AnalyticWeight UK (M1Kh h ψ) ρ) (κ' : AnalyticWeight UK' (M1Kh h ψ) ρ')
    (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θG)
    (vRep : Fin p → G) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) θG) (idx : ι → Fin p → ι)
    (uu : ι → Fin p → U) (cst : K) {u : ι → Fin p → ZMod (p ^ h) → K}
    (hA : ∀ (i' : ι) (t : Fin p) (a : ZMod (p ^ h)),
      κ.toWeightSeries.autFactor
          ((discConjK h (certM1 θG U hU vRep hvΔ uu i' t) a ψ : M1Kh h ψ) :
            Matrix (Fin 2) (Fin 2) K)
          * linX ((discConjK h (certM1 θG U hU vRep hvΔ uu i' t) a ψ : M1Kh h ψ) :
            Matrix (Fin 2) (Fin 2) K)
        = PowerSeries.C (u i' t a)
          * linX ((discConjK h (certM1 θG U hU vRep hvΔ uu i' t) a ψ : M1Kh h ψ) :
            Matrix (Fin 2) (Fin 2) K) ^ r)
    (hA' : ∀ (i' : ι) (t : Fin p) (a : ZMod (p ^ h)),
      κ'.toWeightSeries.autFactor
          ((discConjK h (certM1 θG U hU vRep hvΔ uu i' t) a ψ : M1Kh h ψ) :
            Matrix (Fin 2) (Fin 2) K)
          * linX ((discConjK h (certM1 θG U hU vRep hvΔ uu i' t) a ψ : M1Kh h ψ) :
            Matrix (Fin 2) (Fin 2) K) ^ (r + 1) = PowerSeries.C (u i' t a))
    (hdet : ∀ i' t, ψ ((certM1 θG U hU vRep hvΔ uu i' t :
      Matrix (Fin 2) (Fin 2) ℚ_[p]).det) = cst) (i j : ι) :
    (thetaDisc p K h r).comp (discHeckeBlock θG h ψ κ U hU vRep hvΔ idx uu i j)
      = (cst ^ r) •
        ((discHeckeBlock θG h ψ κ' U hU vRep hvΔ idx uu i j).comp (thetaDisc p K h r)) := by
  rw [discHeckeBlock, discHeckeBlock, comp_sum, sum_comp', Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [thetaDisc_comp_discSlash_of_autFactor h r ψ κ κ' _ (hA i t) (hA' i t), hdet]

end Disc

end LWX
